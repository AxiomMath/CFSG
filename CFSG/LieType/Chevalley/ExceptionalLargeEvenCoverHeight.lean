module

public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable

public noncomputable section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

variable (τ) in
abbrev heightSet (h : ℤ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α}

theorem heightSeries_eq_closure
    (h : ℤ) :
    heightSeries τ K h =
      Subgroup.closure {g | ∃ α ∈ heightSet τ h, ∃ c : K, pinnedX τ K α c = g} :=
  rootSpan_eq_closure K _

theorem pinnedX_mem_heightSeries
    {h : ℤ} {α : Fin τ.rank → ℤ} (hα : α ∈ heightSet τ h)
    (c : K) : pinnedX τ K α c ∈ heightSeries τ K h := by
  rw [heightSeries_eq_closure]
  exact Subgroup.subset_closure ⟨α, hα, c, rfl⟩

theorem heightSeries_eq_succ_of_nonpos
    {h : ℤ} (hh : h ≤ 0) :
    heightSeries τ K h = heightSeries τ K (h + 1) := by
  unfold heightSeries
  congr 1
  ext α
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by omega⟩

theorem commutator_heightSeries_le_succ
    (h : ℤ) :
    ⁅heightSeries τ K h, heightSeries τ K h⁆ ≤ heightSeries τ K (h + 1) := by
  rcases le_or_gt h 0 with hh | hh
  · rw [← heightSeries_eq_succ_of_nonpos hh]
    exact Subgroup.commutator_le_self _
  · exact (commutator_heightSeries_le K h h).trans (heightSeries_antitone (by omega))

theorem sq_mem_heightSeries_succ
    [CharP K 2] {h : ℤ} {x : ModGL τ K}
    (hx : x ∈ heightSeries τ K h) : x ^ 2 ∈ heightSeries τ K (h + 1) := by
  have hcl := heightSeries_eq_closure (τ := τ) (K := K) h
  rw [hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, -, c, rfl⟩ := hg
    rw [sq, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
    exact one_mem _
  | one => rw [one_pow]; exact one_mem _
  | mul x y hx hy ihx ihy =>
    have hxV : x ∈ heightSeries τ K h := hcl ▸ hx
    have hyV : y ∈ heightSeries τ K h := hcl ▸ hy
    have hc : ⁅x⁻¹, y⁆ ∈ heightSeries τ K (h + 1) :=
      commutator_heightSeries_le_succ h (Subgroup.commutator_mem_commutator (inv_mem hxV) hyV)
    have e : (x * y) ^ 2 = x ^ 2 * ⁅x⁻¹, y⁆ * y ^ 2 := by
      simp only [sq, commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem ihx hc) ihy
  | inv x _ ihx =>
    rw [inv_pow]
    exact inv_mem ihx

instance heightSeries_succ_subgroupOf_normal
    (h : ℤ) :
    ((heightSeries τ K (h + 1)).subgroupOf (heightSeries τ K h)).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : ModGL τ K) ∈ posUnipotent τ K := heightSeries_le_posUnipotent h g.2
    exact (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K (h + 1) hg) n).1 hn⟩

variable (τ K) in
abbrev HeightQuot
    (h : ℤ) : Type :=
  heightSeries τ K h ⧸ (heightSeries τ K (h + 1)).subgroupOf (heightSeries τ K h)

instance instCommGroupHeightQuot
    (h : ℤ) : CommGroup (HeightQuot τ K h) :=
  { (inferInstance : Group (HeightQuot τ K h)) with
    mul_comm := fun q q' => by
      induction q using QuotientGroup.induction_on with
      | H x =>
        induction q' using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
            Subgroup.mem_subgroupOf]
          have e : (((x * y)⁻¹ * (y * x) : heightSeries τ K h) : ModGL τ K) =
              ⁅((y : ModGL τ K))⁻¹, ((x : ModGL τ K))⁻¹⁆ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
            group
          rw [e]
          exact commutator_heightSeries_le_succ h
            (Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2)) }

theorem heightQuot_sq_eq_one
    [CharP K 2] {h : ℤ} (q : HeightQuot τ K h) : q ^ 2 = 1 := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      SubgroupClass.coe_pow]
    exact sq_mem_heightSeries_succ x.2

@[expose] def rootElt
    {h : ℤ} {α : Fin τ.rank → ℤ} (hα : α ∈ heightSet τ h) :
    Multiplicative K →* HeightQuot τ K h where
  toFun c := QuotientGroup.mk ⟨pinnedX τ K α (Multiplicative.toAdd c),
    pinnedX_mem_heightSeries hα _⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext (pinnedX_zero τ K α)
  map_mul' c d := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (pinnedX_add τ K α _ _)

theorem heightQuot_induction
    {h : ℤ} {P : HeightQuot τ K h → Prop}
    (hgen : ∀ (α : Fin τ.rank → ℤ) (hα : α ∈ heightSet τ h) (c : K),
      P (rootElt hα (Multiplicative.ofAdd c)))
    (hone : P 1) (hmul : ∀ q q', P q → P q' → P (q * q')) (hinv : ∀ q, P q → P q⁻¹)
    (q : HeightQuot τ K h) : P q := by
  have hcl := heightSeries_eq_closure (τ := τ) (K := K) h
  have key : ∀ (g : ModGL τ K)
      (hg : g ∈ Subgroup.closure {g | ∃ α ∈ heightSet τ h, ∃ c : K, pinnedX τ K α c = g})
      (hg₀ : g ∈ heightSeries τ K h), P (QuotientGroup.mk ⟨g, hg₀⟩) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨α, hα, c, rfl⟩ := hg
      intro _
      exact hgen α hα c
    | one =>
      intro _
      exact hone
    | mul x y hx hy ihx ihy =>
      intro _
      exact hmul _ _ (ihx (hcl ▸ hx)) (ihy (hcl ▸ hy))
    | inv x hx ihx =>
      intro _
      exact hinv _ (ihx (hcl ▸ hx))
  induction q using QuotientGroup.induction_on with
  | H x => exact key x (hcl ▸ x.2) x.2

theorem torusVec_conj_mem_heightSeries
    (t : Fin τ.rank → Kˣ) {h : ℤ} {x : ModGL τ K}
    (hx : x ∈ heightSeries τ K h) :
    torusVec τ K t * x * (torusVec τ K t)⁻¹ ∈ heightSeries τ K h :=
  torusVec_conj_mem_rootSpan t (fun _ hα => hα.1) hx

@[expose] def heightConj
    (h : ℤ) (t : Fin τ.rank → Kˣ) :
    heightSeries τ K h →* heightSeries τ K h where
  toFun x := ⟨torusVec τ K t * x * (torusVec τ K t)⁻¹, torusVec_conj_mem_heightSeries t x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_heightConj
    (h : ℤ) (t : Fin τ.rank → Kˣ) (x : heightSeries τ K h) :
    ((heightConj h t x : heightSeries τ K h) : ModGL τ K) =
      torusVec τ K t * x * (torusVec τ K t)⁻¹ :=
  rfl

@[expose] def heightQuotSmul
    (h : ℤ) (t : Fin τ.rank → Kˣ) :
    HeightQuot τ K h →* HeightQuot τ K h :=
  QuotientGroup.map _ _ (heightConj h t) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_heightConj]
    exact torusVec_conj_mem_heightSeries t hx

theorem heightQuotSmul_mk
    (h : ℤ) (t : Fin τ.rank → Kˣ) (x : heightSeries τ K h) :
    heightQuotSmul h t (QuotientGroup.mk x) = QuotientGroup.mk (heightConj h t x) :=
  QuotientGroup.map_mk _ _ _ _ _

theorem heightQuotSmul_rootElt
    {h : ℤ} (t : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ}
    (hα : α ∈ heightSet τ h) (c : K) :
    heightQuotSmul h t (rootElt hα (Multiplicative.ofAdd c)) =
      rootElt hα (Multiplicative.ofAdd ((rootChar K α t : K) * c)) :=
  (heightQuotSmul_mk h t _).trans (congrArg QuotientGroup.mk (Subtype.ext
    ((coe_heightConj h t _).trans (torusVec_conj_pinnedX hα.1 t c))))

theorem heightQuot_prod_smul_eq_one
    [Fintype (Fin τ.rank → Kˣ)]
    (hχ : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → 0 < height β → rootChar K β ≠ 1) {h : ℤ}
    (q : HeightQuot τ K h) : ∏ t : Fin τ.rank → Kˣ, heightQuotSmul h t q = 1 := by
  induction q using heightQuot_induction with
  | hgen α hα c =>
    have hsum : ∑ t : Fin τ.rank → Kˣ, (rootChar K α t : K) = 0 := by
      refine sum_hom_units_eq_zero ((Units.coeHom K).comp (rootChar K α)) fun h1 => ?_
      refine hχ α hα.1 hα.2.1 (MonoidHom.ext fun t => Units.ext ?_)
      exact DFunLike.congr_fun h1 t
    simp only [heightQuotSmul_rootElt]
    rw [← map_prod, ← ofAdd_sum, ← Finset.sum_mul, hsum, zero_mul, ofAdd_zero, map_one]
  | hone => simp
  | hmul q q' hq hq' => simp only [map_mul, Finset.prod_mul_distrib, hq, hq', mul_one]
  | hinv q hq => simp only [map_inv, Finset.prod_inv_distrib, hq, inv_one]

theorem mem_heightSeries_succ_of_forall
    [Finite K] [CharP K 2]
    (hT : Odd (Nat.card (Fin τ.rank → Kˣ)))
    (hχ : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → 0 < height β → rootChar K β ≠ 1) {h : ℤ}
    {x : ModGL τ K} (hx : x ∈ heightSeries τ K h)
    (hfix : ∀ t : Fin τ.rank → Kˣ,
      (torusVec τ K t * x * (torusVec τ K t)⁻¹)⁻¹ * x ∈ heightSeries τ K (h + 1)) :
    x ∈ heightSeries τ K (h + 1) := by
  classical
  have := Fintype.ofFinite (Fin τ.rank → Kˣ)
  set q : HeightQuot τ K h := QuotientGroup.mk ⟨x, hx⟩ with hq
  have hsmul : ∀ t, heightQuotSmul h t q = q := fun t => by
    rw [hq, heightQuotSmul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hfix t
  have hprod := heightQuot_prod_smul_eq_one hχ q
  simp only [hsmul, Finset.prod_const, Finset.card_univ] at hprod
  obtain ⟨k, hk⟩ := hT
  rw [← Nat.card_eq_fintype_card, hk, pow_succ, pow_mul, heightQuot_sq_eq_one, one_pow,
    one_mul] at hprod
  rw [hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hprod
  exact hprod

theorem eq_zero_of_closure {G : Type*} [Group G] {s : Set G} (φ : G → ZMod 2)
    (hφ : ∀ x ∈ Subgroup.closure s, ∀ x' ∈ Subgroup.closure s, φ (x * x') = φ x + φ x')
    (hs : ∀ g ∈ s, φ g = 0) : ∀ x ∈ Subgroup.closure s, φ x = 0 := by
  have h1 : φ 1 = 0 := by
    have h := hφ 1 (one_mem _) 1 (one_mem _)
    rwa [mul_one, left_eq_add] at h
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact hs g hg
  | one => exact h1
  | mul x y hx hy ihx ihy => rw [hφ x hx y hy, ihx, ihy, add_zero]
  | inv x hx ihx =>
    have h := hφ x hx x⁻¹ (inv_mem hx)
    rwa [mul_inv_cancel, h1, ihx, zero_add, eq_comm] at h

theorem form_eq_zero_of_heightSeries
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f)
    (harith : ∀ α β : Fin τ.rank → ℤ, IsRoot τ α → 0 < height α → IsRoot τ β → 0 < height β →
      ∀ i j : ℕ, i < f → j < f →
        ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k)
    (h h' : ℤ) (b : ModGL τ K → ModGL τ K → ZMod 2)
    (hb₁ : ∀ x ∈ heightSeries τ K h, ∀ x' ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h',
      b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h', ∀ y' ∈ heightSeries τ K h',
      b x (y * y') = b x y + b x y')
    (hb₅ : ∀ (t : Fin τ.rank → Kˣ), ∀ x ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h',
      b (torusVec τ K t * x * (torusVec τ K t)⁻¹) (torusVec τ K t * y * (torusVec τ K t)⁻¹) =
        b x y) :
    ∀ x ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h', b x y = 0 := by
  have hroot : ∀ α ∈ heightSet τ h, ∀ β ∈ heightSet τ h', ∀ c d : K,
      b (pinnedX τ K α c) (pinnedX τ K β d) = 0 := by
    intro α hα β hβ
    refine rootChar_form_eq_zero hf hK (harith α β hα.1 hα.2.1 hβ.1 hβ.2.1)
      (fun c d => b (pinnedX τ K α c) (pinnedX τ K β d)) (fun c₁ c₂ d => ?_)
      (fun c d₁ d₂ => ?_) (fun t c d => ?_)
    · rw [pinnedX_add]
      exact hb₁ _ (pinnedX_mem_heightSeries hα _) _ (pinnedX_mem_heightSeries hα _) _
        (pinnedX_mem_heightSeries hβ _)
    · rw [pinnedX_add]
      exact hb₂ _ (pinnedX_mem_heightSeries hα _) _ (pinnedX_mem_heightSeries hβ _) _
        (pinnedX_mem_heightSeries hβ _)
    · rw [← torusVec_conj_pinnedX hα.1, ← torusVec_conj_pinnedX hβ.1]
      exact hb₅ t _ (pinnedX_mem_heightSeries hα _) _ (pinnedX_mem_heightSeries hβ _)
  have hleft : ∀ α ∈ heightSet τ h, ∀ c : K, ∀ y ∈ heightSeries τ K h',
      b (pinnedX τ K α c) y = 0 := by
    intro α hα c y hy
    rw [heightSeries_eq_closure] at hy
    refine eq_zero_of_closure (b (pinnedX τ K α c)) (fun y hy y' hy' => ?_) ?_ y hy
    · rw [← heightSeries_eq_closure] at hy hy'
      exact hb₂ _ (pinnedX_mem_heightSeries hα _) _ hy _ hy'
    · rintro _ ⟨β, hβ, d, rfl⟩
      exact hroot α hα β hβ c d
  intro x hx y hy
  rw [heightSeries_eq_closure] at hx
  refine eq_zero_of_closure (fun x => b x y) (fun x hx x' hx' => ?_) ?_ x hx
  · rw [← heightSeries_eq_closure] at hx hx'
    exact hb₁ _ hx _ hx' _ hy
  · rintro _ ⟨α, hα, c, rfl⟩
    exact hleft α hα c y hy

end CFSG.LieType.Chevalley.ExceptionalCover
