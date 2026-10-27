module

public import CFSG.LieType.Ree.LargeReeTorusRootForms
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open scoped commutatorElement

variable {K : Type} [Field K]

abbrev heightSet (h : ℤ) : Set (Fin F4.tag.rank → ℤ) :=
  {α | IsRoot F4.tag α ∧ 0 < height α ∧ h ≤ height α}

theorem heightSeries_eq_closure
    (h : ℤ) :
    heightSeries F4.tag K h =
      Subgroup.closure {g | ∃ α ∈ heightSet h, ∃ c : K, pinnedX F4.tag K α c = g} :=
  rootSpan_eq_closure K _

theorem pinnedX_mem_heightSeries
    {h : ℤ} {α : Fin F4.tag.rank → ℤ} (hα : α ∈ heightSet h)
    (c : K) : pinnedX F4.tag K α c ∈ heightSeries F4.tag K h := by
  rw [heightSeries_eq_closure]
  exact Subgroup.subset_closure ⟨α, hα, c, rfl⟩

theorem heightSeries_eq_succ_of_nonpos
    {h : ℤ} (hh : h ≤ 0) :
    heightSeries F4.tag K h = heightSeries F4.tag K (h + 1) := by
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
    ⁅heightSeries F4.tag K h, heightSeries F4.tag K h⁆ ≤ heightSeries F4.tag K (h + 1) := by
  rcases le_or_gt h 0 with hh | hh
  · rw [← heightSeries_eq_succ_of_nonpos hh]
    exact Subgroup.commutator_le_self _
  · exact (commutator_heightSeries_le K h h).trans (heightSeries_antitone (by omega))

theorem sq_mem_heightSeries_succ
    [CharP K 2] {h : ℤ} {x : (Module.End K (RootModule F4.tag K))ˣ}
    (hx : x ∈ heightSeries F4.tag K h) : x ^ 2 ∈ heightSeries F4.tag K (h + 1) := by
  have hcl := heightSeries_eq_closure (K := K) h
  rw [hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, -, c, rfl⟩ := hg
    rw [sq, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
    exact one_mem _
  | one => rw [one_pow]; exact one_mem _
  | mul x y hx hy ihx ihy =>
    have hxV : x ∈ heightSeries F4.tag K h := hcl ▸ hx
    have hyV : y ∈ heightSeries F4.tag K h := hcl ▸ hy
    have hc : ⁅x⁻¹, y⁆ ∈ heightSeries F4.tag K (h + 1) :=
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
    ((heightSeries F4.tag K (h + 1)).subgroupOf (heightSeries F4.tag K h)).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : (Module.End K (RootModule F4.tag K))ˣ) ∈ posUnipotent F4.tag K :=
      heightSeries_le_posUnipotent h g.2
    exact (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K (h + 1) hg) n).1 hn⟩

variable (K) in
abbrev HeightQuot
    (h : ℤ) : Type :=
  heightSeries F4.tag K h ⧸ (heightSeries F4.tag K (h + 1)).subgroupOf (heightSeries F4.tag K h)

instance instCommGroupHeightQuot
    (h : ℤ) : CommGroup (HeightQuot K h) :=
  { (inferInstance : Group (HeightQuot K h)) with
    mul_comm := fun q q' => by
      induction q using QuotientGroup.induction_on with
      | H x =>
        induction q' using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
            Subgroup.mem_subgroupOf]
          have e : (((x * y)⁻¹ * (y * x) : heightSeries F4.tag K h) :
              (Module.End K (RootModule F4.tag K))ˣ) =
                ⁅((y : (Module.End K (RootModule F4.tag K))ˣ))⁻¹,
                  ((x : (Module.End K (RootModule F4.tag K))ˣ))⁻¹⁆ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
            group
          rw [e]
          exact commutator_heightSeries_le_succ h
            (Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2)) }

theorem heightQuot_sq_eq_one
    [CharP K 2] {h : ℤ} (q : HeightQuot K h) : q ^ 2 = 1 := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      SubgroupClass.coe_pow]
    exact sq_mem_heightSeries_succ x.2

@[expose] def rootElt
    {h : ℤ} {α : Fin F4.tag.rank → ℤ} (hα : α ∈ heightSet h) :
    Multiplicative K →* HeightQuot K h where
  toFun c := QuotientGroup.mk ⟨pinnedX F4.tag K α (Multiplicative.toAdd c),
    pinnedX_mem_heightSeries hα _⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext (pinnedX_zero F4.tag K α)
  map_mul' c d := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (pinnedX_add F4.tag K α _ _)

theorem rootElt_apply
    {h : ℤ} {α : Fin F4.tag.rank → ℤ} (hα : α ∈ heightSet h) (c : K) :
    rootElt hα (Multiplicative.ofAdd c) =
      QuotientGroup.mk ⟨pinnedX F4.tag K α c, pinnedX_mem_heightSeries hα c⟩ :=
  rfl

theorem heightQuot_induction
    {h : ℤ} {P : HeightQuot K h → Prop}
    (hgen : ∀ (α : Fin F4.tag.rank → ℤ) (hα : α ∈ heightSet h) (c : K),
      P (rootElt hα (Multiplicative.ofAdd c)))
    (hone : P 1) (hmul : ∀ q q', P q → P q' → P (q * q')) (hinv : ∀ q, P q → P q⁻¹)
    (q : HeightQuot K h) : P q := by
  have hcl := heightSeries_eq_closure (K := K) h
  have key : ∀ (g : (Module.End K (RootModule F4.tag K))ˣ)
      (hg : g ∈ Subgroup.closure {g | ∃ α ∈ heightSet h, ∃ c : K, pinnedX F4.tag K α c = g})
      (hg₀ : g ∈ heightSeries F4.tag K h), P (QuotientGroup.mk ⟨g, hg₀⟩) := by
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

variable (a : ℕ)

theorem torusPair_conj_mem_rootSpan
    (t : Kˣ × Kˣ) {S : Set (Fin F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot F4.tag α) {x : (Module.End K (RootModule F4.tag K))ˣ}
    (hx : x ∈ rootSpan F4.tag K S) :
    torusPair a t * x * (torusPair a t)⁻¹ ∈ rootSpan F4.tag K S := by
  rw [rootSpan_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hα, c, rfl⟩ := hg
    rw [torusPair_conj_pinnedX a t (hS α hα)]
    exact Subgroup.subset_closure ⟨α, hα, _, rfl⟩
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have e : torusPair a t * (x * y) * (torusPair a t)⁻¹ =
        torusPair a t * x * (torusPair a t)⁻¹ * (torusPair a t * y * (torusPair a t)⁻¹) := by
      group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : torusPair a t * x⁻¹ * (torusPair a t)⁻¹ =
        (torusPair a t * x * (torusPair a t)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem torusPair_conj_mem_heightSeries
    (t : Kˣ × Kˣ) {h : ℤ}
    {x : (Module.End K (RootModule F4.tag K))ˣ} (hx : x ∈ heightSeries F4.tag K h) :
    torusPair a t * x * (torusPair a t)⁻¹ ∈ heightSeries F4.tag K h :=
  torusPair_conj_mem_rootSpan a t (fun _ hα => hα.1) hx

@[expose] def heightConj
    (h : ℤ) (t : Kˣ × Kˣ) :
    heightSeries F4.tag K h →* heightSeries F4.tag K h where
  toFun x := ⟨torusPair a t * x * (torusPair a t)⁻¹, torusPair_conj_mem_heightSeries a t x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_heightConj
    (h : ℤ) (t : Kˣ × Kˣ) (x : heightSeries F4.tag K h) :
    ((heightConj a h t x : heightSeries F4.tag K h) : (Module.End K (RootModule F4.tag K))ˣ) =
      torusPair a t * x * (torusPair a t)⁻¹ :=
  rfl

@[expose] def heightQuotSmul
    (h : ℤ) (t : Kˣ × Kˣ) : HeightQuot K h →* HeightQuot K h :=
  QuotientGroup.map _ _ (heightConj a h t) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_heightConj]
    exact torusPair_conj_mem_heightSeries a t hx

theorem heightQuotSmul_mk
    (h : ℤ) (t : Kˣ × Kˣ) (x : heightSeries F4.tag K h) :
    heightQuotSmul a h t (QuotientGroup.mk x) = QuotientGroup.mk (heightConj a h t x) :=
  QuotientGroup.map_mk _ _ _ _ _

theorem heightQuotSmul_rootElt
    {h : ℤ} (t : Kˣ × Kˣ) {α : Fin F4.tag.rank → ℤ}
    (hα : α ∈ heightSet h) (c : K) :
    heightQuotSmul a h t (rootElt hα (Multiplicative.ofAdd c)) =
      rootElt hα (Multiplicative.ofAdd ((torusWeight a α t : K) * c)) :=
  (heightQuotSmul_mk a h t _).trans (congrArg QuotientGroup.mk (Subtype.ext
    ((coe_heightConj a h t _).trans (torusPair_conj_pinnedX a t hα.1 c))))

theorem heightQuotSmul_one
    (h : ℤ) : heightQuotSmul (K := K) a h 1 = MonoidHom.id _ := by
  refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x => ?_)
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, heightQuotSmul_mk,
    MonoidHom.id_apply]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  rw [coe_heightConj, map_one, one_mul, inv_one, mul_one]

theorem heightQuotSmul_mul
    (h : ℤ) (s t : Kˣ × Kˣ) :
    heightQuotSmul (K := K) a h (s * t) = (heightQuotSmul a h s).comp (heightQuotSmul a h t) := by
  refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x => ?_)
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, heightQuotSmul_mk]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  rw [coe_heightConj, coe_heightConj, coe_heightConj, map_mul]
  group

@[expose, instance_reducible] def heightQuotAction
    (h : ℤ) :
    MulDistribMulAction (Kˣ × Kˣ) (HeightQuot K h) where
  smul t q := heightQuotSmul a h t q
  one_smul q := DFunLike.congr_fun (heightQuotSmul_one a h) q
  mul_smul s t q := DFunLike.congr_fun (heightQuotSmul_mul a h s t) q
  smul_mul t q q' := map_mul (heightQuotSmul a h t) q q'
  smul_one t := map_one (heightQuotSmul a h t)

theorem odd_card_torus [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Odd (Nat.card (Kˣ × Kˣ)) := by
  rw [Nat.card_prod, Nat.card_units, hK]
  have h1 : Odd (2 ^ (2 * a + 1) - 1) := by
    refine ⟨2 ^ (2 * a) - 1, ?_⟩
    have h2 : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  exact h1.mul h1

theorem sum_torusWeight_eq_zero
    [Finite K] [Fintype (Kˣ × Kˣ)] (ha : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α)
    (hαp : 0 < height α) : ∑ t : Kˣ × Kˣ, (torusWeight a α t : K) = 0 := by
  refine sum_hom_units_eq_zero ((Units.coeHom K).comp (torusWeight a α)) fun h1 => ?_
  refine torusWeight_ne_one a ha hK hα hαp (MonoidHom.ext fun t => Units.ext ?_)
  exact DFunLike.congr_fun h1 t

theorem heightQuot_prod_smul_eq_one
    [Finite K] [Fintype (Kˣ × Kˣ)] (ha : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {h : ℤ} (q : HeightQuot K h) :
    ∏ t : Kˣ × Kˣ, heightQuotSmul a h t q = 1 := by
  induction q using heightQuot_induction with
  | hgen α hα c =>
    simp only [heightQuotSmul_rootElt]
    rw [← map_prod, ← ofAdd_sum, ← Finset.sum_mul,
      sum_torusWeight_eq_zero a ha hK hα.1 hα.2.1, zero_mul, ofAdd_zero, map_one]
  | hone => simp
  | hmul q q' hq hq' => simp only [map_mul, Finset.prod_mul_distrib, hq, hq', mul_one]
  | hinv q hq => simp only [map_inv, Finset.prod_inv_distrib, hq, inv_one]

theorem mem_heightSeries_succ_of_forall
    [Finite K] [CharP K 2] (ha : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {h : ℤ} {x : (Module.End K (RootModule F4.tag K))ˣ}
    (hx : x ∈ heightSeries F4.tag K h)
    (hfix : ∀ t : Kˣ × Kˣ,
      (torusPair a t * x * (torusPair a t)⁻¹)⁻¹ * x ∈ heightSeries F4.tag K (h + 1)) :
    x ∈ heightSeries F4.tag K (h + 1) := by
  classical
  have := Fintype.ofFinite (Kˣ × Kˣ)
  set q : HeightQuot K h := QuotientGroup.mk ⟨x, hx⟩ with hq
  have hsmul : ∀ t, heightQuotSmul a h t q = q := fun t => by
    rw [hq, heightQuotSmul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hfix t
  have hprod := heightQuot_prod_smul_eq_one a ha hK q
  simp only [hsmul, Finset.prod_const, Finset.card_univ] at hprod
  obtain ⟨k, hk⟩ := odd_card_torus a hK
  rw [← Nat.card_eq_fintype_card, hk, pow_succ, pow_mul, heightQuot_sq_eq_one, one_pow,
    one_mul] at hprod
  rw [hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hprod
  exact hprod

theorem heightQuot_form_eq_zero
    [Finite K] [CharP K 2] (ha : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {h h' : ℤ} (B : HeightQuot K h → HeightQuot K h' → ZMod 2)
    (hB₁ : ∀ q₁ q₂ q', B (q₁ * q₂) q' = B q₁ q' + B q₂ q')
    (hB₂ : ∀ q q₁' q₂', B q (q₁' * q₂') = B q q₁' + B q q₂')
    (hBT : ∀ (t : Kˣ × Kˣ) q q', B (heightQuotSmul a h t q) (heightQuotSmul a h' t q') = B q q') :
    ∀ q q', B q q' = 0 := by
  have hB1 : ∀ q', B 1 q' = 0 := fun q' => by
    have h1 := hB₁ 1 1 q'
    rwa [mul_one, left_eq_add] at h1
  have hB1' : ∀ q, B q 1 = 0 := fun q => by
    have h1 := hB₂ q 1 1
    rwa [mul_one, left_eq_add] at h1
  have hroot : ∀ (α : Fin F4.tag.rank → ℤ) (hα : α ∈ heightSet h) (β : Fin F4.tag.rank → ℤ)
      (hβ : β ∈ heightSet h') (c d : K),
      B (rootElt hα (Multiplicative.ofAdd c)) (rootElt hβ (Multiplicative.ofAdd d)) = 0 := by
    intro α hα β hβ
    refine torusWeight_form_eq_zero a ha hK hα.1 hα.2.1 hβ.1 hβ.2.1
      (fun c d => B (rootElt hα (Multiplicative.ofAdd c)) (rootElt hβ (Multiplicative.ofAdd d)))
      (fun c₁ c₂ d => ?_) (fun c d₁ d₂ => ?_) (fun t c d => ?_)
    · rw [ofAdd_add, map_mul, hB₁]
    · rw [ofAdd_add, map_mul, hB₂]
    · rw [← heightQuotSmul_rootElt, ← heightQuotSmul_rootElt, hBT]
  have hleft : ∀ (β : Fin F4.tag.rank → ℤ) (hβ : β ∈ heightSet h') (d : K) (q : HeightQuot K h),
      B q (rootElt hβ (Multiplicative.ofAdd d)) = 0 := by
    intro β hβ d q
    induction q using heightQuot_induction with
    | hgen α hα c => exact hroot α hα β hβ c d
    | hone => exact hB1 _
    | hmul q q' hq hq' => rw [hB₁, hq, hq', add_zero]
    | hinv q hq =>
      have h1 := hB₁ q q⁻¹ (rootElt hβ (Multiplicative.ofAdd d))
      rwa [mul_inv_cancel, hB1, hq, zero_add, eq_comm] at h1
  intro q q'
  induction q' using heightQuot_induction with
  | hgen β hβ d => exact hleft β hβ d q
  | hone => exact hB1' q
  | hmul q₁ q₂ h₁ h₂ => rw [hB₂, h₁, h₂, add_zero]
  | hinv q₁ h₁ =>
    have h1 := hB₂ q q₁ q₁⁻¹
    rwa [mul_inv_cancel, hB1', h₁, zero_add, eq_comm] at h1

end CFSG.LieType.Ree.LargeReeCover
