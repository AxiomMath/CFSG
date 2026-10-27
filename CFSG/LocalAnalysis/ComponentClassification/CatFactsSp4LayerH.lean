module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerG
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerD
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerE

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem normal_subgroupOf_map (φ : G ≃* G') {R E : Subgroup G} (hRE : R ≤ E)
    (h : (R.subgroupOf E).Normal) :
    ((R.map φ.toMonoidHom).subgroupOf (E.map φ.toMonoidHom)).Normal := by
  let ψ : E ≃* E.map φ.toMonoidHom := E.equivMapOfInjective φ.toMonoidHom φ.injective
  have key : (R.subgroupOf E).map ψ.toMonoidHom =
      (R.map φ.toMonoidHom).subgroupOf (E.map φ.toMonoidHom) := by
    ext ⟨x, hx⟩
    rw [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨⟨c, hc⟩, hcR, hceq⟩
      exact ⟨c, hcR, congrArg Subtype.val hceq⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hRE hm⟩, hm, rfl⟩
  rw [← key]
  exact h.map _ ψ.surjective

theorem card_map_equiv (φ : G ≃* G') (E : Subgroup G) :
    Nat.card (E.map φ.toMonoidHom) = Nat.card E :=
  (Nat.card_congr (E.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm

theorem relIndex_map_equiv [Finite G] (φ : G ≃* G') {R E : Subgroup G} (hRE : R ≤ E) :
    (R.map φ.toMonoidHom).relIndex (E.map φ.toMonoidHom) = R.relIndex E := by
  have h1 := Subgroup.relIndex_mul_card (H := R) (K := E)
  have h2 := Subgroup.relIndex_mul_card (H := R.map φ.toMonoidHom) (K := E.map φ.toMonoidHom)
  rw [inf_of_le_left hRE] at h1
  rw [inf_of_le_left (map_mono hRE), card_map_equiv, card_map_equiv] at h2
  have hpos : 0 < Nat.card R := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)

theorem relIndex_eq_card_of_simple [Finite G] {E R R₁ : Subgroup G} (hE : IsSimpleGroup E)
    (hEc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) (hEe : Even (Nat.card E)) (hRE : R ≤ E)
    (hRn : (R.subgroupOf E).Normal) (hR₁R : R₁ ≤ R) (hR₁n : (R₁.subgroupOf R).Normal)
    (hR₁o : Odd (Nat.card R₁)) (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k ∈ R₁) :
    R.relIndex E = Nat.card E := by
  rw [eq_bot_of_simple hE hEc hEe hRE hRn hR₁R hR₁n hR₁o hR2, Subgroup.relIndex_bot_left]

theorem simple_data_map (φ : G ≃* G') {E₀ : Subgroup G} (hE : IsSimpleGroup E₀)
    (hEc : ∃ x ∈ E₀, ∃ y ∈ E₀, x * y ≠ y * x) :
    IsSimpleGroup (E₀.map φ.toMonoidHom) ∧
      ∃ x ∈ E₀.map φ.toMonoidHom, ∃ y ∈ E₀.map φ.toMonoidHom, x * y ≠ y * x := by
  refine ⟨(E₀.equivMapOfInjective φ.toMonoidHom φ.injective).symm.isSimpleGroup, ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hEc
  refine ⟨φ x, mem_map_of_mem _ hx, φ y, mem_map_of_mem _ hy, fun h => hxy ?_⟩
  apply φ.injective
  rw [map_mul, map_mul]
  exact h

end Transport

variable {K : Type} [Field K]

theorem isQuasisimple_Lsub [Finite K] (h4 : 4 ≤ Nat.card K) : CFSG.IsQuasisimple (Lsub K) := by
  have hL : Lsub K = ((proj 2 K).comp (diagSL K)).range := by
    rw [Lsub, MonoidHom.range_comp]
  rw [hL]
  exact isQuasisimple_range_comp h4 (diagSL K) (ker_proj_comp_diagSL (K := K))

theorem isQuasisimple_JI [Finite K] {a : K} (ha : a ≠ 0) (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (JI ha) := by
  have hJ : JI ha = ((proj 2 K).comp (gI ha)).range := by
    rw [JI, MonoidHom.range_comp]
  rw [hJ]
  exact isQuasisimple_range_comp h4 (gI ha) (ker_proj_comp_gI ha)

theorem card_Lsub [Finite K] (hodd : Odd (Nat.card K)) :
    Nat.card (Lsub K) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
  rw [Nat.card_congr (LtoStated K).toEquiv, card_statedProj_statedSL_two_odd hodd]

theorem card_JI [Finite K] (hodd : Odd (Nat.card K)) {a : K} (ha : a ≠ 0) :
    Nat.card (JI ha) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
  rw [← Nat.card_congr (JIEquiv ha).toEquiv,
    Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 K).toEquiv,
    card_statedProj_statedSL_two_odd hodd]

theorem ordL2_lt_of_two_mul {q n : ℕ} (hq : 3 ≤ q) (h : n * 2 = q ^ 2 * ((q ^ 2) ^ 2 - 1)) :
    q * (q ^ 2 - 1) / 2 < n := by
  have h1 : q * (q ^ 2 - 1) < q ^ 2 * ((q ^ 2) ^ 2 - 1) := by
    have hq2 : 1 ≤ q ^ 2 := by nlinarith
    have hq4 : q ^ 2 - 1 < (q ^ 2) ^ 2 - 1 := by
      have : q ^ 2 < (q ^ 2) ^ 2 := by nlinarith
      omega
    calc q * (q ^ 2 - 1) ≤ q * ((q ^ 2) ^ 2 - 1) := Nat.mul_le_mul_left _ hq4.le
      _ < q ^ 2 * ((q ^ 2) ^ 2 - 1) := by
          apply Nat.mul_lt_mul_of_pos_right (by nlinarith)
          have : 1 < (q ^ 2) ^ 2 := by nlinarith
          omega
  have : q * (q ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) := Nat.div_le_self _ _
  omega

theorem ordL2_lt_P {q n : ℕ} (hq : 3 ≤ q)
    (h : n * 2 = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) : q * (q ^ 2 - 1) / 2 < n := by
  have hq2 : 1 ≤ q ^ 2 - 1 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have hq4 : 2 ≤ q ^ 4 - 1 := by
    have : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    omega
  have hq' : q ≤ q ^ 4 := Nat.le_self_pow (by norm_num) q
  have h1 : q * (q ^ 2 - 1) < q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    have hB : 0 < q ^ 4 * (q ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
    calc q * (q ^ 2 - 1) ≤ q ^ 4 * (q ^ 2 - 1) := Nat.mul_le_mul_right _ hq'
      _ < 2 * (q ^ 4 * (q ^ 2 - 1)) := lt_mul_of_one_lt_left hB (by norm_num)
      _ = q ^ 4 * ((q ^ 2 - 1) * 2) := by ring
      _ ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hq4)
  have : q * (q ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) := Nat.div_le_self _ _
  omega

theorem ordL2_lt_field {k n : ℕ} (hk : 3 ≤ k)
    (h : n * 2 = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1))) :
    k ^ 2 * ((k ^ 2) ^ 2 - 1) / 2 < n := by
  have e : (k ^ 2) ^ 2 = k ^ 4 := by ring
  rw [e]
  have hk4 : 1 ≤ k ^ 4 - 1 := by
    have : 3 ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
    omega
  have hk2 : 8 ≤ k ^ 2 - 1 := by
    have : 9 ≤ k ^ 2 := by nlinarith
    omega
  have h1 : k ^ 2 * (k ^ 4 - 1) < k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := by
    have hk2' : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hA : k ^ 2 * (k ^ 4 - 1) ≤ k ^ 4 * (k ^ 4 - 1) := Nat.mul_le_mul_right _ hk2'
    have hB : 0 < k ^ 4 * (k ^ 4 - 1) := Nat.mul_pos (by positivity) (by omega)
    calc k ^ 2 * (k ^ 4 - 1) ≤ k ^ 4 * (k ^ 4 - 1) := hA
      _ < 8 * (k ^ 4 * (k ^ 4 - 1)) := lt_mul_of_one_lt_left hB (by norm_num)
      _ = k ^ 4 * (8 * (k ^ 4 - 1)) := by ring
      _ ≤ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk2)
  have : k ^ 2 * (k ^ 4 - 1) / 2 ≤ k ^ 2 * (k ^ 4 - 1) := Nat.div_le_self _ _
  omega

theorem layer_P {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (hs : IsSimpleGroup (StatedProj (StatedSp 2 K)))
    (B : gsp 2 K) (hB : ∀ l : K, l ^ 2 ≠ (multiplierUnit B : K))
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα2 : α * α = 1)
    {R R₁ : Subgroup (StatedProj (StatedSp 2 K))} (hRE : R ≤ layerOf (fixOf α))
    (hRn : (R.subgroupOf (layerOf (fixOf α))).Normal) (hR₁R : R₁ ≤ R)
    (hR₁n : (R₁.subgroupOf R).Normal) (hR₁o : Odd (Nat.card R₁))
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k ∈ R₁)
    (hidx : R.relIndex (layerOf (fixOf α)) ≤ p ^ f * ((p ^ f) ^ 2 - 1) / 2) :
    R.relIndex (layerOf (fixOf α)) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      ∃ y ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range ⊔ zpowers (conjAut 2 K B),
        y * α = α * y ∧ (∀ t ∈ layerOf (fixOf α), y t = t) ∧
          (orderOf y = 4 ∨ (Odd (orderOf y) ∧ y ≠ 1)) := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have h5K : 5 ≤ Nat.card K := by omega
  have hq3 : 3 ≤ p ^ f := by omega
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  set E := layerOf (fixOf α) with hEdef
  set I := (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range with hI
  have hsimple : ∀ (E₀ : Subgroup (StatedProj (StatedSp 2 K))) (φ : MulAut (StatedProj
      (StatedSp 2 K))), E₀.map φ.toMonoidHom = E → IsSimpleGroup E₀ →
      (∃ x ∈ E₀, ∃ y ∈ E₀, x * y ≠ y * x) → Even (Nat.card E₀) →
      R.relIndex E = Nat.card E₀ := by
    intro E₀ φ hφ hE hEc hEe
    obtain ⟨hE', hEc'⟩ := simple_data_map φ hE hEc
    rw [hφ] at hE' hEc'
    have hEe' : Even (Nat.card E) := by rw [← hφ, card_map_equiv]; exact hEe
    rw [relIndex_eq_card_of_simple hE' hEc' hEe' hRE hRn hR₁R hR₁n hR₁o hR2, ← hφ,
      card_map_equiv]
  have hconj_y : ∀ (β α₀ y₀ : MulAut (StatedProj (StatedSp 2 K))), β ∈ I →
      (∀ x, β (α x) = α₀ (β x)) → y₀ ∈ I ⊔ zpowers (conjAut 2 K B) → y₀ * α₀ = α₀ * y₀ →
      (∀ t ∈ E.map β.toMonoidHom, y₀ t = t) →
      ∃ y ∈ I ⊔ zpowers (conjAut 2 K B), y * α = α * y ∧ (∀ t ∈ E, y t = t) ∧
        orderOf y = orderOf y₀ := by
    intro β α₀ y₀ hβ hcomm hy₀ hyα hyE
    have hαβ : β * α = α₀ * β := MulEquiv.ext fun x => hcomm x
    have hα' : β⁻¹ * α₀ * β = α := by
      rw [mul_assoc, ← hαβ, ← mul_assoc, inv_mul_cancel, one_mul]
    refine ⟨β⁻¹ * y₀ * β, ?_, ?_, ?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem (mem_sup_left hβ)) hy₀) (mem_sup_left hβ)
    · calc β⁻¹ * y₀ * β * α = β⁻¹ * (y₀ * α₀) * β := by
            rw [← hα']
            group
        _ = β⁻¹ * (α₀ * y₀) * β := by rw [hyα]
        _ = β⁻¹ * α₀ * β * (β⁻¹ * y₀ * β) := by group
        _ = α * (β⁻¹ * y₀ * β) := by rw [hα']
    · intro t ht
      have := hyE (β t) (mem_map_of_mem _ ht)
      simp only [MulAut.mul_apply]
      change β⁻¹ (y₀ (β t)) = t
      rw [this, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    · have : β⁻¹ * y₀ * β = MulAut.conj β⁻¹ y₀ := by
        rw [MulAut.conj_apply, inv_inv]
      rw [this, MulEquiv.orderOf_eq]
  by_cases hα1 : α = 1
  · exfalso
    subst hα1
    have hE : E = ⊤ := by rw [hEdef, fixOf_one, layerOf_top h2 h4 hs]
    have htop : IsSimpleGroup (⊤ : Subgroup (StatedProj (StatedSp 2 K))) :=
      Subgroup.topEquiv.isSimpleGroup
    obtain ⟨x, y, hxy⟩ := exists_noncomm_P h2 h4
    have hr := hsimple ⊤ 1 (by rw [hE]; exact Subgroup.map_id ⊤ |>.trans rfl) htop
      ⟨x, mem_top x, y, mem_top y, hxy⟩ (by rw [Subgroup.card_top]; exact even_card_P h2)
    rw [Subgroup.card_top] at hr
    have hP := two_mul_card_P h2
    rw [hK] at hP
    have := ordL2_lt_P hq3 hP
    omega
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, hlin, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    have hα' : α = conjAut 2 K A := by rw [hα, map_one, mul_one]
    have hAA := mul_self_of_rep A d hd
    have hμ := multiplierUnit_spec A
    by_cases hsq : ∃ l : K, l ^ 2 = (multiplierUnit A : K)
    ·
      obtain ⟨u, hu⟩ := conjAut_mem_range_of_sq A hsq.choose_spec
      have hαu : α = MulAut.conj u := by rw [hα', ← hu]
      have hu1 : u ≠ 1 := fun h => hα1 (by rw [hαu, h, map_one])
      have hu2 : u * u = 1 := by
        have hc : MulAut.conj (u * u) = 1 := by rw [map_mul, ← hαu, hα2]
        apply eq_one_of_mem_center_P h2 h4 hs
        rw [mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ g) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * (u * u) = u * u * g * (u * u)⁻¹ * (u * u) := by rw [this]
          _ = u * u * g := by group
      have huo : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
      obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd huo
      set φ := MulAut.conj g⁻¹ with hφdef
      have hφI : φ ∈ I := ⟨g⁻¹, rfl⟩
      have hφu : φ u = g⁻¹ * u * g := by rw [hφdef, MulAut.conj_apply, inv_inv]
      have hcomm : ∀ x, φ (α x) = MulAut.conj (φ u) (φ x) := fun x => by
        rw [hαu]
        exact conj_comm φ u x
      have hEmap : E.map φ.toMonoidHom = layerOf (fixOf (MulAut.conj (φ u))) := by
        rw [hEdef, map_layerOf, map_fixOf_of_comm hcomm]
      rcases hg with h | h
      ·
        exfalso
        rw [hφu, h, fixOf_conj, layerOf_u1 hodd h4, E1_sup_E2 h2] at hEmap
        have hR'X : R.map φ.toMonoidHom ≤ X0 K := by rw [← hEmap]; exact map_mono hRE
        have hR'n := normal_subgroupOf_map φ hRE hRn
        rw [hEmap] at hR'n
        have hgt := relIndex_gt_of_u1 hodd h5K hR'X hR'n (map_mono hR₁R)
          (normal_subgroupOf_map φ hR₁R hR₁n) (by rw [card_map_equiv]; exact hR₁o)
          (by
            rintro _ ⟨r, hr, rfl⟩
            obtain ⟨k, hk⟩ := hR2 r hr
            exact ⟨k, by rw [← map_pow]; exact mem_map_of_mem _ hk⟩)
        rw [← hEmap, relIndex_map_equiv φ hRE, hK] at hgt
        omega
      ·
        rw [hφu, h, fixOf_conj, layerOf_u2 hodd h4] at hEmap
        have hEL : (Lsub K).map φ.symm.toMonoidHom = E := by
          rw [← hEmap, Subgroup.map_map]
          convert Subgroup.map_id E
          ext x
          simp
        have hr := hsimple (Lsub K) φ.symm hEL (isSimpleGroup_Lsub h4)
          (exists_mul_ne_of_isQuasisimple (isQuasisimple_Lsub h4))
          (even_card_of_mem w0_mem_Lsub orderOf_w0)
        rw [card_Lsub hodd, hK] at hr
        refine ⟨hr, ?_⟩
        have hcomm' : ∀ x, φ (α x) = MulAut.conj (u2 K) (φ x) := fun x => by
          rw [hcomm, hφu, h]
        obtain ⟨y, hyI, hyα, hyE, hyo⟩ := hconj_y φ (MulAut.conj (u2 K)) (y2 h2) hφI hcomm'
          (conjAut_mem_inn_sup B hB (qJgsp h2)) (y2_comm h2)
          (by rw [hEmap]; exact fun t ht => y2_Lsub h2 ht)
        exact ⟨y, hyI, hyα, hyE, Or.inl (by rw [hyo, orderOf_y2 h2 h4 hs])⟩
    · push Not at hsq
      rcases eq_or_eq_neg_multiplier A hAA with hdm | hdm
      ·
        exfalso
        have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
        have hμd : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
            formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
              (d : K) • formJ 2 K := by rw [hdm]; exact hμ
        obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        have hc := card_center_fixOf_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        have hθα : ∀ g, α (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
          rw [hα', conjAut_proj]
        have hZ : ∀ z ∈ spScalars 2 K, conjSp 2 K A z = z := fun z hz => conjSp_scalar A hz
        have h4dvd : 4 ∣ Nat.card (fixOf (conjSp 2 K A)) := by
          rw [hcard]
          have : 4 ∣ ((p ^ f) ^ 2) ^ 2 - 1 := by
            have ho : Odd ((p ^ f) ^ 2) := (hK ▸ hodd).pow
            obtain ⟨r, hr⟩ := ho
            refine ⟨r ^ 2 + r, ?_⟩
            rw [hr]
            have : (2 * r + 1) ^ 2 = 4 * (r ^ 2 + r) + 1 := by ring
            omega
          exact Dvd.dvd.mul_left this _
        have hEN := layerOf_fixOf_eq h2 (conjSp 2 K A) hθα hZ hQ h4dvd
        have hNs := isSimpleGroup_map_fixOf h2 (conjSp 2 K A) hZ hQ hc
        have hNq : CFSG.IsQuasisimple ((fixOf (conjSp 2 K A)).map (proj 2 K)) :=
          LocalCores.isQuasisimple_of_surjective hQ (fixProj _)
            ((proj 2 K).subgroupMap_surjective _) (ker_fixProj_le_center _)
        have hNc := card_map_fixOf_mul_two h2 (conjSp 2 K A) hZ
        rw [hcard] at hNc
        have hNe : Even (Nat.card ((fixOf (conjSp 2 K A)).map (proj 2 K))) := by
          obtain ⟨m, hm⟩ := h4dvd
          rw [hcard] at hm
          exact ⟨m, by omega⟩
        have hr := hsimple _ 1 (by rw [← hEN]; exact Subgroup.map_id _ |>.trans rfl) hNs
          (exists_mul_ne_of_isQuasisimple hNq) hNe
        have := ordL2_lt_of_two_mul hq3 hNc
        omega
      ·
        have ha : (d : K) ≠ 0 := d.ne_zero
        have hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
            formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
              (-(d : K)) • formJ 2 K := by
          rw [hμ, hdm, neg_neg]
        have hna : ∀ l : K, l ^ 2 ≠ -(d : K) := by rw [hdm, neg_neg]; exact hsq
        obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
        have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
            (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, coe_aIgsp]
          exact hg
        set β := (MulAut.conj (proj 2 K g))⁻¹ with hβdef
        have hβI : β ∈ I := inv_mem ⟨proj 2 K g, rfl⟩
        have hcomm : ∀ x, β (α x) = alphaI ha (β x) := fun x => by
          rw [hα']
          exact conj_inv_conjAut A (aIgsp ha) g hGL x
        have hEmap : E.map β.toMonoidHom = JI ha := by
          rw [hEdef, map_layerOf, map_fixOf_of_comm hcomm]
          exact layerOf_alphaI ha h2 h4
        have hEJ : (JI ha).map β.symm.toMonoidHom = E := by
          rw [← hEmap, Subgroup.map_map]
          convert Subgroup.map_id E
          ext x
          simp
        have hJmem : proj 2 K (gI ha J₁SL) ∈ JI ha := ⟨_, ⟨J₁SL, rfl⟩, rfl⟩
        have hr := hsimple (JI ha) β.symm hEJ (isSimpleGroup_JI ha h4)
          (exists_mul_ne_of_isQuasisimple (isQuasisimple_JI ha h4))
          (even_card_of_mem hJmem (orderOf_proj_J₁SL (gI ha) (ker_proj_comp_gI ha)))
        rw [card_JI hodd ha, hK] at hr
        refine ⟨hr, ?_⟩
        obtain ⟨y₀, hy₀I, hy₀α, hy₀E, hy₀o, hy₀1⟩ := exists_y_alphaI ha h2 h5K hna hs
        obtain ⟨y, hyI, hyα, hyE, hyo⟩ := hconj_y β (alphaI ha) y₀ hβI hcomm
          (mem_sup_left hy₀I) hy₀α (by rw [hEmap]; exact hy₀E)
        refine ⟨y, hyI, hyα, hyE, Or.inr ⟨by rw [hyo]; exact hy₀o, fun h1 => hy₀1 ?_⟩⟩
        rw [h1, orderOf_one] at hyo
        exact orderOf_eq_one_iff.mp hyo.symm
  ·
    exfalso
    have hθα : ∀ g, α (proj 2 K g) = proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) g) := fun g => by
      rw [hα]
      rfl
    obtain ⟨hQ, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
    have hc := card_center_fixOf_field hodd A σ hσ2 hσ d hd
    have hZ : ∀ z ∈ spScalars 2 K, (conjSp 2 K A * fieldSp 2 K σ) z = z :=
      fun z hz => conjSp_fieldSp_scalar A σ hz
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk, hK] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) with hkdef
    have hkodd : Odd k := (Nat.odd_mul.mp (by rw [← sq, ← hKk]; exact hK ▸ hodd)).1
    have hk3 : 3 ≤ k := by
      by_contra hlt
      push Not at hlt
      obtain ⟨r, hr⟩ := hkodd
      have hk1 : k = 1 := by omega
      have hq1 : p ^ f = 1 := by rw [hKk, hk1, one_pow]
      omega
    have h4dvd : 4 ∣ Nat.card (fixOf (conjSp 2 K A * fieldSp 2 K σ)) := by
      rw [hcard]
      have : 4 ∣ k ^ 2 - 1 := by
        obtain ⟨r, hr⟩ := hkodd
        refine ⟨r ^ 2 + r, ?_⟩
        rw [hr]
        have : (2 * r + 1) ^ 2 = 4 * (r ^ 2 + r) + 1 := by ring
        omega
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right this _) _
    have hEN := layerOf_fixOf_eq h2 _ hθα hZ hQ h4dvd
    have hNs := isSimpleGroup_map_fixOf h2 _ hZ hQ hc
    have hNq : CFSG.IsQuasisimple ((fixOf (conjSp 2 K A * fieldSp 2 K σ)).map (proj 2 K)) :=
      LocalCores.isQuasisimple_of_surjective hQ (fixProj _)
        ((proj 2 K).subgroupMap_surjective _) (ker_fixProj_le_center _)
    have hNc := card_map_fixOf_mul_two h2 _ hZ
    rw [hcard] at hNc
    have hNe : Even (Nat.card ((fixOf (conjSp 2 K A * fieldSp 2 K σ)).map (proj 2 K))) := by
      obtain ⟨m, hm⟩ := h4dvd
      rw [hcard] at hm
      exact ⟨m, by omega⟩
    have hr := hsimple _ 1 (by rw [← hEN]; exact Subgroup.map_id _ |>.trans rfl) hNs
      (exists_mul_ne_of_isQuasisimple hNq) hNe
    have hlt := ordL2_lt_field hk3 hNc
    rw [hKk, hr] at hidx
    exact absurd hidx (not_le.mpr hlt)

end CFSG.ComponentClassification.CatFactsSp4
