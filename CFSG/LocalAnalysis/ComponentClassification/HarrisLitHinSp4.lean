module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSp4G
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinU42
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSp4H
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Layer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open CFSG.ComponentClassification.CatFactsSp4

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]

omit [Finite Y] in
theorem hinConcl_psp4_ge_five {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hY : StatedClassicalModel Y .PSp 2 ℓ e) (h5 : 5 ≤ ℓ ^ e) {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    HinConcl Y p m τ := by
  classical
  obtain ⟨⟨-, he, -⟩, K, _, _, hK, ⟨φ₀⟩⟩ := hY
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hℓ hℓ2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 K)) := φ₀.symm.isSimpleGroup
  set α := MulAut.congr φ₀ τ with hαdef
  have hcomm0 : ∀ x, φ₀ (τ x) = α (φ₀ x) := fun x => by
    rw [hαdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hfix0 : (fixedPoints τ).map φ₀.toMonoidHom = fixOf α := map_fixOf_of_comm hcomm0
  have hτ2 : τ * τ = 1 := by
    have := pow_orderOf_eq_one τ
    rwa [hτ, pow_two] at this
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hτ2, map_one]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    norm_num at hτ
  have hα1 : α ≠ 1 := fun h => hτ1 ((MulAut.congr φ₀).injective (by rw [← hαdef, h, map_one]))
  have hlay : (GSThmB.layerIn (fixedPoints τ)).map φ₀.toMonoidHom = layerOf (fixOf α) := by
    rw [layerIn_eq_layerOf, map_layerOf, hfix0]
  let eL : ↥(GSThmB.layerIn (fixedPoints τ)) ≃* ↥(layerOf (fixOf α)) :=
    ((GSThmB.layerIn (fixedPoints τ)).equivMapOfInjective _ φ₀.injective).trans
      (MulEquiv.subgroupCongr hlay)
  have hLm : Blueprint.LieModel ↥(layerOf (fixOf α)) .PSL 2 p m :=
    lieModel_psl2_of_mulEquiv eL.symm hL
  have hcc : ∀ t : Y, MulAut.congr φ₀ (MulAut.conj t) = MulAut.conj (φ₀ t) := fun t =>
    MulEquiv.ext fun x => by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
  have hinn : τ ∈ innAut Y ↔ α ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨φ₀ t, (hcc t).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨φ₀.symm x, (MulAut.congr φ₀).injective ?_⟩
      rw [hcc, MulEquiv.apply_symm_apply, hx]
  have hrank : ∀ (β α₀ : MulAut (StatedProj (StatedSp 2 K))), (∀ x, β (α x) = α₀ (β x)) →
      ∀ E : Subgroup (StatedProj (StatedSp 2 K)), E ≤ fixOf α₀ → ElemTwo E → ∀ r : ℕ,
        2 ^ r < Nat.card E → ¬ GH74.SectionalTwoRankLE ↥(fixedPoints τ) r := by
    intro β α₀ hβ E hE hE2 r hr
    refine not_sectionalTwoRankLE_of_equiv (φ₀.trans β) ?_ hE hE2 hr
    rw [← map_fixOf_of_comm hβ, ← hfix0, Subgroup.map_map]
    rfl
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
      set β := MulAut.conj g⁻¹ with hβdef
      have hβu : β u = g⁻¹ * u * g := by rw [hβdef, MulAut.conj_apply, inv_inv]
      have hcomm : ∀ x, β (α x) = MulAut.conj (β u) (β x) := fun x => by
        rw [hαu]
        exact conj_comm β u x
      rcases hg with h | h
      ·
        exfalso
        have hEmap : (layerOf (fixOf α)).map β.toMonoidHom = X0 K := by
          rw [map_layerOf, map_fixOf_of_comm hcomm, hβu, h, fixOf_conj, layerOf_u1 hodd h4,
            E1_sup_E2 h2]
        let eX : ↥(layerOf (fixOf α)) ≃* ↥(X0 K) :=
          ((layerOf (fixOf α)).equivMapOfInjective _ β.injective).trans
            (MulEquiv.subgroupCongr hEmap)
        have hXs : IsSimpleGroup ↥(X0 K) := by
          have := isSimpleGroup_of_lieModel_psl2 hLm
          exact eX.symm.isSimpleGroup
        have hXnab : ∃ a b : ↥(X0 K), a * b ≠ b * a := by
          obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 hLm
          exact ⟨eX a, eX b, fun h' => hab (eX.injective (by rw [map_mul, map_mul, h']))⟩
        have hZ := CatLeaf.center_eq_bot_of_simple hXnab
        have hu1X : u1 K ∈ X0 K := E1_le_X0 h2 u1_mem_E1
        have hc : (⟨u1 K, hu1X⟩ : ↥(X0 K)) ∈ center ↥(X0 K) := by
          rw [mem_center_iff]
          intro y
          apply Subtype.ext
          exact mem_centralizer_singleton_iff.mp (X0_le_centralizer y.2)
        rw [hZ, mem_bot] at hc
        exact u1_ne_one h2 (congrArg Subtype.val hc)
      ·
        refine hinConcl_of_rank (fun _ => ?_)
          (fun hout => (hout (hinn.mpr ⟨u, hαu.symm⟩)).elim)
        obtain ⟨E, hE, hE2, hE16⟩ := exists_elemTwo_u2 hodd h4
        refine hrank β (MulAut.conj (u2 K)) ?_ E (by rw [fixOf_conj]; exact hE) hE2 3
          (by omega)
        intro x
        rw [hcomm, hβu, h]
    ·
      push Not at hsq
      have hout : τ ∉ innAut Y := fun hτi =>
        conjAut_not_mem_range_conj A hsq (hα' ▸ hinn.mp hτi)
      refine hinConcl_of_rank (fun hτi => (hout hτi).elim) (fun _ => ?_)
      rcases eq_or_eq_neg_multiplier A hAA with hdm | hdm
      ·
        have hd0 : (d : K) ≠ 0 := d.ne_zero
        have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
        have hμd : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
            formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
              (d : K) • formJ 2 K := by rw [hdm]; exact hμ
        obtain ⟨g, hg⟩ := GSThmB.Cat7E6.exists_frame_typeII h2 hd0 hdsq hμd hAA
        have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
            (g : GL (Fin 2 ⊕ Fin 2) K) * ((b0gsp hd0 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, coe_b0gsp]
          exact hg
        obtain ⟨E, hE, hE2, hE8⟩ := exists_elemTwo_b0 hodd h4 hd0
        refine hrank (MulAut.conj (proj 2 K g))⁻¹ _ ?_ E hE hE2 2 (by omega)
        intro x
        rw [hα']
        exact conj_inv_conjAut A (b0gsp hd0) g hGL x
      ·
        have ha : (d : K) ≠ 0 := d.ne_zero
        have hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
            formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
              (-(d : K)) • formJ 2 K := by
          rw [hμ, hdm, neg_neg]
        obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
        have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
            (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, coe_aIgsp]
          exact hg
        obtain ⟨E, hE, hE2, hE8⟩ := exists_elemTwo_alphaI hodd h4 ha
        refine hrank (MulAut.conj (proj 2 K g))⁻¹ (alphaI ha) ?_ E hE hE2 2 (by omega)
        intro x
        rw [hα']
        exact conj_inv_conjAut A (aIgsp ha) g hGL x
  ·
    exfalso
    have hθα : ∀ g, α (proj 2 K g) = proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) g) := fun g => by
      rw [hα]
      rfl
    obtain ⟨hQ, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
    have hZ : ∀ z ∈ spScalars 2 K, (conjSp 2 K A * fieldSp 2 K σ) z = z :=
      fun z hz => conjSp_fieldSp_scalar A σ hz
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk, hK] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) with hkdef
    have hk3 : 3 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : k ^ 2 ≤ 4 := by nlinarith
      omega
    have h4dvd : 4 ∣ Nat.card (fixOf (conjSp 2 K A * fieldSp 2 K σ)) := by
      have hkodd : Odd k := by
        have : Odd (k ^ 2) := by rw [← hKk]; exact (hℓ.odd_of_ne_two hℓ2).pow
        rw [pow_two] at this
        exact (Nat.odd_mul.mp this).1
      rw [hcard]
      have : 4 ∣ k ^ 2 - 1 := by
        obtain ⟨r, hr⟩ := hkodd
        refine ⟨r ^ 2 + r, ?_⟩
        rw [hr]
        have : (2 * r + 1) ^ 2 = 4 * (r ^ 2 + r) + 1 := by ring
        omega
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right this _) _
    have hEN := layerOf_fixOf_eq h2 _ hθα hZ hQ h4dvd
    have hNc := card_map_fixOf_mul_two h2 _ hZ
    rw [hcard, ← hEN] at hNc
    exact false_of_field_order hℓ hℓ2 hp hp2 hm hKk.symm hk3 (by
      rw [← hNc, card_mul_two_of_lieModel_psl2 hp2 h16 hLm])

theorem hinConcl_psp4 (hnab : ∃ a b : Y, a * b ≠ b * a) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hY : StatedClassicalModel Y .PSp 2 ℓ e) {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    HinConcl Y p m τ := by
  obtain ⟨⟨-, he, -, hne⟩, -⟩ := id hY
  by_cases h3 : ℓ ^ e = 3
  · have hℓ3 : ℓ = 3 := by
      have : ℓ ∣ 3 := h3 ▸ dvd_pow_self ℓ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp this
    subst hℓ3
    have he1 : e = 1 := by
      rcases Nat.lt_or_ge e 2 with h | h
      · omega
      · have : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) h
        omega
    subst he1
    exact hinConcl_psp_four_three hnab hY hp hp2 hm h16 hτ hL
  · have h5 : 5 ≤ ℓ ^ e := by
      have hℓ3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
      have h3' : 3 ≤ ℓ ^ e := le_trans hℓ3 (Nat.le_self_pow (by omega) ℓ)
      have hodd : Odd (ℓ ^ e) := (hℓ.odd_of_ne_two hℓ2).pow
      obtain ⟨r, hr⟩ := hodd
      omega
    exact hinConcl_psp4_ge_five hℓ hℓ2 hY h5 hp hp2 hm h16 hτ hL

end CFSG.ComponentClassification.HarrisLit.Hin
