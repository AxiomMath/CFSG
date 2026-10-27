module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinDesc
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinThreeLevi

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem LinA.cyclic_of_fixing_perfect_conj (κ : MulAut (projectiveSL 3 K))
    (J D : Subgroup (projectiveSL 3 K))
    (hκ : J.map κ.toMonoidHom = projStabilizer (flagSpace 3 K 1)) (hDp : ⁅D, D⁆ = D) (hDJ : D ≤ J)
    (s : projectiveSL 3 K) (hsD : s ∈ D)
    (hs : orderOf s = 3 ^ padicValNat 3 (Nat.card K ^ 2 - 1))
    (U : Subgroup (MulAut (projectiveSL 3 K))) (hU3 : IsPGroup 3 U)
    (hJ : ∀ α ∈ U, J.map α.toMonoidHom = J) (hD : ∀ α ∈ U, ∀ d ∈ D, α d = d) : IsCyclic U := by
  set c : MulAut (MulAut (projectiveSL 3 K)) := MulAut.conj κ with hc
  set U' : Subgroup (MulAut (projectiveSL 3 K)) := U.map c.toMonoidHom with hU'
  have hcyc : IsCyclic U' := by
    refine LinA.cyclic_of_fixing_perfect (D.map κ.toMonoidHom) ?_ ?_ (κ s) ⟨s, hsD, rfl⟩ ?_ U' ?_ ?_ ?_
    · rw [← Subgroup.map_commutator, hDp]
    · rw [← hκ]; exact Subgroup.map_mono hDJ
    · rw [MulEquiv.orderOf_eq]; exact hs
    · exact hU3.map c.toMonoidHom
    · rintro _ ⟨α, hα, rfl⟩
      rw [← hκ]
      rw [Subgroup.map_map, MulEquiv.coe_toMonoidHom]
      have h1 : ((c α : MulAut (projectiveSL 3 K)).toMonoidHom).comp κ.toMonoidHom =
          κ.toMonoidHom.comp α.toMonoidHom := by
        ext x
        simp [hc, MulAut.conj_apply, MulAut.mul_apply]
      rw [h1, ← Subgroup.map_map, hJ α hα]
    · rintro _ ⟨α, hα, rfl⟩ _ ⟨d, hd, rfl⟩
      have := hD α hα d hd
      simp [hc, MulAut.conj_apply, MulAut.mul_apply, this]
  have hinj : Function.Injective c.toMonoidHom := c.injective
  exact isCyclic_of_surjective (Subgroup.equivMapOfInjective U c.toMonoidHom hinj).symm.toMonoidHom
    (Subgroup.equivMapOfInjective U c.toMonoidHom hinj).symm.surjective

end Conj

section Main

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem blockIb_cyclic_three (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hT : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb)) {f : ℕ} (hf : 2 ≤ f)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* projectiveSL 3 (GaloisField 2 f))
    (U : Subgroup Y) (hUL : U ≤ Subgroup.normalizer (Lb : Set Y))
    (hUP : U ≤ Subgroup.normalizer (Pb : Set Y)) (hUD : U ≤ Subgroup.centralizer (D : Set Y))
    (hU3 : IsPGroup 3 U) :
    IsCyclic ((descendHom e).comp (Subgroup.inclusion hUL)).range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h4s : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    haveI := Fintype.ofFinite (GaloisField 2 f)
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (GaloisField 2 f)))
      (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK4)
    exact ⟨t, ht⟩
  have hPL : Pb ≤ Lb := hP.parab.1
  set ψ := centralQuotientHom e with hψ
  set Jb : Subgroup (projectiveSL 3 (GaloisField 2 f)) := (Pb.subgroupOf Lb).map ψ with hJb
  obtain ⟨S, hNJ, hne, htop⟩ := exists_parab_X hP hD hT e
  obtain ⟨g, d, hd, hJ⟩ := LinearThreeKit.eq_map_conj_projStabilizer_of_sylow 2 S Jb hNJ hne htop
  obtain ⟨κ, hκ⟩ : ∃ κ : MulAut (projectiveSL 3 (GaloisField 2 f)),
      Jb.map κ.toMonoidHom = projStabilizer (flagSpace 3 (GaloisField 2 f) 1) := by
    have hJg : Jb.map (MulAut.conj g⁻¹).toMonoidHom =
        projStabilizer (flagSpace 3 (GaloisField 2 f) d) := by
      rw [hJ, Subgroup.map_map]
      have : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom :
          projectiveSL 3 (GaloisField 2 f) →* _) = MonoidHom.id _ := by
        ext y; simp [MulAut.conj_apply, mul_assoc]
      rw [this, Subgroup.map_id]
    rcases hd with rfl | rfl
    · exact ⟨MulAut.conj g⁻¹, hJg⟩
    · obtain ⟨κ₀, hκ₀⟩ := LinA.exists_aut_plane_to_point (K := GaloisField 2 f)
      refine ⟨κ₀ * MulAut.conj g⁻¹, ?_⟩
      rw [LinA.map_toMonoidHom_mul', hJg, hκ₀]
  have hDp := barD_perfect hPL hD.Dperf hD.Dle e
  have hDJ : barD D hPL e ≤ Jb := barD_le hPL e
  set b := padicValNat 3 (Nat.card (GaloisField 2 f) ^ 2 - 1) with hb
  have hb1 : 1 ≤ b := by
    rw [hb]
    exact one_le_padicValNat_of_dvd (by
      have : 1 < Nat.card (GaloisField 2 f) := Finite.one_lt_card
      have : 1 < Nat.card (GaloisField 2 f) ^ 2 := by nlinarith
      omega) LinA.three_dvd_card_sq_sub_one
  obtain ⟨V₀, hV₀P, hV₀p, hV₀card⟩ := LinA.exists_levi_perfect h4s
  have hκinv : (projStabilizer (flagSpace 3 (GaloisField 2 f) 1)).map κ.symm.toMonoidHom = Jb := by
    rw [← hκ, Subgroup.map_map]
    have : (κ.symm.toMonoidHom.comp κ.toMonoidHom :
        projectiveSL 3 (GaloisField 2 f) →* _) = MonoidHom.id _ := by
      ext y; simp
    rw [this, Subgroup.map_id]
  obtain ⟨s, hsD, hso⟩ := exists_barD_order hP hD e hb1
    ⟨V₀.map κ.symm.toMonoidHom, by
      have := Subgroup.map_mono (f := κ.symm.toMonoidHom) hV₀P
      rw [hκinv] at this
      exact this,
      by rw [← Subgroup.map_commutator, hV₀p],
      by
        have hc : Nat.card (V₀.map κ.symm.toMonoidHom) = Nat.card V₀ :=
          Nat.card_congr (Subgroup.equivMapOfInjective V₀ κ.symm.toMonoidHom κ.symm.injective).toEquiv.symm
        rw [hc]
        exact (pow_padicValNat_dvd).trans hV₀card⟩
  set φ := (descendHom e).comp (Subgroup.inclusion hUL) with hφ
  have hU3' : IsPGroup 3 φ.range :=
    hU3.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  refine LinA.cyclic_of_fixing_perfect_conj κ Jb (barD D hPL e) hκ hDp hDJ s hsD hso φ.range hU3' ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact descendAut_map_eq e (hUL a.2) (hUP a.2)
  · rintro _ ⟨a, rfl⟩ d hd
    exact descendAut_fixes_barD hPL e (hUL a.2) (hUD a.2) d hd

end Main

end CFSG.HardMathSupport.Curtis.UnitaryLevi
