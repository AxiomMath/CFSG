module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Fix
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteGen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Model
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5L2

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] [Finite Y] (e : Y ≃* PSL2 F)

theorem exists_conj_stdT (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (D : Sylow 2 (PSL2 F)) :
    ∃ h : PSL2 F, ∀ d : PSL2 F, d ∈ (D : Subgroup (PSL2 F)) ↔ h⁻¹ * d * h ∈ stdT F := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) D
  exact ⟨h, fun d => by rw [← hh, mem_smul_sylow_iff, coe_stdSylow]⟩

theorem centralizes_stdT_of_conj {D : Subgroup (PSL2 F)} {h : PSL2 F}
    (hh : ∀ d : PSL2 F, d ∈ D ↔ h⁻¹ * d * h ∈ stdT F) {x : PGammaL2 F}
    (hx : ∀ d ∈ D, x * incl F d = incl F d * x) :
    ∀ g ∈ (stdT F).map (incl F),
      (incl F h)⁻¹ * x * incl F h * g = g * ((incl F h)⁻¹ * x * incl F h) := by
  rintro _ ⟨t, ht, rfl⟩
  have hd : h * t * h⁻¹ ∈ D := by
    rw [hh, show h⁻¹ * (h * t * h⁻¹) * h = t by group]
    exact ht
  have h1 := hx _ hd
  rw [map_mul, map_mul, map_inv] at h1
  calc (incl F h)⁻¹ * x * incl F h * incl F t
      = (incl F h)⁻¹ * (x * (incl F h * incl F t * (incl F h)⁻¹)) * incl F h := by group
    _ = (incl F h)⁻¹ * ((incl F h * incl F t * (incl F h)⁻¹) * x) * incl F h := by rw [h1]
    _ = incl F t * ((incl F h)⁻¹ * x * incl F h) := by group

theorem commute_of_fix (R : Sylow 2 Y) {α : MulAut Y} (hα : ∀ r ∈ (R : Subgroup Y), α r = r) :
    ∀ d ∈ (sylowMap e R : Subgroup (PSL2 F)),
      autEquiv e α * incl F d = incl F d * autEquiv e α := by
  intro d hd
  have h1 : e.symm d ∈ (R : Subgroup Y) := by
    rw [← mem_sylowMap_iff e R, MulEquiv.apply_symm_apply]
    exact hd
  have h2 := (apply_eq_iff_commute e α (e.symm d)).mp (hα _ h1)
  rwa [MulEquiv.apply_symm_apply] at h2

include e in
theorem centralizer_sylow_l2 {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (R : Sylow 2 Y)
    (P : Subgroup (MulAut Y)) (hP : IsPGroup 2 P)
    (hPR : ∀ α ∈ P, ∀ r ∈ (R : Subgroup Y), α r = r) :
    (∀ α ∈ P, α * α = 1) ∧ Nat.card P ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  set D := sylowMap e R with hD
  have h2k : ∀ α ∈ P, ∃ k : ℕ, α ^ 2 ^ k = 1 := fun α hα => by
    obtain ⟨k, hk⟩ := hP ⟨α, hα⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  by_cases hab : ∀ a ∈ (R : Subgroup Y), ∀ b ∈ (R : Subgroup Y), a * b = b * a
  ·
    obtain ⟨hR4, hfo⟩ := not_even_of_abelian e hp hp2 hf hF R hab
    have hD4 : Nat.card D = 4 := by rw [card_sylowMap e R, hR4]
    set V := (D : Subgroup (PSL2 F)).map
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) with hV
    have hDsq : ∀ d ∈ (D : Subgroup (PSL2 F)), d * d = 1 := by
      obtain ⟨ρ⟩ := (sylow_two_dihedral_of_equiv (MulEquiv.refl (PSL2 F)) hodd D)
        |>.elim fun m ⟨hm, hρ⟩ => by
          have hcard : Nat.card D = 2 ^ (m + 1) := by
            rw [Nat.card_congr hρ.some.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
          have hm1 : m = 1 := by
            rw [hD4] at hcard
            have := Nat.pow_right_injective le_rfl (show 2 ^ 2 = 2 ^ (m + 1) by omega)
            omega
          subst hm1
          exact hρ
      intro d hd
      have hD2 : ∀ x : DihedralGroup (2 ^ 1), x * x = 1 := by decide
      have h1 := hD2 (ρ ⟨d, hd⟩)
      rw [← map_mul, ← map_one ρ] at h1
      exact congrArg Subtype.val (ρ.injective h1)
    have hVK : IsKleinFour V := by
      apply isKleinFour_of_card_four_sq
      · rw [hV, card_map_of_injective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, hD4]
      · rintro ⟨_, d, hd, rfl⟩
        apply Subtype.ext
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← map_pow, sq, hDsq d hd, map_one]
    have hmem : ∀ α ∈ P, autEquiv e α ∈ (D : Subgroup (PSL2 F)).map (incl F) := fun α hα => by
      obtain ⟨k, hk⟩ := h2k α hα
      have hr : (autEquiv e α).right = 1 := right_eq_one_of_odd hp hF hfo _ (k := k)
        (by rw [← map_pow, hk, map_one])
      have hxg := eq_inl_of_right_eq_one hr
      have hgC : (autEquiv e α).left ∈ centralizer (V : Set (PGL2 F)) := by
        rw [mem_centralizer_iff]
        rintro _ ⟨d, hd, rfl⟩
        have h1 := commute_of_fix e R (hPR α hα) d hd
        rw [hxg, incl_apply, ← map_mul, ← map_mul] at h1
        exact (SemidirectProduct.inl_injective h1).symm
      rw [pgl2_kleinFour_centralizer_eq_self F hodd V hVK] at hgC
      obtain ⟨d, hd, hdg⟩ := hgC
      exact ⟨d, hd, by rw [hxg, incl_apply, hdg]⟩
    refine ⟨fun α hα => (autEquiv e).injective ?_, ?_⟩
    · obtain ⟨d, hd, hdα⟩ := hmem α hα
      rw [map_mul, map_one, ← hdα, ← map_mul, hDsq d hd, map_one]
    · calc Nat.card P = Nat.card (P.map (autEquiv e).toMonoidHom) :=
            (card_map_of_injective (autEquiv e).injective).symm
        _ ≤ Nat.card ((D : Subgroup (PSL2 F)).map (incl F)) := by
            apply card_le_of_le
            rintro _ ⟨α, hα, rfl⟩
            exact hmem α hα
        _ = 4 := by rw [card_map_of_injective (incl_injective F), hD4]
  ·
    have hna : ∃ a ∈ (R : Subgroup Y), ∃ b ∈ (R : Subgroup Y), a * b ≠ b * a := by
      push Not at hab
      exact hab
    have hD8 := eight_le_of_noncomm e hodd R hna
    refine ⟨fun α hα => (autEquiv e).injective ?_, ?_⟩
    · obtain ⟨k, hk⟩ := h2k α hα
      rw [map_mul, map_one]
      set x := autEquiv e α with hx
      have hxk : x ^ 2 ^ k = 1 := by rw [hx, ← map_pow, hk, map_one]
      have hxD := commute_of_fix e R (hPR α hα)
      by_cases hxr : x.right = 1
      · obtain ⟨d, ⟨hdD, hdC⟩, hd⟩ := mem_center_of_right_eq_one hodd D hD8 x hxr hxk hxD
        obtain ⟨-, hZ⟩ := sylow_noncomm_center hodd D hD8
        have hdd : d * d = 1 := by
          have h1 : (⟨d, hdD, hdC⟩ : ↥((D : Subgroup (PSL2 F)) ⊓
              centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F)))) ^ 2 = 1 := by
            have h2 := orderOf_dvd_natCard (⟨d, hdD, hdC⟩ : ↥((D : Subgroup (PSL2 F)) ⊓
              centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F))))
            rw [hZ] at h2
            exact orderOf_dvd_iff_pow_eq_one.mp h2
          rw [← sq]
          exact congrArg Subtype.val h1
        rw [← hd, ← map_mul, hdd, map_one]
      ·
        have hfe := even_of_right_ne_one hp hF x hxk hxr
        obtain ⟨hsq, hq4, hn⟩ := model_hyps_of_even hp hp2 hf hF hfe
        obtain ⟨h, hh⟩ := exists_conj_stdT hodd hsq hq4 D
        have hxC := centralizes_stdT_of_conj hh hxD
        have hσ : ((incl F h)⁻¹ * x * incl F h).right * ((incl F h)⁻¹ * x * incl F h).right =
            1 := by
          have h1 := right_sq_of_centralizes_sylow hp hp2 hf hF D hD8 x (k := k)
            (by rw [← SemidirectProduct.rightHom_eq_right, ← map_pow, hxk, map_one]) hxD
          have hr : ((incl F h)⁻¹ * x * incl F h).right = x.right := by simp [incl_apply]
          rw [hr, ← sq]
          exact h1
        have h1 := mul_self_of_centralizes_stdT hodd hsq hn _ hxC hσ
        calc x * x = incl F h * (((incl F h)⁻¹ * x * incl F h) * ((incl F h)⁻¹ * x * incl F h)) *
              (incl F h)⁻¹ := by group
          _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    · calc Nat.card P = Nat.card (P.map (autEquiv e).toMonoidHom) :=
            (card_map_of_injective (autEquiv e).injective).symm
        _ ≤ 4 := card_le_four_of_centralizes_sylow hp hp2 hf hF D hD8 _ (hP.map _) (by
            rintro _ ⟨α, hα, rfl⟩ t ht
            exact commute_of_fix e R (hPR α hα) t ht)

end CFSG.ComponentClassification.FooteLit.Aut5L2
