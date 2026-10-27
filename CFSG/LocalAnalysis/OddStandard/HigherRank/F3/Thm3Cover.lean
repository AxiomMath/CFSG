module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Lift

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

theorem classBShape_of_bar_equiv {A B : Type} [Group A] [Group B]
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) (h : ClassBShape A) : ClassBShape B := by
  obtain ⟨eZ⟩ := ComponentClassification.FooteLit.nonempty_fusionZStar_equiv_of_quotient_equiv e
  obtain ⟨τ, n, hm, hs⟩ := h
  exact ⟨τ, n, ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv eZ hm, hs⟩

theorem nonempty_equiv_of_diag {H : Type} [Group H] [Finite H] {t : H} (ht : orderOf t = 2)
    {K₀ K₁ R : Subgroup H} (hK₀ : IsTwoComponent K₀)
    (hK₁ : K₁ = K₀.map (MulAut.conj t).toMonoidHom) (hne : K₁ ≠ K₀)
    (hR : R = centralizerResidual (K₀ ⊔ K₁) t) (hP : ¬ PartialCentre ↥R) :
    Nonempty (↥K₀ ⧸ pPrimeCore 2 ↥K₀ ≃* ↥R ⧸ pPrimeCore 2 ↥R) := by
  subst hK₁
  set R0 := centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) t with hR0
  rw [hR] at hP
  have hL := (L219.isTwoComponent_iff_twoComponents K₀).mp hK₀
  obtain ⟨φ, hφ⟩ := L219.part_b3 ht hL hne
  obtain ⟨hR2, -, -⟩ := L219.part_b1 ht hL hne
  have hQq : IsQuasisimple (↥K₀ ⧸ pPrimeCore 2 ↥K₀) := hK₀.2.2
  have hBq : IsQuasisimple (↥R0 ⧸ pPrimeCore 2 ↥R0) := hR2.2.2.2
  have hQo : Open.IsQuasisimple (↥K₀ ⧸ pPrimeCore 2 ↥K₀) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQq)
  have hker : φ.ker ≤ center (↥K₀ ⧸ pPrimeCore 2 ↥K₀) := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQo φ.ker with
      hc | htop
    · exact hc
    · exfalso
      haveI : Nontrivial (↥R0 ⧸ pPrimeCore 2 ↥R0) := LocalCores.isQuasisimple_nontrivial hBq
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥R0 ⧸ pPrimeCore 2 ↥R0)
      obtain ⟨x, rfl⟩ := hφ a
      obtain ⟨y, rfl⟩ := hφ b
      have hx : x ∈ φ.ker := htop ▸ mem_top x
      have hy : y ∈ φ.ker := htop ▸ mem_top y
      rw [MonoidHom.mem_ker] at hx hy
      exact hab (by rw [hx, hy])
  have hoddO : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥R0)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := 2) (G := ↥R0))
  have hP' : ¬ PartialCentre (↥R0 ⧸ pPrimeCore 2 ↥R0) := fun hb =>
    hP ((partialCentre_iff_of_surjective_odd (QuotientGroup.mk' (pPrimeCore 2 ↥R0))
      (QuotientGroup.mk'_surjective _) hoddO).mpr hb)
  have hodd : ¬ 2 ∣ Nat.card φ.ker :=
    not_two_dvd_card_ker_of_full_cover φ hφ hker hQq.1 hBq
      (pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥R0) 2) hP'
  have hkerbot : φ.ker = ⊥ := by
    have hle : φ.ker ≤ pPrimeCore 2 (↥K₀ ⧸ pPrimeCore 2 ↥K₀) :=
      le_sSup ⟨φ.normal_ker, Nat.prime_two.coprime_iff_not_dvd.mpr hodd⟩
    have hO : pPrimeCore 2 (↥K₀ ⧸ pPrimeCore 2 ↥K₀) = ⊥ :=
      pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K₀) 2
    simpa [hO] using hle
  have he : ↥K₀ ⧸ pPrimeCore 2 ↥K₀ ≃* ↥R0 ⧸ pPrimeCore 2 ↥R0 :=
    MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hkerbot, hφ⟩
  rw [hR]
  exact ⟨he⟩

theorem cover_of_diag {H : Type} [Group H] [Finite H] {t : H} (ht : orderOf t = 2)
    {K₀ K₁ R : Subgroup H} (hK₀ : IsTwoComponent K₀)
    (hK₁ : K₁ = K₀.map (MulAut.conj t).toMonoidHom) (hne : K₁ ≠ K₀)
    (hR : R = centralizerResidual (K₀ ⊔ K₁) t) (hM : IsMTypeSchur 3 ↥R) (hS : ClassBShape ↥R)
    (hP : ¬ PartialCentre ↥R) :
    Nonempty (↥K₀ ⧸ pPrimeCore 2 ↥K₀ ≃* ↥R ⧸ pPrimeCore 2 ↥R) ∧ IsMTypeSchur 3 ↥K₀ ∧
      ClassBShape ↥K₀ := by
  obtain ⟨e⟩ := nonempty_equiv_of_diag ht hK₀ hK₁ hne hR hP
  exact ⟨⟨e⟩, T1.isMTypeSchur_of_bar_equiv hM hK₀.2 e.symm, classBShape_of_bar_equiv e.symm hS⟩

end CFSG.OddStandard.HigherRank.F3
