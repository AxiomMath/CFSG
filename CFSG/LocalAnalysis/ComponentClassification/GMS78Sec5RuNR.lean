module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRIso
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRTwist

public section

namespace CFSG.ComponentClassification.GMS78.RuN

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN CFSG.GMS78RuS
open CFSG.ComponentClassification.GMS78.RuSimCode

section Cert

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  {Φ : ℕ × Fin 8 × Fin 8 → G}

theorem linExt_zero (lam : ℕ → Fin 8) : linExt lam 0 = 0 := by
  simp [linExt, nCo_zero, xs8_zero]

theorem conjData_cAut (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (lam : ℕ → Fin 8)
    (hmem : ∀ k : nK, cAut lam * (k : MulAut RuR) * cAut lam ∈ (actN hM hS).range)
    (hfix : ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) →
      cAut lam * (k : MulAut RuR) * cAut lam = k) :
    ConjData hM hS (cAut lam) where
  sq := MulEquiv.ext fun x => by
    rw [MulAut.mul_apply, cAut_apply, cAut_apply]
    exact RuR.ext rfl (fin8_xor_xor_self _ _)
  fix_m _ := rfl
  fix_A t := by
    rw [cAut_apply]
    refine RuR.ext rfl ?_
    change t ^^^ linExt lam 0 = t
    rw [linExt_zero, fin8_xor_zero]
  mem := hmem
  fix_D := hfix

theorem exists_ruNIso [Finite G] (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) (hcardR : Nat.card R = 2048)
    (hNA : normalizer (gmsA L T : Set G) = normalizer (R : Set G)) :
    ∃ f : RuNModel ≃* ↥(normalizer (gmsA L T : Set G)),
      ∀ m, m ∈ A1model ↔ ((f m : ↥(normalizer (gmsA L T : Set G))) : G) ∈ gmsA L T := by
  obtain ⟨lam, hmem, hfix⟩ := exists_cAut_conj_mem (actN hM hS).range
    (fun y => ⟨_, actN_thetaR hM hS y⟩)
    (fun k j hk => ⟨⟨Φ (0, 0, j), hS.mem _⟩,
      MulEquiv.ext fun x => (actN_D hM hS j x).trans (hk x).symm⟩)
    (fun r hr => by
      obtain ⟨n, hm, hA⟩ := exists_actN_code hM hS hNC hidx hr
      exact ⟨_, ⟨n, rfl⟩, hm, hA⟩)
    (by
      rintro f ⟨n, rfl⟩ - hA
      exact exists_eq_conj hM hS hNC n hA)
  exact exists_ruNIso_of_conjData hM hS hNC hidx hcardR hNA
    (conjData_cAut hM hS lam hmem hfix)

end Cert

end CFSG.ComponentClassification.GMS78.RuN
