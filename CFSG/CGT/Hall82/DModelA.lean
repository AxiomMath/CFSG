module

public import Certificates.Certificate840002
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsFacts
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsCert

public noncomputable section

namespace CFSG.CGT.Hall82.DModel

open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.HeTri CFSG.Monster.B.Co2

theorem lin :
    ∀ x ∈ hexaM, ∀ v w, x (xorF v w) = xorF (x v) (x w) :=
  Certificates.certificate840002.1

theorem oval_trans :
    ∀ h h', IsOvalVec h → IsOvalVec h' → ∃ a ∈ hexaL, a h = h' :=
  Certificates.certificate840002.2.1

theorem five_trans :
    ∀ v, v ≠ 0 → ¬ IsOvalVec v → ∃ a ∈ hexaL, a 5 = v :=
  Certificates.certificate840002.2.2.1

theorem five_not_oval : ¬ IsOvalVec 5 :=
  Certificates.certificate840002.2.2.2.1

theorem card_stab_oval :
    ∀ h, IsOvalVec h → Nat.card (stabSub hexaM h) = 120 :=
  Certificates.certificate840002.2.2.2.2.1

theorem card_stab :
    ∀ v, v ≠ 0 → ¬ IsOvalVec v → Nat.card (stabSub hexaM v) = 48 :=
  Certificates.certificate840002.2.2.2.2.2.1

theorem card_stabL_oval :
    ∀ h, IsOvalVec h → Nat.card (stabSub hexaL h) = 60 :=
  Certificates.certificate840002.2.2.2.2.2.2.1

theorem card_stabL :
    ∀ v, v ≠ 0 → ¬ IsOvalVec v → Nat.card (stabSub hexaL v) = 24 :=
  Certificates.certificate840002.2.2.2.2.2.2.2.1

theorem eq_bot_of_oval :
    ∀ h, IsOvalVec h → ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM →
      IsPGroup 2 B → (∀ b ∈ B, b h = h) →
      (∀ a ∈ hexaL, a h = h → ∀ b ∈ B, a * b * a⁻¹ ∈ B) → B = ⊥ :=
  Certificates.certificate840002.2.2.2.2.2.2.2.2.1

theorem zeta_fix : ∀ v, heZeta v = v → v = 0 :=
  Certificates.certificate840002.2.2.2.2.2.2.2.2.2

theorem zeta_pow : heZeta ^ 3 = 1 :=
  zeta_pow_of he_modelCheck

theorem zeta_ne : heZeta ≠ 1 :=
  zeta_ne_of he_modelCheck

theorem zeta_conj :
    ∀ x ∈ hexaM, x * heZeta * x⁻¹ = heZeta ∨ x * heZeta * x⁻¹ = heZeta ^ 2 := by
  intro x hx
  have h := zeta_normal_of he_modelCheck x hx
  have hz2 : heZeta ^ 2 = heZeta⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, zeta_pow_of he_modelCheck]
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hz2.symm)

end CFSG.CGT.Hall82.DModel
