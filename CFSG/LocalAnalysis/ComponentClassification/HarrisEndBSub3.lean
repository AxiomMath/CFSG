module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSubModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub1

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

namespace EndB

theorem factorization_card_R :
    (Nat.card R).factorization 2 = 8 := by
  rw [card_R, show (1209600 : ℕ) = 2 ^ 8 * 4725 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem isSylowOf_SA0 :
    IsSylowOf 2 (vModel.sub ⊔ zpowers u0) R ∧
      (∀ x ∈ vModel.sub ⊔ zpowers u0, x ∉ P → x * u0⁻¹ ∈ vModel.sub) ∧
      ∀ x ∈ vModel.sub ⊔ zpowers u0, x ∈ P → x ∈ vModel.sub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hu0R, hu0P, hcu, husq⟩ := u0_facts
  have hVP : vModel.sub ≤ P := by
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_centralizerIn.mp (vE_mem hk)).1
  have hn : ∀ x ∈ vModel.sub, u0 * x * u0⁻¹ ∈ vModel.sub := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hcu k hk]
    exact vModel.e_mem (vCu_facts k hk).1
  have hsq : u0 ^ 2 ∈ vModel.sub := by
    rw [sq, husq]
    exact vModel.e_mem vUsq_lt
  have hu0V : u0 ∉ vModel.sub := fun h => hu0P (hVP h)
  have hcard := card_sup_zpowers hn hsq hu0V
  rw [vModel.card_sub] at hcard
  have hle : vModel.sub ⊔ zpowers u0 ≤ R :=
    sup_le (hVP.trans P_le_R) (zpowers_le.mpr (mem_centralizerIn.mp hu0R).1)
  refine ⟨isSylowOf_of_card hle ?_, fun x hx hxP => ?_, fun x hx hxP => ?_⟩
  · rw [hcard, factorization_card_R]
    norm_num
  · rcases (mem_sup_zpowers_iff hn hsq).mp hx with h | h
    · exact absurd (hVP h) hxP
    · exact h
  · rcases (mem_sup_zpowers_iff hn hsq).mp hx with h | h
    · exact h
    · exfalso
      apply hu0P
      rw [show u0 = (x * u0⁻¹)⁻¹ * x by group]
      exact mul_mem (inv_mem (hVP h)) hxP

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem rt_facts
    (hJ : JLayer hs π) :
    ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315)) ∉ P ∧
      ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315)) ^ 2 = 1 ∧
      ∀ (l l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))),
        (l' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
          hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹ →
        ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315)) *
            ((π l : P) : Equiv.Perm (Fin 315)) *
            ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315))⁻¹ =
          ((π l' : P) : Equiv.Perm (Fin 315)) := by
  set r := rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) with hr
  have hrθ : rAutEquiv r = hJ.theta (hs.setup.tBar i j) := MulEquiv.apply_symm_apply _ _
  refine ⟨fun hP => hJ.alpha_not_mem ?_, ?_, fun l l' hl => ?_⟩
  · have hr' : r = ⟨((⟨(r : Equiv.Perm (Fin 315)), hP⟩ : P) : Equiv.Perm (Fin 315)),
        P_le_R hP⟩ := rfl
    rw [← hrθ, hr', rAutEquiv_of_mem]
    exact ⟨_, rfl⟩
  · have h1 : rAutEquiv (r ^ 2) = 1 := by
      rw [map_pow, hrθ, ← map_pow, hs.tBar_sq, map_one]
    have h2 : r ^ 2 = 1 := rAutEquiv.injective (by rw [h1, map_one])
    rw [← Subgroup.coe_pow, h2, Subgroup.coe_one]
  · have h1 := hJ.theta_apply (hs.setup.tBar i j) l l' hl
    rw [← hrθ, rAutEquiv_apply] at h1
    rw [← rConj_apply, h1]

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
