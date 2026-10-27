module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Choice
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2V
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Q

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem t_comm_beta (_hc : L2Ctx hs W) :
    t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t :=
  mem_centralizer_singleton_iff.mp (hs.setup.t_mem_centralizer_beta i j)

theorem qc_structure (hKF : AutPSL2FusionInput) (hc : L2Ctx hs W) (hSV : S.relIndex V = 2) :
    Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 2 ∧
      V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) = W ∧
      Nat.card W = Nat.card S ∧
      Nat.card S = 2 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) = 2 := by
    have hlt : Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) < 4 := by
      by_contra hge
      push Not at hge
      obtain ⟨y, -, hy⟩ := hc.exists_conj_t_eq hge
      exact hs.conj_t_ne_t_mul_beta hKF hSV y (hy.trans hc.t_comm_beta.symm)
    have hP2 : IsPGroup 2 ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) :=
      hc.sylow.isPGroup.to_le hc.qTilde_le
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have hge : 2 ≤ Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) := by
      have := Subgroup.card_le_of_le (zpowers_le.mpr hc.beta_mem_qTilde)
      rw [hc.card_zpowers_beta] at this
      exact this
    rw [hk] at hlt hge ⊢
    rcases k with _ | _ | k
    · norm_num at hge
    · rfl
    · exfalso
      have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hQ : Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 2 := by
    rw [← hc.card_qTilde, hQ2]
  have hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    isCyclic_of_prime_card (p := 2) hQ
  have h1 := hc.card_W_le hQc
  have h2 := hs.card_S_le
  have h3 := hs.two_mul_card_T_le
  have h4 := hc.card_U_le
  have hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) = W :=
    Subgroup.eq_of_le_of_card_ge hc.le (by omega)
  exact ⟨hQ, hUW, by omega, by omega⟩

theorem qd_not_cyclic (hc : L2Ctx hs W) (hSV : S.relIndex V = 4) :
    ¬ IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  intro hQc
  have h1 := hc.card_W_le hQc
  have h4 := hc.card_U_le
  have hU := hs.beta.relIndex_le
  have hcU := Subgroup.relIndex_mul_card (V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
    Set X)) V
  have hcS := Subgroup.relIndex_mul_card S V
  rw [inf_of_le_left inf_le_left] at hcU
  rw [inf_of_le_left hs.le_V, hSV] at hcS
  have hpos : 0 < Nat.card S := Nat.card_pos
  have : Nat.card ↥(V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) ≥
      2 * Nat.card S := by
    by_contra hlt
    push Not at hlt
    have h5 : (V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).relIndex V *
        Nat.card ↥(V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) <
        2 * (2 * Nat.card S) := Nat.mul_lt_mul_of_le_of_lt hU hlt (by norm_num)
    omega
  omega

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
