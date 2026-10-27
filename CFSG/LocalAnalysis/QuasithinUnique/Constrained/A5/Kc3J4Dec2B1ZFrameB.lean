module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZK
public import CFSG.Sporadic.J4.QT2LocBasicRep

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem card_centralizer_eta_one_b
    (hF : J4Basic) :
    Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1} : Set J)) = 1816657920 := by
  have hM := hF.mat
  have hz : eta uJ 11 1 ∈ tFin := mem_tFin.2 ⟨1, one_mem_tMasks, rfl⟩
  have hHM := card_eq_card_mul_centralizer Hj (eta uJ 11 1) tFin hz (tFin_conj hM)
    (fun x hx => tFin_trans hM x hx)
  have hle : Subgroup.centralizer ({eta uJ 11 1} : Set J) ≤ Hj := by
    intro x hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hx
    have h2 : x * eta uJ 11 1 = eta uJ 11 1 * x := h1
    exact centralizer_eta_one_le_Hj_b hF h2
  have hinf : Subgroup.centralizer ({eta uJ 11 1} : Set J) ⊓ Hj =
      Subgroup.centralizer ({eta uJ 11 1} : Set J) := le_antisymm inf_le_left (le_inf le_rfl hle)
  rw [hinf, hF.cardHj, card_tFin hM] at hHM
  omega

end CFSG.QuasithinUnique.A5
