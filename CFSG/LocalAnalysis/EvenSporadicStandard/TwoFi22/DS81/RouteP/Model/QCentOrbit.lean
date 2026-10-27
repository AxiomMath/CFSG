module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Dictionary
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem smul_x2_eq_of_cover
    {K W : Subgroup Q3} (hQK : Q0 ≤ K) (hKL : K ≤ L0)
    (hWQ : W ≤ Q0) {root : Ω} (hcard : Nat.card (MulAction.orbit W root) = 693)
    (hx2 : x2 ∉ MulAction.orbit W root)
    (hcover : ∀ k ∈ K, k • x2 = x2 ∨ k • x2 ∈ MulAction.orbit W root) :
    ∀ k ∈ K, k • x2 = x2 := by
  by_contra h
  push Not at h
  obtain ⟨k0, hk0K, hk0⟩ := h
  have hmem : k0 • x2 ∈ MulAction.orbit ↥W root := by
    rcases hcover k0 hk0K with h' | h'
    · exact absurd h' hk0
    · exact h'
  obtain ⟨w0, hw0⟩ := MulAction.mem_orbit_iff.mp hmem
  have hO : MulAction.orbit ↥K x2 = insert x2 (MulAction.orbit ↥W root) := by
    ext a
    constructor
    · intro ha
      rw [MulAction.mem_orbit_iff] at ha
      obtain ⟨k, rfl⟩ := ha
      rcases hcover (k : Q3) k.2 with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · intro ha
      rw [Set.mem_insert_iff] at ha
      rcases ha with rfl | ha
      · exact MulAction.mem_orbit_self x2
      · rw [MulAction.mem_orbit_iff] at ha ⊢
        obtain ⟨w, hw⟩ := ha
        have hw0' : (w0 : Q3) • root = k0 • x2 := hw0
        refine ⟨⟨(w : Q3) * (w0 : Q3)⁻¹ * k0, ?_⟩, ?_⟩
        · exact K.mul_mem (K.mul_mem (hQK (hWQ w.2)) (K.inv_mem (hQK (hWQ w0.2)))) hk0K
        · change ((w : Q3) * (w0 : Q3)⁻¹ * k0) • x2 = a
          rw [mul_smul, mul_smul, ← hw0', inv_smul_smul]
          exact hw
  have hWcard : (MulAction.orbit ↥W root).ncard = 693 := hcard
  have hKcard : Nat.card (MulAction.orbit ↥K x2) = 694 := by
    rw [hO, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hx2]
    omega
  have hmul := card_orbit_mul_card_stabilizer (G := ↥K) x2
  rw [hKcard] at hmul
  have hdvd : 694 ∣ Nat.card ↥K := ⟨_, hmul.symm⟩
  have hdvdL : 694 ∣ Nat.card ↥L0 := hdvd.trans (Subgroup.card_dvd_of_le hKL)
  rw [card_L0_eq] at hdvdL
  exact absurd hdvdL (by norm_num)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
