module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

theorem uexc_not_dvd_card_ker {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω Ω' : Type} [Group Ω]
    [Finite Ω] [Group Ω'] (π : Ω →* Ω') (hk : IsPGroup 2 π.ker) : ¬ p ∣ Nat.card π.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  intro hd
  rw [hn] at hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))

theorem uexc_B_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω Ω' : Type} [Group Ω] [Finite Ω]
    [Group Ω'] (π : Ω →* Ω') (hk : IsPGroup 2 π.ker) {B : Subgroup Ω} {x : Ω}
    (hB : IsElemAbelian p B) (hx : x ∈ B) (hx1 : x ≠ 1) :
    IsElemAbelian p (B.map π) ∧ Nat.card (B.map π) = Nat.card B ∧ π x ∈ B.map π ∧ π x ≠ 1 := by
  have hN := uexc_not_dvd_card_ker hp hp2 π hk
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  refine ⟨CFSG.SectionRank.isElemAbelian_map hB π, S267.card_map_of_isPGroup hp π hN hBp,
    Subgroup.mem_map_of_mem π hx, fun h => hx1 ?_⟩
  have h1 : x ∈ B ⊓ π.ker := ⟨hx, h⟩
  rw [S267.inf_ker_eq_bot' hp π hN hBp, Subgroup.mem_bot] at h1
  exact h1

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
