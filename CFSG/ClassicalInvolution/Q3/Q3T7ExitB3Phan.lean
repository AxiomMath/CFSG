module

public import CFSG.ClassicalInvolution.Q3.Q3T7Exit
public import CFSG.ClassicalInvolution.Phan.Phan3B3Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TW CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Phan.Q3G
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open CFSG.ClassicalInvolution.Asc77.B3C (SymplecticPhanPair)

section Phan

variable {G : Type} [Group G]

@[expose] def B3PhanChain3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
    (∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U 0) (U 1)) ∧
    (∃ W, SymplecticPhanPair (GaloisField 3 1)
      (ModelFacts.two_ne_zero_galoisField 1 (by norm_num)) W (U 1) (U 2)) ∧
    ⨆ k, U k = ⊤ ∧
    ∃ w ∈ U 2, Commutes (U 1) (conjSub w (U 1)) ∧
      ¬ 3 ∣ Nat.card (Subgroup.center ↥(U 0 ⊔ U 1 ⊔ conjSub w (U 1)))

end Phan

section Exits

variable {G : Type} [Group G] [IsSimpleGroup G]

theorem conclusionD_of_b3PhanChain3
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)} (h : B3PhanChain3 Ω) :
    ConclusionD G := by
  obtain ⟨U, -, hcomm, h01, h12, hgen, hH3⟩ := h
  obtain ⟨V, hV02, hV01, hV12, hVgen⟩ := exists_b3CtChain_of_phanChain hnab hcomm h01 h12 hgen
    hH3 (K := GaloisField 3 1) card_gf3
  exact conclusionD_of_b3Chain3 hnab (Ω := Set.univ)
    ⟨V, Set.mem_univ _, hV02, hV01, hV12, hVgen⟩

end Exits

end CFSG.ClassicalInvolution.Q3.Q3T7
