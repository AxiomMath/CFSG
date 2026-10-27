module

public import CFSG.ClassicalInvolution.Q3.Q3WAClose
public import CFSG.ClassicalInvolution.Q3.Q3WADict

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem oddLieType_of_psl_model3 {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {k : ℕ} (hk : 3 ≤ k)
    (hmodel : CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) StatedLieTag.PSL k 3 1) :
    CFSG.Blueprint.OddLieType G := by
  have hZ : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  let e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible StatedLieTag.PSL k 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  exact ⟨StatedLieTag.PSL, k, 3, 1, Nat.prime_three, by norm_num, hadm,
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel⟩


@[expose] def OddThreeFreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    RouteD3Setup K z → LocalOddThreeFree3 (conjClass3 K) z

theorem piece3SL7_of_odd3 (h3 : OddThreeFreeInput) : Piece3SL7 := by
  rintro a t n ⟨rfl, rfl, hn⟩ G _ _ _ hnab K z hR hshape
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dict (by omega) hR.inClass hK hR.cls hshape
  obtain ⟨ψ, -, -, -, -, hmodel⟩ := routeD_typeA3 (by omega) hR.inClass hex hK hsingle hconn
    hR.cls d hP1 (h3 G K z hR)
  exact Or.inl (oddLieType_of_psl_model3 hnab (by omega) hmodel)

@[expose] def ChainPiece3SLs : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ m : ℕ, 2 ≤ m → m ≤ 4 →
      LocalShapeC3 1 (CompData.model .PSL (m + 1)) (conjClass3 K) z →
      ∃ U : Fin (m + 2) → Subgroup G, (∀ i, U i ∈ conjClass3 K) ∧
        (∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
        ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
          ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)

theorem piece3SLs_of_chain (h3 : OddThreeFreeInput) (h : ChainPiece3SLs) : Piece3SLs := by
  rintro a t n ⟨rfl, rfl, hn3, hn5⟩ G _ _ _ hnab K z hR hshape
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dict (by omega) hR.inClass hK hR.cls hshape
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z hR m (by omega) (by omega) hshape
  let c : ACore3 m (conjClass3 K) K z :=
    { hm := by omega, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d }
  obtain ⟨ψ, -, -, -, -, hmodel⟩ := c.typeA_of_chain hsingle hconn U hUΩ hcomm hpair
  exact Or.inl (oddLieType_of_psl_model3 hnab (by omega) hmodel)

end CFSG.ClassicalInvolution.Q3.Q3W
