module

public import CFSG.RankThree.PartOne.KE.E8TwelveClasses

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE

@[expose] def e8T12Coroot (γ : Fin Tag.E8.rank → ℤ) (i : Fin Tag.E8.rank) : ℤ :=
  ∑ j, γ j * Tag.E8.cartan j i

@[expose] def e8T12D4Gamma (w : List (Fin Tag.E8.rank)) (k : Fin 4) : Fin Tag.E8.rank → ℤ :=
  fun j => lget (e8wl w) j.val (k.val + 1)

@[expose] def e8T12D4Exp (w : List (Fin Tag.E8.rank)) (u : Fin 4 → ℤ) (i : Fin Tag.E8.rank) : ℤ :=
  ∑ k, u k * e8T12Coroot (e8T12D4Gamma w k) i

@[expose] def E8T12D4Good (w : List (Fin Tag.E8.rank)) (y : Fin 4 → Fin 4 → ℤ)
    (lam : Fin Tag.E8.rank → ℤ) : Prop :=
  (∀ j : Fin Tag.E8.rank,
    ∑ i : Fin Tag.E8.rank, e8T12D4Exp w (y 0) i * lget e8T12VList i j = e8T12D4Exp w (y 1) j) ∧
  (∀ j : Fin Tag.E8.rank,
    ∑ i : Fin Tag.E8.rank, e8T12D4Exp w (y 1) i * lget e8T12VList i j = e8T12D4Exp w (y 2) j) ∧
  (∀ j : Fin Tag.E8.rank,
    ∑ i : Fin Tag.E8.rank, e8T12D4Exp w (y 2) i * lget e8T12VList i j = e8T12D4Exp w (y 3) j) ∧
  (∀ j : Fin Tag.E8.rank, ∑ i : Fin Tag.E8.rank, e8T12D4Exp w (y 3) i * lget e8T12VList i j =
    e8T12D4Exp w (y 2) j - e8T12D4Exp w (y 0) j) ∧
  (∑ i : Fin Tag.E8.rank, lam i * e8T12D4Exp w (y 0) i = 0) ∧
  (∑ i : Fin Tag.E8.rank, lam i * e8T12D4Exp w (y 1) i = 0) ∧
  (∑ i : Fin Tag.E8.rank, lam i * e8T12D4Exp w (y 2) i = 0) ∧
  (∑ i : Fin Tag.E8.rank, lam i * e8T12D4Exp w (y 3) i = 1)

instance (w : List (Fin Tag.E8.rank)) (y : Fin 4 → Fin 4 → ℤ) (lam : Fin Tag.E8.rank → ℤ) :
    Decidable (E8T12D4Good w y lam) := by
  unfold E8T12D4Good
  infer_instance

@[expose] def e8T12D4Data : List (ℕ × (Fin 4 → Fin 4 → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(0, ![![1, 1, 1, 1], ![1, 0, 1, 1], ![1, 0, 0, 0], ![0, -1, -1, 0]],
      ![0, 0, 0, 0, 0, 0, 0, -1]),
   (1, ![![1, 1, 1, 1], ![1, 1, 1, 0], ![0, 1, 0, 0], ![0, 0, -1, -1]],
      ![0, 0, 0, 0, 0, 0, -1, 0]),
   (3, ![![1, 1, 1, 1], ![1, 1, 2, 1], ![1, 1, 1, 0], ![1, 0, 1, 0]],
      ![0, -1, -1, 0, 0, 0, 0, 0]),
   (7, ![![1, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 0, 0], ![-1, 0, -1, 0]],
      ![1, 0, 1, 0, 0, 0, 0, 0]),
   (10, ![![1, 1, 1, 1], ![1, 0, 1, 1], ![1, 0, 0, 0], ![0, -1, -1, 0]],
      ![0, -1, -1, -1, 0, 0, 0, 0]),
   (11, ![![1, 1, 1, 1], ![1, 1, 1, 0], ![0, 1, 0, 0], ![0, 0, -1, -1]],
      ![0, 1, 0, 1, 0, 0, 0, 0])]

theorem e8T12_d4_data_check : ∀ c ∈ e8T12D4Certs, ∃ d ∈ e8T12D4Data, d.1 = c.cls ∧
    E8T12D4Good c.w d.2.1 d.2.2 := by
  decide +kernel

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
