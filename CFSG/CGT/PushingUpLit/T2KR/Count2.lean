module

public import CFSG.CGT.PushingUpLit.T2KR.Count1

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

variable {G : Type} [Group G] [Finite G]

namespace PairFacts

variable {L M : Subgroup G} {n : ℕ} {H : MData G L M n} {P B D : Subgroup G}

theorem chi_eq_one_of_torus (hP : PairFacts H P B D) {h : G} (hh : h ∈ M)
    (htor : ∀ x ∈ B, ∃ x' ∈ B, ∃ d ∈ D, x = ⁅x', h⁆ * d) :
    ∀ x (hx : x ∈ B), H.chi ⟨x, hP.B_le_M hx⟩ = 1 := by
  intro x hx
  obtain ⟨x', hx', d, hd, rfl⟩ := htor x hx
  have hdQ : d ∈ QM L M := hP.D_le_Q hd
  have e : (⟨⁅x', h⁆ * d, hP.B_le_M hx⟩ : ↥M) =
      ⁅(⟨x', hP.B_le_M hx'⟩ : ↥M), (⟨h, hh⟩ : ↥M)⁆ * ⟨d, hdQ.1⟩ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [e, map_mul, map_commutatorElement, H.chi_of_centralizer (m := ⟨d, hdQ.1⟩) hdQ.2, mul_one,
    commutatorElement_eq_one_iff_mul_comm.2 (ringEquiv_mul_comm n _ _)]

omit [Finite G] in
theorem relIndex_pos' [Finite G] (A C : Subgroup G) : 0 < A.relIndex C :=
  Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card A C) Nat.card_pos

theorem step67 (hP : PairFacts H P B D) (hBLQ : ¬ B ≤ L ⊔ QM L M) :
    P.relIndex (QM L M) = 2 := by
  have hne1 : P.relIndex (QM L M) ≠ 1 := fun h =>
    hP.P_ne_Q (le_antisymm hP.P_le_Q (Subgroup.relIndex_eq_one.1 h))
  have hpos := relIndex_pos' P (QM L M)
  by_contra hne2
  have h2lt : 2 < P.relIndex (QM L M) := by omega
  obtain ⟨h, hh, htor⟩ := hP.torus h2lt
  have hchi := hP.chi_eq_one_of_torus hh htor
  apply hBLQ
  intro x hx
  exact H.mem_LQ_of_chi_eq_one (m := ⟨x, hP.B_le_M hx⟩) (k := 1)
    (Subtype.ext (by simpa [pow_two] using hP.B_sq x hx)) (hchi x hx)

theorem relIndex_E (hP : PairFacts H P B D) (hBLQ : ¬ B ≤ L ⊔ QM L M) :
    (B ⊓ (L ⊔ QM L M)).relIndex B = 2 := by
  have hle := H.relIndex_le_two hP.B_le_M hP.B_sq
  have hne1 : (B ⊓ (L ⊔ QM L M)).relIndex B ≠ 1 := fun h =>
    hBLQ (fun x hx => (Subgroup.relIndex_eq_one.1 h hx).2)
  have hpos := relIndex_pos' (B ⊓ (L ⊔ QM L M)) B
  omega

theorem even_n (hP : PairFacts H P B D) (hBLQ : ¬ B ≤ L ⊔ QM L M) : Even n := by
  obtain ⟨x, hx, hxn⟩ := IsConcreteLE.not_le_iff_exists.1 hBLQ
  exact H.even_of_not_mem (x := ⟨x, hP.B_le_M hx⟩)
    (Subtype.ext (by simpa using hP.B_sq x hx)) hxn

theorem chi_ne_one (hP : PairFacts H P B D) {x : G} (hx : x ∈ B) (hxn : x ∉ L ⊔ QM L M) :
    H.chi ⟨x, hP.B_le_M hx⟩ ≠ 1 :=
  H.chi_ne_one_of_not_mem (x := ⟨x, hP.B_le_M hx⟩) (Subtype.ext (by simpa using hP.B_sq x hx)) hxn

end PairFacts

end CFSG.CGT.PushingUpLit.T2KR
