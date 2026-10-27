module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.RootCheck
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux.Plane
public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Malle.LocalAction CFSG.RankThree.PartOne.SEITZ3
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux

section Frame

variable (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a p : ℕ)

structure ReePlane where
  D : ReeFrameData K (AlgebraicClosure K) a
  w : WeylGroup ReeTag.F4.tag
  U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ
  g₀ : ModGL ReeTag.F4.tag (AlgebraicClosure K)
  hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag (AlgebraicClosure K)
  hFg₀ : Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) (AlgebraicClosure K) w
  Ψ : (rootsOfUnity p (AlgebraicClosure K)) × (rootsOfUnity p (AlgebraicClosure K)) →*
    ReeTag.F4.reeGamma K a
  Ψinj : Function.Injective Ψ
  hΨ : ∀ z, reeConj g₀ (Ψ z) = rootDiagUnit ReeTag.F4.tag
    (expTuple ((z.1 : (AlgebraicClosure K)ˣ)) (z.2 : (AlgebraicClosure K)ˣ) U)
  hF1 : ∀ β ∈ rootFinset ReeTag.F4.tag,
    ¬ (((∑ i, U 0 i * β i : ℤ) : ZMod p) = 0 ∧ ((∑ i, U 1 i * β i : ℤ) : ZMod p) = 0)

variable {K a p}

theorem exists_plane_of_data (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : Odd p)
    (w : WeylGroup ReeTag.F4.tag) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ)
    (i j : Fin 4)
    (hW : ∀ k l : Fin ReeTag.F4.tag.rank,
      (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin 4),
      (∑ l, U s l * Wm l k) ≡
        U s ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
          (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
            ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) [ZMOD p])
    (hF1 : ∀ β ∈ rootFinset ReeTag.F4.tag,
      ¬ (((∑ i, U 0 i * β i : ℤ) : ZMod p) = 0 ∧ ((∑ i, U 1 i * β i : ℤ) : ZMod p) = 0)) :
    Nonempty (ReePlane K a p) := by
  classical
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Φ, hΦinj, hΦF, hΦ⟩ := exists_hom_twisted_explicit D.isFrob w hp Wm U i j hW hdet hfix
  obtain ⟨g₀, hg₀, hFg₀, Ψ, hΨinj, hΨ⟩ := exists_hom_reeGamma_explicit D w Φ hΦinj hΦF
  refine ⟨⟨D, w, U, g₀, hg₀, hFg₀, Ψ, hΨinj, fun z => ?_, hF1⟩⟩
  rw [reeConj_apply, hΨ z, ← hΦ z]
  group

end Frame

section Cases

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem exists_plane_phi1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) - 1) : Nonempty (ReePlane K a p) := by
  have hW : wordMat ReeTag.F4.tag [] =
      toMat ReeTag.F4.tag.rank [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_plane_of_data hK (hp.odd_of_ne_two (by omega)) wPhi1
    (toMat 4 [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]) (U1 (2 ^ a)) 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_ ?_
  · exact ⟨1, 0, by norm_num [U1]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, U1] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨1, ?_⟩; ring1)
  · refine regular_roots_phi1 hp hp3 (v := 2 ^ a) ?_
    have h : (2 : ℤ) * ((2 : ℤ) ^ a) ^ 2 - 1 = 2 ^ (2 * a + 1) - 1 := by ring
    rw [h]
    exact hmM

theorem exists_plane_phi2 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) + 1) : Nonempty (ReePlane K a p) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_plane_of_data hK (hp.odd_of_ne_two (by omega)) wPhi2
    (toMat 4 [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]]) (U2 (2 ^ a)) 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_ ?_
  · exact ⟨-1, 0, by norm_num [U2]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, U2] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)
  · refine regular_roots_phi2 hp hp3 (v := 2 ^ a) ?_
    have h : (2 : ℤ) * ((2 : ℤ) ^ a) ^ 2 + 1 = 2 ^ (2 * a + 1) + 1 := by ring
    rw [h]
    exact hmM

theorem exists_plane_phi4m (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) :
    Nonempty (ReePlane K a p) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_plane_of_data hK (hp.odd_of_ne_two (by omega)) wPhi4m
    (toMat 4 [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]]) (U4m (2 ^ a)) 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_ ?_
  · exact ⟨1, 0, by norm_num [U4m]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, U4m] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)
  · refine regular_roots_phi4m hp hp3 (v := 2 ^ a) ?_
    have h : (2 : ℤ) * ((2 : ℤ) ^ a) ^ 2 - 2 * 2 ^ a + 1 = 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
      ring
    rw [h]
    exact hmM

theorem exists_plane_phi4p (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) :
    Nonempty (ReePlane K a p) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_plane_of_data hK (hp.odd_of_ne_two (by omega)) wPhi4p
    (toMat 4 [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]]) (U4p (2 ^ a)) 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_ ?_
  · exact ⟨1, 0, by norm_num [U4p]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, U4p] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)
  · refine regular_roots_phi4p hp hp3 (v := 2 ^ a) ?_
    have h : (2 : ℤ) * ((2 : ℤ) ^ a) ^ 2 + 2 * 2 ^ a + 1 = 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
      ring
    rw [h]
    exact hmM

end Cases

section PlaneElt

variable {L : Type} [Field L] {p : ℕ}

theorem exists_primitive_root_two (hp : p.Prime) (hp2 : p ≠ 2) [CharP L 2] [IsAlgClosed L] :
    ∃ ξ : Lˣ, IsPrimitiveRoot ξ p := by
  have hpL : (p : L) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff L 2 p).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hpL⟩
  obtain ⟨ξ₀, hξ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  lift ξ₀ to Lˣ using hξ₀.isUnit hp.ne_zero
  rw [IsPrimitiveRoot.coe_units_iff] at hξ₀
  exact ⟨ξ₀, hξ₀⟩

theorem mem_rootsOfUnity_pow {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ p) (s : ℕ) :
    ξ ^ s ∈ rootsOfUnity p L := by
  rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]

@[expose] def planeElt {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ p) (s t : ℕ) :
    (rootsOfUnity p L) × (rootsOfUnity p L) :=
  (⟨ξ ^ s, mem_rootsOfUnity_pow hξ s⟩, ⟨ξ ^ t, mem_rootsOfUnity_pow hξ t⟩)

theorem planeElt_ne_one {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ p) {s t : ℕ}
    (h : (s : ZMod p) ≠ 0 ∨ (t : ZMod p) ≠ 0) : planeElt hξ s t ≠ 1 := by
  intro h1
  rcases h with h | h
  · apply h
    have h2 : ξ ^ s = 1 := congrArg (fun z : (rootsOfUnity p L) × (rootsOfUnity p L) =>
      ((z.1 : rootsOfUnity p L) : Lˣ)) h1
    rw [hξ.pow_eq_one_iff_dvd] at h2
    exact (ZMod.natCast_eq_zero_iff s p).2 h2
  · apply h
    have h2 : ξ ^ t = 1 := congrArg (fun z : (rootsOfUnity p L) × (rootsOfUnity p L) =>
      ((z.2 : rootsOfUnity p L) : Lˣ)) h1
    rw [hξ.pow_eq_one_iff_dvd] at h2
    exact (ZMod.natCast_eq_zero_iff t p).2 h2

theorem rootChar_expTuple_pow_iff {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ p)
    (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (x y : ℕ) (β : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (expTuple (ξ ^ x) (ξ ^ y) U) β = 1 ↔
      ((((x : ℤ) * ∑ i, U 0 i * β i + (y : ℤ) * ∑ i, U 1 i * β i : ℤ)) : ZMod p) = 0 := by
  rw [rootChar_expTuple, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
    hξ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]

end PlaneElt

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big
