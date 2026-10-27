module

public import CFSG.LieType.Ree.LargeReeInvolutionFusionCoords

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

inductive Idx
  | i1 | i2 | i3 | i4 | i5 | i6 | i7 | i8 | i9 | i10 | i11 | i12
  deriving DecidableEq, Repr

instance : Fintype Idx :=
  Fintype.ofList [.i1, .i2, .i3, .i4, .i5, .i6, .i7, .i8, .i9, .i10, .i11, .i12]
    fun x => by cases x <;> simp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (twoSet fourSet)
open CFSG.LieType.Chevalley.RootOps (orbitCertRoot)

namespace Idx

@[expose] def isSz : Idx → Bool
  | .i1 | .i4 | .i5 | .i6 => true
  | _ => false

@[expose] def isLin : Idx → Bool
  | .i3 | .i7 | .i9 | .i10 => true
  | _ => false

@[expose] def isCenter : Idx → Bool
  | .i2 | .i8 | .i11 | .i12 => true
  | _ => false

@[expose] def base : Idx → Idx
  | .i2 => .i1
  | .i8 => .i4
  | .i11 => .i6
  | .i12 => .i5
  | i => i

@[expose] def center : Idx → Idx
  | .i1 => .i2
  | .i4 => .i8
  | .i5 => .i12
  | .i6 => .i11
  | i => i

@[expose] def coord : Idx → Fin 12
  | .i1 => 1
  | .i2 => 2
  | .i3 => 0
  | .i4 => 3
  | .i5 => 7
  | .i6 => 5
  | .i7 => 9
  | .i8 => 4
  | .i9 => 10
  | .i10 => 11
  | .i11 => 6
  | .i12 => 8

@[expose] def ofCoord (n : Fin 12) : Idx :=
  ![.i3, .i1, .i2, .i4, .i8, .i6, .i11, .i5, .i12, .i7, .i9, .i10] n

theorem coord_ofCoord (n : Fin 12) : (ofCoord n).coord = n := by
  fin_cases n <;> rfl

theorem ofCoord_coord (i : Idx) : ofCoord i.coord = i := by
  cases i <;> rfl

@[expose] def coords (i : Idx) : Finset (Fin 12) :=
  if i.isSz then {i.coord, i.center.coord} else {i.coord}

@[expose] def pos : Idx → Fin 8
  | .i1 | .i2 => 0
  | .i7 => 1
  | .i6 | .i11 => 2
  | .i10 => 3
  | .i5 | .i12 => 4
  | .i9 => 5
  | .i4 | .i8 => 6
  | .i3 => 7

@[expose] def fourIdx : Idx → Fin 4
  | .i4 | .i8 => 1
  | .i6 | .i11 => 2
  | .i5 | .i12 => 3
  | _ => 0

@[expose] def twoIdx : Idx → Fin 4
  | .i7 => 1
  | .i9 => 2
  | .i10 => 3
  | _ => 0

@[expose] def sPerm : Idx → Idx
  | .i1 => .i4
  | .i4 => .i1
  | .i2 => .i8
  | .i8 => .i2
  | .i5 => .i6
  | .i6 => .i5
  | .i12 => .i11
  | .i11 => .i12
  | .i7 => .i9
  | .i9 => .i7
  | .i10 => .i10
  | .i3 => .i3

@[expose] def rPerm : Idx → Idx
  | .i3 => .i7
  | .i7 => .i3
  | .i4 => .i6
  | .i6 => .i4
  | .i8 => .i11
  | .i11 => .i8
  | .i9 => .i10
  | .i10 => .i9
  | .i5 => .i5
  | .i12 => .i12
  | .i1 => .i1
  | .i2 => .i2

theorem isSz_or_isLin_or_isCenter (i : Idx) :
    i.isSz = true ∨ i.isLin = true ∨ i.isCenter = true := by
  cases i <;> simp [isSz, isLin, isCenter]

end Idx

section Definitions

variable (K : Type) [Field K] (a : ℕ)

@[expose] def rootElt :
    Idx → K → ModGL F4.tag K
  | .i1, u => sylowB a K u 0
  | .i2, u => sylowB a K 0 u
  | .i3, u => sylowA a K u
  | .i4, u => sylowD a K u 0
  | .i5, u => sylowH a K u 0
  | .i6, u => sylowF a K u 0
  | .i7, u => sylowJ a K u
  | .i8, u => sylowD a K 0 u
  | .i9, u => sylowK a K u
  | .i10, u => sylowL a K u
  | .i11, u => sylowF a K 0 u
  | .i12, u => sylowH a K 0 u

@[expose] def rootV (i : Idx) :
    Subgroup (ModGL F4.tag K) :=
  Subgroup.closure (Set.range (rootElt K a i))

@[expose] def rootJoin
    (I : Finset Idx) : Subgroup (ModGL F4.tag K) :=
  ⨆ i ∈ I, rootV K a i

@[expose] def radR :
    Subgroup (ModGL F4.tag K) :=
  rootJoin K a {.i3, .i4, .i5, .i6, .i7, .i9, .i10}

@[expose] def radS :
    Subgroup (ModGL F4.tag K) :=
  rootJoin K a {.i1, .i4, .i5, .i6, .i7, .i9, .i10}

@[expose] def R1 :
    Subgroup (ModGL F4.tag K) :=
  rootJoin K a {.i8, .i9, .i10, .i11, .i12}

@[expose] def S1 :
    Subgroup (ModGL F4.tag K) :=
  rootJoin K a {.i11, .i12}

@[expose] def S2 :
    Subgroup (ModGL F4.tag K) :=
  rootJoin K a {.i10, .i11, .i12}

@[expose] def S3 :
    Subgroup (ModGL F4.tag K) :=
  rootJoin K a {.i7, .i9, .i10, .i11, .i12}

@[expose] def S4 :
    Subgroup (ModGL F4.tag K) :=
  rootJoin K a {.i2, .i5, .i6, .i8, .i7, .i9, .i10, .i11, .i12}

@[expose] def torusH :
    Subgroup (ModGL F4.tag K) :=
  (LargeReeCover.torusPair (K := K) a).range

@[expose] def torusHi (i : Idx) :
    Subgroup (ModGL F4.tag K) :=
  torusH K a ⊓ Subgroup.centralizer (rootV K a i : Set (ModGL F4.tag K))

abbrev weylR : ModGL F4.tag K :=
  weylTwo K

abbrev weylS : ModGL F4.tag K :=
  weylOne K

@[expose] def leviN [Finite K] [CharP K F4.prime] :
    Idx → Subgroup (ModGL F4.tag K)
  | .i1 | .i2 => rankOneGroupTwo K a
  | .i3 => rankOneGroupOne K a
  | .i4 | .i8 => (rankOneGroupTwo K a).map (MulAut.conj (weylS K)).toMonoidHom
  | .i6 | .i11 => (rankOneGroupTwo K a).map (MulAut.conj (weylR K * weylS K)).toMonoidHom
  | .i5 | .i12 =>
    (rankOneGroupTwo K a).map (MulAut.conj (weylS K * weylR K * weylS K)).toMonoidHom
  | .i7 => (rankOneGroupOne K a).map (MulAut.conj (weylR K)).toMonoidHom
  | .i9 => (rankOneGroupOne K a).map (MulAut.conj (weylS K * weylR K)).toMonoidHom
  | .i10 =>
    (rankOneGroupOne K a).map (MulAut.conj (weylR K * weylS K * weylR K)).toMonoidHom

@[expose] def invE :
    ModGL F4.tag K :=
  rootElt K a .i12 1

@[expose] def invF :
    ModGL F4.tag K :=
  rootElt K a .i10 1

end Definitions


section Zero

variable {K : Type} [Field K] {a : ℕ}

theorem wordD_zero : sylowD a K 0 0 = 1 := by
  simp [sylowD, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem wordF_zero : sylowF a K 0 0 = 1 := by
  simp [sylowF, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem wordH_zero : sylowH a K 0 0 = 1 := by
  simp [sylowH, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem wordJ_zero : sylowJ a K 0 = 1 := by
  simp [sylowJ, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem wordK_zero : sylowK a K 0 = 1 := by
  simp [sylowK, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem wordL_zero : sylowL a K 0 = 1 := by
  simp [sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem rootElt_zero (i : Idx) : rootElt K a i 0 = 1 := by
  cases i <;> simp [rootElt, sylowA_zero, sylowB_zero_zero, wordD_zero, wordF_zero, wordH_zero,
    wordJ_zero, wordK_zero, wordL_zero]

theorem rootElt_eq_sylowVec (i : Idx) (u : K) :
    rootElt K a i u = sylowVec a K (Pi.single i.coord u) := by
  cases i <;> simp [rootElt, sylowVec, sylowV, Idx.coord, sylowA_zero, sylowB_zero_zero,
    wordD_zero, wordF_zero, wordH_zero, wordJ_zero, wordK_zero, wordL_zero]

theorem rootElt_mem_rootV (i : Idx) (u : K) : rootElt K a i u ∈ rootV K a i :=
  Subgroup.subset_closure ⟨u, rfl⟩

theorem rootV_le_rootJoin {I : Finset Idx} {i : Idx} (hi : i ∈ I) :
    rootV K a i ≤ rootJoin K a I :=
  le_iSup₂_of_le i hi le_rfl

theorem rootJoin_mono {I J : Finset Idx} (h : I ⊆ J) : rootJoin K a I ≤ rootJoin K a J :=
  iSup₂_le fun _ hi => rootV_le_rootJoin (h hi)

end Zero

theorem exists_largeReeSigma_mul_self_eq {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) : ∃ w : K, largeReeSigma a w * w = c := by
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have hq' : Fintype.card K = 2 * (2 ^ a * 2 ^ a) := by rw [hq, pow_succ, pow_mul']; ring
  have hexp : (2 * 2 ^ a - 1) * (2 * 2 ^ a) + (2 * 2 ^ a - 1) =
      Fintype.card K + (Fintype.card K - 1) := by
    rw [hq']
    have h0 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have h1 : 1 ≤ 2 * 2 ^ a := by omega
    have h2 : 1 ≤ 2 * (2 ^ a * 2 ^ a) := by nlinarith
    zify [h1, h2]
    ring
  refine ⟨c ^ (2 * 2 ^ a - 1), ?_⟩
  rw [largeReeSigma, ← pow_mul, ← pow_add, hexp, pow_add, FiniteField.pow_card]
  by_cases hc : c = 0
  · subst hc
    exact zero_mul _
  · rw [FiniteField.pow_card_sub_one_eq_one c hc, mul_one]

theorem exists_largeReeSigma_ne {K : Type} [Field K] [Finite K] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : ∃ l : K, largeReeSigma a l ≠ l := by
  by_contra! h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have h2 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h1 : g ^ (2 * 2 ^ a - 1) = 1 := by
    have hσ := h g
    have e : (g : K) ^ (2 * 2 ^ a) = (g : K) ^ (2 * 2 ^ a - 1) * g := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    apply Units.ext
    rw [largeReeSigma, e] at hσ
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (mul_eq_right₀ g.ne_zero).1 hσ
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hord, hK] at hdvd
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hq : 2 ^ (2 * a + 1) = 2 * (2 ^ a * 2 ^ a) := by rw [pow_succ, pow_mul']; ring
  have h3 : 2 * 2 ^ a ≤ 2 ^ a * 2 ^ a := Nat.mul_le_mul_right _ h2
  rw [hq] at hle
  set A := 2 ^ a * 2 ^ a
  set B := 2 ^ a
  omega

theorem coe_closure_range_of_add {K G : Type*} [AddGroup K] [Group G] {φ : K → G}
    (h0 : φ 0 = 1) (hadd : ∀ u v, φ (u + v) = φ u * φ v) :
    (Subgroup.closure (Set.range φ) : Set G) = Set.range φ := by
  let ψ : Multiplicative K →* G := ⟨⟨fun u => φ u.toAdd, h0⟩, fun u v => hadd u.toAdd v.toAdd⟩
  have hr : (ψ.range : Set G) = Set.range φ := by
    rw [MonoidHom.coe_range]
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.toAdd, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨Multiplicative.ofAdd u, rfl⟩
  rw [← hr, Subgroup.closure_eq]

section Blocks

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem fourCoordG_mul_fourCoordG (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : Fin 4)
    (b c b' c' : K) :
    fourCoordG a f b c * fourCoordG a f b' c' =
      fourCoordG a f (b + b') (c + c' + largeReeSigma a b * b') := by
  have e : ∀ n A B : ModGL F4.tag K, n * A * n⁻¹ * (n * B * n⁻¹) = n * (A * B) * n⁻¹ :=
    fun _ _ _ => by group
  have key : stdFourG a b c * stdFourG a b' c' =
      stdFourG a (b + b') (c + c' + largeReeSigma a b * b') := by
    rw [stdFourG_eq_largeReeCoord, stdFourG_eq_largeReeCoord, stdFourG_eq_largeReeCoord]
    exact largeReeCoord_mul hK b c b' c'
  rw [fourCoordG, fourCoordG, fourCoordG, e, key]

omit [Finite K] in
theorem rootElt_eq_coord (i : Idx) (u : K) :
    (i.isSz = true → rootElt K a i u = fourCoordG a i.fourIdx u 0) ∧
      (i.isCenter = true → rootElt K a i u = fourCoordG a i.fourIdx 0 u) ∧
        (i.isLin = true → rootElt K a i u = twoCoordG a i.twoIdx u) := by
  cases i <;> simp [Idx.isSz, Idx.isCenter, Idx.isLin, rootElt, Idx.fourIdx, Idx.twoIdx,
    sylowA_eq, sylowB_eq, sylowD_eq, sylowF_eq, sylowH_eq, sylowJ_eq, sylowK_eq, sylowL_eq]

omit [Finite K] in
theorem sylowVec_eq_of_supp (i : Idx) {x : Fin 12 → K} (hx : ∀ n ∉ i.coords, x n = 0) :
    (i.isSz = true →
        sylowVec a K x = fourCoordG a i.fourIdx (x i.coord) (x i.center.coord)) ∧
      (i.isSz = false → sylowVec a K x = rootElt K a i (x i.coord)) := by
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · have hz : ∀ n : Fin 12, n ≠ i.coord → n ≠ i.center.coord → x n = 0 := fun n h1 h2 =>
      hx n (by simp [Idx.coords, hi, h1, h2])
    cases i <;> simp only [Idx.isSz, Bool.false_eq_true] at hi <;>
      simp only [Idx.coord, Idx.center, Idx.fourIdx] at hz ⊢
    · rw [sylowVec, sylowV, hz 0 (by decide) (by decide), hz 3 (by decide) (by decide),
        hz 4 (by decide) (by decide), hz 5 (by decide) (by decide), hz 6 (by decide) (by decide),
        hz 7 (by decide) (by decide), hz 8 (by decide) (by decide), hz 9 (by decide) (by decide),
        hz 10 (by decide) (by decide), hz 11 (by decide) (by decide), sylowA_zero, wordD_zero,
        wordF_zero, wordH_zero, wordJ_zero, wordK_zero, wordL_zero, sylowB_eq]
      simp only [one_mul, mul_one]
    · rw [sylowVec, sylowV, hz 0 (by decide) (by decide), hz 1 (by decide) (by decide),
        hz 2 (by decide) (by decide), hz 5 (by decide) (by decide), hz 6 (by decide) (by decide),
        hz 7 (by decide) (by decide), hz 8 (by decide) (by decide), hz 9 (by decide) (by decide),
        hz 10 (by decide) (by decide), hz 11 (by decide) (by decide), sylowA_zero,
        sylowB_zero_zero, wordF_zero, wordH_zero, wordJ_zero, wordK_zero, wordL_zero, sylowD_eq]
      simp only [one_mul, mul_one]
    · rw [sylowVec, sylowV, hz 0 (by decide) (by decide), hz 1 (by decide) (by decide),
        hz 2 (by decide) (by decide), hz 3 (by decide) (by decide), hz 4 (by decide) (by decide),
        hz 5 (by decide) (by decide), hz 6 (by decide) (by decide), hz 9 (by decide) (by decide),
        hz 10 (by decide) (by decide), hz 11 (by decide) (by decide), sylowA_zero,
        sylowB_zero_zero, wordD_zero, wordF_zero, wordJ_zero, wordK_zero, wordL_zero, sylowH_eq]
      simp only [one_mul, mul_one]
    · rw [sylowVec, sylowV, hz 0 (by decide) (by decide), hz 1 (by decide) (by decide),
        hz 2 (by decide) (by decide), hz 3 (by decide) (by decide), hz 4 (by decide) (by decide),
        hz 7 (by decide) (by decide), hz 8 (by decide) (by decide), hz 9 (by decide) (by decide),
        hz 10 (by decide) (by decide), hz 11 (by decide) (by decide), sylowA_zero,
        sylowB_zero_zero, wordD_zero, wordH_zero, wordJ_zero, wordK_zero, wordL_zero, sylowF_eq]
      simp only [one_mul, mul_one]
  · have hxe : x = Pi.single i.coord (x i.coord) := by
      funext n
      by_cases hn : n = i.coord
      · subst hn
        simp
      · rw [Pi.single_eq_of_ne hn]
        exact hx n (by simp [Idx.coords, hi, hn])
    rw [rootElt_eq_sylowVec, ← hxe]

theorem rootElt_add_of_isCenter (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isCenter = true) (u v : K) :
    rootElt K a i (u + v) = rootElt K a i u * rootElt K a i v := by
  rw [(rootElt_eq_coord i _).2.1 hi, (rootElt_eq_coord i _).2.1 hi, (rootElt_eq_coord i _).2.1 hi,
    fourCoordG_mul_fourCoordG hK, largeReeSigma_zero, zero_mul, add_zero, add_zero]

theorem coe_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    (rootV K a i : Set (ModGL F4.tag K)) = sylowVec a K '' {x | ∀ n ∉ i.coords, x n = 0} := by
  have hsingle : ∀ u : K, Pi.single i.coord u ∈ {x : Fin 12 → K | ∀ n ∉ i.coords, x n = 0} := by
    intro u n hn
    have hc : i.coord ∈ i.coords := by
      rw [Idx.coords]
      split <;> simp
    have hne : n ≠ i.coord := fun h => hn (by rw [h]; exact hc)
    simp [hne]
  rcases i.isSz_or_isLin_or_isCenter with hi | hi | hi
  ·
    have hle : rootV K a i ≤ largeReeBlockGroup K a (fourSet i.fourIdx) := by
      rw [rootV, Subgroup.closure_le]
      rintro _ ⟨u, rfl⟩
      rw [(rootElt_eq_coord i u).1 hi]
      exact fourCoordG_mem_block hK _ _ _
    ext g
    constructor
    · intro hg
      obtain ⟨b, c, rfl⟩ := exists_fourCoordG_eq hK _ (hle hg)
      refine ⟨Function.update (Pi.single i.coord b) i.center.coord c, fun n hn => ?_, ?_⟩
      · have h1 : n ≠ i.coord := fun h => hn (by simp [Idx.coords, hi, h])
        have h2 : n ≠ i.center.coord := fun h => hn (by simp [Idx.coords, hi, h])
        rw [Function.update_of_ne h2, Pi.single_eq_of_ne h1]
      · have hne : i.coord ≠ i.center.coord := by
          cases i <;> simp_all [Idx.isSz, Idx.coord, Idx.center]
        rw [(sylowVec_eq_of_supp i (x := Function.update (Pi.single i.coord b) i.center.coord c)
          (fun n hn => ?_)).1 hi, Function.update_of_ne hne, Pi.single_eq_same,
          Function.update_self]
        have h1 : n ≠ i.coord := fun h => hn (by simp [Idx.coords, hi, h])
        have h2 : n ≠ i.center.coord := fun h => hn (by simp [Idx.coords, hi, h])
        rw [Function.update_of_ne h2, Pi.single_eq_of_ne h1]
    · rintro ⟨x, hx, rfl⟩
      rw [(sylowVec_eq_of_supp i hx).1 hi]
      obtain ⟨w, hw⟩ := exists_largeReeSigma_mul_self_eq hK (x i.center.coord)
      have e : fourCoordG a i.fourIdx (x i.coord) (x i.center.coord) =
          rootElt K a i (x i.coord) * rootElt K a i w * rootElt K a i w := by
        obtain ⟨σ, hσ, -⟩ := exists_sigma (m := a) hK
        rw [(rootElt_eq_coord i _).1 hi, (rootElt_eq_coord i _).1 hi,
          fourCoordG_mul_fourCoordG hK, fourCoordG_mul_fourCoordG hK]
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        congr 1
        · linear_combination (-w) * h2
        · rw [← hσ, ← hσ, map_add, hσ, hσ, ← hw]
          linear_combination (-(largeReeSigma a (x i.coord) * w)) * h2
      rw [e, SetLike.mem_coe]
      exact mul_mem (mul_mem (Subgroup.subset_closure ⟨_, rfl⟩) (Subgroup.subset_closure ⟨_, rfl⟩))
        (Subgroup.subset_closure ⟨_, rfl⟩)
  ·
    have hsz : i.isSz = false := by cases i <;> simp_all [Idx.isSz, Idx.isLin]
    have hle : rootV K a i ≤ largeReeBlockGroup K a (twoSet i.twoIdx) := by
      rw [rootV, Subgroup.closure_le]
      rintro _ ⟨u, rfl⟩
      rw [(rootElt_eq_coord i u).2.2 hi]
      exact twoCoordG_mem_block hK _ _
    ext g
    constructor
    · intro hg
      obtain ⟨u, rfl⟩ := exists_twoCoordG_eq hK _ (hle hg)
      exact ⟨Pi.single i.coord u, hsingle u, by
        rw [← rootElt_eq_sylowVec, (rootElt_eq_coord i u).2.2 hi]⟩
    · rintro ⟨x, hx, rfl⟩
      rw [(sylowVec_eq_of_supp i hx).2 hsz]
      exact Subgroup.subset_closure ⟨_, rfl⟩
  ·
    have hsz : i.isSz = false := by cases i <;> simp_all [Idx.isSz, Idx.isCenter]
    rw [rootV, coe_closure_range_of_add (rootElt_zero i) (rootElt_add_of_isCenter hK hi)]
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨Pi.single i.coord u, hsingle u, (rootElt_eq_sylowVec i u).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x i.coord, ((sylowVec_eq_of_supp i hx).2 hsz).symm⟩

theorem card_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    Nat.card (rootV K a i) = (2 ^ (2 * a + 1)) ^ (if i.isSz then 2 else 1) := by
  have hc : i.coords.card = if i.isSz then 2 else 1 := by
    cases i <;> rfl
  have h := card_image_sylowVec (m := a) hK (i.coords)ᶜ
  have hS : {x : Fin 12 → K | ∀ n ∈ (i.coords)ᶜ, x n = 0} = {x | ∀ n ∉ i.coords, x n = 0} := by
    ext x
    simp [Finset.mem_compl]
  have hle : i.coords.card ≤ 12 := by
    cases i <;> decide
  rw [hS, ← coe_rootV hK i, Finset.card_compl, Fintype.card_fin,
    show 12 - (12 - i.coords.card) = i.coords.card by omega, hc] at h
  exact h

theorem rootV_le_sylowP (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    rootV K a i ≤ F4.reeFixedPosUnipotent K a := by
  intro g hg
  have hg' : g ∈ (rootV K a i : Set (ModGL F4.tag K)) := hg
  rw [coe_rootV hK] at hg'
  obtain ⟨x, -, rfl⟩ := hg'
  exact (bijOn_sylowVec hK).1 (Set.mem_univ x)

theorem rootV_le_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    rootV K a i ≤ F4.reeGamma K a :=
  (rootV_le_sylowP hK i).trans inf_le_right

theorem rootV_le_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) {i j : Idx}
    (h : i.coords ⊆ j.coords) : rootV K a i ≤ rootV K a j := by
  intro g hg
  have hg' : g ∈ (rootV K a i : Set (ModGL F4.tag K)) := hg
  rw [coe_rootV hK] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  have hmem : sylowVec a K x ∈ (rootV K a j : Set (ModGL F4.tag K)) := by
    rw [coe_rootV hK]
    exact ⟨x, fun n hn => hx n fun h' => hn (h h'), rfl⟩
  exact hmem

theorem rootV_center_le (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    rootV K a i.center ≤ rootV K a i ∧ rootV K a i ≤ rootV K a i.base :=
  ⟨rootV_le_rootV hK (by cases i <;> decide), rootV_le_rootV hK (by cases i <;> decide)⟩

theorem rootV_inf_centralizer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isSz = true) :
    rootV K a i ⊓ Subgroup.centralizer (rootV K a i : Set (ModGL F4.tag K)) =
      rootV K a i.center := by
  have hci : i.center.isCenter = true := by
    cases i <;> simp_all [Idx.isSz, Idx.center, Idx.isCenter]
  have hf : i.center.fourIdx = i.fourIdx := by
    cases i <;> simp_all [Idx.isSz, Idx.center, Idx.fourIdx]
  have hcsz : i.center.isSz = false := by cases i <;> simp_all [Idx.isSz, Idx.center]
  have hV : ∀ g ∈ rootV K a i, ∃ b c : K, g = fourCoordG a i.fourIdx b c := by
    intro g hg
    have hg' : g ∈ (rootV K a i : Set (ModGL F4.tag K)) := hg
    rw [coe_rootV hK] at hg'
    obtain ⟨x, hx, rfl⟩ := hg'
    exact ⟨_, _, (sylowVec_eq_of_supp i hx).1 hi⟩
  have hZ : ∀ g ∈ rootV K a i.center, ∃ c : K, g = fourCoordG a i.fourIdx 0 c := by
    intro g hg
    have hg' : g ∈ (rootV K a i.center : Set (ModGL F4.tag K)) := hg
    rw [coe_rootV hK] at hg'
    obtain ⟨x, hx, rfl⟩ := hg'
    rw [(sylowVec_eq_of_supp i.center hx).2 hcsz, (rootElt_eq_coord _ _).2.1 hci, hf]
    exact ⟨_, rfl⟩
  refine le_antisymm (fun g hg' => ?_) fun g hg =>
    Subgroup.mem_inf.2 ⟨(rootV_center_le hK i).1 hg, ?_⟩
  · obtain ⟨hg, hgc⟩ := Subgroup.mem_inf.1 hg'
    obtain ⟨b, c, rfl⟩ := hV g hg
    by_cases hb : b = 0
    · subst hb
      rw [← hf, ← (rootElt_eq_coord _ _).2.1 hci]
      exact rootElt_mem_rootV _ _
    · exfalso
      obtain ⟨l, hl⟩ := exists_largeReeSigma_ne ha hK
      have hmem : fourCoordG a i.fourIdx (l * b) 0 ∈ rootV K a i := by
        rw [← (rootElt_eq_coord i _).1 hi]
        exact rootElt_mem_rootV _ _
      have hcomm := Subgroup.mem_centralizer_iff.1 hgc _ hmem
      rw [fourCoordG_mul_fourCoordG hK, fourCoordG_mul_fourCoordG hK] at hcomm
      have h2 := (fourCoordG_injective hK _ hcomm).2
      have hσ : largeReeSigma a (l * b) = largeReeSigma a l * largeReeSigma a b := by
        simp only [largeReeSigma, mul_pow]
      rw [hσ] at h2
      have hσb : largeReeSigma a b ≠ 0 := fun h0 => hb ((largeReeSigma_eq_zero_iff b).1 h0)
      have key : largeReeSigma a b * b * (largeReeSigma a l - l) = 0 := by
        linear_combination h2
      rcases mul_eq_zero.1 key with h | h
      · exact mul_ne_zero hσb hb h
      · exact hl (sub_eq_zero.1 h)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨b, c, rfl⟩ := hV h hh
    obtain ⟨d, rfl⟩ := hZ g hg
    rw [fourCoordG_mul_fourCoordG hK, fourCoordG_mul_fourCoordG hK, largeReeSigma_zero, zero_mul,
      mul_zero, add_zero, add_zero, add_zero, zero_add, add_comm c d]

theorem fourCoordG_eq_mul (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : Fin 4) (b c : K) :
    fourCoordG a f b c = fourCoordG a f b 0 * fourCoordG a f 0 c := by
  rw [fourCoordG_mul_fourCoordG hK, add_zero, zero_add, mul_zero, add_zero]

theorem sylowVec_eq_prod_rootElt (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : Fin 12 → K) :
    sylowVec a K x = rootElt K a .i3 (x 0) * rootElt K a .i1 (x 1) * rootElt K a .i2 (x 2) *
      rootElt K a .i4 (x 3) * rootElt K a .i8 (x 4) * rootElt K a .i6 (x 5) *
      rootElt K a .i11 (x 6) * rootElt K a .i5 (x 7) * rootElt K a .i12 (x 8) *
      rootElt K a .i7 (x 9) * rootElt K a .i9 (x 10) * rootElt K a .i10 (x 11) := by
  simp only [rootElt, sylowVec, sylowV]
  rw [sylowB_eq, sylowB_eq, sylowB_eq, fourCoordG_eq_mul hK, sylowD_eq, sylowD_eq, sylowD_eq,
    fourCoordG_eq_mul hK (f := 1), sylowF_eq, sylowF_eq, sylowF_eq, fourCoordG_eq_mul hK (f := 2),
    sylowH_eq, sylowH_eq, sylowH_eq, fourCoordG_eq_mul hK (f := 3)]
  simp only [mul_assoc]

theorem bijOn_prod_rootElt (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Set.BijOn (fun x : Fin 12 → K => rootElt K a .i3 (x 0) * rootElt K a .i1 (x 1) *
      rootElt K a .i2 (x 2) * rootElt K a .i4 (x 3) * rootElt K a .i8 (x 4) *
      rootElt K a .i6 (x 5) * rootElt K a .i11 (x 6) * rootElt K a .i5 (x 7) *
      rootElt K a .i12 (x 8) * rootElt K a .i7 (x 9) * rootElt K a .i9 (x 10) *
      rootElt K a .i10 (x 11))
      Set.univ (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
  have e : (fun x : Fin 12 → K => rootElt K a .i3 (x 0) * rootElt K a .i1 (x 1) *
      rootElt K a .i2 (x 2) * rootElt K a .i4 (x 3) * rootElt K a .i8 (x 4) *
      rootElt K a .i6 (x 5) * rootElt K a .i11 (x 6) * rootElt K a .i5 (x 7) *
      rootElt K a .i12 (x 8) * rootElt K a .i7 (x 9) * rootElt K a .i9 (x 10) *
      rootElt K a .i10 (x 11)) = sylowVec a K :=
    funext fun x => (sylowVec_eq_prod_rootElt hK x).symm
  rw [e]
  exact bijOn_sylowVec hK

theorem rootJoin_le_of_coe (hK : Nat.card K = 2 ^ (2 * a + 1)) {I : Finset Idx}
    {Z : Finset (Fin 12)} {H : Subgroup (ModGL F4.tag K)}
    (hH : (H : Set (ModGL F4.tag K)) = sylowVec a K '' {x | ∀ n ∈ Z, x n = 0})
    (hI : ∀ i ∈ I, ∀ n ∈ Z, n ∉ i.coords) : rootJoin K a I ≤ H := by
  refine iSup₂_le fun i hi g hg => ?_
  have hg' : g ∈ (rootV K a i : Set (ModGL F4.tag K)) := hg
  rw [coe_rootV hK] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  have hmem : sylowVec a K x ∈ (H : Set (ModGL F4.tag K)) := by
    rw [hH]
    exact ⟨x, fun n hn => hx n (hI i hi n hn), rfl⟩
  exact hmem

theorem le_rootJoin_of_coe (hK : Nat.card K = 2 ^ (2 * a + 1)) {I : Finset Idx}
    {Z : Finset (Fin 12)} {H : Subgroup (ModGL F4.tag K)}
    (hH : (H : Set (ModGL F4.tag K)) = sylowVec a K '' {x | ∀ n ∈ Z, x n = 0})
    (hI : ∀ i : Idx, i.coord ∉ Z → i ∈ I ∨ i.base ∈ I) : H ≤ rootJoin K a I := by
  intro g hg
  have hg' : g ∈ (H : Set (ModGL F4.tag K)) := hg
  rw [hH] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  have key : ∀ i : Idx, rootElt K a i (x i.coord) ∈ rootJoin K a I := by
    intro i
    by_cases hz : i.coord ∈ Z
    · rw [hx _ hz, rootElt_zero]
      exact one_mem _
    · rcases hI i hz with h | h
      · exact rootV_le_rootJoin h (rootElt_mem_rootV i _)
      · exact rootV_le_rootJoin h ((rootV_center_le hK i).2 (rootElt_mem_rootV i _))
  rw [sylowVec_eq_prod_rootElt hK]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem (key .i3) (key .i1)) (key .i2)) (key .i4)) (key .i8)) (key .i6)) (key .i11))
    (key .i5)) (key .i12)) (key .i7)) (key .i9)) (key .i10)

theorem rootJoin_eq_of_coe (hK : Nat.card K = 2 ^ (2 * a + 1)) {I : Finset Idx}
    {Z : Finset (Fin 12)} {H : Subgroup (ModGL F4.tag K)}
    (hH : (H : Set (ModGL F4.tag K)) = sylowVec a K '' {x | ∀ n ∈ Z, x n = 0})
    (hI : ∀ i ∈ I, ∀ n ∈ Z, n ∉ i.coords) (hI' : ∀ i : Idx, i.coord ∉ Z → i ∈ I ∨ i.base ∈ I) :
    rootJoin K a I = H :=
  le_antisymm (rootJoin_le_of_coe hK hH hI) (le_rootJoin_of_coe hK hH hI')

theorem rootJoin_le_rootJoin (hK : Nat.card K = 2 ^ (2 * a + 1)) {I J : Finset Idx}
    (h : ∀ i ∈ I, i ∈ J ∨ i.base ∈ J) : rootJoin K a I ≤ rootJoin K a J := by
  refine iSup₂_le fun i hi => ?_
  rcases h i hi with h' | h'
  · exact rootV_le_rootJoin h'
  · exact (rootV_center_le hK i).2.trans (rootV_le_rootJoin h')

theorem rootJoin_le_sylowP (hK : Nat.card K = 2 ^ (2 * a + 1)) (I : Finset Idx) :
    rootJoin K a I ≤ F4.reeFixedPosUnipotent K a :=
  iSup₂_le fun i _ => rootV_le_sylowP hK i

theorem rootJoin_univ (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rootJoin K a Finset.univ = F4.reeFixedPosUnipotent K a := by
  refine le_antisymm (rootJoin_le_sylowP hK _) (le_rootJoin_of_coe hK (Z := ∅) ?_
    fun i _ => Or.inl (Finset.mem_univ i))
  rw [show {x : Fin 12 → K | ∀ n ∈ (∅ : Finset (Fin 12)), x n = 0} = Set.univ by
    ext x
    simp, (bijOn_sylowVec hK).image_eq]

theorem S1_le_S2_le_S3_le_S4_le_radS (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S1 K a ≤ S2 K a ∧ S2 K a ≤ S3 K a ∧ S3 K a ≤ S4 K a ∧ S4 K a ≤ radS K a ∧
      R1 K a ≤ radR K a ∧ S2 K a ≤ R1 K a :=
  ⟨rootJoin_mono (by decide), rootJoin_mono (by decide), rootJoin_mono (by decide),
    rootJoin_le_rootJoin hK (by decide), rootJoin_le_rootJoin hK (by decide),
    rootJoin_mono (by decide)⟩

end Blocks

section Level

open CFSG.LieType.Ree.LargeReeCover (f4i)

@[expose] def level (ℓ β : Fin F4.tag.rank → ℤ) : ℤ :=
  ℓ (f4i 0) * β (f4i 0) + ℓ (f4i 1) * β (f4i 1) + ℓ (f4i 2) * β (f4i 2) +
    ℓ (f4i 3) * β (f4i 3)

@[expose] def levelSet (ℓ : Fin F4.tag.rank → ℤ) (t : ℤ) : Set (Fin F4.tag.rank → ℤ) :=
  {β | IsRoot F4.tag β ∧ 0 < height β ∧ t ≤ level ℓ β}

@[expose] def polyVanishes (Z : Finset (Fin 12)) (P : Poly) : Bool :=
  P.all fun m => m.any fun v => decide (v < 24 ∧ ∃ n ∈ Z, (n : ℕ) = v % 12)

section Basic


theorem nonneg_of_isRoot_of_height_pos {γ : Fin F4.tag.rank → ℤ} (hγ : IsRoot F4.tag γ)
    (hγp : 0 < height γ) (k : Fin F4.tag.rank) : 0 ≤ γ k := by
  rcases hγ.nonneg_or_nonpos with h | h
  · exact h k
  · exfalso
    have : height γ ≤ 0 := Finset.sum_nonpos fun k _ => h k
    omega

theorem levelSet_absorbs {ℓ : Fin F4.tag.rank → ℤ} (hℓ : ∀ k, 0 ≤ ℓ k) (t : ℤ) :
    ∀ α, IsRoot F4.tag α ∧ 0 < height α → ∀ β ∈ levelSet ℓ t, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      IsRoot F4.tag (m • α + n • β) → m • α + n • β ∈ levelSet ℓ t := by
  have hlev : ∀ {γ : Fin F4.tag.rank → ℤ}, IsRoot F4.tag γ → 0 < height γ → 0 ≤ level ℓ γ := by
    intro γ hγ hγp
    have := nonneg_of_isRoot_of_height_pos hγ hγp
    unfold level
    have h0 := mul_nonneg (hℓ (f4i 0)) (this (f4i 0))
    have h1 := mul_nonneg (hℓ (f4i 1)) (this (f4i 1))
    have h2 := mul_nonneg (hℓ (f4i 2)) (this (f4i 2))
    have h3 := mul_nonneg (hℓ (f4i 3)) (this (f4i 3))
    linarith
  rintro α ⟨hα, hαp⟩ β ⟨hβ, hβp, hβt⟩ m n hm hn hr
  have h1 := hlev hα hαp
  have h2 := hlev hβ hβp
  have e : level ℓ (m • α + n • β) = (m : ℤ) * level ℓ α + (n : ℤ) * level ℓ β := by
    simp only [level, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul]
    ring
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  refine ⟨hr, ?_, ?_⟩
  · rw [CFSG.LieType.Chevalley.height_nsmul_add_nsmul]
    nlinarith
  · rw [e]
    nlinarith

theorem levelSet_closed {ℓ : Fin F4.tag.rank → ℤ} (hℓ : ∀ k, 0 ≤ ℓ k) (t : ℤ) :
    ∀ α ∈ levelSet ℓ t, ∀ β ∈ levelSet ℓ t, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      IsRoot F4.tag (m • α + n • β) → m • α + n • β ∈ levelSet ℓ t :=
  fun α hα => levelSet_absorbs hℓ t α ⟨hα.1, hα.2.1⟩

end Basic

variable {K : Type} [Field K] {a : ℕ}

theorem coordVal_eq {x : Fin 12 → K} {v : ℕ} (hv : v < 24) :
    coordVal a (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) v =
      if v < 12 then x ⟨v % 12, Nat.mod_lt _ (by norm_num)⟩
      else largeReeSigma a (x ⟨v % 12, Nat.mod_lt _ (by norm_num)⟩) := by
  interval_cases v <;> rfl

theorem polyEval_eq_zero_of_polyVanishes {Z : Finset (Fin 12)} {P : Poly}
    (hP : polyVanishes Z P = true) {x : Fin 12 → K} (hx : ∀ n ∈ Z, x n = 0) :
    polyEval (coordVal a (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
      (x 11)) P = 0 := by
  unfold polyEval
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
  simp only [polyVanishes, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hP
  obtain ⟨v, hvm, hv24, n, hnZ, hn⟩ := hP m hm
  unfold monoEval
  refine List.prod_eq_zero (List.mem_map.2 ⟨v, hvm, ?_⟩)
  have hn' : n = ⟨v % 12, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext hn
  rw [coordVal_eq hv24, ← hn', hx n hnZ]
  split_ifs
  · rfl
  · exact largeReeSigma_zero

theorem coordVal_coe (x : Fin 12 → K) (n : Fin 12) :
    coordVal a (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) n =
      x n := by
  fin_cases n <;> rfl


theorem eq_zero_of_list_prod_mem_rootSpan {Q : Set (Fin F4.tag.rank → ℤ)}
    (hQ : ∀ α ∈ Q, IsRoot F4.tag α ∧ 0 < height α)
    (hcl : ∀ α ∈ Q, ∀ β ∈ Q, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot F4.tag (m • α + n • β) →
      m • α + n • β ∈ Q)
    {L : List (Fin F4.tag.rank → ℤ)} (hnd : L.Nodup)
    (hL : ∀ α ∈ L, IsRoot F4.tag α ∧ 0 < height α) (hQL : ∀ α ∈ Q, α ∈ L)
    (c : (Fin F4.tag.rank → ℤ) → K)
    (hmem : (L.map fun α => pinnedX F4.tag K α (c α)).prod ∈ rootSpan F4.tag K Q) :
    ∀ α ∈ L, α ∉ Q → c α = 0 := by
  classical
  set L' := L.filter fun α => decide (α ∈ Q) with hL'
  have hnd' : L'.Nodup := hnd.filter _
  have hset : {x | x ∈ L'} = Q := by
    ext x
    simp only [Set.mem_ofPred_eq, hL', List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hQL x h, h⟩⟩
  obtain ⟨-, hex, -⟩ := list_prod_pinnedX_bijective (K := K) hQ hcl hnd' hset
  obtain ⟨d, hd⟩ := hex _ hmem
  let d' : (Fin F4.tag.rank → ℤ) → K := fun α => if α ∈ Q then d α else 0
  have hd1 : ∀ α ∈ Q, d' α = d α := fun α hα => by simp [d', hα]
  have hd0 : ∀ α ∉ Q, d' α = 0 := fun α hα => by simp [d', hα]
  have hfilt : ∀ L₀ : List (Fin F4.tag.rank → ℤ),
      (L₀.map fun α => pinnedX F4.tag K α (d' α)).prod =
        ((L₀.filter fun α => decide (α ∈ Q)).map fun α => pinnedX F4.tag K α (d α)).prod := by
    intro L₀
    induction L₀ with
    | nil => simp only [List.map_nil, List.filter_nil]
    | cons β L₀ ih =>
      by_cases hβ : β ∈ Q
      · rw [List.filter_cons_of_pos (by simpa using hβ), List.map_cons, List.map_cons,
          List.prod_cons, List.prod_cons, ih, hd1 β hβ]
      · rw [List.filter_cons_of_neg (by simpa using hβ), List.map_cons, List.prod_cons, ih,
          hd0 β hβ, pinnedX_zero, one_mul]
  have heq : (L.map fun α => pinnedX F4.tag K α (c α)).prod =
      (L.map fun α => pinnedX F4.tag K α (d' α)).prod := by
    rw [hfilt, hd]
  intro α hα hαQ
  have h := pinnedX_list_prod_injective L hnd hL c d' heq α hα
  rwa [hd0 α hαQ] at h


theorem sylowWord_roots :
    (sylowWord.map fun f => orbitCertRoot F4.tag f.1).Nodup ∧
      (∀ f ∈ sylowWord, IsRoot F4.tag (orbitCertRoot F4.tag f.1) ∧
        0 < height (orbitCertRoot F4.tag f.1)) ∧
      ∀ α, IsRoot F4.tag α → 0 < height α → α ∈ sylowWord.map fun f => orbitCertRoot F4.tag f.1
    := by
  have hpos := (f4_even_positive_root_commutator_table.{0}).1
  have hb : ∀ f ∈ sylowWord, 24 ≤ f.1 ∧ f.1 ≤ 47 := by decide
  have hb' : ∀ i ∈ sylowWord.map Prod.fst, 24 ≤ i ∧ i ≤ 47 := by decide
  have hc : ∀ i < 48, 24 ≤ i → ∃ f ∈ sylowWord, f.1 = i := by decide
  have hnd : (sylowWord.map fun f => orbitCertRoot F4.tag f.1).Nodup := by
    have e : (sylowWord.map fun f => orbitCertRoot F4.tag f.1) =
        (sylowWord.map Prod.fst).map (orbitCertRoot F4.tag) := by
      rw [List.map_map]
      rfl
    rw [e]
    exact (show (sylowWord.map Prod.fst).Nodup by decide).map_on
      fun i hi j hj h => f4_orbitCertRoot_inj' (hb' i hi) (hb' j hj) h
  refine ⟨hnd, fun f hf => (hpos _).2 ⟨f.1, (hb f hf).1, (hb f hf).2, rfl⟩,
    fun α hα hαp => ?_⟩
  obtain ⟨i, hi1, hi2, rfl⟩ := (hpos α).1 ⟨hα, hαp⟩
  obtain ⟨f, hf, rfl⟩ := hc i (by omega) hi1
  exact List.mem_map_of_mem hf

variable [Finite K] [CharP K F4.prime]

theorem coe_rootSpan_levelSet_inf (hK : Nat.card K = 2 ^ (2 * a + 1))
    {ℓ : Fin F4.tag.rank → ℤ} (hℓ : ∀ k, 0 ≤ ℓ k) (t : ℤ) (Z : Finset (Fin 12))
    (h1 : ∀ f ∈ sylowWord, t ≤ level ℓ (orbitCertRoot F4.tag f.1) ∨ polyVanishes Z f.2 = true)
    (h2 : ∀ f ∈ sylowWord, ∀ n ∈ Z, f.2 = [[(n : ℕ)]] → level ℓ (orbitCertRoot F4.tag f.1) < t) :
    ((rootSpan F4.tag K (levelSet ℓ t) ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
        Set (ModGL F4.tag K)) =
      sylowVec a K '' {x | ∀ n ∈ Z, x n = 0} := by
  obtain ⟨hnd, hpos, hcov⟩ := sylowWord_roots
  have hQ : ∀ α ∈ levelSet ℓ t, IsRoot F4.tag α ∧ 0 < height α := fun α h => ⟨h.1, h.2.1⟩
  have hlead : ∀ n : Fin 12, ∃ f ∈ sylowWord, f.2 = [[(n : ℕ)]] := by decide
  ext u
  constructor
  · rintro ⟨huS, huΓ⟩
    have huP : u ∈ F4.reeFixedPosUnipotent K a := ⟨rootSpan_le_posUnipotent hQ huS, huΓ⟩
    obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 huP
    refine ⟨x, fun n hn => ?_, rfl⟩
    set y := coordVal a (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11)
    set l := sylowWord.map fun f => (orbitCertRoot F4.tag f.1, polyEval y f.2) with hl
    have hlnd : (l.map Prod.fst).Nodup := by
      rw [hl, List.map_map]
      exact hnd
    have hw : sylowVec a K x = ((l.map Prod.fst).map fun α =>
        pinnedX F4.tag K α (rootParam l α)).prod := by
      rw [← rootProd_eq_map_rootParam hlnd, sylowVec, sylowV_eq_wordEval, wordEval, rootProd, hl,
        List.map_map]
      rfl
    rw [hw] at huS
    have hvan := eq_zero_of_list_prod_mem_rootSpan (K := K) hQ (levelSet_closed hℓ t) hlnd
      (fun α hα => by
        rw [hl, List.map_map] at hα
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hα
        exact hpos f hf)
      (fun α hα => by
        rw [hl, List.map_map]
        exact hcov α hα.1 hα.2.1) _ huS
    obtain ⟨f, hf, hfn⟩ := hlead n
    have hmem : (orbitCertRoot F4.tag f.1, polyEval y f.2) ∈ l :=
      List.mem_map.2 ⟨f, hf, rfl⟩
    have h0 := hvan _ (List.mem_map_of_mem (f := Prod.fst) hmem)
      (fun hQ' => absurd hQ'.2.2 (not_le.2 (h2 f hf n hn hfn)))
    rw [rootParam_of_mem hlnd hmem, hfn] at h0
    have hy : polyEval y [[(n : ℕ)]] = x n := by
      simp only [polyEval, monoEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, List.sum_cons, List.sum_nil, add_zero, y]
      exact coordVal_coe x n
    rw [← hy]
    exact h0
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, (Subgroup.mem_inf.1 ((bijOn_sylowVec hK).1 (Set.mem_univ x))).2⟩
    rw [sylowVec, sylowV_eq_wordEval, wordEval]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    rcases h1 f hf with hlev | hvan
    · exact pinnedX_mem_rootSpan (S := levelSet ℓ t) ⟨(hpos f hf).1, (hpos f hf).2, hlev⟩ _
    · rw [polyEval_eq_zero_of_polyVanishes hvan hx, pinnedX_zero]
      exact one_mem _

theorem rootJoin_levelSet (hK : Nat.card K = 2 ^ (2 * a + 1)) {I : Finset Idx}
    {ℓ : Fin F4.tag.rank → ℤ} (hℓ : ∀ k, 0 ≤ ℓ k) {t : ℤ} {Z : Finset (Fin 12)}
    (h1 : ∀ f ∈ sylowWord, t ≤ level ℓ (orbitCertRoot F4.tag f.1) ∨ polyVanishes Z f.2 = true)
    (h2 : ∀ f ∈ sylowWord, ∀ n ∈ Z, f.2 = [[(n : ℕ)]] → level ℓ (orbitCertRoot F4.tag f.1) < t)
    (hI : ∀ i ∈ I, ∀ n ∈ Z, n ∉ i.coords) (hI' : ∀ i : Idx, i.coord ∉ Z → i ∈ I ∨ i.base ∈ I) :
    rootJoin K a I = rootSpan F4.tag K (levelSet ℓ t) ⊓ F4.reeGamma K a ∧
      (rootJoin K a I : Set (ModGL F4.tag K)) = sylowVec a K '' {x | ∀ n ∈ Z, x n = 0} ∧
      Nat.card (rootJoin K a I) = (2 ^ (2 * a + 1)) ^ (12 - Z.card) ∧
      F4.reeFixedPosUnipotent K a ≤
        Subgroup.normalizer (rootJoin K a I : Set (ModGL F4.tag K)) := by
  have hH := coe_rootSpan_levelSet_inf hK hℓ t Z h1 h2
  have heq := rootJoin_eq_of_coe hK hH hI hI'
  refine ⟨heq, by rw [heq, hH], ?_, ?_⟩
  · rw [← card_image_sylowVec hK Z, ← hH, heq]
    rfl
  · rw [heq]
    intro u hu
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
      ⟨posUnipotent_le_normalizer_of_absorbs (fun α hα => ⟨hα.1, hα.2.1⟩)
        (levelSet_absorbs hℓ t) (Subgroup.mem_inf.1 hu).1,
        Subgroup.le_normalizer (Subgroup.mem_inf.1 hu).2⟩)

theorem radR_spec (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    radR K a = rootSpan F4.tag K (levelSet ![1, 0, 0, 1] 1) ⊓ F4.reeGamma K a ∧
      (radR K a : Set (ModGL F4.tag K)) =
        sylowVec a K '' {x | ∀ n ∈ ({1, 2} : Finset (Fin 12)), x n = 0} ∧
      Nat.card (radR K a) = (2 ^ (2 * a + 1)) ^ 10 ∧
      F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) :=
  rootJoin_levelSet hK (fun k => by fin_cases k <;> decide) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem radS_spec (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    radS K a = rootSpan F4.tag K (levelSet ![0, 1, 1, 0] 1) ⊓ F4.reeGamma K a ∧
      (radS K a : Set (ModGL F4.tag K)) =
        sylowVec a K '' {x | ∀ n ∈ ({0} : Finset (Fin 12)), x n = 0} ∧
      Nat.card (radS K a) = (2 ^ (2 * a + 1)) ^ 11 ∧
      F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) :=
  rootJoin_levelSet hK (fun k => by fin_cases k <;> decide) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem R1_spec (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    R1 K a = rootSpan F4.tag K (levelSet ![10, 0, 0, 7] 15) ⊓ F4.reeGamma K a ∧
      (R1 K a : Set (ModGL F4.tag K)) =
        sylowVec a K '' {x | ∀ n ∈ ({0, 1, 2, 3, 5, 7, 9} : Finset (Fin 12)), x n = 0} ∧
      Nat.card (R1 K a) = (2 ^ (2 * a + 1)) ^ 5 ∧
      F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (R1 K a : Set (ModGL F4.tag K)) :=
  rootJoin_levelSet hK (fun k => by fin_cases k <;> decide) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem S1_spec (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S1 K a = rootSpan F4.tag K (levelSet ![0, 10, 7, 0] 41) ⊓ F4.reeGamma K a ∧
      (S1 K a : Set (ModGL F4.tag K)) =
        sylowVec a K '' {x | ∀ n ∈ ({0, 1, 2, 3, 4, 5, 7, 9, 10, 11} : Finset (Fin 12)), x n = 0} ∧
      Nat.card (S1 K a) = (2 ^ (2 * a + 1)) ^ 2 ∧
      F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (S1 K a : Set (ModGL F4.tag K)) :=
  rootJoin_levelSet hK (fun k => by fin_cases k <;> decide) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem S2_spec (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S2 K a = rootSpan F4.tag K (levelSet ![0, 10, 7, 0] 34) ⊓ F4.reeGamma K a ∧
      (S2 K a : Set (ModGL F4.tag K)) =
        sylowVec a K '' {x | ∀ n ∈ ({0, 1, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 12)), x n = 0} ∧
      Nat.card (S2 K a) = (2 ^ (2 * a + 1)) ^ 3 ∧
      F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (S2 K a : Set (ModGL F4.tag K)) :=
  rootJoin_levelSet hK (fun k => by fin_cases k <;> decide) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem S3_spec (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S3 K a = rootSpan F4.tag K (levelSet ![0, 10, 7, 0] 24) ⊓ F4.reeGamma K a ∧
      (S3 K a : Set (ModGL F4.tag K)) =
        sylowVec a K '' {x | ∀ n ∈ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 12)), x n = 0} ∧
      Nat.card (S3 K a) = (2 ^ (2 * a + 1)) ^ 5 ∧
      F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (S3 K a : Set (ModGL F4.tag K)) :=
  rootJoin_levelSet hK (fun k => by fin_cases k <;> decide) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem S4_spec (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S4 K a = rootSpan F4.tag K (levelSet ![0, 10, 7, 0] 17) ⊓ F4.reeGamma K a ∧
      (S4 K a : Set (ModGL F4.tag K)) =
        sylowVec a K '' {x | ∀ n ∈ ({0, 1, 3} : Finset (Fin 12)), x n = 0} ∧
      Nat.card (S4 K a) = (2 ^ (2 * a + 1)) ^ 9 ∧
      F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (S4 K a : Set (ModGL F4.tag K)) :=
  rootJoin_levelSet hK (fun k => by fin_cases k <;> decide) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

omit [Finite K] [CharP K F4.prime] in
theorem fixedOrbitComplementRoots_eq_levelSet :
    F4.fixedOrbitComplementRoots ⟨1, by decide⟩ = levelSet ![1, 0, 0, 1] 1 ∧
      F4.fixedOrbitComplementRoots ⟨0, by decide⟩ = levelSet ![0, 1, 1, 0] 1 := by
  have hpos := (f4_even_positive_root_commutator_table.{0}).1
  have key : ∀ (j : Fin F4.fixedOrbitCount) (ℓ : Fin F4.tag.rank → ℤ),
      (∀ i < 48, 24 ≤ i → ((∃ k, F4.fixedOrbitIndex k ≠ j ∧ orbitCertRoot F4.tag i k ≠ 0) ↔
        1 ≤ level ℓ (orbitCertRoot F4.tag i))) →
      F4.fixedOrbitComplementRoots j = levelSet ℓ 1 := by
    intro j ℓ h
    ext α
    rw [mem_fixedOrbitComplementRoots_iff]
    constructor
    · rintro ⟨hα, hαp, hk⟩
      obtain ⟨i, hi1, hi2, rfl⟩ := (hpos α).1 ⟨hα, hαp⟩
      exact ⟨hα, hαp, (h i (by omega) hi1).1 hk⟩
    · rintro ⟨hα, hαp, hl⟩
      obtain ⟨i, hi1, hi2, rfl⟩ := (hpos α).1 ⟨hα, hαp⟩
      exact ⟨hα, hαp, (h i (by omega) hi1).2 hl⟩
  exact ⟨key _ _ (by decide +kernel), key _ _ (by decide +kernel)⟩

theorem radR_eq_complement (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    radR K a = F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  rw [(radR_spec hK).1, ReeTag.reeFixedOrbitComplementUnipotent,
    fixedOrbitComplementRoots_eq_levelSet.1]

theorem radS_eq_complement (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    radS K a = F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  rw [(radS_spec hK).1, ReeTag.reeFixedOrbitComplementUnipotent,
    fixedOrbitComplementRoots_eq_levelSet.2]

theorem S4_eq_tKernel (hK : Nat.card K = 2 ^ (2 * a + 1)) : S4 K a = tKernel K a := by
  refine SetLike.coe_injective ?_
  rw [(S4_spec hK).2.1, coe_tKernel hK]
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Set.mem_ofPred_eq]

end Level

end CFSG.LocalAnalysis.EvenBN.TwoF4
