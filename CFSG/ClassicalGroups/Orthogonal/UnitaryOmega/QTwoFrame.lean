module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlockDefs
public import CFSG.LieType.Universal.SpinOmega.FrameGeneration
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankSiegel
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

section Vectors

variable (F) in
@[expose] def normPlaneVec {m : ℕ} (k : Fin m) (x : K) : (F × F) × (Fin m → K) :=
  (0, Pi.single k x)

variable (K) in
@[expose] def normWVec (m : ℕ) : Bool → (F × F) × (Fin m → K)
  | true => ((1, 0), 0)
  | false => ((0, 1), 0)

@[expose] def IsTraceNormOne (ω : K) : Prop :=
  polar (normQuad E) 1 ω = 1 ∧ normQuad E ω = 1

private theorem eq_zero_or_eq_one [Finite F] (hF : Nat.card F = 2) (a : F) :
    a = 0 ∨ a = 1 := by
  classical
  by_contra h
  rw [not_or] at h
  obtain ⟨ha0, ha1⟩ := h
  have h0a : (0 : F) ≠ a := fun h => ha0 h.symm
  have h1a : (1 : F) ≠ a := fun h => ha1 h.symm
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have hinj : Function.Injective ![(0 : F), (1 : F), a] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hle : Nat.card (Fin 3) ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
  rw [hF] at hle
  norm_num at hle

theorem exists_isTraceNormOne (hF : Nat.card F = 2) : ∃ ω, IsTraceNormOne E ω := by
  classical
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have hcardK : Nat.card K = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), E.finrank_eq, hF]
    norm_num
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω ∉ Set.range (algebraMap F K) := by
    by_contra h
    rw [not_exists] at h
    let : Fintype K := Fintype.ofFinite K
    let : Fintype F := Fintype.ofFinite F
    have hsurj : Function.Surjective (algebraMap F K) := fun x => by simpa using h x
    have himg : (Finset.univ : Finset F).image (algebraMap F K) = Finset.univ := by
      ext x
      simp [hsurj x]
    have hle : Fintype.card K ≤ Fintype.card F := by
      have h := Finset.card_image_le (s := (Finset.univ : Finset F)) (f := algebraMap F K)
      simpa only [himg, Finset.card_univ] using h
    have hcK : Fintype.card K = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcardK
    have hcF : Fintype.card F = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hF
    omega
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  refine ⟨ω, ?_, ?_⟩
  · rcases eq_zero_or_eq_one hF (polar (normQuad E) 1 ω) with h0 | h1
    · exfalso
      apply hω
      have h := algebraMap_polar_normQuad E 1 ω
      rw [h0, map_zero, map_one, mul_one, one_mul] at h
      have hfix : unitaryInvolution K 2 f ω = ω := CharTwo.add_eq_zero.mp h.symm
      exact E.exists_of_fix ω hfix
    · exact h1
  · rcases eq_zero_or_eq_one hF (normQuad E ω) with h0 | h1
    · exfalso
      apply hω
      have h := algebraMap_normQuad E ω
      rw [h0, map_zero] at h
      have hω0 : ω = 0 := by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact h'
        · have h2 := congrArg (unitaryInvolution K 2 f) h'
          rw [map_zero, E.isUnitary.invol] at h2
          exact h2
      subst hω0
      exact ⟨0, by rw [map_zero]⟩
    · exact h1

variable (F) in
@[expose] noncomputable def qTwoVec (ω : K) (i : Fin 5) : Bool → (F × F) × (Fin 4 → K)
  | true => ![normPlaneVec F 0 1 + normPlaneVec F 1 1,
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω, normWVec K 4 true,
      normPlaneVec F 3 1 + normPlaneVec F 2 1, normPlaneVec F 3 (1 + ω) + normPlaneVec F 2 ω] i
  | false => ![normPlaneVec F 0 ω + normPlaneVec F 1 1,
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω), normWVec K 4 false,
      normPlaneVec F 3 ω + normPlaneVec F 2 1,
      normPlaneVec F 3 (1 + ω) + normPlaneVec F 2 (1 + ω)] i

variable (F) in
@[expose] noncomputable def qTwoVecTwo (ω : K) (i : Fin 3) : Bool → (F × F) × (Fin 2 → K)
  | true => ![normPlaneVec F 0 1 + normPlaneVec F 1 1,
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω, normWVec K 2 true] i
  | false => ![normPlaneVec F 0 ω + normPlaneVec F 1 1,
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω), normWVec K 2 false] i

variable (F) in
@[expose] noncomputable def qTwoVecTwoW (ω : K) (i : Fin 3) : Bool → (F × F) × (Fin 2 → K)
  | true => ![normWVec K 2 true, normPlaneVec F 0 1 + normPlaneVec F 1 1,
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω] i
  | false => ![normWVec K 2 false, normPlaneVec F 0 ω + normPlaneVec F 1 1,
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω)] i

end Vectors

section Helpers

variable [CharP F 2]

omit [CharP F 2] in
private theorem normHypForm_planeVec {m : ℕ} (k : Fin m) (x : K) :
    normHypForm E m (normPlaneVec F k x) = normQuad E x := by
  rw [normHypForm, hypSum_apply, Qn_apply]
  change 0 * 0 + (∑ i, normQuad E ((Pi.single k x : Fin m → K) i)) = normQuad E x
  rw [zero_mul, zero_add, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, QuadraticMap.map_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

omit [CharP F 2] in
private theorem polar_normHypForm_planeVec_planeVec {m : ℕ} (k l : Fin m) (x y : K) :
    polar (normHypForm E m) (normPlaneVec F k x) (normPlaneVec F l y) =
      if k = l then polar (normQuad E) x y else 0 := by
  rw [normHypForm, polar_hypSum, polar_Qn]
  change 0 * 0 + 0 * 0 + (∑ i, polar (normQuad E) ((Pi.single k x : Fin m → K) i)
    ((Pi.single l y : Fin m → K) i)) = if k = l then polar (normQuad E) x y else 0
  simp only [zero_mul, zero_add]
  by_cases h : k = l
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, QuadraticMap.polar_zero_left]
    · intro h'
      exact absurd (Finset.mem_univ k) h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases eq_or_ne j l with rfl | hj
    · rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm h), QuadraticMap.polar_zero_left]
    · rw [Pi.single_eq_of_ne hj, QuadraticMap.polar_zero_right]

omit [CharP F 2] in
private theorem normHypForm_wVec {m : ℕ} (s : Bool) :
    normHypForm E m (normWVec K m s) = 0 := by
  cases s <;> simp [normWVec, normHypForm, hypSum_apply, Qn_apply]

omit [CharP F 2] in
private theorem polar_normHypForm_wVec_planeVec {m : ℕ} (s : Bool) (k : Fin m) (x : K) :
    polar (normHypForm E m) (normWVec K m s) (normPlaneVec F k x) = 0 := by
  rw [normHypForm, polar_hypSum]
  cases s <;> simp [normWVec, normPlaneVec]

omit [CharP F 2] in
private theorem polar_normHypForm_planeVec_wVec {m : ℕ} (k : Fin m) (x : K) (s : Bool) :
    polar (normHypForm E m) (normPlaneVec F k x) (normWVec K m s) = 0 := by
  rw [polar_comm]
  exact polar_normHypForm_wVec_planeVec E s k x

omit [CharP F 2] in
private theorem polar_normHypForm_wVec_wVec {m : ℕ} (s t : Bool) :
    polar (normHypForm E m) (normWVec K m s) (normWVec K m t) =
      if s = !t then 1 else 0 := by
  rw [normHypForm, polar_hypSum]
  cases s <;> cases t <;> simp [normWVec]

private theorem polar_normQuad_self (x : K) : polar (normQuad E) x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

private theorem normQuad_one_add {ω : K} (hω : IsTraceNormOne E ω) :
    normQuad E (1 + ω) = 1 := by
  rw [QuadraticMap.map_add (normQuad E), normQuad_one, hω.2, hω.1,
    CharTwo.add_self_eq_zero, zero_add]

private theorem polar_normQuad_one_add {ω : K} (hω : IsTraceNormOne E ω) :
    polar (normQuad E) 1 (1 + ω) = 1 := by
  rw [polar_add_right, hω.1, polar_normQuad_self, zero_add]

private theorem polar_normQuad_omega_add {ω : K} (hω : IsTraceNormOne E ω) :
    polar (normQuad E) ω (1 + ω) = 1 := by
  rw [polar_add_right, polar_normQuad_self, add_zero, polar_comm, hω.1]

omit [CharP F 2] in
private theorem polar_normQuad_omega_one {ω : K} (hω : IsTraceNormOne E ω) :
    polar (normQuad E) ω 1 = 1 := by
  rw [polar_comm, hω.1]

omit [Finite K] [CharP K 2] [CharP F 2] in
private theorem mem_sup_coordPlane {m : ℕ} (i : Fin m) (x : K) :
    normPlaneVec F i x ∈
      Finset.univ.sup (coordPlane (LinearEquiv.refl F ((F × F) × (Fin m → K)))) :=
  Finset.le_sup (f := fun i => coordPlane (LinearEquiv.refl F ((F × F) × (Fin m → K))) i)
    (Finset.mem_univ i) (mem_coordPlane.mpr ⟨x, rfl⟩)

omit [Finite K] [CharP K 2] [CharP F 2] in
private theorem mem_coordSupport_singleton {m : ℕ} (k : Fin m) (x : K) :
    normPlaneVec F k x ∈
      coordSupport (LinearEquiv.refl F ((F × F) × (Fin m → K))) {k} := by
  rw [coordSupport, Submodule.mem_sup]
  refine ⟨0, Submodule.zero_mem _, normPlaneVec F k x, ?_, zero_add _⟩
  exact Finset.le_sup (f := fun i =>
    coordPlane (LinearEquiv.refl F ((F × F) × (Fin m → K))) i)
    (Finset.mem_singleton_self k) (mem_coordPlane.mpr ⟨x, rfl⟩)

omit [Finite K] [CharP K 2] [CharP F 2] in
private theorem normWVec_mem_coordSupport {m : ℕ} (s : Bool) (S : Finset (Fin m)) :
    normWVec K m s ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin m → K))) S := by
  rw [coordSupport]
  cases s
  · exact Submodule.mem_sup_left (mem_coordAnchor.mpr ⟨(0, 1), rfl⟩)
  · exact Submodule.mem_sup_left (mem_coordAnchor.mpr ⟨(1, 0), rfl⟩)

theorem exists_aux_of_fields {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {Q : QuadraticForm L V} {n : ℕ} (hn : 3 ≤ n) (vec : Fin n → Bool → V)
    (hQ : ∀ i s, Q (vec i s) = 0)
    (hne : ∀ ⦃i j : Fin n⦄, i ≠ j → ∀ s t, polar Q (vec i s) (vec j t) = 0)
    (hnot : ∀ i s, polar Q (vec i s) (vec i (!s)) = 1) :
    ∀ i j : Fin n, ∃ a : V, IsUnit (Q a) ∧
      ∀ s, polar Q (vec i s) a = 0 ∧ polar Q (vec j s) a = 0 := by
  intro i j
  obtain ⟨k, hki, hkj⟩ := exists_ne_and_ne hn i j
  refine ⟨vec k true + vec k false, ?_, fun s => ⟨?_, ?_⟩⟩
  · have hQa : Q (vec k true + vec k false) = 1 := by
      have hnt : polar Q (vec k true) (vec k false) = 1 := by simpa using hnot k true
      rw [QuadraticMap.map_add Q, hQ k true, hQ k false, hnt, zero_add, zero_add]
    rw [hQa]
    exact isUnit_one
  · rw [polar_add_right, hne (Ne.symm hki) s true, hne (Ne.symm hki) s false, add_zero]
  · rw [polar_add_right, hne (Ne.symm hkj) s true, hne (Ne.symm hkj) s false, add_zero]

end Helpers

section Frames

variable {E} {ω : K}

theorem qTwoFrame_map_vec (hω : IsTraceNormOne E ω) (i : Fin 5) (s : Bool) :
    normHypForm E 4 (qTwoVec F ω i s) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i
  · cases s
    · change normHypForm E 4 (normPlaneVec F 0 ω + normPlaneVec F 1 1) = 0
      rw [QuadraticMap.map_add (normHypForm E 4)]
      simp [normHypForm_planeVec, hω.2, normQuad_one, polar_normHypForm_planeVec_planeVec,
        CharTwo.add_self_eq_zero]
    · change normHypForm E 4 (normPlaneVec F 0 1 + normPlaneVec F 1 1) = 0
      rw [QuadraticMap.map_add (normHypForm E 4)]
      simp [normHypForm_planeVec, normQuad_one, polar_normHypForm_planeVec_planeVec,
        CharTwo.add_self_eq_zero]
  · cases s
    · change normHypForm E 4
        (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω)) = 0
      rw [QuadraticMap.map_add (normHypForm E 4)]
      simp [normHypForm_planeVec, normQuad_one_add E hω, 
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
    · change normHypForm E 4 (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω) = 0
      rw [QuadraticMap.map_add (normHypForm E 4)]
      simp [normHypForm_planeVec, normQuad_one_add E hω, hω.2,
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
  · cases s
    · change normHypForm E 4 (normWVec K 4 false) = 0
      exact normHypForm_wVec E false
    · change normHypForm E 4 (normWVec K 4 true) = 0
      exact normHypForm_wVec E true
  · cases s
    · change normHypForm E 4 (normPlaneVec F 3 ω + normPlaneVec F 2 1) = 0
      rw [QuadraticMap.map_add (normHypForm E 4)]
      simp [normHypForm_planeVec, hω.2, normQuad_one, polar_normHypForm_planeVec_planeVec,
        CharTwo.add_self_eq_zero]
    · change normHypForm E 4 (normPlaneVec F 3 1 + normPlaneVec F 2 1) = 0
      rw [QuadraticMap.map_add (normHypForm E 4)]
      simp [normHypForm_planeVec, normQuad_one, polar_normHypForm_planeVec_planeVec,
        CharTwo.add_self_eq_zero]
  · cases s
    · change normHypForm E 4
        (normPlaneVec F 3 (1 + ω) + normPlaneVec F 2 (1 + ω)) = 0
      rw [QuadraticMap.map_add (normHypForm E 4)]
      simp [normHypForm_planeVec, normQuad_one_add E hω, 
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
    · change normHypForm E 4 (normPlaneVec F 3 (1 + ω) + normPlaneVec F 2 ω) = 0
      rw [QuadraticMap.map_add (normHypForm E 4)]
      simp [normHypForm_planeVec, normQuad_one_add E hω, hω.2,
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]

theorem qTwoFrame_polar_vec_of_ne (hω : IsTraceNormOne E ω)
    {i j : Fin 5} (hij : i ≠ j) (s t : Bool) :
    polar (normHypForm E 4) (qTwoVec F ω i s) (qTwoVec F ω j t) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp_all [qTwoVec, normQuad_one,
      hω.1, hω.2, polar_normHypForm_planeVec_planeVec,
      polar_normHypForm_planeVec_wVec, polar_normHypForm_wVec_planeVec,
      
      polar_normQuad_one_add E hω, polar_normQuad_omega_add E hω,
      polar_normQuad_omega_one E hω, polar_add_left, polar_add_right, 
      CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]

theorem qTwoFrame_polar_vec_not (hω : IsTraceNormOne E ω) (i : Fin 5) (s : Bool) :
    polar (normHypForm E 4) (qTwoVec F ω i s) (qTwoVec F ω i (!s)) = 1 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i <;> cases s <;>
    simp [qTwoVec, hω.1, hω.2,
      polar_normHypForm_planeVec_planeVec, polar_normHypForm_wVec_wVec,
      polar_normQuad_omega_add E hω,
      polar_normQuad_omega_one E hω, polar_add_left, polar_add_right, 
      CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]

@[expose] noncomputable def qTwoFrame (hω : IsTraceNormOne E ω) : HypFrame (normHypForm E 4) 5 where
  vec := qTwoVec F ω
  map_vec := qTwoFrame_map_vec hω
  polar_vec_of_ne := fun i j hij s t => qTwoFrame_polar_vec_of_ne hω hij s t
  polar_vec_not := qTwoFrame_polar_vec_not hω
  exists_aux := by
    have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
    exact exists_aux_of_fields (Q := normHypForm E 4) (n := 5) (by norm_num) (qTwoVec F ω)
      (qTwoFrame_map_vec hω)
      (fun i j hij => qTwoFrame_polar_vec_of_ne hω hij)
      (qTwoFrame_polar_vec_not hω)

theorem qTwoFrameTwo_map_vec (hω : IsTraceNormOne E ω) (i : Fin 3) (s : Bool) :
    normHypForm E 2 (qTwoVecTwo F ω i s) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i
  · cases s
    · change normHypForm E 2 (normPlaneVec F 0 ω + normPlaneVec F 1 1) = 0
      rw [QuadraticMap.map_add (normHypForm E 2)]
      simp [normHypForm_planeVec, hω.2, normQuad_one,
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
    · change normHypForm E 2 (normPlaneVec F 0 1 + normPlaneVec F 1 1) = 0
      rw [QuadraticMap.map_add (normHypForm E 2)]
      simp [normHypForm_planeVec, normQuad_one,
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
  · cases s
    · change normHypForm E 2 (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω)) = 0
      rw [QuadraticMap.map_add (normHypForm E 2)]
      simp [normHypForm_planeVec, normQuad_one_add E hω, 
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
    · change normHypForm E 2 (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω) = 0
      rw [QuadraticMap.map_add (normHypForm E 2)]
      simp [normHypForm_planeVec, normQuad_one_add E hω, hω.2, 
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
  · cases s
    · change normHypForm E 2 (normWVec K 2 false) = 0
      exact normHypForm_wVec E false
    · change normHypForm E 2 (normWVec K 2 true) = 0
      exact normHypForm_wVec E true
theorem qTwoFrameTwo_polar_vec_of_ne (hω : IsTraceNormOne E ω)
    {i j : Fin 3} (hij : i ≠ j) (s t : Bool) :
    polar (normHypForm E 2) (qTwoVecTwo F ω i s) (qTwoVecTwo F ω j t) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp_all [qTwoVecTwo, normQuad_one,
      hω.1, hω.2, polar_normHypForm_planeVec_planeVec,
      polar_normHypForm_planeVec_wVec, polar_normHypForm_wVec_planeVec,
      polar_normQuad_one_add E hω,
      polar_normQuad_omega_add E hω, polar_normQuad_omega_one E hω, polar_add_left,
      polar_add_right, CharTwo.add_self_eq_zero,
      CharTwo.two_eq_zero]

theorem qTwoFrameTwo_polar_vec_not (hω : IsTraceNormOne E ω) (i : Fin 3) (s : Bool) :
    polar (normHypForm E 2) (qTwoVecTwo F ω i s) (qTwoVecTwo F ω i (!s)) = 1 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i <;> cases s <;>
    simp [qTwoVecTwo, hω.1, hω.2,
      polar_normHypForm_planeVec_planeVec, polar_normHypForm_wVec_wVec,
      polar_normQuad_omega_add E hω,
      polar_normQuad_omega_one E hω, polar_add_left, polar_add_right, 
      CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]

theorem qTwoFrameTwoW_map_vec (hω : IsTraceNormOne E ω) (i : Fin 3) (s : Bool) :
    normHypForm E 2 (qTwoVecTwoW F ω i s) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i
  · cases s
    · change normHypForm E 2 (normWVec K 2 false) = 0
      exact normHypForm_wVec E false
    · change normHypForm E 2 (normWVec K 2 true) = 0
      exact normHypForm_wVec E true
  · cases s
    · change normHypForm E 2 (normPlaneVec F 0 ω + normPlaneVec F 1 1) = 0
      rw [QuadraticMap.map_add (normHypForm E 2)]
      simp [normHypForm_planeVec, hω.2, normQuad_one,
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
    · change normHypForm E 2 (normPlaneVec F 0 1 + normPlaneVec F 1 1) = 0
      rw [QuadraticMap.map_add (normHypForm E 2)]
      simp [normHypForm_planeVec, normQuad_one,
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
  · cases s
    · change normHypForm E 2 (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω)) = 0
      rw [QuadraticMap.map_add (normHypForm E 2)]
      simp [normHypForm_planeVec, normQuad_one_add E hω, 
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
    · change normHypForm E 2 (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω) = 0
      rw [QuadraticMap.map_add (normHypForm E 2)]
      simp [normHypForm_planeVec, normQuad_one_add E hω, hω.2, 
        polar_normHypForm_planeVec_planeVec, CharTwo.add_self_eq_zero,
        ]
theorem qTwoFrameTwoW_polar_vec_of_ne (hω : IsTraceNormOne E ω)
    {i j : Fin 3} (hij : i ≠ j) (s t : Bool) :
    polar (normHypForm E 2) (qTwoVecTwoW F ω i s) (qTwoVecTwoW F ω j t) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp_all [qTwoVecTwoW, normQuad_one,
      hω.1, hω.2, polar_normHypForm_planeVec_planeVec,
      polar_normHypForm_planeVec_wVec, polar_normHypForm_wVec_planeVec,
      polar_normQuad_one_add E hω,
      polar_normQuad_omega_add E hω, polar_normQuad_omega_one E hω, polar_add_left,
      polar_add_right, CharTwo.add_self_eq_zero,
      CharTwo.two_eq_zero]

theorem qTwoFrameTwoW_polar_vec_not (hω : IsTraceNormOne E ω) (i : Fin 3) (s : Bool) :
    polar (normHypForm E 2) (qTwoVecTwoW F ω i s) (qTwoVecTwoW F ω i (!s)) = 1 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  fin_cases i <;> cases s <;>
    simp [qTwoVecTwoW, hω.1, hω.2,
      polar_normHypForm_planeVec_planeVec, polar_normHypForm_wVec_wVec,
      polar_normQuad_omega_add E hω,
      polar_normQuad_omega_one E hω, polar_add_left, polar_add_right, 
      CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]

@[expose] noncomputable def qTwoFrameTwo (hω : IsTraceNormOne E ω) :
    HypFrame (normHypForm E 2) 3 where
  vec := qTwoVecTwo F ω
  map_vec := qTwoFrameTwo_map_vec hω
  polar_vec_of_ne := fun i j hij s t => qTwoFrameTwo_polar_vec_of_ne hω hij s t
  polar_vec_not := qTwoFrameTwo_polar_vec_not hω
  exists_aux := by
    exact exists_aux_of_fields (Q := normHypForm E 2) (n := 3) (by norm_num) (qTwoVecTwo F ω)
      (qTwoFrameTwo_map_vec hω)
      (fun i j hij => qTwoFrameTwo_polar_vec_of_ne hω hij)
      (qTwoFrameTwo_polar_vec_not hω)

@[expose] noncomputable def qTwoFrameTwoW (hω : IsTraceNormOne E ω) :
    HypFrame (normHypForm E 2) 3 where
  vec := qTwoVecTwoW F ω
  map_vec := qTwoFrameTwoW_map_vec hω
  polar_vec_of_ne := fun i j hij s t => qTwoFrameTwoW_polar_vec_of_ne hω hij s t
  polar_vec_not := qTwoFrameTwoW_polar_vec_not hω
  exists_aux := by
    exact exists_aux_of_fields (Q := normHypForm E 2) (n := 3) (by norm_num) (qTwoVecTwoW F ω)
      (qTwoFrameTwoW_map_vec hω)
      (fun i j hij => qTwoFrameTwoW_polar_vec_of_ne hω hij)
      (qTwoFrameTwoW_polar_vec_not hω)

end Frames

section Spin

variable {ω : K}

@[expose] noncomputable def qTwoLambda (hω : IsTraceNormOne E ω) :
    normOmega E 4 ≃* spinGroup (quadPlus 5 F) :=
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  commutatorEquivSpinPlusOfIsometry
    ((qTwoFrame hω).isometryQuadPlus (finrank_normHypForm E 4)) (by norm_num)
    CharTwo.two_eq_zero

@[expose] noncomputable def qTwoLambdaTwo (hω : IsTraceNormOne E ω) :
    normOmega E 2 ≃* spinGroup (quadPlus 3 F) :=
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  commutatorEquivSpinPlusOfIsometry
    ((qTwoFrameTwo hω).isometryQuadPlus (finrank_normHypForm E 2)) le_rfl
    CharTwo.two_eq_zero

@[expose] noncomputable def qTwoLambdaTwoW (hω : IsTraceNormOne E ω) :
    normOmega E 2 ≃* spinGroup (quadPlus 3 F) :=
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  commutatorEquivSpinPlusOfIsometry
    ((qTwoFrameTwoW hω).isometryQuadPlus (finrank_normHypForm E 2)) le_rfl
    CharTwo.two_eq_zero

end Spin

section Elements

@[expose] noncomputable def qTwoW0Lin : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)) :=
  eichler (normHypForm E 4) (normWVec K 4 true) (normPlaneVec F 2 1) *
    eichler (normHypForm E 4) (normWVec K 4 false) (normPlaneVec F 2 1) *
    eichler (normHypForm E 4) (normWVec K 4 true) (normPlaneVec F 2 1)

theorem qTwoW0Lin_mem {ω : K} (hω : IsTraceNormOne E ω) : qTwoW0Lin E ∈ normOmega E 4 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have hQa : normHypForm E 4 (normPlaneVec F 2 1) ≠ 0 := by
    rw [normHypForm_planeVec, normQuad_one]
    exact one_ne_zero
  have hwa : polar (normHypForm E 4) (normPlaneVec F 2 1) (normPlaneVec F 2 ω) =
      normHypForm E 4 (normPlaneVec F 2 1) := by
    rw [polar_normHypForm_planeVec_planeVec, if_pos rfl, normHypForm_planeVec, normQuad_one]
    exact hω.1
  have heaT : polar (normHypForm E 4) (normWVec K 4 true) (normPlaneVec F 2 1) = 0 :=
    polar_normHypForm_wVec_planeVec E true 2 1
  have hewT : polar (normHypForm E 4) (normWVec K 4 true) (normPlaneVec F 2 ω) = 0 :=
    polar_normHypForm_wVec_planeVec E true 2 ω
  have heaF : polar (normHypForm E 4) (normWVec K 4 false) (normPlaneVec F 2 1) = 0 :=
    polar_normHypForm_wVec_planeVec E false 2 1
  have hewF : polar (normHypForm E 4) (normWVec K 4 false) (normPlaneVec F 2 ω) = 0 :=
    polar_normHypForm_wVec_planeVec E false 2 ω
  have hmemT : eichler (normHypForm E 4) (normWVec K 4 true) (normPlaneVec F 2 1) ∈
      normOmega E 4 :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.eichler_mem_orthDerived (Q := normHypForm E 4)
      (e := normWVec K 4 true) (a := normPlaneVec F 2 1) (w := normPlaneVec F 2 ω)
      hQa heaT hewT hwa
  have hmemF : eichler (normHypForm E 4) (normWVec K 4 false) (normPlaneVec F 2 1) ∈
      normOmega E 4 :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.eichler_mem_orthDerived (Q := normHypForm E 4)
      (e := normWVec K 4 false) (a := normPlaneVec F 2 1) (w := normPlaneVec F 2 ω)
      hQa heaF hewF hwa
  rw [qTwoW0Lin]
  exact mul_mem (mul_mem hmemT hmemF) hmemT

@[expose] noncomputable def qTwoW0 {ω : K} (hω : IsTraceNormOne E ω) : normOmega E 4 :=
  ⟨qTwoW0Lin E, qTwoW0Lin_mem E hω⟩

theorem qTwoW0Lin_wVec (s : Bool) : qTwoW0Lin E (normWVec K 4 s) = normWVec K 4 (!s) := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have hQe : normHypForm E 4 (normWVec K 4 true) = 0 := normHypForm_wVec E true
  have hQf : normHypForm E 4 (normWVec K 4 false) = 0 := normHypForm_wVec E false
  have heaT : polar (normHypForm E 4) (normWVec K 4 true) (normPlaneVec F 2 1) = 0 :=
    polar_normHypForm_wVec_planeVec E true 2 1
  have heaF : polar (normHypForm E 4) (normWVec K 4 false) (normPlaneVec F 2 1) = 0 :=
    polar_normHypForm_wVec_planeVec E false 2 1
  have hQa : normHypForm E 4 (normPlaneVec F 2 1) = 1 := by
    rw [normHypForm_planeVec, normQuad_one]
  cases s
  · rw [qTwoW0Lin]
    simp only [LinearEquiv.mul_apply]
    simp only [eichler_apply hQe heaT, eichler_apply hQf heaF]
    simp [hQa, polar_normHypForm_wVec_wVec, polar_normHypForm_wVec_planeVec,
      polar_normHypForm_planeVec_wVec, 
      polar_add_left, 
      sub_eq_add_neg, CharTwo.neg_eq,
      CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_ <;>
      simp [normWVec, normPlaneVec, CharTwo.add_self_eq_zero, CharTwo.neg_eq]
    · funext j
      fin_cases j <;> simp [normWVec, normPlaneVec, CharTwo.add_self_eq_zero, CharTwo.neg_eq]
  · rw [qTwoW0Lin]
    simp only [LinearEquiv.mul_apply]
    simp only [eichler_apply hQe heaT, eichler_apply hQf heaF]
    simp [hQa, polar_normHypForm_wVec_wVec, polar_normHypForm_wVec_planeVec,
      polar_normHypForm_planeVec_wVec, 
      polar_add_left, 
      sub_eq_add_neg, CharTwo.neg_eq,
      CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_ <;>
      simp [normWVec, normPlaneVec, CharTwo.add_self_eq_zero, CharTwo.neg_eq]
    · funext j
      fin_cases j <;> simp [normWVec, normPlaneVec, CharTwo.add_self_eq_zero, CharTwo.neg_eq]

theorem qTwoW0Lin_planeVec {k : Fin 4} (hk : k ≠ 2) (x : K) :
    qTwoW0Lin E (normPlaneVec F k x) = normPlaneVec F k x := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have h1 : polar (normHypForm E 4) (normPlaneVec F k x) (normWVec K 4 true) = 0 :=
    polar_normHypForm_planeVec_wVec E k x true
  have h2 : polar (normHypForm E 4) (normPlaneVec F k x) (normPlaneVec F 2 1) = 0 := by
    rw [polar_normHypForm_planeVec_planeVec, if_neg hk]
  have h3 : polar (normHypForm E 4) (normPlaneVec F k x) (normWVec K 4 false) = 0 :=
    polar_normHypForm_planeVec_wVec E k x false
  rw [qTwoW0Lin]
  simp only [LinearEquiv.mul_apply]
  simp only [
    eichler_apply_of_polar_eq_zero (Q := normHypForm E 4) h3 h2,
    eichler_apply_of_polar_eq_zero (Q := normHypForm E 4) h1 h2]

theorem qTwoW0_mem_normBlock {ω : K} (hω : IsTraceNormOne E ω) :
    qTwoW0 E hω ∈ normBlock E 4 {2} := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let W : Submodule F ((F × F) × (Fin 4 → K)) :=
    coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) {2}
  have hQa : normHypForm E 4 (normPlaneVec F 2 1) ≠ 0 := by
    rw [normHypForm_planeVec, normQuad_one]
    exact one_ne_zero
  have hwa : polar (normHypForm E 4) (normPlaneVec F 2 1) (normPlaneVec F 2 ω) =
      normHypForm E 4 (normPlaneVec F 2 1) := by
    rw [polar_normHypForm_planeVec_planeVec, if_pos rfl, normHypForm_planeVec, normQuad_one]
    exact hω.1
  have hw1 : normPlaneVec F 2 1 ∈ W := mem_coordSupport_singleton (m := 4) (2 : Fin 4) 1
  have hwω : normPlaneVec F 2 ω ∈ W := mem_coordSupport_singleton (m := 4) (2 : Fin 4) ω
  have he : ∀ s : Bool, normWVec K 4 s ∈ W := fun s =>
    normWVec_mem_coordSupport (m := 4) s {2}
  have hfactor : ∀ s : Bool,
      eichler (normHypForm E 4) (normWVec K 4 s) (normPlaneVec F 2 1) ∈
        supportedDerived (normHypForm E 4) W := by
    intro s
    refine eichler_mem_supportedDerived (Q := normHypForm E 4) (W := W)
      (e := normWVec K 4 s) (w := normPlaneVec F 2 1) (he s) hw1
      (normHypForm_wVec E s) (polar_normHypForm_wVec_planeVec E s 2 1) ?_
    have hQa' : ((normHypForm E 4).comp W.subtype) ⟨normPlaneVec F 2 1, hw1⟩ ≠ 0 := by
      simpa using hQa
    have hea' : polar ((normHypForm E 4).comp W.subtype)
        ⟨normWVec K 4 s, he s⟩ ⟨normPlaneVec F 2 1, hw1⟩ = 0 := by
      rw [polar_comp_subtype_eq]
      exact polar_normHypForm_wVec_planeVec E s 2 1
    have hew' : polar ((normHypForm E 4).comp W.subtype)
        ⟨normWVec K 4 s, he s⟩ ⟨normPlaneVec F 2 ω, hwω⟩ = 0 := by
      rw [polar_comp_subtype_eq]
      exact polar_normHypForm_wVec_planeVec E s 2 ω
    have hwa' : polar ((normHypForm E 4).comp W.subtype)
        ⟨normPlaneVec F 2 1, hw1⟩ ⟨normPlaneVec F 2 ω, hwω⟩ =
        ((normHypForm E 4).comp W.subtype) ⟨normPlaneVec F 2 1, hw1⟩ := by
      rw [polar_comp_subtype_eq]
      exact hwa
    exact CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.eichler_mem_orthDerived hQa' hea' hew' hwa'
  rw [qTwoW0, normBlock]
  exact Subgroup.mem_subgroupOf.mpr
    (mul_mem (mul_mem (hfactor true) (hfactor false)) (hfactor true))

@[expose] noncomputable def qTwoYLin (ω : K) :
    ((F × F) × (Fin 3 → K)) ≃ₗ[F] ((F × F) × (Fin 3 → K)) :=
  eichler (normHypForm E 3) (normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1)
    (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω)

private theorem qTwoY_Qe {ω : K} (hω : IsTraceNormOne E ω) :
    normHypForm E 3 (normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  rw [QuadraticMap.map_add (normHypForm E 3), normHypForm_planeVec,
    normHypForm_planeVec, normQuad_one_add E hω, normQuad_one,
    polar_normHypForm_planeVec_planeVec, if_neg (by decide : (0 : Fin 3) ≠ 2)]
  rw [CharTwo.add_self_eq_zero (1 : F), zero_add]

private theorem qTwoY_Qa {ω : K} (hω : IsTraceNormOne E ω) :
    normHypForm E 3 (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω) = 1 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  rw [QuadraticMap.map_add (normHypForm E 3), QuadraticMap.map_add (normHypForm E 3)]
  simp [normHypForm_planeVec, hω.2, normQuad_one, polar_normHypForm_planeVec_planeVec,
    reduceIte, CharTwo.add_self_eq_zero]

private theorem qTwoY_polar_ea {ω : K} (hω : IsTraceNormOne E ω) :
    polar (normHypForm E 3)
      (normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1)
      (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  simp [polar_add_left, polar_add_right, polar_normHypForm_planeVec_planeVec,
    
    hω.1, hω.2, reduceIte,
    CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]

private theorem qTwoY_polar_ew {ω : K} (_hω : IsTraceNormOne E ω) :
    polar (normHypForm E 3)
      (normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1)
      (normPlaneVec F 1 ω) = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  simp [polar_add_left, polar_normHypForm_planeVec_planeVec,
    reduceIte]

private theorem qTwoY_polar_aw {ω : K} (hω : IsTraceNormOne E ω) :
    polar (normHypForm E 3)
      (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω)
      (normPlaneVec F 1 ω) = 1 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  simp [polar_add_left, polar_normHypForm_planeVec_planeVec,
    hω.1, reduceIte]

theorem qTwoYLin_mem {ω : K} (hω : IsTraceNormOne E ω) : qTwoYLin E ω ∈ normOmega E 3 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have hQa : normHypForm E 3
      (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω) ≠ 0 := by
    rw [qTwoY_Qa E hω]
    exact one_ne_zero
  have hwa : polar (normHypForm E 3)
      (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω)
      (normPlaneVec F 1 ω) =
      normHypForm E 3 (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω) := by
    rw [qTwoY_polar_aw E hω, qTwoY_Qa E hω]
  have hmem := CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.eichler_mem_orthDerived
    (Q := normHypForm E 3)
    (e := normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1)
    (a := normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω)
    (w := normPlaneVec F 1 ω) hQa (qTwoY_polar_ea E hω) (qTwoY_polar_ew E hω) hwa
  rw [qTwoYLin]
  exact hmem

theorem qTwoYLin_wVec (ω : K) (s : Bool) : qTwoYLin E ω (normWVec K 3 s) = normWVec K 3 s := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  rw [qTwoYLin]
  refine eichler_apply_of_polar_eq_zero (Q := normHypForm E 3) ?_ ?_
  · simp [polar_add_right, polar_normHypForm_wVec_planeVec]
  · simp [polar_add_right, polar_normHypForm_wVec_planeVec]

theorem qTwoYLin_planeVec_two {ω : K} (hω : IsTraceNormOne E ω) :
    qTwoYLin E ω (normPlaneVec F 2 1) = normPlaneVec F 0 (1 + ω) := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have hQe : normHypForm E 3
      (normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1) = 0 := qTwoY_Qe E hω
  have hxe : polar (normHypForm E 3) (normPlaneVec F 2 1)
      (normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1) = 0 := by
    rw [polar_add_right, polar_normHypForm_planeVec_planeVec,
      polar_normHypForm_planeVec_planeVec, if_neg (by decide : (2 : Fin 3) ≠ 0),
      if_pos rfl, polar_normQuad_self]
    simp
  have hxa : polar (normHypForm E 3) (normPlaneVec F 2 1)
      (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω) = 1 := by
    rw [polar_add_right, polar_add_right, polar_normHypForm_planeVec_planeVec,
      polar_normHypForm_planeVec_planeVec, polar_normHypForm_planeVec_planeVec,
      if_neg (by decide : (2 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 1),
      if_pos rfl, hω.1]
    simp
  rw [qTwoYLin, eichler_apply hQe (qTwoY_polar_ea E hω), hxe, hxa, qTwoY_Qa E hω]
  simp only [zero_smul, mul_zero, add_zero, one_smul, sub_eq_add_neg]
  refine Prod.ext ?_ ?_
  · refine Prod.ext ?_ ?_ <;>
      simp [normPlaneVec, CharTwo.neg_eq, add_comm]
  · funext j
    fin_cases j <;>
      simp [normPlaneVec, CharTwo.add_self_eq_zero, CharTwo.neg_eq, add_comm]

@[expose] noncomputable def qTwoY {ω : K} (hω : IsTraceNormOne E ω) : normOmega E 3 :=
  ⟨qTwoYLin E ω, qTwoYLin_mem E hω⟩

theorem qTwoY_mem_normPureBlock {ω : K} (hω : IsTraceNormOne E ω) :
    qTwoY E hω ∈ normPureBlock E 3 Finset.univ := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let W : Submodule F ((F × F) × (Fin 3 → K)) :=
    Finset.univ.sup (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 3 → K))))
  have he0 : normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1 ∈ W :=
    Submodule.add_mem _ (mem_sup_coordPlane (m := 3) 0 (1 + ω))
      (mem_sup_coordPlane (m := 3) 2 1)
  have ha : normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω ∈ W :=
    Submodule.add_mem _
      (Submodule.add_mem _ (mem_sup_coordPlane (m := 3) 0 ω)
        (mem_sup_coordPlane (m := 3) 1 1))
      (mem_sup_coordPlane (m := 3) 2 ω)
  have hw : normPlaneVec F 1 ω ∈ W := mem_sup_coordPlane (m := 3) 1 ω
  have hQa : normHypForm E 3
      (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω) ≠ 0 := by
    rw [qTwoY_Qa E hω]
    exact one_ne_zero
  have hwa : polar (normHypForm E 3)
      (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω)
      (normPlaneVec F 1 ω) =
      normHypForm E 3 (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω) := by
    rw [qTwoY_polar_aw E hω, qTwoY_Qa E hω]
  have hmem : eichler (normHypForm E 3)
      (normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1)
      (normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω) ∈
      supportedDerived (normHypForm E 3) W := by
    refine eichler_mem_supportedDerived (Q := normHypForm E 3) (W := W)
      (e := normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1)
      (w := normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω)
      he0 ha (qTwoY_Qe E hω) (qTwoY_polar_ea E hω) ?_
    have hQa' : ((normHypForm E 3).comp W.subtype)
        ⟨normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω, ha⟩ ≠ 0 := by
      simpa using hQa
    have hea' : polar ((normHypForm E 3).comp W.subtype)
        ⟨normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1, he0⟩
        ⟨normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω, ha⟩ = 0 := by
      rw [polar_comp_subtype_eq]
      exact qTwoY_polar_ea E hω
    have hew' : polar ((normHypForm E 3).comp W.subtype)
        ⟨normPlaneVec F 0 (1 + ω) + normPlaneVec F 2 1, he0⟩
        ⟨normPlaneVec F 1 ω, hw⟩ = 0 := by
      rw [polar_comp_subtype_eq]
      exact qTwoY_polar_ew E hω
    have hwa' : polar ((normHypForm E 3).comp W.subtype)
        ⟨normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω, ha⟩
        ⟨normPlaneVec F 1 ω, hw⟩ =
        ((normHypForm E 3).comp W.subtype)
          ⟨normPlaneVec F 0 ω + normPlaneVec F 1 1 + normPlaneVec F 2 ω, ha⟩ := by
      rw [polar_comp_subtype_eq]
      exact hwa
    exact CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.eichler_mem_orthDerived hQa' hea' hew' hwa'
  rw [qTwoY, normPureBlock]
  exact Subgroup.mem_subgroupOf.mpr hmem

end Elements

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
