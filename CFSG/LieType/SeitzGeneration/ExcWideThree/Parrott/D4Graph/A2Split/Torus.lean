module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.Orbit
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Tup

variable {K : Type} [Field K]

@[expose] def tupAct (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)
    (a : Fin Tag.D4.rank → Kˣ) : Fin Tag.D4.rank → Kˣ :=
  fun j => ∏ k, a k ^ M j k

theorem tupAct_tupAct (M N : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)
    (a : Fin Tag.D4.rank → Kˣ) : tupAct M (tupAct N a) = tupAct (M * N) a := by
  funext j
  simp only [tupAct, Matrix.mul_apply]
  rw [show ∏ k, (∏ l, a l ^ N k l) ^ M j k = ∏ k, ∏ l, a l ^ (M j k * N k l) by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← zpow_mul, mul_comm]]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Finset.prod_zpow_eq_zpow_sum]

theorem tupAct_mul (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)
    (a b : Fin Tag.D4.rank → Kˣ) : tupAct M (a * b) = tupAct M a * tupAct M b := by
  funext j
  simp only [tupAct, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem tupAct_inv (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)
    (a : Fin Tag.D4.rank → Kˣ) : tupAct M a⁻¹ = (tupAct M a)⁻¹ := by
  funext j
  simp only [tupAct, Pi.inv_apply, inv_zpow', zpow_neg, Finset.prod_inv_distrib]

theorem tupAct_one (a : Fin Tag.D4.rank → Kˣ) : tupAct 1 a = a := by
  funext j
  simp only [tupAct, Matrix.one_apply]
  rw [Finset.prod_eq_single j (fun k _ hkj => by rw [if_neg (Ne.symm hkj), zpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), if_pos rfl, zpow_one]

theorem tupAct_zpow (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ) (ω : Kˣ)
    (v : Fin Tag.D4.rank → ℤ) :
    tupAct M (fun k => ω ^ v k) = fun j => ω ^ (M.mulVec v j) := by
  funext j
  simp only [tupAct, Matrix.mulVec, dotProduct]
  rw [← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

theorem zpow_eq_of_three {ω : Kˣ} (hω : ω ^ 3 = 1) {m n : ℤ} (h : m % 3 = n % 3) :
    ω ^ m = ω ^ n := by
  have hm : m = m % 3 + 3 * (m / 3) := by have := Int.mul_ediv_add_emod m 3; omega
  have hn : n = n % 3 + 3 * (n / 3) := by have := Int.mul_ediv_add_emod n 3; omega
  have h3 : ω ^ (3 : ℤ) = 1 := by exact_mod_cast hω
  rw [hm, hn, zpow_add, zpow_add, zpow_mul, zpow_mul, h3, one_zpow, one_zpow, h]

theorem zpow_tuple_eq_of_three {ω : Kˣ} (hω : ω ^ 3 = 1) {v w : Fin Tag.D4.rank → ℤ}
    (h : ∀ j, v j % 3 = w j % 3) : (fun j => ω ^ v j) = fun j => ω ^ w j :=
  funext fun j => zpow_eq_of_three hω (h j)

@[expose] def reflM (i : Fin Tag.D4.rank) : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  Matrix.of fun j k => (if j = k then 1 else 0) - (if k = i then Tag.D4.cartan i j else 0)

theorem tupAct_reflM (i : Fin Tag.D4.rank) (a : Fin Tag.D4.rank → Kˣ) :
    tupAct (reflM i) a = fun j => a j * a i ^ (-Tag.D4.cartan i j) := by
  funext j
  simp only [tupAct, reflM, Matrix.of_apply, zpow_sub, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  have h1 : ∏ k, a k ^ (if j = k then (1 : ℤ) else 0) = a j := by
    rw [Finset.prod_eq_single j (fun k _ hkj => by rw [if_neg (Ne.symm hkj), zpow_zero])
      (fun h => absurd (Finset.mem_univ j) h), if_pos rfl, zpow_one]
  have h2 : ∏ k, a k ^ (if k = i then Tag.D4.cartan i j else 0) = a i ^ Tag.D4.cartan i j := by
    rw [Finset.prod_eq_single i (fun k _ hki => by rw [if_neg hki, zpow_zero])
      (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  rw [h1, h2, zpow_neg]

@[expose] def rhoP : Equiv.Perm (Fin Tag.D4.rank) := TwistTag.D4.perm

@[expose] def permM : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  Matrix.of fun j k => if k = rhoP.symm j then 1 else 0

theorem tupAct_permM (a : Fin Tag.D4.rank → Kˣ) :
    tupAct permM a = fun j => a (rhoP.symm j) := by
  funext j
  simp only [tupAct, permM, Matrix.of_apply]
  rw [Finset.prod_eq_single (rhoP.symm j)
    (fun k _ hk => by rw [if_neg hk, zpow_zero]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl, zpow_one]

end Tup

section D4


variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

theorem weylElt_conj_rootDiagUnit_tupAct (i : Fin Tag.D4.rank) (a : Fin Tag.D4.rank → Kˣ) :
    weylElt Tag.D4 K i 1 * rootDiagUnit Tag.D4 a * (weylElt Tag.D4 K i 1)⁻¹ =
      rootDiagUnit Tag.D4 (tupAct (reflM i) a) := by
  rw [weylElt_conj_rootDiagUnit, tupAct_reflM]

theorem diagramMap_conj_rootDiagUnit_tupAct (a : Fin Tag.D4.rank → Kˣ) :
    d4P K * rootDiagUnit Tag.D4 a * (d4P K)⁻¹ = rootDiagUnit Tag.D4 (tupAct permM a) := by
  rw [tupAct_permM]
  have h : d4P K * rootDiagUnit Tag.D4 a =
      rootDiagUnit Tag.D4 (fun j => a (rhoP.symm j)) * d4P K :=
    diagramMap_mul_rootDiagUnit (K := K) (t := TwistTag.D4) a
  rw [h, mul_inv_cancel_right]

theorem coe_weylElement_one (i : Fin Tag.D4.rank) :
    ((CFSG.LieType.Steinberg.weylElement 𝕩 i (1 : Kˣ) : ↥(adjointGroup Tag.D4 K)) :
      ModGL Tag.D4 K) = weylElt Tag.D4 K i 1 := by
  rw [weylElement_xPar]
  show torusElt Tag.D4 K i 1 * weylElt Tag.D4 K i 1 = _
  rw [torusElt_one, one_mul]

@[expose] def weylG2M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  reflM ⟨2, by decide⟩ * (reflM ⟨0, by decide⟩ * reflM ⟨1, by decide⟩ * reflM ⟨3, by decide⟩)

theorem weylG2_conj_rootDiagUnit (a : Fin Tag.D4.rank → Kˣ) :
    ((weylG2 : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a *
        ((weylG2 : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁻¹ =
      rootDiagUnit Tag.D4 (tupAct weylG2M a) := by
  unfold weylG2
  simp only [Subgroup.coe_mul, coe_weylElement_one]
  set n2 := weylElt Tag.D4 K ⟨2, by decide⟩ 1
  set n0 := weylElt Tag.D4 K ⟨0, by decide⟩ 1
  set n1 := weylElt Tag.D4 K ⟨1, by decide⟩ 1
  set n3 := weylElt Tag.D4 K ⟨3, by decide⟩ 1
  have e : n2 * (n0 * n1 * n3) * rootDiagUnit Tag.D4 a * (n2 * (n0 * n1 * n3))⁻¹ =
      n2 * (n0 * (n1 * (n3 * rootDiagUnit Tag.D4 a * n3⁻¹) * n1⁻¹) * n0⁻¹) * n2⁻¹ := by group
  rw [e, weylElt_conj_rootDiagUnit_tupAct, weylElt_conj_rootDiagUnit_tupAct,
    weylElt_conj_rootDiagUnit_tupAct, weylElt_conj_rootDiagUnit_tupAct, tupAct_tupAct,
    tupAct_tupAct, tupAct_tupAct]
  simp only [weylG2M, Matrix.mul_assoc]

theorem weylG2_pow_conj_rootDiagUnit (n : ℕ) (a : Fin Tag.D4.rank → Kˣ) :
    (((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) *
        rootDiagUnit Tag.D4 a *
        (((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ n : ↥(adjointGroup Tag.D4 K)) :
          ModGL Tag.D4 K)⁻¹ =
      rootDiagUnit Tag.D4 (tupAct (weylG2M ^ n) a) := by
  induction n generalizing a with
  | zero =>
    simp only [pow_zero, Subgroup.coe_one, one_mul, inv_one, mul_one]
    rw [tupAct_one]
  | succ n ih =>
    rw [pow_succ', Subgroup.coe_mul, mul_inv_rev,
      show ((weylG2 : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) *
          ((weylG2 ^ n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a *
          (((weylG2 ^ n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁻¹ *
            ((weylG2 : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁻¹) =
        ((weylG2 : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) *
          (((weylG2 ^ n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a *
            ((weylG2 ^ n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁻¹) *
          ((weylG2 : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁻¹ by group,
      ih, weylG2_conj_rootDiagUnit, tupAct_tupAct, pow_succ']

@[expose] def wG2r (β : Fin Tag.D4.rank → ℤ) : Fin Tag.D4.rank → ℤ :=
  reflect Tag.D4 ⟨2, by decide⟩ (reflect Tag.D4 ⟨0, by decide⟩
    (reflect Tag.D4 ⟨1, by decide⟩ (reflect Tag.D4 ⟨3, by decide⟩ β)))

theorem isRoot_wG2r {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot Tag.D4 β) : IsRoot Tag.D4 (wG2r β) :=
  (((hβ.reflect _).reflect _).reflect _).reflect _

theorem exists_weylG2_pow_conj (n : ℕ) {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot Tag.D4 β) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ u : K,
      (weylG2 : ↥(adjointGroup Tag.D4 K)) ^ n * 𝕩 β u *
          ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ n)⁻¹ =
        𝕩 (wG2r^[n] β) (ε * u) := by
  induction n with
  | zero => exact ⟨1, by ring, fun u => by simp⟩
  | succ n ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hβn : IsRoot Tag.D4 (wG2r^[n] β) := by
      clear h hε ε
      induction n with
      | zero => exact hβ
      | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact isRoot_wG2r ihm
    obtain ⟨ε', hε', h'⟩ := exists_weylG2_conj (K := K) hβn
    refine ⟨ε' * ε, ?_, fun u => ?_⟩
    · calc ε' * ε * (ε' * ε) = (ε' * ε') * (ε * ε) := by ring
        _ = 1 := by rw [hε, hε', one_mul]
    · rw [pow_succ', mul_inv_rev,
        show (weylG2 : ↥(adjointGroup Tag.D4 K)) * weylG2 ^ n * 𝕩 β u *
            ((weylG2 ^ n)⁻¹ * (weylG2 : ↥(adjointGroup Tag.D4 K))⁻¹) =
          weylG2 * (weylG2 ^ n * 𝕩 β u * (weylG2 ^ n)⁻¹) * weylG2⁻¹ by group, h, h',
        Function.iterate_succ_apply', mul_assoc]
      rfl

theorem wG2r_iterate_six : ∀ l ∈ Tag.D4.artifactRoots,
    wG2r^[6] (fun i : Fin Tag.D4.rank => l.getD (i : ℕ) 0) =
      fun i : Fin Tag.D4.rank => l.getD (i : ℕ) 0 := by
  decide

theorem wG2r_iterate_six_of_isRoot {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot Tag.D4 β) :
    wG2r^[6] β = β := by
  have h := wG2r_iterate_six _ (isRoot_iff_mem_artifactRoots.1 hβ)
  have e : (fun i : Fin Tag.D4.rank => (List.ofFn β).getD (i : ℕ) 0) = β := by
    funext i
    simp [List.getD_eq_getElem?_getD]
  rwa [e] at h

theorem weylG2_pow_twelve [Finite K] : (weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 12 = 1 := by
  have hcomm : ∀ β : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 β → ∀ u : K,
      (weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 12 * 𝕩 β u *
          ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 12)⁻¹ =
        𝕩 β u := by
    intro β hβ u
    obtain ⟨ε, hε, h⟩ := exists_weylG2_pow_conj (K := K) 6 hβ
    rw [wG2r_iterate_six_of_isRoot hβ] at h
    rw [show (12 : ℕ) = 6 + 6 from rfl, pow_add, mul_inv_rev,
      show (weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 6 * weylG2 ^ 6 * 𝕩 β u *
          ((weylG2 ^ 6)⁻¹ * ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 6)⁻¹) =
        weylG2 ^ 6 * (weylG2 ^ 6 * 𝕩 β u * (weylG2 ^ 6)⁻¹) * (weylG2 ^ 6)⁻¹ by group, h, h,
      ← mul_assoc, hε, one_mul]
  set z := (weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 12
  have htop : Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.D4 K)) = ⊤ := by
    refine eq_top_of_simple_mem fun i c => ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hcomm _ (isRoot_single Tag.D4 i) c
      calc 𝕩 (Pi.single i 1) c * z = z * 𝕩 (Pi.single i 1) c * z⁻¹ * z := by rw [h]
        _ = z * 𝕩 (Pi.single i 1) c := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hcomm _ (isRoot_neg_single Tag.D4 i) c
      calc 𝕩 (-Pi.single i 1) c * z = z * 𝕩 (-Pi.single i 1) c * z⁻¹ * z := by rw [h]
        _ = z * 𝕩 (-Pi.single i 1) c := by group
  have hz : z ∈ Subgroup.center ↥(adjointGroup Tag.D4 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.D4 K)) := htop ▸ trivial
    exact Subgroup.mem_centralizer_singleton_iff.1 hy
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  exact hz

theorem rootDiagUnit_injective_D4 {a b : Fin Tag.D4.rank → Kˣ}
    (h : rootDiagUnit Tag.D4 a = rootDiagUnit Tag.D4 b) : a = b := by
  funext i
  have hr := isRoot_single Tag.D4 i
  obtain ⟨s, hs, hxs⟩ := coe_xPar_eq_pinnedX_sign (K := K) hr
  have key : ∀ c : Kˣ, rootDiagUnit Tag.D4 (fun j => if j = i then c else 1) =
      rootDiagUnit Tag.D4 (fun j => if j = i then c else 1) := fun _ => rfl
  clear key
  have hA := rootDiagUnit_conj_pinnedX a hr (1 : K)
  have hB := rootDiagUnit_conj_pinnedX b hr (1 : K)
  rw [h] at hA
  rw [hA] at hB
  have hchar : ∀ c : Fin Tag.D4.rank → Kˣ, rootChar c (Pi.single i 1) = c i := by
    intro c
    have := rootChar_nsmul_single c i 1
    simpa using this
  rw [hchar, hchar, mul_one, mul_one] at hB
  have hpx : ∀ c : K, pinnedX Tag.D4 K (Pi.single i 1) c =
      ((𝕩 (Pi.single i 1) (s * c) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) := by
    intro c
    rw [hxs, ← mul_assoc, hs, one_mul]
  rw [hpx, hpx] at hB
  have h2 := xPar_injective hr (Subtype.ext hB)
  have hs0 : s ≠ 0 := fun h0 => by rw [h0, zero_mul] at hs; exact zero_ne_one hs
  exact Units.ext (mul_left_cancel₀ hs0 h2)

end D4

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
