module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Orthogonal
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryMaxBorel

public section

namespace CFSG.Quasithin.LieOver

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Pointwise

abbrev ljGL (n : ℕ) (K : Type) [Field K] : Type :=
  (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)

theorem lj_peel {r : ℕ} {K : Type} [Field K] (hr2 : 2 ≤ r) (hr : 3 ≤ r)
    {M : Subgroup (ljGL r K)} (hUM : unipotent r K ≤ M) :
    ∀ (ℓ : ℕ) (n : ljGL r K) (hn : n ∈ torusWeyl r K), n ∈ M →
      weylLength r ((torusWeylNu r K hr2 ⟨n, hn⟩ : weylGroup r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = ℓ →
      n ∈ Subgroup.closure ((borel r K : Set (ljGL r K)) ∪
        weylElt r K '' {i | weylElt r K i ∈ M}) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro n hn _ hℓ
    have h1 := eq_one_of_weylLength_eq_zero hr (torusWeylNu r K hr2 ⟨n, hn⟩).2 hℓ
    have hker : (⟨n, hn⟩ : torusWeyl r K) ∈ (torusWeylNu r K hr2).ker :=
      MonoidHom.mem_ker.2 (Subtype.ext h1)
    rw [torusWeylNu_ker hr2, Subgroup.mem_subgroupOf] at hker
    exact Subgroup.subset_closure (Or.inl (torus_le_borel hker))
  | succ ℓ ih =>
    intro n hn hnM hℓ
    set w := ((torusWeylNu r K hr2 ⟨n, hn⟩ : weylGroup r) :
      (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) with hw
    have hwW : w ∈ weylGroup r := (torusWeylNu r K hr2 ⟨n, hn⟩).2
    have hne : w ≠ 1 := by
      rintro h1
      rw [h1] at hℓ
      have : weylLength r (1 : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = 0 := by
        have hempty : inversionSet r (1 : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = ∅ := by
          ext β
          simp only [inversionSet, LinearEquiv.coe_one, id_eq, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro hβ hβ'
          exact (mem_posRoots_or_neg_mem_posRoots (posRoots_subset_roots hβ)).2 ⟨hβ, hβ'⟩
        rw [weylLength, hempty, Set.ncard_empty]
      omega
    obtain ⟨i, hi⟩ := exists_simpleRoot_neg hr hwW hne
    have hα := simpleRoot_mem_posRoots hr2 i
    have hXα : rootSubgroup r K (simpleRoot r i) ≤ M :=
      le_trans (rootSubgroup_le_unipotent hα) hUM
    have hXβ : rootSubgroup r K (-(w⁻¹ (simpleRoot r i))) ≤ M :=
      le_trans (rootSubgroup_le_unipotent hi) hUM
    have hmap := map_conj_rootSubgroup_torusWeyl hr2 ⟨n, hn⟩ (posRoots_subset_roots hi)
    have hww : w (w⁻¹ (simpleRoot r i)) = simpleRoot r i := by
      rw [LinearEquiv.coe_inv]
      exact LinearEquiv.apply_symm_apply _ _
    rw [← hw, map_neg, hww] at hmap
    have hXneg : rootSubgroup r K (-simpleRoot r i) ≤ M := by
      rw [← hmap]
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hnM (hXβ hy)) (inv_mem hnM)
    have hniM : weylElt r K i ∈ M :=
      mul_mem (mul_mem (hXα (rootElt_mem_rootSubgroup _ _))
        (hXneg (rootElt_mem_rootSubgroup _ _))) (hXα (rootElt_mem_rootSubgroup _ _))
    have hniH : weylElt r K i ∈ Subgroup.closure ((borel r K : Set (ljGL r K)) ∪
        weylElt r K '' {i | weylElt r K i ∈ M}) :=
      Subgroup.subset_closure (Or.inr ⟨i, hniM, rfl⟩)
    have hn' : (weylElt r K i)⁻¹ * n ∈ torusWeyl r K :=
      mul_mem (inv_mem (weylElt_mem_torusWeyl i)) hn
    have hν : ((torusWeylNu r K hr2 ⟨_, hn'⟩ : weylGroup r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = simpleRefl r i * w := by
      have he : (⟨(weylElt r K i)⁻¹ * n, hn'⟩ : torusWeyl r K) =
          (⟨weylElt r K i, weylElt_mem_torusWeyl i⟩ : torusWeyl r K)⁻¹ * ⟨n, hn⟩ := rfl
      rw [he, map_mul, map_inv, torusWeylNu_weylElt hr2 i, Subgroup.coe_mul,
        Subgroup.coe_inv]
      congr 1
      rw [inv_eq_iff_mul_eq_one, simpleRefl_mul_self hr2]
    have hlen := weylLength_simpleRefl_mul hr2 hwW hi
    rw [← hν, hℓ, Nat.add_sub_cancel] at hlen
    have hrec := ih _ hn' (mul_mem (inv_mem hniM) hnM) hlen
    have he : n = weylElt r K i * ((weylElt r K i)⁻¹ * n) := by group
    rw [he]
    exact mul_mem hniH hrec

theorem lj_le_closure {r : ℕ} {K : Type} [Field K] (hr : 3 ≤ r)
    {M : Subgroup (ljGL r K)} (hMG : M ≤ orthElementaryGroup (quadPlus r K))
    (hUM : unipotent r K ≤ M) :
    M ≤ Subgroup.closure ((borel r K : Set (ljGL r K)) ∪
      weylElt r K '' {i | weylElt r K i ∈ M}) := by
  have hr2 : 2 ≤ r := by omega
  intro g hg
  obtain ⟨b₁, h₁, n, hn, b₂, h₂, rfl⟩ :=
    (orthogonal_geometry_split_Bruhat_coverage hr g).1 (hMG hg)
  have hB := borel_eq_torus_mul_unipotent (r := r) (K := K)
  have h₁' : b₁ ∈ (unipotent r K : Set (ljGL r K)) * (torus r K : Set (ljGL r K)) := by
    rw [← hB.2]
    exact h₁
  have h₂' : b₂ ∈ (torus r K : Set (ljGL r K)) * (unipotent r K : Set (ljGL r K)) := by
    rw [← hB.1]
    exact h₂
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := h₁'
  obtain ⟨t₂, ht₂, u₂, hu₂, rfl⟩ := h₂'
  have hnT : t₁ * n * t₂ ∈ torusWeyl r K :=
    mul_mem (mul_mem (torus_le_torusWeyl ht₁) hn) (torus_le_torusWeyl ht₂)
  have hnM : t₁ * n * t₂ ∈ M := by
    have he : t₁ * n * t₂ = u₁⁻¹ * (u₁ * t₁ * n * (t₂ * u₂)) * u₂⁻¹ := by group
    rw [he]
    exact mul_mem (mul_mem (inv_mem (hUM hu₁)) hg) (inv_mem (hUM hu₂))
  have hkey := lj_peel hr2 hr hUM _ _ hnT hnM rfl
  have he2 : u₁ * t₁ * n * (t₂ * u₂) = u₁ * (t₁ * n * t₂) * u₂ := by group
  rw [he2]
  exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl (unipotent_le_borel hu₁))) hkey)
    (Subgroup.subset_closure (Or.inl (unipotent_le_borel hu₂)))

theorem lj_cut_stab {r : ℕ} {K : Type} [Field K] (hr : 3 ≤ r)
    {M : Subgroup (ljGL r K)} (hMG : M ≤ orthElementaryGroup (quadPlus r K))
    (hUM : unipotent r K ≤ M) {V : Submodule K (Fin r ⊕ Fin r → K)}
    (hbV : borel r K ≤ MulAction.stabilizer (ljGL r K) V)
    {i : Fin r} (hfix : ∀ j : Fin r, j ≠ i → weylElt r K j • V = V)
    (hi : weylElt r K i ∉ M) :
    M ≤ MulAction.stabilizer (ljGL r K) V := by
  refine le_trans (lj_le_closure hr hMG hUM) ?_
  rw [Subgroup.closure_le]
  rintro _ (hb | ⟨j, hj, rfl⟩)
  · exact hbV hb
  · refine MulAction.mem_stabilizer_iff.2 (hfix j ?_)
    rintro rfl
    exact hi hj

theorem lj_move_flag {n : ℕ} {K : Type} [Field K] (hr : 3 ≤ n) {m : ℕ} (hm1 : 1 ≤ m)
    (hm2 : m ≤ n - 2) (k : Fin n) (hk : k.val + 1 = m) :
    weylElt n K k • flag n K m ≠ flag n K m := by
  subst hk
  exact weylElt_smul_flag_ne hr hm2

theorem lj_fix_flag {n : ℕ} {K : Type} [Field K] (hr : 3 ≤ n) {m : ℕ} (hm1 : 1 ≤ m)
    (hm2 : m ≤ n - 2) (k : Fin n) (hk : k.val + 1 ≠ m) :
    weylElt n K k • flag n K m = flag n K m :=
  weylElt_smul_flag_of_ne hr hm1 hm2 hk

theorem lj_exists_move_flag {n : ℕ} {K : Type} [Field K] (hr : 3 ≤ n) {m : ℕ} (hm1 : 1 ≤ m)
    (hm2 : m ≤ n - 2) : ∃ k : Fin n, k.val + 1 = m ∧ weylElt n K k • flag n K m ≠ flag n K m :=
  ⟨⟨m - 1, by omega⟩, by show m - 1 + 1 = m; omega,
    lj_move_flag (K := K) hr hm1 hm2 _ (by show m - 1 + 1 = m; omega)⟩

theorem lj_top {n : ℕ} {K : Type} [Field K] (hr : 3 ≤ n) (k : Fin n)
    (hk : k.val + 1 ≤ n - 2) :
    weylElt n K k • flag n K n = flag n K n ∧
      weylElt n K k • Xstar n K (by omega) = Xstar n K (by omega) :=
  weylElt_smul_flag_top_and_Xstar hr hk

theorem lj_pen {n : ℕ} {K : Type} [Field K] (hr : 3 ≤ n) (k : Fin n) (hk : k.val = n - 2) :
    weylElt n K k • Xstar n K (by omega) ≠ Xstar n K (by omega) ∧
      weylElt n K k • flag n K n = flag n K n := by
  rw [show k = ⟨n - 2, by omega⟩ from Fin.ext hk]
  exact weylElt_penult_smul hr

theorem lj_last {n : ℕ} {K : Type} [Field K] (hr : 3 ≤ n) (k : Fin n) (hk : k.val = n - 1) :
    weylElt n K k • flag n K n ≠ flag n K n ∧
      weylElt n K k • Xstar n K (by omega) = Xstar n K (by omega) := by
  rw [show k = ⟨n - 1, by omega⟩ from Fin.ext hk]
  exact weylElt_last_smul hr

theorem lj_table {n : ℕ} {K : Type} [Field K] (hn : 4 ≤ n) (i : Fin n) :
    ∃ V ∈ pOmegaPlusSubspaces n K hn,
      borel n K ≤ MulAction.stabilizer (ljGL n K) V ∧
      (∀ j : Fin n, j ≠ i → weylElt n K j • V = V) ∧ weylElt n K i • V ≠ V := by
  have hr : 3 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hiL := i.isLt
  by_cases h1 : i.val + 1 ≤ n - 2
  · exact ⟨flag n K (i.val + 1), Or.inl ⟨i.val + 1, by omega, h1, rfl⟩,
      borel_le_stabilizer_flag (by omega) (by omega),
      fun j hj => lj_fix_flag (K := K) hr (by omega) h1 j (fun h => hj (Fin.ext (by omega))),
      lj_move_flag (K := K) hr (by omega) h1 i rfl⟩
  by_cases h2 : i.val = n - 2
  · refine ⟨Xstar n K hn0, Or.inr (Or.inr rfl), borel_le_stabilizer_Xstar _,
      fun j hj => ?_, (lj_pen (K := K) hr i h2).1⟩
    by_cases hj1 : j.val + 1 ≤ n - 2
    · exact (lj_top (K := K) hr j hj1).2
    · have hjv : j.val = n - 1 := by
        have hjL := j.isLt
        have : j.val ≠ i.val := fun h => hj (Fin.ext h)
        omega
      exact (lj_last (K := K) hr j hjv).2
  · have hiv : i.val = n - 1 := by omega
    refine ⟨flag n K n, Or.inr (Or.inl rfl), borel_le_stabilizer_flag (by omega) le_rfl,
      fun j hj => ?_, (lj_last (K := K) hr i hiv).1⟩
    by_cases hj1 : j.val + 1 ≤ n - 2
    · exact (lj_top (K := K) hr j hj1).1
    · have hjv : j.val = n - 2 := by
        have hjL := j.isLt
        have : j.val ≠ i.val := fun h => hj (Fin.ext h)
        omega
      exact (lj_pen (K := K) hr j hjv).2

theorem lj_moved {n : ℕ} {K : Type} [Field K] (hn : 4 ≤ n)
    {W : Submodule K (Fin n ⊕ Fin n → K)} (hW : W ∈ pOmegaPlusSubspaces n K hn) :
    ∃ k : Fin n, weylElt n K k • W ≠ W := by
  have hr : 3 ≤ n := by omega
  rcases hW with ⟨i, hi1, hi2, rfl⟩ | rfl | rfl
  · obtain ⟨k, -, hk⟩ := lj_exists_move_flag (K := K) hr hi1 hi2
    exact ⟨k, hk⟩
  · exact ⟨⟨n - 1, by omega⟩, (lj_last (K := K) hr ⟨n - 1, by omega⟩ rfl).1⟩
  · exact ⟨⟨n - 2, by omega⟩, (lj_pen (K := K) hr ⟨n - 2, by omega⟩ rfl).1⟩

theorem lj_antichain {n : ℕ} {K : Type} [Field K] (hn : 4 ≤ n)
    {W W' : Submodule K (Fin n ⊕ Fin n → K)} (hW : W ∈ pOmegaPlusSubspaces n K hn)
    (hW' : W' ∈ pOmegaPlusSubspaces n K hn)
    (hfix : ∀ k : Fin n, weylElt n K k • W = W → weylElt n K k • W' = W') : W = W' := by
  have hr : 3 ≤ n := by omega
  rcases hW with ⟨i, hi1, hi2, rfl⟩ | rfl | rfl <;>
    rcases hW' with ⟨i', hi1', hi2', rfl⟩ | rfl | rfl
  ·
    by_cases hii : i = i'
    · rw [hii]
    · exfalso
      obtain ⟨k, hk1, hkm⟩ := lj_exists_move_flag (K := K) hr hi1' hi2'
      exact hkm (hfix k (lj_fix_flag (K := K) hr hi1 hi2 k (by omega)))
  ·
    exfalso
    have h := hfix ⟨n - 1, by omega⟩
      (lj_fix_flag (K := K) hr hi1 hi2 ⟨n - 1, by omega⟩ (by show n - 1 + 1 ≠ i; omega))
    exact (lj_last (K := K) hr ⟨n - 1, by omega⟩ rfl).1 h
  ·
    exfalso
    have h := hfix ⟨n - 2, by omega⟩
      (lj_fix_flag (K := K) hr hi1 hi2 ⟨n - 2, by omega⟩ (by show n - 2 + 1 ≠ i; omega))
    exact (lj_pen (K := K) hr ⟨n - 2, by omega⟩ rfl).1 h
  ·
    exfalso
    obtain ⟨k, hk1, hkm⟩ := lj_exists_move_flag (K := K) hr hi1' hi2'
    exact hkm (hfix k (lj_top (K := K) hr k (by omega)).1)
  · rfl
  ·
    exfalso
    have h := hfix ⟨n - 2, by omega⟩ (lj_pen (K := K) hr ⟨n - 2, by omega⟩ rfl).2
    exact (lj_pen (K := K) hr ⟨n - 2, by omega⟩ rfl).1 h
  ·
    exfalso
    obtain ⟨k, hk1, hkm⟩ := lj_exists_move_flag (K := K) hr hi1' hi2'
    exact hkm (hfix k (lj_top (K := K) hr k (by omega)).2)
  ·
    exfalso
    have h := hfix ⟨n - 1, by omega⟩ (lj_last (K := K) hr ⟨n - 1, by omega⟩ rfl).2
    exact (lj_last (K := K) hr ⟨n - 1, by omega⟩ rfl).1 h
  · rfl

theorem lj_nu_surj {r : ℕ} {K : Type} [Field K] (hr2 : 2 ≤ r) (hr : 3 ≤ r)
    {M : Subgroup (ljGL r K)} (hall : ∀ i : Fin r, weylElt r K i ∈ M)
    {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} (hw : w ∈ weylGroup r) :
    ∃ z : ljGL r K, ∃ hz : z ∈ torusWeyl r K, z ∈ M ∧
      ((torusWeylNu r K hr2 ⟨z, hz⟩ : weylGroup r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = w := by
  have key : ∀ v ∈ Subgroup.closure (Set.range (simpleRefl r)), ∃ z : ljGL r K,
      ∃ hz : z ∈ torusWeyl r K, z ∈ M ∧
        ((torusWeylNu r K hr2 ⟨z, hz⟩ : weylGroup r) :
          (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = v := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨weylElt r K i, weylElt_mem_torusWeyl i, hall i,
        congrArg Subtype.val (torusWeylNu_weylElt hr2 i)⟩
    | one =>
      exact ⟨1, one_mem _, one_mem _, congrArg Subtype.val (map_one (torusWeylNu r K hr2))⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨z₁, hz₁, hM₁, hν₁⟩ := ihx
      obtain ⟨z₂, hz₂, hM₂, hν₂⟩ := ihy
      refine ⟨z₁ * z₂, mul_mem hz₁ hz₂, mul_mem hM₁ hM₂, ?_⟩
      have e : (⟨z₁ * z₂, mul_mem hz₁ hz₂⟩ : torusWeyl r K) = ⟨z₁, hz₁⟩ * ⟨z₂, hz₂⟩ := rfl
      rw [e, map_mul, Subgroup.coe_mul, hν₁, hν₂]
    | inv x _ ihx =>
      obtain ⟨z, hz, hM, hν⟩ := ihx
      refine ⟨z⁻¹, inv_mem hz, inv_mem hM, ?_⟩
      have e : (⟨z⁻¹, inv_mem hz⟩ : torusWeyl r K) = (⟨z, hz⟩ : torusWeyl r K)⁻¹ := rfl
      rw [e, map_inv, Subgroup.coe_inv, hν]
  obtain ⟨z, hz, hzM, hν⟩ := key w (by rwa [closure_simpleRefl hr])
  exact ⟨z, hz, hzM, hν⟩

theorem lj_core {r : ℕ} {K : Type} [Field K] (hn : 4 ≤ r)
    {M : Subgroup (ljGL r K)} (hMG : M ≤ orthElementaryGroup (quadPlus r K))
    (hUM : unipotent r K ≤ M) (hM : M ≠ orthElementaryGroup (quadPlus r K)) :
    ∃ V ∈ pOmegaPlusSubspaces r K hn, M ≤ MulAction.stabilizer (ljGL r K) V := by
  have hr : 3 ≤ r := by omega
  have hr2 : 2 ≤ r := by omega
  by_cases hall : ∀ i : Fin r, weylElt r K i ∈ M
  · exfalso
    apply hM
    refine le_antisymm hMG ?_
    rw [(orthogonal_geometry_split_root_generation hr).1]
    unfold rootSupr
    refine iSup₂_le fun α hα => ?_
    have hs0 : simpleRoot r ⟨0, by omega⟩ ∈ roots r :=
      posRoots_subset_roots (simpleRoot_mem_posRoots hr2 ⟨0, by omega⟩)
    obtain ⟨w, hw, hwα⟩ := exists_weyl_apply_eq hr hs0 hα
    obtain ⟨z, hz, hzM, hνz⟩ := lj_nu_surj hr2 hr hall hw
    have hX : rootSubgroup r K (simpleRoot r ⟨0, by omega⟩) ≤ M :=
      le_trans (rootSubgroup_le_unipotent (simpleRoot_mem_posRoots hr2 ⟨0, by omega⟩)) hUM
    have hmap := map_conj_rootSubgroup_torusWeyl hr2 ⟨z, hz⟩ hs0
    rw [hνz, hwα] at hmap
    rw [← hmap]
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hzM (hX hy)) (inv_mem hzM)
  · simp only [not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨V, hV, hbV, hfix, -⟩ := lj_table (K := K) hn i
    exact ⟨V, hV, lj_cut_stab hr hMG hUM hbV hfix hi⟩


theorem lj_cover_holds : POmegaPlusCover := by
  intro n K _ _ _ hn A hA hAt
  let M : Subgroup (ljGL n K) := A.map (orthElementaryGroup (quadPlus n K)).subtype
  have hMG : M ≤ orthElementaryGroup (quadPlus n K) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hUM : unipotent n K ≤ M := by
    intro u hu
    have huE : u ∈ orthElementaryGroup (quadPlus n K) := unipotent_le hu
    rw [unipotent_eq_posUnip] at hu
    exact ⟨⟨u, huE⟩, hA (Subgroup.mem_subgroupOf.2 hu), rfl⟩
  have hMne : M ≠ orthElementaryGroup (quadPlus n K) := by
    intro hME
    apply hAt
    rw [eq_top_iff]
    rintro x -
    have hx : (x : ljGL n K) ∈ M := by
      rw [hME]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy
  obtain ⟨V, hV, hle⟩ := lj_core hn hMG hUM hMne
  refine ⟨V, hV, fun x hx => ?_⟩
  exact Subgroup.mem_subgroupOf.2 (hle ⟨x, hx, rfl⟩)

theorem lj_coatom_holds : POmegaPlusCoatom := by
  intro n K _ _ _ hn W hW
  refine ⟨?_, fun c hc hcb => ?_⟩
  · refine lt_of_le_of_ne le_top ?_
    intro htop
    obtain ⟨k, hk⟩ := lj_moved hn hW
    apply hk
    have hmem : (⟨weylElt n K k, weylElt_mem k⟩ : ↥(orthElementaryGroup (quadPlus n K))) ∈
        lf_stab n K W := by
      rw [htop]
      exact Subgroup.mem_top _
    exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_subgroupOf.1 hmem)
  · obtain ⟨W', hW', hcW'⟩ :=
      lj_cover_holds n K hn c ((lf_plus_sub_le hn hW).trans hc.le) (ne_of_lt hcb)
    have hfix : ∀ k : Fin n, weylElt n K k • W = W → weylElt n K k • W' = W' := by
      intro k hk
      have hmem : (⟨weylElt n K k, weylElt_mem k⟩ : ↥(orthElementaryGroup (quadPlus n K))) ∈
          lf_stab n K W :=
        Subgroup.mem_subgroupOf.2 (MulAction.mem_stabilizer_iff.2 hk)
      exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_subgroupOf.1 (hc.le.trans hcW' hmem))
    have hWW' := lj_antichain hn hW hW' hfix
    subst hWW'
    exact lt_irrefl _ (lt_of_lt_of_le hc hcW')

theorem pOmegaPlusCover_holds : POmegaPlusCover := lj_cover_holds

theorem pOmegaPlusCoatom_holds : POmegaPlusCoatom := lj_coatom_holds

end CFSG.Quasithin.LieOver
