module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailBruhatCoverage

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

theorem eq_one_of_weylLengthB_eq_zero {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} (hw : w ∈ weylGroupB r)
    (h0 : weylLengthB r w = 0) : w = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ := exists_simpleRootB_neg hw hne
  have := weylLengthB_pos hw hi
  omega

theorem weylLengthB_one : weylLengthB r (1 : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = 0 := by
  have hempty : inversionSetB r (1 : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = ∅ := by
    ext β
    simp only [inversionSetB, LinearEquiv.coe_one, id_eq, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hβ hβ'
    exact (mem_posRootsB_or_neg_mem_posRootsB (posRootsB_subset_rootsB hβ)).2 ⟨hβ, hβ'⟩
  rw [weylLengthB, hempty, Set.ncard_empty]

theorem tailWeylElt_mem_of_le {M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)} (a₀ : A)
    (i : Fin r) (h1 : tailRootGroup r qA (simpleRootB r i) ≤ M)
    (h2 : tailRootGroup r qA (-simpleRootB r i) ≤ M) : tailWeylElt r qA a₀ i ∈ M := by
  by_cases hi : i.val + 1 < r
  · rw [tailWeylElt_of_lt a₀ hi]
    have hα : simpleRootB r i ∈ roots r :=
      posRoots_subset_roots (simpleRootB_mem_posRoots_of_lt hi)
    have hα' : -simpleRootB r i ∈ roots r := neg_mem_roots hα
    exact mul_mem (mul_mem (h1 ((mem_tailRootGroup_long hα).2 ⟨1, rfl⟩))
      (h2 ((mem_tailRootGroup_long hα').2 ⟨-1, rfl⟩))) (h1 ((mem_tailRootGroup_long hα).2 ⟨1, rfl⟩))
  · rw [tailWeylElt, ite_eq_right hi]
    rw [simpleRootB_of_not_lt hi] at h1 h2
    exact mul_mem (mul_mem (h1 (mem_tailRootGroup_eps.2 ⟨a₀, rfl⟩))
      (h2 (mem_tailRootGroup_neg_eps.2 ⟨_, rfl⟩))) (h1 (mem_tailRootGroup_eps.2 ⟨a₀, rfl⟩))

section Generation

variable [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
include hani ha₀

theorem eq_closure_of_tailBorel_le {M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)}
    (hMG : M ≤ orthElementaryGroup (quadTail r qA)) (hBM : tailBorel r qA ≤ M) :
    M = Subgroup.closure ((tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)) ∪
      tailWeylElt r qA a₀ '' {i | tailWeylElt r qA a₀ i ∈ M}) := by
  set H := Subgroup.closure ((tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)) ∪
    tailWeylElt r qA a₀ '' {i | tailWeylElt r qA a₀ i ∈ M}) with hHdef
  have hBH : tailBorel r qA ≤ H := fun b hb => Subgroup.subset_closure (Or.inl hb)
  have hUM : tailUnipotent r qA ≤ M := (tailUnipotent_le_tailBorel hani).trans hBM
  refine le_antisymm (fun g hg => ?_) ((Subgroup.closure_le _).2 ?_)
  ·
    have key : ∀ ℓ : ℕ, ∀ n (hn : n ∈ tailTorusWeyl r qA a₀), n ∈ M →
        weylLengthB r ((tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩ : weylGroupB r) :
          (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = ℓ → n ∈ H := by
      intro ℓ
      induction ℓ with
      | zero =>
        intro n hn _ hℓ
        have h1 := eq_one_of_weylLengthB_eq_zero (tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩).2 hℓ
        have hker : (⟨n, hn⟩ : tailTorusWeyl r qA a₀) ∈ (tailTorusWeylNu r qA hani ha₀).ker :=
          MonoidHom.mem_ker.2 (Subtype.ext h1)
        rw [tailTorusWeylNu_ker hani ha₀, Subgroup.mem_subgroupOf] at hker
        exact hBH (tailTorus_le_tailBorel hker)
      | succ ℓ ih =>
        intro n hn hnM hℓ
        set w := ((tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩ : weylGroupB r) :
          (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) with hw
        have hwW : w ∈ weylGroupB r := (tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩).2
        have hne : w ≠ 1 := by
          rintro h1
          rw [h1, weylLengthB_one] at hℓ
          omega
        obtain ⟨i, hi⟩ := exists_simpleRootB_neg hwW hne
        have hα := simpleRootB_mem_posRootsB (r := r) i
        have hXα : tailRootGroup r qA (simpleRootB r i) ≤ M :=
          (tailRootGroup_le_tailUnipotent hα).trans hUM
        have hXβ : tailRootGroup r qA (-(w⁻¹ (simpleRootB r i))) ≤ M :=
          (tailRootGroup_le_tailUnipotent hi).trans hUM
        have hmap := map_conj_tailRootGroup hani ha₀ ⟨n, hn⟩ (posRootsB_subset_rootsB hi)
        have hww : w (w⁻¹ (simpleRootB r i)) = simpleRootB r i := by
          rw [LinearEquiv.coe_inv]
          exact LinearEquiv.apply_symm_apply _ _
        rw [← hw, map_neg, hww] at hmap
        have hXneg : tailRootGroup r qA (-simpleRootB r i) ≤ M := by
          rw [← hmap]
          rintro _ ⟨y, hy, rfl⟩
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact mul_mem (mul_mem hnM (hXβ hy)) (inv_mem hnM)
        have hniM : tailWeylElt r qA a₀ i ∈ M := tailWeylElt_mem_of_le a₀ i hXα hXneg
        have hniH : tailWeylElt r qA a₀ i ∈ H := Subgroup.subset_closure (Or.inr ⟨i, hniM, rfl⟩)
        have hn' : (tailWeylElt r qA a₀ i)⁻¹ * n ∈ tailTorusWeyl r qA a₀ :=
          mul_mem (inv_mem (tailWeylElt_mem_tailTorusWeyl a₀ i)) hn
        have hν : ((tailTorusWeylNu r qA hani ha₀ ⟨_, hn'⟩ : weylGroupB r) :
            (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = simpleReflB r i * w := by
          have he : (⟨(tailWeylElt r qA a₀ i)⁻¹ * n, hn'⟩ : tailTorusWeyl r qA a₀) =
              (⟨tailWeylElt r qA a₀ i, tailWeylElt_mem_tailTorusWeyl a₀ i⟩ :
                tailTorusWeyl r qA a₀)⁻¹ * ⟨n, hn⟩ := rfl
          rw [he, map_mul, map_inv, tailTorusWeylNu_tailWeylElt hani ha₀ i, Subgroup.coe_mul,
            Subgroup.coe_inv]
          congr 1
          rw [inv_eq_iff_mul_eq_one, simpleReflB_mul_self]
        have hlen := weylLengthB_simpleReflB_mul hwW hi
        rw [← hν, hℓ, Nat.add_sub_cancel] at hlen
        have := ih _ hn' (mul_mem (inv_mem hniM) hnM) hlen
        have he : n = tailWeylElt r qA a₀ i * ((tailWeylElt r qA a₀ i)⁻¹ * n) := by group
        rw [he]
        exact mul_mem hniH this
    obtain ⟨b₁, h1, n, hn, b₂, h2, rfl⟩ :=
      (orthogonal_geometry_tail_Bruhat_coverage hani ha₀ g).1 (hMG hg)
    have hnM : n ∈ M := by
      have : n = b₁⁻¹ * (b₁ * n * b₂) * b₂⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem (hBM h1)) hg) (inv_mem (hBM h2))
    exact mul_mem (mul_mem (hBH h1) (key _ n hn hnM rfl)) (hBH h2)
  · rintro _ (hb | ⟨i, hi, rfl⟩)
    · exact hBM hb
    · exact hi

theorem eq_stabilizer_of_isMax_tail {M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)}
    (hMG : M ≤ orthElementaryGroup (quadTail r qA)) (hBM : tailBorel r qA ≤ M)
    (hne : M ≠ orthElementaryGroup (quadTail r qA))
    (hmax : ∀ M' : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)),
      M ≤ M' → M' ≤ orthElementaryGroup (quadTail r qA) →
        M' = M ∨ M' = orthElementaryGroup (quadTail r qA)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ M = orthElementaryGroup (quadTail r qA) ⊓
      MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
        (tailFlag K A r k) := by
  have hgen := eq_closure_of_tailBorel_le hani ha₀ hMG hBM
  obtain ⟨i, hi⟩ : ∃ i, tailWeylElt r qA a₀ i ∉ M := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    refine le_antisymm hMG ?_
    rw [orthogonal_geometry_tail_Borel_Weyl_generation hani ha₀, Subgroup.closure_le]
    rintro _ (hb | ⟨j, rfl⟩)
    · exact hBM hb
    · exact h j
  have hBV : tailBorel r qA ≤ MulAction.stabilizer
      (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) (tailFlag K A r (i + 1)) :=
    fun b hb => Submodule.mem_stabilizer_submodule_iff_map_eq.2
      ((mem_tailBorel.1 hb).2 _ (by omega) (by have := i.isLt; omega))
  have hle : M ≤ orthElementaryGroup (quadTail r qA) ⊓
      MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
        (tailFlag K A r (i + 1)) := by
    refine le_inf hMG ?_
    rw [hgen, Subgroup.closure_le]
    rintro _ (hb | ⟨j, hj, rfl⟩)
    · exact hBV hb
    · refine MulAction.mem_stabilizer_iff.2 ((tailWeylElt_smul_tailFlag hani ha₀ i j).2 ?_)
      rintro rfl
      exact hi hj
  refine ⟨i.val + 1, by omega, by have := i.isLt; omega, ?_⟩
  rcases hmax _ hle inf_le_left with h | h
  · exact h.symm
  · exfalso
    have hni : tailWeylElt r qA a₀ i ∈ orthElementaryGroup (quadTail r qA) ⊓
        MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
          (tailFlag K A r (i + 1)) := by
      rw [h]
      exact tailWeylElt_mem a₀ i
    exact ((tailWeylElt_smul_tailFlag hani ha₀ i i).1
      (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hni).2)) rfl

end Generation

theorem orthogonal_geometry_tail_maximal_Borel_overgroups {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) :
    (∀ M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)),
      M ≤ orthElementaryGroup (quadTail r qA) → tailBorel r qA ≤ M →
      M = Subgroup.closure ((tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)) ∪
        tailWeylElt r qA a₀ '' {i | tailWeylElt r qA a₀ i ∈ M})) ∧
    ∀ M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)),
      M ≤ orthElementaryGroup (quadTail r qA) → tailBorel r qA ≤ M →
      M ≠ orthElementaryGroup (quadTail r qA) →
      (∀ M' : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)), M ≤ M' →
        M' ≤ orthElementaryGroup (quadTail r qA) →
        M' = M ∨ M' = orthElementaryGroup (quadTail r qA)) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ M = orthElementaryGroup (quadTail r qA) ⊓
        MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
          (tailFlag K A r k) :=
  ⟨fun _ hMG hBM => eq_closure_of_tailBorel_le hani ha₀ hMG hBM,
    fun _ hMG hBM hne hmax => eq_stabilizer_of_isMax_tail hani ha₀ hMG hBM hne hmax⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
