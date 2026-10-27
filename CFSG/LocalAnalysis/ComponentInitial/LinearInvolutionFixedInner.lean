module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

theorem isCompl_eigenspaces (hK : ringChar K ≠ 2) {B : Matrix (Fin n) (Fin n) K}
    (hB : B * B = 1) :
    IsCompl (LinearMap.ker (toLin' B - 1)) (LinearMap.ker (toLin' B + 1)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hBB : ∀ v : Fin n → K, B *ᵥ (B *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hB, one_mulVec]
  refine isCompl_iff.2 ⟨Submodule.disjoint_def.2 fun v h1 h2' => ?_, codisjoint_iff.2 ?_⟩
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, toLin'_apply, Module.End.one_apply,
      sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.add_apply, toLin'_apply, Module.End.one_apply, h1] at h2'
    have : (2 : K) • v = 0 := by rw [two_smul]; exact h2'
    exact (smul_eq_zero.1 this).resolve_left h2
  · refine eq_top_iff.2 fun v _ => Submodule.mem_sup.2 ⟨(2 : K)⁻¹ • (v + B *ᵥ v), ?_,
      (2 : K)⁻¹ • (v - B *ᵥ v), ?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, toLin'_apply, Module.End.one_apply,
        mulVec_smul, mulVec_add, hBB, add_comm (B *ᵥ v), sub_self]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, toLin'_apply, Module.End.one_apply,
        mulVec_smul, mulVec_sub, hBB, ← smul_add, sub_add_sub_cancel', sub_self, smul_zero]
    · rw [← smul_add, add_add_sub_cancel, ← two_smul K v, smul_smul, inv_mul_cancel₀ h2,
        one_smul]

theorem exists_eigenbasis (hK : ringChar K ≠ 2) {B : Matrix (Fin n) (Fin n) K}
    (hB : B * B = 1) :
    ∃ b : Basis (Fin n) K (Fin n → K), ∀ i : Fin n,
      B *ᵥ b i = (if (i : ℕ) < finrank K (LinearMap.ker (toLin' B - 1)) then 1 else -1 : K) •
        b i := by
  set Vp := LinearMap.ker (toLin' B - 1) with hVp
  set Vm := LinearMap.ker (toLin' B + 1) with hVm
  have hc := isCompl_eigenspaces hK hB
  have hkl : finrank K Vp + finrank K Vm = n := by
    rw [Submodule.finrank_add_eq_of_isCompl hc, finrank_fin_fun]
  set e := finSumFinEquiv.trans (finCongr hkl) with he
  set b₀ := ((Module.finBasis K Vp).prod (Module.finBasis K Vm)).map
    (Submodule.prodEquivOfIsCompl Vp Vm hc) with hb₀
  refine ⟨b₀.reindex e, fun i => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective i
  rw [Basis.reindex_apply, Equiv.symm_apply_apply]
  rcases a with j | j
  · have hv : b₀ (Sum.inl j) = ((Module.finBasis K Vp j : Vp) : Fin n → K) := by
      rw [hb₀, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl', Basis.prod_apply_inl_fst,
        Basis.prod_apply_inl_snd, Submodule.coe_zero, add_zero]
    have hlt : ((e (Sum.inl j) : Fin n) : ℕ) < finrank K Vp := by simp [he]
    simp only [hlt, ↓reduceIte, one_smul, hv]
    have hmem : (toLin' B - 1) ((Module.finBasis K Vp j : Vp) : Fin n → K) = 0 :=
      (Module.finBasis K Vp j).2
    rw [LinearMap.sub_apply, toLin'_apply, Module.End.one_apply, sub_eq_zero] at hmem
    exact hmem
  · have hv : b₀ (Sum.inr j) = ((Module.finBasis K Vm j : Vm) : Fin n → K) := by
      rw [hb₀, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl', Basis.prod_apply_inr_fst,
        Basis.prod_apply_inr_snd, Submodule.coe_zero, zero_add]
    have hlt : ¬ ((e (Sum.inr j) : Fin n) : ℕ) < finrank K Vp := by simp [he]
    simp only [hlt, ↓reduceIte, neg_one_smul, hv]
    have hmem : (toLin' B + 1) ((Module.finBasis K Vm j : Vm) : Fin n → K) = 0 :=
      (Module.finBasis K Vm j).2
    rw [LinearMap.add_apply, toLin'_apply, Module.End.one_apply] at hmem
    exact eq_neg_of_add_eq_zero_left hmem

theorem conjAut_neg (B : GL (Fin n) K) : conjAut n K (-B) = conjAut n K B := by
  have h : -B = GeneralLinearGroup.scalar (Fin n) (-1) * B := by
    apply Units.ext
    rw [Units.val_neg, Units.val_mul]
    change -(B : Matrix (Fin n) (Fin n) K) = scalar (Fin n) ((-1 : Kˣ) : K) * B
    ext i j
    rw [scalar_apply, diagonal_mul]
    simp
  rw [h, map_mul, conjAut_scalar, one_mul]

theorem exists_fixed_perfect_even_conjAut_of_mul_self_eq_one (hK : ringChar K ≠ 2)
    (h4 : ∃ s : Finset K, s.card = 4) {m : ℕ} (hm : 1 ≤ m) (B : GL (Fin (2 + m)) K)
    (hB : B * B = 1) :
    ∃ P : Subgroup (projectiveSL (2 + m) K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, conjAut (2 + m) K B s = s := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have key : ∀ B' : GL (Fin (2 + m)) K, B' * B' = 1 →
      2 ≤ finrank K (LinearMap.ker (toLin' B'.val - 1)) →
      ∃ P : Subgroup (projectiveSL (2 + m) K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
        ∀ s ∈ P, conjAut (2 + m) K B' s = s := by
    intro B' hB' h2
    have hBm : (B' : Matrix (Fin (2 + m)) (Fin (2 + m)) K) * B' = 1 := by
      rw [← Units.val_mul, hB', Units.val_one]
    obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
    obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B'
    set k := finrank K (LinearMap.ker (toLin' (B' : Matrix (Fin (2 + m)) (Fin (2 + m)) K) - 1))
      with hk
    set d : Fin (2 + m) → K := fun i => if (i : ℕ) < k then 1 else -1 with hd
    have hDd : (D : Matrix (Fin (2 + m)) (Fin (2 + m)) K) = diagonal d := by
      rw [hD]
      ext a c
      rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, map_smul, Basis.repr_self,
        Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
      by_cases hac : a = c
      · subst hac
        simp [hd]
      · simp [hac, Ne.symm hac]
    have hconj : conjAut (2 + m) K B' =
        conjAut (2 + m) K P * conjAut (2 + m) K D * (conjAut (2 + m) K P)⁻¹ := by
      rw [← hPD, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    refine exists_fixed_perfect_even_conj hconj ?_
    refine exists_fixed_perfect_even_of_hom ((blockGL K 2 m).comp SpecialLinearGroup.toGL)
      (conjAut (2 + m) K D) ?_ (QuaternionMatrices.slQuatI K) QuaternionMatrices.slQuatI_pow_four
      ?_
    · intro X hX
      refine (conjAut_proj D _).trans ?_
      congr 1
      apply Subtype.ext
      refine (coe_slConjugation D _).trans ?_
      change (D : Matrix (Fin (2 + m)) (Fin (2 + m)) K) *
          (blockGL K 2 m (SpecialLinearGroup.toGL X) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) *
          ((D⁻¹ : GL (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) = _
      rw [hDd, ← blockGL_mul_diagonal_comm, Matrix.mul_assoc, ← hDd, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
      · rfl
      · intro i j
        have hi : ((finSumFinEquiv (Sum.inl i : Fin 2 ⊕ Fin m) : Fin (2 + m)) : ℕ) < k := by
          simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
          omega
        have hj : ((finSumFinEquiv (Sum.inl j : Fin 2 ⊕ Fin m) : Fin (2 + m)) : ℕ) < k := by
          simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
          omega
        simp only [hd, hi, hj, ↓reduceIte]
    · intro c
      refine blockGL_ne_scalar_of_ne_one hm (fun h1 => ?_) c
      have h1' : QuaternionMatrices.slQuatI K = 1 :=
        SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm)
      have := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0)
        h1'
      simp [QuaternionMatrices.slQuatI, QuaternionMatrices.quatI] at this
  by_cases h2 : 2 ≤ finrank K (LinearMap.ker (toLin' B.val - 1))
  · exact key B hB h2
  · have hBm : (B : Matrix (Fin (2 + m)) (Fin (2 + m)) K) * B = 1 := by
      rw [← Units.val_mul, hB, Units.val_one]
    have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hK hBm)
    rw [finrank_fin_fun] at hsum
    have hker : LinearMap.ker (toLin' ((-B : GL (Fin (2 + m)) K) :
        Matrix (Fin (2 + m)) (Fin (2 + m)) K) - 1) =
          LinearMap.ker (toLin' (B : Matrix (Fin (2 + m)) (Fin (2 + m)) K) + 1) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
        Module.End.one_apply, Units.val_neg, neg_mulVec]
      rw [← neg_add', neg_eq_zero]
    obtain ⟨P, hP, he, hfix⟩ := key (-B) (by rw [neg_mul_neg, hB]) (by rw [hker]; omega)
    exact ⟨P, hP, he, fun s hs => by rw [← conjAut_neg]; exact hfix s hs⟩

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
