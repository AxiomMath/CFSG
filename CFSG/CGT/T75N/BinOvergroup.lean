module

public import CFSG.CGT.T75N.BinTransvection

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {F : Type} [Field F] {m : ℕ}

theorem eq_top_of_unitriangular_le (hF : Nat.card F = 2) (hm : 1 ≤ m)
    (S : Subgroup (SpecialLinearGroup (Fin (m + 1)) F))
    (hU : unitriangular (m + 1) F ≤ S)
    (hirr : ∀ X : Submodule F (Fin (m + 1) → F),
      (∀ s ∈ S, ∀ v ∈ X, (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ v ∈ X) →
        X = ⊥ ∨ X = ⊤) :
    S = ⊤ := by
  classical
  set e0 : Fin (m + 1) → F := Pi.single 0 1 with he0
  set eL : Fin (m + 1) → F := Pi.single (Fin.last m) 1 with heL
  have hXinv : ∀ s ∈ S, ∀ v ∈ Submodule.span F (Set.range fun t : S =>
      ((t : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0),
      (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ v ∈ Submodule.span F (Set.range fun t : S =>
      ((t : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0) := by
    intro s hs v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨t, ht⟩, rfl⟩ := hx
      refine Submodule.subset_span ⟨⟨s * t, S.mul_mem hs ht⟩, ?_⟩
      show ((s * t : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
        e0 = _
      rw [SpecialLinearGroup.coe_mul, mulVec_mulVec]
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ a hx
  have hXne : Submodule.span F (Set.range fun t : S =>
      ((t : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0)
      ≠ ⊥ := by
    intro h
    have h1 : e0 ∈ Submodule.span F (Set.range fun t : S =>
        ((t : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0) :=
      Submodule.subset_span ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at h1
    have h2 := congrFun h1 0
    simp [he0] at h2
  have hXtop := (hirr _ hXinv).resolve_left hXne
  obtain ⟨⟨s, hs⟩, hsL⟩ : ∃ s : S, (((s : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0) (Fin.last m) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : Submodule.span F (Set.range fun t : S =>
        ((t : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0)
        ≤ LinearMap.ker (LinearMap.proj (Fin.last m) : (Fin (m + 1) → F) →ₗ[F] F) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact hcon t
    have h1 := LinearMap.mem_ker.1 (hle (hXtop ▸ Submodule.mem_top : eL ∈ _))
    simp [heL] at h1
  set v : Fin (m + 1) → F := ((s : SpecialLinearGroup (Fin (m + 1)) F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0 with hv
  have hvL : v (Fin.last m) = 1 := (eq_zero_or_one_of_card_two hF _).resolve_left hsL
  set w : Fin (m + 1) → F := v - eL with hw
  have hwL : w (Fin.last m) = 0 := by simp [hw, heL, hvL]
  have hu0 : eL ⬝ᵥ w = 0 := by simp [heL, hwL]
  have hu_mem : tv w eL hu0 ∈ unitriangular (m + 1) F := by
    refine tv_mem_unitriangular hu0 fun a b hba => ?_
    by_cases hb : b = Fin.last m
    · have ha : a = Fin.last m := le_antisymm (Fin.le_last a) (hb ▸ hba)
      rw [ha, hwL, zero_mul]
    · simp [heL, hb]
  have hu_act : ((tv w eL hu0 : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ eL = v := by
    rw [tv_mulVec]
    have : eL ⬝ᵥ eL = 1 := by simp [heL]
    rw [this, one_smul, hw]
    abel
  set g₀ : SpecialLinearGroup (Fin (m + 1)) F := (tv w eL hu0)⁻¹ * s with hg₀
  have hg₀S : g₀ ∈ S := S.mul_mem (S.inv_mem (hU hu_mem)) hs
  have hg₀e : (g₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0 = eL := by
    rw [hg₀, SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
    change (((tv w eL hu0)⁻¹ : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ v = eL
    rw [← hu_act, mulVec_mulVec, coe_inv_mul_coe, one_mulVec]
  have hlow : ∀ (j : Fin (m + 1)) (hj : Fin.last m ≠ j),
      SpecialLinearGroup.transvection hj (1 : F) ∈ S := by
    intro j hj
    set ψ : Fin (m + 1) → F := fun k => (g₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) j k with hψ
    have hψ0 : ψ 0 = 0 := by
      have h := congrFun hg₀e j
      simpa [he0, heL, Pi.single_apply, hj.symm, mulVec_single_one] using h
    have hψv : ψ ⬝ᵥ e0 = 0 := by simp [he0, hψ0]
    have ht : tv e0 ψ hψv ∈ unitriangular (m + 1) F := by
      refine tv_mem_unitriangular hψv fun a b hba => ?_
      by_cases ha : a = 0
      · have hb : b = 0 := Fin.le_zero_iff.1 (ha ▸ hba)
        rw [hb, hψ0, mul_zero]
      · simp [he0, ha]
    have hψg : ψ ᵥ* ((g₀⁻¹ : SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Pi.single j 1 := by
      funext k
      have h := congrFun (congrFun (coe_mul_coe_inv g₀) j) k
      rw [Matrix.mul_apply] at h
      simp only [vecMul, dotProduct, hψ, h, Matrix.one_apply, Pi.single_apply]
      simp [eq_comm]
    have hT : g₀ * tv e0 ψ hψv * g₀⁻¹ = SpecialLinearGroup.transvection hj (1 : F) := by
      rw [tv_conj, transvection_eq_tv hj]
      exact tv_congr hg₀e hψg _ _
    rw [← hT]
    exact S.mul_mem (S.mul_mem hg₀S (hU ht)) (S.inv_mem hg₀S)
  refine eq_top_of_transvections hF (by omega) S ?_
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hU (transvection_mem_unitriangular hlt)
  · by_cases hi : i = Fin.last m
    · subst hi
      exact hlow j hij
    · have hil : i < Fin.last m := lt_of_le_of_ne (Fin.le_last i) hi
      have hjl : j ≠ Fin.last m := ne_of_lt (lt_trans hgt hil)
      have h1 := hU (transvection_mem_unitriangular (F := F) hil)
      have h2 := hlow j (Ne.symm hjl)
      rw [← commutator_transvection (ne_of_lt hil) (Ne.symm hjl) hij, commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem h1 h2) (S.inv_mem h1)) (S.inv_mem h2)

end CFSG.CGT.T75N
