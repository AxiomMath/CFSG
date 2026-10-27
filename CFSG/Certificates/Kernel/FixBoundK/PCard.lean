module

public import CFSG.Certificates.Kernel.FixBoundK.FixMath
public import CFSG.Certificates.Kernel.FixBoundK.Complete

public noncomputable section

namespace CFSG.KC.FixBoundK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Quasithin.H.Mathieu

theorem imgL_unique {σ τ : Equiv.Perm (Fin 24)} {g : List Nat} (hσ : ImgL σ g) (hτ : ImgL τ g) :
    σ = τ :=
  Equiv.ext fun i => Fin.ext ((hσ.2 i).trans (hτ.2 i).symm)

theorem card_closure_GenSet_le {gens : List (List Nat)}
    (hP : CFSG.Open.IsElemAbelian 2 (Subgroup.closure (GenSet gens))) :
    Nat.card (Subgroup.closure (GenSet gens)) ≤ 2 ^ gens.length := by
  classical
  set P := Subgroup.closure (GenSet gens)
  set n := gens.length
  let h : Nat → AutPerm := fun i =>
    if hx : ∃ σ : AutPerm, ImgL (σ : Equiv.Perm (Fin 24)) (gens.getD i []) then hx.choose else 1
  have hhP : ∀ i, h i ∈ P := by
    intro i
    by_cases hx : ∃ σ : AutPerm, ImgL (σ : Equiv.Perm (Fin 24)) (gens.getD i [])
    · have e : h i = hx.choose := dif_pos hx
      rw [e]
      by_cases hi : i < n
      · have hg : gens.getD i [] ∈ gens := by
          rw [List.getD_eq_getElem _ _ hi]
          exact List.getElem_mem hi
        exact Subgroup.subset_closure ⟨_, hg, hx.choose_spec⟩
      · have hl := hx.choose_spec.1
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at hl
        exact absurd hl (by simp)
    · have e : h i = 1 := dif_neg hx
      rw [e]
      exact P.one_mem
  have hc : ∀ i j, Commute (h i) (h j) := fun i j =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨h i, hhP i⟩ ⟨h j, hhP j⟩)
  have hsq : ∀ i, h i * h i = 1 := fun i => by
    rw [← pow_two]
    exact hP.2 _ (hhP i)
  have hgen : ∀ σ ∈ GenSet gens, ∃ i < n, σ = h i := by
    rintro σ ⟨g, hg, hσ⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    have hσ' : ImgL (σ : Equiv.Perm (Fin 24)) (gens.getD i []) := by
      rwa [List.getD_eq_getElem _ _ hi]
    have hx : ∃ τ : AutPerm, ImgL (τ : Equiv.Perm (Fin 24)) (gens.getD i []) := ⟨σ, hσ'⟩
    refine ⟨i, hi, ?_⟩
    have e : h i = hx.choose := dif_pos hx
    rw [e]
    exact Subtype.ext (imgL_unique hσ' hx.choose_spec)
  have h0 : prodL h (List.range n) 0 = 1 :=
    List.prod_eq_one fun b hb => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hb
      simp
  let T : Subgroup AutPerm :=
    { carrier := (fun μ => prodL h (List.range n) μ) '' ((Finset.range (2 ^ n) : Finset Nat) : Set Nat)
      one_mem' := ⟨0, by simp, h0⟩
      mul_mem' := by
        rintro _ _ ⟨μ, hμ, rfl⟩ ⟨ν, hν, rfl⟩
        refine ⟨μ ^^^ ν, ?_, prodL_xor hc hsq _ μ ν⟩
        simp only [Finset.coe_range, Set.mem_Iio] at hμ hν ⊢
        exact Nat.xor_lt_two_pow hμ hν
      inv_mem' := by
        rintro _ ⟨μ, hμ, rfl⟩
        refine ⟨μ, hμ, ?_⟩
        have e : prodL h (List.range n) μ * prodL h (List.range n) μ = 1 := by
          rw [← prodL_xor hc hsq, Nat.xor_self, h0]
        exact eq_inv_of_mul_eq_one_left e }
  have hPT : P ≤ T := (Subgroup.closure_le T).2 fun σ hσ => by
    obtain ⟨i, hi, rfl⟩ := hgen σ hσ
    refine ⟨2 ^ i, ?_, prodL_two_pow h List.nodup_range (List.mem_range.2 hi)⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.pow_lt_pow_right (by norm_num) hi
  have hT : Nat.card T ≤ 2 ^ n := by
    change Nat.card ↥((fun μ => prodL h (List.range n) μ) ''
      ((Finset.range (2 ^ n) : Finset Nat) : Set Nat)) ≤ _
    rw [Nat.card_coe_set_eq]
    calc _ ≤ ((Finset.range (2 ^ n) : Finset Nat) : Set Nat).ncard :=
          Set.ncard_image_le (Finset.finite_toSet _)
      _ = 2 ^ n := by rw [Set.ncard_coe_finset, Finset.card_range]
  exact le_trans (Subgroup.card_le_of_le hPT) hT

end CFSG.KC.FixBoundK

end
