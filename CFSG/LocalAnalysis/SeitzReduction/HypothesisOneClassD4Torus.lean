module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

variable {τ : Tag} {K : Type} [Field K]

theorem iform_eq_zero_of_not_isRoot_add_sub
    {σ σ' : Fin τ.rank → ℤ} (hσ : IsRoot τ σ) (hσ' : IsRoot τ σ')
    (hne : σ ≠ σ') (hne' : σ ≠ -σ') (hadd : ¬IsRoot τ (σ + σ')) (hsub : ¬IsRoot τ (σ - σ')) :
    iform σ σ' = 0 := by
  rcases lt_trichotomy (iform σ σ') 0 with h | h | h
  · exact absurd (isRoot_add_of_iform_neg hσ hσ' hne' h) hadd
  · exact h
  · exact absurd (isRoot_sub_of_iform_pos hσ hσ' hne h) hsub

variable (τ K) in
@[expose] noncomputable def frameTorusElt
    (σ : Fin τ.rank → ℤ) (a : Kˣ) : ModGL τ K :=
  ((List.finRange τ.rank).map fun i => torusElt τ K i (a ^ (τ.symmetrizer i i * σ i))).prod

theorem frameTorusElt_mem_adjointGroup
    (σ : Fin τ.rank → ℤ) (a : Kˣ) :
    frameTorusElt τ K σ a ∈ adjointGroup τ K :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact torusElt_mem_adjointGroup i _

theorem frameTorusElt_mem_torusGroup
    (σ : Fin τ.rank → ℤ) (a : Kˣ) :
    frameTorusElt τ K σ a ∈ torusGroup τ K :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact torusElt_mem_torusGroup i _

theorem frameTorusElt_conj_pinnedX
    (σ : Fin τ.rank → ℤ) (a : Kˣ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (c : K) :
    frameTorusElt τ K σ a * pinnedX τ K γ c * (frameTorusElt τ K σ a)⁻¹ =
      pinnedX τ K γ (((a ^ iform σ γ : Kˣ) : K) * c) := by
  have h := list_prod_torusElt_eq_rootDiagUnit (τ := τ) (K := K)
    fun i => a ^ (τ.symmetrizer i i * σ i)
  rw [frameTorusElt, h, rootDiagUnit_conj_pinnedX _ hγ]
  congr 3
  simp only [rootChar, cartanChar, ← zpow_mul, prod_zpow_eq_zpow_sum]
  congr 1
  simp only [iform, symmetrizedCartan_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem frameTorus_exists_sq_eq [Finite K] [CharP K 2] (u : Kˣ) : ∃ a : Kˣ, a ^ 2 = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective fun a : Kˣ => a ^ 2 := fun a b hab => by
    have h := congrArg (fun x : Kˣ => (x : K)) hab
    simp only [Units.val_pow_eq_pow_val] at h
    exact Units.ext (frobenius_inj K 2 (by simpa only [frobenius_def] using h))
  exact Finite.injective_iff_surjective.1 hinj u

theorem frameTorus_exists_zpow_eq [Finite K] [CharP K 2] {n : ℤ} (hn : n = 2 ∨ n = 4)
    (u : Kˣ) : ∃ a : Kˣ, a ^ n = u := by
  obtain ⟨b, hb⟩ := frameTorus_exists_sq_eq u
  rcases hn with rfl | rfl
  · exact ⟨b, by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hb]⟩
  · obtain ⟨a, ha⟩ := frameTorus_exists_sq_eq b
    refine ⟨a, ?_⟩
    rw [show (4 : ℤ) = ((2 * 2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_mul, ha, hb]

theorem frameTorus_conj_list_prod_of_forall {G : Type*} [Group G] (A : G) (L : List G)
    (h : ∀ x ∈ L, A * x * A⁻¹ = x) : A * L.prod * A⁻¹ = L.prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.prod_cons, show A * (x * L.prod) * A⁻¹ = (A * x * A⁻¹) * (A * L.prod * A⁻¹) by group,
      h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem exists_torus_conj_frame_prod
    [Finite K] [CharP K 2] (hτ : NoG2 τ)
    {F : List (Fin τ.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot τ σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) (c : (Fin τ.rank → ℤ) → K)
    (hc : ∀ σ ∈ F, c σ ≠ 0) :
    ∃ h ∈ adjointGroup τ K, h ∈ torusGroup τ K ∧
      (∀ γ, IsRoot τ γ → (∀ σ ∈ F, iform σ γ = 0) → ∀ e : K,
        h * pinnedX τ K γ e * h⁻¹ = pinnedX τ K γ e) ∧
      h * (F.map fun σ => pinnedX τ K σ (c σ)).prod * h⁻¹ =
        (F.map fun σ => pinnedX τ K σ 1).prod := by
  induction F with
  | nil =>
    exact ⟨1, one_mem _, one_mem _, fun γ _ _ e => by rw [one_mul, inv_one, mul_one], by simp⟩
  | cons σ F ih =>
    obtain ⟨hσF, hFF⟩ := List.pairwise_cons.1 horth
    obtain ⟨h', hC', hT', hfix', hprod'⟩ := ih (fun σ' h => hF σ' (List.mem_cons_of_mem _ h)) hFF
      fun σ' h => hc σ' (List.mem_cons_of_mem _ h)
    have hσ := hF σ List.mem_cons_self
    obtain ⟨a, ha⟩ := frameTorus_exists_zpow_eq (iform_self_cases hτ hσ)
      (Units.mk0 (c σ) (hc σ List.mem_cons_self))⁻¹
    set A := frameTorusElt τ K σ a with hA
    have hfixA : ∀ γ, IsRoot τ γ → iform σ γ = 0 → ∀ e : K,
        A * pinnedX τ K γ e * A⁻¹ = pinnedX τ K γ e := fun γ hγ h0 e => by
      rw [hA, frameTorusElt_conj_pinnedX _ _ hγ, h0, zpow_zero, Units.val_one, one_mul]
    refine ⟨A * h', mul_mem (frameTorusElt_mem_adjointGroup σ a) hC',
      mul_mem (frameTorusElt_mem_torusGroup σ a) hT', fun γ hγ hγF e => ?_, ?_⟩
    · rw [show A * h' * pinnedX τ K γ e * (A * h')⁻¹ = A * (h' * pinnedX τ K γ e * h'⁻¹) * A⁻¹ by
          group, hfix' γ hγ (fun σ' h => hγF σ' (List.mem_cons_of_mem _ h)) e,
        hfixA γ hγ (hγF σ List.mem_cons_self) e]
    · have hσ' : ∀ σ' ∈ F, iform σ' σ = 0 := fun σ' h => by rw [iform_comm]; exact hσF σ' h
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        show A * h' * (pinnedX τ K σ (c σ) * (F.map fun σ => pinnedX τ K σ (c σ)).prod) *
            (A * h')⁻¹ = A * (h' * pinnedX τ K σ (c σ) * h'⁻¹) * A⁻¹ *
              (A * (h' * (F.map fun σ => pinnedX τ K σ (c σ)).prod * h'⁻¹) * A⁻¹) by group,
        hfix' σ hσ hσ' (c σ), hprod', frameTorusElt_conj_pinnedX _ _ hσ, ha]
      congr 1
      · congr 1
        simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
        exact inv_mul_cancel₀ (hc σ List.mem_cons_self)
      · refine frameTorus_conj_list_prod_of_forall A _ fun x hx => ?_
        obtain ⟨σ', hσ'F, rfl⟩ := List.mem_map.1 hx
        exact hfixA σ' (hF σ' (List.mem_cons_of_mem _ hσ'F)) (hσF σ' hσ'F) 1

theorem exists_torus_conj_frame_prod_of_not_isRoot
    [Finite K] [CharP K 2]
    (hτ : NoG2 τ) {F : List (Fin τ.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot τ σ)
    (hfr : F.Pairwise fun σ σ' =>
      σ ≠ σ' ∧ σ ≠ -σ' ∧ ¬IsRoot τ (σ + σ') ∧ ¬IsRoot τ (σ - σ'))
    (c : (Fin τ.rank → ℤ) → K) (hc : ∀ σ ∈ F, c σ ≠ 0) :
    ∃ h ∈ adjointGroup τ K, h ∈ torusGroup τ K ∧
      (∀ γ, IsRoot τ γ → (∀ σ ∈ F, iform σ γ = 0) → ∀ e : K,
        h * pinnedX τ K γ e * h⁻¹ = pinnedX τ K γ e) ∧
      h * (F.map fun σ => pinnedX τ K σ (c σ)).prod * h⁻¹ =
        (F.map fun σ => pinnedX τ K σ 1).prod :=
  exists_torus_conj_frame_prod hτ hF (hfr.imp_of_mem fun hσ hσ' h =>
    iform_eq_zero_of_not_isRoot_add_sub (hF _ hσ) (hF _ hσ') h.1 h.2.1 h.2.2.1 h.2.2.2) c hc

end CFSG.SeitzReduction
