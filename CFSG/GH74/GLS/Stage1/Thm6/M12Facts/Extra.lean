module

public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Sub
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.M12Facts

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13

@[expose] def pR1 (p : NF) : Prop :=
  p ∈ [(0, 0, 0, 0), (0, 2, 1, 0), (1, 1, 1, 0), (1, 3, 0, 0), (2, 0, 1, 0), (2, 2, 0, 0),
    (3, 1, 0, 0), (3, 3, 1, 0)]

instance : DecidablePred pR1 := fun p => by unfold pR1; infer_instance

theorem closed_pR1 : NFClosed pR1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem conj_pR1 : ∀ p q : NF, pR1 q → pR1 (nfMul (nfMul p q) (nfInv p)) := by decide +kernel

theorem pR_of_pR1 : ∀ p : NF, pR1 p → pR p := by decide +kernel

@[expose] def q8NF : QuaternionGroup 2 → NF
  | .a i => [(0, 0, 0, 0), (3, 1, 0, 0), (2, 2, 0, 0), (1, 3, 0, 0)].getD i.val (0, 0, 0, 0)
  | .xa i => [(1, 1, 1, 0), (2, 0, 1, 0), (3, 3, 1, 0), (0, 2, 1, 0)].getD i.val (0, 0, 0, 0)

theorem q8NF_mul : ∀ u v : QuaternionGroup 2, q8NF (u * v) = nfMul (q8NF u) (q8NF v) := by
  decide +kernel

theorem q8NF_pR1 : ∀ u : QuaternionGroup 2, pR1 (q8NF u) := by decide +kernel

theorem q8NF_inj : Function.Injective q8NF := by decide +kernel

theorem q8NF_surj : ∀ p : NF, pR1 p → ∃ u : QuaternionGroup 2, q8NF u = p := by decide +kernel

theorem pR1_gen : ∀ q : NF, pR1 q → ∃ m < 4, ∃ n < 2,
    nfMul (nfPow (3, 1, 0, 0) m) (nfPow (1, 1, 1, 0) n) = q := by decide +kernel

theorem pR_sq_cases : ∀ p : NF, pR p → nfMul p p = (0, 0, 0, 0) ∨ nfMul p p = zNF := by
  decide +kernel

theorem zNF_central : ∀ q : NF, nfMul q zNF = nfMul zNF q := by decide +kernel

theorem zNF_sq : nfMul zNF zNF = (0, 0, 0, 0) := by decide +kernel

theorem pR_zNF : pR zNF := by decide +kernel

theorem card_pR : Nat.card {p : NF // pR p} = 32 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; decide +kernel

section
variable {G : Type*} [Group G] {S : Subgroup G} {a b y x : G} (h : M12Data S a b y x)

theorem inv_eq_pow3 {g : G} (hg : g ^ 4 = 1) : g⁻¹ = g ^ 3 := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ]; exact hg

theorem R1_eq : Subgroup.closure ({a⁻¹ * b, a * b * y} : Set G) = nfSub h pR1 closed_pR1 := by
  have hg1 : a⁻¹ * b = nu a b y x (3, 1, 0, 0) := by simp [nu, inv_eq_pow3 h.ha]
  have hg2 : a * b * y = nu a b y x (1, 1, 1, 0) := by simp [nu]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(3, 1, 0, 0), by decide, hg1⟩
    · exact ⟨(1, 1, 1, 0), by decide, hg2⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨m, _, n, _, hmn⟩ := pR1_gen p hp
    have : nu a b y x p = (a⁻¹ * b) ^ m * (a * b * y) ^ n := by
      rw [← hmn, ← nu_mul h, ← nu_pow h, ← nu_pow h, hg1, hg2]
    rw [this]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)

theorem R1_le_R : nfSub h pR1 closed_pR1 ≤ nfSub h pR closed_pR :=
  nfSub_le_nfSub h _ _ pR_of_pR1

theorem R1_q8 : Nonempty (↥(nfSub h pR1 closed_pR1) ≃* QuaternionGroup 2) := by
  let f : QuaternionGroup 2 →* ↥(nfSub h pR1 closed_pR1) :=
    MonoidHom.mk' (fun u => ⟨nu a b y x (q8NF u), ⟨q8NF u, q8NF_pR1 u, rfl⟩⟩) (by
      intro u v
      apply Subtype.ext
      show nu a b y x (q8NF (u * v)) = nu a b y x (q8NF u) * nu a b y x (q8NF v)
      rw [q8NF_mul, nu_mul h])
  have hbij : Function.Bijective f := by
    constructor
    · intro u v huv
      exact q8NF_inj (nu_injective h (congrArg Subtype.val huv))
    · rintro ⟨g, p, hp, rfl⟩
      obtain ⟨u, hu⟩ := q8NF_surj p hp
      exact ⟨u, Subtype.ext (by simp [f, hu])⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

theorem card_R : Nat.card (nfSub h pR closed_pR) = 32 := by
  rw [card_nfSub h]; exact card_pR

end

end CFSG.GH74.GLS.Stage1.Thm6.M12Facts
