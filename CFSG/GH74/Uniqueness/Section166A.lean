module

public import CFSG.GH74.Uniqueness.Section166Basic
public import CFSG.GH74.Uniqueness.Section166Aut

public section

namespace CFSG.GH74.Uniqueness.Cor166

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem mem_T_of_mem_T1
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h165 : Prop165Stmt Z M)
    {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) {v : X} (hvT1 : v ∈ c.T1) (hv : v * v = 1) :
    v ∈ c.T := by
  refine Subgroup.mem_inf.mpr ⟨hvT1, ?_⟩
  by_cases hv1 : v = 1
  · rw [hv1]
    exact one_mem _
  by_cases hvu : v = c.u
  · rw [hvu]
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨u_mem_B c, u_mem_J c⟩)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv) hv1
  have hvB : v ∈ c.B := T1_le_B c hvT1
  have hvM : v ∈ M := T1_le_M c hvT1
  let g : ↥(normalizer (c.B0 : Set X)) := ⟨v, B_le_normalizer c S hvB⟩
  obtain ⟨y, hy⟩ := benderSub_exists_inner_of_fixed_le (g := g) S.invariant hB hv
    (fun x hxv => mem_M_of_comm S c h165 hv2 hvu hvM hvB x.2 hxv)
  have hyB : (y : X) ∈ c.B := B0_le_B c y.2
  have hjB : (y : X)⁻¹ * v ∈ c.B := c.B.mul_mem (c.B.inv_mem hyB) hvB
  have hv' : v = (y : X) * ((y : X)⁻¹ * v) := by group
  rw [hv']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left y.2)
    (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hjB, hy⟩))

theorem cor166a
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h164 : Lemma164Stmt Z M)
    (h165 : Prop165Stmt Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) :
    c.Q ⊔ zpowers c.u = omegaOneSub c.T1 := by
  obtain ⟨-, ⟨-, -, h3⟩, -⟩ := h164 c n i e hB
  rw [h3]
  apply le_antisymm
  · exact Subgroup.closure_mono fun x hx => ⟨(Subgroup.mem_inf.mp hx.1).1, hx.2⟩
  · rw [omegaOneSub, Subgroup.closure_le]
    rintro x ⟨hx, hx2⟩
    exact Subgroup.subset_closure ⟨mem_T_of_mem_T1 S c h165 hB hx hx2, hx2⟩

theorem mem_or_mul_mem_Q
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h164 : Lemma164Stmt Z M)
    (h165 : Prop165Stmt Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) {v : X}
    (hvT1 : v ∈ c.T1) (hv : v * v = 1) : v ∈ c.Q ∨ v * c.u ∈ c.Q := by
  have hmem : v ∈ c.Q ⊔ zpowers c.u := by
    rw [cor166a S c h164 h165 hB]
    exact Subgroup.subset_closure ⟨hvT1, hv⟩
  exact mem_or_mul_mem_of_mem_sup (u_mul_self c)
    (fun q hq => comm_u_of_mem_B c (B0_le_B c (Q_le_B0 c hq))) hmem

end CFSG.GH74.Uniqueness.Cor166
