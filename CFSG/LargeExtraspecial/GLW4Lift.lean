module

public import CFSG.LargeExtraspecial.GLW4Good
public import CFSG.LargeExtraspecial.GLRElimCent
public import CFSG.LargeExtraspecial.S3Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR
open scoped commutatorElement

section General

variable {G : Type*} [Group G] [Finite G]

theorem commutatorElement_mem_of_relIndex_le_two {H K : Subgroup G}
    (h2 : H.relIndex K ≤ 2) {a b : G} (ha : a ∈ K) (hb : b ∈ K) : ⁅a, b⁆ ∈ H := by
  have h0 : H.relIndex K ≠ 0 := by
    rw [relIndex]; exact index_ne_zero_of_finite
  rcases (show H.relIndex K = 1 ∨ H.relIndex K = 2 by omega) with h1 | h1
  · refine relIndex_eq_one.mp h1 ?_
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
  · have hidx : (H.subgroupOf K).index = 2 := h1
    have key : ⁅(⟨a, ha⟩ : K), ⟨b, hb⟩⁆ ∈ H.subgroupOf K := by
      rw [commutatorElement_def, mul_assoc, Subgroup.mul_mem_iff_of_index_two hidx,
        Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
        Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
    rw [mem_subgroupOf] at key
    simpa [commutatorElement_def] using key

omit [Finite G] in
theorem mul_self_eq_one_of_mem_closure {k : Set G} (hcomm : k.Pairwise Commute)
    (hk : ∀ x ∈ k, x * x = 1) {x : G} (hx : x ∈ closure k) : x * x = 1 := by
  have hc := Subgroup.isMulCommutative_closure hcomm
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hk x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * x * (y * y) := by rw [← hxy]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [← _root_.mul_inv_rev, ihx, inv_one]

end General

section Config

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem formOf_self_eq_zero (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hs : gram C e s = J)
    (a : C.At) : C.formOf s a a = 0 := by
  rw [formOf_eq_dot e hs]
  exact dot_J_self _

theorem fixQt_eq_clSub (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
    (hττ : τ * τ = 1) (hJ : gram C e (S.ρ ⟨τ, hτM⟩) = J) :
    S.fixQt τ = S.clSub (S.QG ⊓ centralizer {τ}) := by
  refine le_antisymm (fun v hv => ?_) (S.clSub_centralizer_le_fixQt hτM)
  set s := S.ρ ⟨τ, hτM⟩
  have hsM : s ∈ S.Mbar := Config.ρ_mem_Mbar _
  have hsX : s ∉ C.Xbar := Config.ρ_not_mem_Xbar hτM hτX
  have hfix : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    rw [S.fixQt_of_mem hτM] at hv
    exact CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hv
  obtain ⟨a, ha, b, hb, hab⟩ := C.exists_eq_add v
  have hsab : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) b + (s : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + b := by
    rw [add_comm, ← map_add, hab, hfix]
  obtain ⟨-, hb'⟩ := C.eq_of_add_eq (C.apply_mem_At_of_not_mem hsM hsX hb) ha
    (C.apply_mem_Bt_of_not_mem hsM hsX ha) hb hsab
  obtain ⟨q, hq, hqτ, hcl⟩ := Config.exists_mem_centralizer_cl_eq hτM hτX (Or.inl hττ) ha
    (formOf_self_eq_zero e hJ ⟨a, ha⟩)
  have hv' : v = S.cl q := by rw [hcl, hb', hab]
  rw [hv']
  exact S.cl_mem_clSub ⟨hq, mem_centralizer_singleton_iff.mpr hqτ.symm⟩ hq

theorem exists_lift_commutator (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M)
    (hτX : τ ∉ C.X) (hττ : τ * τ = 1) (hJ : gram C e (S.ρ ⟨τ, hτM⟩) = J) {a b : S.O}
    (ha : a ∈ S.Mbar) (hb : b ∈ S.Mbar) (haτ : a * S.ρ ⟨τ, hτM⟩ = S.ρ ⟨τ, hτM⟩ * a)
    (hbτ : b * S.ρ ⟨τ, hτM⟩ = S.ρ ⟨τ, hτM⟩ * b) :
    ∃ l : G, ∃ hl : l ∈ S.M, l * τ = τ * l ∧ S.ρ ⟨l, hl⟩ = ⁅a, b⁆ := by
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Finite.of_injective (fun f : S.Qt ≃ₗ[ZMod 2] S.Qt => (f : S.Qt → S.Qt))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  have h2 := S.lemma_3_2_index hτM (by rw [pow_two]; exact hττ) (fixQt_eq_clSub e hτM hτX hττ hJ)
  have hmem := commutatorElement_mem_of_relIndex_le_two h2 (a := a) (b := b)
    ⟨ha, mem_centralizer_singleton_iff.mpr haτ⟩ ⟨hb, mem_centralizer_singleton_iff.mpr hbτ⟩
  obtain ⟨⟨l, hlM⟩, hl, hle⟩ := hmem
  rw [SetLike.mem_coe, mem_subgroupOf] at hl
  exact ⟨l, hlM, mem_centralizer_singleton_iff.mp hl.2, hle⟩

end Config

end CFSG.LargeExtraspecial.GLW4
