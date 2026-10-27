module

public import CFSG.Quasithin.Background.Module
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (fixV IsFFStarOffender)

theorem normal_of_isSubnormal_of_centralizer_eq_bot {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hs : IsSimpleGroup ↥H) (hC : Subgroup.centralizer (H : Set G) = ⊥)
    (hH : H.IsSubnormal) : H.Normal := by
  classical
  let _ : IsSimpleGroup ↥H := hs
  have hnt : Nontrivial ↥H := hs.toNontrivial
  have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hle : H ≤ Subgroup.centralizer (H : Set G) := by
      intro x hx y hy
      exact congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩).symm
    rw [hC, le_bot_iff] at hle
    exact (Subgroup.nontrivial_iff_ne_bot H).mp hnt hle
  obtain ⟨hQ, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  have hcomp : IsComponent H := ⟨hQ, hH⟩
  have hconj : ∀ g : G,
      IsComponent (H.map (MulAut.conj g).toMonoidHom) := fun g =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hcomp
  have hfix : ∀ g : G, H.map (MulAut.conj g).toMonoidHom = H := by
    intro g
    rcases CFSG.LocalCores.distinct_components_commute hcomp (hconj g) with h | h
    · exact h.symm
    · exfalso
      have hle : H.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (H : Set G) := by
        rw [Subgroup.commutator_comm] at h
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      rw [hC] at hle
      obtain ⟨x, hx1⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.nontrivial_iff_ne_bot H).mp hnt)
      have hxbot : (MulAut.conj g) (x : G) = 1 := by
        have := hle (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom x.2)
        simpa using this
      exact hx1 (Subtype.ext ((MulAut.conj g).injective (by simpa using hxbot)))
  refine Subgroup.Normal.mk fun x hx g => ?_
  have h1 : (MulAut.conj g) x ∈ H := by
    rw [← hfix g]
    exact Subgroup.mem_map_of_mem _ hx
  simpa [MulAut.conj_apply] using h1

section Restrict

variable {W : Type} [CommGroup W] [Finite W]

theorem card_le_index_mul_card_fixV {Y A : Subgroup (MulAut W)} (hA : IsFFStarOffender Y A)
    (U : Subgroup W) :
    Nat.card U ≤ (A ⊓ fixingSubgroup (MulAut W) (U : Set W)).relIndex A *
      Nat.card ↥(U ⊓ fixV A) := by
  set B := A ⊓ fixingSubgroup (MulAut W) (U : Set W) with hBdef
  set C := fixV A with hCdef
  have hBA : B ≤ A := inf_le_left
  have hUC : U ⊔ C ≤ fixV B := by
    refine sup_le (fun u hu b hb => ?_) (fun c hc b hb => hc b (hBA hb))
    have hfix := (mem_fixingSubgroup_iff (MulAut W)).mp (Subgroup.mem_inf.mp hb).2 u hu
    simpa [MulAut.smul_def] using hfix
  have hsup : C.relIndex (U ⊔ C) * Nat.card C = Nat.card ↥(U ⊔ C) := by
    have h := Subgroup.relIndex_mul_card C (U ⊔ C)
    rwa [inf_eq_left.mpr (le_sup_right : C ≤ U ⊔ C)] at h
  have hU : C.relIndex U * Nat.card ↥(U ⊓ C) = Nat.card U := by
    rw [inf_comm]
    exact Subgroup.relIndex_mul_card C U
  rw [Subgroup.relIndex_sup_right] at hsup
  have hAcard : B.relIndex A * Nat.card B = Nat.card A := by
    have h := Subgroup.relIndex_mul_card B A
    rwa [inf_eq_left.mpr hBA] at h
  have hoff : Nat.card B * Nat.card (fixV B) ≤ Nat.card A * Nat.card C := hA.2.2.2 B hBA
  have hle : Nat.card ↥(U ⊔ C) ≤ Nat.card (fixV B) := Subgroup.card_le_of_le hUC
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hr : C.relIndex U ≤ B.relIndex A := by
    have h1 : C.relIndex U * Nat.card C * Nat.card B ≤ B.relIndex A * Nat.card B * Nat.card C := by
      calc C.relIndex U * Nat.card C * Nat.card B = Nat.card ↥(U ⊔ C) * Nat.card B := by
            rw [hsup]
        _ ≤ Nat.card (fixV B) * Nat.card B := Nat.mul_le_mul_right _ hle
        _ = Nat.card B * Nat.card (fixV B) := mul_comm _ _
        _ ≤ Nat.card A * Nat.card C := hoff
        _ = B.relIndex A * Nat.card B * Nat.card C := by rw [hAcard]
    have h2 : C.relIndex U * (Nat.card C * Nat.card B) ≤
        B.relIndex A * (Nat.card C * Nat.card B) := by
      calc C.relIndex U * (Nat.card C * Nat.card B) = C.relIndex U * Nat.card C * Nat.card B :=
            (mul_assoc _ _ _).symm
        _ ≤ B.relIndex A * Nat.card B * Nat.card C := h1
        _ = B.relIndex A * (Nat.card C * Nat.card B) := by ring
    exact Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hCpos hBpos)
  calc Nat.card U = C.relIndex U * Nat.card ↥(U ⊓ C) := hU.symm
    _ ≤ B.relIndex A * Nat.card ↥(U ⊓ C) := Nat.mul_le_mul_right _ hr

end Restrict

theorem exists_mem_commutator_ne_bot_of_sSup {G : Type*} [Group G] {L : Subgroup G}
    {𝒮 : Set (Subgroup G)} (h : ⁅L, sSup 𝒮⁆ ≠ ⊥) : ∃ A ∈ 𝒮, ⁅L, A⁆ ≠ ⊥ := by
  by_contra hne
  push Not at hne
  apply h
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine sSup_le fun A hA => ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hne A hA

end CFSG.GroupTheory

end
