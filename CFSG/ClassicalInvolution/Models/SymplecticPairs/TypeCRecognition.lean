module

public import CFSG.ClassicalInvolution.WeakCT.Symplectic
public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCPairs

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open scoped MatrixGroups

section Generation

variable {K : Type} [Field K] {X : Type} [Group X]

theorem linearBlockStandardPair_le_sup {W U V : Subgroup X}
    (h : LinearBlockStandardPair K W U V) : W ≤ U ⊔ V := by
  obtain ⟨θ, c, hrange, -, hcases⟩ := h
  have hB : (B12 K).map (MulAut.conj c⁻¹).toMonoidHom ⊔ (B23 K).map (MulAut.conj c⁻¹).toMonoidHom =
      ⊤ := by
    rw [← Subgroup.map_sup, WeakCT.B12_sup_B23]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  have hW : W = ((B12 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ ⊔
      ((B23 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    rw [← hrange, MonoidHom.range_eq_map, ← hB, Subgroup.map_sup]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hW, h1, h2]
  · rw [hW, h1, h2, sup_comm]

theorem suppGroup_coords_zero_union_one :
    suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)) = (⊤ : Subgroup (StatedSp 2 K)) := by
  rw [eq_top_iff]
  intro x _
  rw [mem_suppGroup]
  intro r t hrt
  exfalso
  apply hrt
  have hmem : ∀ a : Fin 2 ⊕ Fin 2, a ∈ coords (0 : Fin 2) ∪ coords (1 : Fin 2) := by
    intro a
    rcases a with a | a <;> fin_cases a <;> simp [coords]
  exact ⟨hmem r, hmem t⟩

theorem symplecticBlockStandardPair_le_sup {W U V : Subgroup X}
    (h : SymplecticBlockStandardPair K W U V) : W ≤ U ⊔ V := by
  obtain ⟨θ, c, hrange, -, -, -, hU, hV⟩ := h
  have h01 : (0 : Fin 2) ≠ 1 := zero_ne_one
  have htop : (longBlock K 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (shortBlock K h01).range.map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, sup_comm, shortBlock_sup_longBlock_eq_suppGroup h01,
      suppGroup_coords_zero_union_one]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  rw [← hrange, MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, hU, hV]

end Generation

section Chain

theorem iSup_subgroupOf_eq_top {G : Type*} [Group G] {ι : Type*} (U : ι → Subgroup G) :
    ⨆ i, (U i).subgroupOf (⨆ i, U i) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.iSup_induction' with
  | hp i x hx => exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_subgroupOf).mpr hx)
  | h1 => exact one_mem _
  | hmul x y hx hy hx' hy' => exact mul_mem hx' hy'

theorem weakCT_symplectic_subgroup {n p f : ℕ} (hadm : StatedLieAdmissible .PSp n p f)
    (hn : 3 ≤ n) (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ Nat.card F) {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* G, Ψ.ker ≤ Subgroup.center (StatedSp n F) ∧
      Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .PSp n p f ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup k).map Ψ = U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, hqs, -, hlie, hblk⟩ := WeakCT.weakCT_symplectic hadm hn hp2 hF hq
    (U := fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hij hj => by
      obtain ⟨W, hW⟩ := hpair i j hij hj
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (fun i j hi hj => by
      obtain ⟨W, hW⟩ := hsp i j hi hj
      exact ⟨W.subgroupOf Gs, symplecticBlockStandardPair_subgroupOf
        ((symplecticBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, hqs, hlie, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro k
    rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]

end Chain

end CFSG.ClassicalInvolution.Models.SymplecticPairs
