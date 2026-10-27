module

public import CFSG.ClassicalInvolution.Q3.Q3VCtMain
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (blk spBlock B12_sup_B23 spBlock_zero_eq_shortBlock
  spBlock_one_eq_longBlock)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (shortBlock_sup_longBlock_eq_top
  iSup_subgroupOf_eq_top)
open scoped MatrixGroups

section Generation

variable {F : Type} [Field F] {G : Type} [Group G]

theorem range_eq_sup_of_blocks {ρ₀ ρ₁ : SL(2, F) →* G} {ψ : SL(3, F) →* G}
    (h0 : ψ.comp (blk F 0) = ρ₀) (h1 : ψ.comp (blk F 1) = ρ₁) :
    ψ.range = ρ₀.range ⊔ ρ₁.range := by
  rw [← h0, ← h1, MonoidHom.range_comp, MonoidHom.range_comp, ← Subgroup.map_sup,
    show (blk F 0).range ⊔ (blk F 1).range = ⊤ from B12_sup_B23, ← MonoidHom.range_eq_map]

theorem range_eq_sup_of_spBlocks {ρs ρl : SL(2, F) →* G} {ψ : StatedSp 2 F →* G}
    (hs : ψ.comp (spBlock F 0) = ρs) (hl : ψ.comp (spBlock F 1) = ρl) :
    ψ.range = ρs.range ⊔ ρl.range := by
  rw [← hs, ← hl, MonoidHom.range_comp, MonoidHom.range_comp, ← Subgroup.map_sup,
    spBlock_zero_eq_shortBlock, spBlock_one_eq_longBlock, shortBlock_sup_longBlock_eq_top,
    ← MonoidHom.range_eq_map]

end Generation

section Subgroup

theorem weakCT_symplectic_subgroup_of_family {n p f : ℕ}
    (hadm : StatedLieAdmissible .PSp n p f) (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (ρ : Fin n → SL(2, F) →* G) (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (ψ : ∀ i : Fin n, i.val + 2 < n → SL(3, F) →* G)
    (hψ0 : ∀ (i : Fin n) (h : i.val + 2 < n),
      (ψ i h).comp (blk F 0) = ρ ⟨i.val + 1, by omega⟩)
    (hψ1 : ∀ (i : Fin n) (h : i.val + 2 < n), (ψ i h).comp (blk F 1) = ρ i)
    (ψ4 : StatedSp 2 F →* G)
    (hψ4l : ψ4.comp (spBlock F 1) = ρ ⟨n - 1, by omega⟩)
    (hψ4s : ψ4.comp (spBlock F 0) = ρ ⟨n - 2, by omega⟩) :
    ∃ Ψ : StatedSp n F →* G, Ψ.ker ≤ Subgroup.center (StatedSp n F) ∧
      Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .PSp n p f ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup k).map Ψ = U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  have hρR : ∀ k, (ρ k).range ≤ Gs := fun k => (hρ k).2 ▸ hUle k
  have hρle : ∀ k A, ρ k A ∈ Gs := fun k A => hρR k ⟨A, rfl⟩
  have hψR : ∀ (i : Fin n) (h : i.val + 2 < n), (ψ i h).range ≤ Gs := fun i h => by
    rw [range_eq_sup_of_blocks (hψ0 i h) (hψ1 i h)]
    exact sup_le (hρR _) (hρR _)
  have hψ4R : ψ4.range ≤ Gs := by
    rw [range_eq_sup_of_spBlocks hψ4s hψ4l]
    exact sup_le (hρR _) (hρR _)
  obtain ⟨Ψ', hsurj, hker, hqs, -, hlie, hblk⟩ := weakCT_symplectic_of_family hadm hn hF
    (fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun k => (ρ k).codRestrict Gs (hρle k))
    (fun k => ⟨fun _ _ h => (hρ k).1 (congrArg Subtype.val h), by
      rw [← (hρ k).2]
      exact (MonoidHom.subgroupOf_range_eq_of_le (ρ k) (hρR k)).symm⟩)
    (fun i h => (ψ i h).codRestrict Gs fun A => hψR i h ⟨A, rfl⟩)
    (fun i h => MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun (hψ0 i h) A))
    (fun i h => MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun (hψ1 i h) A))
    (ψ4.codRestrict Gs fun A => hψ4R ⟨A, rfl⟩)
    (MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun hψ4l A))
    (MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun hψ4s A))
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, hqs, hlie, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro k
    rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]

end Subgroup

end CFSG.ClassicalInvolution.Q3.Q3V
