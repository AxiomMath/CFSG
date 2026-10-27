module

public import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameDL

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Blocks

variable {F : Type} [Field F]

theorem range_le_of_blk {G : Type*} [Group G] (ψ : SL(3, F) →* G) {T : Subgroup G}
    (h0 : (ψ.comp (blk F 0)).range ≤ T) (h1 : (ψ.comp (blk F 1)).range ≤ T) : ψ.range ≤ T := by
  have htop : (blk F 0).range ⊔ (blk F 1).range = ⊤ := B12_sup_B23 (K := F)
  rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, ← MonoidHom.range_comp,
    ← MonoidHom.range_comp]
  exact sup_le h0 h1

theorem range_le_of_spBlock {G : Type*} [Group G] (ψ : StatedSp 2 F →* G) {T : Subgroup G}
    (h0 : (ψ.comp (spBlock F 0)).range ≤ T) (h1 : (ψ.comp (spBlock F 1)).range ≤ T) :
    ψ.range ≤ T := by
  have htop : (spBlock F 0).range ⊔ (spBlock F 1).range = ⊤ := by
    rw [spBlock_zero_eq_shortBlock, spBlock_one_eq_longBlock,
      ClassicalInvolution.Models.SymplecticPairs.shortBlock_sup_longBlock_eq_suppGroup,
      ClassicalInvolution.Models.SymplecticPairs.suppGroup_coords_zero_union_one]
  rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, ← MonoidHom.range_comp,
    ← MonoidHom.range_comp]
  exact sup_le h0 h1

theorem sl3_comp_blk {G : Type*} [Group G] {ψ : SL(3, F) →* G} {ρi ρj : SL(2, F) →* G}
    {u v u' v' : F → G}
    (hψ : ∀ c, ψ (tv 0 1 c) = u c ∧ ψ (tv 1 0 c) = v c ∧ ψ (tv 1 2 c) = u' c ∧
      ψ (tv 2 1 c) = v' c)
    (hi : ∀ c, ρi (tv 0 1 c) = u c ∧ ρi (tv 1 0 c) = v c)
    (hj : ∀ c, ρj (tv 0 1 c) = u' c ∧ ρj (tv 1 0 c) = v' c) :
    ψ.comp (blk F 0) = ρi ∧ ψ.comp (blk F 1) = ρj := by
  refine ⟨hom_ext_sl2 (fun c => ?_) (fun c => ?_), hom_ext_sl2 (fun c => ?_) (fun c => ?_)⟩
  · rw [MonoidHom.comp_apply, blk_zero_tv01, (hψ c).1, (hi c).1]
  · rw [MonoidHom.comp_apply, blk_zero_tv10, (hψ c).2.1, (hi c).2]
  · rw [MonoidHom.comp_apply, blk_one_tv01, (hψ c).2.2.1, (hj c).1]
  · rw [MonoidHom.comp_apply, blk_one_tv10, (hψ c).2.2.2, (hj c).2]

end Blocks

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem weakCT_of_frame_dl_subgroup [Finite F] {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hq : IsQuasisimple (StatedSp 2 F)) (h2 : (2 : F) ≠ 0)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {G : Type} [Group G] {U : Fin D.rank → Subgroup G}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* G} (hρ : ∀ k, (ρ k).range = U k)
    (hρa : Function.Injective (ρ a))
    (hψ : ∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j)
    (hψ4 : ∃ ψ : StatedSp 2 F →* G, ψ.comp (spBlock F 1) = ρ a ∧ ψ.comp (spBlock F 0) = ρ b) :
    ∃ Ψ : K →* G, Ψ.ker ≤ Subgroup.center K ∧ Ψ.range = ⨆ k, U k ∧
      IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  have hρle : ∀ k, (ρ k).range ≤ Gs := fun k => (hρ k).le.trans (hUle k)
  have hρ' : ∀ k, ((ρ k).codRestrict Gs fun A => hρle k ⟨A, rfl⟩).range = (U k).subgroupOf Gs := by
    intro k
    ext y
    rw [Subgroup.mem_subgroupOf, ← hρ k]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩
      exact ⟨A, Subtype.ext hA⟩
  obtain ⟨Ψ', hsurj, hker, hqs, -, hlie, hblk⟩ := weakCT_of_frame_dl_of_isQuasisimple hCT hL hE
    hdiv hq h2 hdiag hind hsq (X := Gs) (U := fun k => (U k).subgroupOf Gs)
    (ClassicalInvolution.Models.SymplecticPairs.iSup_subgroupOf_eq_top U)
    (fun i j hne hij hji u hu v hv => Subtype.ext (hcomm i j hne hij hji u.1 hu v.1 hv))
    (ρ := fun k => (ρ k).codRestrict Gs fun A => hρle k ⟨A, rfl⟩) hρ'
    (fun A B h => hρa (congrArg Subtype.val h))
    (fun i j hij hne => by
      obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij hne
      have hle : ψ.range ≤ Gs := range_le_of_blk ψ (by rw [hψ0]; exact hρle i)
        (by rw [hψ1]; exact hρle j)
      refine ⟨ψ.codRestrict Gs fun A => hle ⟨A, rfl⟩, MonoidHom.ext fun A => Subtype.ext ?_,
        MonoidHom.ext fun A => Subtype.ext ?_⟩
      · exact DFunLike.congr_fun hψ0 A
      · exact DFunLike.congr_fun hψ1 A)
    (by
      obtain ⟨ψ, hψ1, hψ0⟩ := hψ4
      have hle : ψ.range ≤ Gs := range_le_of_spBlock ψ (by rw [hψ0]; exact hρle b)
        (by rw [hψ1]; exact hρle a)
      refine ⟨ψ.codRestrict Gs fun A => hle ⟨A, rfl⟩, MonoidHom.ext fun A => Subtype.ext ?_,
        MonoidHom.ext fun A => Subtype.ext ?_⟩
      · exact DFunLike.congr_fun hψ1 A
      · exact DFunLike.congr_fun hψ0 A)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, hqs, hlie, fun k => ?_⟩
  · intro y hy
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hy))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]

theorem exists_rankOne_param (hE : Steinberg.ChevalleyExtras D F x C O) (i : Fin D.rank) :
    ∃ ρ : SL(2, F) →* K, Function.Injective ρ ∧ ρ.range = CurtisTits.rankOne D.rootGroup i ∧
      ∀ c, ρ (tv 0 1 c) = x (sroot i) c ∧ ρ (tv 1 0 c) = x (-sroot i) c := by
  obtain ⟨ρ, hρ, hup, hlow⟩ := hE.rankOne i
  have h1 : ∀ c, ρ (tv 0 1 c) = x (sroot i) c := fun c => by rw [tv01_eq_sl2Upper, hup]
  have h2 : ∀ c, ρ (tv 1 0 c) = x (-sroot i) c := fun c => by rw [tv10_eq_sl2Lower, hlow]
  have hs : sroot i ∈ D.roots := single_mem_roots i
  have hn : -sroot i ∈ D.roots := neg_mem_roots hs
  refine ⟨ρ, hρ, (rankOne_eq_range_of_param ρ (fun c => ?_) (fun c => ?_) (fun g hg => ?_)
    (fun g hg => ?_)).symm, fun c => ⟨h1 c, h2 c⟩⟩
  · rw [h1]
    exact ((hE.param _ hs).1 _).2 ⟨c, rfl⟩
  · rw [h2]
    exact ((hE.param _ hn).1 _).2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := ((hE.param _ hs).1 g).1 hg
    exact ⟨c, h1 c⟩
  · obtain ⟨c, rfl⟩ := ((hE.param _ hn).1 g).1 hg
    exact ⟨c, h2 c⟩

end Recognition

end CFSG.ComponentClassification.CatLeafProof
