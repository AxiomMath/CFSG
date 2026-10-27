module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameDLSubgroup

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

section Frame

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem commutes_rankOne_of_cartan_eq_zero (hE : Steinberg.ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {i j : Fin D.rank} (hij : i ≠ j) (hcij : D.cartan i j = 0)
    (hcji : D.cartan j i = 0) :
    Commutes (CurtisTits.rankOne D.rootGroup i) (CurtisTits.rankOne D.rootGroup j) := by
  have hpar : ∀ γ ∈ D.roots, ∀ g ∈ D.rootGroup γ, ∃ c, x γ c = g := fun γ hγ g hg =>
    ((hE.param γ hγ).1 g).1 hg
  have hsi : sroot i ∈ D.roots := single_mem_roots i
  have hsj : sroot j ∈ D.roots := single_mem_roots j
  have hni : -sroot i ∈ D.roots := neg_mem_roots hsi
  have hnj : -sroot j ∈ D.roots := neg_mem_roots hsj
  change Commutes (D.rootGroup (sroot i) ⊔ D.rootGroup (-sroot i))
    (D.rootGroup (sroot j) ⊔ D.rootGroup (-sroot j))
  rw [ClassicalInvolution.RouteD.commutes_sup_left, ClassicalInvolution.RouteD.commutes_sup_right,
    ClassicalInvolution.RouteD.commutes_sup_right]
  refine ⟨⟨fun a ha b hb => ?_, fun a ha b hb => ?_⟩, fun a ha b hb => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨s, rfl⟩ := hpar _ hsi a ha
    obtain ⟨t, rfl⟩ := hpar _ hsj b hb
    exact (commute_nonadj hE hdiv hij hcij hcji s t).1.eq
  · obtain ⟨s, rfl⟩ := hpar _ hsi a ha
    obtain ⟨t, rfl⟩ := hpar _ hnj b hb
    exact (commute_nonadj hE hdiv hij hcij hcji s t).2.1.eq
  · obtain ⟨s, rfl⟩ := hpar _ hni a ha
    obtain ⟨t, rfl⟩ := hpar _ hsj b hb
    exact (commute_nonadj hE hdiv hij hcij hcji s t).2.2.1.eq
  · obtain ⟨s, rfl⟩ := hpar _ hni a ha
    obtain ⟨t, rfl⟩ := hpar _ hnj b hb
    exact (commute_nonadj hE hdiv hij hcij hcji s t).2.2.2.eq

theorem exists_levi_frame [Finite F] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {r : ℕ} (ι : Fin r → Fin D.rank) {adj : Fin r → Fin r → Prop}
    (hadj : ∀ i j, adj i j → ι i ≠ ι j ∧ D.cartan (ι i) (ι j) = -1 ∧
      D.cartan (ι j) (ι i) = -1 ∧ ∃ l, ¬ (3 : ℤ) ∣ D.cartan (ι i) l + 2 * D.cartan (ι j) l)
    (hnadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i →
      ι i ≠ ι j ∧ D.cartan (ι i) (ι j) = 0 ∧ D.cartan (ι j) (ι i) = 0) :
    ∃ ρ : Fin r → SL(2, F) →* K,
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = CurtisTits.rankOne D.rootGroup (ι k)) ∧
      (∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ CurtisTits.rankOne D.rootGroup (ι i),
        ∀ v ∈ CurtisTits.rankOne D.rootGroup (ι j), u * v = v * u) ∧
      ∀ i j, adj i j → ∃ ψ : SL(3, F) →* K, ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j := by
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  refine ⟨fun k => ρF (ι k), fun k => ⟨hρFi _, hρFr _⟩, fun i j hij h1 h2 => ?_,
    fun i j h => ?_⟩
  · obtain ⟨hne, hc1, hc2⟩ := hnadj i j hij h1 h2
    exact commutes_rankOne_of_cartan_eq_zero hE hdiv hne hc1 hc2
  · obtain ⟨hne, hc1, hc2, l, hl⟩ := hadj i j h
    obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE hdiv hne hc1 hc2 hl
    exact ⟨emb, sl3_comp_blk hv (hρFv _) (hρFv _)⟩

end Frame

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

theorem weakCT_of_frame_subgroup {F₀ : Type} [Field F₀] (e : F₀ ≃+* F) {t : StatedLieTag}
    {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank) {G : Type} [Group G]
    {U : Fin D.rank → Subgroup G}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F₀) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F₀) →* G,
      ψ.comp (blk F₀ 0) = ρ i ∧ ψ.comp (blk F₀ 1) = ρ j) :
    ∃ Ψ : K →* G, Ψ.ker ≤ Subgroup.center K ∧ Ψ.range = ⨆ k, U k ∧
      IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  let φ₂ : SL(2, F) →* SL(2, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let φ₃ : SL(3, F) →* SL(3, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rwa [map_symm_map, map_symm_map] at this
  have hφ₂surj : ∀ A : SL(2, F₀), ∃ B : SL(2, F), φ₂ B = A := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.toRingHom A, map_map_symm e A⟩
  have hφ₃ : ∀ (s : Fin 2) (A : SL(2, F)), φ₃ (blk F s A) = blk F₀ s (φ₂ A) := fun s A =>
    map_blk e.symm.toRingHom s A
  have hr : ∀ k, ((ρ k).comp φ₂).range = U k := fun k => by
    rw [← (hρ k).2]
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨φ₂ B, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  have hρle : ∀ k, ((ρ k).comp φ₂).range ≤ Gs := fun k => (hr k).le.trans (hUle k)
  have hρ' : ∀ k, Function.Injective (((ρ k).comp φ₂).codRestrict Gs fun A => hρle k ⟨A, rfl⟩) ∧
      (((ρ k).comp φ₂).codRestrict Gs fun A => hρle k ⟨A, rfl⟩).range = (U k).subgroupOf Gs := by
    intro k
    refine ⟨fun A B h => ((hρ k).1.comp hφ₂inj) (congrArg Subtype.val h), ?_⟩
    ext y
    rw [Subgroup.mem_subgroupOf, ← hr k]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩
      exact ⟨A, Subtype.ext hA⟩
  obtain ⟨Ψ', hsurj, hker, hqs, -, hlie, hblk⟩ := weakCT_of_frame hCT hL hD k₀ (X := Gs)
    (U := fun k => (U k).subgroupOf Gs)
    (ClassicalInvolution.Models.SymplecticPairs.iSup_subgroupOf_eq_top U)
    (fun i j hne hij hji u hu v hv => Subtype.ext (hcomm i j hne hij hji u.1 hu v.1 hv))
    (ρ := fun k => ((ρ k).comp φ₂).codRestrict Gs fun A => hρle k ⟨A, rfl⟩) hρ'
    (fun i j hij => by
      obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij
      have hle : (ψ.comp φ₃).range ≤ Gs := by
        rw [MonoidHom.range_comp]
        refine (Subgroup.map_le_range ψ _).trans (range_le_of_blk ψ ?_ ?_)
        · rw [hψ0]
          exact (hρ i).2.le.trans (hUle i)
        · rw [hψ1]
          exact (hρ j).2.le.trans (hUle j)
      refine ⟨(ψ.comp φ₃).codRestrict Gs fun A => hle ⟨A, rfl⟩,
        MonoidHom.ext fun A => Subtype.ext ?_, MonoidHom.ext fun A => Subtype.ext ?_⟩
      · show ψ (φ₃ (blk F 0 A)) = ρ i (φ₂ A)
        rw [hφ₃, ← hψ0, MonoidHom.comp_apply]
      · show ψ (φ₃ (blk F 1 A)) = ρ j (φ₂ A)
        rw [hφ₃, ← hψ1, MonoidHom.comp_apply])
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, hqs, hlie, fun k => ?_⟩
  · intro y hy
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hy))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]

end Recognition

end CFSG.ComponentClassification.CatLeafProof
