module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.WeakCT CFSG.ComponentClassification.CatLeafProof
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
open scoped MatrixGroups

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

theorem weakCT_of_frame_pinned {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      (∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k) ∧
      ∀ k c, Ψ (x (sroot k) c) = ρ k (tv 0 1 c) ∧ Ψ (x (-sroot k) c) = ρ k (tv 1 0 c) := by
  classical
  have hρU : ∀ k c, ρ k (tv 0 1 c) ∈ U k ∧ ρ k (tv 1 0 c) ∈ U k := fun k c => by
    rw [← (hρ k).2]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  have hfr : SimplyLacedFrame D F adj (fun k c => ρ k (tv 0 1 c)) (fun k c => ρ k (tv 1 0 c)) := by
    refine ⟨fun i j h => ?_, fun k => ⟨ρ k, fun c => ⟨rfl, rfl⟩⟩, fun i j hne h1 h2 c d => ?_⟩
    · obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j h
      refine ⟨ψ, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
      · show ψ (tv 0 1 c) = ρ i (tv 0 1 c)
        rw [← hψ0, MonoidHom.comp_apply, blk_zero_tv01]
      · show ψ (tv 1 0 c) = ρ i (tv 1 0 c)
        rw [← hψ0, MonoidHom.comp_apply, blk_zero_tv10]
      · show ψ (tv 1 2 c) = ρ j (tv 0 1 c)
        rw [← hψ1, MonoidHom.comp_apply, blk_one_tv01]
      · show ψ (tv 2 1 c) = ρ j (tv 1 0 c)
        rw [← hψ1, MonoidHom.comp_apply, blk_one_tv10]
    · have hc := hcomm i j hne h1 h2
      exact ⟨hc _ (hρU i c).1 _ (hρU j d).1, hc _ (hρU i c).1 _ (hρU j d).2,
        hc _ (hρU i c).2 _ (hρU j d).1, hc _ (hρU i c).2 _ (hρU j d).2⟩
  have hgen' : Subgroup.closure (⋃ k, Set.range (fun c => ρ k (tv 0 1 c)) ∪
      Set.range (fun c => ρ k (tv 1 0 c))) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rw [← (hρ k).2]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl ⟨c, rfl⟩⟩)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr ⟨c, rfl⟩⟩)
  have hnt : ∃ k c, ρ k (tv 0 1 c) ≠ 1 := ⟨k₀, 1, fun h =>
    tv_zero_one_one_ne_one ((hρ k₀).1 (h.trans (map_one _).symm))⟩
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩ :=
    exists_surjective_of_simplyLacedFrame hCT hL hD hfr hgen' hnt
  refine ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ?_, fun k c => ⟨hΨu k c, hΨv k c⟩⟩
  have hk : ∀ k, sroot k ∈ D.roots ∧ -sroot k ∈ D.roots := fun k =>
    ⟨single_mem_roots k, neg_mem_roots (single_mem_roots k)⟩
  rw [CurtisTits.rankOne, Subgroup.map_sup]
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hD.surj _ (hk k).1 g hg
      rw [hΨu]
      exact (hρU k c).1
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hD.surj _ (hk k).2 g hg
      rw [hΨv]
      exact (hρU k c).2
  · rw [← (hρ k).2]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · refine Subgroup.mem_sup_left ⟨x (sroot k) c, hD.mem _ (hk k).1 c, ?_⟩
      exact hΨu k c
    · refine Subgroup.mem_sup_right ⟨x (-sroot k) c, hD.mem _ (hk k).2 c, ?_⟩
      exact hΨv k c

theorem weakCT_of_frame_subgroup_pinned {t : StatedLieTag}
    {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank) {G : Type} [Group G]
    {U : Fin D.rank → Subgroup G}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : K →* G, Ψ.ker ≤ Subgroup.center K ∧ Ψ.range = ⨆ k, U k ∧
      IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) t n p f ∧
      (∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k) ∧
      ∀ k c, Ψ (x (sroot k) c) = ρ k (tv 0 1 c) ∧ Ψ (x (-sroot k) c) = ρ k (tv 1 0 c) := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  have hρle : ∀ k, (ρ k).range ≤ Gs := fun k => (hρ k).2.le.trans (hUle k)
  have hρ' : ∀ k, Function.Injective ((ρ k).codRestrict Gs fun A => hρle k ⟨A, rfl⟩) ∧
      ((ρ k).codRestrict Gs fun A => hρle k ⟨A, rfl⟩).range = (U k).subgroupOf Gs := by
    intro k
    refine ⟨fun A B h => (hρ k).1 (congrArg Subtype.val h), ?_⟩
    ext y
    rw [Subgroup.mem_subgroupOf, ← (hρ k).2]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩
      exact ⟨A, Subtype.ext hA⟩
  obtain ⟨Ψ', hsurj, hker, hqs, -, hlie, hblk, hpin⟩ := weakCT_of_frame_pinned hCT hL hD k₀
    (X := Gs) (U := fun k => (U k).subgroupOf Gs)
    (ClassicalInvolution.Models.SymplecticPairs.iSup_subgroupOf_eq_top U)
    (fun i j hne hij hji u hu v hv => Subtype.ext (hcomm i j hne hij hji u.1 hu v.1 hv))
    (ρ := fun k => (ρ k).codRestrict Gs fun A => hρle k ⟨A, rfl⟩) hρ'
    (fun i j hij => by
      obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij
      have hle : ψ.range ≤ Gs := range_le_of_blk ψ (by rw [hψ0]; exact hρle i)
        (by rw [hψ1]; exact hρle j)
      refine ⟨ψ.codRestrict Gs fun A => hle ⟨A, rfl⟩, MonoidHom.ext fun A => Subtype.ext ?_,
        MonoidHom.ext fun A => Subtype.ext ?_⟩
      · exact DFunLike.congr_fun hψ0 A
      · exact DFunLike.congr_fun hψ1 A)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, hqs, hlie, fun k => ?_, fun k c => ?_⟩
  · intro y hy
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hy))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]
  · exact ⟨congrArg Subtype.val (hpin k c).1, congrArg Subtype.val (hpin k c).2⟩

end Recognition

section Frame

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_levi_frame_pinned [Finite F] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {r : ℕ} (ι : Fin r → Fin D.rank) {adj : Fin r → Fin r → Prop}
    (hadj : ∀ i j, adj i j → ι i ≠ ι j ∧ D.cartan (ι i) (ι j) = -1 ∧
      D.cartan (ι j) (ι i) = -1 ∧ ∃ l, ¬ (3 : ℤ) ∣ D.cartan (ι i) l + 2 * D.cartan (ι j) l)
    (hnadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i →
      ι i ≠ ι j ∧ D.cartan (ι i) (ι j) = 0 ∧ D.cartan (ι j) (ι i) = 0) :
    ∃ ρ : Fin r → SL(2, F) →* K,
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = CurtisTits.rankOne D.rootGroup (ι k)) ∧
      (∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ CurtisTits.rankOne D.rootGroup (ι i),
        ∀ v ∈ CurtisTits.rankOne D.rootGroup (ι j), u * v = v * u) ∧
      (∀ i j, adj i j → ∃ ψ : SL(3, F) →* K, ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) ∧
      ∀ k c, ρ k (tv 0 1 c) = x (sroot (ι k)) c ∧ ρ k (tv 1 0 c) = x (-sroot (ι k)) c := by
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  refine ⟨fun k => ρF (ι k), fun k => ⟨hρFi _, hρFr _⟩, fun i j hij h1 h2 => ?_,
    fun i j h => ?_, fun k c => hρFv _ c⟩
  · obtain ⟨hne, hc1, hc2⟩ := hnadj i j hij h1 h2
    exact commutes_rankOne_of_cartan_eq_zero hE hdiv hne hc1 hc2
  · obtain ⟨hne, hc1, hc2, l, hl⟩ := hadj i j h
    obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE hdiv hne hc1 hc2 hl
    exact ⟨emb, sl3_comp_blk hv (hρFv _) (hρFv _)⟩

end Frame

section Pin


theorem e6_frame_subgroup_pinned
    {p f : ℕ} [Fact p.Prime] (hadm : StatedLieAdmissible .E6 0 p f) {G : Type} [Group G]
    {U : Fin 6 → Subgroup G}
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin 6 → SL(2, GaloisField p f) →* G}
    (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin 6, edgeE 6 i j → ∃ ψ : SL(3, GaloisField p f) →* G,
      ψ.comp (blk (GaloisField p f) 0) = ρ i ∧ ψ.comp (blk (GaloisField p f) 1) = ρ j) :
    ∃ Ψ : (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →* G,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .E6 0 p f ∧
      ∀ (k : Fin 6) (c : GaloisField p f),
        Ψ (Steinberg.Minuscule.e6Data_valid.xm (GaloisField p f) (Pi.single k 1) c) =
          ρ k (tv 0 1 c) ∧
        Ψ (Steinberg.Minuscule.e6Data_valid.xm (GaloisField p f) (-Pi.single k 1) c) =
          ρ k (tv 1 0 c) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e6Datum (GaloisField p f)).isFiniteType
    (Dv := (Steinberg.Minuscule.e6Datum (GaloisField p f)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E6) (Or.inl rfl)
  obtain ⟨x', hD, hx⟩ := exists_simplyLacedLevis
    (Steinberg.Minuscule.e6_chevalleyExtras (GaloisField p f) O _
      (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC (GaloisField p f)
        Steinberg.Minuscule.posDef_cartan_E6 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e6Data_valid.commC_natAbs (GaloisField p f) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e6Datum_steinbergExtras (GaloisField p f)).torus_iSupIndep
    (fun (k : Fin 6) => by
      have h := (Steinberg.Minuscule.e6Datum_isCTGroupDatum (GaloisField p f)).sq_mem k
      have e := Steinberg.Minuscule.e6Data_valid.weylElement_xm (GaloisField p f) k 1
      rw [e]
      exact h)
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -, hpin⟩ := weakCT_of_frame_subgroup_pinned
    (CurtisTits.curtisTitsConclusion_e6 p f hadm) (leviConePresented_e6 _) hD
    (⟨0, by norm_num⟩ : Fin 6) hcomm hρ hψ
  exact ⟨Ψ, hker, hrange, hqs, hlie, fun k c =>
    ⟨(congrArg Ψ (hx k c).1.symm).trans (hpin k c).1,
      (congrArg Ψ (hx k c).2.symm).trans (hpin k c).2⟩⟩

theorem e8E6_frame_pinned (p f : ℕ) [Fact p.Prime] (hadm : StatedLieAdmissible .E6 0 p f) :
    ∃ Ψ : ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →*
        ↥(adjointGroup .E8 (GaloisField p f)),
      Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, CurtisTits.rankOne
        (adjDatum (rootOperatorFamily .E8) (GaloisField p f)).rootGroup (E8Layer.e8E6Node k) ∧
      CFSG.IsQuasisimple ↥(⨆ k, CurtisTits.rankOne
        (adjDatum (rootOperatorFamily .E8) (GaloisField p f)).rootGroup (E8Layer.e8E6Node k)) ∧
      CFSG.Blueprint.LieModel
        (↥(⨆ k, CurtisTits.rankOne (adjDatum (rootOperatorFamily .E8) (GaloisField p f)).rootGroup
          (E8Layer.e8E6Node k)) ⧸
          Subgroup.center ↥(⨆ k, CurtisTits.rankOne
            (adjDatum (rootOperatorFamily .E8) (GaloisField p f)).rootGroup
            (E8Layer.e8E6Node k))) .E6 0 p f ∧
      ∀ (k : Fin 6) (c : GaloisField p f),
        Ψ (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm (GaloisField p f) (Pi.single k 1) c) =
          e8Par (GaloisField p f) (Pi.single (E8Layer.e8E6Node k) 1) c ∧
        Ψ (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm (GaloisField p f) (-Pi.single k 1)
            c) =
          e8Par (GaloisField p f) (-Pi.single (E8Layer.e8E6Node k) 1) c := by
  obtain ⟨O, C, hE⟩ := exists_e8_chevalleyExtras (GaloisField p f)
  obtain ⟨ρ, hρ, hcomm, hψ, hpin⟩ := exists_levi_frame_pinned hE rfl E8Layer.e8E6Node
    E8Layer.e8E6_adj E8Layer.e8E6_nadj
  obtain ⟨Ψ, hker, hrange, hqs, hlie, hΨ⟩ := e6_frame_subgroup_pinned hadm hcomm hρ hψ
  exact ⟨Ψ, hker, hrange, hqs, hlie, fun k c =>
    ⟨(hΨ k c).1.trans (hpin k c).1, (hΨ k c).2.trans (hpin k c).2⟩⟩

theorem e8E6_pinned (p f : ℕ) [Fact p.Prime] (hadm : StatedLieAdmissible .E6 0 p f) :
    ∃ Ψ : ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →*
        ↥(adjointGroup .E8 (GaloisField p f)),
      Ψ.ker ≤ Subgroup.center _ ∧
      ∀ (k : Fin 6) (c : GaloisField p f),
        Ψ (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm (GaloisField p f) (Pi.single k 1) c) =
          e8Par (GaloisField p f) (Pi.single (E8Layer.e8E6Node k) 1) c ∧
        Ψ (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm (GaloisField p f) (-Pi.single k 1)
            c) =
          e8Par (GaloisField p f) (-Pi.single (E8Layer.e8E6Node k) 1) c := by
  obtain ⟨Ψ, hker, -, -, -, hΨ⟩ := e8E6_frame_pinned p f hadm
  exact ⟨Ψ, hker, hΨ⟩

end Pin

end CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw
