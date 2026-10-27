module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Two
public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameToral
public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinSingular
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8SylowSeven
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond
public import CFSG.ClassicalInvolution.RouteD.GapsFrMain

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

section S12
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups


theorem exists_e8D8_family_param (K : Type) [Field K] [Finite K] :
    ∃ ρ : Fin 8 → SL(2, K) →* adjointGroup .E8 K,
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = e8D8Chain K k) ∧
      (∀ i j : Fin 8, i ≠ j → ¬ edgeD 8 i j → ¬ edgeD 8 j i →
        ∀ u ∈ e8D8Chain K i, ∀ v ∈ e8D8Chain K j, u * v = v * u) ∧
      (∀ i j : Fin 8, edgeD 8 i j → ∃ ψ : SL(3, K) →* adjointGroup .E8 K,
        ψ.comp (ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
          ψ.comp (ClassicalInvolution.WeakCT.blk K 1) = ρ j) ∧
      ∀ k : Fin 8, k ≠ 0 → ∀ c, ρ k (tv 0 1 c) = e8Par K (Pi.single (e8D8Node k) 1) c ∧
        ρ k (tv 1 0 c) = e8Par K (-Pi.single (e8D8Node k) 1) c := by
  obtain ⟨O, C, hE⟩ := exists_e8_chevalleyExtras K
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  set n := weylWordElt .E8 K e8D8Word with hn
  let ρ : Fin 8 → SL(2, K) →* adjointGroup .E8 K := fun k =>
    if k = 0 then (MulAut.conj n).toMonoidHom.comp (ρF (e8Node 6)) else ρF (e8D8Node k)
  have hρ0 : ρ 0 = (MulAut.conj n).toMonoidHom.comp (ρF (e8Node 6)) := by simp [ρ]
  have hρk : ∀ k, k ≠ 0 → ρ k = ρF (e8D8Node k) := fun k hk => by simp [ρ, hk]
  have hU0 : e8D8Chain K 0 =
      (e8Datum K).rootGroup e8D8Root ⊔ (e8Datum K).rootGroup (-e8D8Root) := by
    simp [e8D8Chain]
  have hUk : ∀ k, k ≠ 0 → e8D8Chain K k = rankOne (e8Datum K).rootGroup (e8D8Node k) :=
    fun k hk => by simp [e8D8Chain, hk]
  have hr0 : (ρ 0).range = e8D8Chain K 0 := by
    rw [hρ0, hU0, MonoidHom.range_comp, hρFr]
    change ((e8Datum K).rootGroup (Pi.single (e8Node 6) 1) ⊔
      (e8Datum K).rootGroup (-Pi.single (e8Node 6) 1)).map _ = _
    rw [map_conj_weylWordElt_rootPair e8D8Word (isRoot_single _ _), wordReflect_e8D8Word]
  have hρ' : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = e8D8Chain K k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      refine ⟨?_, hr0⟩
      rw [hρ0]
      exact (MulAut.conj n).injective.comp (hρFi _)
    · rw [hρk k hk, hUk k hk]
      exact ⟨hρFi _, hρFr _⟩
  have h0 : ∀ j : Fin 8, j ≠ 0 → j ≠ 1 → Commutes (e8D8Chain K 0) (e8D8Chain K j) := by
    intro j hj0 hj1
    rw [hU0, hUk j hj0]
    obtain ⟨h1, h2, h3, h4, h5⟩ := e8D8_root_orth j hj0 hj1
    exact commutes_rootPair_of_noG2 noG2_E8 isRoot_e8D8Root (isRoot_single _ _) h1 h2 h3 h4 h5
  have hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeD 8 i j → ¬ edgeD 8 j i →
      ∀ u ∈ e8D8Chain K i, ∀ v ∈ e8D8Chain K j, u * v = v * u := by
    intro i j hij h1 h2 u hu v hv
    by_cases hi : i = 0
    · subst hi
      exact h0 j (fun h => hij h.symm) (e8D8_ne_one_of_nadj j h1) u hu v hv
    · by_cases hj : j = 0
      · subst hj
        exact (h0 i hi (e8D8_ne_one_of_nadj i h2) v hv u hu).symm
      · rw [hUk i hi] at hu
        rw [hUk j hj] at hv
        obtain ⟨hne, hc1, hc2⟩ := e8D8_nadj i j hij h1 h2 hi hj
        exact commutes_rankOne_of_cartan_eq_zero hE rfl hne hc1 hc2 u hu v hv
  have hψ : ∀ i j : Fin 8, edgeD 8 i j → ∃ ψ : SL(3, K) →* adjointGroup .E8 K,
      ψ.comp (ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
        ψ.comp (ClassicalInvolution.WeakCT.blk K 1) = ρ j := by
    intro i j hij
    have hj0 : j ≠ 0 := fun h => e8D8_not_edge_to_zero i (h ▸ hij)
    by_cases hi : i = 0
    · subst hi
      obtain rfl := e8D8_edge_zero j hij
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (k := e8Node 5) e8Node_six_ne_seven
        e8_cartan_67 e8_cartan_76 e8_sl3_witness_67
      obtain ⟨h0', h1'⟩ := sl3_comp_blk hv (hρFv (e8Node 6)) (hρFv (e8Node 7))
      refine ⟨(MulAut.conj n).toMonoidHom.comp emb, ?_, ?_⟩
      · rw [hρ0, MonoidHom.comp_assoc, h0']
      · rw [hρk 1 (by decide), MonoidHom.comp_assoc, h1']
        refine MonoidHom.ext fun A => ?_
        have hA : ρF (e8Node 7) A ∈ rankOne (e8Datum K).rootGroup (e8Node 7) := by
          rw [← hρFr]
          exact ⟨A, rfl⟩
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          (commute_weylWordElt hE e8D8Word e8D8Word_orth hA).eq, mul_inv_cancel_right]
        rfl
    · obtain ⟨hne, hc1, hc2, l, hl⟩ := e8D8_adj i j hij hi
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl hne hc1 hc2 hl
      rw [hρk i hi, hρk j hj0]
      exact ⟨emb, sl3_comp_blk hv (hρFv _) (hρFv _)⟩
  refine ⟨ρ, hρ', hcomm, hψ, fun k hk c => ?_⟩
  rw [hρk k hk]
  exact hρFv _ c

end S12

section S13
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

theorem weakCT_param_top {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧
      (∀ k c, Ψ (x (sroot k) c) = ρ k (tv 0 1 c)) ∧ (∀ k c, Ψ (x (-sroot k) c) = ρ k (tv 1 0 c)) ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
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
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, -, -, -⟩ :=
    exists_surjective_of_simplyLacedFrame hCT hL hD hfr hgen' hnt
  refine ⟨Ψ, hsurj, hker, hΨu, hΨv, fun k => ?_⟩
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

theorem weakCT_param {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank) {G : Type} [Group G]
    {U : Fin D.rank → Subgroup G}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : K →* G, Ψ.ker ≤ Subgroup.center K ∧ Ψ.range = ⨆ k, U k ∧
      (∀ k c, Ψ (x (sroot k) c) = ρ k (tv 0 1 c)) ∧ (∀ k c, Ψ (x (-sroot k) c) = ρ k (tv 1 0 c)) ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
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
  obtain ⟨Ψ', hsurj, hker, hu, hv, hblk⟩ := weakCT_param_top hCT hL hD k₀ (X := Gs)
    (U := fun k => (U k).subgroupOf Gs)
    (ClassicalInvolution.Models.SymplecticPairs.iSup_subgroupOf_eq_top U)
    (fun i j hne hij hji u hu v hv => Subtype.ext (hcomm i j hne hij hji u.1 hu v.1 hv))
    (ρ := fun k => (ρ k).codRestrict Gs fun A => hρle k ⟨A, rfl⟩) hρ'
    (fun i j hij => by
      obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij
      have hle : ψ.range ≤ Gs := by
        refine range_le_of_blk ψ ?_ ?_
        · rw [hψ0]
          exact (hρ i).2.le.trans (hUle i)
        · rw [hψ1]
          exact (hρ j).2.le.trans (hUle j)
      refine ⟨ψ.codRestrict Gs fun A => hle ⟨A, rfl⟩,
        MonoidHom.ext fun A => Subtype.ext ?_, MonoidHom.ext fun A => Subtype.ext ?_⟩
      · show ψ (blk F 0 A) = ρ i A
        rw [← hψ0, MonoidHom.comp_apply]
      · show ψ (blk F 1 A) = ρ j A
        rw [← hψ1, MonoidHom.comp_apply])
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, fun k c => ?_, fun k c => ?_, fun k => ?_⟩
  · intro y hy
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hy))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · exact congrArg Subtype.val (hu k c)
  · exact congrArg Subtype.val (hv k c)
  · rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]

end Recognition

end S13

section S14
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups


theorem exists_psi_D8_param (K : Type) [Field K] [Finite K] (hn3 : 3 ≤ 8) :
    ∃ Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)) ∧
      Ψ.range = ⨆ k, e8D8Chain K k ∧
      (∀ k, (CurtisTits.rankOne (Spin.plusDatum 8 K hn3).rootGroup k).map Ψ = e8D8Chain K k) ∧
      ∀ k : Fin 8, k ≠ 0 →
        Ψ (Spin.weylD K hn3 k) = Chevalley.weylElement .E8 K (e8D8Node k) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  have hadm : StatedLieAdmissible .POmegaPlus 8 (ringChar K) m := ⟨hℓ, m.pos, by norm_num⟩
  obtain ⟨ρ, hρ, hcomm, hψ, hparam⟩ := exists_e8D8_family_param K
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum 8 K hn3).isFiniteType
    (Dv := (Spin.plusDatum 8 K hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨x', hD, hx'⟩ := exists_simplyLacedLevis hE rfl
    (fun α _ β _ _ _ => Steinberg.SpinPlus.commC_natAbs α β (1, 1)) LevisSpin.edgeD_asymm
    (fun _ _ h => LevisSpin.cartanD_of_edgeD h)
    (fun _ _ hij h1 h2 => LevisSpin.cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => LevisSpin.edgeD_neighbour hn3 h)
    (Spin.plusDatum_steinbergExtras hn3).torus_iSupIndep
    (fun (k : Fin 8) => by
      have h := (Steinberg.SpinPlus.isCTGroupDatum (K := K) hn3).sq_mem k
      rw [← weylElement_spinPlus hn3 k] at h
      exact h)
  obtain ⟨Ψ, hker, hrange, hu, hv, hrank⟩ := weakCT_param
    (CurtisTits.curtisTitsConclusion_spinPlus hadm hK hn3) (leviConePresented_spinPlus K hn3) hD
    (⟨0, by omega⟩ : Fin 8) (U := e8D8Chain K) hcomm hρ hψ
  have hU1 : ∀ k c, Ψ (Steinberg.SpinPlus.x 8 K hn3 (sroot k) c) = ρ k (tv 0 1 c) := fun k c =>
    (congrArg Ψ (hx' k c).1.symm).trans (hu k c)
  have hU2 : ∀ k c, Ψ (Steinberg.SpinPlus.x 8 K hn3 (-sroot k) c) = ρ k (tv 1 0 c) := fun k c =>
    (congrArg Ψ (hx' k c).2.symm).trans (hv k c)
  refine ⟨Ψ, hker, hrange, hrank, fun k hk => ?_⟩
  rw [← weylElement_spinPlus hn3 k, weylElement_eq_xPar (rootOperatorFamily .E8) (e8D8Node k)]
  simp only [Steinberg.weylElement, Units.val_one, inv_one, map_mul]
  change Ψ (Steinberg.SpinPlus.x 8 K hn3 (sroot k) 1) *
    Ψ (Steinberg.SpinPlus.x 8 K hn3 (-sroot k) (-1)) *
      Ψ (Steinberg.SpinPlus.x 8 K hn3 (sroot k) 1) = _
  rw [hU1, hU2, (hparam k hk 1).1, (hparam k hk (-1)).2]

end S14

section S15
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CoxeterSystem
open scoped MatrixGroups

section SpinConj

variable {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)

theorem spin_conj_inv_mem (i : Fin n) : ∀ γ ∈ RootSystem.roots (Spin.isFiniteType_cartanD n) ∅,
    ∀ x ∈ Spin.plusRootGroup n K hn γ,
      (Spin.weylD K hn i)⁻¹ * x * Spin.weylD K hn i ∈
        Spin.plusRootGroup n K hn (RootSystem.weylAction (Spin.isFiniteType_cartanD n)
          ((RootSystem.coxeterMatrix (Spin.isFiniteType_cartanD n)).toCoxeterSystem.simple i)
            γ) := by
  intro γ hγ x hx
  have hK := Steinberg.SpinPlus.isCTGroupDatum (K := K) hn
  have hΦ := RootSystem.isCTRootSystem (Spin.isFiniteType_cartanD n) ∅
  have hγ' := hΦ.smul_mem
    ((RootSystem.coxeterMatrix (Spin.isFiniteType_cartanD n)).toCoxeterSystem.simple i) γ hγ
  have h1 := hK.conj_mem i γ hγ x hx
  have h2 := hK.H_conj_mem i _ hγ' _ (inv_mem (hK.sq_mem i)) _ h1
  have : (Spin.weylD K hn i)⁻¹ * x * Spin.weylD K hn i =
      (Spin.weylD K hn i ^ 2)⁻¹ * (Spin.weylD K hn i * x * (Spin.weylD K hn i)⁻¹) *
        ((Spin.weylD K hn i ^ 2)⁻¹)⁻¹ := by group
  rw [this]
  exact h2

theorem spin_conj_prod_inv_mem : ∀ (ω : List (Fin n)),
    ∀ γ ∈ RootSystem.roots (Spin.isFiniteType_cartanD n) ∅,
      ∀ x ∈ Spin.plusRootGroup n K hn γ,
        ((ω.map (Spin.weylD K hn)).prod)⁻¹ * x * (ω.map (Spin.weylD K hn)).prod ∈
          Spin.plusRootGroup n K hn (RootSystem.weylAction (Spin.isFiniteType_cartanD n)
            ((RootSystem.coxeterMatrix (Spin.isFiniteType_cartanD n)).toCoxeterSystem.wordProd
              ω)⁻¹ γ)
  | [], γ, _, x, hx => by simpa using hx
  | a :: ω, γ, hγ, x, hx => by
    have hΦ := RootSystem.isCTRootSystem (Spin.isFiniteType_cartanD n) (∅ : Set (Fin n))
    have h := spin_conj_inv_mem hn a γ hγ x hx
    have h' := spin_conj_prod_inv_mem ω _ (hΦ.smul_mem _ γ hγ) _ h
    rw [CoxeterSystem.wordProd_cons, mul_inv_rev, CoxeterSystem.inv_simple, map_mul,
      Module.End.mul_apply]
    simpa [List.map_cons, List.prod_cons, mul_assoc] using h'

theorem spin_rootGroup_wordProd_le (ω : List (Fin n)) {γ₀ : Fin n → ℤ}
    (hγ₀ : γ₀ ∈ RootSystem.roots (Spin.isFiniteType_cartanD n) ∅) :
    Spin.plusRootGroup n K hn (RootSystem.weylAction (Spin.isFiniteType_cartanD n)
      ((RootSystem.coxeterMatrix (Spin.isFiniteType_cartanD n)).toCoxeterSystem.wordProd ω) γ₀) ≤
      (Spin.plusRootGroup n K hn γ₀).map
        (MulAut.conj ((ω.map (Spin.weylD K hn)).prod)).toMonoidHom := by
  have hΦ := RootSystem.isCTRootSystem (Spin.isFiniteType_cartanD n) (∅ : Set (Fin n))
  intro y hy
  have hmem : RootSystem.weylAction (Spin.isFiniteType_cartanD n)
      ((RootSystem.coxeterMatrix (Spin.isFiniteType_cartanD n)).toCoxeterSystem.wordProd ω) γ₀ ∈
        RootSystem.roots (Spin.isFiniteType_cartanD n) ∅ := hΦ.smul_mem _ γ₀ hγ₀
  have h := spin_conj_prod_inv_mem hn ω _ hmem y hy
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
  refine ⟨_, h, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end SpinConj

end S15

section S16
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CoxeterSystem CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Coordinates

variable {n : ℕ}

theorem toStdD_weylAction_wordProd (ω : List (Fin n)) (v : Fin n → ℤ) :
    toStdD n (RootSystem.weylAction (isFiniteType_cartanD n)
      ((RootSystem.coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.wordProd ω) v) =
      ω.foldr (fun a e => stdReflD n a e) (toStdD n v) := by
  induction ω with
  | nil => simp
  | cons a ω ih =>
    rw [CoxeterSystem.wordProd_cons, RootSystem.weylAction_mul_apply, RootSystem.weylAction_simple,
      toStdD_reflection, ih, List.foldr_cons]

example : ([1, 2, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1] : List (Fin 8)).foldr (fun a e => stdReflD 8 a e)
    (toStdD 8 (Pi.single 0 1)) = Pi.single 0 (boolSign true) + Pi.single 1 (boolSign true) := by
  decide +kernel

example : ([3, 2, 4, 3, 5, 4, 6, 5] : List (Fin 8)).foldr (fun a e => stdReflD 8 a e)
    (toStdD 8 (Pi.single 7 1)) = Pi.single 2 (boolSign true) + Pi.single 3 (boolSign true) := by
  decide +kernel

example : ([5, 4, 6, 5] : List (Fin 8)).foldr (fun a e => stdReflD 8 a e)
    (toStdD 8 (Pi.single 7 1)) = Pi.single 4 (boolSign true) + Pi.single 5 (boolSign true) := by
  decide +kernel

end Coordinates

end S16

section S17
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
open scoped MatrixGroups


section Identification

variable {K : Type} [Field K] (hn3 : 3 ≤ 8)
  {Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K}

theorem map_longSL2_eq_chain
    (hrank : ∀ k, (CurtisTits.rankOne (Spin.plusDatum 8 K hn3).rootGroup k).map Ψ = e8D8Chain K k)
    {k i j : Fin 8} (hij : i ≠ j) (s t : Bool)
    (hγ : toStdD 8 (Pi.single k 1) = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    ((Spin.plusFrame 8 K hn3).longSL2 hij s t).range.map Ψ = e8D8Chain K k := by
  have h := CFSG.ClassicalInvolution.RouteD.Gaps.rootGroup_sup_eq_longSL2_range (K := K) hn3 hij
    s t hγ
  rw [← h]
  exact hrank k

theorem map_longSL2_le_of_word
    (hrank : ∀ k, (CurtisTits.rankOne (Spin.plusDatum 8 K hn3).rootGroup k).map Ψ = e8D8Chain K k)
    (hweyl : ∀ k : Fin 8, k ≠ 0 →
      Ψ (Spin.weylD K hn3 k) = Chevalley.weylElement .E8 K (e8D8Node k))
    (ω : List (Fin 8)) (hω : ∀ k ∈ ω, k ≠ 0) (k₀ : Fin 8) {i j : Fin 8} (hij : i ≠ j) (s t : Bool)
    (hγ : ω.foldr (fun a e => stdReflD 8 a e) (toStdD 8 (Pi.single k₀ 1)) =
      Pi.single i (boolSign s) + Pi.single j (boolSign t))
    {c β : Fin (Tag.rank .E8) → ℤ} (hc : IsRoot .E8 c) (hchain : e8D8Chain K k₀ = rootPairE8 K c)
    (hβ : wordReflect .E8 (ω.map e8D8Node) c = β) :
    ((Spin.plusFrame 8 K hn3).longSL2 hij s t).range.map Ψ ≤ rootPairE8 K β := by
  have hΦ := RootSystem.isCTRootSystem (isFiniteType_cartanD 8) (∅ : Set (Fin 8))
  set w := (RootSystem.coxeterMatrix (isFiniteType_cartanD 8)).toCoxeterSystem.wordProd ω with hw
  set γ : Fin 8 → ℤ := RootSystem.weylAction (isFiniteType_cartanD 8) w (Pi.single k₀ 1) with hγdef
  have hγ' : toStdD 8 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
    rw [hγdef, hw, toStdD_weylAction_wordProd, hγ]
  have hsingle : (Pi.single k₀ 1 : Fin 8 → ℤ) ∈ RootSystem.roots (isFiniteType_cartanD 8) ∅ :=
    hΦ.single_mem k₀
  have hneg : (-Pi.single k₀ 1 : Fin 8 → ℤ) ∈ RootSystem.roots (isFiniteType_cartanD 8) ∅ := by
    have := hΦ.smul_mem ((RootSystem.coxeterMatrix (isFiniteType_cartanD 8)).toCoxeterSystem.simple
      k₀) _ (hΦ.single_mem k₀)
    rwa [hΦ.simple_single] at this
  have hrg := CFSG.ClassicalInvolution.RouteD.Gaps.rootGroup_sup_eq_longSL2_range (K := K) hn3 hij
    s t hγ'
  have hle : ((Spin.plusFrame 8 K hn3).longSL2 hij s t).range ≤
      (CurtisTits.rankOne (Spin.plusDatum 8 K hn3).rootGroup k₀).map
        (MulAut.conj ((ω.map (Spin.weylD K hn3)).prod)).toMonoidHom := by
    rw [← hrg]
    refine sup_le ?_ ?_
    · exact (spin_rootGroup_wordProd_le (K := K) hn3 ω hsingle).trans
        (Subgroup.map_mono le_sup_left)
    · have h2 := spin_rootGroup_wordProd_le (K := K) hn3 ω hneg
      rw [hw, map_neg] at *
      exact h2.trans (Subgroup.map_mono le_sup_right)
  have hΨz : Ψ ((ω.map (Spin.weylD K hn3)).prod) = weylWordElt .E8 K (ω.map e8D8Node) := by
    rw [map_list_prod, List.map_map, weylWordElt, List.map_map]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    exact hweyl k (hω k hk)
  calc ((Spin.plusFrame 8 K hn3).longSL2 hij s t).range.map Ψ
      ≤ ((CurtisTits.rankOne (Spin.plusDatum 8 K hn3).rootGroup k₀).map
          (MulAut.conj ((ω.map (Spin.weylD K hn3)).prod)).toMonoidHom).map Ψ :=
        Subgroup.map_mono hle
    _ = ((CurtisTits.rankOne (Spin.plusDatum 8 K hn3).rootGroup k₀).map Ψ).map
          (MulAut.conj (Ψ ((ω.map (Spin.weylD K hn3)).prod))).toMonoidHom :=
        map_conj_map Ψ _ _
    _ = (rootPairE8 K c).map (MulAut.conj (weylWordElt .E8 K (ω.map e8D8Node))).toMonoidHom := by
        rw [hrank k₀, hchain, hΨz]
    _ = rootPairE8 K β := by
        rw [← hβ]
        exact map_conj_weylWordElt_rootPair (K := K) (ω.map e8D8Node) hc

end Identification

end S17

section S18
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo
open scoped MatrixGroups

@[expose] def ιstd : Fin 4 × Bool ≃ Fin 8 where
  toFun p := ⟨2 * p.1.val + (if p.2 then 1 else 0), by
    have := p.1.isLt
    split_ifs <;> omega⟩
  invFun j := (⟨j.val / 2, by omega⟩, decide (j.val % 2 = 1))
  left_inv := by decide
  right_inv := by decide


section Frame

variable {K : Type} [Field K] (hn3 : 3 ≤ 8)
  {Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K}

theorem e8D8Chain_zero_eq : e8D8Chain K 0 = rootPairE8 K e8D8Root := by
  simp [e8D8Chain]

theorem e8D8Chain_ne_zero_eq {k : Fin 8} (hk : k ≠ 0) :
    e8D8Chain K k = rootPairE8 K (Pi.single (e8D8Node k) 1) := by
  simp only [e8D8Chain, hk, if_false]
  rfl

theorem rootPairE8_le_frame (i : Fin 8) : rootPairE8 K (frameE8Root i) ≤ e8FrameGroup K :=
  le_iSup (fun i => rootPairE8 K (frameE8Root i)) i

theorem e8D8Chain_le_frame_of_simple {k : Fin 8} {i : Fin 8} (hk : k ≠ 0)
    (h : frameE8Root i = Pi.single (e8D8Node k) 1) : e8D8Chain K k ≤ e8FrameGroup K := by
  rw [e8D8Chain_ne_zero_eq hk, ← h]
  exact rootPairE8_le_frame i

theorem map_spinFrameGroup_le
    (hrank : ∀ k, (CurtisTits.rankOne (Spin.plusDatum 8 K hn3).rootGroup k).map Ψ = e8D8Chain K k)
    (hweyl : ∀ k : Fin 8, k ≠ 0 →
      Ψ (Spin.weylD K hn3 k) = Chevalley.weylElement .E8 K (e8D8Node k)) :
    (spinFrameGroup 8 K hn3 ιstd).map Ψ ≤ e8FrameGroup K := by
  unfold spinFrameGroup
  rw [Subgroup.map_iSup]
  refine iSup_le fun a => ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · fin_cases a
    ·
      refine (map_longSL2_le_of_word hn3 hrank hweyl [1, 2, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1]
        (by decide) 0 (ne_of_pairing ιstd _) true true (by decide +kernel)
        isRoot_e8D8Root e8D8Chain_zero_eq (β := frameE8Root 0) (by decide)).trans
        (rootPairE8_le_frame 0)
    ·
      refine (map_longSL2_le_of_word hn3 hrank hweyl [3, 2, 4, 3, 5, 4, 6, 5]
        (by decide) 7 (ne_of_pairing ιstd _) true true (by decide +kernel)
        (isRoot_single _ _) (e8D8Chain_ne_zero_eq (by decide)) (β := frameE8Root 2)
        (by decide)).trans (rootPairE8_le_frame 2)
    ·
      refine (map_longSL2_le_of_word hn3 hrank hweyl [5, 4, 6, 5]
        (by decide) 7 (ne_of_pairing ιstd _) true true (by decide +kernel)
        (isRoot_single _ _) (e8D8Chain_ne_zero_eq (by decide)) (β := frameE8Root 3)
        (by decide)).trans (rootPairE8_le_frame 3)
    ·
      rw [map_longSL2_eq_chain hn3 hrank (k := 7) (ne_of_pairing ιstd _) true true
        (by decide +kernel)]
      exact e8D8Chain_le_frame_of_simple (i := 7) (by decide) (by decide)
  · fin_cases a
    ·
      rw [map_longSL2_eq_chain hn3 hrank (k := 0) (ne_of_pairing ιstd _) true false
        (by decide +kernel), e8D8Chain_zero_eq]
      have e : e8D8Root = frameE8Root 1 := by decide
      rw [e]
      exact rootPairE8_le_frame 1
    ·
      rw [map_longSL2_eq_chain hn3 hrank (k := 2) (ne_of_pairing ιstd _) true false
        (by decide +kernel)]
      exact e8D8Chain_le_frame_of_simple (i := 4) (by decide) (by decide)
    ·
      rw [map_longSL2_eq_chain hn3 hrank (k := 4) (ne_of_pairing ιstd _) true false
        (by decide +kernel)]
      exact e8D8Chain_le_frame_of_simple (i := 5) (by decide) (by decide)
    ·
      rw [map_longSL2_eq_chain hn3 hrank (k := 6) (ne_of_pairing ιstd _) true false
        (by decide +kernel)]
      exact e8D8Chain_le_frame_of_simple (i := 6) (by decide) (by decide)

end Frame

end S18

section S19
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
open scoped MatrixGroups

section Arith

variable {K : Type} [Field K] [Finite K]

theorem orderOf_eq_two_of_dvd_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hsq : ((Nat.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    have h : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hpq
    push_cast at h
    linear_combination ((Nat.card K : ZMod p) - 1) * h
  have hne1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h1
    have h2 : p ∣ Nat.card K - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h1, Nat.cast_one, sub_self]
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h2
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)
  have hd : orderOf ((Nat.card K : ℕ) : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hne1
  · exact h

omit [Field K] [Finite K] in
theorem not_dvd_card_of_dvd_add_one {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) :
    ¬ p ∣ Nat.card K := by
  intro hd
  have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem not_dvd_pred_of_dvd_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) : ¬ p ∣ Nat.card K - 1 := by
  intro hd
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
  have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
  rw [e] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

theorem odd_card_of_seven_dvd_add_one (hpq : 7 ∣ Nat.card K + 1) : Odd (Nat.card K) := by
  by_contra hodd
  have : Fintype K := Fintype.ofFinite K
  have heven : Even (Fintype.card K) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.not_odd_iff_even.mp hodd
  have h2 : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp heven)
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  rw [h2] at hm
  have hK : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  rw [hK] at hpq
  have h3 : (2 ^ (m : ℕ) + 1) % 7 ≠ 0 := by
    have : (2 : ℕ) ^ (m : ℕ) % 7 = 1 ∨ (2 : ℕ) ^ (m : ℕ) % 7 = 2 ∨ (2 : ℕ) ^ (m : ℕ) % 7 = 4 := by
      induction (m : ℕ) with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Nat.mul_mod]
        rcases ih with h | h | h <;> rw [h] <;> norm_num
    omega
  exact h3 (Nat.mod_eq_zero_of_dvd hpq)

end Arith

end S19

section S20
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups


section Assembly

variable {K : Type} [Field K] [Finite K]

theorem not_dvd_card_center_spinPlus {n : ℕ} (hn3 : 3 ≤ n) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq1 : ¬ p ∣ Nat.card K - 1) :
    ¬ p ∣ Nat.card (Subgroup.center (spinGroup (Spin.quadPlus n K))) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  haveI : Finite (spinGroup (Spin.quadPlus n K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := n) (K := K) hn3
  exact not_dvd_card_center_spin_of_not_dvd_pred (Spin.quadPlus n K)
    (range_spinMatrix_quadPlus hn3) hZ hcomap
    (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1

theorem map_ne_bot_of_central_kernel {S G : Type*} [Group S] [Group G] [Finite S] {r : ℕ}
    [Fact r.Prime] (Ψ : S →* G) (hker : Ψ.ker ≤ Subgroup.center S)
    (hcen : ¬ r ∣ Nat.card (Subgroup.center S)) {U : Subgroup S} (hU : U ≠ ⊥)
    (hUp : IsPGroup r U) : U.map Ψ ≠ ⊥ := by
  intro h
  apply hU
  rw [eq_bot_iff]
  intro u hu
  have hu1 : u ∈ Ψ.ker := by
    rw [MonoidHom.mem_ker]
    have : Ψ u ∈ U.map Ψ := ⟨u, hu, rfl⟩
    rw [h] at this
    exact this
  obtain ⟨k, hk⟩ := hUp ⟨u, hu⟩
  have hk' : u ^ (r ^ k) = 1 := congrArg Subtype.val hk
  have hcz : u ∈ Subgroup.center S := hker hu1
  have hdvd : orderOf u ∣ Nat.card (Subgroup.center S) := by
    have : orderOf (⟨u, hcz⟩ : Subgroup.center S) ∣ Nat.card (Subgroup.center S) :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at this
  have hord : orderOf u ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h1 : orderOf u = 1 := by
    rcases (Nat.dvd_prime_pow (Fact.out : r.Prime)).1 hord with ⟨j, -, hj⟩
    by_cases hj0 : j = 0
    · rw [hj, hj0, pow_zero]
    · exfalso
      apply hcen
      rw [hj] at hdvd
      exact (dvd_pow_self r hj0).trans hdvd
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

end Assembly

end S20

section S21
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups


section Final

theorem normalizesRGroup_of_map_conj {G : Type*} [Group G] {r : ℕ} {E₀ : Subgroup G} (g : G)
    (h : NormalizesRGroup r (E₀.map (MulAut.conj g).toMonoidHom)) : NormalizesRGroup r E₀ := by
  obtain ⟨U, hU0, hUp, hUn⟩ := h
  refine ⟨U.map (MulAut.conj g⁻¹).toMonoidHom, ?_, hUp.map _, ?_⟩
  · intro hbot
    apply hU0
    have := congrArg (fun S : Subgroup G => S.map (MulAut.conj g).toMonoidHom) hbot
    simp only [Subgroup.map_map, Subgroup.map_bot] at this
    have e : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) = MonoidHom.id G := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rwa [e, Subgroup.map_id] at this
  · intro x hx
    have h1 := hUn (g * x * g⁻¹) ⟨x, hx, rfl⟩
    have h2 : (U.map (MulAut.conj (g * x * g⁻¹)).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
        (U.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [← h2, h1]

end Final

end S21

section S22
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups


section Main

variable {K : Type} [Field K] [Finite K]

theorem e8_conj_into_frame_seven (hpq : 7 ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ 7 = 1)
    (hE₀c : Nat.card E₀ = 7 ^ 2) (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8FrameGroup K := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : (7 : ℕ).Prime := by norm_num
  have hodd := odd_card_of_seven_dvd_add_one hpq
  have hord := orderOf_eq_two_of_dvd_add_one hp7 (by norm_num) hpq
  have hpK : ¬ 7 ∣ Nat.card K := not_dvd_card_of_dvd_add_one hp7 hpq
  have hpq1 := not_dvd_pred_of_dvd_add_one hp7 (by norm_num) hpq
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  have hpl : 7 ≠ ringChar K := by
    intro h
    apply hpK
    rw [hK, ← h]
    exact dvd_pow_self 7 m.ne_zero
  have hn3 : 3 ≤ 8 := by norm_num
  obtain ⟨Ψ, hker, hrange, hrank, hweyl⟩ := exists_psi_D8_param K hn3
  obtain ⟨g, hg⟩ := exists_conj_le_range_of_sylow_E8_seven hpq Ψ hker E₀ hE₀p
  set E := E₀.map (MulAut.conj g).toMonoidHom with hE
  have hEp : ∀ x ∈ E, x ^ 7 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hE₀p y hy]
    group
  have hEc : Nat.card E = 7 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  haveI : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  haveI : Finite (spinGroup (Spin.quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hcen7 := not_dvd_card_center_spinPlus (K := K) hn3 (p := 7) (by norm_num) hpq1
  have hΨcop : ¬ 7 ∣ Nat.card Ψ.ker := fun hd => hcen7 (hd.trans (Subgroup.card_dvd_of_le hker))
  have hE_le : E ≤ Ψ.range := hg
  set Ψ' : spinGroup (Spin.quadPlus 8 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian 7 E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = 7 ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = 7 ^ 2 := by
    rw [← card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE', hcardE1]
  have hlift : ∀ ε ∈ E, ∃ e ∈ E', Ψ e = ε := by
    intro ε hε
    have : (⟨ε, hE_le hε⟩ : Ψ.range) ∈ E1 := hε
    rw [← hmapE'] at this
    obtain ⟨e, he, hee⟩ := this
    exact ⟨e, he, congrArg Subtype.val hee⟩
  have hNS : ∀ T : Submodule K (Fin 8 ⊕ Fin 8 → K),
      (∀ e ∈ E', ∀ v ∈ T, spinAction (Spin.quadPlus 8 K) e v ∈ T) →
      (∀ v ∈ T, Spin.quadPlus 8 K v = 0) → T = ⊥ := by
    intro T hTi hTs
    by_contra hT0
    obtain ⟨U, hU0, hUp, hUn⟩ :=
      exists_rGroup_normalized_of_invariant_singular hodd hn3 E' T hT0 hTs hTi
    haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
    have hr2 : ringChar K ≠ 2 := by
      intro h2
      have : Even (Nat.card K) := by
        rw [hK, h2]
        exact (Nat.even_pow.mpr ⟨even_two, m.ne_zero⟩)
      exact (Nat.not_even_iff_odd.mpr hodd) this
    have hrq1 : ¬ ringChar K ∣ Nat.card K - 1 := by
      intro hd
      have hq1 : 1 ≤ Nat.card K := Nat.card_pos
      have h1 : ringChar K ∣ Nat.card K := by
        rw [hK]
        exact dvd_pow_self _ m.ne_zero
      have h2 : ringChar K ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hd
      have e : Nat.card K - (Nat.card K - 1) = 1 := by omega
      rw [e] at h2
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
    have hcenr := not_dvd_card_center_spinPlus (K := K) hn3 hr2 hrq1
    have hV0 := map_ne_bot_of_central_kernel Ψ hker hcenr hU0 hUp
    apply hN
    refine normalizesRGroup_of_map_conj g ⟨U.map Ψ, hV0, hUp.map Ψ, ?_⟩
    rintro ε hε
    obtain ⟨e, he, rfl⟩ := hlift ε hε
    rw [← map_conj_map Ψ e U, hUn e he]
  obtain ⟨x, hx⟩ := exists_spin_conj_frameGroup hodd hn3 (k := 4) (by norm_num) ιstd hp7
    (by norm_num) hpl hord E' hE'ea.2 hcardE' hNS
  refine ⟨Ψ x * g, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨e, he, hee⟩ := hlift (g * z * g⁻¹) ⟨z, hz, rfl⟩
  have h1 : Ψ (x * e * x⁻¹) ∈ e8FrameGroup K :=
    map_spinFrameGroup_le hn3 hrank hweyl ⟨_, hx e he, rfl⟩
  have h2 : Ψ (x * e * x⁻¹) = Ψ x * (g * z * g⁻¹) * (Ψ x)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hee]
  rw [h2] at h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  simpa [mul_assoc] using h1

end Main

end S22

section S23
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge TauCeti CFSG.AGLEmbeddingD2
  CFSG.LieType.SeitzGeneration
open scoped MatrixGroups


section Glue

@[expose] def E8TwoSylowSeven : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 7 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ 7 = 1) → Nat.card E₀ = 7 ^ 2 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
        ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8FrameGroup K

theorem e8TwoSylowSeven : E8TwoSylowSeven := fun K _ _ hpq E₀ hE₀p hE₀c hN =>
  e8_conj_into_frame_seven hpq E₀ hE₀p hE₀c hN

@[expose] def E8TwoNativeSeven : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 7 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ 7 = 1) → Nat.card E₀ = 7 ^ 2 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
        Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤

theorem e8TwoNativeSeven_of_sylow (h : E8TwoSylowSeven) : E8TwoNativeSeven := by
  intro K _ _ hpq E₀ hE₀p hE₀c hN
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := h K hpq E₀ hE₀p hE₀c hN
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  exact closure_centralizers_eq_top_of_two_conj (p := 7) (⨆ k, e8D8Chain K k) (e8FrameGroup K)
    (weylWordElt .E8 K e8Word) e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_d8Chain_le_closure_centralizers_two (by norm_num) (by norm_num) hpq
      Ψ hker hrange E hE hEp hEc) E₀ hE₀p hE₀c ⟨g, hg⟩

theorem seitzExcHighE8Two_of_native_for {R : ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 5 ≤ p → R p →
      p ∣ Nat.card K + 1 → ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ p = 1) →
        Nat.card E₀ = p ^ 2 → ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤) :
    SeitzExcHighForAt IsE8Index fun d p =>
      R p ∧ ClassRange LieTypeIndex.E8 (fun _ => True) 2 d p := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hR, hp5, q, hdq, -, hord⟩, -, hn⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp hord
  have hr : ringChar K = (LieTypeIndex.E8 q).characteristic := by
    rw [LieTypeIndex.characteristic_E8]
    exact ringChar.eq K q.p
  refine planeGen_of_native_closure_cond (r := ringChar K) e center_adjointGroup_eq_bot
    (fun E₀ hE₀p hE₀c hN => h K p hp5 hR hpq E₀ hE₀p hE₀c hN) hE hcard hin ?_
  rw [hr]
  exact hn

@[expose] def SeitzExcHighE8TwoFive : Prop :=
  SeitzExcHighForAt IsE8Index fun d p => p = 5 ∧ ClassRange LieTypeIndex.E8 (fun _ => True) 2 d p

theorem seitzExcHighE8TwoSeven : SeitzExcHighForAt IsE8Index fun d p => p = 7 ∧ ClassRange LieTypeIndex.E8 (fun _ => True) 2 d p := by
  refine seitzExcHighE8Two_of_native_for (R := fun p => p = 7) ?_
  intro K _ _ p hpF hp5 hR hpq E₀ hE₀p hE₀c hN
  subst hR
  exact e8TwoNativeSeven_of_sylow e8TwoSylowSeven K hpq E₀ hE₀p hE₀c hN

theorem seitzExcHighE8TwoLtEleven_of_five (h : SeitzExcHighE8TwoFive) :
    SeitzExcHighE8TwoLtEleven :=
  SeitzExcHighForAt.union (fun d p hp _ hQ => by
    obtain ⟨hlt, hcr⟩ := hQ
    have hp5 : 5 ≤ p := hcr.1
    have h7 : p = 5 ∨ p = 7 := by
      interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)
    rcases h7 with rfl | rfl
    · exact Or.inl ⟨rfl, hcr⟩
    · exact Or.inr ⟨rfl, hcr⟩) h seitzExcHighE8TwoSeven

theorem seitzExcHighE8Two_of_five (h : SeitzExcHighE8TwoFive) : SeitzExcHighE8Two :=
  seitzExcHighE8Two_of_ge_eleven_of_lt (seitzExcHighE8TwoLtEleven_of_five h)

end Glue

end S23

end CFSG.LieType.SeitzGeneration.ExcHigh
