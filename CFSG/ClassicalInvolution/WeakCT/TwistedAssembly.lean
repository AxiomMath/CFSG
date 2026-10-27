module

public import CFSG.ClassicalInvolution.WeakCT.DoublyLaced

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

structure NodeData {K : Type} [Group K] (D : UniversalRootDatum K) (X : Type) [Group X]
    (k : Fin D.rank) (U : Subgroup X) where
  ψp : D.rootGroup (Pi.single k 1) → X
  ψm : D.rootGroup (-Pi.single k 1) → X
  ψp_mem : ∀ g, ψp g ∈ U
  ψm_mem : ∀ g, ψm g ∈ U
  gen : U ≤ Subgroup.closure (Set.range ψp ∪ Set.range ψm)

section Param

variable {K : Type} [Group K] {D : UniversalRootDatum K} {X : Type} [Group X] {k : Fin D.rank}
  {U : Subgroup X}

structure NodeData.IsParam (nd : NodeData D X k U) {F : Type} [Field F] (r : SL(2, F) →* K)
    (ρ : SL(2, F) →* X) : Prop where
  r_upper : ∀ c, r (tv 0 1 c) ∈ D.rootGroup (Pi.single k 1)
  r_lower : ∀ c, r (tv 1 0 c) ∈ D.rootGroup (-Pi.single k 1)
  param_upper : ∀ g ∈ D.rootGroup (Pi.single k 1), ∃ c, r (tv 0 1 c) = g
  param_lower : ∀ g ∈ D.rootGroup (-Pi.single k 1), ∃ c, r (tv 1 0 c) = g
  ψp_eq : ∀ c, nd.ψp ⟨r (tv 0 1 c), r_upper c⟩ = ρ (tv 0 1 c)
  ψm_eq : ∀ c, nd.ψm ⟨r (tv 1 0 c), r_lower c⟩ = ρ (tv 1 0 c)

noncomputable def NodeData.ofParam {F : Type} [Field F] (r : SL(2, F) →* K) (ρ : SL(2, F) →* X)
    (hU : ρ.range = U) (hr : Function.Injective r)
    (r_upper : ∀ c, r (tv 0 1 c) ∈ D.rootGroup (Pi.single k 1))
    (r_lower : ∀ c, r (tv 1 0 c) ∈ D.rootGroup (-Pi.single k 1))
    (param_upper : ∀ g ∈ D.rootGroup (Pi.single k 1), ∃ c, r (tv 0 1 c) = g)
    (param_lower : ∀ g ∈ D.rootGroup (-Pi.single k 1), ∃ c, r (tv 1 0 c) = g) :
    NodeData D X k U where
  ψp g := ρ (tv 0 1 (Classical.choose (param_upper g.1 g.2)))
  ψm g := ρ (tv 1 0 (Classical.choose (param_lower g.1 g.2)))
  ψp_mem g := hU ▸ ⟨_, rfl⟩
  ψm_mem g := hU ▸ ⟨_, rfl⟩
  gen := by
    rw [← hU]
    refine range_le_of_tv ρ _ (fun c => ?_) (fun c => ?_)
    · refine Subgroup.subset_closure (Or.inl ⟨⟨r (tv 0 1 c), r_upper c⟩, ?_⟩)
      have h := Classical.choose_spec (param_upper (r (tv 0 1 c)) (r_upper c))
      have h' : Classical.choose (param_upper (r (tv 0 1 c)) (r_upper c)) = c := by
        have := hr h
        have h01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) this
        simpa [tv01_eq_sl2Upper, Steinberg.sl2Upper] using h01
      show ρ (tv 0 1 (Classical.choose (param_upper (r (tv 0 1 c)) (r_upper c)))) = _
      rw [h']
    · refine Subgroup.subset_closure (Or.inr ⟨⟨r (tv 1 0 c), r_lower c⟩, ?_⟩)
      have h := Classical.choose_spec (param_lower (r (tv 1 0 c)) (r_lower c))
      have h' : Classical.choose (param_lower (r (tv 1 0 c)) (r_lower c)) = c := by
        have := hr h
        have h10 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) this
        simpa [tv10_eq_sl2Lower, Steinberg.sl2Lower] using h10
      show ρ (tv 1 0 (Classical.choose (param_lower (r (tv 1 0 c)) (r_lower c)))) = _
      rw [h']

theorem NodeData.ofParam_isParam {F : Type} [Field F] {r : SL(2, F) →* K} {ρ : SL(2, F) →* X}
    (hU : ρ.range = U) (hr : Function.Injective r)
    (r_upper : ∀ c, r (tv 0 1 c) ∈ D.rootGroup (Pi.single k 1))
    (r_lower : ∀ c, r (tv 1 0 c) ∈ D.rootGroup (-Pi.single k 1))
    (param_upper : ∀ g ∈ D.rootGroup (Pi.single k 1), ∃ c, r (tv 0 1 c) = g)
    (param_lower : ∀ g ∈ D.rootGroup (-Pi.single k 1), ∃ c, r (tv 1 0 c) = g) :
    (NodeData.ofParam r ρ hU hr r_upper r_lower param_upper param_lower).IsParam r ρ where
  r_upper := r_upper
  r_lower := r_lower
  param_upper := param_upper
  param_lower := param_lower
  ψp_eq c := by
    show ρ (tv 0 1 (Classical.choose (param_upper (r (tv 0 1 c)) (r_upper c)))) = _
    have h := Classical.choose_spec (param_upper (r (tv 0 1 c)) (r_upper c))
    have := hr h
    have h01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) this
    have h' : Classical.choose (param_upper (r (tv 0 1 c)) (r_upper c)) = c := by
      simpa [tv01_eq_sl2Upper, Steinberg.sl2Upper] using h01
    rw [h']
  ψm_eq c := by
    show ρ (tv 1 0 (Classical.choose (param_lower (r (tv 1 0 c)) (r_lower c)))) = _
    have h := Classical.choose_spec (param_lower (r (tv 1 0 c)) (r_lower c))
    have := hr h
    have h10 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) this
    have h' : Classical.choose (param_lower (r (tv 1 0 c)) (r_lower c)) = c := by
      simpa [tv10_eq_sl2Lower, Steinberg.sl2Lower] using h10
    rw [h']

theorem NodeData.IsParam.comp_eq_of_rootGroup {F : Type} [Field F]
    {r : SL(2, F) →* K} {ρ : SL(2, F) →* X} {nd : NodeData D X k U}
    (h : nd.IsParam r ρ) (Ψ : K →* X)
    (hp : ∀ g : D.rootGroup (Pi.single k 1), Ψ g = nd.ψp g)
    (hm : ∀ g : D.rootGroup (-Pi.single k 1), Ψ g = nd.ψm g) :
    Ψ.comp r = ρ := by
  apply MonoidHom.eq_of_eqOn_dense (closure_tv_two (F := F))
  rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact (hp ⟨r (tv 0 1 c), h.r_upper c⟩).trans (h.ψp_eq c)
  · exact (hm ⟨r (tv 1 0 c), h.r_lower c⟩).trans (h.ψm_eq c)

end Param

section Levi

variable {K : Type} [Group K] {D : UniversalRootDatum K}

theorem rootGroup_le_of_rankOne (hdiv : D.divisible = ∅) {nw : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hCT : CurtisTits.IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    {i j : Fin D.rank} {M : Subgroup K} (hi : CurtisTits.rankOne D.rootGroup i ≤ M)
    (hj : CurtisTits.rankOne D.rootGroup j ≤ M) :
    ∀ γ ∈ pairRoots D i j, D.rootGroup γ ≤ M := by
  have key : ∀ k, CurtisTits.rankOne D.rootGroup k ≤ M →
      ∀ γ ∈ {γ | γ ∈ D.roots ∧ D.rootGroup γ ≤ M},
        reflection D.cartan k γ ∈ {γ | γ ∈ D.roots ∧ D.rootGroup γ ≤ M} := by
    intro k hk γ ⟨hγ, hM⟩
    refine ⟨reflection_mem_roots k hγ, fun y hy => ?_⟩
    have h1 := hCT.conj_mem k (reflection D.cartan k γ) (reflection_mem_roots k hγ) y hy
    rw [weylAction_simple] at h1
    have hrr : reflection D.cartan k (reflection D.cartan k γ) = γ := by
      have := reflection_mul_self (D.isFiniteType.apply_self k)
      exact (by simpa [Module.End.mul_apply] using congrArg (fun T => T γ) this)
    rw [hrr] at h1
    have hn : nw k ∈ M := hk (hCT.n_mem k)
    have h2 : nw k * y * (nw k)⁻¹ ∈ M := hM h1
    have : y = (nw k)⁻¹ * (nw k * y * (nw k)⁻¹) * nw k := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hn) h2) hn
  have hsingle : ∀ k, CurtisTits.rankOne D.rootGroup k ≤ M →
      sroot k ∈ {γ | γ ∈ D.roots ∧ D.rootGroup γ ≤ M} := fun k hk =>
    ⟨single_mem_roots k, le_sup_left.trans hk⟩
  intro γ hγ
  exact (pairRoots_subset hdiv (hsingle i hi) (hsingle j hj) (key i hi) (key j hj) hγ).2

theorem exists_levi_of_model (hdiv : D.divisible = ∅) {nw : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hCT : CurtisTits.IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (nd : ∀ k, NodeData D X k (U k))
    {i j : Fin D.rank} {Fi Fj : Type} [Field Fi] [Field Fj] {ri : SL(2, Fi) →* K}
    {rj : SL(2, Fj) →* K} {ρi : SL(2, Fi) →* X} {ρj : SL(2, Fj) →* X}
    (hi : (nd i).IsParam ri ρi) (hj : (nd j).IsParam rj ρj) {L : Type} [Group L] (emb : L →* K)
    (hinj : Function.Injective emb) (ιi : SL(2, Fi) →* L) (ιj : SL(2, Fj) →* L)
    (hei : emb.comp ιi = ri) (hej : emb.comp ιj = rj) (ψ : L →* X) (hψi : ψ.comp ιi = ρi)
    (hψj : ψ.comp ιj = ρj) :
    ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : D.rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g := by
  have hrank : ∀ (k : Fin D.rank) {F : Type} [Field F] (r : SL(2, F) →* K) (ρ : SL(2, F) →* X),
      (nd k).IsParam r ρ → r.range ≤ emb.range → CurtisTits.rankOne D.rootGroup k ≤ emb.range := by
    intro k F _ r ρ hk hr
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨c, rfl⟩ := hk.param_upper g hg
      exact hr ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := hk.param_lower g hg
      exact hr ⟨_, rfl⟩
  have hri : ri.range ≤ emb.range := by
    rintro _ ⟨A, rfl⟩
    exact ⟨ιi A, by rw [← hei]; rfl⟩
  have hrj : rj.range ≤ emb.range := by
    rintro _ ⟨A, rfl⟩
    exact ⟨ιj A, by rw [← hej]; rfl⟩
  let E : LeviEmbedding D i j := ⟨L, emb, hinj, rootGroup_le_of_rankOne hdiv hCT
    (hrank i ri ρi hi hri) (hrank j rj ρj hj hrj)⟩
  refine ⟨E, ψ, fun k hk => ?_⟩
  rcases hk with rfl | rfl
  · refine ⟨fun g => ?_, fun g => ?_⟩
    · obtain ⟨c, hc⟩ := hi.param_upper g.1 g.2
      have e1 : emb (ιi (tv 0 1 c)) = g := (DFunLike.congr_fun hei _).trans hc
      rw [preimage_eq_of_emb (E := E) e1]
      have := hi.ψp_eq c
      have hg : g = ⟨ri (tv 0 1 c), hi.r_upper c⟩ := Subtype.ext hc.symm
      rw [hg, this]
      exact DFunLike.congr_fun hψi _
    · obtain ⟨c, hc⟩ := hi.param_lower g.1 g.2
      have e1 : emb (ιi (tv 1 0 c)) = g := (DFunLike.congr_fun hei _).trans hc
      rw [preimage_eq_of_emb (E := E) e1]
      have := hi.ψm_eq c
      have hg : g = ⟨ri (tv 1 0 c), hi.r_lower c⟩ := Subtype.ext hc.symm
      rw [hg, this]
      exact DFunLike.congr_fun hψi _
  · refine ⟨fun g => ?_, fun g => ?_⟩
    · obtain ⟨c, hc⟩ := hj.param_upper g.1 g.2
      have e1 : emb (ιj (tv 0 1 c)) = g := (DFunLike.congr_fun hej _).trans hc
      rw [preimage_eq_of_emb (E := E) e1]
      have := hj.ψp_eq c
      have hg : g = ⟨rj (tv 0 1 c), hj.r_upper c⟩ := Subtype.ext hc.symm
      rw [hg, this]
      exact DFunLike.congr_fun hψj _
    · obtain ⟨c, hc⟩ := hj.param_lower g.1 g.2
      have e1 : emb (ιj (tv 1 0 c)) = g := (DFunLike.congr_fun hej _).trans hc
      rw [preimage_eq_of_emb (E := E) e1]
      have := hj.ψm_eq c
      have hg : g = ⟨rj (tv 1 0 c), hj.r_lower c⟩ := Subtype.ext hc.symm
      rw [hg, this]
      exact DFunLike.congr_fun hψj _

theorem exists_levi_node (hdiv : D.divisible = ∅) {nw : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hCT : CurtisTits.IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (nd : ∀ k, NodeData D X k (U k))
    {i : Fin D.rank} {Fi : Type} [Field Fi] {ri : SL(2, Fi) →* K} {ρi : SL(2, Fi) →* X}
    (hi : (nd i).IsParam ri ρi) (hinj : Function.Injective ri) :
    ∃ (E : LeviEmbedding D i i) (φ : E.L →* X), ∀ k, (k = i ∨ k = i) →
      (∀ g : D.rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g :=
  exists_levi_of_model hdiv hCT nd hi hi ri hinj (MonoidHom.id _) (MonoidHom.id _)
    (MonoidHom.comp_id _) (MonoidHom.comp_id _) ρi (MonoidHom.comp_id _) (MonoidHom.comp_id _)

end Levi

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K}

theorem weakCT_of_twisted_nodes_pinned {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hdiv : D.divisible = ∅) {X : Type} [Group X] {U : Fin D.rank → Subgroup X}
    (hgen : ⨆ k, U k = ⊤) (nd : ∀ k, NodeData D X k (U k))
    (hnt : ∃ k, ∃ g, (nd k).ψp g ≠ 1)
    (hloc : ∀ i j, i ≤ j → ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : D.rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k ∧
        (∀ g : D.rootGroup (Pi.single k 1), Ψ g = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), Ψ g = (nd k).ψm g := by
  classical
  choose E φ hspec using hloc
  have hcompat : ∀ i j (h : i ≤ j) k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots D k k,
      ∀ g ∈ D.rootGroup γ,
        φ i j h ((E i j h).preimage g) = φ k k le_rfl ((E k k le_rfl).preimage g) := by
    intro i j h k hk γ hγ g hg
    have hγ' := pairRoots_self_subset hdiv k hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ'
    rcases hγ' with rfl | rfl
    · exact ((hspec i j h k hk).1 ⟨g, hg⟩).trans ((hspec k k le_rfl k (Or.inl rfl)).1 ⟨g, hg⟩).symm
    · exact ((hspec i j h k hk).2 ⟨g, hg⟩).trans ((hspec k k le_rfl k (Or.inl rfl)).2 ⟨g, hg⟩).symm
  have hfmu : ∀ k (g : D.rootGroup (Pi.single k 1)), frameMap E φ (Pi.single k 1) g =
      (nd k).ψp g := by
    intro k g
    rw [frameMap_of_mem_self (Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (k := k)
      (Or.inl rfl)).1]
    exact (hspec k k le_rfl k (Or.inl rfl)).1 g
  have hfmv : ∀ k (g : D.rootGroup (-Pi.single k 1)), frameMap E φ (-Pi.single k 1) g =
      (nd k).ψm g := by
    intro k g
    rw [frameMap_of_mem_self (Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (k := k)
      (Or.inl rfl)).2]
    exact (hspec k k le_rfl k (Or.inl rfl)).2 g
  have hgen' : Subgroup.closure (⋃ k, Set.range (frameMap E φ (Pi.single k 1)) ∪
      Set.range (frameMap E φ (-Pi.single k 1))) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun k => (nd k).gen.trans (Subgroup.closure_mono ?_)
    rintro _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact Set.mem_iUnion.2 ⟨k, Or.inl ⟨g, hfmu k g⟩⟩
    · exact Set.mem_iUnion.2 ⟨k, Or.inr ⟨g, hfmv k g⟩⟩
  have hnt' : ∃ k, ∃ x, frameMap E φ (Pi.single k 1) x ≠ 1 := by
    obtain ⟨k, g, hg⟩ := hnt
    exact ⟨k, g, by rw [hfmu]; exact hg⟩
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩ :=
    CFSG.WeakCTLevi.exists_surjective_of_leviEmbeddings hCT hL E φ hcompat hgen' hnt'
  refine ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ?_⟩
  have hΨu' : ∀ g : D.rootGroup (Pi.single k 1), Ψ g = (nd k).ψp g := fun g =>
    (hΨu k g).trans (hfmu k g)
  have hΨv' : ∀ g : D.rootGroup (-Pi.single k 1), Ψ g = (nd k).ψm g := fun g =>
    (hΨv k g).trans (hfmv k g)
  refine ⟨?_, hΨu', hΨv'⟩
  rw [CurtisTits.rankOne, Subgroup.map_sup]
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      rw [show Ψ g = (nd k).ψp ⟨g, hg⟩ from hΨu' ⟨g, hg⟩]
      exact (nd k).ψp_mem _
    · rintro _ ⟨g, hg, rfl⟩
      rw [show Ψ g = (nd k).ψm ⟨g, hg⟩ from hΨv' ⟨g, hg⟩]
      exact (nd k).ψm_mem _
  · refine (nd k).gen.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact Subgroup.mem_sup_left ⟨g.1, g.2, hΨu' g⟩
    · exact Subgroup.mem_sup_right ⟨g.1, g.2, hΨv' g⟩

theorem weakCT_of_twisted_nodes {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hdiv : D.divisible = ∅) {X : Type} [Group X] {U : Fin D.rank → Subgroup X}
    (hgen : ⨆ k, U k = ⊤) (nd : ∀ k, NodeData D X k (U k))
    (hnt : ∃ k, ∃ g, (nd k).ψp g ≠ 1)
    (hloc : ∀ i j, i ≤ j → ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : D.rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, hpin⟩ :=
    weakCT_of_twisted_nodes_pinned hCT hL hdiv hgen nd hnt hloc
  exact ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => (hpin k).1⟩

end Recognition

section TwoFields

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] {H : Type*} [Group H]

theorem commute_of_tv₂ (ρ : SL(2, F₁) →* H) (ρ' : SL(2, F₂) →* H)
    (h : ∀ (c : F₁) (d : F₂), Commute (ρ (tv 0 1 c)) (ρ' (tv 0 1 d)) ∧
      Commute (ρ (tv 0 1 c)) (ρ' (tv 1 0 d)) ∧ Commute (ρ (tv 1 0 c)) (ρ' (tv 0 1 d)) ∧
      Commute (ρ (tv 1 0 c)) (ρ' (tv 1 0 d)))
    (a : SL(2, F₁)) (b : SL(2, F₂)) : Commute (ρ a) (ρ' b) := by
  have hgen₁ := closure_tv_two (F := F₁)
  have hgen₂ := closure_tv_two (F := F₂)
  have hmem₁ : ∀ g : SL(2, F₁), g ∈ Subgroup.closure ({g | ∃ c : F₁, g = tv 0 1 c} ∪
      {g | ∃ c : F₁, g = tv 1 0 c}) := fun g => by
    rw [hgen₁]; trivial
  have hmem₂ : ∀ g : SL(2, F₂), g ∈ Subgroup.closure ({g | ∃ c : F₂, g = tv 0 1 c} ∪
      {g | ∃ c : F₂, g = tv 1 0 c}) := fun g => by
    rw [hgen₂]; trivial
  have hb : ∀ s ∈ ({g | ∃ c : F₁, g = tv 0 1 c} ∪ {g | ∃ c : F₁, g = tv 1 0 c} :
      Set SL(2, F₁)), ∀ b, Commute (ρ s) (ρ' b) := by
    intro s hs b
    induction hmem₂ b using Subgroup.closure_induction with
    | mem y hy =>
      rcases hs with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;> rcases hy with ⟨d, rfl⟩ | ⟨d, rfl⟩
      exacts [(h c d).1, (h c d).2.1, (h c d).2.2.1, (h c d).2.2.2]
    | one => rw [map_one]; exact Commute.one_right _
    | mul y z _ _ hy hz => rw [map_mul]; exact hy.mul_right hz
    | inv y _ hy => rw [map_inv]; exact hy.inv_right
  induction hmem₁ a using Subgroup.closure_induction with
  | mem y hy => exact hb y hy b
  | one => rw [map_one]; exact Commute.one_left _
  | mul y z _ _ hy hz => rw [map_mul]; exact hy.mul_left hz
  | inv y _ hy => rw [map_inv]; exact hy.inv_left

theorem injective_noncommCoprod₂ {φ : SL(2, F₁) →* H} {ψ : SL(2, F₂) →* H}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (hc : ∀ a b, Commute (φ a) (ψ b))
    (hZ : ∀ (a : SL(2, F₁)) (b : SL(2, F₂)), a ∈ Subgroup.center SL(2, F₁) →
      b ∈ Subgroup.center SL(2, F₂) → φ a = ψ b → φ a = 1) :
    Function.Injective (φ.noncommCoprod ψ hc) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  rw [MonoidHom.noncommCoprod_apply] at h
  have e : φ a = ψ b⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have ha : a ∈ Subgroup.center SL(2, F₁) :=
    Subgroup.mem_center_iff.2 fun y => hφ (by rw [map_mul, map_mul, e]; exact (hc y b⁻¹).eq)
  have hb : b⁻¹ ∈ Subgroup.center SL(2, F₂) :=
    Subgroup.mem_center_iff.2 fun y => hψ (by rw [map_mul, map_mul, ← e]; exact (hc a y).symm.eq)
  have ha1 : a = 1 := (injective_iff_map_eq_one φ).1 hφ a (hZ a b⁻¹ ha hb e)
  rw [ha1, map_one] at e
  have hb1 : b⁻¹ = 1 := (injective_iff_map_eq_one ψ).1 hψ _ e.symm
  rw [ha1, inv_eq_one.1 hb1]
  rfl

theorem hZ_of_torus {ι : Type*} {H' : ι → Subgroup H} (hind : iSupIndep H') {i j : ι}
    (hij : i ≠ j) (φ : SL(2, F₁) →* H) (ψ : SL(2, F₂) →* H)
    (hφ : φ (wS (1 : F₁ˣ) * wS (1 : F₁ˣ)) ∈ H' i) (hψ : ψ (wS (1 : F₂ˣ) * wS (1 : F₂ˣ)) ∈ H' j) :
    ∀ (a : SL(2, F₁)) (b : SL(2, F₂)), a ∈ Subgroup.center SL(2, F₁) →
      b ∈ Subgroup.center SL(2, F₂) → φ a = ψ b → φ a = 1 := by
  intro a b ha hb hab
  rcases eq_one_or_eq_sq_of_mem_center ha with rfl | rfl
  · exact map_one φ
  · rcases eq_one_or_eq_sq_of_mem_center hb with rfl | rfl
    · rw [hab, map_one]
    · have hdis := hind i
      rw [Subgroup.disjoint_def] at hdis
      exact hdis hφ (Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem hij.symm
        (hab ▸ hψ)))

theorem exists_levi_orth {K : Type} [Group K] {D : UniversalRootDatum K} (hdiv : D.divisible = ∅)
    {nw : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hCT : CurtisTits.IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (nd : ∀ k, NodeData D X k (U k))
    {i j : Fin D.rank} {ri : SL(2, F₁) →* K} {rj : SL(2, F₂) →* K} {ρi : SL(2, F₁) →* X}
    {ρj : SL(2, F₂) →* X} (hi : (nd i).IsParam ri ρi) (hj : (nd j).IsParam rj ρj)
    (hri : Function.Injective ri) (hrj : Function.Injective rj) (hc : ∀ a b, Commute (ri a) (rj b))
    (hZ : ∀ (a : SL(2, F₁)) (b : SL(2, F₂)), a ∈ Subgroup.center SL(2, F₁) →
      b ∈ Subgroup.center SL(2, F₂) → ri a = rj b → ri a = 1)
    (hcX : ∀ a b, Commute (ρi a) (ρj b)) :
    ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : D.rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g :=
  exists_levi_of_model hdiv hCT nd hi hj (ri.noncommCoprod rj hc)
    (injective_noncommCoprod₂ hri hrj hc hZ) (MonoidHom.inl _ _) (MonoidHom.inr _ _)
    (MonoidHom.noncommCoprod_comp_inl _ _ _) (MonoidHom.noncommCoprod_comp_inr _ _ _)
    (ρi.noncommCoprod ρj hcX) (MonoidHom.noncommCoprod_comp_inl _ _ _)
    (MonoidHom.noncommCoprod_comp_inr _ _ _)

end TwoFields

end CFSG.ClassicalInvolution.WeakCT
