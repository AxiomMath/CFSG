module

public import CFSG.ClassicalInvolution.WeakCT.DoublyLaced
public import CFSG.ClassicalInvolution.WeakCT.DLWeakTree

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open scoped MatrixGroups

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem weakCT_of_frame_dl' [Finite F] {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, (ρ k).range = U k)
    (hρa : Function.Injective (ρ a))
    (hψ : ∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j)
    (hψ4 : ∃ ψ : StatedSp 2 F →* X, ψ.comp (spBlock F 1) = ρ a ∧ ψ.comp (spBlock F 0) = ρ b) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  classical
  obtain ⟨hab, hcba, hcab, hadj, hnadj, hnb⟩ := hdiag
  obtain ⟨ψ4, hψ41, hψ40⟩ := hψ4
  have hρU : ∀ k c, ρ k (tv 0 1 c) ∈ U k ∧ ρ k (tv 1 0 c) ∈ U k := fun k c => by
    rw [← hρ k]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  have hsr : ∀ k, sroot k ∈ D.roots ∧ -sroot k ∈ D.roots := fun k =>
    ⟨single_mem_roots k, neg_mem_roots (single_mem_roots k)⟩
  have hmem : ∀ γ ∈ D.roots, ∀ c, x γ c ∈ D.rootGroup γ := fun γ hγ c =>
    ((hE.param γ hγ).1 _).2 ⟨_, rfl⟩
  have hloc : ∀ i j (h : i ≤ j), ∃ (E : LeviEmbedding D i j) (φ : E.L →* X),
      ∀ k, (k = i ∨ k = j) → ∀ c,
        φ (E.preimage (x (sroot k) c)) = ρ k (tv 0 1 c) ∧
          φ (E.preimage (x (-sroot k) c)) = ρ k (tv 1 0 c) := by
    intro i j h
    rcases h.eq_or_lt with rfl | hlt
    ·
      obtain ⟨emb, hinj, hle, hv⟩ := exists_sl2Levi hE hdiv i
      refine ⟨⟨SL(2, F), emb, hinj, hle⟩, ρ i, fun k hk c => ?_⟩
      have hk' : k = i := by rcases hk with h | h <;> exact h
      subst hk'
      exact ⟨by rw [preimage_eq_of_emb (E := ⟨SL(2, F), emb, hinj, hle⟩) (hv c).1],
        by rw [preimage_eq_of_emb (E := ⟨SL(2, F), emb, hinj, hle⟩) (hv c).2]⟩
    ·
      by_cases hij : adj i j
      · by_cases hd : i = a ∧ j = b
        ·
          obtain ⟨rfl, rfl⟩ := hd
          obtain ⟨φ, hφinj, hφle, hφv⟩ := exists_sp4Levi hF h2 hE hdiv hcba hcab
          refine ⟨⟨StatedSp 2 F, φ, hφinj, fun γ hγ => hφle γ (by rwa [pairRoots_comm] at hγ)⟩,
            ψ4, fun k hk c => ?_⟩
          rcases hk with rfl | rfl
          · refine ⟨?_, ?_⟩
            · rw [preimage_eq_of_emb (hφv c).2.2.1]
              exact DFunLike.congr_fun hψ41 (tv 0 1 c)
            · rw [preimage_eq_of_emb (hφv c).2.2.2]
              exact DFunLike.congr_fun hψ41 (tv 1 0 c)
          · refine ⟨?_, ?_⟩
            · rw [preimage_eq_of_emb (hφv c).1]
              exact DFunLike.congr_fun hψ40 (tv 0 1 c)
            · rw [preimage_eq_of_emb (hφv c).2.1]
              exact DFunLike.congr_fun hψ40 (tv 1 0 c)
        ·
          obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij hd
          obtain ⟨hc1, hc2⟩ := hadj i j hij hd
          obtain ⟨k', hk'⟩ := hnb i j hij hd
          obtain ⟨emb, hinj, hle, hv⟩ := exists_sl3Levi hE hdiv hlt.ne hc1 hc2 hk'
          refine ⟨⟨SL(3, F), emb, hinj, hle⟩, ψ, fun k hk c => ?_⟩
          rcases hk with rfl | rfl
          · refine ⟨?_, ?_⟩
            · rw [preimage_eq_of_emb (hv c).1]
              have := DFunLike.congr_fun hψ0 (tv 0 1 c)
              rw [MonoidHom.comp_apply, blk_zero_tv01] at this
              exact this
            · rw [preimage_eq_of_emb (hv c).2.1]
              have := DFunLike.congr_fun hψ0 (tv 1 0 c)
              rw [MonoidHom.comp_apply, blk_zero_tv10] at this
              exact this
          · refine ⟨?_, ?_⟩
            · rw [preimage_eq_of_emb (hv c).2.2.1]
              have := DFunLike.congr_fun hψ1 (tv 0 1 c)
              rw [MonoidHom.comp_apply, blk_one_tv01] at this
              exact this
            · rw [preimage_eq_of_emb (hv c).2.2.2]
              have := DFunLike.congr_fun hψ1 (tv 1 0 c)
              rw [MonoidHom.comp_apply, blk_one_tv10] at this
              exact this
      · by_cases hji : adj j i
        · by_cases hd : j = a ∧ i = b
          ·
            obtain ⟨rfl, rfl⟩ := hd
            obtain ⟨φ, hφinj, hφle, hφv⟩ := exists_sp4Levi hF h2 hE hdiv hcba hcab
            refine ⟨⟨StatedSp 2 F, φ, hφinj, hφle⟩, ψ4, fun k hk c => ?_⟩
            rcases hk with rfl | rfl
            · refine ⟨?_, ?_⟩
              · rw [preimage_eq_of_emb (hφv c).1]
                exact DFunLike.congr_fun hψ40 (tv 0 1 c)
              · rw [preimage_eq_of_emb (hφv c).2.1]
                exact DFunLike.congr_fun hψ40 (tv 1 0 c)
            · refine ⟨?_, ?_⟩
              · rw [preimage_eq_of_emb (hφv c).2.2.1]
                exact DFunLike.congr_fun hψ41 (tv 0 1 c)
              · rw [preimage_eq_of_emb (hφv c).2.2.2]
                exact DFunLike.congr_fun hψ41 (tv 1 0 c)
          ·
            obtain ⟨ψ, hψ0, hψ1⟩ := hψ j i hji hd
            obtain ⟨hc1, hc2⟩ := hadj j i hji hd
            obtain ⟨k', hk'⟩ := hnb j i hji hd
            obtain ⟨emb, hinj, hle, hv⟩ := exists_sl3Levi hE hdiv hlt.ne' hc1 hc2 hk'
            refine ⟨⟨SL(3, F), emb, hinj, fun γ hγ => hle γ (by rwa [pairRoots_comm] at hγ)⟩, ψ,
              fun k hk c => ?_⟩
            rcases hk with rfl | rfl
            · refine ⟨?_, ?_⟩
              · rw [preimage_eq_of_emb (hv c).2.2.1]
                have := DFunLike.congr_fun hψ1 (tv 0 1 c)
                rw [MonoidHom.comp_apply, blk_one_tv01] at this
                exact this
              · rw [preimage_eq_of_emb (hv c).2.2.2]
                have := DFunLike.congr_fun hψ1 (tv 1 0 c)
                rw [MonoidHom.comp_apply, blk_one_tv10] at this
                exact this
            · refine ⟨?_, ?_⟩
              · rw [preimage_eq_of_emb (hv c).1]
                have := DFunLike.congr_fun hψ0 (tv 0 1 c)
                rw [MonoidHom.comp_apply, blk_zero_tv01] at this
                exact this
              · rw [preimage_eq_of_emb (hv c).2.1]
                have := DFunLike.congr_fun hψ0 (tv 1 0 c)
                rw [MonoidHom.comp_apply, blk_zero_tv10] at this
                exact this
        ·
          obtain ⟨hc1, hc2⟩ := hnadj i j hlt.ne hij hji
          obtain ⟨l, hl, hle, hv⟩ := exists_sl2sl2Levi hE hdiv hlt.ne hc1 hc2 hind hsq
          have hc : ∀ u v, Commute (ρ i u) (ρ j v) := fun u v =>
            hcomm i j hlt.ne hij hji (ρ i u) (by rw [← hρ i]; exact ⟨u, rfl⟩) (ρ j v)
              (by rw [← hρ j]; exact ⟨v, rfl⟩)
          refine ⟨⟨SL(2, F) × SL(2, F), l, hl, hle⟩, (ρ i).noncommCoprod (ρ j) hc,
            fun k hk c => ?_⟩
          rcases hk with rfl | rfl
          · refine ⟨?_, ?_⟩
            · rw [preimage_eq_of_emb (hv c).1, MonoidHom.noncommCoprod_apply, map_one, mul_one]
            · rw [preimage_eq_of_emb (hv c).2.1, MonoidHom.noncommCoprod_apply, map_one, mul_one]
          · refine ⟨?_, ?_⟩
            · rw [preimage_eq_of_emb (hv c).2.2.1, MonoidHom.noncommCoprod_apply, map_one,
                one_mul]
            · rw [preimage_eq_of_emb (hv c).2.2.2, MonoidHom.noncommCoprod_apply, map_one,
                one_mul]
  choose E φ hspec using hloc
  have hsing : ∀ k, ∀ γ ∈ pairRoots D k k, ∀ g ∈ D.rootGroup γ, ∃ c,
      (γ = sroot k ∧ g = x (sroot k) c) ∨ (γ = -sroot k ∧ g = x (-sroot k) c) := by
    intro k γ hγ g hg
    obtain ⟨c, rfl⟩ := ((hE.param γ hγ.1).1 g).1 hg
    refine ⟨c, ?_⟩
    have hγ' := pairRoots_self_subset hdiv k hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ'
    rcases hγ' with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hcompat : ∀ i j (h : i ≤ j) k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots D k k,
      ∀ g ∈ D.rootGroup γ,
        φ i j h ((E i j h).preimage g) = φ k k le_rfl ((E k k le_rfl).preimage g) := by
    intro i j h k hk γ hγ g hg
    obtain ⟨c, hc⟩ := hsing k γ hγ g hg
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(hspec i j h k hk c).1, (hspec k k le_rfl k (Or.inl rfl) c).1]
    · rw [(hspec i j h k hk c).2, (hspec k k le_rfl k (Or.inl rfl) c).2]
  have hfmu : ∀ k c, frameMap E φ (Pi.single k 1) ⟨x (sroot k) c, hmem _ (hsr k).1 c⟩ =
      ρ k (tv 0 1 c) := by
    intro k c
    rw [frameMap_of_mem_self (Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (k := k)
      (Or.inl rfl)).1]
    exact (hspec k k le_rfl k (Or.inl rfl) c).1
  have hfmv : ∀ k c, frameMap E φ (-Pi.single k 1) ⟨x (-sroot k) c, hmem _ (hsr k).2 c⟩ =
      ρ k (tv 1 0 c) := by
    intro k c
    rw [frameMap_of_mem_self (Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (k := k)
      (Or.inl rfl)).2]
    exact (hspec k k le_rfl k (Or.inl rfl) c).2
  have hgen' : Subgroup.closure (⋃ k, Set.range (frameMap E φ (Pi.single k 1)) ∪
      Set.range (frameMap E φ (-Pi.single k 1))) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rw [← hρ k]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl
        ⟨⟨x (sroot k) c, hmem _ (hsr k).1 c⟩, hfmu k c⟩⟩)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr
        ⟨⟨x (-sroot k) c, hmem _ (hsr k).2 c⟩, hfmv k c⟩⟩)
  have hnt : ∃ k, ∃ y, frameMap E φ (Pi.single k 1) y ≠ 1 :=
    ⟨a, ⟨x (sroot a) 1, hmem _ (hsr a).1 1⟩, by
      rw [hfmu]
      intro h
      exact tv_zero_one_one_ne_one (hρa (h.trans (map_one _).symm))⟩
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩ :=
    CFSG.WeakCTLevi.exists_surjective_of_leviEmbeddings hCT hL E φ hcompat hgen' hnt
  refine ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ?_⟩
  have hΨu' : ∀ c, Ψ (x (sroot k) c) = ρ k (tv 0 1 c) := fun c => by
    have := hΨu k ⟨x (sroot k) c, hmem _ (hsr k).1 c⟩
    rw [hfmu] at this
    exact this
  have hΨv' : ∀ c, Ψ (x (-sroot k) c) = ρ k (tv 1 0 c) := fun c => by
    have := hΨv k ⟨x (-sroot k) c, hmem _ (hsr k).2 c⟩
    rw [hfmv] at this
    exact this
  rw [CurtisTits.rankOne, Subgroup.map_sup]
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := ((hE.param _ (hsr k).1).1 g).1 hg
      rw [hΨu' c]
      exact (hρU k c).1
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := ((hE.param _ (hsr k).2).1 g).1 hg
      rw [hΨv' c]
      exact (hρU k c).2
  · rw [← hρ k]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · exact Subgroup.mem_sup_left ⟨x (sroot k) c, hmem _ (hsr k).1 c, hΨu' c⟩
    · exact Subgroup.mem_sup_right ⟨x (-sroot k) c, hmem _ (hsr k).2 c, hΨv' c⟩

theorem weakCT_doublyLaced_leaf {F₀ : Type} [Field F₀] [Finite F₀] (e : F₀ ≃+* F) {t : StatedLieTag}
    {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hF : 4 ≤ Nat.card F₀) (h2 : (2 : F) ≠ 0)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {par : Fin D.rank → Fin D.rank} {dep : Fin D.rank → ℕ} {k₀ : Fin D.rank}
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀) (hpar : par b = a)
    (hb0 : b ≠ k₀) (hleaf : ∀ q, (adj b q ∨ adj q b) → q = a) {X : Type} [Group X]
    {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hpair : ∀ i j, adj i j → ¬ (i = a ∧ j = b) →
      ∃ W, LinearBlockStandardPair F₀ W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockPair F₀ W (U a) (U b)) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  have : Finite F := Finite.of_equiv F₀ e.toEquiv
  have hF' : 4 ≤ Nat.card F := by rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨ρ, hρ, hψ, ψ4, -, hψ41, hψ40⟩ :=
    exists_frame_of_tree_sp_leaf hF hT hroot hdiag.adj_ab hpar hb0 hleaf hcomm hpair hsp
  obtain ⟨Φ, hΦ⟩ := exists_spMap (F := F) e.symm.toRingHom
  let φ₂ : SL(2, F) →* SL(2, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let φ₃ : SL(3, F) →* SL(3, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rwa [map_symm_map, map_symm_map] at this
  have hφ₂surj : ∀ A : SL(2, F₀), ∃ B : SL(2, F), φ₂ B = A := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.toRingHom A, map_map_symm e A⟩
  have hne_ab : a ≠ b := fun h => by
    have hab := hdiag.adj_ab
    rw [h] at hab
    exact hT.asymm _ _ hab hab
  refine weakCT_of_frame_dl' hCT hL hE hdiv hF' h2 hdiag hind hsq hgen hcomm
    (ρ := fun k => (ρ k).comp φ₂) (fun k => ?_) (((hρ a).1 hne_ab).comp hφ₂inj)
    (fun i j hij hne => ?_) ⟨ψ4.comp Φ, ?_, ?_⟩
  · rw [← (hρ k).2]
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨φ₂ B, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  · obtain ⟨ψ', hψ0, hψ1⟩ := hψ i j hij hne
    refine ⟨ψ'.comp φ₃, ?_, ?_⟩
    · ext A
      show ψ' (φ₃ (blk F 0 A)) = ρ i (φ₂ A)
      rw [← hψ0, MonoidHom.comp_apply]
      exact congrArg ψ' (map_blk e.symm.toRingHom 0 A)
    · ext A
      show ψ' (φ₃ (blk F 1 A)) = ρ j (φ₂ A)
      rw [← hψ1, MonoidHom.comp_apply]
      exact congrArg ψ' (map_blk e.symm.toRingHom 1 A)
  · rw [MonoidHom.comp_assoc, spMap_comp_spBlock e.symm.toRingHom hΦ 1, ← MonoidHom.comp_assoc,
      hψ41]
  · rw [MonoidHom.comp_assoc, spMap_comp_spBlock e.symm.toRingHom hΦ 0, ← MonoidHom.comp_assoc,
      hψ40]

end Recognition

end CFSG.ClassicalInvolution.WeakCT
