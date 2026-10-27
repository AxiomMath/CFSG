module

public import CFSG.ClassicalInvolution.Q3.Q3VCtLevi
public import CFSG.ClassicalInvolution.WeakCT.Symplectic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem weakCT_of_frame_dl_of_sp4Levi [Finite F] {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    (hSp4 : ∃ φ : StatedSp 2 F →* K, Function.Injective φ ∧
      (∀ γ ∈ pairRoots D b a, D.rootGroup γ ≤ φ.range) ∧
      ∀ c, φ (spBlock F 0 (tv 0 1 c)) = x (sroot b) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = x (-sroot b) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = x (sroot a) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = x (-sroot a) c)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j)
    (hψ4 : ∃ ψ : StatedSp 2 F →* X, ψ.comp (spBlock F 1) = ρ a ∧ ψ.comp (spBlock F 0) = ρ b) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  classical
  obtain ⟨-, -, -, hadj, hnadj, hnb⟩ := hdiag
  obtain ⟨ψ4, hψ41, hψ40⟩ := hψ4
  have hρU : ∀ k c, ρ k (tv 0 1 c) ∈ U k ∧ ρ k (tv 1 0 c) ∈ U k := fun k c => by
    rw [← (hρ k).2]
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
          obtain ⟨φ, hφinj, hφle, hφv⟩ := hSp4
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
            obtain ⟨φ, hφinj, hφle, hφv⟩ := hSp4
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
            hcomm i j hlt.ne hij hji (ρ i u) (by rw [← (hρ i).2]; exact ⟨u, rfl⟩) (ρ j v)
              (by rw [← (hρ j).2]; exact ⟨v, rfl⟩)
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
    rw [← (hρ k).2]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl
        ⟨⟨x (sroot k) c, hmem _ (hsr k).1 c⟩, hfmu k c⟩⟩)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr
        ⟨⟨x (-sroot k) c, hmem _ (hsr k).2 c⟩, hfmv k c⟩⟩)
  have hnt : ∃ k, ∃ y, frameMap E φ (Pi.single k 1) y ≠ 1 :=
    ⟨a, ⟨x (sroot a) 1, hmem _ (hsr a).1 1⟩, by
      rw [hfmu]
      intro h
      exact tv_zero_one_one_ne_one ((hρ a).1 (h.trans (map_one _).symm))⟩
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
  · rw [← (hρ k).2]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · exact Subgroup.mem_sup_left ⟨x (sroot k) c, hmem _ (hsr k).1 c, hΨu' c⟩
    · exact Subgroup.mem_sup_right ⟨x (-sroot k) c, hmem _ (hsr k).2 c, hΨv' c⟩

end Recognition

section Symplectic

theorem weakCT_symplectic_of_family {n p f : ℕ} (hadm : StatedLieAdmissible .PSp n p f)
    (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (ρ : Fin n → SL(2, F) →* X) (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (ψ : ∀ i : Fin n, i.val + 2 < n → SL(3, F) →* X)
    (hψ0 : ∀ (i : Fin n) (h : i.val + 2 < n),
      (ψ i h).comp (blk F 0) = ρ ⟨i.val + 1, by omega⟩)
    (hψ1 : ∀ (i : Fin n) (h : i.val + 2 < n), (ψ i h).comp (blk F 1) = ρ i)
    (ψ4 : StatedSp 2 F →* X)
    (hψ4l : ψ4.comp (spBlock F 1) = ρ ⟨n - 1, by omega⟩)
    (hψ4s : ψ4.comp (spBlock F 0) = ρ ⟨n - 2, by omega⟩) :
    ∃ Ψ : StatedSp n F →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (StatedSp n F)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSp n p f ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup k).map Ψ = U k := by
  have hn1 : n - 1 < n := by omega
  have hn2 : n - 2 < n := by omega
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Symplectic.rootDatum n F).isFiniteType
    (Dv := (Symplectic.rootDatum n F).divisible) rfl
  have hE := Steinberg.Sp.chevalleyExtras (by omega : 2 ≤ n) O Steinberg.Sp.commC
    (Steinberg.Sp.commutatorFormula O)
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a.val + 1 = n := ⟨⟨n - 1, hn1⟩, by simp only; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b.val + 2 = n := ⟨⟨n - 2, hn2⟩, by simp only; omega⟩
  have hsq : ∀ k : Fin n,
      Steinberg.weylElement (Steinberg.Sp.x n F) k 1 ^ 2 ∈ Symplectic.torus n F k := by
    intro k
    rw [weylElement_sp_one]
    exact (Symplectic.isCTGroupDatum n F).sq_mem k
  have hcomm' : ∀ i j : Fin n, i ≠ j → ¬ edgeDown n i j → ¬ edgeDown n j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hne h1 h2 u hu v hv
    simp only [edgeDown] at h1 h2
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm i j (by omega) u hu v hv
    · exact (hcomm j i (by omega) v hv u hu).symm
  have hψ' : ∀ i j : Fin n, edgeDown n i j → ¬ (i = a ∧ j = b) →
      ∃ ψ' : SL(3, F) →* X, ψ'.comp (blk F 0) = ρ i ∧ ψ'.comp (blk F 1) = ρ j := by
    intro i j hij hn'
    simp only [edgeDown] at hij
    have hj2 : j.val + 2 < n := by
      have := i.2
      by_contra hc
      exact hn' ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    obtain rfl : i = ⟨j.val + 1, Nat.lt_of_succ_lt hj2⟩ := Fin.ext hij.symm
    exact ⟨ψ j hj2, hψ0 j hj2, hψ1 j hj2⟩
  have hψ4' : ∃ ψ' : StatedSp 2 F →* X, ψ'.comp (spBlock F 1) = ρ a ∧
      ψ'.comp (spBlock F 0) = ρ b := by
    obtain rfl : a = ⟨n - 1, hn1⟩ := Fin.ext (by simp only; omega)
    obtain rfl : b = ⟨n - 2, hn2⟩ := Fin.ext (by simp only; omega)
    exact ⟨ψ4, hψ4l, hψ4s⟩
  exact weakCT_of_frame_dl_of_sp4Levi (CurtisTits.curtisTitsConclusion_symplectic hadm hF hn)
    (leviConePresented_symplectic n F) hE rfl (doubleBondDiagram_cartanC hn ha hb)
    (exists_sp4Levi_sp hb ha) (Symplectic.steinbergExtras n F).torus_iSupIndep hsq hgen hcomm'
    hρ hψ' hψ4'

end Symplectic

end CFSG.ClassicalInvolution.Q3.Q3V
