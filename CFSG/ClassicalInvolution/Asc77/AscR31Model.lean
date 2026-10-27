module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDWeak
public import CFSG.ClassicalInvolution.WeakCT.DLWeakAgree
public import CFSG.Timmesfeld.RankTwo.LevisSpin
import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes
import CFSG.ClassicalInvolution.RouteD.TypeDAdapt
import CFSG.ClassicalInvolution.RouteD.TypeTwistedDNodes
import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
import CFSG.ClassicalInvolution.Balance.LayerGenerationSimple
import CFSG.ClassicalInvolution.Balance.QNineStandard
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace R31

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)

variable {p f : ℕ} [Fact p.Prime]


theorem surjective_hom_of_card_eq_one {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (D : LieSystemData p f G Ω) (hc : D.card = 1) (i : Fin D.card) :
    Function.Surjective (D.hom i) := by
  have hsub : Subsingleton (Fin D.card) := by rw [hc]; infer_instance
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  calc (⊤ : Subgroup G) = ⨆ j, (D.hom j).range := D.generate.symm
    _ ≤ (D.hom i).range := iSup_le fun j => by rw [Subsingleton.elim j i]


theorem chainB3_aux (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G]
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (ψ : (modelUniv .POmegaOdd 3 p f Fact.out).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .POmegaOdd 3 p f Fact.out).K)
    (hsurj : Function.Surjective ψ)
    (hmeet : ∃ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 p f Fact.out).D,
      R.map ψ ∈ Ω) :
    ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
      (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
      (∃ V, SymplecticBlockPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤ := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hFcard]; omega
  have h5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hFcard]; exact hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hn : 3 ≤ 3 := le_rfl
  have hadm : StatedLieAdmissible .POmegaOdd 3 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf, hn, hp2⟩
  let R : Fin 3 → Subgroup (modelUniv .POmegaOdd 3 p f Fact.out).K :=
    fun k => rankOne (modelUniv .POmegaOdd 3 p f Fact.out).D.rootGroup k
  have hRmem : ∀ k : Fin 3, k.val + 1 < 3 →
      R k ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 p f Fact.out).D :=
    fun k hk => rankOne_mem_fundamentalSubgroups_oddDatum hn hk
  refine ⟨fun k => (R k).map ψ, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨R₀, hR₀, hR₀Ω⟩ := hmeet
    have hsc : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd 3 p f Fact.out).D :=
      CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd 3 p f Fact.out
        trivial hadm (by decide) (by decide)
    obtain ⟨g, hg⟩ := hsc R₀ hR₀ (R 0) (hRmem 0 (by norm_num))
    show (R 0).map ψ ∈ Ω
    rw [hg, ← conjSub_map]
    exact hΩ _ _ hR₀Ω
  · exact commutes_map ψ (commutes_rankOne_oddDatum hn h2
      (cartanB_eq_zero_of_far (i := (0 : Fin 3)) (j := (2 : Fin 3)) (Or.inl (by simp))))
  · obtain ⟨W, hW⟩ := standardPair_oddDatum_edge (F := GaloisField p f) hn (i := 0) (by norm_num)
    exact ⟨_, CFSG.ClassicalInvolution.Balance.linearBlockStandardPair_map_of_ker_le_center hW ψ
      hker⟩
  · obtain ⟨W, hW⟩ := symplecticPair_oddDatum (F := GaloisField p f) h4 h2 hn
    exact ⟨_, symplecticBlockPair_map_central h5 hW ψ hker⟩
  · have hgen := CFSG.ClassicalInvolution.Balance.iSup_rankOneRoot_simple_eq_top .POmegaOdd 3 p f
      Fact.out trivial hadm 1
    have hR : ⨆ k : Fin 3, R k = ⊤ := by
      refine eq_top_iff.mpr (le_of_eq_of_le hgen.symm (iSup_mono fun k => ?_))
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hc : (MulEquiv.toMonoidHom (MulAut.conj
          (1 : (modelUniv .POmegaOdd 3 p f Fact.out).K))) y = y := by simp
      rw [hc]
      exact hy
    have hmap : (⨆ k : Fin 3, R k).map ψ = ⨆ k : Fin 3, (R k).map ψ := Subgroup.map_iSup ψ R
    show ⨆ k : Fin 3, (R k).map ψ = ⊤
    rw [← hmap, hR, Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj]


open CFSG.Timmesfeld (edgeD)

theorem chainD4_aux (hq : 5 ≤ p ^ f) {G : Type} [Group G]
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (ψ : (modelUniv .POmegaPlus 4 p f Fact.out).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .POmegaPlus 4 p f Fact.out).K)
    (hsurj : Function.Surjective ψ)
    (hmeet : ∃ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 p f Fact.out).D,
      R.map ψ ∈ Ω) :
    ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
      (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 4, edgeD 4 i j →
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) ∧ ⨆ k, U k = ⊤ := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hm3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf, by show 4 ≤ 4; exact le_rfl⟩
  set Dm := (modelUniv .POmegaPlus 4 p f Fact.out).D with hDm
  obtain ⟨e, he⟩ := exists_equiv_cartan_plus (p := p) (f := f) hm3
  have hR : ∀ a, rankOne Dm.rootGroup a ∈ fundamentalSubgroups .POmegaPlus Dm := by
    rw [hDm, modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
    exact fun a => rankOne_mem_fundamentalSubgroups_plusDatum hm3 a
  have hcomm : ∀ a b : Fin Dm.rank, Dm.cartan a b = 0 →
      Commutes (rankOne Dm.rootGroup a) (rankOne Dm.rootGroup b) := by
    rw [hDm, modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
    exact fun a b h => commutes_rankOne_plusDatum hm3 h
  have hstd : ∀ a b : Fin Dm.rank, Dm.cartan a b = -1 →
      ∃ W : Subgroup (modelUniv .POmegaPlus 4 p f Fact.out).K,
        LinearBlockStandardPair (GaloisField p f) W (rankOne Dm.rootGroup a)
          (rankOne Dm.rootGroup b) := by
    rw [hDm, modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
    exact fun a b h => standardPair_plusDatum_of_cartan hm3 h
  have hsc : FundamentalSingleClass .POmegaPlus Dm :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus 4 p f Fact.out
      trivial hadm (by decide) (by decide)
  have heinj : ∀ a b, a ≠ b → e a ≠ e b := fun a b hab h => hab (e.injective h)
  refine ⟨fun k => (rankOne Dm.rootGroup (e.symm k)).map ψ, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨R₀, hR₀, hR₀Ω⟩ := hmeet
    obtain ⟨g, hg⟩ := hsc R₀ hR₀ _ (hR (e.symm k))
    show (rankOne Dm.rootGroup (e.symm k)).map ψ ∈ Ω
    rw [hg, ← conjSub_map]
    exact hΩ _ _ hR₀Ω
  · intro i j hij h1 h2
    refine commutes_map ψ (hcomm _ _ ?_)
    have hh := (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD hij h1 h2).1
    have h0 := he (e.symm i) (e.symm j)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h0
    exact h0.trans hh
  · intro i j hij
    obtain ⟨W, hW⟩ := hstd (e.symm i) (e.symm j) (by
      have hh := (CFSG.Timmesfeld.LevisSpin.cartanD_of_edgeD hij).1
      have h0 := he (e.symm i) (e.symm j)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h0
      exact h0.trans hh)
    exact ⟨_, CFSG.ClassicalInvolution.Balance.linearBlockStandardPair_map_of_ker_le_center hW ψ
      hker⟩
  · have hgen := CFSG.ClassicalInvolution.Balance.iSup_rankOneRoot_simple_eq_top .POmegaPlus 4 p f
      Fact.out trivial hadm 1
    have hRtop : ⨆ a : Fin Dm.rank, rankOne Dm.rootGroup a = ⊤ := by
      refine eq_top_iff.mpr (le_of_eq_of_le hgen.symm (iSup_mono fun k => ?_))
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hc : (MulEquiv.toMonoidHom (MulAut.conj
          (1 : (modelUniv .POmegaPlus 4 p f Fact.out).K))) y = y := by simp
      rw [hc]
      exact hy
    have hmap : (⨆ a : Fin Dm.rank, rankOne Dm.rootGroup a).map ψ =
        ⨆ a : Fin Dm.rank, (rankOne Dm.rootGroup a).map ψ := Subgroup.map_iSup ψ _
    rw [hRtop, Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj] at hmap
    rw [← Equiv.iSup_comp e.symm] at hmap
    exact hmap.symm


open CFSG.LieType.Universal.Spin.Twisted (minusDatum fact_shortField minusDatum_steinbergExtras)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel)

theorem chainMinus4_aux (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G]
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (ψ : (modelUniv .POmegaMinus 4 p f Fact.out).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .POmegaMinus 4 p f Fact.out).K)
    (hsurj : Function.Surjective ψ)
    (hmeet : ∃ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D,
      R.map ψ ∈ Ω) :
    ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
      (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
      (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤ := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hn4 : 4 ≤ 4 := le_rfl
  have hirr := minusCoeffs_irr p f
  have := fact_shortField hirr
  have hadm : StatedLieAdmissible .POmegaMinus 4 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf, hn4⟩
  let R : Fin 3 → Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K :=
    fun k => rankOne (modelUniv .POmegaMinus 4 p f Fact.out).D.rootGroup k
  have hRmem : ∀ k : Fin 3, k.val + 1 < 3 →
      R k ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D :=
    fun k hk => rankOne_mem_fund_minus hirr hk
  refine ⟨fun k => (R k).map ψ, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨R₀, hR₀, hR₀Ω⟩ := hmeet
    have hsc : FundamentalSingleClass .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D :=
      CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus 4 p f Fact.out
        trivial hadm (by decide) (by decide)
    obtain ⟨g, hg⟩ := hsc R₀ hR₀ (R 0) (hRmem 0 (by norm_num))
    show (R 0).map ψ ∈ Ω
    rw [hg, ← conjSub_map]
    exact hΩ _ _ hR₀Ω
  · refine commutes_map ψ ?_
    exact commutes_rankOne_of_cartan_eq_zero_of_longest (minusDatum 4 hirr)
      (minusDatum_steinbergExtras 4 hirr)
      (i := (0 : Fin 3)) (j := (2 : Fin 3))
      (isLongestRoot_node_minus hirr (n := 4) (k := (0 : Fin 3)) (by norm_num)).2
      (cartanB_eq_zero_of_far (n := 3) (i := (0 : Fin 3)) (j := (2 : Fin 3)) (Or.inl (by simp)))
  · obtain ⟨W, hW⟩ := (CFSG.ClassicalInvolution.ModelFacts.standardPair_minusDatum
      (F := GaloisField p f) hn4 h2 hirr).2
    exact ⟨_, CFSG.ClassicalInvolution.Balance.linearBlockStandardPair_map_of_ker_le_center hW ψ
      hker⟩
  · obtain ⟨θ, hθinj, hθlb, hθL, hθS⟩ := exists_twistedB2_minusDatum_inj (hirr := hirr) h2 hn4
      (i := (⟨1, by norm_num⟩ : Fin (4 - 1))) (j := (⟨2, by norm_num⟩ : Fin (4 - 1))) rfl rfl
    have hfn := CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p
    have key : ∀ r ∈ R 1, r ∈ ψ.ker → r = 1 := fun r hr hrk =>
      hfn .POmegaMinus 4 f trivial hadm (by simp) (R 1) (hRmem 1 (by norm_num)) r hr (fun y => by
        have hc : r ∈ Subgroup.center _ := hker hrk
        have h1 : y * r = r * y := Subgroup.mem_center_iff.mp hc y
        have h2' : r * y * r⁻¹ * y⁻¹ = 1 := by rw [← h1]; group
        rw [h2']
        exact one_mem _)
    let θ' : spinGroup (quadMinus 3 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) →* (modelUniv .POmegaMinus 4 p f Fact.out).K := θ
    have hθinj' : Function.Injective θ' := hθinj
    have hθlb' : Function.Injective (θ'.comp (spinMinusModel hirr).lb) := hθlb
    have hθL' : Subgroup.map θ' (spinMinusModel hirr).lb.range = R 1 := hθL
    have hθS' : Subgroup.map θ' (spinMinusModel hirr).sb.range = R 2 := hθS
    refine ⟨(ψ.comp θ').range, ?_⟩
    unfold TwistedB2BlockPair
    refine ⟨ψ.comp θ', rfl, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxc : θ' x ∈ Subgroup.center (modelUniv .POmegaMinus 4 p f Fact.out).K := hker hx
      rw [Subgroup.mem_center_iff] at hxc ⊢
      intro y
      apply hθinj'
      rw [map_mul, map_mul]
      exact hxc (θ' y)
    · intro a b hab
      simp only [MonoidHom.comp_apply] at hab
      have hr : θ' ((spinMinusModel hirr).lb (a⁻¹ * b)) ∈ R 1 := by
        have h : θ' ((spinMinusModel hirr).lb (a⁻¹ * b)) ∈
            Subgroup.map θ' (spinMinusModel hirr).lb.range := ⟨_, ⟨_, rfl⟩, rfl⟩
        rw [hθL'] at h
        exact h
      have hrk : θ' ((spinMinusModel hirr).lb (a⁻¹ * b)) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hab, inv_mul_cancel]
      have h1 := key _ hr hrk
      have h3 : θ' ((spinMinusModel hirr).lb (a⁻¹ * b)) = θ' ((spinMinusModel hirr).lb 1) := by
        rw [map_one, map_one]
        exact h1
      have h4 : a⁻¹ * b = 1 := hθlb' h3
      exact inv_mul_eq_one.mp h4
    · rw [← Subgroup.map_map, hθL']
    · rw [← Subgroup.map_map, hθS']
  · have hgen := CFSG.ClassicalInvolution.Balance.iSup_rankOneRoot_simple_eq_top .POmegaMinus 4 p f
      Fact.out trivial hadm 1
    have hR : ⨆ k : Fin 3, R k = ⊤ := by
      refine eq_top_iff.mpr (le_of_eq_of_le hgen.symm (iSup_mono fun k => ?_))
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hc : (MulEquiv.toMonoidHom (MulAut.conj
          (1 : (modelUniv .POmegaMinus 4 p f Fact.out).K))) y = y := by simp
      rw [hc]
      exact hy
    have hmap : (⨆ k : Fin 3, R k).map ψ = ⨆ k : Fin 3, (R k).map ψ := Subgroup.map_iSup ψ R
    show ⨆ k : Fin 3, (R k).map ψ = ⊤
    rw [← hmap, hR, Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj]

theorem chainB3_of_lieSystem (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G]
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (D : LieSystemData p f G Ω)
    (hc : D.card = 1) {i : Fin D.card} (ht : D.tag i = .POmegaOdd) (hr : D.rank i = 3) :
    ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
      (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
      (∃ V, SymplecticBlockPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤ := by
  have hex : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h (by decide)
  have key : ∀ (t : StatedLieTag) (n e : ℕ), t = .POmegaOdd → n = 3 → e = f →
      ∀ (ψ : (modelUniv t n p e Fact.out).K →* G),
        ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K → Function.Surjective ψ →
        (∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R.map ψ ∈ Ω) →
        ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
          (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
          (∃ V, SymplecticBlockPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤ := by
    intro t n e ht hn he ψ hker hsurj hmeet
    subst ht hn he
    exact chainB3_aux hp2 hq hΩ ψ hker hsurj hmeet
  exact key _ _ _ ht hr hex (D.hom i) (D.ker_le_center i)
    (surjective_hom_of_card_eq_one D hc i) (D.meets i)

theorem chainD4_of_lieSystem (hq : 5 ≤ p ^ f) {G : Type} [Group G]
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (D : LieSystemData p f G Ω)
    (hc : D.card = 1) {i : Fin D.card} (ht : D.tag i = .POmegaPlus) (hr : D.rank i = 4) :
    ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
      (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 4, edgeD 4 i j →
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) ∧ ⨆ k, U k = ⊤ := by
  have hex : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h (by decide)
  have key : ∀ (t : StatedLieTag) (n e : ℕ), t = .POmegaPlus → n = 4 → e = f →
      ∀ (ψ : (modelUniv t n p e Fact.out).K →* G),
        ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K → Function.Surjective ψ →
        (∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R.map ψ ∈ Ω) →
        ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
          (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
          (∀ i j : Fin 4, edgeD 4 i j →
            ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) ∧ ⨆ k, U k = ⊤ := by
    intro t n e ht hn he ψ hker hsurj hmeet
    subst ht hn he
    exact chainD4_aux hq hΩ ψ hker hsurj hmeet
  exact key _ _ _ ht hr hex (D.hom i) (D.ker_le_center i)
    (surjective_hom_of_card_eq_one D hc i) (D.meets i)

theorem chainMinus4_of_lieSystem (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G]
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (D : LieSystemData p f G Ω)
    (hc : D.card = 1) {i : Fin D.card} (ht : D.tag i = .POmegaMinus) (hr : D.rank i = 4) :
    ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
      (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
      (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤ := by
  have hex : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h (by decide)
  have key : ∀ (t : StatedLieTag) (n e : ℕ), t = .POmegaMinus → n = 4 → e = f →
      ∀ (ψ : (modelUniv t n p e Fact.out).K →* G),
        ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K → Function.Surjective ψ →
        (∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R.map ψ ∈ Ω) →
        ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
          (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
          (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤ := by
    intro t n e ht hn he ψ hker hsurj hmeet
    subst ht hn he
    exact chainMinus4_aux hp2 hq hΩ ψ hker hsurj hmeet
  exact key _ _ _ ht hr hex (D.hom i) (D.ker_le_center i)
    (surjective_hom_of_card_eq_one D hc i) (D.meets i)

end R31

end CFSG.ClassicalInvolution.Asc77
