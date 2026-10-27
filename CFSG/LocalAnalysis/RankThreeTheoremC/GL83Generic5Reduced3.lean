module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced2
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.AGLEmbedding (exists_mem_sylow_inf_component isElemAbelian_zpowers)

section Components

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem centralizer_layer_eq_bot_of_pCore_eq_bot [Fact p.Prime]
    (hcore : primeComplementCore (G := Y) p = ⊥) (hR : CFSG.pCore p Y = ⊥) :
    centralizer (CFSG.layer Y : Set Y) = ⊥ := by
  have hF : CFSG.fittingSubgroup Y = ⊥ := (CFSG.Fitting_eq_pcore Y p hcore).trans hR
  have hle : centralizer (CFSG.layer Y : Set Y) ≤ CFSG.layer Y := by
    have := CFSG.centralizer_generalizedFitting_le Y
    rwa [CFSG.generalizedFitting, hF, bot_sup_eq] at this
  have : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  have : IsMulCommutative (centralizer (CFSG.layer Y : Set Y)) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (mem_centralizer_iff.mp b.2 a (hle a.2))
  have hnil : Group.IsNilpotent (centralizer (CFSG.layer Y : Set Y)) := inferInstance
  exact le_bot_iff.mp (hF ▸ CFSG.LocalCores.fitting_characteristic.2.2 _ inferInstance hnil)

theorem center_eq_bot_of_centralizer_layer_eq_bot (hCE : centralizer (CFSG.layer Y : Set Y) = ⊥)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : center K = ⊥ := by
  have := CFSG.LocalCores.center_component_le_centralizer_layer
    ((CFSG.isComponent_iff_open K).mpr hK)
  rwa [hCE, le_bot_iff, map_eq_bot_iff_of_injective _ K.subtype_injective] at this

omit [Finite Y] in
theorem isSimpleGroup_of_isComponentOf_of_center_eq_bot {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hZ : center K = ⊥) : IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  let e : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
  refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba

theorem isElemAbelian_iSup_zpowers {ι : Type*} [DecidableEq ι] (hp : p.Prime)
    (K : ι → Subgroup Y) (t : ι → Y) (htp : ∀ i, t i ^ p = 1) (htK : ∀ i, t i ∈ K i)
    (htC : ∀ i, t i ∉ centralizer (K i : Set Y))
    (hKK : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set Y)) (s : Finset ι) :
    IsElemAbelian p (⨆ i ∈ s, zpowers (t i)) ∧
      Nat.card (⨆ i ∈ s, zpowers (t i) : Subgroup Y) = p ^ s.card := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iSup_of_empty, iSup_bot, card_bot, Finset.card_empty,
      pow_zero, and_true]
    exact ⟨inferInstance, fun g hg => by rw [mem_bot.mp hg, one_pow]⟩
  | @insert a s has ih =>
    obtain ⟨hE, hEc⟩ := ih
    have hEC : (⨆ i ∈ s, zpowers (t i)) ≤ centralizer (K a : Set Y) :=
      iSup₂_le fun i hi => zpowers_le.mpr (hKK i a (fun hia => has (hia ▸ hi)) (htK i))
    have htE : t a ∉ ⨆ i ∈ s, zpowers (t i) := fun h => htC a (hEC h)
    have hcomm : ∀ e ∈ ⨆ i ∈ s, zpowers (t i), e * t a = t a * e := fun e he =>
      (mem_centralizer_iff.mp (hEC he) (t a) (htK a)).symm
    rw [Finset.iSup_insert, sup_comm, Finset.card_insert_of_notMem has]
    refine ⟨CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hE
      (isElemAbelian_zpowers (htp a)) (le_centralizer_iff.mpr
        (zpowers_le.mpr (mem_centralizer_iff.mpr hcomm))), ?_⟩
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp _ (htp a) htE hcomm, hEc, pow_succ]

theorem card_le_pRank_of_isComponentOf (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : primeComplementCore (G := Y) p = ⊥) (s : Finset (Subgroup Y))
    (hs : ∀ K ∈ s, IsComponentOf K ⊤) : s.card ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow p Y))
  have ht : ∀ K : s, ∃ t ∈ (R : Subgroup Y) ⊓ (K : Subgroup Y), orderOf t = p ∧
      t ∉ centralizer ((K : Subgroup Y) : Set Y) := fun K =>
    exists_mem_sylow_inf_component hp hp2 hcore R (hs K K.2)
  choose t htR hto htC using ht
  have hKK : ∀ i j : s, i ≠ j → (i : Subgroup Y) ≤ centralizer ((j : Subgroup Y) : Set Y) :=
    fun i j hij => commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hs i i.2) (hs j j.2)
        fun h => hij (Subtype.ext h))
  obtain ⟨hE, hEc⟩ := isElemAbelian_iSup_zpowers hp (fun K : s => (K : Subgroup Y)) t
    (fun K => hto K ▸ pow_orderOf_eq_one (t K)) (fun K => (htR K).2) htC hKK Finset.univ
  rw [Finset.card_univ, Fintype.card_coe] at hEc
  exact le_pRank_of_elemAbelian_card le_top hE hEc

omit [Finite Y] in
theorem mem_normalizer_of_pow_mem (hp : p.Prime) {H : Subgroup Y} {y : Y} (hy : y ^ p = 1)
    {m : ℕ} (hm : Nat.Coprime m p) (hym : y ^ m ∈ normalizer (H : Set Y)) :
    y ∈ normalizer (H : Set Y) := by
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hp.one_lt
  have h1 : y = (y ^ m) ^ k := by
    rw [← pow_mul, pow_eq_pow_mod (m * k) hy, hk, pow_one]
  rw [h1]
  exact pow_mem hym k

theorem mem_normalizer_of_isComponentOf_of_pow_eq_one (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcore : primeComplementCore (G := Y) p = ⊥)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3) {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    {y : Y} (hy : y ^ p = 1) : y ∈ normalizer (K : Set Y) := by
  classical
  by_contra hyK
  set f : ℕ → Subgroup Y := fun i => K.map (MulAut.conj (y ^ i)).toMonoidHom with hf
  have hfK : ∀ i, IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (y ^ i)) K).mpr hK
  have hinj : Set.InjOn f (Finset.range 4 : Set ℕ) := by
    have key : ∀ i j : ℕ, i < j → j < 4 → f i ≠ f j := by
      intro i j hij hj hfij
      apply hyK
      refine mem_normalizer_of_pow_mem hp hy (m := j - i) ?_ ?_
      · exact (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
      · rw [mem_normalizer_iff_map_conj_eq]
        have h1 : f j = (f (j - i)).map (MulAut.conj (y ^ i)).toMonoidHom := by
          simp only [hf]
          rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
            Nat.add_sub_cancel' hij.le]
        rw [h1] at hfij
        exact (map_injective (MulAut.conj (y ^ i)).injective hfij).symm
    intro i hi j hj hfij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hfij (key i j h hj)
    · exact h
    · exact absurd hfij.symm (key j i h hi)
  have hcard := card_le_pRank_of_isComponentOf hp (by omega) hcore ((Finset.range 4).image f)
    (fun K' hK' => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK'
      exact hfK i)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  omega

end Components

namespace GL83Generic5CaseIIHyp

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {L U : Subgroup Y} {x : Y}

theorem le_normalizer_of_isComponentOf (h : GL83Generic5CaseIIHyp p L U x) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) : L ≤ normalizer (K : Set Y) := by
  have hΩK : normalClosure {y : Y | y ^ p = 1} ≤ normalizer (K : Set Y) := by
    refine closure_le _ |>.mpr fun z hz => ?_
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    refine mem_normalizer_of_isComponentOf_of_pow_eq_one h.prime h.five_le h.core_eq_bot
      h.pRank_le hK ?_
    rw [conj_pow, show a ^ p = 1 from ha, mul_one, mul_inv_cancel]
  have hUΩ : U ≤ normalClosure {y : Y | y ^ p = 1} := fun u hu =>
    subset_normalClosure (h.isElemAbelian.2 u hu)
  have := h.isSimpleGroup
  have : ((normalClosure {y : Y | y ^ p = 1}).subgroupOf L).Normal :=
    normalClosure_normal.subgroupOf L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((normalClosure {y : Y | y ^ p = 1}).subgroupOf L) with h1 | h1
  · exfalso
    apply h.ne_bot
    have h2 : normalClosure {y : Y | y ^ p = 1} ⊓ L = ⊥ := by
      rw [← subgroupOf_map_subtype, h1, Subgroup.map_bot]
    exact le_bot_iff.mp (h2 ▸ le_inf hUΩ h.sylow.le)
  · exact (subgroupOf_eq_top.mp h1).trans hΩK

theorem exists_isComponentOf_not_le_centralizer (h : GL83Generic5CaseIIHyp p L U x)
    (hCE : centralizer (CFSG.layer Y : Set Y) = ⊥) :
    ∃ K : Subgroup Y, IsComponentOf K ⊤ ∧ ¬ L ≤ centralizer (K : Set Y) := by
  by_contra hall
  push Not at hall
  have hLE : L ≤ centralizer (CFSG.layer Y : Set Y) := le_centralizer_iff.mpr
    (sSup_le fun K hK => le_centralizer_iff.mp (hall K ((CFSG.isComponent_iff_open K).mp hK)))
  rw [hCE] at hLE
  exact h.ne_bot (le_bot_iff.mp (h.sylow.le.trans hLE))

theorem map_conj_eq_of_isComponentOf (h : GL83Generic5CaseIIHyp p L U x)
    (hL : IsComponentOf L ⊤) (g : Y) : L.map (MulAut.conj g).toMonoidHom = L := by
  by_contra hne
  have hLg : IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  have hC : L.map (MulAut.conj g).toMonoidHom ≤ centralizer (L : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLg hL hne)
  have hV := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p h.isElemAbelian
    (MulAut.conj g).toMonoidHom
  have hVc : Nat.card (U.map (MulAut.conj g).toMonoidHom) = p ^ 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective, h.card_eq]
  have hVL : U.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom :=
    map_mono h.sylow.le
  have h4 := add_le_pRank_of_commute (P := ⊤) h.isElemAbelian hV h.card_eq hVc
    (fun a ha b hb => mem_centralizer_iff.mp (hC (hVL hb)) a (h.sylow.le ha))
    (disjoint_def.mpr fun hu hv => h.eq_one_of_mem_centralizer (h.sylow.le hu) (hC (hVL hv)))
    le_top le_top
  have := h.pRank_le
  omega

end GL83Generic5CaseIIHyp

end CFSG.LocalAnalysis.RankThreeTheoremC
