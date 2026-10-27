module

public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructureAux
public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem isPGroup_iSup_sup_of_pairwise_commutator_le {p : ℕ} {ι : Type*} [Finite ι]
    (A : ι → Subgroup G) {Q : Subgroup G} (hQ : IsPGroup p Q) (hA : ∀ i, IsPGroup p (A i))
    (hAQ : ∀ i, A i ≤ Subgroup.normalizer (Q : Set G)) (hc : Pairwise fun i j => ⁅A i, A j⁆ ≤ Q) :
    IsPGroup p ((⨆ i, A i) ⊔ Q : Subgroup G) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, IsPGroup p ((⨆ i ∈ s, A i) ⊔ Q : Subgroup G) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show (⨆ i ∈ (∅ : Finset ι), A i : Subgroup G) = ⊥ by simp, bot_sup_eq]
      exact hQ
    | insert a s ha ih =>
      rw [Finset.iSup_insert, sup_assoc]
      refine (hA a).to_sup_of_normal_right' ih (le_normalizer_of_forall_map_conj_le fun x hx =>
        Subgroup.map_le_iff_le_comap.mpr (sup_le (iSup₂_le fun i hi y hy => ?_) fun q hq => ?_))
      · have hai : a ≠ i := fun he => ha (he ▸ hi)
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_right (hc hai (Subgroup.commutator_mem_commutator hx hy)))
          (Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi hy)))
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hAQ a hx) q).mp hq)
  have hall := key Finset.univ
  rwa [show (⨆ i ∈ (Finset.univ : Finset ι), A i : Subgroup G) = ⨆ i, A i by simp] at hall

theorem charTwo_of_twoCore_le {M X : Subgroup G} (hM : CharTwo M) (hQX : pCoreOf 2 M ≤ X)
    (hXM : X ≤ M) : CharTwo X := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hM hXM hQX

theorem map_inclusion_subgroupOf {X L M : Subgroup G} (hXL : X ≤ L) (hLM : L ≤ M) :
    (X.subgroupOf L).map (Subgroup.inclusion hLM) = X.subgroupOf M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hXL hx⟩, hx, rfl⟩

end General

section Bar

variable {G : Type} [Group G]

theorem isSylowTwoOf_inf_of_barM {M S L : Subgroup G} (hLM : L ≤ M) (hQS : pCoreOf 2 M ≤ S)
    (hS : IsPGroup 2 S) (h : IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) :
    IsSylowTwoOf (S ⊓ L) L := by
  refine ⟨inf_le_right, hS.to_le inf_le_left, ?_⟩
  let f := (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM)
  have hbar : ∀ X ≤ L, barM M X = (X.subgroupOf L).map f := fun X hX => by
    rw [barM, ← map_inclusion_subgroupOf hX hLM, Subgroup.map_map]
  have hker : f.ker ≤ (S ⊓ L).subgroupOf L := fun x hx => by
    have h1 : Subgroup.inclusion hLM x ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨_, h1, rfl⟩
    exact ⟨hQS h2, x.2⟩
  have hidx : ((barM M (S ⊓ L)).subgroupOf (barM M L)).index =
      ((S ⊓ L).subgroupOf L).index := by
    change (barM M (S ⊓ L)).relIndex (barM M L) = _
    rw [hbar _ inf_le_right, hbar L le_rfl, Subgroup.subgroupOf_self, Subgroup.relIndex_map_map,
      sup_of_le_left hker, top_sup_eq, Subgroup.relIndex_top_right]
  rw [← hidx]
  exact h.2.2

end Bar

section Asc81bHyp

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem Asc81bHyp.le_of_le_twoPrimeComponent (hA : Asc81bHyp M S)
    (hL : IsTwoPrimeComponent M L) {U : Subgroup G} (hUL : U ≤ L) (hU : IsPGroup 2 U)
    (hN : M ⊓ Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (U : Set G)) : U ≤ S := by
  let K := M ⊓ Subgroup.normalizer (S : Set G)
  let C : Set (Subgroup G) := {V | ∃ k ∈ K, V = U.map (MulAut.conj k).toMonoidHom}
  have hQM : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  have hCM : ∀ V ∈ C, V ≤ M := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.map_mono (hUL.trans hL.le)).trans
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hk.1)).le
  have hCp : IsPGroup 2 ((sSup C : Subgroup G) ⊔ pCoreOf 2 M : Subgroup G) := by
    rw [sSup_eq_iSup']
    refine isPGroup_iSup_sup_of_pairwise_commutator_le _ (pCoreOf_isPGroup 2 M) ?_
      (fun V => (hCM V.1 V.2).trans hQM) ?_
    · rintro ⟨V, k, hk, rfl⟩
      exact hU.map _
    · rintro ⟨V, k, hk, rfl⟩ ⟨V', k', hk', rfl⟩ hne
      have hLne : L.map (MulAut.conj k).toMonoidHom ≠ L.map (MulAut.conj k').toMonoidHom :=
        fun he => hne (Subtype.ext (map_conj_eq_of_map_conj_eq hN hk hk' he))
      exact (Subgroup.commutator_mono (Subgroup.map_mono hUL) (Subgroup.map_mono hUL)).trans
        ((hL.map_conj hk.1).commutator_le (hL.map_conj hk'.1) hLne)
  have hCN : K ≤ Subgroup.normalizer (((sSup C : Subgroup G) ⊔ pCoreOf 2 M : Subgroup G) :
      Set G) := by
    refine (le_inf ?_ (inf_le_left.trans hQM)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
    refine Subgroup.map_le_iff_le_comap.mpr (sSup_le ?_)
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.map_le_iff_le_comap.mp (le_sSup ⟨g * k, K.mul_mem hg hk, ?_⟩)
    rw [map_conj_mul_eq]
  have hUC : U ≤ (sSup C : Subgroup G) := le_sSup ⟨1, K.one_mem, by ext x; simp⟩
  exact (hUC.trans le_sup_left).trans (le_of_two_radical hA.twoRadical.1
    hA.twoRadical.2.2 (sup_le (sSup_le hCM) (pCoreOf_le 2 M)) hCp hCN)

theorem Asc81bHyp.twoCore_eq_pCoreOf_normalizer_sup (hA : Asc81bHyp M S)
    (hL : IsTwoPrimeComponent M L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    S = pCoreOf 2 ((L ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) := by
  set Y := (L ⊔ S) ⊓ Subgroup.normalizer (S : Set G)
  have hSY : S ≤ Y := le_inf le_sup_right Subgroup.le_normalizer
  have hST : S ≤ pCoreOf 2 Y := normal_pGroup_le_pCoreOf 2 S Y hSY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hSY).mpr inf_le_right) hA.twoRadical.isPGroup
  have hU : pCoreOf 2 Y ⊓ L ≤ S := by
    refine hA.le_of_le_twoPrimeComponent hL inf_le_right
      ((pCoreOf_isPGroup 2 Y).to_le inf_le_left) fun g hg => ?_
    have hgY : g ∈ Subgroup.normalizer (Y : Set G) := Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hg.2, hg.1.2⟩,
        Subgroup.le_normalizer hg.1.2⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨normalizer_localGroup_le_normalizer_pCoreOf 2 Y hgY, hg.2⟩
  refine le_antisymm hST fun t ht => ?_
  have htLS : t ∈ ((S ⊔ L : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact ((pCoreOf_le 2 Y).trans inf_le_left) ht
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S L hSL] at htLS
  obtain ⟨s, hs, l, hl, rfl⟩ := htLS
  have hlT : l ∈ pCoreOf 2 Y := by
    have := (pCoreOf 2 Y).mul_mem ((pCoreOf 2 Y).inv_mem (hST hs)) ht
    rwa [inv_mul_cancel_left] at this
  exact S.mul_mem hs (hU ⟨hlT, hl⟩)

omit [Finite G] in
theorem Asc81bHyp.cgsIn_eq_of_le (hA : Asc81bHyp M S) {X : Subgroup G} (hXM : X ≤ M) :
    cgsIn X S = X ⊓ Subgroup.normalizer (S : Set G) := by
  refine le_antisymm ?_ (inf_normalizer_le_cgsIn hA.twoRadical.2.1)
  refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have h1 : M ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn M S :=
    le_iSup_of_le C (le_iSup_of_le hCS (le_iSup_of_le hC1 (le_iSup_of_le hchar le_rfl)))
  rw [hA.cgs] at h1
  intro x hx
  exact ⟨hx.1, (h1 ⟨hXM hx.1, hx.2⟩).2⟩

theorem Asc81bHyp.weakSBlock_asc81bHyp (hA : Asc81bHyp M S) (hK : Open.IsKGroup ↥M)
    (hQS : pCoreOf 2 M ≤ S) (h86 : Asc81bEightSix) (hL : IsWeakSBlock M S L) :
    S ≤ Subgroup.normalizer (L : Set G) ∧ Asc81bHyp (L ⊔ S) S := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    hL.toIsTwoPrimeComponent.le_normalizer (h86 G M S hK hA _ hL.component) hA.twoRadical.1
  refine ⟨hSL, ⟨le_sup_right, hA.twoRadical.2.1,
    hA.twoCore_eq_pCoreOf_normalizer_sup hL.toIsTwoPrimeComponent hSL⟩,
    charTwo_of_twoCore_le hA.charTwo (hQS.trans le_sup_right) (sup_le hL.le hA.twoRadical.1),
    hA.cgsIn_eq_of_le (sup_le hL.le hA.twoRadical.1)⟩

open CFSG.AGLEmbeddingD2 (NoXBlockFor) in
theorem Asc81bHyp.oddCore_le_centralizer (hA : Asc81bHyp M S) (hK : Open.IsKGroup ↥M)
    (hM : GLBIsMaxTwoLocal M) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) :
    CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) ≤ Subgroup.centralizer (barM M S : Set _) := by
  rcases h84 G M S hK hA with h1 | ⟨Y, hYM, hYs, hY⟩
  · exact h1
  · exact (hD2 M Y hM hYM hYs (inClassXBlock_of_mulEquiv_alternatingFour hY)).elim

end Asc81bHyp

section PhaseThree

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}

open CFSG.AGLEmbeddingD2 (NoXBlockFor)

theorem TwoLocalPhaseThree.oddCore_le_centralizer (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) :
    CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) ≤
      Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _) :=
  h.asc81bHyp.oddCore_le_centralizer hK h.maxTwoLocal_M h84 hD2

theorem TwoLocalPhaseThree.not_isSylowTwoOf_inf (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive)
    (hD2 : NoXBlockFor G) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ¬ IsSylowTwoOf (pCoreOf 2 H ⊓ L) L := fun hsyl =>
  hD2 M L h.maxTwoLocal_M hL.le hL.subnormal
    (h85 G M (pCoreOf 2 H) L hK h.asc81bHyp hL.toIsTwoPrimeComponent hsyl)

theorem TwoLocalPhaseThree.not_isSylowTwoOf_M (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G) : ¬ IsSylowTwoOf (pCoreOf 2 H) M := by
  intro hsyl
  have hne : cgsIn M (pCoreOf 2 H) ≠ M := by
    rw [h.cgsIn_eq, inf_comm]
    exact h.inf_lt_right.ne
  obtain ⟨Y, hYM, hYs, hYX, -⟩ := hCGT G M (pCoreOf 2 H) hK h.charTwo_M hsyl hne
  exact hD2 M Y h.maxTwoLocal_M hYM hYs hYX

theorem TwoLocalPhaseThree.le_twoCore_of_le_twoPrimeComponent (h : TwoLocalPhaseThree M H)
    (hL : IsTwoPrimeComponent M L) {U : Subgroup G} (hUL : U ≤ L) (hU : IsPGroup 2 U)
    (hN : M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (U : Set G)) : U ≤ pCoreOf 2 H :=
  h.asc81bHyp.le_of_le_twoPrimeComponent hL hUL hU hN

theorem TwoLocalPhaseThree.twoCore_eq_pCoreOf_normalizer_sup (h : TwoLocalPhaseThree M H)
    (hL : IsTwoPrimeComponent M L) (hSL : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 H =
      pCoreOf 2 ((L ⊔ pCoreOf 2 H) ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
  h.asc81bHyp.twoCore_eq_pCoreOf_normalizer_sup hL hSL

theorem TwoLocalPhaseThree.weakSBlock_asc81bHyp (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h86 : Asc81bEightSix)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) ∧
      Asc81bHyp (L ⊔ pCoreOf 2 H) (pCoreOf 2 H) :=
  h.asc81bHyp.weakSBlock_asc81bHyp hK (h.twoCore_M_le h.twoCore_inf) h86 hL

theorem TwoLocalPhaseThree.blockV_facts (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h86 : Asc81bEightSix)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    pCoreOf 2 M ≤ pCoreOf 2 (L ⊔ pCoreOf 2 H) ∧ pCoreOf 2 (L ⊔ pCoreOf 2 H) ≤ pCoreOf 2 H ∧
      omegaOneCenterOf (pCoreOf 2 H) =
        blockV (pCoreOf 2 H) L ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      (L ⊔ pCoreOf 2 H) ⊓ Subgroup.centralizer (blockV (pCoreOf 2 H) L : Set G) ≤ H ⊓ M := by
  obtain ⟨-, hyp⟩ := h.weakSBlock_asc81bHyp hK h86 hL
  set S := pCoreOf 2 H
  set T := pCoreOf 2 (L ⊔ S)
  have hQS : pCoreOf 2 M ≤ L ⊔ S := (h.twoCore_M_le h.twoCore_inf).trans le_sup_right
  have hLSM : L ⊔ S ≤ M := sup_le hL.le h.twoCore_le
  have hQT : pCoreOf 2 M ≤ T := normal_pGroup_le_pCoreOf 2 _ _ hQS
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQS).mpr
      (hLSM.trans (localGroup_le_normalizer_pCoreOf 2 M))) (pCoreOf_isPGroup 2 M)
  have hTS : T ≤ S := le_of_two_radical le_sup_right hyp.twoRadical.2.2 (pCoreOf_le 2 _)
    (pCoreOf_isPGroup 2 _) (inf_le_left.trans (localGroup_le_normalizer_pCoreOf 2 _))
  have hZ : ∀ X : Subgroup G, omegaOneCenterOf X ≤ centerOf X := fun X =>
    (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hΩ : omegaOneCenterOf S ≤ blockV S L := Subgroup.closure_mono fun x hx =>
    ⟨⟨hyp.charTwo ⟨(le_sup_right : S ≤ L ⊔ S) hx.1.1, Subgroup.centralizer_le hTS hx.1.2⟩,
      Subgroup.centralizer_le hTS hx.1.2⟩, hx.2⟩
  refine ⟨hQT, hTS, le_antisymm (le_inf hΩ ((hZ S).trans inf_le_right)) ?_, ?_⟩
  · rintro x ⟨hxV, hxC⟩
    exact Subgroup.subset_closure
      ⟨⟨hTS ((hZ T) hxV).1, hxC⟩, (isElemAbelian_omegaOneCenterOf T).2 x hxV⟩
  · rintro x ⟨hxLS, hxC⟩
    refine ⟨?_, hLSM hxLS⟩
    rw [← h.normalizer_thompsonJ_eq.2]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hΩ hxC)

theorem TwoLocalPhaseThree.exists_weakSBlock (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) : ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L :=
  (h.exists_weakSBlock_or_oddCore h.twoCore_inf).resolve_right
    fun h' => h' (h.oddCore_le_centralizer hK h84 hD2)

theorem TwoLocalPhaseThree.nineThree (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h93 : Asc81bNineThree)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : NineThreeConclusion M (pCoreOf 2 H) L :=
  h93 G M (pCoreOf 2 H) L hK h.asc81bHyp hL

theorem TwoLocalPhaseThree.nineThree_not_one (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive)
    (hD2 : NoXBlockFor G) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ¬ NineThreeOne L ∧ (NineThreeTwo M (pCoreOf 2 H) L →
      ¬ IsSylowTwoOf (barM M (pCoreOf 2 H ⊓ L)) (barM M L)) :=
  ⟨fun h1 => hD2 M L h.maxTwoLocal_M hL.le hL.subnormal h1, fun _ hsyl =>
    h.not_isSylowTwoOf_inf hK h85 hD2 hL (isSylowTwoOf_inf_of_barM hL.le
      (h.twoCore_M_le h.twoCore_inf) (pCoreOf_isPGroup 2 H) hsyl)⟩

theorem TwoLocalPhaseThree.hasIrreducibleCommutatorQuotient (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h86 : Asc81bEightSix) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (htype : IsShort2 L ∨ NineThreeThree M (pCoreOf 2 H) L ∨ NineThreeSix M (pCoreOf 2 H) L ∨
      NineThreeSeven M (pCoreOf 2 H) L)
    (hnc : ¬ L ≤ Subgroup.centralizer (blockV (pCoreOf 2 H) L : Set G)) :
    HasIrreducibleCommutatorQuotient L (blockV (pCoreOf 2 H) L) := by
  rcases htype with hs | h3 | h6 | h7
  · obtain ⟨hSL, -⟩ := h.weakSBlock_asc81bHyp hK h86 hL
    have hTS := (h.blockV_facts hK h86 hL).2.1
    set S := pCoreOf 2 H
    have hVT : blockV S L ≤ pCoreOf 2 (L ⊔ S) := QuasithinUnique.Setup.omegaOneCenterOf_le _
    have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) :=
      le_sup_left.trans (le_normalizer_of_characteristic_pCoreOf
        (QuasithinUnique.Setup.omegaOneCenterOf_le _)
        (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _))
    have hVL : ⁅blockV S L, L⁆ ≤ L := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      rw [commutatorElement_def]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSL (hTS (hVT hv))) l).mp hl)
        (L.inv_mem hl)
    refine IsShort2.hasIrreducibleCommutatorQuotient hs hLV (normal_pGroup_le_pCoreOf 2 _ L hVL
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hVL).mpr
        (le_normalizer_commutator_of_le_normalizer hLV))
      ((pCoreOf_isPGroup 2 (L ⊔ S)).to_le ((commutator_le_left_of_le_normalizer hLV).trans hVT)))
      (isElemAbelian_omegaOneCenterOf _).1 hnc
  · exact h3.2.2.1
  · exact h6.1
  · exact h7.1


theorem D1PhaseThree.oddCore_le_centralizer (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) ≤
      Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _) :=
  h.toTwoLocalPhaseThree.oddCore_le_centralizer h.isKGroup.1 h84 (hD2 G h.glob)

theorem D1PhaseThree.not_isSylowTwoOf_inf (h : D1PhaseThree p P M H R) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ¬ IsSylowTwoOf (pCoreOf 2 H ⊓ L) L :=
  h.toTwoLocalPhaseThree.not_isSylowTwoOf_inf h.isKGroup.1 h85 (hD2 G h.glob) hL

theorem D1PhaseThree.not_isSylowTwoOf_M (h : D1PhaseThree p P M H R)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : ¬ IsSylowTwoOf (pCoreOf 2 H) M :=
  h.toTwoLocalPhaseThree.not_isSylowTwoOf_M h.isKGroup.1 hCGT (hD2 G h.glob)

theorem D1PhaseThree.le_twoCore_of_le_twoPrimeComponent (h : D1PhaseThree p P M H R)
    (hL : IsTwoPrimeComponent M L) {U : Subgroup G} (hUL : U ≤ L) (hU : IsPGroup 2 U)
    (hN : M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (U : Set G)) : U ≤ pCoreOf 2 H :=
  h.toTwoLocalPhaseThree.le_twoCore_of_le_twoPrimeComponent hL hUL hU hN

theorem D1PhaseThree.twoCore_eq_pCoreOf_normalizer_sup (h : D1PhaseThree p P M H R)
    (hL : IsTwoPrimeComponent M L) (hSL : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 H =
      pCoreOf 2 ((L ⊔ pCoreOf 2 H) ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
  h.toTwoLocalPhaseThree.twoCore_eq_pCoreOf_normalizer_sup hL hSL

theorem D1PhaseThree.weakSBlock_asc81bHyp (h : D1PhaseThree p P M H R) (h86 : Asc81bEightSix)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) ∧
      Asc81bHyp (L ⊔ pCoreOf 2 H) (pCoreOf 2 H) :=
  h.toTwoLocalPhaseThree.weakSBlock_asc81bHyp h.isKGroup.1 h86 hL

theorem D1PhaseThree.blockV_facts (h : D1PhaseThree p P M H R) (h86 : Asc81bEightSix)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    pCoreOf 2 M ≤ pCoreOf 2 (L ⊔ pCoreOf 2 H) ∧ pCoreOf 2 (L ⊔ pCoreOf 2 H) ≤ pCoreOf 2 H ∧
      omegaOneCenterOf (pCoreOf 2 H) =
        blockV (pCoreOf 2 H) L ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      (L ⊔ pCoreOf 2 H) ⊓ Subgroup.centralizer (blockV (pCoreOf 2 H) L : Set G) ≤ H ⊓ M :=
  h.toTwoLocalPhaseThree.blockV_facts h.isKGroup.1 h86 hL

theorem D1PhaseThree.exists_weakSBlock (h : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) : ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L :=
  h.toTwoLocalPhaseThree.exists_weakSBlock h.isKGroup.1 h84 (hD2 G h.glob)

theorem D1PhaseThree.nineThree (h : D1PhaseThree p P M H R) (h93 : Asc81bNineThree)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : NineThreeConclusion M (pCoreOf 2 H) L :=
  h.toTwoLocalPhaseThree.nineThree h.isKGroup.1 h93 hL

theorem D1PhaseThree.nineThree_not_one (h : D1PhaseThree p P M H R) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ¬ NineThreeOne L ∧ (NineThreeTwo M (pCoreOf 2 H) L →
      ¬ IsSylowTwoOf (barM M (pCoreOf 2 H ⊓ L)) (barM M L)) :=
  h.toTwoLocalPhaseThree.nineThree_not_one h.isKGroup.1 h85 (hD2 G h.glob) hL

theorem D1PhaseThree.hasIrreducibleCommutatorQuotient (h : D1PhaseThree p P M H R)
    (h86 : Asc81bEightSix) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (htype : IsShort2 L ∨ NineThreeThree M (pCoreOf 2 H) L ∨ NineThreeSix M (pCoreOf 2 H) L ∨
      NineThreeSeven M (pCoreOf 2 H) L)
    (hnc : ¬ L ≤ Subgroup.centralizer (blockV (pCoreOf 2 H) L : Set G)) :
    HasIrreducibleCommutatorQuotient L (blockV (pCoreOf 2 H) L) :=
  h.toTwoLocalPhaseThree.hasIrreducibleCommutatorQuotient h.isKGroup.1 h86 hL htype hnc

end PhaseThree

end CFSG.AGLEmbedding
