module

import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Abstract

variable {Y : Type*} [Group Y]

theorem isPGroup_closure_of_pairwise_commute {q : ℕ} {S : Set Y} (hcomm : S.Pairwise Commute)
    (hS : ∀ y ∈ S, IsPGroup q (Subgroup.zpowers y)) : IsPGroup q (Subgroup.closure S) := by
  have : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hcomm
  have hc : ∀ x ∈ Subgroup.closure S, ∀ z ∈ Subgroup.closure S, Commute x z := fun x hx z hz =>
    congrArg Subtype.val ((isMulCommutative_iff.mp this) (⟨x, hx⟩ : Subgroup.closure S) ⟨z, hz⟩)
  have key : ∀ x ∈ Subgroup.closure S, ∃ k : ℕ, x ^ q ^ k = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk⟩ := hS y hy ⟨y, Subgroup.mem_zpowers y⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    | one => exact ⟨0, one_pow _⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨i, hi⟩ := iha
      obtain ⟨j, hj⟩ := ihb
      have h1 : a ^ q ^ (i + j) = 1 := by rw [pow_add, pow_mul, hi, one_pow]
      have h2 : b ^ q ^ (i + j) = 1 := by rw [pow_add, mul_comm, pow_mul, hj, one_pow]
      exact ⟨i + j, by rw [(hc a ha b hb).mul_pow, h1, h2, one_mul]⟩
    | inv a ha iha =>
      obtain ⟨i, hi⟩ := iha
      exact ⟨i, by rw [inv_pow, hi, inv_one]⟩
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := key x hx
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem comap_sSup_le_of_forall {X : Type*} [Group X] {f : X →* Y} (hf : Function.Surjective f)
    {C : Set (Subgroup Y)} (hC : C.Nonempty) {J : Subgroup X} (hJ : ∀ L ∈ C, L.comap f ≤ J) :
    (sSup C).comap f ≤ J := by
  obtain ⟨L₀, hL₀⟩ := hC
  have hker : f.ker ≤ J := (Subgroup.ker_le_comap f L₀).trans (hJ L₀ hL₀)
  have hle : sSup C ≤ J.map f := sSup_le fun L hL => by
    rw [← Subgroup.map_comap_eq_self_of_surjective hf L]
    exact Subgroup.map_mono (hJ L hL)
  calc (sSup C).comap f ≤ (J.map f).comap f := Subgroup.comap_mono hle
    _ = J ⊔ f.ker := Subgroup.comap_map_eq f J
    _ = J := sup_eq_left.mpr hker

theorem normal_sSup_of_forall_map_conj {C : Set (Subgroup Y)}
    (hC : ∀ g : Y, ∀ L ∈ C, L.map (MulAut.conj g).toMonoidHom ∈ C) : (sSup C).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hle : (sSup C).map (MulAut.conj g).toMonoidHom ≤ sSup C := by
    rw [(Subgroup.gc_map_comap _).l_sSup]
    exact iSup₂_le fun L hL => le_sSup (hC g L hL)
  exact hle ⟨x, hx, rfl⟩

end Abstract

section Components

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_isPGroup_pRank_inf_centralizer {s : ℕ} (hs : s.Prime) (L : Fin 4 → Subgroup Y)
    (hL : ∀ i, IsComponentOf (L i) ⊤) (hinj : Function.Injective L)
    (hdvd : ∀ i, s ∣ Nat.card (↥(L i) ⧸ Subgroup.center ↥(L i))) :
    ∃ A : Subgroup Y, IsPGroup s A ∧ A ≤ ⨆ i, L i ∧ 4 ≤ Open.pRank s A ∧
      ∀ L' : Subgroup Y, IsComponentOf L' ⊤ →
        3 ≤ Open.pRank s (A ⊓ Subgroup.centralizer (L' : Set Y)) := by
  classical
  choose y hyL hyq hyZ using fun i => exists_qElement_not_central hs (hdvd i)
  have hcen : ∀ i, ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L i ≠ L' →
      L i ≤ Subgroup.centralizer (L' : Set Y) := fun i L' hL' hne =>
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hL i) hL' hne)
  have hpair : (Set.range y).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hne : L i ≠ L j := fun he => hij (by rw [hinj he])
    exact (Subgroup.mem_centralizer_iff.mp (hcen i (L j) (hL j) hne (hyL i)) _ (hyL j)).symm
  set A := Subgroup.closure (Set.range y) with hA
  have hyA : ∀ i, y i ∈ A := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  refine ⟨A, isPGroup_closure_of_pairwise_commute hpair (by rintro _ ⟨i, rfl⟩; exact hyq i),
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact le_iSup L i (hyL i)), ?_, ?_⟩
  · have h := le_pRank_of_components hs L hL hinj A y hyA hyL hyq hyZ
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  · intro L' hL'
    have h := le_pRank_of_components hs (fun i : {i : Fin 4 // L i ≠ L'} => L i)
      (fun i => hL i) (fun i j he => Subtype.ext (hinj he))
      (A ⊓ Subgroup.centralizer (L' : Set Y)) (fun i => y i)
      (fun i => ⟨hyA i, hcen i L' hL' i.2 (hyL i)⟩) (fun i => hyL i) (fun i => hyq i)
      (fun i => hyZ i)
    refine le_trans ?_ h
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h1 : (Finset.univ.filter fun i : Fin 4 => L i = L').card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb =>
        hinj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin 4 => L i = L')
    rw [Finset.card_univ, Fintype.card_fin] at h2
    simp only [ne_eq] at h2 ⊢
    omega

theorem exists_injective_fin_of_le_ncard {C : Set (Subgroup Y)} (h4 : 4 ≤ C.ncard) :
    ∃ L : Fin 4 → Subgroup Y, (∀ i, L i ∈ C) ∧ Function.Injective L := by
  have hfin : C.Finite := Set.toFinite C
  rw [Set.ncard_eq_toFinset_card C hfin] at h4
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin 4)
    (s := hfin.toFinset) (by simpa using h4)
  exact ⟨f, fun i => by simpa using hf ⟨i, rfl⟩, f.injective⟩

end Components

theorem stmtOneLieLemmaUPrime :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G},
      D1PhaseThree p P M H R → ∀ {s : ℕ}, s.Prime → s ≠ 2 → s ≠ p →
      ∀ (W : Subgroup G), W ≤ H → H ≤ Subgroup.normalizer (W : Set G) → W ≤ M →
      ∀ C : Set (Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)),
        (∀ L ∈ C, IsComponentOf L ⊤) →
        (∀ m : ↥M ⧸ CFSG.pCore 2 ↥M, ∀ L ∈ C, L.map (MulAut.conj m).toMonoidHom ∈ C) →
        (∀ L ∈ C, s ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) →
        (∀ L ∈ C, (L.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ W) →
        4 ≤ C.ncard → False := by
  intro G _ _ p P M H R h s hs hs2 _ W hWH hWn hWM C hCc hCi hCs hCW h4
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hmks : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hO : s.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hs Nat.prime_two).mpr hs2)
  obtain ⟨L, hLC, hinj⟩ := exists_injective_fin_of_le_ncard h4
  obtain ⟨A, hA, hAL, hA4, hA3⟩ := exists_isPGroup_pRank_inf_centralizer hs L
    (fun i => hCc _ (hLC i)) hinj (fun i => hCs _ (hLC i))
  have hAC : A ≤ sSup C := hAL.trans (iSup_le fun i => le_sSup (hLC i))
  obtain ⟨B, hB, hBA⟩ := exists_isPGroup_map_mk_eq (CFSG.pCore 2 ↥M) hA
  have hBGM : B.map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hBG4 : 4 ≤ Open.pRank s (B.map M.subtype) := by
    have h1 := pRank_barM_le hs hs2 M _ hBGM
    rw [barM_map_subtype, hBA] at h1
    exact hA4.trans h1
  obtain ⟨Ts, hBTs⟩ := (hB.map M.subtype).exists_le_sylow
  have hβ : s ∈ GLBBetaFour G := mem_glbBetaFour_of_le_pRank hs hs2 h.maxTwoLocal_M.1 hBGM hBG4
  obtain ⟨L₀, hL₀, hcoreL⟩ := (h.glob.pre s hβ).2 Ts
  obtain ⟨Ms, hLMs, hMs⟩ := exists_maximal_twoLocal hL₀
  have hcore : GLBWeakCore s (Ts : Subgroup G) ≤ Ms := hcoreL.trans hLMs
  have hTsMs : (Ts : Subgroup G) ≤ Ms := (subgroup_le_weakCore_of_rank s hs _
    ((by omega : 3 ≤ 4).trans (hBG4.trans (pRank_mono s hs hBTs)))).trans hcore
  have hQMs : pCoreOf 2 M ≤ Ms := intersecting_local_twoCore_le s hs hs2 Ts hTsMs hcore
    ((by omega : 3 ≤ 4).trans (hBG4.trans (pRank_mono s hs (le_inf hBGM (hBTs.trans hTsMs)))))
  have hmem : ∀ L₁ ∈ C, L₁.comap mk ≤ Ms.subgroupOf M := by
    intro L₁ hL₁
    set A₁ : Subgroup ↥M := (A ⊓ Subgroup.centralizer (L₁ : Set _)).comap mk ⊓ B with hA₁
    have hA₁map : A₁.map mk = A ⊓ Subgroup.centralizer (L₁ : Set _) :=
      map_comap_inf_eq mk (inf_le_left.trans hBA.ge)
    have hA₁p : IsPGroup s A₁ := hB.to_le inf_le_right
    have hA₁3 : 3 ≤ Open.pRank s (A₁.map M.subtype) := by
      have h1 := pRank_barM_le hs hs2 M (A₁.map M.subtype) (Subgroup.map_subtype_le _)
      rw [barM_map_subtype, hA₁map] at h1
      exact (hA3 L₁ (hCc L₁ hL₁)).trans h1
    have hA₁Ms : A₁.map M.subtype ≤ Ms :=
      (Subgroup.map_mono inf_le_right).trans (hBTs.trans hTsMs)
    have hN : Subgroup.normalizer (A₁.map M.subtype : Set G) ≤ Ms :=
      normalizer_le_of_subgroup_rank_in_containing_sylow s hs Ts hTsMs hcore hA₁Ms hA₁3
    intro x hx
    have hx' : x ∈ (Subgroup.centralizer ((A₁.map mk : Subgroup _) : Set _)).comap mk := by
      rw [Subgroup.mem_comap, hA₁map]
      exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (Subgroup.mem_centralizer_iff.mp ha.2 _ hx).symm
    have hsup : CFSG.pCore 2 ↥M ⊔ Subgroup.centralizer (A₁ : Set ↥M) ≤ Ms.subgroupOf M := by
      refine sup_le (fun q hq => Subgroup.mem_subgroupOf.mpr ?_)
        (fun c hc => Subgroup.mem_subgroupOf.mpr ?_)
      · have hq' : (q : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨q, hq, rfl⟩
        exact hQMs hq'
      · refine hN (Subgroup.centralizer_le_normalizer _ ?_)
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨a, ha, rfl⟩
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc a ha)
    exact hsup (comap_centralizer_map_le_sup hs (CFSG.pCore 2 ↥M) hO hA₁p hx')
  have hCne : C.Nonempty := ⟨L 0, hLC 0⟩
  set E := (sSup C).comap mk with hE
  have : (sSup C).Normal := normal_sSup_of_forall_map_conj hCi
  have : E.Normal := Subgroup.Normal.comap inferInstance mk
  have hEMs : E.map M.subtype ≤ Ms :=
    Subgroup.map_le_iff_le_comap.mpr (comap_sSup_le_of_forall hmks hCne hmem)
  have hEW : E.map M.subtype ≤ W := Subgroup.map_le_iff_le_comap.mpr
    (comap_sSup_le_of_forall hmks hCne fun L₁ hL₁ => Subgroup.map_le_iff_le_comap.mp (hCW L₁ hL₁))
  have hBE : B ≤ E := fun b hb => hAC (hBA ▸ Subgroup.mem_map_of_mem mk hb :)
  have hE3 : 3 ≤ Open.pRank s (E.map M.subtype) :=
    (by omega : 3 ≤ 4).trans (hBG4.trans (pRank_mono s hs (Subgroup.map_mono hBE)))
  have hMMs : M ≤ Ms := normal_subgroup_sylow_rank_forces_containment s hs Ts hTsMs hcore E hEMs hE3
  have hMseq : Ms = M := h.maxTwoLocal_M.2 Ms hMs.1 hMMs
  have : (W.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mpr hWn
  have hWmap : (W.subgroupOf H).map H.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWH
  have hHMs : H ≤ Ms := normal_subgroup_sylow_rank_forces_containment s hs Ts hTsMs hcore
    (W.subgroupOf H) (by rw [hWmap, hMseq]; exact hWM)
    (by rw [hWmap]; exact hE3.trans (pRank_mono s hs hEW))
  exact h.not_le (hMseq ▸ hHMs)

end CFSG.AGLEmbedding
