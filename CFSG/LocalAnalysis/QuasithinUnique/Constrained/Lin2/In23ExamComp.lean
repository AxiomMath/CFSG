module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamLambda
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLem125
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeFive
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow

public section

namespace CFSG.QuasithinUnique.Lin2.Exam

open CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

section Local

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem exam_pCore_ne_bot {s : G} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) :
    pCoreOf 2 (Subgroup.centralizer ({s} : Set G)) ≠ ⊥ := by
  have hE := isElemAbelian_zpowers_of_sq_eq_one hs2
  have hzp : IsPGroup 2 (Subgroup.zpowers s) :=
    fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  have hsC : s ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hXn : Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers s : Subgroup G) : Set G) := by
    refine le_normalizer_of_commute fun a ha b hb => ?_
    have hc : Subgroup.centralizer ({s} : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers s : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hc] at hb
    exact Subgroup.mem_centralizer_iff.1 hb a ha
  have hsP : s ∈ pCoreOf 2 (Subgroup.centralizer ({s} : Set G)) :=
    le_pCoreOf_of_normalizes (Subgroup.zpowers_le.2 hsC) hXn hzp (Subgroup.mem_zpowers s)
  intro h
  rw [h, Subgroup.mem_bot] at hsP
  exact hs1 hsP

theorem exam_isLocal (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s : G} (hs : s ∈ S)
    (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (h4 : 4 < 2 ^ n) :
    quasithinIsLocal (S ⊓ Subgroup.centralizer ({s} : Set G))
      (L ⊓ Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨m, hm, hm1, hsh, hlin, hUs, hO, hRsyl⟩ := exam_block E hcfg hs hsR hs2 h4
  set C := Subgroup.centralizer ({s} : Set G) with hC
  set Ls := L ⊓ C with hLs
  set Ss := S ⊓ C with hSs
  have hSsN : Ss ≤ Subgroup.normalizer (Ls : Set G) := fun σ hσ =>
    exam_Ss_le_normalizer_Ls hcfg hσ.1 (Subgroup.mem_centralizer_singleton_iff.mp hσ.2)
  have hXN : Ls ⊔ Ss ≤ Subgroup.normalizer (Ls : Set G) := sup_le Subgroup.le_normalizer hSsN
  have hS2 : IsPGroup 2 Ss := hcfg.S_isPGroup.to_le inf_le_left
  have hSyl : IsSylowTwoOf Ss (Ls ⊔ Ss) := by
    have hbase := E.S_s_sylow hcfg hs hsR hs2 hRsyl.card_eq.symm
    refine isSylowTwoOf_of_le_of_le hbase le_sup_right ?_
    refine sup_le (le_inf ?_ inf_le_right) (le_inf ?_ inf_le_right)
    · exact fun g hg => hcfg.H_le_normalizer_Q (hcfg.L_le_H hg.1)
    · exact fun g hg => hcfg.H_le_normalizer_Q (hcfg.S_le_H hg.1)
  have hblk : IsBlock2 (Ls ⊔ Ss) Ls := by
    refine ⟨hsh, le_sup_left, ?_⟩
    have hnorm : (Ls.subgroupOf (Ls ⊔ Ss)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXN
    exact hnorm.isSubnormal
  have hUsne : blockU L ⊓ C ≠ ⊥ := by
    rw [hUs]
    intro h
    have := hsh.2.2.2.2.1
    rw [h] at this
    exact not_lt_bot this
  have hUsN : Ls ⊔ Ss ≤ Subgroup.normalizer ((blockU L ⊓ C : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · have := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Ls
      rwa [hO] at this
    · intro σ hσ
      have hσs := Subgroup.mem_centralizer_singleton_iff.mp hσ.2
      rw [← conjR_eq_self_iff, conjR_inf,
        conjR_eq_of_mem_normalizer (E.S_le_normalizer_U hcfg hσ.1),
        conjR_centralizer_of_comm hσs]
  have hUs2 : IsPGroup 2 (blockU L ⊓ C : Subgroup G) := by
    rw [← hO]
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Ls
  have hUsle : blockU L ⊓ C ≤ Ls ⊔ Ss :=
    (inf_le_inf_right _ (blockU_le L)).trans le_sup_left
  have hmem : blockU L ⊓ C ≤ pCoreOf 2 (Ls ⊔ Ss) := le_pCoreOf_of_normalizes hUsle hUsN hUs2
  refine ⟨hS2, ?_, hSyl.2.2, ?_⟩
  · exact L238.mem_cComp_of_isChi0Block_nonsolvable hblk (Or.inl ⟨m, hm1, hlin⟩)
  · intro h
    apply hUsne
    rw [eq_bot_iff]
    exact hmem.trans h.le

end Local

section Component

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S)
  (hs2 : s ^ 2 = 1) (hc : centerOf L ≠ ⊥) (h4 : 4 < 2 ^ n)
  (hx : x ∈ T ⊓ Subgroup.centralizer ({s} : Set G)) (hxS : x ∉ S)

include E hcfg hs hsR hs2 h4

omit hx hxS in
theorem exam_exists_K
    (a39 : A39ForSQTKCat) :
    ∃ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({s} : Set G)) ∧
      L ⊓ Subgroup.centralizer ({s} : Set G) ≤ K := by
  obtain ⟨m, hm, hm1, hsh, hlin, hUs, hO, hRsyl⟩ := exam_block E hcfg hs hsR hs2 h4
  have hs1 : s ≠ 1 := fun h => hsR (h ▸ (thompsonJ S).one_mem)
  have hX := exam_pCore_ne_bot hs1 hs2
  have hTs : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({s} : Set G))
      (Subgroup.centralizer ({s} : Set G)) :=
    E.T_s_sylow hcfg hs hsR hs2 hO hRsyl.card_eq.symm
  have hRS : S ⊓ Subgroup.centralizer ({s} : Set G) ≤ T ⊓ Subgroup.centralizer ({s} : Set G) :=
    inf_le_inf_right _ hcfg.S_le_T
  have hidx : (S ⊓ Subgroup.centralizer ({s} : Set G)).relIndex
      (T ⊓ Subgroup.centralizer ({s} : Set G)) ≤ 2 := by
    have h1 : (S ⊓ Subgroup.centralizer ({s} : Set G)).relIndex
        (T ⊓ Subgroup.centralizer ({s} : Set G)) =
        S.relIndex (T ⊓ Subgroup.centralizer ({s} : Set G)) := by
      rw [← Subgroup.inf_relIndex_right S (T ⊓ Subgroup.centralizer ({s} : Set G))]
      congr 1
      ext y
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, hcfg.S_le_T h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [h1]
    have h2 := Subgroup.relIndex_le_of_le_right (H := S) (inf_le_left : T ⊓
      Subgroup.centralizer ({s} : Set G) ≤ T) (by rw [E.idxTS hcfg]; norm_num)
    rw [E.idxTS hcfg] at h2
    exact h2
  have hloc := exam_isLocal E hcfg hs hsR hs2 h4
  exact (lemma_1_2_5 hcfg.cs.setting.qtke.1 a37ForSQTKCat_proved a39 hX hTs hRS hidx hloc
    inf_le_right).exists

omit hx hxS in
theorem exam_Ts_sylow :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({s} : Set G)) (Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨m, hm, hm1, hsh, hlin, hUs, hO, hRsyl⟩ := exam_block E hcfg hs hsR hs2 h4
  exact E.T_s_sylow hcfg hs hsR hs2 hO hRsyl.card_eq.symm

include hc hx hxS

section KProps

variable {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({s} : Set G)))
  (hLK : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ K)

include hK hLK

omit hLK in
theorem exam_K_pCore_le : pCoreOf 2 K ≤ Subgroup.zpowers s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans
    (exam_pCore_centralizer_le E hcfg hs hsR hs2 hc h4 hx hxS)

theorem exam_K_conj
    : conjR K x = K := by
  have hxT : x ∈ T := (Subgroup.mem_inf.mp hx).1
  have hxC : x ∈ Subgroup.centralizer ({s} : Set G) := (Subgroup.mem_inf.mp hx).2
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  by_contra hne
  obtain ⟨m, hm, hm1, hsh, hlin, hUs, hO, hRsyl⟩ := exam_block E hcfg hs hsR hs2 h4
  have hs1 : s ≠ 1 := fun h => hsR (h ▸ (thompsonJ S).one_mem)
  have hX := exam_pCore_ne_bot hs1 hs2
  have hK' : conjR K x ∈ cComp (Subgroup.centralizer ({s} : Set G)) :=
    map_conj_mem_cComp hK ((Subgroup.centralizer ({s} : Set G)).inv_mem hxC)
  obtain ⟨h1, -⟩ := lemma_1_2_1_two hcfg.cs.setting.qtke.1 a37ForSQTKCat_proved hX hK hK'
    (fun h => hne h.symm)
  have hcomm : ⁅K, conjR K x⁆ ≤ Subgroup.zpowers s :=
    h1.trans (inf_le_left.trans (exam_K_pCore_le E hcfg hs hsR hs2 hc h4 hx hxS hK))
  have hzc : ∀ a ∈ Subgroup.zpowers s, ∀ k ∈ K, ⁅a, k⁆ = 1 := by
    intro a ha k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hkC : k ∈ Subgroup.centralizer ({s} : Set G) := le_of_mem_cComp hK hk
    have hks : k * s = s * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((Commute.zpow_left (show Commute s k from hks.symm) j)).eq
  have h2 : ⁅⁅K, conjR K x⁆, K⁆ = ⊥ :=
    eq_bot_iff.2 (Subgroup.commutator_le.2 fun a ha k hk =>
      Subgroup.mem_bot.2 (hzc a (hcomm ha) k hk))
  have h3 : ⁅⁅conjR K x, K⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (conjR K x) K]
    exact h2
  have h5 : ⁅⁅K, K⁆, conjR K x⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h3
  rw [perfect_of_mem_cComp hK] at h5
  have hRsLsx : thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) ≤
      conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := exam_Rs_le_conj E hcfg hxT hxs
  have hUR : blockU L ≤ thompsonJ S := by
    rw [(E.RUU hcfg hxT hxS).1]; exact le_sup_left
  have hUsK' : blockU L ⊓ Subgroup.centralizer ({s} : Set G) ≤ conjR K x :=
    ((inf_le_inf_right _ hUR).trans hRsLsx).trans (conjR_mono hLK x)
  have hbU : blockU (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      ⁅blockU L ⊓ Subgroup.centralizer ({s} : Set G), L ⊓ Subgroup.centralizer ({s} : Set G)⁆ := by
    have h' : blockU (L ⊓ Subgroup.centralizer ({s} : Set G)) =
        ⁅pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)), L ⊓ Subgroup.centralizer ({s} : Set G)⁆ :=
      rfl
    rw [h', hO]
  have hUsC : ⁅blockU L ⊓ Subgroup.centralizer ({s} : Set G),
      L ⊓ Subgroup.centralizer ({s} : Set G)⁆ = ⊥ := by
    refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun u hu ℓ hℓ => ?_)
    rw [Subgroup.mem_bot]
    have hmem : ⁅ℓ, u⁆ ∈ ⁅K, conjR K x⁆ := Subgroup.commutator_mem_commutator (hLK hℓ) (hUsK' hu)
    rw [h5] at hmem
    have h1' : ⁅ℓ, u⁆ = 1 := Subgroup.mem_bot.mp hmem
    rw [← commutatorElement_inv, h1', inv_one]
  have hUsne : blockU (L ⊓ Subgroup.centralizer ({s} : Set G)) ≠ ⊥ := by
    intro h
    have := hsh.2.2.2.2.1
    rw [h] at this
    exact not_lt_bot this
  exact hUsne (hbU.trans hUsC)

theorem exam_Ks_le_K
    : L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
    conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x ≤ K := by
  refine sup_le hLK ?_
  have := conjR_mono hLK x
  rwa [exam_K_conj E hcfg hs hsR hs2 hc h4 hx hxS hK hLK] at this

theorem exam_K_quasisimple
    : CFSG.IsQuasisimple ↥K := by
  have hxT : x ∈ T := (Subgroup.mem_inf.mp hx).1
  have hs1 : s ≠ 1 := fun h => hsR (h ▸ (thompsonJ S).one_mem)
  have hX := exam_pCore_ne_bot hs1 hs2
  have hKC : K ≤ Subgroup.centralizer ({s} : Set G) := le_of_mem_cComp hK
  have hZK : pCoreOf 2 K ≤ centerOf K := by
    intro y hy
    have hyz := exam_K_pCore_le E hcfg hs hsR hs2 hc h4 hx hxS hK hy
    refine ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K hy,
      Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyz
    have hks : k * s = s * k := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
    exact ((Commute.zpow_right (show Commute k s from hks) j)).eq
  have hn3 := Five.three_le_of_four_lt_two_pow h4
  have hUel : IsElemAbelian 2 (blockU L ⊓ Subgroup.centralizer ({s} : Set G)) :=
    IsElemAbelian.mono inf_le_left (E.elemU hcfg hxT hxS).1
  have hUcard := ((E.U_s_values hcfg hs hsR hs2 hxT hxS).2 hc).1
  have hm : 1 < CFSG.Open.pRank 2 K := by
    have hmem : 3 * n / 2 ∈ {k | ∃ E' : Subgroup G, E' ≤ K ∧ IsElemAbelian 2 E' ∧
        Nat.card E' = 2 ^ k} :=
      ⟨blockU L ⊓ Subgroup.centralizer ({s} : Set G), (inf_le_inf_right _ (blockU_le L)).trans hLK,
        hUel, hUcard⟩
    have hbdd : BddAbove {k | ∃ E' : Subgroup G, E' ≤ K ∧ IsElemAbelian 2 E' ∧
        Nat.card E' = 2 ^ k} := by
      refine ⟨Nat.card G, fun k hk => ?_⟩
      obtain ⟨E', -, -, hEc⟩ := hk
      have h1 : 2 ^ k ≤ Nat.card G := hEc ▸ Subgroup.card_le_card_group E'
      exact (Nat.lt_two_pow_self.trans_le h1).le
    exact lt_of_lt_of_le (by omega) (le_csSup hbdd hmem)
  exact lemma_1_2_1_five_core hcfg.cs.setting.qtke.1 a36CoreForSQTKCat_proved
    CFSG.Quasithin.l2MultiplierFact hX hK hZK hm

theorem exam_K_list
    : CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K) := by
  have hq := exam_K_quasisimple E hcfg hs hsR hs2 hc h4 hx hxS hK hLK
  have hKC : K ≤ Subgroup.centralizer ({s} : Set G) := le_of_mem_cComp hK
  have hs1 : s ≠ 1 := fun h => hsR (h ▸ (thompsonJ S).one_mem)
  have hX := exam_pCore_ne_bot hs1 hs2
  have hSQTK : CFSG.SectionRank.IsSQTKCat ↥(Subgroup.centralizer ({s} : Set G)) :=
    hcfg.cs.setting.qtke.1 _ hX
  have e : ↥K ≃* ↥(K.subgroupOf (Subgroup.centralizer ({s} : Set G))) :=
    (Subgroup.subgroupOfEquivOfLe hKC).symm
  have hqH : CFSG.IsQuasisimple ↥(K.subgroupOf (Subgroup.centralizer ({s} : Set G))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have : IsSimpleGroup (↥(K.subgroupOf (Subgroup.centralizer ({s} : Set G))) ⧸
      Subgroup.center ↥(K.subgroupOf (Subgroup.centralizer ({s} : Set G)))) := hqH.2.1
  have hlist := CFSG.Milestones.cl_lit_sqtk_simple_list_section _ hSQTK
    (K.subgroupOf (Subgroup.centralizer ({s} : Set G)))
    (Subgroup.center ↥(K.subgroupOf (Subgroup.centralizer ({s} : Set G)))) hqH.2.2
  exact CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv
    (QuotientGroup.congr _ _ e
      (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e)) hlist

omit hc hx hxS hLK in
theorem exam_K_sylow : IsSylowTwoOf ((T ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ K) K :=
  A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK)
    (exam_Ts_sylow E hcfg hs hsR hs2 h4)

end KProps

end Component

end CFSG.QuasithinUnique.Lin2.Exam
