module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneDefs
public import CFSG.LieType.SeitzGeneration.HyperLeaf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieWeakCore
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bKGroup
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LieType.SeitzGeneration.ExtSeitzG2Odd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LieType.SeitzGeneration (HyperGen)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hp, hs⟩ := hA
  have hc : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
  refine ⟨?_, (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator, hp]

theorem primeComplementCore_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ}
    (e : A ≃* B) (h : primeComplementCore (G := A) p = ⊥) :
    primeComplementCore (G := B) p = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le ?_
  rintro N ⟨hN, hcop⟩ x hx
  have hN' : (N.map e.symm.toMonoidHom).Normal := hN.map _ e.symm.surjective
  have hcard : Nat.card (N.map e.symm.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective e.symm.injective
  have hle := normal_coprime_le_primeComplementCore p (N.map e.symm.toMonoidHom) hN'
    (by rw [hcard]; exact hcop)
  rw [h] at hle
  have h1 : e.symm x = 1 := Subgroup.mem_bot.1 (hle ⟨x, hx, rfl⟩)
  rw [Subgroup.mem_bot]
  simpa using congrArg e h1

private theorem openIsKGroup_of_isKGroup {X : Type} [Group X] (h : CFSG.IsKGroup X) :
    CFSG.Open.IsKGroup X := fun K L _ _ hsimple _ => h K (L.subgroupOf K) hsimple

theorem glbCore_one_subgroupOf_le_comap {G : Type} [Group G] [Finite G] (p : ℕ)
    {M E : Subgroup G} :
    GLBCore p 1 (E.subgroupOf M) ≤ (GLBCore p 1 E).comap M.subtype := by
  refine sSup_le ?_
  rintro N ⟨Q, hQ, hQ1, rfl⟩ x hx
  have hQm : Q.map M.subtype ≤ E := by
    refine (Subgroup.map_mono hQ).trans ?_
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hrank : 1 ≤ Open.pRank p (Q.map M.subtype) := by
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
      M.subtype_injective]
    exact hQ1
  exact (le_sSup ⟨Q.map M.subtype, hQm, hrank, rfl⟩ :
    Subgroup.normalizer ((Q.map M.subtype : Subgroup G) : Set G) ≤ GLBCore p 1 E)
    (Subgroup.le_normalizer_map M.subtype ⟨x, hx, rfl⟩)

theorem kFactThreeOne_of_hyp
    (h : ∀ (p : ℕ) (G : Type) [Group G] [Finite G] (K : Subgroup G) (P : Sylow p G)
      (E : Subgroup G), Hyp p K P E →
      ¬ K ≤ (if 3 ≤ Open.pRank p (P : Subgroup G) then GLBWeakCore p (P : Subgroup G)
        else GLBCore p 1 E) →
      OnThreeOneList p K ∧ Subgroup.center K = ⊥) :
    KFactThreeOne := by
  intro p Y _ _ X K P E hp hp2 hKX hXN hq hK hcore _ hP hEP hE hEc hnot
  haveI : Fact p.Prime := ⟨hp⟩
  set M : Subgroup Y := K ⊔ P with hM
  have hKM : K ≤ M := le_sup_left
  have hPM : P ≤ M := le_sup_right
  have hMX : M ≤ X := sup_le hKX hP.le
  have hMN : M ≤ Subgroup.normalizer (K : Set Y) := hMX.trans hXN
  have hEM : E ≤ M := hEP.trans hPM
  have hPsyl : CFSG.Quasithin.IsSylowIn p P M :=
    ⟨hPM, hP.isPGroup, fun hdvd => hP.not_dvd_relIndex
      (hdvd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex P M X hPM hMX)))⟩
  set P' : Sylow p M := hPsyl.toSylow with hP'def
  have hP' : (P' : Subgroup M) = P.subgroupOf M := hPsyl.coe_toSylow
  set K' : Subgroup M := K.subgroupOf M with hK'def
  set E' : Subgroup M := E.subgroupOf M with hE'def
  let eK : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKM
  have hcat : CatalogSimpleSections M := catalogSimpleSections_iff_isKGroup.2
    (CFSG.LocalAnalysis.GLTheoremA.openIsKGroup_sup_pGroup hp (openIsKGroup_of_isKGroup hK)
      hP.isPGroup (hP.le.trans hXN))
  have hyp : Hyp p K' P' E' :=
    { prime := hp
      ne_two := hp2
      normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMN
      sup_eq_top := by
        rw [hP', ← Subgroup.subgroupOf_sup hKM hPM, Subgroup.subgroupOf_self]
      quasi := isQuasisimple_of_mulEquiv eK.symm hq
      catalog := hcat
      core := primeComplementCore_eq_bot_of_mulEquiv eK.symm hcore
      E_le := by
        rw [hP']
        exact fun x hx => hEP hx
      elem := CFSG.Open.IsElemAbelian.subgroupOf hE M
      card_E := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv).trans hEc }
  have hrank : Open.pRank p (P' : Subgroup M) = Open.pRank p P := by
    rw [hP']
    exact CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf p hPM
  have hnot' : ¬ K' ≤ (if 3 ≤ Open.pRank p (P' : Subgroup M) then
      GLBWeakCore p (P' : Subgroup M) else GLBCore p 1 E') := by
    rw [hrank]
    intro hle
    apply hnot
    by_cases h3 : 3 ≤ Open.pRank p P
    · rw [if_pos h3] at hle ⊢
      have htr := CFSG.AGLEmbedding.P1Lie.weakCore_le_comap_map hp M.subtype
        (P := (P' : Subgroup M)) (fun x _ hx => M.subtype_injective (by simpa using hx))
      have hmap : (P' : Subgroup M).map M.subtype = P := by
        rw [hP', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPM]
      rw [hmap] at htr
      intro k hk
      exact htr (hle (show (⟨k, hKM hk⟩ : M) ∈ K' from hk))
    · rw [if_neg h3] at hle ⊢
      intro k hk
      exact glbCore_one_subgroupOf_le_comap p (hle (show (⟨k, hKM hk⟩ : M) ∈ K' from hk))
  obtain ⟨hlist, hZ⟩ := h p M K' P' E' hyp hnot'
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, ⟨f⟩⟩ := hlist
    exact ⟨i, hi, ⟨eK.symm.trans f⟩⟩
  · rw [eq_bot_iff]
    intro z hz
    have hz' : eK.symm z ∈ Subgroup.center K' := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply eK.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (eK g)
    rw [hZ, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg eK hz'

section Hyp

variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

theorem Hyp.isPGroup_center (H : Hyp p K P E) : IsPGroup p (Subgroup.center K) := by
  exact normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot p H.prime H.core _ inferInstance
    inferInstance

theorem Hyp.isComponentOf (H : Hyp p K P E) : IsComponentOf K ⊤ := by
  haveI := H.normal
  exact ⟨le_top, CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤),
    H.quasi⟩

theorem Hyp.centralizer_le (H : Hyp p K P E) :
    Subgroup.centralizer (K : Set G) ≤ (P : Subgroup G) := by
  haveI := H.normal
  haveI : Fact p.Prime := ⟨H.prime⟩
  refine IsPGroup.le_sylow_of_normal ?_ P
  have hmap : (P : Subgroup G).map (QuotientGroup.mk' K) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' K)) H.sup_eq_top
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] at h1
  intro c
  have hc : ((c : G) : G ⧸ K) ∈ (P : Subgroup G).map (QuotientGroup.mk' K) :=
    hmap ▸ Subgroup.mem_top _
  obtain ⟨x, hx, hxc⟩ := hc
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hck : (c : G) ^ p ^ k ∈ K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have : ((c : G) : G ⧸ K) = QuotientGroup.mk' K x := hxc.symm
    rw [this, ← map_pow, hxk, map_one]
  have hz : (⟨(c : G) ^ p ^ k, hck⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.pow_mem _ c.2 _) g g.2
  obtain ⟨j, hj⟩ := H.isPGroup_center ⟨_, hz⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have h2 : ((c : G) ^ p ^ k) ^ p ^ j = 1 := by
    simpa using congrArg (fun y : Subgroup.center K => ((y : K) : G)) hj
  simpa [pow_add, pow_mul] using h2

theorem Hyp.isCatalogGroup (H : Hyp p K P E) (hZ : Subgroup.center K = ⊥) :
    IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K := by
  have e₀ : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := H.quasi.2
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K H.quasi
  refine ⟨e₀.symm.isSimpleGroup, ⟨e₀ a, e₀ b, fun h => hab (e₀.injective ?_)⟩, ?_⟩
  · rw [map_mul, map_mul, h]
  · exact IsCatalogGroup.of_mulEquiv e₀.symm
      (H.catalog K (Subgroup.center K) inferInstance H.quasi.2 ⟨a, b, hab⟩)

theorem Hyp.false_of_cyclic (H : Hyp p K P E) {q : ℕ} {hq : q.Prime}
    (e : K ≃* (TauCeti.CFSGIndex.cyclic q hq).Group) : False := by
  have hcomm : ∀ a b : K, a * b = b * a := by
    intro a b
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod q)) (e a) (e b)
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := H.quasi.2
  obtain ⟨x, y, hxy⟩ := hsimple.toNontrivial.exists_pair_ne
  apply hxy
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [QuotientGroup.eq, Subgroup.mem_center_iff]
  intro z
  exact hcomm z _

theorem Hyp.center_eq_bot_of_centralizer_eq_bot (H : Hyp p K P E)
    (hC : Subgroup.centralizer (K : Set G) = ⊥) : Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzC : (z : G) ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩)
  rw [hC, Subgroup.mem_bot] at hzC
  exact Subgroup.mem_bot.2 (Subtype.ext hzC)

theorem Hyp.centralizer_eq_bot_of_two (H : Hyp p K P E)
    (h3 : ¬ 3 ≤ Open.pRank p (P : Subgroup G)) (hnot : ¬ K ≤ GLBCore p 1 E) :
    Subgroup.centralizer (K : Set G) = ⊥ := by
  haveI := H.normal
  haveI : Fact p.Prime := ⟨H.prime⟩
  by_contra hC
  have hCP : Subgroup.centralizer (K : Set G) ≤ (P : Subgroup G) := H.centralizer_le
  obtain ⟨z₀, hz₀C, hz₀1, hz₀c⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_central_of_normal H.prime
    P.isPGroup' hCP
    (fun g _ u hu => (inferInstance : (Subgroup.centralizer (K : Set G)).Normal).conj_mem u hu g)
    hC
  have hzp : IsPGroup p (Subgroup.zpowers z₀) :=
    P.isPGroup'.to_le (Subgroup.zpowers_le.2 (hCP hz₀C))
  obtain ⟨k, hk⟩ := hzp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hz₀1
    have h1 : orderOf z₀ = 1 := by rw [← Nat.card_zpowers, hk, pow_zero]
    exact orderOf_eq_one_iff.1 h1
  obtain ⟨⟨z, hz⟩, hzo⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers z₀) p
    (by rw [hk]; exact dvd_pow_self p hk0)
  rw [Subgroup.orderOf_mk] at hzo
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hzC : z ∈ Subgroup.centralizer (K : Set G) := hj ▸ Subgroup.zpow_mem _ hz₀C j
  have hzc : ∀ g ∈ (P : Subgroup G), g * z = z * g := fun g hg => by
    rw [← hj]
    exact (Commute.zpow_right (show Commute g z₀ from hz₀c g hg) j).eq
  have hzpow : z ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzE : z ∈ E := by
    have hA : IsElemAbelian p (E ⊔ Subgroup.zpowers z) :=
      CFSG.Open.IsElemAbelian.sup_of_commute H.elem (CFSG.Open.isElemAbelian_zpowers hzpow) (by
        rintro a ha b ⟨n, rfl⟩
        exact (Commute.zpow_right (show Commute a z from hzc a (H.E_le ha)) n).eq)
    have hAP : E ⊔ Subgroup.zpowers z ≤ (P : Subgroup G) :=
      sup_le H.E_le (Subgroup.zpowers_le.2 (hCP hzC))
    obtain ⟨m, hm⟩ := (P.isPGroup'.to_le hAP).exists_card_eq
    have hEA : p ^ 2 ∣ Nat.card (E ⊔ Subgroup.zpowers z : Subgroup G) :=
      H.card_E ▸ Subgroup.card_dvd_of_le le_sup_left
    rw [hm] at hEA
    have hm2 : 2 ≤ m := (Nat.pow_dvd_pow_iff_le_right H.prime.one_lt).1 hEA
    have hm3 : m < 3 := by
      by_contra hm3
      have := CFSG.GH74.Uniqueness.SU.SU1.le_pRank H.prime.one_lt hAP hA hm
      omega
    have heq : E = E ⊔ Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, H.card_E, show m = 2 by omega])
    rw [heq]
    exact (le_sup_right : Subgroup.zpowers z ≤ E ⊔ Subgroup.zpowers z) (Subgroup.mem_zpowers z)
  apply hnot
  intro x hx
  have hrank : 1 ≤ Open.pRank p (Subgroup.zpowers z) :=
    CFSG.GH74.Uniqueness.SU.SU1.le_pRank H.prime.one_lt le_rfl
      (CFSG.Open.isElemAbelian_zpowers hzpow) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hN : Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ≤ GLBCore p 1 E :=
    le_sSup ⟨Subgroup.zpowers z, Subgroup.zpowers_le.2 hzE, hrank, rfl⟩
  refine hN (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_))
  rintro y ⟨n, rfl⟩
  exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.1 hzC x hx).symm n).eq

theorem Hyp.le_of_not_dvd_card_outer (H : Hyp p K P E)
    (hC : Subgroup.centralizer (K : Set G) = ⊥) (hout : ¬ p ∣ Nat.card (Outer K)) :
    (P : Subgroup G) ≤ K := by
  haveI := H.normal
  intro x hx
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  have := mem_sup_centralizer_of_not_dvd_card_outer H.prime hout hxN hxk
  rwa [hC, sup_bot_eq] at this

theorem Hyp.le_weakCore_of_sylow (H : Hyp p K P E)
    (hT : ∀ T : Sylow p K, GLBWeakCore p (T : Subgroup K) = ⊤) :
    K ≤ GLBWeakCore p (P : Subgroup G) := by
  haveI := H.normal
  haveI : Fact p.Prime := ⟨H.prime⟩
  set T := CFSG.QuasiDihedralFusion.sylowInfNormal P K
  have h1 := P1Lie.weakCore_le_comap_map H.prime K.subtype (P := (T : Subgroup K))
    (fun x _ hx => K.subtype_injective (by simpa using hx))
  rw [hT T] at h1
  have hTmap : (T : Subgroup K).map K.subtype ≤ (P : Subgroup G) := by
    rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  intro x hx
  exact CFSG.PreuniquenessRankFour.Helpers.weakCore_mono p H.prime hTmap
    (h1 (Subgroup.mem_top (⟨x, hx⟩ : K)))

theorem Hyp.pRank_top_le (H : Hyp p K P E) :
    Open.pRank p (⊤ : Subgroup K) ≤ Open.pRank p (P : Subgroup G) := by
  haveI := H.normal
  haveI : Fact p.Prime := ⟨H.prime⟩
  set T := CFSG.QuasiDihedralFusion.sylowInfNormal P K
  rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p H.prime T,
    ← CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p K.subtype_injective]
  refine CFSG.PreuniquenessRankFour.Helpers.pRank_mono p H.prime ?_
  rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_map_subtype]
  exact inf_le_left

theorem Hyp.pRank_le_of_le (H : Hyp p K P E) (hPK : (P : Subgroup G) ≤ K) :
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (⊤ : Subgroup K) := by
  rw [← CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf p hPK]
  exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono p H.prime le_top

theorem Hyp.elem_subgroupOf (H : Hyp p K P E) (hEK : E ≤ K) :
    IsElemAbelian p (E.subgroupOf K) ∧ Nat.card (E.subgroupOf K) = p ^ 2 := by
  exact ⟨CFSG.Open.IsElemAbelian.subgroupOf H.elem K,
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv).trans H.card_E⟩

theorem Hyp.card_eq_sq_of_not_dvd (H : Hyp p K P E) (hPK : (P : Subgroup G) ≤ K)
    (h3 : ¬ p ^ 3 ∣ Nat.card K) : Nat.card (P : Subgroup G) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hE : p ^ 2 ∣ Nat.card (P : Subgroup G) := H.card_E ▸ Subgroup.card_dvd_of_le H.E_le
  have hK : Nat.card (P : Subgroup G) ∣ Nat.card K := Subgroup.card_dvd_of_le hPK
  rw [hk] at hE hK ⊢
  have h2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right H.prime.one_lt).1 hE
  have h3' : k < 3 := by
    by_contra hc
    exact h3 ((Nat.pow_dvd_pow p (by omega)).trans hK)
  have : k = 2 := by omega
  rw [this]

end Hyp

theorem le_glbCore_one_of_subgroupOf {G : Type} [Group G] [Finite G] {p : ℕ} {K E : Subgroup G}
    (hEK : E ≤ K) (h : GLBCore p 1 (E.subgroupOf K) = ⊤) : K ≤ GLBCore p 1 E := by
  have key : GLBCore p 1 (E.subgroupOf K) ≤ (GLBCore p 1 E).comap K.subtype := by
    refine sSup_le ?_
    rintro N ⟨Q, hQ, hQ1, rfl⟩ x hx
    have hQm : Q.map K.subtype ≤ E := by
      refine (Subgroup.map_mono hQ).trans ?_
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    have hrank : 1 ≤ Open.pRank p (Q.map K.subtype) := by
      rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
        K.subtype_injective]
      exact hQ1
    exact (le_sSup ⟨Q.map K.subtype, hQm, hrank, rfl⟩ :
      Subgroup.normalizer ((Q.map K.subtype : Subgroup G) : Set G) ≤ GLBCore p 1 E)
      (Subgroup.le_normalizer_map K.subtype ⟨x, hx, rfl⟩)
  intro x hx
  exact key (h ▸ Subgroup.mem_top (⟨x, hx⟩ : K))

theorem le_weakCore_of_hyperGen {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P K E₃ : Subgroup G} (hE₃P : E₃ ≤ P) (hE : IsElemAbelian p E₃) (hc : Nat.card E₃ = p ^ 3)
    (hg : HyperGen p K E₃) : K ≤ GLBWeakCore p P := by
  refine hg.trans ((Subgroup.closure_le _).2 ?_)
  rintro k ⟨-, F, hFE, hrel, hF⟩
  have hFcard : Nat.card F = p ^ 2 := by
    have h1 : Nat.card (F.subgroupOf E₃) * F.relIndex E₃ = Nat.card E₃ :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (F.subgroupOf E₃) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
    rw [h2, hrel, hc] at h1
    have : p ^ 3 = p ^ 2 * p := by ring
    rw [this] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hFa : IsElemAbelian p F := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
    refine Subtype.ext ?_
    have h0 := hE.1.is_comm.comm (⟨a, hFE a.2⟩ : E₃) ⟨b, hFE b.2⟩
    have h1 := congrArg Subtype.val h0
    exact h1
  have hEC : E₃ ≤ Subgroup.centralizer (F : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun f hf =>
      congrArg Subtype.val (hE.1.is_comm.comm (⟨f, hFE hf⟩ : E₃) ⟨e, he⟩)
  have h2 : 2 ≤ Open.pRank p F :=
    CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian_of_pow_le_card hp hFa le_rfl (n := 2)
      (by rw [hFcard])
  have h3 : 3 ≤ Open.pRank p (F ⊔ (P ⊓ Subgroup.centralizer (F : Set G))) :=
    CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian_of_pow_le_card hp hE
      (le_sup_of_le_right (le_inf hE₃P hEC)) (n := 3) (by rw [hc])
  exact CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p (hFE.trans hE₃P) h2 h3
    (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hF))

theorem onThreeOneList_of_isSmallStrongP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type}
    [Group K] (h : IsSmallStrongP p K) : OnThreeOneList p K := by
  rcases h with ⟨d, ⟨q, hq, hqp, hqe⟩, ⟨e⟩⟩ | ⟨d, ⟨q, hqp, -, hq⟩, ⟨e⟩⟩ | ⟨e⟩ | ⟨hp3, h⟩ |
    ⟨hp5, h⟩ | ⟨hp11, e⟩
  · exact ⟨.lie d, Or.inl (Or.inl ⟨q, hqp, by omega, hq⟩), ⟨e⟩⟩
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inl ⟨q, hqp, hq⟩)), ⟨e⟩⟩
  · have h5 : 5 ≤ 2 * p := by have := hp.two_le; omega
    exact ⟨.alternating (2 * p) h5, Or.inr (Or.inr ⟨2 * p, h5, rfl, Or.inl rfl⟩), e⟩
  · rcases h with ⟨d, ⟨q, hq2, hqe, hq⟩, ⟨e⟩⟩ | e
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hp3, Or.inr (Or.inl ⟨q, hq2, hqe, hq⟩)⟩)))))), ⟨e⟩⟩
    · exact ⟨.sporadic .M11, Or.inl (Or.inl ⟨hp3, Or.inl rfl⟩), e⟩
  · rcases h with ⟨d, hd, ⟨e⟩⟩ | e | e
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hp5, Or.inr (Or.inl hd)⟩)))))), ⟨e⟩⟩
    · exact ⟨.sporadic .McL, Or.inl (Or.inr (Or.inl ⟨hp5, Or.inl rfl⟩)), e⟩
    · exact ⟨.sporadic .Fi22, Or.inr (Or.inl ⟨hp5, rfl⟩), e⟩
  · exact ⟨.sporadic .J4, Or.inl (Or.inr (Or.inr (Or.inr ⟨hp11, rfl⟩))), e⟩

theorem onThreeOneList_of_oneLie {p : ℕ} {K : Type} [Group K]
    (h : ∃ d : TauCeti.ValidLieTypeIndex,
      ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨ (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
        IsReeGTwoIndex p d) ∧ Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    OnThreeOneList p K := by
  obtain ⟨d, ⟨n, hn, q, hq, hqp, hqe⟩ | ⟨⟨q, hqp, hq⟩, -⟩ | hd, ⟨e⟩⟩ := h
  · exact ⟨.lie d, Or.inl (Or.inl ⟨q, hqp, by omega, hq⟩), ⟨e⟩⟩
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inl ⟨q, hqp, hq⟩)), ⟨e⟩⟩
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd))))), ⟨e⟩⟩

theorem onThreeOneList_of_isCaseTwoGroup {p : ℕ} {K : Type} [Group K]
    (h : IsCaseTwoGroup p K) : OnThreeOneList p K := by
  obtain ⟨d, ⟨hp3, q, hq2, hq3, hq⟩ | ⟨hp5, hq⟩, ⟨e⟩⟩ := h
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp3, Or.inl ⟨q, hq2, hq3, Or.inl hq⟩⟩)))))), ⟨e⟩⟩
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hp5, Or.inl hq⟩)))))), ⟨e⟩⟩

theorem OnThreeOneList.of_mulEquiv {p : ℕ} {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : OnThreeOneList p L) : OnThreeOneList p K := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
