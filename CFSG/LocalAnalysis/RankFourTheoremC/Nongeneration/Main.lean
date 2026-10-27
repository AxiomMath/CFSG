module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.KFacts
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
import CFSG.LocalAnalysis.RankFourTheoremC.NongenerationMonster
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Generation
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem exists_type_of_isSmallStrongP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    (h : IsSmallStrongP p K) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (K ≃* i.Group) ∧ GL83Type24 p i := by
  rcases h with h | h | h | ⟨hp3, h⟩ | ⟨hp5, h⟩ | ⟨hp11, h⟩
  · obtain ⟨d, hd, ⟨e⟩⟩ := h
    exact ⟨.lie d, ⟨e⟩, .linTwo le_rfl hd⟩
  · obtain ⟨d, ⟨q, hqp, -, hq⟩, ⟨e⟩⟩ := h
    exact ⟨.lie d, ⟨e⟩, .unitary ⟨q, hqp, hq⟩⟩
  · obtain ⟨e⟩ : Nonempty (K ≃* alternatingGroup (Fin (2 * p))) := h
    have h5 : 5 ≤ 2 * p := by have := hp.two_le; omega
    exact ⟨.alternating (2 * p) h5, ⟨e⟩, .altTwoP h5⟩
  · rcases h with ⟨d, ⟨q, hqp, hqe, hq⟩, ⟨e⟩⟩ | ⟨e⟩
    · exact ⟨.lie d, ⟨e⟩, .linThreeFour hp3 ⟨q, hq, hqp, hqe⟩⟩
    · exact ⟨.sporadic .M11, e, .mEleven hp3⟩
  · rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩
    · exact ⟨.lie d, ⟨e⟩, .tits hp5 hd⟩
    · exact ⟨.sporadic .McL, e, .mcl hp5⟩
    · exact ⟨.sporadic .Fi22, e, .fiTwentyTwo hp5⟩
  · exact ⟨.sporadic .J4, h, .jFour hp11⟩

theorem exists_type_of_oneLie {p : ℕ} {K : Type} [Group K]
    (h : ∃ d : TauCeti.ValidLieTypeIndex,
      ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨ (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
        IsReeGTwoIndex p d) ∧ Nonempty (K ≃* CatGroup d)) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (K ≃* i.Group) ∧ GL83Type24 p i := by
  obtain ⟨d, hd | ⟨hd, -⟩ | hd, ⟨e⟩⟩ := h
  · obtain ⟨n, hn, hd⟩ := hd
    exact ⟨.lie d, ⟨e⟩, .linTwo (by omega) hd⟩
  · exact ⟨.lie d, ⟨e⟩, .unitary hd⟩
  · exact ⟨.lie d, ⟨e⟩, .ree hd⟩

theorem exists_type_of_caseTwo {p : ℕ} {K : Type} [Group K] (h : IsCaseTwoGroup p K) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (K ≃* i.Group) ∧ GL83Type24 p i ∧ GL83OuterType24 p i := by
  obtain ⟨d, hd | hd, ⟨e⟩⟩ := h
  · obtain ⟨hp3, q, hqp, hqe, hq⟩ := hd
    exact ⟨.lie d, ⟨e⟩, .linTwoEight hp3 ⟨q, hq, hqp, hqe⟩, d, rfl,
      Or.inl ⟨hp3, q, hq, hqp, hqe⟩⟩
  · obtain ⟨hp5, hq⟩ := hd
    exact ⟨.lie d, ⟨e⟩, .suzuki hp5 hq, d, rfl, Or.inr ⟨hp5, hq⟩⟩

theorem exists_central_orderOf {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (R : Sylow p X) {N : Subgroup X} [N.Normal] (hne : (R : Subgroup X) ⊓ N ≠ ⊥) :
    ∃ z ∈ (R : Subgroup X) ⊓ N, orderOf z = p ∧ ∀ g ∈ (R : Subgroup X), g * z = z * g := by
  have hp : p.Prime := Fact.out
  obtain ⟨z, hzU, hz1, hzc⟩ := GH74.Uniqueness.SU.SU1.exists_central_of_normal hp R.isPGroup'
    (inf_le_left : (R : Subgroup X) ⊓ N ≤ R)
    (fun g hg u hu => ⟨R.mul_mem (R.mul_mem hg hu.1) (R.inv_mem hg),
      Subgroup.Normal.conj_mem inferInstance u hu.2 g⟩) hne
  have hzle : zpowers z ≤ (R : Subgroup X) ⊓ N := Subgroup.zpowers_le.2 hzU
  have hAp : IsPGroup p (zpowers z) := R.isPGroup'.to_le (hzle.trans inf_le_left)
  have hA1 : zpowers z ≠ ⊥ := fun h => hz1 (by simpa [h] using Subgroup.mem_zpowers z)
  obtain ⟨a, ha, hao⟩ := exists_mem_orderOf_eq_of_isPGroup_ne_bot hAp hA1
  refine ⟨a, hzle ha, hao, fun g hg => ?_⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact (Commute.zpow_right (show Commute g z from hzc g hg) j).eq

theorem card_le_of_le_centralizer {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {R K : Subgroup X} (hnot : ¬ K ≤ GLBCore p 2 R) {B : Subgroup X} (hBR : B ≤ R)
    (hBK : B ≤ centralizer (K : Set X)) (hB : IsElemAbelian p B) : Nat.card B ≤ p := by
  have hp : p.Prime := Fact.out
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hB
  have hk2 : 2 ≤ k := by
    by_contra h
    have h1 : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at h1
    omega
  obtain ⟨W, hWB, hWel, hWcard⟩ := GH74.Uniqueness.SU.SU1.exists_vertex_le hp hB
    (by rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2)
  have hrk : 2 ≤ Open.pRank p W := GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_rfl hWel hWcard
  apply hnot
  intro x hx
  have hnorm : x ∈ normalizer (W : Set X) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (hBK (hWB hw)) x hx).symm)
  exact (le_sSup ⟨W, hWB.trans hBR, hrk, rfl⟩ : normalizer (W : Set X) ≤ GLBCore p 2 R) hnorm

theorem not_dvd_card_center_of_pCore_eq_bot {K : Type*} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (h : CFSG.pCore p K = ⊥) : ¬ p ∣ Nat.card (center K) := by
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center K) p hd
  have hNc : zpowers (z : K) ≤ center K := Subgroup.zpowers_le.2 z.2
  have hNp : IsPGroup p (zpowers (z : K)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
  have hle : zpowers (z : K) ≤ CFSG.pCore p K :=
    le_sSup ⟨Subgroup.normal_of_le_center hNc, hNp⟩
  rw [h, le_bot_iff] at hle
  have h1 : (z : K) = 1 := by
    have := hle ▸ Subgroup.mem_zpowers (z : K)
    simpa using this
  rw [show z = 1 from Subtype.ext h1, orderOf_one] at hz
  exact (Fact.out : p.Prime).one_lt.ne hz

theorem inf_ne_bot_of_two_le_pRank {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (R : Sylow p X) (K : Subgroup X) [K.Normal]
    (h : 2 ≤ Open.pRank p (⊤ : Subgroup (K ⧸ center K))) : (R : Subgroup X) ⊓ K ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, -, hEel, hEcard⟩ :=
    GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp (H := (⊤ : Subgroup (K ⧸ center K)))
      h
  have h1 : p ∣ Nat.card (K ⧸ center K) := by
    have := Subgroup.card_subgroup_dvd_card E
    rw [hEcard] at this
    exact (dvd_pow_self p (by norm_num)).trans this
  have hpK : p ∣ Nat.card K :=
    h1.trans (Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)).symm)
  intro hbot
  have hne := Sylow.ne_bot_of_dvd_card (QuasiDihedralFusion.sylowInfNormal R K) hpK
  apply hne
  rw [QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_eq_bot]
  exact disjoint_iff.2 hbot

theorem pRank_top_subgroup_top {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K] :
    CFSG.pRank p ↥(⊤ : Subgroup K) = Open.pRank p (⊤ : Subgroup K) := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt Subgroup.topEquiv

theorem not_isCyclic_sylow_of_two_le_pRank {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (h : 2 ≤ Open.pRank p (⊤ : Subgroup K)) (T : Sylow p K) : ¬ IsCyclic (T : Subgroup K) := by
  intro hcyc
  have hp : p.Prime := Fact.out
  rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hp T] at h
  obtain ⟨E, hET, hEel, hEcard⟩ := GH74.Uniqueness.SU.SU1.exists_pRank hp.one_lt (T : Subgroup K)
  haveI : IsCyclic (T : Subgroup K) := hcyc
  haveI : IsCyclic E := Subgroup.isCyclic_of_le hET
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hord : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEel.2 g g.2))
  have hcard : Nat.card E = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hle : Nat.card E ≤ p := hcard ▸ Nat.le_of_dvd hp.pos hord
  rw [hEcard] at hle
  have h2 : p ^ 2 ≤ p ^ Open.pRank p (T : Subgroup K) := Nat.pow_le_pow_right hp.pos h
  have h3 : p < p ^ 2 := by
    have := hp.one_lt
    nlinarith
  omega

theorem dvd_card_of_plane {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hcenter : center K = ⊥)
    (hout : Open.pRank p (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer K))
      ≤ 1)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    p ∣ Nat.card K := by
  have hp : p.Prime := Fact.out
  by_contra hndvd
  have hinj := conj_injective_of_center_eq_bot hcenter
  have hqinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)).comp
        E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at he
    obtain ⟨kb, hkb'⟩ := he
    have hkb : MulAut.conj kb = (e : MulAut K) := hkb'
    have hkbp : kb ^ p = 1 := hinj (by rw [map_pow, hkb, map_one]; exact hE.2 e e.2)
    have hord : orderOf kb ∣ p := orderOf_dvd_of_pow_eq_one hkbp
    have hone : orderOf kb = 1 := by
      rcases (Nat.dvd_prime hp).1 hord with h | h
      · exact h
      · exact absurd (h ▸ orderOf_dvd_natCard kb) hndvd
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hkb, orderOf_eq_one_iff.1 hone, map_one]
    rfl
  have := hE.1
  have h2 := CFSG.SectionRank.le_pRank_of_injective (p := p) hp.one_lt
    (fun a b => mul_comm' a b) (fun a => Subtype.ext (hE.2 a a.2)) hEcard _ hqinj (H := ⊤) le_top
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration Subgroup

theorem gl83NongenerationList_of_kfacts (h243 : GL83ComponentPCoreTrivial) (h241 : GL83I241)
    (h7131 : GL83.I_7_13_1) (h7132 : KFactSeitzCyc) (h2316 : GL83I2316) :
    GL83NongenerationList := by
  intro X _ _ hcat p R K hp hp2 hrk hKc hKn hC hnot
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hKn
  have hperf : commutator ↥K = ⊤ := hKc.2.2.1
  have hsimple : IsSimpleGroup (↥K ⧸ center ↥K) := hKc.2.2.2
  have hnonab : ∃ a b : ↥K ⧸ center ↥K, a * b ≠ b * a := exists_noncomm_center_quotient hperf
  have hcatK : IsCatalogGroup (↥K ⧸ center ↥K) := hcat K (center ↥K) inferInstance hsimple hnonab
  have hcenter : center (↥K ⧸ center ↥K) = ⊥ := center_eq_bot_of_simple hnonab
  have hW : GLBWeakCore p (R : Subgroup X) ≤ GLBCore p 2 (R : Subgroup X) := by
    refine sSup_le_sSup ?_
    rintro N ⟨Q, hQR, hQ2, -, rfl⟩
    exact ⟨Q, hQR, hQ2, rfl⟩
  have hZ : ¬ p ∣ Nat.card (center ↥K) := not_dvd_card_center_of_pCore_eq_bot
    (h243 X hcat p R K hp hp2 hrk hKc fun hle => hnot (hle.trans hW))
  obtain ⟨c, ⟨hcR, hcK⟩, hcp, hcc⟩ := exists_central_orderOf R (N := centralizer (K : Set X)) hC
  obtain ⟨T, hT⟩ : ∃ T : Sylow p (↥K ⧸ center ↥K),
      GLBCore p 1 (T : Subgroup (↥K ⧸ center ↥K)) ≠ ⊤ := by
    by_contra hcon
    push Not at hcon
    haveI : Nontrivial (↥K ⧸ center ↥K) := hsimple.toNontrivial
    exact hnot (le_glbCore_two_of_central_cover R (QuotientGroup.mk' (center ↥K))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hZ hC hcon)
  by_cases hcase : 2 ≤ Open.pRank p (⊤ : Subgroup (↥K ⧸ center ↥K))
  ·
    have hTnc := not_isCyclic_sylow_of_two_le_pRank hcase T
    have hlist : ∃ i : TauCeti.CFSGIndex, Nonempty (↥K ⧸ center ↥K ≃* i.Group) ∧
        GL83Type24 p i := by
      by_cases h2 : Open.pRank p (⊤ : Subgroup (↥K ⧸ center ↥K)) ≤ 2
      · exact exists_type_of_isSmallStrongP hp hp2 (h241.1 _ hsimple hnonab hcatK p hp hp2 T hTnc hT
          ((pRank_top_subgroup_top hp).trans_le h2))
      · refine exists_type_of_oneLie
          (h241.2 _ hsimple hnonab hcatK p hp hp2 T hTnc hT fun h => h2 ?_)
        exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt _
          (conj_injective_of_center_eq_bot hcenter)).trans h
    obtain ⟨i, e, hi⟩ := hlist
    refine ⟨i, e, hi, Or.inr fun g hgR hgp => ?_⟩
    by_contra hgK
    obtain ⟨z, ⟨hzR, hzK⟩, hzp, hzc⟩ :=
      exists_central_orderOf R (N := K) (inf_ne_bot_of_two_le_pRank R K hcase)
    obtain ⟨E, hEel, hEcard, hEnot, hEA⟩ :=
      exists_outer_plane_of_elt hperf hZ hgp hgK hzK hzp (hzc g hgR)
    have hzp' : z ^ p = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
    have hAR : zpowers g ⊔ zpowers z ≤ (R : Subgroup X) :=
      sup_le (Subgroup.zpowers_le.2 hgR) (Subgroup.zpowers_le.2 hzR)
    have hAel : IsElemAbelian p (zpowers g ⊔ zpowers z) :=
      IsElemAbelian.sup_of_commute (GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hgp)
        (GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hzp') (by
          rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
          exact (Commute.zpow_zpow (show Commute g z from hzc g hgR) m n).eq)
    exact hnot (le_glbCore_two_of_closure_fixed hperf hZ hAR hAel hcR hcK hcp
      (fun a ha => hcc a (hAR ha)) hEA
      (h2316 _ hsimple hnonab hcatK p hp hp2 T hTnc hT E hEel hEcard hEnot))
  ·
    have hrk1 : Open.pRank p (⊤ : Subgroup (↥K ⧸ center ↥K)) ≤ 1 := by omega
    obtain ⟨A, hAR, hAel, hAcard⟩ :=
      GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp (H := (R : Subgroup X))
        (k := 3) hrk
    have hcen : Nat.card ↥(A ⊓ centralizer (K : Set X)) ≤ p :=
      card_le_of_le_centralizer hnot (inf_le_left.trans hAR) inf_le_right (hAel.mono inf_le_left)
    obtain ⟨E, hEel, hEcard, hEnot, hEA⟩ := exists_outer_plane hperf hAel hAcard hcen hrk1
    have hgen : Subgroup.closure {kb : ↥K ⧸ center ↥K | ∃ e ∈ E, e ≠ 1 ∧ e kb = kb} ≠ ⊤ :=
      fun hgen => hnot (le_glbCore_two_of_closure_fixed hperf hZ hAR hAel hcR hcK hcp
        (fun a ha => hcc a (hAR ha)) hEA hgen)
    have hpdvd : p ∣ Nat.card (↥K ⧸ center ↥K) := dvd_card_of_plane hcenter
      (h7131 p hp hp2 (↥K ⧸ center ↥K) hsimple hnonab hcatK hrk1).1 hEel hEcard
    have hTcyc := isCyclic_sylow_of_pRank_le_one hp2 hrk1 T
    obtain ⟨i, e, hi, hio⟩ := exists_type_of_caseTwo (h7132 _ hsimple hnonab hcatK p hp hp2 T
      (Sylow.ne_bot_of_dvd_card T hpdvd) hTcyc E hEel hEcard hEnot hgen)
    exact ⟨i, e, hi, Or.inl hio⟩

end CFSG.LocalAnalysis.RankFourTheoremC
