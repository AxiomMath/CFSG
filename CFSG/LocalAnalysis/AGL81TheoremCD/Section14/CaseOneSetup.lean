module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneThreeStarImg
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.Quasithin.Background.A3Structure318Star
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6CentralizingBase
import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.LocalAnalysis.RankThreeUC.AGL81CPComp

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open scoped commutatorElement Pointwise
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (gnV gnC gnImg)

variable {G : Type} [Group G] [Finite G]

private instance instSubgroupConjAction (Q : Subgroup G) : MulAction ↥Q (Subgroup G) :=
  MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp Q.subtype)

theorem S14Choice.isKComp {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J) :
    IsKComp M H J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H', -, hK', -⟩ := h.J_star.1
  have hintr := (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff
    3 J (kSub 3 M H') hK'.1).mp hK'.2
  exact ⟨h.J_comp.1,
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff
      3 J (kSub 3 M H) h.J_comp.1).mpr ⟨h.J_comp.2.1, hintr.2.1, hintr.2.2⟩⟩

theorem Is3A6Star.card_threeStar {J : Subgroup G} (h : Is3A6Star J) :
    Nat.card (threeStar J) = 1080 := by
  obtain ⟨e⟩ := h.1
  have hmul := Subgroup.card_mul_index (Subgroup.center (threeStar J))
  rw [h.2, Subgroup.index_eq_card, Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hmul
  norm_num at hmul
  omega

theorem S14Choice.isSL34Star_of_typeA
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hA : TypeA M H) : IsSL34Star J := by
  have hfive := (hpre 3 Q (h.Q_mem_QSet hU) H h.mem_H2StarFam).2
  obtain ⟨J₀, hJ₀, hSL₀⟩ := hA
  rcases hfive with ⟨hK, -⟩ | ⟨J₁, J₂, hne, hJ₁, hJ₂, hsup, honly, hSL₁, hSL₂⟩
  · have hJeq : J = kSub 3 M H := IsKComp.eq_kSub_of_isKComp_self hK h.isKComp
    have hJ₀eq : J₀ = kSub 3 M H := IsKComp.eq_kSub_of_isKComp_self hK hJ₀
    simpa [hJeq, hJ₀eq] using hSL₀
  · rcases honly J h.isKComp with hJ | hJ
    · simpa [hJ] using hSL₁
    · rcases hSL₂ with hSL₂ | hA6
      · simpa [hJ] using hSL₂
      · exfalso
        subst hJ
        obtain ⟨H', hH', hKJ, hL34orA11⟩ := h.J_star.1
        have hcard := Is3A6Star.card_threeStar hA6
        rcases hL34orA11 with hL34 | hA11
        · rcases IsKComp.isL34Star_or_isSL34Star hKJ hL34 with hL | hSL
          · rw [IsL34Star.card_threeStar hL] at hcard
            norm_num at hcard
          · rw [IsSL34Star.card_threeStar hSL] at hcard
            norm_num at hcard
        · rw [IsA11Star.card_threeStar hA11] at hcard
          norm_num at hcard

theorem CaseOneCtx.isKComp {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T) :
    IsKComp M H J :=
  c.choice.isKComp

theorem CaseOneCtx.isSL34Star
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) : IsSL34Star J :=
  c.choice.isSL34Star_of_typeA c.pre c.nine c.typeA

theorem isPComponentIn_conj_of_mem_normalizer {p : ℕ} {K J : Subgroup G} {y : G}
    (hJ : IsPComponentIn p J K) (hy : y ∈ Subgroup.normalizer (K : Set G)) :
    IsPComponentIn p (J.map (MulAut.conj y).toMonoidHom) K := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hy j).mp (hJ.1 hj)
  · let φ : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨y, hy⟩
    have h1 : (J.map (MulAut.conj y).toMonoidHom).subgroupOf K =
        (J.subgroupOf K).map φ.toMonoidHom := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨a, ha, haz⟩
        refine ⟨⟨a, hJ.1 ha⟩, ha, ?_⟩
        apply Subtype.ext
        simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using haz
      · rintro ⟨b, hb, hbz⟩
        refine ⟨b, hb, ?_⟩
        simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using
          congrArg Subtype.val hbz
    rw [h1]
    exact isPComponent_map p φ hJ.2

private theorem le_normalizer_of_le_normalizer_subgroupOf {K A B : Subgroup G}
    (hAK : A ≤ K) (hBK : B ≤ K)
    (h : B.subgroupOf K ≤ Subgroup.normalizer ((A.subgroupOf K) : Set ↥K)) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hbK : b ∈ K := hBK hb
  have hmap := h (show (⟨b, hbK⟩ : ↥K) ∈ B.subgroupOf K from hb)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hmap
  have hcomp : (MulAut.conj b).toMonoidHom.comp K.subtype =
      K.subtype.comp (MulAut.conj (⟨b, hbK⟩ : ↥K)).toMonoidHom := by
    ext x
    rfl
  have hmap' : (A.subgroupOf K).map
      (MulAut.conj (⟨b, hbK⟩ : ↥K)).toMonoidHom = A.subgroupOf K := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using hmap
  calc A.map (MulAut.conj b).toMonoidHom
      = (A.subgroupOf K).map ((MulAut.conj b).toMonoidHom.comp K.subtype) := by
        conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hAK]
        rw [Subgroup.map_map]
    _ = (A.subgroupOf K).map
          (K.subtype.comp (MulAut.conj (⟨b, hbK⟩ : ↥K)).toMonoidHom) := by
        rw [hcomp]
    _ = ((A.subgroupOf K).map (MulAut.conj (⟨b, hbK⟩ : ↥K)).toMonoidHom).map K.subtype := by
        rw [Subgroup.map_map]
    _ = A := by
        rw [hmap', Subgroup.map_subgroupOf_eq_of_le hAK]

theorem S14Choice.Q_le_normalizer_kSub {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hU : NineNineOneAt M) :
    Q ≤ Subgroup.normalizer (kSub 3 M H : Set G) := by
  refine h.sylow.le.trans (sup_le (Subgroup.le_normalizer) ?_)
  intro e he
  exact inf_le_normalizer_kSub 3 M H ⟨h.E_le_H he, h.hypCGen.E_le_M he⟩

theorem FiveTypes.kSub_le_normalizer_of_isKComp {M N J' : Subgroup G} (hfive : FiveTypes M N)
    (hJ' : IsKComp M N J') : kSub 3 M N ≤ Subgroup.normalizer (J' : Set G) := by
  rcases hfive with ⟨hK, -⟩ | ⟨J₁, J₂, hne, hJ₁, hJ₂, hsup, honly, hSL₁, hSL₂⟩
  · have hJeq : J' = kSub 3 M N := IsKComp.eq_kSub_of_isKComp_self hK hJ'
    rw [hJeq]
    exact Subgroup.le_normalizer
  · have hneK : J₁.subgroupOf (kSub 3 M N) ≠ J₂.subgroupOf (kSub 3 M N) := by
      intro heq
      apply hne
      have h1 := congrArg (Subgroup.map (kSub 3 M N).subtype) heq
      rwa [Subgroup.map_subgroupOf_eq_of_le hJ₁.1,
        Subgroup.map_subgroupOf_eq_of_le hJ₂.1] at h1
    obtain ⟨hJ₂N, hJ₁N, -⟩ :=
      CFSG.ComponentClassification.CatalogueBPrimeJoin.mutual_normalization_core_commutation
        3 (J₁.subgroupOf (kSub 3 M N)) (J₂.subgroupOf (kSub 3 M N)) hJ₁.2 hJ₂.2 hneK
    have hJ₂NG : J₂ ≤ Subgroup.normalizer (J₁ : Set G) :=
      le_normalizer_of_le_normalizer_subgroupOf hJ₁.1 hJ₂.1 hJ₂N
    have hJ₁NG : J₁ ≤ Subgroup.normalizer (J₂ : Set G) :=
      le_normalizer_of_le_normalizer_subgroupOf hJ₂.1 hJ₁.1 hJ₁N
    rcases honly J' hJ' with hJ | hJ
    · rw [hsup, hJ]
      exact sup_le (Subgroup.le_normalizer) hJ₂NG
    · rw [hsup, hJ]
      exact sup_le hJ₁NG (Subgroup.le_normalizer)

theorem S14Choice.kSub_le_normalizer_of_isKComp {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    {J' : Subgroup G} (hJ' : IsKComp M H J') :
    kSub 3 M H ≤ Subgroup.normalizer (J' : Set G) :=
  (hpre 3 Q (h.Q_mem_QSet hU) H h.mem_H2StarFam).2.kSub_le_normalizer_of_isKComp hJ'

theorem S14Choice.kSub_le_normalizer_J {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M) :
    kSub 3 M H ≤ Subgroup.normalizer (J : Set G) :=
  h.kSub_le_normalizer_of_isKComp hpre hU h.isKComp

theorem orbit_card_one_of_two_components {K Q J₁ J₂ : Subgroup G}
    (hne : J₁ ≠ J₂)
    (honly : ∀ Y : Subgroup G, IsPComponentIn 3 Y K → Y = J₁ ∨ Y = J₂)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hQ3 : IsPGroup 3 Q) :
    ∀ J' : Subgroup G, IsPComponentIn 3 J' K →
      Nat.card (MulAction.orbit ↥Q J') = 1 := by
  classical
  have horbit : ∀ J' : Subgroup G, IsPComponentIn 3 J' K →
      MulAction.orbit ↥Q J' ⊆ ({J₁, J₂} : Set (Subgroup G)) := by
    intro J' hJ' Y hY
    obtain ⟨q, rfl⟩ := MulAction.mem_orbit_iff.mp hY
    have hq : (q : G) ∈ Subgroup.normalizer (K : Set G) := hQK q.2
    have hmap : (q : ↥Q) • J' = J'.map (↑(MulAut.conj (q : G))) := rfl
    have hcomp : IsPComponentIn 3 ((q : ↥Q) • J') K := by
      rw [hmap]
      exact isPComponentIn_conj_of_mem_normalizer hJ' hq
    rcases honly _ hcomp with hYeq | hYeq <;> simp [hYeq]
  intro J' hJ'
  have hle2 : Nat.card (MulAction.orbit ↥Q J') ≤ 2 := by
    have h := Set.ncard_le_ncard (horbit J' hJ') (Set.toFinite _)
    rwa [Set.ncard_pair hne] at h
  have hdvd : Nat.card (MulAction.orbit ↥Q J') ∣ Nat.card ↥Q := by
    haveI : Fintype ↥Q := Fintype.ofFinite _
    haveI : Fintype ↥(MulAction.orbit ↥Q J') := Fintype.ofFinite _
    haveI : Fintype ↥(MulAction.stabilizer ↥Q J') := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥Q J'
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card] at h
    exact ⟨_, h.symm⟩
  obtain ⟨n, hn⟩ := hQ3.exists_card_eq
  have hdvd3 : Nat.card (MulAction.orbit ↥Q J') ∣ 3 ^ n := by
    simpa [hn] using hdvd
  haveI : Nonempty ↥(MulAction.orbit ↥Q J') :=
    ⟨⟨J', by simpa using MulAction.mem_orbit J' (1 : ↥Q)⟩⟩
  have hpos : 0 < Nat.card (MulAction.orbit ↥Q J') := Nat.card_pos
  have hnot2 : ¬ 2 ∣ Nat.card (MulAction.orbit ↥Q J') := by
    intro h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h2.trans hdvd3))
      (by norm_num)
  have h12 : Nat.card (MulAction.orbit ↥Q J') = 1 ∨
      Nat.card (MulAction.orbit ↥Q J') = 2 := by omega
  rcases h12 with h | h
  · exact h
  · exfalso
    exact hnot2 (h ▸ dvd_rfl)

theorem le_normalizer_of_orbit_card_one {Q J : Subgroup G}
    (hcard : Nat.card (MulAction.orbit ↥Q J) = 1) :
    Q ≤ Subgroup.normalizer (J : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcard' : Nat.card (MulAction.orbit ↥Q J) = 1 := hcard
  obtain ⟨Y, hY⟩ := Set.ncard_eq_one.mp (by simpa using hcard')
  have hJmem : J ∈ MulAction.orbit ↥Q J := by
    simpa using MulAction.mem_orbit J (1 : ↥Q)
  have hqmem : (⟨q, hq⟩ : ↥Q) • J ∈ MulAction.orbit ↥Q J :=
    MulAction.mem_orbit J (⟨q, hq⟩ : ↥Q)
  rw [hY, Set.mem_singleton_iff] at hJmem hqmem
  have h := hqmem.trans hJmem.symm
  have hmap : (⟨q, hq⟩ : ↥Q) • J = J.map (↑(MulAut.conj q)) := rfl
  rwa [hmap] at h

theorem S14Choice.Q_le_normalizer_of_isKComp {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    {J' : Subgroup G} (hJ' : IsKComp M H J') :
    Q ≤ Subgroup.normalizer (J' : Set G) := by
  have hfive := (hpre 3 Q (h.Q_mem_QSet hU) H h.mem_H2StarFam).2
  have hQK := h.Q_le_normalizer_kSub hU
  rcases hfive with ⟨hK, -⟩ | ⟨J₁, J₂, hne, hJ₁, hJ₂, hsup, honly, hSL₁, hSL₂⟩
  · have hJeq : J' = kSub 3 M H := IsKComp.eq_kSub_of_isKComp_self hK hJ'
    rw [hJeq]
    exact hQK
  · have hcard := orbit_card_one_of_two_components hne honly hQK h.sylow.isPGroup
    rcases honly J' hJ' with hJ | hJ
    · rw [hJ]
      exact le_normalizer_of_orbit_card_one (hcard J₁ hJ₁)
    · rw [hJ]
      exact le_normalizer_of_orbit_card_one (hcard J₂ hJ₂)

theorem S14Choice.Q_le_normalizer_J {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M) :
    Q ≤ Subgroup.normalizer (J : Set G) :=
  h.Q_le_normalizer_of_isKComp hpre hU h.isKComp

theorem S14Choice.isSylowOf_inf_of_isKComp {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    {J' : Subgroup G} (hJ' : IsKComp M H J') :
    CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J') J' :=
  CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer h.sylow
    (hJ'.1.trans le_sup_left)
    (sup_le (h.kSub_le_normalizer_of_isKComp hpre hU hJ')
      (h.E_le_Q.trans (h.Q_le_normalizer_of_isKComp hpre hU hJ')))

theorem S14Choice.isSylowOf_inf_J {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J) J :=
  h.isSylowOf_inf_of_isKComp hpre hU h.isKComp

theorem S14Choice.card_inf_J
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hA : TypeA M H) :
    Nat.card ↥(Q ⊓ J) = 27 := by
  have hSL := h.isSL34Star_of_typeA hpre hU hA
  have hcardJ : Nat.card ↥J =
      Nat.card (threeStar J) * Nat.card (CFSG.pPrimeCore 3 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 3 ↥J)
  have hdvd3 : 3 ^ 3 ∣ Nat.card ↥J := by
    rw [hcardJ, IsSL34Star.card_threeStar hSL]
    exact dvd_mul_of_dvd_left (by norm_num) _
  have hndvd4 : ¬ 3 ^ 4 ∣ Nat.card ↥J := by
    rw [hcardJ, IsSL34Star.card_threeStar hSL]
    intro h
    have hcop : Nat.Coprime (3 ^ 4) (Nat.card (CFSG.pPrimeCore 3 ↥J)) :=
      CFSG.pPrimeCore_coprime_card.pow_left 4
    have h60480 : 3 ^ 4 ∣ 60480 := hcop.dvd_of_dvd_mul_right h
    norm_num at h60480
  have hfac : (Nat.card ↥J).factorization 3 = 3 := by
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos.ne')).mp hdvd3
    have h4 : ¬ 4 ≤ (Nat.card ↥J).factorization 3 := by
      intro hle
      exact hndvd4 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (Nat.card_pos.ne')).mpr hle)
    omega
  rw [CFSG.ABGLocalTools.IsSylowOf.card_eq (h.isSylowOf_inf_J hpre hU), hfac]
  norm_num

private theorem center_le_image_inf_of_card
    {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hA : TypeA M H) :
    Subgroup.center (threeStar J) ≤
      ((Q ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)) := by
  classical
  have hSL := h.isSL34Star_of_typeA hpre hU hA
  let π : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  let P : Subgroup (threeStar J) := ((Q ⊓ J).subgroupOf J).map π
  have hPcard : Nat.card ↥P = 27 := by
    change Nat.card ↥(threeStarImg J (Q ⊓ J)) = 27
    rw [card_threeStarImg_of_isPGroup (h.sylow.isPGroup.to_le inf_le_left) inf_le_right,
      h.card_inf_J hpre hU hA]
  have hZcard : Nat.card ↥(Subgroup.center (threeStar J)) = 3 := hSL.2
  by_contra hnotle
  have hdisj : Disjoint P (Subgroup.center (threeStar J)) := by
    rw [disjoint_iff]
    by_contra hne
    apply hnotle
    have hdvd : Nat.card ↥(P ⊓ Subgroup.center (threeStar J)) ∣ 3 := by
      simpa [hZcard] using Subgroup.card_dvd_of_le
        (inf_le_right : P ⊓ Subgroup.center (threeStar J) ≤
          Subgroup.center (threeStar J))
    have hne1 : Nat.card ↥(P ⊓ Subgroup.center (threeStar J)) ≠ 1 := by
      intro h1
      exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hne1
    · intro z hz
      have hEq : P ⊓ Subgroup.center (threeStar J) = Subgroup.center (threeStar J) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZcard])
      have : z ∈ P ⊓ Subgroup.center (threeStar J) := by rw [hEq]; exact hz
      exact this.1
  have hnorm : Subgroup.center (threeStar J) ≤
      Subgroup.normalizer (P : Set (threeStar J)) :=
    (Subgroup.center_le_centralizer (P : Set (threeStar J))).trans
      (Subgroup.centralizer_le_normalizer (P : Set (threeStar J)))
  have h81 : Nat.card ↥(P ⊔ Subgroup.center (threeStar J)) = 81 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P
      (Subgroup.center (threeStar J)) hnorm hdisj, hPcard, hZcard]
  have hdvd : Nat.card ↥(P ⊔ Subgroup.center (threeStar J)) ∣
      Nat.card (threeStar J) := by
    simpa using Subgroup.card_dvd_of_le
      (H := P ⊔ Subgroup.center (threeStar J)) (K := ⊤) le_top
  rw [h81, IsSL34Star.card_threeStar hSL] at hdvd
  norm_num at hdvd

theorem S14Choice.oTwoZStar_le_M
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hA : TypeA M H) :
    oTwoZStar J ≤ M := by
  classical
  have hSL := h.isSL34Star_of_typeA hpre hU hA
  let OJ : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  let π : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  have hnotdvd : ¬ 3 ∣ Nat.card ↥OJ := by
    rw [show Nat.card ↥OJ = Nat.card (CFSG.pPrimeCore 3 ↥J) from
      Subgroup.card_map_of_injective J.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      CFSG.pPrimeCore_coprime_card
  have hQO : Q ≤ Subgroup.normalizer (OJ : Set G) := by
    intro q hq
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := J) (h.Q_le_normalizer_J hpre hU hq)
  have hO : OJ ≤ M := h.hypCGen.invariant_coprime_le_M hnotdvd (h.E_le_Q.trans hQO)
  have hπker : π.ker = CFSG.pPrimeCore 3 ↥J :=
    QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 ↥J)
  have hZleP := center_le_image_inf_of_card h hpre hU hA
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyZ : π y ∈ Subgroup.center (threeStar J) := Subgroup.mem_comap.mp hy
  obtain ⟨z, hzP, hzy⟩ := Subgroup.mem_map.mp (hZleP hyZ)
  have hzQJ : (z : G) ∈ Q ⊓ J := Subgroup.mem_subgroupOf.mp hzP
  have hker : π (y * z⁻¹) = 1 := by
    rw [map_mul, map_inv, hzy, mul_inv_cancel]
  have hmemO : (y * z⁻¹ : ↥J) ∈ CFSG.pPrimeCore 3 ↥J := by
    rw [← hπker]
    exact MonoidHom.mem_ker.mpr hker
  have hmemO' : x * (z : G)⁻¹ ∈ OJ := by
    have hcoe : ((y * z⁻¹ : ↥J) : G) = x * (z : G)⁻¹ := by
      have hyx' : (y : G) = x := hyx
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hyx']
    rw [← hcoe]
    exact Subgroup.mem_map_of_mem J.subtype hmemO
  have hxO : x * (z : G)⁻¹ ∈ M := hO hmemO'
  have hzM : (z : G) ∈ M := h.Q_le_M hU hzQJ.1
  have := M.mul_mem hxO hzM
  simpa [mul_assoc] using this

theorem exists_caseOneCtx {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : TypeA M H) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M) : ∃ R T : Subgroup G, CaseOneCtx G M H E Q J R T := by
  have hS₀H : CFSG.Open.pCoreOf 2 H ≤ H :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hS₀ : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hQN : Q ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    (h.sylow.le.trans (sup_le (kSub_le 3 M H) h.E_le_H)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  obtain ⟨R, hS₀R, hRmax⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.exists_isMaxInvariantTwoIn_ge
      (B := Q) (S₀ := CFSG.Open.pCoreOf 2 H) (Y := H) hS₀H hS₀ hQN
  have hR2 : IsPGroup 2 R := hRmax.2.1
  have hRM : R ≤ M := h.hypCGen.invariant_coprime_le_M
    (CFSG.GroupTheory.not_dvd_card_of_isPGroup hR2 Nat.prime_three (by norm_num))
    (h.E_le_Q.trans hRmax.2.2.1)
  obtain ⟨T, hTsylow, hRT⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge
    (p := 2) (K := H ⊓ M) (Q := R) (le_inf hRmax.1 hRM) hR2
  exact ⟨R, T, CaseOneCtx.mk h hA hpre hU hL hRmax hS₀R hTsylow hRT⟩

theorem CaseOneCtx.R_le_M {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T) :
    R ≤ M :=
  c.choice.hypCGen.invariant_coprime_le_M
    (CFSG.GroupTheory.not_dvd_card_of_isPGroup c.R_max.2.1 Nat.prime_three (by norm_num))
    (c.choice.E_le_Q.trans c.R_max.2.2.1)

theorem commutator_le_pPrimeCore_of_distinct {K J J' : Subgroup G}
    (hJ : IsPComponentIn 3 J K) (hJ' : IsPComponentIn 3 J' K) (hne : J' ≠ J) :
    ⁅J', J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hneK : J'.subgroupOf K ≠ J.subgroupOf K := by
    intro heq
    apply hne
    have h := congrArg (Subgroup.map K.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ'.1,
      Subgroup.map_subgroupOf_eq_of_le hJ.1] at h
  have hcore :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.mutual_normalization_core_commutation
      3 (J'.subgroupOf K) (J.subgroupOf K) hJ'.2 hJ.2 hneK).2.2
  have hcoreJ : ⁅J'.subgroupOf K, J.subgroupOf K⁆ ≤
      (CFSG.pPrimeCore 3 ↥(J.subgroupOf K)).map (J.subgroupOf K).subtype :=
    hcore.trans inf_le_right
  have hleK : ⁅J', J⁆ ≤ K :=
    (Subgroup.commutator_mono hJ'.1 hJ.1).trans (Subgroup.commutator_le_self K)
  have hmap := Subgroup.map_mono (f := K.subtype) hcoreJ
  rw [CFSG.GroupTheory.commutator_subgroupOf_eq hJ'.1 hJ.1,
    Subgroup.map_subgroupOf_eq_of_le hleK] at hmap
  have hcomp : J.subtype.comp (Subgroup.subgroupOfEquivOfLe hJ.1).toMonoidHom =
      K.subtype.comp (J.subgroupOf K).subtype := by
    ext x
    rfl
  have hmapcore : ((CFSG.pPrimeCore 3 ↥(J.subgroupOf K)).map
      (J.subgroupOf K).subtype).map K.subtype = (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
    calc ((CFSG.pPrimeCore 3 ↥(J.subgroupOf K)).map (J.subgroupOf K).subtype).map K.subtype
        = (CFSG.pPrimeCore 3 ↥(J.subgroupOf K)).map
            (K.subtype.comp (J.subgroupOf K).subtype) := by rw [Subgroup.map_map]
      _ = (CFSG.pPrimeCore 3 ↥(J.subgroupOf K)).map
            (J.subtype.comp (Subgroup.subgroupOfEquivOfLe hJ.1).toMonoidHom) := by
            rw [hcomp]
      _ = ((CFSG.pPrimeCore 3 ↥(J.subgroupOf K)).map
            (Subgroup.subgroupOfEquivOfLe hJ.1).toMonoidHom).map J.subtype := by
            rw [Subgroup.map_map]
      _ = (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
            rw [CFSG.pPrimeCore_map_iso 3 (Subgroup.subgroupOfEquivOfLe hJ.1)]
  rwa [hmapcore] at hmap

private theorem card_image_inf_eq_27
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hA : TypeA M H) :
    Nat.card ↥(((Q ⊓ J).subgroupOf J).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))) = 27 := by
  change Nat.card ↥(threeStarImg J (Q ⊓ J)) = 27
  rw [card_threeStarImg_of_isPGroup (h.sylow.isPGroup.to_le inf_le_left) inf_le_right,
    h.card_inf_J hpre hU hA]

private theorem inf_centralizer_le_normalizer_J
    {M H E Q J R : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hA : TypeA M H) (hRnormK : R ≤ Subgroup.normalizer (kSub 3 M H : Set G)) :
    R ⊓ Subgroup.centralizer (Q ⊓ J : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  classical
  have hSL := h.isSL34Star_of_typeA hpre hU hA
  let π : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  intro r hr
  have hrN : r ∈ Subgroup.normalizer (kSub 3 M H : Set G) := hRnormK hr.1
  have hJ' : IsPComponentIn 3 (J.map (MulAut.conj r).toMonoidHom) (kSub 3 M H) :=
    isPComponentIn_conj_of_mem_normalizer h.isKComp hrN
  by_cases hEq : J.map (MulAut.conj r).toMonoidHom = J
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hEq
  · exfalso
    have hQJle : Q ⊓ J ≤ J.map (MulAut.conj r).toMonoidHom := by
      intro q hq
      have hqr : q * r = r * q := Subgroup.mem_centralizer_iff.mp hr.2 q hq
      have hconj : r * q * r⁻¹ = q := by
        rw [← hqr]
        group
      rw [← hconj]
      exact Subgroup.mem_map_of_mem (MulAut.conj r).toMonoidHom (Subgroup.mem_inf.mp hq).2
    have hcomm_le : ⁅J.map (MulAut.conj r).toMonoidHom, J⁆ ≤
        (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
      commutator_le_pPrimeCore_of_distinct h.isKComp hJ' hEq
    have hmemO : ∀ x ∈ Q ⊓ J, ∀ y ∈ J, ⁅x, y⁆ ∈ (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
      fun x hx y hy => hcomm_le (Subgroup.commutator_mem_commutator (hQJle hx) hy)
    have hPleCenter : ((Q ⊓ J).subgroupOf J).map π ≤
        Subgroup.center (threeStar J) := by
      rintro p hp
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hp
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) w
      have hxQJ : (x : G) ∈ Q ⊓ J := Subgroup.mem_subgroupOf.mp hx
      obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp (hmemO (x : G) hxQJ (y : G) y.2)
      have hc_eq : (⁅x, y⁆ : ↥J) = c := by
        apply Subtype.ext
        simpa [commutatorElement_def] using hce.symm
      have hquot : π ⁅x, y⁆ = 1 := by
        have hmem : (⁅x, y⁆ : ↥J) ∈ π.ker := by
          rw [show π.ker = CFSG.pPrimeCore 3 ↥J from
            QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 ↥J)]
          exact hc_eq ▸ hc
        exact (MonoidHom.mem_ker).mp hmem
      rw [map_commutatorElement] at hquot
      exact (commutatorElement_eq_one_iff_mul_comm.mp hquot).symm
    have hdvd : Nat.card ↥(((Q ⊓ J).subgroupOf J).map π) ∣
        Nat.card ↥(Subgroup.center (threeStar J)) :=
      Subgroup.card_dvd_of_le hPleCenter
    rw [show Nat.card ↥(((Q ⊓ J).subgroupOf J).map π) = 27 from
      card_image_inf_eq_27 h hpre hU hA, hSL.2] at hdvd
    norm_num at hdvd

theorem CaseOneCtx.R_le_normalizer_J
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) : R ≤ Subgroup.normalizer (J : Set G) := by
  have hR2 : IsPGroup 2 R := c.R_max.2.1
  have hRnormK : R ≤ Subgroup.normalizer (kSub 3 M H : Set G) :=
    (le_inf c.R_max.1 c.R_le_M).trans (inf_le_normalizer_kSub 3 M H)
  have hAR : Q ⊓ J ≤ Subgroup.normalizer (R : Set G) :=
    inf_le_left.trans c.R_max.2.2.1
  have hcop : Nat.Coprime (Nat.card ↥(Q ⊓ J)) (Nat.card ↥R) := by
    rw [c.choice.card_inf_J c.pre c.nine c.typeA]
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    rw [hn]
    exact (by norm_num : Nat.Coprime 27 2).pow_right n
  have hsolv : Group.IsSolvable ↥R := by
    haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hmain := CFSG.AGLEmbedding.le_commutator_sup_inf_centralizer_of_coprime
    (R := R) (A := Q ⊓ J) hAR hcop hsolv
  refine hmain.trans (sup_le ?hcomm ?hcent)
  · have hcommK : ⁅R, Q ⊓ J⁆ ≤ kSub 3 M H := by
      rw [Subgroup.commutator_le]
      intro r hr q hq
      have hqJ : q ∈ J := (Subgroup.mem_inf.mp hq).2
      have hqK : q ∈ kSub 3 M H := c.choice.isKComp.1 hqJ
      have hrq : r * q * r⁻¹ ∈ kSub 3 M H :=
        (Subgroup.mem_normalizer_iff.mp (hRnormK hr) q).mp hqK
      have hqinv : q⁻¹ ∈ kSub 3 M H := (kSub 3 M H).inv_mem hqK
      have h := (kSub 3 M H).mul_mem hrq hqinv
      simpa [commutatorElement_def] using h
    exact hcommK.trans (c.choice.kSub_le_normalizer_J c.pre c.nine)
  · exact inf_centralizer_le_normalizer_J c.choice c.pre c.nine c.typeA hRnormK

private theorem commutator_subgroup_normal_in_Q {Q J : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer ((Q ⊓ J : Subgroup G) : Set G))
    (hQJ : ¬ IsMulCommutative ↥(Q ⊓ J)) :
    let C := ⁅Q ⊓ J, Q ⊓ J⁆
    C ≤ Q ∧ Q ≤ Subgroup.normalizer (C : Set G) ∧ (C.subgroupOf Q).Normal ∧ C ≠ ⊥ := by
  classical
  let C : Subgroup G := ⁅Q ⊓ J, Q ⊓ J⁆
  have hCQ : C ≤ Q :=
    (Subgroup.commutator_mono inf_le_left inf_le_left).trans (Subgroup.commutator_le_self Q)
  have hQC : Q ≤ Subgroup.normalizer (C : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmapQJ : ((Q ⊓ J : Subgroup G)).map (MulAut.conj q).toMonoidHom = Q ⊓ J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQN hq)
    change C.map (MulAut.conj q).toMonoidHom = C
    rw [show C = ⁅Q ⊓ J, Q ⊓ J⁆ from rfl, Subgroup.map_commutator, hmapQJ]
  haveI : (C.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCQ).mpr hQC
  have hCne : C ≠ ⊥ := by
    intro hCbot
    apply hQJ
    have hle : Q ⊓ J ≤ Subgroup.centralizer (Q ⊓ J : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCbot
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hb := Subgroup.mem_centralizer_iff.mp (hle a.2) b b.2
    exact hb.symm
  exact ⟨hCQ, hQC, inferInstance, hCne⟩

private theorem center_map_le_of_normal_nontrivial {Q C : Subgroup G}
    (hQ3 : IsPGroup 3 Q) (hCQ : C ≤ Q) (hQC : Q ≤ Subgroup.normalizer (C : Set G))
    (hCne : C ≠ ⊥)
    (hAcard : Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) = 3) :
    (Subgroup.center ↥Q).map Q.subtype ≤ C := by
  classical
  haveI : (C.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCQ).mpr hQC
  have hneSub : C.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hCne
    have h := (Subgroup.subgroupOf_eq_bot.mp hbot)
    rw [disjoint_iff, inf_eq_left.mpr hCQ] at h
    exact h
  haveI : Group.IsNilpotent ↥Q := hQ3.isNilpotent
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥Q)
    (H := C.subgroupOf Q) hneSub
  obtain ⟨⟨z, hz⟩, hz_ne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hmeet
  let A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  have hzC : (z : G) ∈ C := by
    have hzsub : z ∈ C.subgroupOf Q := (Subgroup.mem_inf.mp hz).1
    exact Subgroup.mem_subgroupOf.mp hzsub
  have hzA : (z : G) ∈ A :=
    Subgroup.mem_map_of_mem Q.subtype ((Subgroup.mem_inf.mp hz).2)
  have hzne : (z : G) ≠ 1 := by
    intro h1
    apply hz_ne1
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  have hCAne : C ⊓ A ≠ ⊥ := by
    intro hbot
    have hmem : (z : G) ∈ C ⊓ A := ⟨hzC, hzA⟩
    rw [hbot] at hmem
    exact hzne (Subgroup.mem_bot.mp hmem)
  have hCAcard : Nat.card ↥(C ⊓ A) = 3 := by
    have hdvd : Nat.card ↥(C ⊓ A) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : C ⊓ A ≤ A)
      rwa [show Nat.card ↥A = 3 from hAcard] at h
    have hne1 : Nat.card ↥(C ⊓ A) ≠ 1 := by
      intro h1
      exact hCAne (Subgroup.eq_bot_of_card_eq _ h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  have hEq : C ⊓ A = A :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hCAcard, hAcard])
  intro a ha
  have : a ∈ C ⊓ A := by rw [hEq]; exact ha
  exact this.1

private theorem center_le_commutator_of_not_commutative {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hA : TypeA M H) (h142 : FourteenTwoCaseOneAt M) (hQJ : ¬ IsMulCommutative ↥(Q ⊓ J)) :
    (Subgroup.center ↥Q).map Q.subtype ≤ ⁅Q ⊓ J, Q ⊓ J⁆ := by
  classical
  have h142' := h142 H E Q J h hA
  have hAcard : Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) = 3 := h142'.1.2.2.2
  have hQNQJ : Q ≤ Subgroup.normalizer ((Q ⊓ J : Subgroup G) : Set G) := by
    intro q hq
    show q ∈ Subgroup.normalizer ((Q ⊓ J : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hQmap : Q.map (↑(MulAut.conj q)) = Q := by
      simpa only [MulEquiv.toMonoidHom_eq_coe] using
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hq)
    have hJmap : J.map (↑(MulAut.conj q)) = J := by
      simpa only [MulEquiv.toMonoidHom_eq_coe] using
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.Q_le_normalizer_J hpre hU hq)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj q).injective, hQmap, hJmap]
  obtain ⟨hCQ, hQC, -, hCne⟩ := commutator_subgroup_normal_in_Q hQNQJ hQJ
  exact center_map_le_of_normal_nontrivial h.sylow.isPGroup hCQ hQC hCne hAcard

private theorem oTwo_le_oThree {J : Subgroup G} :
    CFSG.Open.pCoreOf 2 J ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
  rw [CFSG.openPCoreOf_eq_map_pCore]
  exact Subgroup.map_mono (CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num))

private theorem card_le_three_of_le_center_image {J N : Subgroup G} (hNJ : N ≤ J)
    (hN3 : IsPGroup 3 N) (hcomm : ⁅N, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype)
    (hZcard : Nat.card ↥(Subgroup.center (threeStar J)) = 3) : Nat.card ↥N ≤ 3 := by
  classical
  let π : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  have hπker : π.ker = CFSG.pPrimeCore 3 ↥J :=
    QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 ↥J)
  have hPcard : Nat.card ↥((N.subgroupOf J).map π) = Nat.card ↥N := by
    change Nat.card ↥(threeStarImg J N) = Nat.card ↥N
    exact card_threeStarImg_of_isPGroup hN3 hNJ
  have hPle : (N.subgroupOf J).map π ≤ Subgroup.center (threeStar J) := by
    rintro p ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) w
    have hxN : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp
      (hcomm (Subgroup.commutator_mem_commutator hxN y.2))
    have hc_eq : (⁅x, y⁆ : ↥J) = c := by
      apply Subtype.ext
      simpa [commutatorElement_def] using hce.symm
    have hquot : π ⁅x, y⁆ = 1 := by
      have hmem : (⁅x, y⁆ : ↥J) ∈ π.ker := by
        rw [hπker]
        exact hc_eq ▸ hc
      exact (MonoidHom.mem_ker).mp hmem
    rw [map_commutatorElement] at hquot
    exact (commutatorElement_eq_one_iff_mul_comm.mp hquot).symm
  have hdvd := Subgroup.card_dvd_of_le hPle
  rw [hPcard, hZcard] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

private theorem exists_Q0_f_of_h142
    {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hA : TypeA M H) (h142 : FourteenTwoCaseOneAt M) :
    ∃ (Q₀ : Subgroup G) (f : G), Q₀ ≤ Q ∧ Nat.card Q₀ = 27 ∧
      ⁅Q₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J ∧ (Subgroup.center ↥Q).map Q.subtype ≤ Q₀ ∧
      f ∈ Q₀ ∧ f ∉ J ∧ f ∈ Q ∧ f ^ 3 = 1 ∧ orderOf f = 3 := by
  classical
  have hSL := h.isSL34Star_of_typeA hpre hU hA
  have h142' := h142 H E Q J h hA
  obtain ⟨Q₀, hQ₀Q, hQ₀card, hQ₀J, hAQ₀⟩ := h142'.2
  have hQ3 : IsPGroup 3 Q := h.sylow.isPGroup
  have hQ03 : IsPGroup 3 ↥(Q₀ ⊓ J) :=
    IsPGroup.to_le (H := Q₀ ⊓ J) hQ3 (by
      intro x hx
      exact hQ₀Q (Subgroup.mem_inf.mp hx).1)
  have hcomm0 : ⁅Q₀ ⊓ J, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
    ((Subgroup.commutator_mono inf_le_left le_rfl).trans hQ₀J).trans oTwo_le_oThree
  have hbound : Nat.card ↥(Q₀ ⊓ J) ≤ 3 :=
    card_le_three_of_le_center_image inf_le_right hQ03 hcomm0 hSL.2
  have hQ₀notle : ¬ Q₀ ≤ J := by
    intro hle
    have hEq : Q₀ ⊓ J = Q₀ := inf_eq_left.mpr hle
    have hle3 : Nat.card ↥Q₀ ≤ 3 := hEq ▸ hbound
    rw [hQ₀card] at hle3
    norm_num at hle3
  obtain ⟨f, hfQ₀, hfJ⟩ := Set.not_subset.mp hQ₀notle
  have hfQ : f ∈ Q := hQ₀Q hfQ₀
  have hf1 : f ≠ 1 := fun h1 => hfJ (h1 ▸ J.one_mem)
  have hf3 : f ^ 3 = 1 := h142'.1.2.1 f hfQ
  have hford : orderOf f = 3 := by
    have hdvd : orderOf f ∣ 3 := orderOf_dvd_of_pow_eq_one hf3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hf1
    · exact h3
  exact ⟨Q₀, f, hQ₀Q, hQ₀card, hQ₀J, hAQ₀, hfQ₀, hfJ, hfQ, hf3, hford⟩

private theorem exists_E81_of_abelian_inf_J {Q J Q₀ M : Subgroup G} {f : G}
    (hQM : Q ≤ M) (hQ3 : IsPGroup 3 Q) (hQ₀Q : Q₀ ≤ Q)
    (hQ₀J : ⁅Q₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hfQ₀ : f ∈ Q₀) (hfJ : f ∉ J) (hfQ : f ∈ Q) (hf3 : f ^ 3 = 1)
    (hford : orderOf f = 3) (hEcard : Nat.card ↥(Q ⊓ J) = 27)
    (hexp : ∀ x ∈ Q, x ^ 3 = 1) (habel : IsMulCommutative ↥(Q ⊓ J)) :
    ∃ Ω : Subgroup G, Ω ≤ M ∧ IsElemAbelian 3 Ω ∧ Nat.card Ω = 81 := by
  classical
  have hEea : IsElemAbelian 3 (Q ⊓ J) := by
    refine ⟨habel, fun x hx => hexp x ?_⟩
    exact (Subgroup.mem_inf.mp hx).1
  have hEea : IsElemAbelian 3 (Q ⊓ J) := by
    refine ⟨habel, fun x hx => hexp x ?_⟩
    exact (Subgroup.mem_inf.mp hx).1
  have hO2not : ¬ 3 ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 J) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J)
      Nat.prime_three (by norm_num)
  have hO2Q : CFSG.Open.pCoreOf 2 J ⊓ Q = ⊥ := by
    rw [inf_comm]
    exact CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hO2not hQ3
  have hcentral : Q₀ ≤ Subgroup.centralizer ((Q ⊓ J : Subgroup G) : Set G) := by
    have hcommE : ⁅Q₀, Q ⊓ J⁆ ≤ CFSG.Open.pCoreOf 2 J ⊓ Q := by
      refine le_inf ?_ ?_
      · exact (Subgroup.commutator_mono (le_refl Q₀) inf_le_right).trans hQ₀J
      · exact (Subgroup.commutator_mono hQ₀Q inf_le_left).trans (Subgroup.commutator_le_self Q)
    have hbot : ⁅Q₀, Q ⊓ J⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact hcommE.trans (le_of_eq hO2Q)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hfC : f ∈ Subgroup.centralizer ((Q ⊓ J : Subgroup G) : Set G) := hcentral hfQ₀
  have hcommE : ∀ a ∈ Q ⊓ J, a * f = f * a := by
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp hfC a ha
  have hcommE' : ∀ a ∈ Q ⊓ J, ∀ b ∈ Subgroup.zpowers f, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hcommE a ha) n).eq
  have hOmegaEa : IsElemAbelian 3 ((Q ⊓ J) ⊔ Subgroup.zpowers f) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEea
      (CFSG.Open.isElemAbelian_zpowers hf3) hcommE'
  have hzfcard : Nat.card ↥(Subgroup.zpowers f) = 3 := by
    rw [Nat.card_zpowers, hford]
  have hfN : f ∈ Subgroup.normalizer ((Q ⊓ J : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hfC
  have hdisj : Disjoint (Q ⊓ J) (Subgroup.zpowers f) := by
    have hnotle : ¬ Subgroup.zpowers f ≤ Q ⊓ J := by
      intro hle
      exact hfJ (Subgroup.mem_inf.mp (hle (Subgroup.mem_zpowers f))).2
    have hdvd : Nat.card ↥((Q ⊓ J) ⊓ Subgroup.zpowers f) ∣ 3 := by
      simpa [hzfcard] using Subgroup.card_dvd_of_le
        (inf_le_right : (Q ⊓ J) ⊓ Subgroup.zpowers f ≤ Subgroup.zpowers f)
    have hne : Nat.card ↥((Q ⊓ J) ⊓ Subgroup.zpowers f) ≠ 3 := by
      intro h3
      apply hnotle
      have hEq : (Q ⊓ J) ⊓ Subgroup.zpowers f = Subgroup.zpowers f :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hzfcard])
      intro x hx
      have : x ∈ (Q ⊓ J) ⊓ Subgroup.zpowers f := by rw [hEq]; exact hx
      exact this.1
    have hcard1 : Nat.card ↥((Q ⊓ J) ⊓ Subgroup.zpowers f) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact h1
      · exact absurd h3 hne
    exact disjoint_iff.mpr (Subgroup.eq_bot_of_card_eq _ hcard1)
  have hOmegaCard : Nat.card ↥((Q ⊓ J) ⊔ Subgroup.zpowers f) = 81 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Q ⊓ J) (Subgroup.zpowers f) (Subgroup.zpowers_le.mpr hfN) hdisj,
      hEcard, hzfcard]
  have hOmegaM : (Q ⊓ J) ⊔ Subgroup.zpowers f ≤ M :=
    sup_le (inf_le_left.trans (hQM)) (Subgroup.zpowers_le.mpr (hQM hfQ))
  exact ⟨(Q ⊓ J) ⊔ Subgroup.zpowers f, hOmegaM, hOmegaEa, hOmegaCard⟩

private theorem not_isMulCommutative_inf_J
    {M H E Q J : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hA : TypeA M H) (h142 : FourteenTwoCaseOneAt M) :
    ¬ IsMulCommutative ↥(Q ⊓ J) := by
  classical
  obtain ⟨Q₀, f, hQ₀Q, hQ₀card, hQ₀J, hAQ₀, hfQ₀, hfJ, hfQ, hf3, hford⟩ :=
    exists_Q0_f_of_h142 h hpre hU hA h142
  have h142' := h142 H E Q J h hA
  have hEcard : Nat.card ↥(Q ⊓ J) = 27 := h.card_inf_J hpre hU hA
  intro habel
  obtain ⟨Ω, hΩM, hΩea, hΩcard⟩ :=
    exists_E81_of_abelian_inf_J (h.Q_le_M hU) h.sylow.isPGroup hQ₀Q hQ₀J hfQ₀ hfJ
      hfQ hf3 hford
      hEcard h142'.1.2.1 habel
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 M :=
    CFSG.SectionRank.le_pRank (by norm_num) hΩM hΩea (by
      rw [hΩcard]
      norm_num)
  have hrank3 : CFSG.Open.pRank 3 M ≤ 3 :=
    h.cstar.pRank_le_three_of_not_mem_sigmaSet h.maxLocal Nat.prime_three (by norm_num)
      h.hypCGen.not_mem_sigmaSet
  omega

theorem CaseOneCtx.exists_Q₀
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M) :
    ∃ Q₀ : Subgroup G, Q₀ ≤ Q ∧ Nat.card Q₀ = 27 ∧ ⁅Q₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J ∧
      (Subgroup.center ↥Q).map Q.subtype ≤ Q₀ ∧
      Q₀ ≤ Subgroup.centralizer ((Q ⊓ J : Subgroup G) : Set G) ∧
      Q₀ ⊓ J = (Subgroup.center ↥Q).map Q.subtype ∧ ∃ f ∈ Q₀, f ∉ J := by
  classical
  have h142' := h142 H E Q J c.choice c.typeA
  obtain ⟨Q₀, hQ₀Q, hQ₀card, hQ₀J, hAQ₀⟩ := h142'.2
  let A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  have hAcard : Nat.card ↥A = 3 := h142'.1.2.2.2
  have hA_le_J : A ≤ J :=
    (center_le_commutator_of_not_commutative c.choice c.pre c.nine c.typeA h142
      (not_isMulCommutative_inf_J c.choice c.pre c.nine c.typeA h142)).trans
      ((Subgroup.commutator_le_self (Q ⊓ J)).trans inf_le_right)
  have hQ03 : IsPGroup 3 ↥(Q₀ ⊓ J) :=
    IsPGroup.to_le (H := Q₀ ⊓ J) c.choice.sylow.isPGroup (by
      intro x hx
      exact hQ₀Q (Subgroup.mem_inf.mp hx).1)
  have hcomm0 : ⁅Q₀ ⊓ J, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
    ((Subgroup.commutator_mono inf_le_left le_rfl).trans hQ₀J).trans oTwo_le_oThree
  have hbound : Nat.card ↥(Q₀ ⊓ J) ≤ 3 :=
    card_le_three_of_le_center_image inf_le_right hQ03 hcomm0
      (c.isSL34Star).2
  have hQ₀C : Q₀ ≤ Subgroup.centralizer ((Q ⊓ J : Subgroup G) : Set G) := by
    have hO2not : ¬ 3 ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 J) :=
      CFSG.GroupTheory.not_dvd_card_of_isPGroup
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J)
        Nat.prime_three (by norm_num)
    have hO2Q : CFSG.Open.pCoreOf 2 J ⊓ Q = ⊥ := by
      rw [inf_comm]
      exact CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hO2not
        c.choice.sylow.isPGroup
    have hcommE : ⁅Q₀, Q ⊓ J⁆ ≤ CFSG.Open.pCoreOf 2 J ⊓ Q := by
      refine le_inf ?_ ?_
      · exact (Subgroup.commutator_mono (le_refl Q₀) inf_le_right).trans hQ₀J
      · exact (Subgroup.commutator_mono hQ₀Q inf_le_left).trans (Subgroup.commutator_le_self Q)
    have hbot : ⁅Q₀, Q ⊓ J⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact hcommE.trans (le_of_eq hO2Q)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hA_le_Q0J : A ≤ Q₀ ⊓ J := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hAQ₀ hx, hA_le_J hx⟩
  have hcardQ0J : Nat.card ↥(Q₀ ⊓ J) = 3 := by
    have h3le : 3 ≤ Nat.card ↥(Q₀ ⊓ J) := by
      have hdvd : 3 ∣ Nat.card ↥(Q₀ ⊓ J) := by
        simpa [hAcard] using Subgroup.card_dvd_of_le hA_le_Q0J
      exact Nat.le_of_dvd Nat.card_pos hdvd
    omega
  have hQ0Jeq : Q₀ ⊓ J = A :=
    (Subgroup.eq_of_le_of_card_ge (H := A) (K := Q₀ ⊓ J) hA_le_Q0J
      (by rw [hcardQ0J, hAcard])).symm
  have hQ₀notle : ¬ Q₀ ≤ J := by
    intro hle
    have hEq : Q₀ ⊓ J = Q₀ := inf_eq_left.mpr hle
    have hle3 : Nat.card ↥Q₀ ≤ 3 := hEq ▸ hbound
    rw [hQ₀card] at hle3
    norm_num at hle3
  obtain ⟨f, hfQ₀, hfJ⟩ := Set.not_subset.mp hQ₀notle
  exact ⟨Q₀, hQ₀Q, hQ₀card, hQ₀J, hAQ₀, hQ₀C, hQ0Jeq, f, hfQ₀, hfJ⟩

theorem CaseOneCtx.center_le_commutator
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M) :
    (Subgroup.center ↥Q).map Q.subtype ≤ ⁅Q ⊓ J, Q ⊓ J⁆ :=
  center_le_commutator_of_not_commutative c.choice c.pre c.nine c.typeA h142
    (not_isMulCommutative_inf_J c.choice c.pre c.nine c.typeA h142)

private theorem zpowers_inf_eq_bot_of_not_mem {J : Subgroup G} {f : G} {p : ℕ}
    [Fact p.Prime] (hfJ : f ∉ J) (hford : orderOf f = p) :
    Subgroup.zpowers f ⊓ J = ⊥ := by
  have hdvd : Nat.card ↥(Subgroup.zpowers f ⊓ J) ∣ p := by
    rw [← hford, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(Subgroup.zpowers f ⊓ J) ≠ p := by
    intro h3
    have hle : Subgroup.zpowers f ≤ Subgroup.zpowers f ⊓ J := by
      refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers f ⊓ J)
        (K := Subgroup.zpowers f) inf_le_left ?_).ge
      rw [h3, Nat.card_zpowers, hford]
    exact hfJ (hle (Subgroup.mem_zpowers f)).2
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd h3 hne

private theorem elemAbelian_sup_zpowers_card {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : IsElemAbelian p A) {y : G} (hy : y ∉ A) (hyp : y ^ p = 1)
    (hyA : ∀ a ∈ A, a * y = y * a) :
    IsElemAbelian p (A ⊔ Subgroup.zpowers y) ∧
      Nat.card ↥(A ⊔ Subgroup.zpowers y) = Nat.card ↥A * p := by
  have hy1 : y ≠ 1 := fun h => hy (h ▸ A.one_mem)
  have hord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hyA a ha) k).eq
  have hdisj : Disjoint A (Subgroup.zpowers y) := by
    rw [disjoint_iff, inf_comm]
    exact zpowers_inf_eq_bot_of_not_mem hy hord
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
    have hyC : y ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hyA a ha
    exact Subgroup.centralizer_le_normalizer (A : Set G) hyC
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A
    (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyN) hdisj
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hA
    (CFSG.Open.isElemAbelian_zpowers hyp) hcomm, ?_⟩
  rw [hcard, Nat.card_zpowers, hord]

theorem CaseOneCtx.exists_E27
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M) :
    ∃ Ω : Subgroup G, Ω ≤ Q ∧ CFSG.Open.IsElemAbelian 3 Ω ∧ Nat.card Ω = 27 ∧
      (Subgroup.center ↥Q).map Q.subtype ≤ Ω := by
  classical
  obtain ⟨Q₀, hQ₀Q, -, hQ₀J, hAQ₀, hQ₀C, -, f, hfQ₀, hfJ⟩ := c.exists_Q₀ h142
  have h142' := h142 H E Q J c.choice c.typeA
  let A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  have hAcard : Nat.card ↥A = 3 := h142'.1.2.2.2
  have hA_le_Q : A ≤ Q := Subgroup.map_subtype_le _
  have hA_le_J : A ≤ J :=
    (center_le_commutator_of_not_commutative c.choice c.pre c.nine c.typeA h142
      (not_isMulCommutative_inf_J c.choice c.pre c.nine c.typeA h142)).trans
      ((Subgroup.commutator_le_self (Q ⊓ J)).trans inf_le_right)
  have hA_le_QJ : A ≤ Q ⊓ J := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hA_le_Q hx, hA_le_J hx⟩
  have hEcard : Nat.card ↥(Q ⊓ J) = 27 := c.choice.card_inf_J c.pre c.nine c.typeA
  have hQJneA : Q ⊓ J ≠ A := by
    intro hEq
    rw [hEq, hAcard] at hEcard
    norm_num at hEcard
  have hnotle : ¬ (Q ⊓ J : Subgroup G) ≤ A :=
    fun hle => hQJneA (le_antisymm hle hA_le_QJ)
  obtain ⟨y, hyQJ, hyA⟩ := Set.not_subset.mp hnotle
  have hyJ : y ∈ J := (Subgroup.mem_inf.mp hyQJ).2
  have hyQ : y ∈ Q := (Subgroup.mem_inf.mp hyQJ).1
  have hfQ : f ∈ Q := hQ₀Q hfQ₀
  have hf3 : f ^ 3 = 1 := h142'.1.2.1 f hfQ
  have hy3 : y ^ 3 = 1 := h142'.1.2.1 y hyQ
  have hcenterEa : IsElemAbelian 3 (Subgroup.center ↥Q) :=
    ⟨inferInstance, fun x hx => by
      have h := h142'.1.2.1 ((x : ↥Q) : G) (x : ↥Q).2
      apply Subtype.ext
      simpa using h⟩
  have hAea : IsElemAbelian 3 A := by
    simpa [A] using CFSG.SectionRank.isElemAbelian_map hcenterEa Q.subtype
  have hA_central : ∀ a ∈ A, ∀ z ∈ Q, a * z = z * a := by
    intro a ha z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have h := Subgroup.mem_center_iff.mp hx ⟨z, hz⟩
    exact (congrArg (fun t : ↥Q => (t : G)) h).symm
  have hf_not_A : f ∉ A := fun h => hfJ (hA_le_J h)
  have hf_comm_A : ∀ a ∈ A, a * f = f * a := fun a ha => hA_central a ha f hfQ
  obtain ⟨hAf_ea, hAf_card⟩ :=
    elemAbelian_sup_zpowers_card hAea hf_not_A hf3 hf_comm_A
  have hfy : f * y = y * f := by
    have h := Subgroup.mem_centralizer_iff.mp (hQ₀C hfQ₀) y hyQJ
    exact h.symm
  have hy_comm_A : ∀ a ∈ A, a * y = y * a := fun a ha => hA_central a ha y hyQ
  obtain ⟨-, hAy_card⟩ :=
    elemAbelian_sup_zpowers_card hAea hyA hy3 hy_comm_A
  have hy_not_Af : y ∉ A ⊔ Subgroup.zpowers f := by
    intro hy
    have hAy_le : A ⊔ Subgroup.zpowers y ≤ A ⊔ Subgroup.zpowers f := by
      refine sup_le le_sup_left ?_
      exact Subgroup.zpowers_le.mpr hy
    have hEq : A ⊔ Subgroup.zpowers y = A ⊔ Subgroup.zpowers f :=
      Subgroup.eq_of_le_of_card_ge hAy_le (by rw [hAf_card, hAy_card])
    have hfAy : f ∈ A ⊔ Subgroup.zpowers y := by
      rw [hEq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
    exact hfJ ((sup_le hA_le_J (Subgroup.zpowers_le.mpr hyJ)) hfAy)
  have hy_comm_Af : ∀ a ∈ A ⊔ Subgroup.zpowers f, a * y = y * a := by
    intro a ha
    have hAcent : A ≤ Subgroup.centralizer ({y} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (hA_central a ha y hyQ).symm
    have hfcent : Subgroup.zpowers f ≤ Subgroup.centralizer ({y} : Set G) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hfy.symm
    exact (Subgroup.mem_centralizer_iff.mp (sup_le hAcent hfcent ha) y
      (Set.mem_singleton y)).symm
  obtain ⟨hOmega_ea, hOmega_card⟩ :=
    elemAbelian_sup_zpowers_card hAf_ea hy_not_Af hy3 hy_comm_Af
  refine ⟨(A ⊔ Subgroup.zpowers f) ⊔ Subgroup.zpowers y, ?_, hOmega_ea, ?_, ?_⟩
  · exact sup_le (sup_le (hA_le_Q) (Subgroup.zpowers_le.mpr hfQ))
      (Subgroup.zpowers_le.mpr hyQ)
  · rw [hOmega_card, hAf_card, hAcard]
  · exact le_sup_left.trans le_sup_left

theorem CaseOneCtx.inf_D_eq_bot {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    Q ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M = ⊥ :=
  inf_inSubgroup_pPrimeCore_eq_bot c.choice.sylow.isPGroup

theorem CaseOneCtx.pRank_threeStar_le {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hquot := CFSG.SectionRank.pRank_quotient_eq (p := 3)
    (N := CFSG.pPrimeCore 3 ↥M) (by
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card)
  have htop := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) M
  have hm3 : CFSG.Open.pRank 3 M ≤ 3 :=
    c.choice.cstar.pRank_le_three_of_not_mem_sigmaSet c.choice.maxLocal Nat.prime_three
      (by norm_num) c.choice.hypCGen.not_mem_sigmaSet
  calc CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M))
      = CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) := hquot
    _ = CFSG.Open.pRank 3 M := htop.symm
    _ ≤ 3 := hm3

private theorem mem_threeStarImg_center_of_mem_center {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) {z : threeStar M} (hzQ : z ∈ threeStarImg M Q)
    (hzcent : ∀ w ∈ threeStarImg M Q, z * w = w * z) :
    z ∈ threeStarImg M ((Subgroup.center ↥Q).map Q.subtype) := by
    have hQM : Q ≤ M := c.choice.Q_le_M c.nine
    let e : ↥Q ≃* ↥(threeStarImg M Q) :=
      threeStarImgMulEquiv M Q hQM c.inf_D_eq_bot
    let zQ : ↥(threeStarImg M Q) := ⟨z, hzQ⟩
    have hzQcenter : zQ ∈ Subgroup.center ↥(threeStarImg M Q) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact (hzcent (w : threeStar M) w.2).symm
    have hmaps := Subgroup.map_center_eq e
    have hmem : zQ ∈ (Subgroup.center ↥Q).map e.toMonoidHom := by
      have h : zQ ∈ (Subgroup.center ↥Q).map (↑e) := by
        rw [hmaps]
        exact hzQcenter
      simpa only [MulEquiv.toMonoidHom_eq_coe] using h
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp hmem
    have hzA : z ∈ threeStarImg M ((Subgroup.center ↥Q).map Q.subtype) := by
      rw [threeStarImg]
      refine Subgroup.mem_map.mpr ⟨⟨(q : G), hQM q.2⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem Q.subtype hq), ?_⟩
      have hval : ((e q : ↥(threeStarImg M Q)) : threeStar M) = z :=
        congrArg Subtype.val hqe
      rwa [show ((e q : ↥(threeStarImg M Q)) : threeStar M) =
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ⟨(q : G), hQM q.2⟩ from rfl] at hval
    exact hzA
theorem CaseOneCtx.mem_centerImg_of_centralizes
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M) {z : threeStar M}
    (hz : orderOf z = 3)
    (hzQ : threeStarImg M Q ≤ Subgroup.centralizer ({z} : Set (threeStar M))) :
    z ∈ threeStarImg M ((Subgroup.center ↥Q).map Q.subtype) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Ω, hΩQ, hΩea, hΩcard, hA_le_Ω⟩ := c.exists_E27 h142
  let A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  have hQM : Q ≤ M := c.choice.Q_le_M c.nine
  have hΩM : Ω ≤ M := hΩQ.trans hQM
  have hAM : A ≤ M := (Subgroup.map_subtype_le _).trans hQM
  have hΩbar_ea : IsElemAbelian 3 (threeStarImg M Ω) := by
    rw [threeStarImg]
    exact CFSG.SectionRank.isElemAbelian_map (hΩea.comap M.subtype_injective)
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))
  have hΩbar_card : Nat.card ↥(threeStarImg M Ω) = 27 := by
    rw [card_threeStarImg_of_isPGroup hΩea.isPGroup hΩM, hΩcard]
  have hΩbar_le_Qbar : threeStarImg M Ω ≤ threeStarImg M Q := by
    rw [threeStarImg, threeStarImg]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono M hΩQ)
  by_contra hznotA
  have hz_not_Ωbar : z ∉ threeStarImg M Ω := by
    intro hzΩ
    apply hznotA
    exact mem_threeStarImg_center_of_mem_center c (hΩbar_le_Qbar hzΩ) (by
      intro w hw
      exact Subgroup.mem_centralizer_iff.mp (hzQ hw) z (Set.mem_singleton z))
  have hz_comm : ∀ a ∈ threeStarImg M Ω, a * z = z * a := by
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hzQ (hΩbar_le_Qbar ha)) z
      (Set.mem_singleton z)).symm
  have hz3 : z ^ 3 = 1 := by
    simpa [hz] using pow_orderOf_eq_one z
  obtain ⟨hsup_ea, hsup_card⟩ :=
    elemAbelian_sup_zpowers_card hΩbar_ea hz_not_Ωbar hz3 hz_comm
  have hsup_le : threeStarImg M Ω ⊔ Subgroup.zpowers z ≤
      (⊤ : Subgroup (threeStar M)) := le_top
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hsup_le hsup_ea (by
      rw [hsup_card, hΩbar_card]
      norm_num)
  have hle := c.pRank_threeStar_le
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
