module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbOrbit
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem ne_bot_of_component {L : Subgroup Y} (hL : IsComponentOf L ⊤) : L ≠ ⊥ := by
  intro hbot
  have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have ha : (a' : Y) ∈ (⊥ : Subgroup Y) := hbot ▸ a'.2
  have hb : (b' : Y) ∈ (⊥ : Subgroup Y) := hbot ▸ b'.2
  have : a' = b' := Subtype.ext ((Subgroup.mem_bot.mp ha).trans (Subgroup.mem_bot.mp hb).symm)
  rw [this]

theorem eq_one_of_mem_center_component_of_pCore {p : ℕ} [Fact p.Prime]
    (hY : CFSG.pCore p Y = ⊥) {L : Subgroup Y} (hL : IsComponentOf L ⊤) {w : Y} (hwL : w ∈ L)
    (hwC : w ∈ Subgroup.centralizer (L : Set Y)) (hwp : w ^ p = 1) : w = 1 := by
  set S := Group.conjugatesOfSet ({w} : Set Y) with hS
  have hconj : ∀ x ∈ S, ∃ g : Y, g * w * g⁻¹ = x := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨g, hg⟩ := isConj_iff.mp hax
    exact ⟨g, hg⟩
  have hmemL : ∀ g : Y, g * w * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := fun g =>
    ⟨w, hwL, rfl⟩
  have hmemC : ∀ g : Y, g * w * g⁻¹ ∈
      Subgroup.centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hwC l hl
    change g * l * g⁻¹ * (g * w * g⁻¹) = g * w * g⁻¹ * (g * l * g⁻¹)
    calc g * l * g⁻¹ * (g * w * g⁻¹) = g * (l * w) * g⁻¹ := by group
      _ = g * (w * l) * g⁻¹ := by rw [h1]
      _ = g * w * g⁻¹ * (g * l * g⁻¹) := by group
  have hcomp : ∀ g : Y, IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ := fun g =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  have hpair : S.Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨g, rfl⟩ := hconj x hx
    obtain ⟨h, rfl⟩ := hconj y hy
    by_cases he : L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj h).toMonoidHom
    · have hyg : h * w * h⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := he ▸ hmemL h
      exact (Subgroup.mem_centralizer_iff.mp (hmemC g) _ hyg).symm
    · have hxC := le_centralizer_of_component_ne (hcomp g) (hcomp h) he (hmemL g)
      exact (Subgroup.mem_centralizer_iff.mp hxC _ (hmemL h)).symm
  have hcomm : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hpair
  set N := Subgroup.normalClosure ({w} : Set Y) with hN
  have hNS : N = Subgroup.closure S := rfl
  have hNp : ∀ x ∈ N, x ^ p = 1 := by
    intro x hx
    rw [hNS] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hconj x hx
      rw [conj_pow, hwp]
      group
    | one => exact one_pow p
    | mul x y hxN hyN hx hy =>
      have hxy : Commute x y := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hxN⟩ ⟨y, hyN⟩)
      rw [hxy.mul_pow, hx, hy, one_mul]
    | inv x _ hx => rw [inv_pow, hx, inv_one]
  have hNpg : IsPGroup p N := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hNp x x.2)⟩
  have hle : N ≤ CFSG.pCore p Y := le_sSup ⟨Subgroup.normalClosure_normal, hNpg⟩
  rw [hY] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.subset_normalClosure (Set.mem_singleton w)))

theorem le_normalizer_of_perfect_of_orbit {D L : Subgroup Y} (hD : ⁅D, D⁆ = D)
    (horbit : ∀ g : Fin 4 → Y, (∀ j, g j ∈ D) →
      ¬ Function.Injective fun j => L.map (MulAut.conj (g j)).toMonoidHom) :
    D ≤ Subgroup.normalizer (L : Set Y) := by
  classical
  set St : Subgroup D := (Subgroup.normalizer (L : Set Y)).subgroupOf D with hSt
  have hDperf : commutator D = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hD]
  have hidx : St.index ≤ 3 := by
    by_contra h4
    push Not at h4
    have : Fintype (D ⧸ St) := Fintype.ofFinite _
    have hcard' : Fintype.card (Fin 4) ≤ Fintype.card (D ⧸ St) := by
      rw [Fintype.card_fin, Fintype.card_eq_nat_card]
      exact h4
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard'
    choose g hg using fun j => QuotientGroup.mk_surjective (f j)
    refine horbit (fun j => (g j : Y)) (fun j => (g j).2) fun i j hij => f.injective ?_
    have hmm : ∀ (a b : Y) (X : Subgroup Y), X.map (MulAut.conj (a * b)).toMonoidHom =
        (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      intro a b X
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have h2' : L.map (MulAut.conj ((g j : Y)⁻¹ * (g i : Y))).toMonoidHom = L := by
      have hij' : L.map (MulAut.conj (g i : Y)).toMonoidHom =
          L.map (MulAut.conj (g j : Y)).toMonoidHom := hij
      rw [hmm, hij', ← hmm, inv_mul_cancel]
      ext x
      simp
    have h2 : ((g j)⁻¹ * g i : D) ∈ St := by
      rw [hSt, Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff_map_conj_eq]
      push_cast
      exact h2'
    rw [← hg i, ← hg j, QuotientGroup.eq]
    have := St.inv_mem h2
    simpa using this
  have htop := eq_top_of_perfect_of_index_le_four hDperf St (by omega)
  intro d hd
  have hmem : (⟨d, hd⟩ : D) ∈ St := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

end Abstract

section D1

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem pCore_eq_bot_of_posZero (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hV : d1MapPCore p M H = ⊥) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ := by
  have hp : p.Prime := h3.prime
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) w
  have hmY : (m : G) ∈ pCorePreimage p M := ⟨m, hw, rfl⟩
  have hmH : (m : G) ∈ H := ((h3.pCorePreimage_le_inf h84 hD2) hmY).1
  have hπ : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨m, hmH⟩ = 1 := by
    have : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨m, hmH⟩ ∈ d1MapPCore p M H :=
      ⟨⟨m, hmH⟩, Subgroup.mem_subgroupOf.mpr hmY, rfl⟩
    rw [hV] at this
    exact Subgroup.mem_bot.mp this
  have hmO : (m : G) ∈ GLBPrimeCore p H := (mem_glbPrimeCore_iff_mk_eq_one _).mpr hπ
  have hcop : Nat.Coprime (orderOf (m : G)) p := by
    have h1 : orderOf (m : G) ∣ Nat.card (GLBPrimeCore p H) :=
      Subgroup.orderOf_dvd_natCard _ hmO
    exact Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_comm.mp (glbPrimeCore_coprime p H))
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p)
    (G := ↥M ⧸ CFSG.pCore 2 ↥M)) ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hw⟩
  have hk' : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hdvd1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) ∣ orderOf (m : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd _ _
  have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd2
    (Nat.Coprime.pow_right k hcop)) hdvd1
  rw [orderOf_eq_one_iff] at h1
  rw [h1]
  exact Subgroup.one_mem _

theorem D1PhaseThree.false_of_component_le_primeCore (h3 : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (hp5 : 5 ≤ p) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) {L : Subgroup G} (hL2 : IsTwoPrimeComponent M L)
    (hLN : L ≤ GLBPrimeCore p H) {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D)
    (hDK : D ≤ barM M (H ⊓ M)) {zb : ↥M ⧸ CFSG.pCore 2 ↥M} (hzD : zb ∈ D) (hzp : zb ^ p = 1)
    (hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → W = ⊥) : False := by
  have hpp : p.Prime := h3.prime
  have : Fact p.Prime := ⟨hpp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Kb := barM M (H ⊓ M) with hKb
  have hLK : L ≤ H ⊓ M := hLN.trans (le_inf (glbPrimeCore_le p H) h3.primeCore_le)
  have hLbC : IsComponentOf Lb ⊤ := hL2.component
  have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop).quotient _
  have hLcat := hcat.isCatalogGroup_center_quotient hLbC
  have hpL : ¬ p ∣ Nat.card Lb := by
    have hcop : p.Coprime (Nat.card L) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) (glbPrimeCore_coprime p H)
    have hdvd : Nat.card Lb ∣ Nat.card L := by
      have := Subgroup.card_map_dvd (L.subgroupOf M) mk
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv] at this
    intro hpd
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcop (hpd.trans hdvd)
  have hsimple : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hLbC.2.2.2
  have hdvdL : Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) ∣ Nat.card Lb :=
    Subgroup.card_quotient_dvd_card _
  obtain ⟨q, hq, hq2, hqp, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q < p ∧
      q ∣ Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) := by
    rcases hα _ hsimple
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLbC.2.2)
      hLcat with h3' | h5
    · exact ⟨3, Nat.prime_three, by decide, by omega, h3'⟩
    · refine ⟨5, Nat.prime_five, by decide, ?_, h5⟩
      have hp5' : p ≠ 5 := fun he => hpL (he ▸ h5.trans hdvdL)
      omega
  obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqdvd
  have hLbK : Lb ≤ Kb := Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.mpr
    (hLK (Subgroup.mem_subgroupOf.mp hz)))
  have hDN : D ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine le_normalizer_of_perfect_of_orbit hDp fun g hg hinj => ?_
    have hm := le_pRank_of_injective_conj stmtComponentRank stmtBarPRankLift inf_le_right hq
      hq2 hLbC hLbK hyL hyq hlL hyl g (fun j => hDK (hg j)) hinj
    exact h3.false_of_four_le_pRank' hind hq hq2 hqp hm
  have hOut := isSolvable_outer_of_component hSch hLbC hLcat
  have hDLC := perfect_le_sup_centralizer_of_outer hOut hDp hDN
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hLC : Lb ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hzLC := hDLC hzD
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb Cb hLC] at hzLC
  obtain ⟨l', hl', c, hc, hlc⟩ := hzLC
  have hlcc : l' * c = c * l' := Subgroup.mem_centralizer_iff.mp hc l' hl'
  have hl'p : l' ^ p ∈ Cb := by
    have h1 : (l' * c) ^ p = 1 := by
      have := hlc ▸ hzp
      exact this
    rw [(Commute.mul_pow hlcc)] at h1
    have h2 : l' ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact Cb.inv_mem (Cb.pow_mem hc p)
  have hcen : (⟨l', hl'⟩ : Lb) ^ p ∈ Subgroup.center Lb := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hl'p (g : ↥M ⧸ CFSG.pCore 2 ↥M) g.2
    simpa using this
  have hord : orderOf ((⟨l', hl'⟩ : Lb) : ↥Lb ⧸ Subgroup.center ↥Lb) = 1 := by
    have h1 : ((⟨l', hl'⟩ : Lb) : ↥Lb ⧸ Subgroup.center ↥Lb) ^ p = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hcen
    have hd1 := orderOf_dvd_of_pow_eq_one h1
    have hd2 := (orderOf_dvd_natCard ((⟨l', hl'⟩ : Lb) : ↥Lb ⧸ Subgroup.center ↥Lb)).trans hdvdL
    rcases (Nat.dvd_prime hpp).mp hd1 with h | h
    · exact h
    · exact absurd (h ▸ hd2) hpL
  have hl'Z : (⟨l', hl'⟩ : Lb) ∈ Subgroup.center Lb := by
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hord
    exact hord
  have hl'C : l' ∈ Cb := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp hl'Z ⟨g, hg⟩
    simpa using congrArg Subtype.val this
  have hzC : zb ∈ Cb := hlc ▸ Cb.mul_mem hl'C hc
  apply ne_bot_of_component hLbC
  refine hZ Lb (Subgroup.isPerfect_iff.mp ⟨hLbC.2.2.1⟩) fun x hx => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hzC x hx

theorem D1OneSmallData.pRank_le_three_of_le_H (hd : D1OneSmallData p P M H R Rbar K)
    {A : Subgroup G} (hAH : A ≤ H) : CFSG.Open.pRank p A ≤ 3 := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  rw [← hd.pRank_R]
  obtain ⟨E, hEA, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  obtain ⟨T, hT⟩ := hd.cfg.ext.isSylow
  have hEH : E ≤ H := hEA.trans hAH
  have hEp : IsPGroup p (E.subgroupOf H) := (IsPGroup.of_card hcard).comap_subtype
  obtain ⟨Q, hQ⟩ := hEp.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq H T Q
  have hle : E.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : (⟨x, hEH hx⟩ : H) ∈ ((h • T : Sylow p H) : Subgroup H) :=
      hQ (Subgroup.mem_subgroupOf.mpr hx)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨y, hy, hyx⟩ := hxQ
    have hyx' : (h : G) * y * (h : G)⁻¹ = x := by
      have := congrArg Subtype.val hyx
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [← hT]
    refine ⟨y, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype, inv_inv]
    rw [← hyx']
    group
  have hE' : IsElemAbelian p (E.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hcard' : Nat.card (E.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom) =
      p ^ CFSG.Open.pRank p A :=
    (Subgroup.card_map_of_injective (MulAut.conj ((h : G)⁻¹)).injective).trans hcard
  exact le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp R) ⟨_, hle, hE', hcard'⟩

end D1

end CFSG.AGLEmbedding
