module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Torus
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
import CFSG.RankThree.PartOne.HNB.Tools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalance
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankFourTheoremC
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)

@[expose] def TypeU0Facts {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G)
    (J : Subgroup G) : Prop :=
  IsElemAbelian p (u3U0 P x J) ∧ Nat.card (u3U0 P x J) = p ^ 2 ∧ u3U0 P x J ≤ u3S P x ∧
    x ∈ u3U0 P x J ∧ (∀ s ∈ u3S P x, ∀ u ∈ u3U0 P x J, s * u = u * s) ∧
    Nat.card (u3ZT P x J) = p ∧ u3ZT P x J ≤ J

structure FusionStruct {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G)
    (J : Subgroup G) : Prop where
  T : TypeTStruct p P x J
  Z : TypeSDecomp p P x J
  U0 : TypeU0Facts p P x J

structure Lemma33Data {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G)
    (J : Subgroup G) : Prop where
  not_mem : x ∉ J
  exp : ∀ t ∈ u3T P x J, t ^ p = 1
  rank : ∀ E : Subgroup G, E ≤ u3T P x J → IsElemAbelian p E → Nat.card E ≤ p ^ 2
  decomp : ∃ Z : Subgroup G, IsCyclic Z ∧ x ∈ Z ∧ Z ≤ u3S P x ∧
    (∀ z ∈ Z, ∀ t ∈ u3T P x J, z * t = t * z) ∧ u3T P x J ⊔ Z = u3S P x
  plane : ∃ A : Subgroup G, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ A ≤ u3S P x ∧
    ∀ s ∈ u3S P x, ∀ a ∈ A, s * a = a * s

@[expose] def TypeSE (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Typ p K → IsRankTwoSEGroup p K ∧ IsCatalogGroup K

@[expose] def TypeTorusLift {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G)
    (J : Subgroup G) : Prop :=
  ∀ c ∈ u3T P x J, c ∈ Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G) → c ≠ 1 →
    ∀ k : ℤ, ¬ (p : ℤ) ∣ k → ∃ h ∈ J, h * c * h⁻¹ = c ^ k

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

@[expose] def U3Lemma33 (p : ℕ) (x : G) : Prop :=
  ∀ D : Subgroup G, D ≤ Subgroup.centralizer ({x} : Set G) → IsElemAbelian p D → Nat.card D = p ^ 2 →
    ∀ s : Finset (Subgroup G), (∀ A ∈ s, A ≤ D ∧ Nat.card A = p ∧
      ∃ g : G, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) → s.card < p

theorem fus_mem_zpowers_of_isCyclic_of_pow_prime {p : ℕ} [Fact p.Prime] {Z : Subgroup G}
    (hZ : IsCyclic Z) {x z : G} (hxZ : x ∈ Z) (hzZ : z ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hzp : z ^ p = 1) : z ∈ Subgroup.zpowers x := by
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem _
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  have h := (IsCyclic.subgroup_eq_iff_card_eq (G := Z) (H := Subgroup.zpowers (⟨x, hxZ⟩ : Z))
    (K := Subgroup.zpowers (⟨z, hzZ⟩ : Z))).2 (by
      rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxo, hzo])
  have hz' : (⟨z, hzZ⟩ : Z) ∈ Subgroup.zpowers (⟨x, hxZ⟩ : Z) := by
    rw [h]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem commutator_mem_inf_centralizer {p : ℕ} [Fact p.Prime] {T : Subgroup G}
    (hcard : Nat.card T = p ^ 3) (hnc : ¬ IsMulCommutative T) {a b : G} (ha : a ∈ T)
    (hb : b ∈ T) :
    a * b * a⁻¹ * b⁻¹ ∈ T ⊓ Subgroup.centralizer (T : Set G) := by
  have hZ : Nat.card (Subgroup.center T) = p := card_center_of_nonabelian_card_p_cube hcard hnc
  have hq : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center T)
    rw [hcard, hZ] at h
    apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
    rw [← h]
    ring
  have hcomm : IsMulCommutative (T ⧸ Subgroup.center T) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hmem : (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : T)⁻¹ * (⟨b, hb⟩ : T)⁻¹ : T) ∈
      Subgroup.center T := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center T)]
    have h1 := hcomm.is_comm.comm (QuotientGroup.mk (⟨a, ha⟩ : T) : T ⧸ Subgroup.center T)
      (QuotientGroup.mk (⟨b, hb⟩ : T))
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1 ⊢
    rw [h1]
    group
  refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha))
    (T.inv_mem hb), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := Subgroup.mem_center_iff.mp hmem ⟨h, hh⟩
  exact congrArg Subtype.val this

theorem fus_exists_mul_of_sup_eq {T Z S : Subgroup G}
    (hcomm : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hsup : T ⊔ Z = S) :
    ∀ s ∈ S, ∃ t ∈ T, ∃ z ∈ Z, s = t * z := by
  have hrange := MonoidHom.noncommCoprod_range T.subtype Z.subtype
    (fun a b => (hcomm b b.2 a a.2).symm)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  intro s hs
  rw [← hsup, ← hrange] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem u3_isSimple_quot {J O : Subgroup G} (hOJ : O ≤ J) (hlt : O < J)
    (hmin : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → O ≤ N → N = O ∨ N = J)
    {Q : Type} [Group Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = O.subgroupOf J) : IsSimpleGroup Q := by
  have hkerne : ψ.ker ≠ ⊤ := by
    intro h
    rw [hker, Subgroup.subgroupOf_eq_top] at h
    exact hlt.ne (le_antisymm hOJ h)
  refine { toNontrivial := ?_, eq_bot_or_eq_top_of_normal := ?_ }
  · by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hkerne (eq_top_iff.mpr fun j _ => Subsingleton.elim _ _)
  · intro S hS
    set N : Subgroup G := (S.comap ψ).map J.subtype with hN
    have hNJ : N ≤ J := Subgroup.map_subtype_le _
    have hNsub : N.subgroupOf J = S.comap ψ :=
      Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
    have hNn : (N.subgroupOf J).Normal := by
      rw [hNsub]
      exact Subgroup.Normal.comap hS ψ
    have hON : O ≤ N := by
      intro o ho
      refine ⟨⟨o, hOJ ho⟩, ?_, rfl⟩
      show ψ ⟨o, hOJ ho⟩ ∈ S
      have : (⟨o, hOJ ho⟩ : J) ∈ ψ.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        exact ho
      rw [MonoidHom.mem_ker.mp this]
      exact S.one_mem
    rcases hmin N hNJ hNn hON with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨j, rfl⟩ := hψ s
      have hj : j ∈ S.comap ψ := hs
      rw [← hNsub, h, ← hker] at hj
      exact MonoidHom.mem_ker.mp hj
    · right
      rw [eq_top_iff]
      intro s _
      obtain ⟨j, rfl⟩ := hψ s
      have : j ∈ N.subgroupOf J := by
        rw [h, Subgroup.subgroupOf_self]
        exact Subgroup.mem_top j
      rw [hNsub] at this
      exact this

theorem u3_card_map_mk_of_disjoint {X : Type} [Group X] (N : Subgroup X) [N.Normal]
    (E : Subgroup X) (hd : Disjoint E N) :
    Nat.card (E.map (QuotientGroup.mk' N)) = Nat.card E := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).domRestrict E) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    rw [eq_bot_iff]
    intro x hx
    have : (x : X) ∈ E ⊓ N := ⟨x.2, hx⟩
    rw [hd.eq_bot] at this
    exact Subtype.ext (by simpa using this)
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.domRestrict_range] at h
  exact h.symm

theorem centralizes_two_group_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G)
    (hD1 : TheoremD1 G) (hSig : SignalizerTwoGroupKFact) (hc : PointConfig Typ G p P M x J)
    (hSE : TypeSE Typ p) (hdat : Lemma33Data p P x J) {E F : Subgroup G}
    (hEQ : E ≤ u3S P x) (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E)
    (hF2 : IsPGroup 2 F) (hFC : F ≤ Subgroup.centralizer ({x} : Set G))
    (hEF : E ≤ Subgroup.normalizer (F : Set G)) :
    ∀ a ∈ E, ∀ f ∈ F, a * f = f * a := by
  have hxJ : x ∉ J := hdat.not_mem
  have hTexp := hdat.exp
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hsup⟩ := hdat.decomp
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 := hc.five
  have hp2 : p ≠ 2 := by omega
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  have hrank3 : CFSG.Open.pRank p (u3S P x) = 3 := hc.generic.2.2.2
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hSC : u3S P x ≤ C := inf_le_right
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hSx : ∀ s ∈ u3S P x, s * x = x * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
  have hcommEx : E ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hSx e (hEQ he))
  have hxel : IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hxp
  have hE'el : IsElemAbelian p (E ⊔ Subgroup.zpowers x) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hE hxel hcommEx
  have hE'S : E ⊔ Subgroup.zpowers x ≤ u3S P x := sup_le hEQ (Subgroup.zpowers_le.mpr hxS)
  have hE'p : IsPGroup p ↥(E ⊔ Subgroup.zpowers x) :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p _ hE'el
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE'p
  have hk3 : k ≤ 3 := by
    have := CFSG.SectionRank.le_pRank hp.one_lt hE'S hE'el hk
    omega
  have hEeq : E = E ⊔ Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
    rw [hk]
    exact (Nat.pow_le_pow_right hp.pos hk3).trans hE3
  have hxE : x ∈ E := by
    rw [hEeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  set E₂ : Subgroup G := E ⊓ J with hE₂
  have hE₂E : E₂ ≤ E := inf_le_left
  have hE₂T : E₂ ≤ u3T P x J := fun e he => ⟨hEQ he.1, he.2⟩
  have hE₂el : IsElemAbelian p E₂ := hE.mono hE₂E
  have hdec : ∀ e ∈ E, ∃ t ∈ E₂, ∃ z ∈ Subgroup.zpowers x, e = t * z := by
    intro e he
    obtain ⟨t₀, ht₀, z₀, hz₀, hez⟩ := fus_exists_mul_of_sup_eq hZT hsup e (hEQ he)
    have hcomm : Commute t₀ z₀ := (hZT z₀ hz₀ t₀ ht₀).symm
    have hep : e ^ p = 1 := hE.2 e he
    have hz₀p : z₀ ^ p = 1 := by
      rw [hez, hcomm.mul_pow, hTexp t₀ ht₀, one_mul] at hep
      exact hep
    have hzx : z₀ ∈ Subgroup.zpowers x :=
      fus_mem_zpowers_of_isCyclic_of_pow_prime hZcyc hxZ hz₀ hx1 hxp hz₀p
    have hz₀E : z₀ ∈ E := Subgroup.zpowers_le.mpr hxE hzx
    have ht₀e : t₀ = e * z₀⁻¹ := by rw [hez]; group
    have ht₀E : t₀ ∈ E := by rw [ht₀e]; exact E.mul_mem he (E.inv_mem hz₀E)
    exact ⟨t₀, ⟨ht₀E, hTJ ht₀⟩, z₀, hzx, hez⟩
  have hEle : E ≤ E₂ ⊔ Subgroup.zpowers x := fun e he => by
    obtain ⟨t, ht, z, hz, rfl⟩ := hdec e he
    exact Subgroup.mul_mem_sup ht hz
  have hxE₂ : x ∉ E₂ := fun h => hxJ h.2
  have hcommE₂x : ∀ a ∈ E₂, a * x = x * a := fun a ha => hSx a (hEQ ha.1)
  have hcardsup : Nat.card ↥(E₂ ⊔ Subgroup.zpowers x) = Nat.card E₂ * p :=
    CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp E₂ hxp hxE₂ hcommE₂x
  have hE₂ge : p ^ 2 ≤ Nat.card E₂ := by
    have h1 : Nat.card E ≤ Nat.card ↥(E₂ ⊔ Subgroup.zpowers x) := Subgroup.card_le_of_le hEle
    rw [hcardsup] at h1
    have h2 : p ^ 2 * p ≤ Nat.card E₂ * p := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ ≤ Nat.card E := hE3
        _ ≤ _ := h1
    exact Nat.le_of_mul_le_mul_right h2 hp.pos
  have hE₂le : Nat.card E₂ ≤ p ^ 2 := hdat.rank E₂ hE₂T hE₂el
  have hE₂card : Nat.card E₂ = p ^ 2 := le_antisymm hE₂le hE₂ge
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hJC : J ≤ C := hc.le_cent
  have hCJ : C ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  set O : Subgroup G := rankThreePrimeCore p J with hO
  have hOJ : O ≤ J := glbPrimeCore_le p J
  have hOC : O ≤ C := hOJ.trans hJC
  have hOcop : p.Coprime (Nat.card O) := glbPrimeCore_coprime p J
  obtain ⟨-, hOodd⟩ := u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hJC hCJ
  have hOnorm : C ≤ Subgroup.normalizer (O : Set G) := by
    intro g hg
    have hgJ : J.map (MulAut.conj g).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCJ hg)
    have h1 := glbPrimeCore_map_automorphism p J (MulAut.conj g)
    rw [hgJ] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  let O' : Subgroup C := O.subgroupOf C
  haveI hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOC).mpr hOnorm
  let π : C →* C ⧸ O' := QuotientGroup.mk' O'
  let J' : Subgroup C := J.subgroupOf C
  haveI hJ'n : J'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hCJ
  let L : Subgroup (C ⧸ O') := J'.map π
  haveI hLn : L.Normal := Subgroup.Normal.map hJ'n π (QuotientGroup.mk'_surjective O')
  let eJ : J' ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  let ψ' : J' →* Q := ψ.comp eJ.toMonoidHom
  have hψ' : Function.Surjective ψ' := hψ.comp eJ.surjective
  let πJ : J' →* L := (π.comp J'.subtype).codRestrict L (fun j => Subgroup.mem_map_of_mem π j.2)
  have hπJ : Function.Surjective πJ := by
    rintro ⟨_, j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  have hkerEq : ψ'.ker = πJ.ker := by
    ext j
    have h1 : ψ' j = 1 ↔ ((j : C) : G) ∈ O := by
      have h : ψ (eJ j) = 1 ↔ eJ j ∈ ψ.ker := MonoidHom.mem_ker.symm
      rw [show ψ' j = ψ (eJ j) from rfl, h, hker, Subgroup.mem_subgroupOf]
      rfl
    have h2 : πJ j = 1 ↔ ((j : C) : G) ∈ O := by
      constructor
      · intro h
        have h' : π (j : C) = 1 := congrArg Subtype.val h
        exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (j : C)).mp h'))
      · intro h
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (j : C)).mpr (Subgroup.mem_subgroupOf.mpr h)
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, h1, h2]
  let eL : L ≃* Q :=
    (QuotientGroup.quotientKerEquivOfSurjective πJ hπJ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ'))
  have hQSE := hSE Q hQ
  have hLSE : IsRankTwoSEGroup p ↥L := IsRankTwoSEGroup.of_mulEquiv eL.symm hQSE.1
  have hQZ : Subgroup.center Q = ⊥ :=
    u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ hker
  haveI hQsimple : IsSimpleGroup Q := u3_isSimple_quot hOJ hc.lt hc.minimal ψ hψ hker
  have hLZ : ∀ l : L, (∀ m : L, m * l = l * m) → l = 1 := by
    intro l hl
    have : eL l ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨m, rfl⟩ := eL.surjective q
      rw [← map_mul, ← map_mul, hl m]
    rw [hQZ, Subgroup.mem_bot] at this
    exact eL.injective (this.trans (map_one eL).symm)
  haveI hLsimple : IsSimpleGroup L := eL.isSimpleGroup
  have hLnonab : ∃ a b : L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl⟩ := exists_ne (1 : L)
    exact hl (hLZ l (fun m => hcon m l))
  have hLcat : IsCatalogGroup L := by
    obtain ⟨i, ⟨f⟩⟩ := hQSE.2
    exact ⟨i, ⟨eL.trans f⟩⟩
  have hPO : (P : Subgroup G) ⊓ O = ⊥ := by
    have hPp : IsPGroup p ↥((P : Subgroup G) ⊓ O) := P.isPGroup'.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have hdvd : Nat.card ((P : Subgroup G) ⊓ O : Subgroup G) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hk0
      have : p ∣ Nat.card O := (dvd_pow_self p hk0).trans (hk ▸ hdvd)
      exact (hp.coprime_iff_not_dvd.mp hOcop) this
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hFO : F ⊓ O = ⊥ := by
    have hFp : IsPGroup 2 ↥(F ⊓ O) := hF2.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hFp
    have hdvd : Nat.card (F ⊓ O : Subgroup G) ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ Nat.card O := (dvd_pow_self 2 hk0).trans (hk ▸ hdvd)
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hE₂J : E₂ ≤ J := inf_le_right
  have hE₂C : E₂ ≤ C := hE₂J.trans hJC
  have hSP : u3S P x ≤ (P : Subgroup G) := inf_le_left
  have hE₂P : E₂ ≤ (P : Subgroup G) := fun e he => hSP (hEQ (hE₂E he))
  have hE₂O : Disjoint E₂ O := by
    rw [disjoint_iff, eq_bot_iff]
    intro g hg
    have h1 : g ∈ (P : Subgroup G) ⊓ O := ⟨hE₂P hg.1, hg.2⟩
    rw [hPO] at h1
    exact h1
  let E₂C : Subgroup C := E₂.subgroupOf C
  let FC : Subgroup C := F.subgroupOf C
  have hdisj : Disjoint E₂C O' := by
    rw [disjoint_iff, eq_bot_iff]
    intro c hc
    have h1 : (c : G) ∈ E₂ ⊓ O := ⟨hc.1, hc.2⟩
    rw [hE₂O.eq_bot] at h1
    exact Subtype.ext (by simpa using h1)
  let B : Subgroup (C ⧸ O') := E₂C.map π
  let Fb : Subgroup (C ⧸ O') := FC.map π
  have hBel : IsElemAbelian p B := (hE₂el.subgroupOf C).map π
  have hBcard : Nat.card B = p ^ 2 := by
    rw [u3_card_map_mk_of_disjoint O' E₂C hdisj, ← hE₂card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₂C).toEquiv
  have hBL : B ≤ L := Subgroup.map_mono (fun c hc => hE₂J hc)
  have hFbp : IsPGroup 2 Fb := (hF2.of_equiv (Subgroup.subgroupOfEquivOfLe hFC).symm).map π
  have hconj : ∀ e' ∈ E₂C, ∀ f ∈ FC, e' * f * e'⁻¹ ∈ FC := by
    intro e' he' f hf
    have h1 : ((e' : C) : G) ∈ Subgroup.normalizer (F : Set G) := hEF (hE₂E he')
    exact (Subgroup.mem_normalizer_iff.mp h1 (f : G)).mp hf
  have hBnorm : B ≤ Subgroup.normalizer (Fb : Set (C ⧸ O')) := by
    rintro _ ⟨ec, hec, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective O') h
    constructor
    · rintro ⟨f, hf, hfg⟩
      refine ⟨ec * f * ec⁻¹, hconj ec hec f hf, ?_⟩
      rw [map_mul, map_mul, map_inv, hfg]
    · rintro ⟨f, hf, hfg⟩
      refine ⟨ec⁻¹ * f * ec, ?_, ?_⟩
      · have := hconj ec⁻¹ (E₂C.inv_mem hec) f hf
        simpa using this
      · rw [map_mul, map_mul, map_inv, hfg]
        group
  have hBZ : B ⊓ Subgroup.centralizer (L : Set (C ⧸ O')) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hbL : b ∈ L := hBL hb.1
    have h1 : (⟨b, hbL⟩ : L) = 1 := hLZ ⟨b, hbL⟩ (fun m =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hb.2 (m : C ⧸ O') m.2))
    exact congrArg Subtype.val h1
  have hKey := hSig (C ⧸ O') L hLn hLsimple hLnonab hLcat p hp hp2 B hBel hBcard hBZ
    (Or.inl ⟨hLSE, hBL⟩) Fb hFbp hBnorm
  have hkey2 : ∀ e ∈ E₂, ∀ f ∈ F,
      e * (e * f * e⁻¹ * f⁻¹) = (e * f * e⁻¹ * f⁻¹) * e := by
    intro e he f hf
    have hen : e ∈ Subgroup.normalizer (F : Set G) := hEF (hE₂E he)
    obtain ⟨k, hk⟩ : ∃ k : G, k = e * f * e⁻¹ * f⁻¹ := ⟨_, rfl⟩
    have hkF : k ∈ F := by
      rw [hk]
      exact F.mul_mem ((Subgroup.mem_normalizer_iff.mp hen f).mp hf) (F.inv_mem hf)
    let eC : C := ⟨e, hE₂C he⟩
    let fC : C := ⟨f, hFC hf⟩
    let kC : C := ⟨k, hFC hkF⟩
    have hkC : kC = eC * fC * eC⁻¹ * fC⁻¹ := Subtype.ext hk
    have heB : π eC ∈ B := Subgroup.mem_map_of_mem π (show eC ∈ E₂C from he)
    have hfF : π fC ∈ Fb := Subgroup.mem_map_of_mem π (show fC ∈ FC from hf)
    have h1 : π kC ∈ Subgroup.centralizer (L : Set (C ⧸ O')) := by
      have h0 := hKey (Subgroup.commutator_mem_commutator heB hfF)
      rw [hkC, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact h0
    have h2 : π eC ∈ L := hBL heB
    have h3 := Subgroup.mem_centralizer_iff.mp h1 (π eC) h2
    have h4 : π (eC * kC * eC⁻¹ * kC⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h3]
      group
    have h5 : (eC * kC * eC⁻¹ * kC⁻¹ : C) ∈ O' := by
      rw [← QuotientGroup.ker_mk' O']
      exact h4
    have h6 : e * k * e⁻¹ * k⁻¹ ∈ O := h5
    have h7 : e * k * e⁻¹ * k⁻¹ ∈ F :=
      F.mul_mem ((Subgroup.mem_normalizer_iff.mp hen k).mp hkF) (F.inv_mem hkF)
    have h8 : e * k * e⁻¹ * k⁻¹ ∈ F ⊓ O := ⟨h7, h6⟩
    rw [hFO] at h8
    rw [← hk]
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp (Subgroup.mem_bot.mp h8))
  have hE₂F : ∀ e ∈ E₂, ∀ f ∈ F, e * f = f * e := by
    intro e he f hf
    have hen : e ∈ Subgroup.normalizer (F : Set G) := hEF (hE₂E he)
    obtain ⟨k, hk⟩ : ∃ k : G, k = e * f * e⁻¹ * f⁻¹ := ⟨_, rfl⟩
    have hkF : k ∈ F := by
      rw [hk]
      exact F.mul_mem ((Subgroup.mem_normalizer_iff.mp hen f).mp hf) (F.inv_mem hf)
    have hcomm : Commute e k := by
      rw [hk]
      exact hkey2 e he f hf
    have hef : e * f * e⁻¹ = k * f := by rw [hk]; group
    have hpow : ∀ n : ℕ, e ^ n * f * (e ^ n)⁻¹ = k ^ n * f := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 : e * k ^ n * e⁻¹ = k ^ n := by
          rw [(hcomm.pow_right n).eq]
          group
        calc e ^ (n + 1) * f * (e ^ (n + 1))⁻¹
            = e * (e ^ n * f * (e ^ n)⁻¹) * e⁻¹ := by
              rw [pow_succ', mul_inv_rev]
              simp only [mul_assoc]
          _ = e * (k ^ n * f) * e⁻¹ := by rw [ih]
          _ = (e * k ^ n * e⁻¹) * (e * f * e⁻¹) := by simp only [mul_assoc, inv_mul_cancel_left]
          _ = k ^ (n + 1) * f := by rw [h1, hef, pow_succ, mul_assoc]
    have hep : e ^ p = 1 := hE₂el.2 e he
    have hkp : k ^ p = 1 := by
      have h := hpow p
      rw [hep, one_mul, inv_one, mul_one] at h
      simpa using h.symm
    have hk1 : k = 1 := by
      obtain ⟨m, hm⟩ := hF2 ⟨k, hkF⟩
      have hm' : k ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      have h1 : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
      have h2 : orderOf k ∣ p := orderOf_dvd_of_pow_eq_one hkp
      have hcop : Nat.Coprime (2 ^ m) p :=
        Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
      exact orderOf_eq_one_iff.mp
        ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)
    have h0 : e * f * e⁻¹ * f⁻¹ = 1 := by rw [← hk]; exact hk1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h0)
  intro a ha f hf
  obtain ⟨t, ht, z, hz, rfl⟩ := hdec a ha
  have hzf : z * f = f * z := by
    have hxf : x ∈ Subgroup.centralizer ({f} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hFC hf)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hxf) hz)
  calc t * z * f = t * (z * f) := by rw [mul_assoc]
    _ = t * (f * z) := by rw [hzf]
    _ = (t * f) * z := by rw [mul_assoc]
    _ = (f * t) * z := by rw [hE₂F t ht f hf]
    _ = f * (t * z) := by rw [mul_assoc]

omit [Finite G] in
private theorem u3f_mem_normalizer_commutator {A D : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hD : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, D⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hD ⊢
  rw [Subgroup.map_commutator, hA, hD]

omit [Finite G] in
private theorem u3f_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hA, hB]

omit [Finite G] in
private theorem u3f_mem_normalizer_centralizer_of_le {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  normalizer_le_normalizer_centralizer L (Subgroup.centralizer_le_normalizer (L : Set G) hg)

omit [Finite G] in
private theorem u3f_le_normalizer_pCoreOf_two (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  have hn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 H H le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  exact Subgroup.le_normalizer_of_normal_subgroupOf
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 H)

omit [Finite G] in
private theorem u3f_exists_conj_to_sylow {p : ℕ} [Fact p.Prime] [Finite G] {Q E L₀ : Subgroup G}
    {x : G} (hQ : CFSG.ABGLocalTools.IsSylowOf p Q (Subgroup.centralizer ({x} : Set G)))
    (hE : IsPGroup p E) (hEL : E ≤ Subgroup.centralizer (L₀ : Set G)) {g : G}
    (hg : L₀ = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) :
    ∃ k : G, E.map (MulAut.conj k).toMonoidHom ≤ Q ∧
      L₀.map (MulAut.conj k).toMonoidHom = Subgroup.zpowers x := by
  have hgx : g * x * g⁻¹ ∈ L₀ := hg ▸ ⟨x, Subgroup.mem_zpowers x, rfl⟩
  have hE₁C : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : e * (g * x * g⁻¹) = (g * x * g⁻¹) * e :=
      (Subgroup.mem_centralizer_iff.mp (hEL he) _ hgx).symm
    change g⁻¹ * e * g⁻¹⁻¹ * x = x * (g⁻¹ * e * g⁻¹⁻¹)
    calc g⁻¹ * e * g⁻¹⁻¹ * x = g⁻¹ * (e * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * e) * g := by rw [hcomm]
      _ = x * (g⁻¹ * e * g⁻¹⁻¹) := by group
  obtain ⟨c, hcC, hcE⟩ := exists_conj_le_of_isSylowOf hQ hE₁C (hE.map _)
  refine ⟨c * g⁻¹, ?_, ?_⟩
  · have : (MulAut.conj (c * g⁻¹)).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom :=
      MonoidHom.ext fun _ => by simp [mul_assoc]
    rw [this, ← Subgroup.map_map]
    exact hcE
  · have hcomp : (MulAut.conj (c * g⁻¹)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj c).toMonoidHom :=
      MonoidHom.ext fun _ => by simp [mul_assoc]
    rw [hg, Subgroup.map_map, hcomp, MonoidHom.map_zpowers]
    have hcx : c * x * c⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hcC
    change Subgroup.zpowers (c * x * c⁻¹) = Subgroup.zpowers x
    rw [hcx]

private theorem u3_false_of_bad_conj_line {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G)
    (hc : PointConfig Typ G p P M x J)
    (hplane : ∃ A : Subgroup G, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ A ≤ u3S P x ∧
      ∀ s ∈ u3S P x, ∀ a ∈ A, s * a = a * s)
    (hcent : ∀ E F : Subgroup G, E ≤ u3S P x → IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
      IsPGroup 2 F → F ≤ Subgroup.centralizer ({x} : Set G) → E ≤ Subgroup.normalizer (F : Set G) →
      ∀ a ∈ E, ∀ f ∈ F, a * f = f * a) {D L₀ : Subgroup G}
    (hDS : D ≤ u3S P x) (hD : IsElemAbelian p D) (hL₀D : L₀ ≤ D)
    (hL₀bad : ⁅pCoreOf 2 M ⊓ Subgroup.centralizer (L₀ : Set G), D⁆ ≠ ⊥) {g : G}
    (hg : L₀ = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) : False := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 := hc.five
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core
  have hrank3 : CFSG.Open.pRank p (u3S P x) = 3 := hc.generic.2.2.2
  have hSM : u3S P x ≤ M := inf_le_left.trans hPM
  have hT₀2 : IsPGroup 2 (pCoreOf 2 M) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    u3f_le_normalizer_pCoreOf_two M
  generalize pCoreOf 2 M = T₀ at hL₀bad hT₀2 hMT₀
  obtain ⟨A₀, hU0el, hU0card, hU0S, hU0cent⟩ := hplane
  obtain ⟨E₃, hE₃S, hE₃el, hE₃card⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (u3S P x)
  have hE₃c : p ^ 3 ≤ Nat.card E₃ := by rw [hE₃card, hrank3]
  obtain ⟨E, hDE, hES, hEel, hE3⟩ :=
    exists_elemAbelian_sup hp hD hDS hU0el hU0card hU0S (fun a ha q hq => (hU0cent q hq a ha).symm)
      hE₃el hE₃S hE₃c
  have hEM : E ≤ M := hES.trans hSM
  have hEp : IsPGroup p E := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hEel
  have hDp : IsPGroup p D := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p D hD
  obtain ⟨A, hA⟩ : ∃ A : Subgroup G, A = T₀ ⊓ Subgroup.centralizer (L₀ : Set G) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = ⁅A, D⁆ := ⟨_, rfl⟩
  rw [← hA, ← hT] at hL₀bad
  have hEL : E ≤ Subgroup.centralizer (L₀ : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun l hl => (CFSG.Open.IsElemAbelian.comm hEel (hDE (hL₀D hl)) he)
  have hEA : E ≤ Subgroup.normalizer (A : Set G) := fun e he => by
    rw [hA]
    exact u3f_mem_normalizer_inf (hMT₀ (hEM he)) (u3f_mem_normalizer_centralizer_of_le (hEL he))
  have hDA : D ≤ Subgroup.normalizer (A : Set G) := fun d hd => hEA (hDE hd)
  have hED : E ≤ Subgroup.normalizer (D : Set G) := fun e he => Subgroup.centralizer_le_normalizer D
    (Subgroup.mem_centralizer_iff.mpr fun d hd => CFSG.Open.IsElemAbelian.comm hEel (hDE hd) he)
  have hA2 : IsPGroup 2 A := by rw [hA]; exact hT₀2.to_le inf_le_left
  have hTA : T ≤ A := by
    rw [hT]
    exact Subgroup.commutator_le.mpr fun a ha d hd => by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hDA hd) a⁻¹).mp (A.inv_mem ha)
      have h2 : a * d * a⁻¹ * d⁻¹ = a * (d * a⁻¹ * d⁻¹) := by group
      change a * d * a⁻¹ * d⁻¹ ∈ A
      rw [h2]
      exact A.mul_mem ha h1
  have hTT : ⁅T, D⁆ = T := by
    have hcop : Nat.Coprime (Nat.card D) (Nat.card A) := by
      obtain ⟨a, ha⟩ := hDp.exists_card_eq
      obtain ⟨b, hb⟩ := hA2.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent A := hA2.isNilpotent
    rw [hT]
    exact CFSG.RankThree.PartOne.HNB.commutator_double_eq_self_of_coprime_solvable D A hDA hcop
      inferInstance
  have hT2 : IsPGroup 2 T := hA2.to_le hTA
  have hTL : T ≤ Subgroup.centralizer (L₀ : Set G) := by
    refine hTA.trans ?_
    rw [hA]
    exact inf_le_right
  have hET : E ≤ Subgroup.normalizer (T : Set G) := fun e he => by
    rw [hT]
    exact u3f_mem_normalizer_commutator (hEA he) (hED he)
  obtain ⟨k, hkE, hkL⟩ := u3f_exists_conj_to_sylow hc.generic.2.2.1 hEp hEL hg
  obtain ⟨κ, hκ⟩ : ∃ κ : G →* G, κ = (MulAut.conj k).toMonoidHom := ⟨_, rfl⟩
  rw [← hκ] at hkE hkL
  have hκinj : Function.Injective κ := by rw [hκ]; exact (MulAut.conj k).injective
  have hTsC : T.map κ ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    have hxL : x ∈ L₀.map κ := hkL ▸ Subgroup.mem_zpowers x
    obtain ⟨l, hl, hlx⟩ := hxL
    rw [Subgroup.mem_centralizer_singleton_iff, ← hlx]
    have hlt := Subgroup.mem_centralizer_iff.mp (hTL ht) l hl
    calc κ t * κ l = κ (t * l) := (map_mul κ t l).symm
      _ = κ (l * t) := congrArg κ hlt.symm
      _ = κ l * κ t := map_mul κ l t
  have hEsel : IsElemAbelian p (E.map κ) := CFSG.Open.IsElemAbelian.map hEel κ
  have hEs3 : p ^ 3 ≤ Nat.card (E.map κ) := by
    rw [Subgroup.card_map_of_injective hκinj]
    exact hE3
  have hTs2 : IsPGroup 2 (T.map κ) := hT2.map κ
  have hTsEs : E.map κ ≤ Subgroup.normalizer ((T.map κ : Subgroup G) : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.le_normalizer_map κ ⟨e, hET he, rfl⟩
  have hcomm := hcent (E.map κ) (T.map κ) hkE hEsel hEs3 hTs2 hTsC hTsEs
  have hTsDs : ⁅T.map κ, D.map κ⁆ = T.map κ := by
    rw [← Subgroup.map_commutator, hTT]
  have hbot : ⁅T.map κ, D.map κ⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hcomm d (Subgroup.map_mono hDE hd) t ht
  rw [hbot] at hTsDs
  exact hL₀bad ((Subgroup.map_eq_bot_iff_of_injective T hκinj).mp hTsDs.symm)

private theorem u3_lemma33_S {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G)
    (hc : PointConfig Typ G p P M x J)
    (hplane : ∃ A : Subgroup G, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ A ≤ u3S P x ∧
      ∀ s ∈ u3S P x, ∀ a ∈ A, s * a = a * s)
    (hcent : ∀ E F : Subgroup G, E ≤ u3S P x → IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
      IsPGroup 2 F → F ≤ Subgroup.centralizer ({x} : Set G) → E ≤ Subgroup.normalizer (F : Set G) →
      ∀ a ∈ E, ∀ f ∈ F, a * f = f * a) {D : Subgroup G} (hDS : D ≤ u3S P x) (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (s : Finset (Subgroup G))
    (hs : ∀ A ∈ s, A ≤ D ∧ Nat.card A = p ∧
      ∃ g : G, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) : s.card < p := by
  classical
  by_contra hcard
  push Not at hcard
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 := hc.five
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core
  have hSM : u3S P x ≤ M := inf_le_left.trans hPM
  have hDM : D ≤ M := hDS.trans hSM
  have hT₀2 : IsPGroup 2 (pCoreOf 2 M) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    u3f_le_normalizer_pCoreOf_two M
  have hcop : p.Coprime (Nat.card (pCoreOf 2 M)) := by
    obtain ⟨b, hb⟩ := hT₀2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hC : ∀ d ∈ D, (∀ t ∈ pCoreOf 2 M, d * t = t * d) → d = 1 := by
    intro d hd hdc
    have hdT : d ∈ pCoreOf 2 M := hS.charTwo M hc.core.1.1
      ⟨hDM hd, Subgroup.mem_centralizer_iff.mpr fun t ht => (hdc t ht).symm⟩
    obtain ⟨k, hk⟩ := hT₀2 ⟨d, hdT⟩
    have h2 : orderOf d ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have hp' : orderOf d ∣ p := orderOf_dvd_of_pow_eq_one (hD.2 d hd)
    have hcoprime : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_one (hcoprime.gcd_eq_one ▸ Nat.dvd_gcd hp' h2))
  obtain ⟨L₁, L₂, hne, ⟨hL₁D, hL₁c, hL₁b⟩, ⟨hL₂D, hL₂c, hL₂b⟩⟩ :=
    exists_two_bad_lines hp hD hDcard (fun d hd => hMT₀ (hDM hd)) hcop hC
  have hkey : ∀ L ∈ s, ⁅pCoreOf 2 M ⊓ Subgroup.centralizer (L : Set G), D⁆ ≠ ⊥ → False :=
    fun L hL hbad => by
      obtain ⟨hLD, -, g, hg⟩ := hs L hL
      exact u3_false_of_bad_conj_line hS hc hplane hcent hDS hD hLD hbad hg
  by_cases h1 : L₁ ∈ s
  · exact hkey L₁ h1 hL₁b
  by_cases h2 : L₂ ∈ s
  · exact hkey L₂ h2 hL₂b
  have hcard' : (insert L₁ (insert L₂ s)).card = s.card + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne, h1]), Finset.card_insert_of_notMem h2]
  have := card_lines_le hp hDcard (insert L₁ (insert L₂ s)) (by
    intro L hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact ⟨hL₁D, hL₁c⟩
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact ⟨hL₂D, hL₂c⟩
    obtain ⟨hLD, hLc, -⟩ := hs L hL
    exact ⟨hLD, hLc⟩)
  omega

theorem lemma33_of_cent {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G)
    (hc : PointConfig Typ G p P M x J)
    (hplane : ∃ A : Subgroup G, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ A ≤ u3S P x ∧
      ∀ s ∈ u3S P x, ∀ a ∈ A, s * a = a * s)
    (hcent : ∀ E F : Subgroup G, E ≤ u3S P x → IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
      IsPGroup 2 F → F ≤ Subgroup.centralizer ({x} : Set G) → E ≤ Subgroup.normalizer (F : Set G) →
      ∀ a ∈ E, ∀ f ∈ F, a * f = f * a) : U3Lemma33 p x := by
  intro D hDC hD hDcard s hs
  classical
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, -, hcD⟩ := exists_conj_le_of_isSylowOf hc.generic.2.2.1 hDC
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p D hD)
  have hκinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hD'el : IsElemAbelian p (D.map (MulAut.conj c).toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hD _
  have hD'card : Nat.card (D.map (MulAut.conj c).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hκinj, hDcard]
  have h := u3_lemma33_S hS hc hplane hcent (D := D.map (MulAut.conj c).toMonoidHom) hcD hD'el hD'card
    (s.image (Subgroup.map (MulAut.conj c).toMonoidHom)) (by
      intro A hA
      obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hA₀D, hA₀c, g, hg⟩ := hs A₀ hA₀
      refine ⟨Subgroup.map_mono hA₀D, ?_, c * g, ?_⟩
      · rw [Subgroup.card_map_of_injective hκinj, hA₀c]
      · rw [hg, Subgroup.map_map]
        congr 1
        ext y
        simp [mul_assoc])
  rwa [Finset.card_image_of_injective _ (Subgroup.map_injective hκinj)] at h

theorem lemma33_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G) (hD1 : TheoremD1 G)
    (hSig : SignalizerTwoGroupKFact) (hc : PointConfig Typ G p P M x J) (hSE : TypeSE Typ p)
    (hdat : Lemma33Data p P x J) : U3Lemma33 p x :=
  lemma33_of_cent hS hc hdat.plane fun _ _ hEQ hE hE3 hF2 hFC hEF =>
    centralizes_two_group_gen hS hD1 hSig hc hSE hdat hEQ hE hE3 hF2 hFC hEF

theorem typeSE_u3 (p : ℕ) : TypeSE (fun p K _ => IsU3Pred p K) p := by
  intro K _ _ hK
  obtain ⟨q, hqp, hq1, hv, ⟨f⟩⟩ := hK
  exact ⟨Or.inr (Or.inl ⟨q, hqp, hq1, hv, ⟨f⟩⟩), TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩, ⟨f⟩⟩

theorem rank_le_of_nonabelian_card_p_cube {p : ℕ} [Fact p.Prime] {T : Subgroup G}
    (hTcard : Nat.card T = p ^ 3) (hTnab : ¬ IsMulCommutative T) (E : Subgroup G) (hET : E ≤ T)
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hdvd : Nat.card E ∣ p ^ 3 := by
    have := Subgroup.card_dvd_of_le hET
    rwa [hTcard] at this
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  by_cases hi3 : i = 3
  · exfalso
    have hTE : E = T := Subgroup.eq_of_le_of_card_ge hET (by rw [hTcard, hcard, hi3])
    apply hTnab
    rw [← hTE]
    exact hE.1
  · have : i ≤ 2 := by omega
    rw [hcard]
    exact Nat.pow_le_pow_right hp.pos this

theorem lemma33Data_of_fusionStruct {p : ℕ} [Fact p.Prime] {P : Sylow p G} {x : G} {J : Subgroup G}
    (hA : FusionStruct p P x J) : Lemma33Data p P x J := by
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := hA.T
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, -, hsup⟩ := hA.Z
  obtain ⟨hU0el, hU0card, hU0S, -, hU0cent, -, -⟩ := hA.U0
  exact ⟨hxJ, hTexp, rank_le_of_nonabelian_card_p_cube hTcard hTnab,
    ⟨Z, hZcyc, hxZ, hZS, hZT, hsup⟩, ⟨u3U0 P x J, hU0el, hU0card, hU0S, hU0cent⟩⟩

theorem u3_lemma33 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSig : SignalizerTwoGroupKFact) (hc : U3Config G p P M x J) : U3Lemma33 p x := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  exact lemma33_gen hS hD1 hSig (pointConfig_of_u3 hc) (typeSE_u3 p)
    (lemma33Data_of_fusionStruct ⟨u3_T_structure hc, u3_S_decomp hc, u3U0_facts hc⟩)

theorem u3f_lines_injOn {p : ℕ} [Fact p.Prime] {D : Subgroup G} (hD : IsElemAbelian p D)
    {a b : G} (haD : a ∈ D) (hbD : b ∈ D) (hb1 : b ≠ 1) (hab : a ∉ Subgroup.zpowers b) :
    Set.InjOn (fun i : ℕ => Subgroup.zpowers (b ^ i * a)) (Set.Iio p) := by
  have hp : p.Prime := Fact.out
  have hbo : orderOf b = p := orderOf_eq_prime (hD.2 b hbD) hb1
  have hne : ∀ i : ℕ, b ^ i * a ≠ 1 := by
    intro i h
    apply hab
    have : a = (b ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) i)
  have hord : ∀ i : ℕ, orderOf (b ^ i * a) = p := fun i =>
    orderOf_eq_prime (hD.2 _ (D.mul_mem (D.pow_mem hbD i) haD)) (hne i)
  intro i hi j hj h
  simp only [Set.mem_Iio] at hi hj
  simp only at h
  set u : G := b ^ i * a with hu
  set v : G := b ^ j * a with hv
  have hvu : v ∈ Subgroup.zpowers u := h ▸ Subgroup.mem_zpowers v
  have hw : b ^ j * (b ^ i)⁻¹ ∈ Subgroup.zpowers u := by
    have : b ^ j * (b ^ i)⁻¹ = v * u⁻¹ := by
      rw [hu, hv, mul_inv_rev]
      group
    rw [this]
    exact Subgroup.mul_mem _ hvu (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
  have hwb : b ^ j * (b ^ i)⁻¹ ∈ Subgroup.zpowers b :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) j)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) i))
  have hw1 : b ^ j * (b ^ i)⁻¹ = 1 := by
    by_contra hw1
    have hwo : orderOf (b ^ j * (b ^ i)⁻¹) = p := by
      refine orderOf_eq_prime ?_ hw1
      exact hD.2 _ (D.mul_mem (D.pow_mem hbD j) (D.inv_mem (D.pow_mem hbD i)))
    have hzw : Subgroup.zpowers (b ^ j * (b ^ i)⁻¹) = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwb) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hbo])
    have hbw : b ∈ Subgroup.zpowers u := by
      have : b ∈ Subgroup.zpowers (b ^ j * (b ^ i)⁻¹) := hzw ▸ Subgroup.mem_zpowers b
      exact Subgroup.zpowers_le.mpr hw this
    have hbu : Subgroup.zpowers u = Subgroup.zpowers b :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbw) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord i, hbo])).symm
    apply hab
    rw [← hbu]
    have : a = (b ^ i)⁻¹ * u := by rw [hu]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hbw i))
      (Subgroup.mem_zpowers u)
  have : b ^ j = b ^ i := by
    have := mul_inv_eq_one.mp hw1
    exact this
  rw [← hbo] at hi hj
  exact (pow_injOn_Iio_orderOf hj hi this).symm

theorem u3f_false_of_lines {p : ℕ} [Fact p.Prime] {x : G} (hL33 : U3Lemma33 p x)
    {D : Subgroup G} (hDC : D ≤ Subgroup.centralizer ({x} : Set G)) (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) {a b : G} (haD : a ∈ D) (hbD : b ∈ D) (hb1 : b ≠ 1)
    (hab : a ∉ Subgroup.zpowers b)
    (hconj : ∀ i : ℕ, i < p → ∃ g : G,
      Subgroup.zpowers (b ^ i * a) = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) :
    False := by
  classical
  have hp : p.Prime := Fact.out
  have hne : ∀ i : ℕ, b ^ i * a ≠ 1 := by
    intro i h
    apply hab
    have : a = (b ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) i)
  have hlt := hL33 D hDC hD hDcard ((Finset.range p).image (fun i : ℕ => Subgroup.zpowers (b ^ i * a)))
    (by
      intro A hA
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      have hmem : b ^ i * a ∈ D := D.mul_mem (D.pow_mem hbD i) haD
      refine ⟨Subgroup.zpowers_le.mpr hmem, ?_, hconj i (Finset.mem_range.mp hi)⟩
      rw [Nat.card_zpowers, orderOf_eq_prime (hD.2 _ hmem) (hne i)])
  rw [Finset.card_image_of_injOn (fun i hi j hj h =>
    u3f_lines_injOn hD haD hbD hb1 hab
      (show i < p from Finset.mem_range.mp (Finset.mem_coe.mp hi))
      (show j < p from Finset.mem_range.mp (Finset.mem_coe.mp hj)) h), Finset.card_range] at hlt
  exact lt_irrefl p hlt

private theorem u3f_commutator_S {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J) (hA : FusionStruct p P x J) :
    ⁅u3S P x, u3S P x⁆ = u3ZT P x J := by
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := hA.T
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := hA.Z
  obtain ⟨hU0el, hU0card, hU0S, hxU0, hU0cent, hZTcard, hZTJ⟩ := hA.U0
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative Z := IsCyclic.isMulCommutative
  have hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' =>
    congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : Z) ⟨z', hz'⟩)
  have key1 : ∀ t z b : G, z * b = b * z →
      (t * z) * b * (t * z)⁻¹ * b⁻¹ = t * b * t⁻¹ * b⁻¹ := by
    intro t z b h
    calc (t * z) * b * (t * z)⁻¹ * b⁻¹ = t * (z * b) * z⁻¹ * t⁻¹ * b⁻¹ := by group
      _ = t * (b * z) * z⁻¹ * t⁻¹ * b⁻¹ := by rw [h]
      _ = t * b * t⁻¹ * b⁻¹ := by group
  have key2 : ∀ t b z : G, z * t⁻¹ = t⁻¹ * z →
      t * (b * z) * t⁻¹ * (b * z)⁻¹ = t * b * t⁻¹ * b⁻¹ := by
    intro t b z h
    calc t * (b * z) * t⁻¹ * (b * z)⁻¹ = t * b * (z * t⁻¹) * z⁻¹ * b⁻¹ := by group
      _ = t * b * (t⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h]
      _ = t * b * t⁻¹ * b⁻¹ := by group
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨t₁, ht₁, z₁, hz₁, rfl⟩ := fus_exists_mul_of_sup_eq hZT hsup a ha
    obtain ⟨t₂, ht₂, z₂, hz₂, rfl⟩ := fus_exists_mul_of_sup_eq hZT hsup b hb
    have h1 : z₁ * t₂ = t₂ * z₁ := hZT z₁ hz₁ t₂ ht₂
    have h2 : z₁ * z₂ = z₂ * z₁ := hZZ z₁ hz₁ z₂ hz₂
    have h3 : z₂ * t₁⁻¹ = t₁⁻¹ * z₂ := hZT z₂ hz₂ t₁⁻¹ ((u3T P x J).inv_mem ht₁)
    have h4 : z₁ * (t₂ * z₂) = (t₂ * z₂) * z₁ := by
      rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
    have hc12 := commutator_mem_inf_centralizer hTcard hTnab ht₁ ht₂
    change (t₁ * z₁) * (t₂ * z₂) * (t₁ * z₁)⁻¹ * (t₂ * z₂)⁻¹ ∈ u3ZT P x J
    rw [key1 t₁ z₁ _ h4, key2 t₁ t₂ z₂ h3]
    exact hc12
  · obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ u3T P x J, ∃ b ∈ u3T P x J, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact hTnab ⟨⟨fun a b => Subtype.ext (hcon a a.2 b b.2)⟩⟩
    have hc12 := commutator_mem_inf_centralizer hTcard hTnab ha hb
    have hc1 : a * b * a⁻¹ * b⁻¹ ≠ 1 := by
      intro h
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h))
    have hcp : (a * b * a⁻¹ * b⁻¹) ^ p = 1 := hTexp _ hc12.1
    have hcord : orderOf (a * b * a⁻¹ * b⁻¹) = p := orderOf_eq_prime hcp hc1
    have hZTeq : Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) = u3ZT P x J :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc12) (by
        rw [Nat.card_zpowers, hcord, hZTcard])
    rw [← hZTeq, Subgroup.zpowers_le]
    have haS : a ∈ u3S P x := (inf_le_left : u3T P x J ≤ u3S P x) ha
    have hbS : b ∈ u3S P x := (inf_le_left : u3T P x J ≤ u3S P x) hb
    exact Subgroup.commutator_mem_commutator haS hbS

private theorem u3f_not_conj_ZT {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J) (hA : FusionStruct p P x J) {g : G}
    (hg : g * x * g⁻¹ ∈ u3ZT P x J) : False := by
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := hA.T
  obtain ⟨hU0el, hU0card, hU0S, hxU0, hU0cent, hZTcard, hZTJ⟩ := hA.U0
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hZTU0 : u3ZT P x J ≤ u3U0 P x J := le_sup_left
  have hSC : u3S P x ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  obtain ⟨y, hy⟩ : ∃ y : G, y = g * x * g⁻¹ := ⟨_, rfl⟩
  rw [← hy] at hg
  have hK : Subgroup.centralizer ({y} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro hz
      refine ⟨g⁻¹ * z * g, ?_, by simp [mul_assoc]⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : z * (g * x * g⁻¹) = (g * x * g⁻¹) * z := by rw [← hy]; exact hz
      calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [h1]
        _ = x * (g⁻¹ * z * g) := by group
    · rintro ⟨c, hc', rfl⟩
      have hc'' : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc'
      rw [hy]
      show g * c * g⁻¹ * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * c * g⁻¹)
      calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
        _ = g * (x * c) * g⁻¹ := by rw [hc'']
        _ = (g * x * g⁻¹) * (g * c * g⁻¹) := by group
  have hSK : u3S P x ≤ Subgroup.centralizer ({y} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hU0cent s hs y (hZTU0 hg))
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf p (u3S P x) (Subgroup.centralizer ({x} : Set G)) :=
    hc.generic.2.2.1
  have hcardK : Nat.card (Subgroup.centralizer ({y} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [hK]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hSsylK : CFSG.ABGLocalTools.IsSylowOf p (u3S P x) (Subgroup.centralizer ({y} : Set G)) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hSK ?_
    rw [hcardK]
    exact hSsyl.card_eq
  have hS'K : (u3S P x).map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [hK]
    exact Subgroup.map_mono hSC
  have hS'p : IsPGroup p ((u3S P x).map (MulAut.conj g).toMonoidHom) := hSsyl.isPGroup.map _
  obtain ⟨c, hcK, hcS⟩ := exists_conj_le_of_isSylowOf hSsylK hS'K hS'p
  have hcardS : Nat.card (((u3S P x).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj c).toMonoidHom) = Nat.card (u3S P x) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hγS : ((u3S P x).map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      u3S P x := Subgroup.eq_of_le_of_card_ge hcS (le_of_eq hcardS.symm)
  have hconjcomp : (MulAut.conj (c * g)).toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp (MulAut.conj g).toMonoidHom :=
    MonoidHom.ext fun _ => by simp [mul_assoc]
  have hγmap : (u3S P x).map (MulAut.conj (c * g)).toMonoidHom = u3S P x := by
    rw [hconjcomp, ← Subgroup.map_map]
    exact hγS
  have hγN : (c * g) ∈ Subgroup.normalizer ((u3S P x : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hγmap
  have hγx : c * g * x * (c * g)⁻¹ = y := by
    have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hcK
    calc c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ := by group
      _ = c * y * c⁻¹ := by rw [hy]
      _ = y := by rw [hcy]; group
  have hyS' : y ∈ ⁅u3S P x, u3S P x⁆ := by
    rw [u3f_commutator_S hc hA]
    exact hg
  have hγN' := u3f_mem_normalizer_commutator hγN hγN
  have hxS' : x ∈ ⁅u3S P x, u3S P x⁆ :=
    (Subgroup.mem_normalizer_iff.mp hγN' x).mpr (by rw [hγx]; exact hyS')
  rw [u3f_commutator_S hc hA] at hxS'
  exact hxJ (hZTJ hxS')

private theorem u3f_shear {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J) (hA : FusionStruct p P x J) (hL33 : U3Lemma33 p x) {g : G}
    (hgS : g * x * g⁻¹ ∈ u3S P x) : g * x * g⁻¹ ∈ u3U0 P x J := by
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := hA.T
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := hA.Z
  obtain ⟨hU0el, hU0card, hU0S, hxU0, hU0cent, hZTcard, hZTJ⟩ := hA.U0
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  have hZTU0 : u3ZT P x J ≤ u3U0 P x J := le_sup_left
  have hSC : u3S P x ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hZTcent : ∀ s ∈ u3S P x, ∀ w ∈ u3ZT P x J, s * w = w * s := fun s hs w hw =>
    hU0cent s hs w (hZTU0 hw)
  by_contra hyU0
  obtain ⟨y, hy⟩ : ∃ y : G, y = g * x * g⁻¹ := ⟨_, rfl⟩
  rw [← hy] at hgS hyU0
  have hyp : y ^ p = 1 := by
    rw [hy, conj_pow, hxp]
    group
  obtain ⟨t, ht, z, hz, hytz⟩ := fus_exists_mul_of_sup_eq hZT hsup y hgS
  have hzp : z ^ p = 1 := by
    have hcomm : Commute t z := (hZT z hz t ht).symm
    have h := hyp
    rw [hytz, hcomm.mul_pow, hTexp t ht, one_mul] at h
    exact h
  have hzx : z ∈ Subgroup.zpowers x :=
    fus_mem_zpowers_of_isCyclic_of_pow_prime hZcyc hxZ hz hx1 hxp hzp
  have htZT : t ∉ u3ZT P x J := fun h =>
    hyU0 (by rw [hytz]; exact Subgroup.mul_mem_sup h hzx)
  have htc : t ∉ Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G) := fun h => htZT ⟨ht, h⟩
  obtain ⟨s, hsT, hst⟩ : ∃ s ∈ u3T P x J, s * t ≠ t * s := by
    by_contra hcon
    push Not at hcon
    exact htc (Subgroup.mem_centralizer_iff.mpr hcon)
  obtain ⟨w, hw⟩ : ∃ w : G, w = s * t * s⁻¹ * t⁻¹ := ⟨_, rfl⟩
  have hwZT : w ∈ u3ZT P x J := by
    rw [hw]
    exact commutator_mem_inf_centralizer hTcard hTnab hsT ht
  have hw1 : w ≠ 1 := by
    intro h
    rw [hw] at h
    exact hst (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h))
  have hsS : s ∈ u3S P x := hTS hsT
  have hzs : z * s⁻¹ = s⁻¹ * z := hZT z hz s⁻¹ ((u3T P x J).inv_mem hsT)
  have hsy : s * y * s⁻¹ = w * y := by
    calc s * y * s⁻¹ = s * (t * z) * s⁻¹ := by rw [hytz]
      _ = s * t * (z * s⁻¹) := by group
      _ = s * t * (s⁻¹ * z) := by rw [hzs]
      _ = (s * t * s⁻¹ * t⁻¹) * (t * z) := by group
      _ = w * y := by rw [hw, hytz]
  have hsw : Commute s w := hZTcent s hsS w hwZT
  have hpow : ∀ i : ℕ, s ^ i * y * (s ^ i)⁻¹ = w ^ i * y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h1 : s * w ^ i * s⁻¹ = w ^ i := by
        rw [(hsw.pow_right i).eq]
        group
      calc s ^ (i + 1) * y * (s ^ (i + 1))⁻¹ = s * (s ^ i * y * (s ^ i)⁻¹) * s⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
        _ = s * (w ^ i * y) * s⁻¹ := by rw [ih]
        _ = (s * w ^ i * s⁻¹) * (s * y * s⁻¹) := by group
        _ = w ^ (i + 1) * y := by rw [h1, hsy, pow_succ, mul_assoc]
  have hyZT : y ∉ u3ZT P x J := fun h => hyU0 (hZTU0 h)
  have hcommD : ∀ e ∈ u3ZT P x J, e * y = y * e := fun e he => (hZTcent y hgS e he).symm
  have hDcard : Nat.card ↥(u3ZT P x J ⊔ Subgroup.zpowers y) = p ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (u3ZT P x J) hyp hyZT hcommD, hZTcard]
    ring
  have hZTel : IsElemAbelian p (u3ZT P x J) := hU0el.mono hZTU0
  have hyel : IsElemAbelian p (Subgroup.zpowers y) := CFSG.Open.isElemAbelian_zpowers hyp
  have hcommD' : u3ZT P x J ≤ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommD e he)
  have hDel : IsElemAbelian p (u3ZT P x J ⊔ Subgroup.zpowers y) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hZTel hyel hcommD'
  have hDC : u3ZT P x J ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (hZTU0.trans (hU0S.trans hSC)) (Subgroup.zpowers_le.mpr (hSC hgS))
  have haD : y ∈ u3ZT P x J ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hbD : w ∈ u3ZT P x J ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left hwZT
  have hab : y ∉ Subgroup.zpowers w := fun h => hyZT (Subgroup.zpowers_le.mpr hwZT h)
  refine u3f_false_of_lines hL33 hDC hDel hDcard haD hbD hw1 hab (fun i _ => ⟨s ^ i * g, ?_⟩)
  rw [MonoidHom.map_zpowers]
  show Subgroup.zpowers (w ^ i * y) = Subgroup.zpowers ((s ^ i * g) * x * (s ^ i * g)⁻¹)
  have : (s ^ i * g) * x * (s ^ i * g)⁻¹ = s ^ i * y * (s ^ i)⁻¹ := by
    rw [hy]
    group
  rw [this, hpow i]

private theorem u3f_wc_S {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J) (hA : FusionStruct p P x J) (hTor : TypeTorusLift p P x J)
    (hL33 : U3Lemma33 p x) :
    ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ u3S P x →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
  intro g hg
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := hA.T
  obtain ⟨hU0el, hU0card, hU0S, hxU0, hU0cent, hZTcard, hZTJ⟩ := hA.U0
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hZTU0 : u3ZT P x J ≤ u3U0 P x J := le_sup_left
  have hxU0' : Subgroup.zpowers x ≤ u3U0 P x J := le_sup_right
  have hSC : u3S P x ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  have hyS : g * x * g⁻¹ ∈ u3S P x := hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
  have hyU0 := u3f_shear hc hA hL33 hyS
  obtain ⟨y, hy⟩ : ∃ y : G, y = g * x * g⁻¹ := ⟨_, rfl⟩
  rw [← hy] at hyS hyU0
  have hmap : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers y := by
    rw [MonoidHom.map_zpowers, hy]
    rfl
  rw [hmap]
  have hyp : y ^ p = 1 := by
    rw [hy, conj_pow, hxp]
    group
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    rw [hy] at h
    have : g * x = g := mul_inv_eq_one.mp h
    exact mul_eq_left.mp this
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  have hcommx : ∀ z ∈ Subgroup.zpowers x, ∀ t ∈ u3ZT P x J, z * t = t * z := by
    intro z hz t ht
    have hzS : z ∈ u3S P x := by
      have : Subgroup.zpowers x ≤ u3S P x := Subgroup.zpowers_le.mpr (hU0S hxU0)
      exact this hz
    exact hU0cent z hzS t (hZTU0 ht)
  obtain ⟨t, ht, z', hz', hytz⟩ := fus_exists_mul_of_sup_eq hcommx
    (rfl : u3ZT P x J ⊔ Subgroup.zpowers x = u3U0 P x J) y hyU0
  by_cases ht1 : t = 1
  ·
    have hyx : y ∈ Subgroup.zpowers x := by
      rw [hytz, ht1, one_mul]
      exact hz'
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyx) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hxo])
  exfalso
  by_cases hz1 : z' = 1
  ·
    apply u3f_not_conj_ZT hc hA (g := g)
    rw [← hy, hytz, hz1, mul_one]
    exact ht
  have hz'U0 : z' ∈ u3U0 P x J := hxU0' hz'
  have hz'o : orderOf z' = p := orderOf_eq_prime (hU0el.2 z' hz'U0) hz1
  have hz'x : Subgroup.zpowers z' = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz') (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hz'o, hxo])
  have htU0 : t ∈ u3U0 P x J := hZTU0 ht
  have hab : z' ∉ Subgroup.zpowers t := by
    intro hmem
    have hz'J : z' ∈ J := (Subgroup.zpowers_le.mpr (hZTJ ht)) hmem
    have hxz' : x ∈ Subgroup.zpowers z' := hz'x ▸ Subgroup.mem_zpowers x
    exact hxJ ((Subgroup.zpowers_le.mpr hz'J) hxz')
  refine u3f_false_of_lines hL33 (hU0S.trans hSC) hU0el hU0card hz'U0 htU0 ht1 hab ?_
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · refine ⟨1, ?_⟩
    rw [pow_zero, one_mul, hz'x]
    ext u
    simp
  · have hk : ¬ (p : ℤ) ∣ (i : ℤ) := by
      intro hdvd
      have := Nat.le_of_dvd hipos (Int.natCast_dvd_natCast.mp hdvd)
      omega
    obtain ⟨h, hhJ, hhtz⟩ := hTor t ht.1 ht.2 ht1 (i : ℤ) hk
    rw [zpow_natCast] at hhtz
    have hhC : h ∈ Subgroup.centralizer ({x} : Set G) := hc.le_cent hhJ
    have hxh : x ∈ Subgroup.centralizer ({h} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hhC).symm
    have hz'h : z' * h = h * z' :=
      Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hxh) hz')
    refine ⟨h * g, ?_⟩
    rw [MonoidHom.map_zpowers]
    show Subgroup.zpowers (t ^ i * z') = Subgroup.zpowers ((h * g) * x * (h * g)⁻¹)
    have : (h * g) * x * (h * g)⁻¹ = t ^ i * z' := by
      calc (h * g) * x * (h * g)⁻¹ = h * (g * x * g⁻¹) * h⁻¹ := by group
        _ = h * (t * z') * h⁻¹ := by rw [← hy, hytz]
        _ = (h * t * h⁻¹) * (h * z' * h⁻¹) := by group
        _ = t ^ i * z' := by
          rw [hhtz, ← hz'h]
          group
    rw [this]

theorem fusion_P_le_C_of_fix {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J)
    (hfix : ∀ y : G, y ∈ (P : Subgroup G) → y ∈ Subgroup.normalizer ((u3S P x : Subgroup G) : Set G) →
      y * x * y⁻¹ ∈ Subgroup.zpowers x) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
  by_contra hPC
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hSP : u3S P x ≤ (P : Subgroup G) := inf_le_left
  let IP : Subgroup P := (u3S P x).subgroupOf (P : Subgroup G)
  have hIPne : IP ≠ ⊤ := by
    intro htop
    apply hPC
    intro y hyP
    have hyIP : (⟨y, hyP⟩ : P) ∈ IP := by
      rw [htop]
      trivial
    exact (Subgroup.mem_subgroupOf.mp hyIP).2
  have hIPlt : IP < ⊤ := lt_of_le_of_ne le_top hIPne
  have : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  have hlt : IP < Subgroup.normalizer (IP : Set P) := hnc IP hIPlt
  obtain ⟨y, hyN, hynotIP⟩ := SetLike.exists_of_lt hlt
  have hyNorm : (y : G) ∈ Subgroup.normalizer ((u3S P x : Subgroup G) : Set G) := by
    have hysub : y ∈ (Subgroup.normalizer ((u3S P x : Subgroup G) : Set G)).subgroupOf
        (P : Subgroup G) := by
      rw [Subgroup.subgroupOf_normalizer_eq hSP]
      exact hyN
    exact Subgroup.mem_subgroupOf.mp hysub
  have hynotS : (y : G) ∉ u3S P x := fun h => hynotIP (Subgroup.mem_subgroupOf.mpr h)
  have hyx : (y : G) * x * (y : G)⁻¹ ∈ Subgroup.zpowers x := hfix (y : G) y.2 hyNorm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x ^ k = (y : G) * x * (y : G)⁻¹ := Subgroup.mem_zpowers_iff.mp hyx
  have hpow : ∀ n : ℕ, (y : G) ^ n * x * ((y : G) ^ n)⁻¹ = x ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (y : G) ^ (n + 1) * x * ((y : G) ^ (n + 1))⁻¹
          = (y : G) * ((y : G) ^ n * x * ((y : G) ^ n)⁻¹) * (y : G)⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
        _ = (y : G) * x ^ (k ^ n) * (y : G)⁻¹ := by rw [ih]
        _ = ((y : G) * x * (y : G)⁻¹) ^ (k ^ n) := conj_zpow.symm
        _ = (x ^ k) ^ (k ^ n) := by rw [hk]
        _ = x ^ (k ^ (n + 1)) := by rw [← zpow_mul, pow_succ']
  obtain ⟨m, hm⟩ := P.isPGroup' y
  have hym : (y : G) ^ (p ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hxpow : x ^ (k ^ (p ^ m)) = x := by
    have := hpow (p ^ m)
    rwa [hym, one_mul, inv_one, mul_one, eq_comm] at this
  have hdvd : (p : ℤ) ∣ k ^ (p ^ m) - 1 := by
    have h1 : x ^ (k ^ (p ^ m) - 1) = 1 := by
      rw [zpow_sub_one, hxpow, mul_inv_cancel]
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hxo] at h2
  have hk1 : (k : ZMod p) = 1 := by
    have h3 : ((k ^ (p ^ m) - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at h3
    rw [ZMod.pow_card_pow] at h3
    exact sub_eq_zero.mp h3
  have hdvd' : (p : ℤ) ∣ k - 1 := by
    have h4 : ((k - 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hk1]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h4
  have hxk : x ^ k = x := by
    have h5 : x ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rwa [hxo])
    rw [zpow_sub_one] at h5
    exact mul_inv_eq_one.mp h5
  have hyC : (y : G) * x = x * (y : G) := by
    rw [hxk] at hk
    exact mul_inv_eq_iff_eq_mul.mp hk.symm
  exact hynotS ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyC⟩

theorem u3f_P_le_C {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J)
    (hwc : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ u3S P x →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
  refine fusion_P_le_C_of_fix hc fun y _ hyNorm => ?_
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hyxS : y * x * y⁻¹ ∈ u3S P x := (Subgroup.mem_normalizer_iff.mp hyNorm x).mp hxS
  have hle : (Subgroup.zpowers x).map (MulAut.conj y).toMonoidHom ≤ u3S P x := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr hyxS
  have heq := hwc y hle
  have : y * x * y⁻¹ ∈ (Subgroup.zpowers x).map (MulAut.conj y).toMonoidHom :=
    ⟨x, Subgroup.mem_zpowers x, rfl⟩
  rwa [heq] at this

theorem fusion_of_wc_S {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J)
    (hwc : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ u3S P x →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G) := by
  have hPC := u3f_P_le_C hc hwc
  exact ⟨hPC, fun g hg => hwc g (hg.trans (le_inf le_rfl hPC : (P : Subgroup G) ≤ u3S P x))⟩

theorem fusion_of_lemma33_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J) (hA : FusionStruct p P x J) (hTor : TypeTorusLift p P x J)
    (hL33 : U3Lemma33 p x) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G) :=
  fusion_of_wc_S hc (u3f_wc_S hc hA hTor hL33)

theorem fusion_core_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G) (hD1 : TheoremD1 G)
    (hSig : SignalizerTwoGroupKFact) (hc : PointConfig Typ G p P M x J) (hSE : TypeSE Typ p)
    (hA : FusionStruct p P x J) (hTor : TypeTorusLift p P x J) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  exact fusion_of_lemma33_gen hc hA hTor
    (lemma33_gen hS hD1 hSig hc hSE (lemma33Data_of_fusionStruct hA))

theorem u3_fusion_of_lemma33 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : U3Config G p P M x J) (hL33 : U3Lemma33 p x) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  exact fusion_of_lemma33_gen (pointConfig_of_u3 hc)
    ⟨u3_T_structure hc, u3_S_decomp hc, u3U0_facts hc⟩
    (fun c hcT hcZ hc1 k hk => by
      obtain ⟨h, hhJ, -, hh⟩ := u3_torus_lift hc hcT hcZ hc1 k hk
      exact ⟨h, hhJ, hh⟩) hL33

theorem u3_fusion_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSig : SignalizerTwoGroupKFact) (hc : U3Config G p P M x J) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G) :=
  u3_fusion_of_lemma33 hS hD1 hU0 hc (u3_lemma33 hS hD1 hU0 hSig hc)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
