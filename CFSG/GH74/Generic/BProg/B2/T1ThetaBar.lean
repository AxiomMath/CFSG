module

public import CFSG.GH74.Generic.BProg.Stage2Defs
import CFSG.GH74.Generic.BProg.B2.T1Basic
import CFSG.GH74.Generic.BProg.B2.U0Gen
import CFSG.GH74.Generic.BProg.B2.Lemma83Bar
import CFSG.GH74.Generic.BProg.B1.Lift0
import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.GH74.Generic.BProg.Theta32

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

namespace T1ThetaBar

abbrev rho (M : Subgroup G) : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M)

theorem odd_card_pPrimeCore (M : Subgroup G) : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
  Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M))

omit [Finite G] in
theorem isElementaryAbelian_barIn {S : Subgroup G} (hSM : S ≤ M)
    (hS : CFSG.IsElementaryAbelian 2 ↥S) : CFSG.IsElementaryAbelian 2 ↥(barIn M S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS
  have : CFSG.IsElementaryAbelian 2 ↥(S.subgroupOf M) := CFSG.IsElementaryAbelian.subgroupOf hSM
  exact CFSG.IsElementaryAbelian.map _

theorem A_le_normalizer_thetaHalf (hs : Stage2Setup G x K A M P Q) :
    A ≤ normalizer (thetaHalf 1 A : Set G) := by
  have hAe3 : IsE 3 ⊤ A := isE3_of_isSource2 hs.src
  have hbal := hs.reg.1
  have hr : 3 ≤ pRank 2 ↥A := hAe3.2.2
  exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2
    ⟨le_rfl, hAe3.2.1, by omega⟩)

theorem centralizer_zpowers_eq {R : Type*} [Group R] (r : R) :
    centralizer ((zpowers r : Subgroup R) : Set R) = centralizer ({r} : Set R) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem barIn_pPrimeCoreOf_centralizer_le {d : ↥M} (hd : IsPGroup 2 ↥(zpowers d)) :
    barIn M (pPrimeCoreOf 2 (centralizer ({(d : G)} : Set G))) ≤
      pPrimeCoreOf 2 (centralizer ({rho M d} : Set (Mbar M))) := by
  refine CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf ?_ ?_
    (Nat.coprime_two_left.2 (Lemma83Bar.odd_card_barIn (TwoThin.card_pPrimeCoreOf_odd _)))
  · rintro _ ⟨y, hy, rfl⟩
    have hyC : (y : G) ∈ centralizer ({(d : G)} : Set G) :=
      TwoThin.pPrimeCoreOf_le _ (show (y : G) ∈ pPrimeCoreOf 2 (centralizer ({(d : G)} : Set G))
        from hy)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg (rho M) (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hyC))
  · intro c hc
    have hcent := B1.map_centralizer_eq_centralizer_map_of_isPGroup (pPrimeCore 2 ↥M)
      (odd_card_pPrimeCore M) hd
    have hc' : c ∈ (centralizer ((zpowers d : Subgroup ↥M) : Set ↥M)).map (rho M) := by
      rw [hcent, MonoidHom.map_zpowers, centralizer_zpowers_eq]
      exact hc
    obtain ⟨g, hg, rfl⟩ := hc'
    rw [centralizer_zpowers_eq] at hg
    have hgC : (g : G) ∈ centralizer ({(d : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg))
    exact Lemma83Bar.mk_mem_normalizer_barIn
      (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hgC))

end T1ThetaBar

theorem thetaHalf_le_M (hs : Stage2Setup G x K A M P Q) : thetaHalf 1 A ≤ M :=
  le_of_inU0_of_odd (inU0_A hs) hs.reg.2.2 (T1ThetaBar.A_le_normalizer_thetaHalf hs)

theorem thetaBar_data (hs : Stage2Setup G x K A M P Q) :
    CFSG.IsElementaryAbelian 2 ↥(barIn M A) ∧ pRank 2 ↥(barIn M A) = 3 ∧
      Odd (Nat.card ↥(barIn M (thetaHalf 1 A))) ∧
      barIn M A ≤ normalizer ((barIn M (thetaHalf 1 A) : Subgroup (Mbar M)) : Set (Mbar M)) ∧
      ∀ E : Subgroup (Mbar M), E ≤ barIn M A → pRank 2 ↥(barIn M A) - 1 ≤ pRank 2 ↥E →
        centralizer (E : Set (Mbar M)) ≤
          normalizer ((barIn M (thetaHalf 1 A) : Subgroup (Mbar M)) : Set (Mbar M)) := by
  obtain ⟨-, hAel, hAcard, -⟩ := hs.src
  have hAM : A ≤ M := (inU0_A hs).1.1
  have hAe3 : IsE 3 ⊤ A := isE3_of_isSource2 hs.src
  have hbal := hs.reg.1
  have hApg : IsPGroup 2 ↥A := CFSG.IsElementaryAbelian.isPGroup 2 ↥A
  have hAN := T1ThetaBar.A_le_normalizer_thetaHalf hs
  have hAbel : CFSG.IsElementaryAbelian 2 ↥(barIn M A) :=
    T1ThetaBar.isElementaryAbelian_barIn hAM hAel
  have hAr : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
  have hAbrank : pRank 2 ↥(barIn M A) = 3 := (Lemma83Bar.pRank_barIn hAM hApg).trans hAr
  refine ⟨hAbel, hAbrank, Lemma83Bar.odd_card_barIn hs.reg.2.2, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Lemma83Bar.mk_mem_normalizer_barIn (hAN (show (a : G) ∈ A from ha))
  · intro E hEA hEr c hc
    have hEr2 : 2 ≤ pRank 2 ↥E := by omega
    have hA₀p : IsPGroup 2 ↥(A.subgroupOf M) := hApg.comap_subtype
    obtain ⟨E₀, hE₀le, hE₀map⟩ : ∃ E₀ : Subgroup ↥M, E₀ ≤ A.subgroupOf M ∧
        E₀.map (T1ThetaBar.rho M) = E := by
      refine ⟨(A.subgroupOf M) ⊓ E.comap (T1ThetaBar.rho M), inf_le_left, ?_⟩
      apply le_antisymm
      · rintro _ ⟨m, ⟨-, hm⟩, rfl⟩
        exact hm
      · intro e he
        obtain ⟨m, hm, hme⟩ := hEA he
        exact ⟨m, ⟨hm, Subgroup.mem_comap.2 (by rw [hme]; exact he)⟩, hme⟩
    subst hE₀map
    have hE₀p : IsPGroup 2 ↥E₀ := hA₀p.to_le hE₀le
    have hE'A : E₀.map M.subtype ≤ A := by
      rintro _ ⟨m, hm, rfl⟩
      exact hE₀le hm
    have hE'el : CFSG.IsElementaryAbelian 2 ↥(E₀.map M.subtype) :=
      Th2Sig6.isElementaryAbelian_of_le hAel hE'A
    have hE'r : 2 ≤ pRank 2 ↥(E₀.map M.subtype) := by
      have hbar : barIn M (E₀.map M.subtype) = E₀.map (T1ThetaBar.rho M) := by
        have : (E₀.map M.subtype).subgroupOf M = E₀ :=
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective E₀
        unfold barIn
        rw [this]
      rw [← Lemma83Bar.pRank_barIn (Subgroup.map_subtype_le E₀) (hE₀p.map M.subtype), hbar]
      exact hEr2
    have hcent := B1.map_centralizer_eq_centralizer_map_of_isPGroup (pPrimeCore 2 ↥M)
      (T1ThetaBar.odd_card_pPrimeCore M) hE₀p
    have hc' : c ∈ (centralizer (E₀ : Set ↥M)).map (T1ThetaBar.rho M) := by
      rw [hcent]
      exact hc
    obtain ⟨g, hg, rfl⟩ := hc'
    have hgE' : (g : G) ∈ normalizer ((E₀.map M.subtype : Subgroup G) : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_)
      rintro _ ⟨m, hm, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg m hm)
    exact Lemma83Bar.mk_mem_normalizer_barIn
      (normalizer_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2 ⟨hE'A, hE'el, hE'r⟩ hgE')

theorem thetaBar_le_iSup_core (hs : Stage2Setup G x K A M P Q) :
    barIn M (thetaHalf 1 A) ≤ ⨆ (e : Mbar M) (_ : e ∈ barIn M (A ⊓ K) ∧ e ≠ 1),
      pPrimeCoreOf 2 (centralizer ({e} : Set (Mbar M))) := by
  obtain ⟨-, hAel, -, -⟩ := hs.src
  have hAM : A ≤ M := (inU0_A hs).1.1
  have hAe3 : IsE 3 ⊤ A := isE3_of_isSource2 hs.src
  have hbal := hs.reg.1
  have hE : IsE 2 A (A ⊓ K) := isE_inf_K hs
  have hEq : thetaHalf 1 (A ⊓ K) = thetaHalf 1 A :=
    b_ig_21_10 G 1 le_rfl A (A ⊓ K) hAe3 hbal.1 hbal.2 hE
  have hApg : IsPGroup 2 ↥A := CFSG.IsElementaryAbelian.isPGroup 2 ↥A
  have hEel : CFSG.IsElementaryAbelian 2 ↥(A ⊓ K) := hE.2.1
  set J : Subgroup (Mbar M) := ⨆ (e : Mbar M) (_ : e ∈ barIn M (A ⊓ K) ∧ e ≠ 1),
    pPrimeCoreOf 2 (centralizer ({e} : Set (Mbar M))) with hJ
  have key : ∀ d ∈ A ⊓ K, d ≠ 1 → pPrimeCoreOf 2 (centralizer ({d} : Set G)) ≤
      (J.comap (T1ThetaBar.rho M)).map M.subtype := by
    intro d hd hd1 y hy
    have hdM : d ∈ M := hAM hd.1
    have hYM : pPrimeCoreOf 2 (centralizer ({d} : Set G)) ≤ M :=
      pPrimeCoreOf_le_of_inU0 (inU0_A hs) fun a ha => Subgroup.mem_centralizer_singleton_iff.2
        (Th2Sig8.mul_comm_of_isElementaryAbelian hAel ha hd.1)
    have hdp : IsPGroup 2 ↥(zpowers (⟨d, hdM⟩ : ↥M)) :=
      (hApg.comap_subtype (K := M)).to_le (Subgroup.zpowers_le.2 hd.1)
    have h1 := T1ThetaBar.barIn_pPrimeCoreOf_centralizer_le hdp
    have hmem : T1ThetaBar.rho M ⟨d, hdM⟩ ∈ barIn M (A ⊓ K) := ⟨⟨d, hdM⟩, hd, rfl⟩
    have hne : T1ThetaBar.rho M ⟨d, hdM⟩ ≠ 1 := fun h => hd1 (congrArg Subtype.val
      (Lemma83Bar.injOn_mk_of_isPGroup hdp ⟨d, hdM⟩ (Subgroup.mem_zpowers _) h))
    have h2 : pPrimeCoreOf 2 (centralizer ({T1ThetaBar.rho M ⟨d, hdM⟩} : Set (Mbar M))) ≤ J :=
      le_iSup₂_of_le (T1ThetaBar.rho M ⟨d, hdM⟩) ⟨hmem, hne⟩ le_rfl
    exact ⟨⟨y, hYM hy⟩, h2 (h1 ⟨⟨y, hYM hy⟩, hy, rfl⟩), rfl⟩
  have hΘ : thetaHalf 1 A ≤ (J.comap (T1ThetaBar.rho M)).map M.subtype := by
    rw [← hEq]
    refine sup_le (iSup₂_le fun D hD => ?_) ?_
    · obtain ⟨d, hdD, hd1⟩ := Th2Sig8.exists_ne_one hD.2.1 hD.2.2
      have hnorm : A ⊓ K ≤ normalizer (AG D : Set G) := Th2Sig10.le_normalizer_AG hEel hD.1
      have hcomm : ⁅AG D, A ⊓ K⁆ ≤ AG D := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ AG D :=
          (Subgroup.mem_normalizer_iff.1 (hnorm hg₂) g₁⁻¹).1 (inv_mem hg₁)
        have h2 : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h2]
        exact mul_mem hg₁ h1
      have hAG : AG D ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) := iInf₂_le d ⟨hdD, hd1⟩
      exact hcomm.trans (hAG.trans (key d (hD.1 hdD) hd1))
    · obtain ⟨e, he, he1⟩ := Th2Sig8.exists_ne_one hEel (by have := hE.2.2; omega)
      have hAG : AG (A ⊓ K) ≤ pPrimeCoreOf 2 (centralizer ({e} : Set G)) := iInf₂_le e ⟨he, he1⟩
      exact hAG.trans (key e he he1)
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨t', ht', htt⟩ := hΘ (show (t : G) ∈ thetaHalf 1 A from ht)
  have : t' = t := Subtype.ext htt
  subst this
  exact ht'

end CFSG.GH74.Generic.BProg.B2
