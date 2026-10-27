module

public import CFSG.LocalAnalysis.ComponentInitial.KnownFourGroupDiagonalPump
public import CFSG.LocalAnalysis.LargeEvenClassification.RankThreeSubgroupConnectivity
public import CFSG.Assembly.OddCoreElimination.Coverage
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {G : Type} [Group G]

theorem isElemAbelian_two_of_le {E B : Subgroup G} (hEB : E ≤ B)
    (hB : CFSG.Assembly.IsElemAbelian 2 B) : CFSG.Assembly.IsElemAbelian 2 E :=
  CFSG.Open.IsElemAbelian.mono hB hEB

theorem isElemAbelian_two_subgroupOf {E H : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 2 E) :
    CFSG.Assembly.IsElemAbelian 2 (E.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem orderOf_eq_two_of_isElemAbelian {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 2 E)
    {x : G} (hx : x ∈ E) (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (hE.2 x hx) hx1

theorem exists_card_eight_mem_of_isElemAbelian [Finite G] {B : Subgroup G}
    (hB : CFSG.Assembly.IsElemAbelian 2 B) (hB4 : 4 < Nat.card B) {t : G} (htB : t ∈ B)
    (ht : orderOf t = 2) :
    ∃ E : Subgroup G, E ≤ B ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hB).exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : ∀ m ≤ 3, 2 ^ m ∣ Nat.card B := fun m hm =>
    hk ▸ Nat.pow_dvd_pow 2 (hm.trans hk3)
  let t' : B := ⟨t, htB⟩
  have ht' : Nat.card (zpowers t') = 2 ^ 1 := by
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact ht
  obtain ⟨K₂, hK₂, hK₂t⟩ := Sylow.exists_subgroup_card_pow_succ (hdvd 2 (by norm_num)) ht'
  obtain ⟨K₃, hK₃, hK₃₂⟩ := Sylow.exists_subgroup_card_pow_succ (hdvd 3 le_rfl) hK₂
  refine ⟨K₃.map B.subtype, map_subtype_le K₃, isElemAbelian_two_of_le (map_subtype_le K₃) hB,
    ?_, ⟨t', hK₃₂ (hK₂t (mem_zpowers t')), rfl⟩⟩
  rw [card_map_of_injective B.subtype_injective, hK₃]
  norm_num

theorem exists_card_eight_le_of_isElemAbelian [Finite G] {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 2 A) (hA8 : 8 ≤ Nat.card A) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ Nat.card A₀ = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 3)
    (hk ▸ Nat.pow_dvd_pow 2 hk3 : 2 ^ 3 ∣ Nat.card A)
  refine ⟨K.map A.subtype, map_subtype_le K, ?_⟩
  rw [card_map_of_injective A.subtype_injective, hK]
  norm_num

theorem isComponentOf_centralizer_conj_of_mem_centralizer {J : Subgroup G} {c x : G}
    (hc : c ∈ centralizer (J : Set G))
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({x} : Set G))) :
    CFSG.Assembly.IsComponentOf J (centralizer ({c * x * c⁻¹} : Set G)) := by
  have h := isComponentOf_map_conj hJ c
  rwa [map_conj_centralizer_singleton, show J.map (MulAut.conj c).toMonoidHom = J from
    conjSub_eq_self_of_mem_centralizer hc] at h

theorem selected_component_eight_group_derived_propagation {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) [Finite G] (hK : CFSG.Assembly.KProper C G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {J A : Subgroup G}
    (hAJ : A ≤ centralizer (J : Set G)) (hA : CFSG.Assembly.IsElemAbelian 2 A)
    (hA8 : 8 ≤ Nat.card A)
    (hJA : ∀ a ∈ A, a ≠ 1 → CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)))
    (hmax : ∀ s : G, orderOf s = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({s} : Set G)) →
        (center Q).index ≤ (center J).index) :
    (∀ E : Subgroup G, E ≤ centralizer (J : Set G) → CFSG.Assembly.IsElemAbelian 2 E →
        Nat.card E = 8 → ∀ t ∈ E, orderOf t = 2 →
          CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G))) ∧
      (∀ t ∈ ⁅centralizer (J : Set G), centralizer (J : Set G)⁆, orderOf t = 2 →
        CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G))) ∧
      (∀ t ∈ centralizer (J : Set G), orderOf t = 2 →
        ¬ CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) →
          t ∉ ⁅centralizer (J : Set G), centralizer (J : Set G)⁆ ∧
            ∀ B : Subgroup G, B ≤ centralizer (J : Set G) → CFSG.Assembly.IsElemAbelian 2 B →
              t ∈ B → Nat.card B ≤ 4) := by
  set Cj := centralizer (J : Set G) with hCj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A₀, hA₀A, hA₀card⟩ := exists_card_eight_le_of_isElemAbelian hA hA8
  have hA₀ : CFSG.Assembly.IsElemAbelian 2 A₀ := isElemAbelian_two_of_le hA₀A hA
  have hA₀C : A₀ ≤ Cj := hA₀A.trans hAJ
  have hmain : ∀ E : Subgroup G, E ≤ Cj → CFSG.Assembly.IsElemAbelian 2 E → Nat.card E = 8 →
      ∀ t ∈ E, orderOf t = 2 → CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) := by
    intro E hEC hE hEcard t htE ht
    obtain ⟨P, hP⟩ := (isPGroup_of_isElemAbelian (isElemAbelian_two_subgroupOf
      (H := Cj) hA₀)).exists_le_sylow
    obtain ⟨Q, hQ⟩ := (isPGroup_of_isElemAbelian (isElemAbelian_two_subgroupOf
      (H := Cj) hE)).exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Cj P Q
    set c : G := (g : G) with hcdef
    have hcC : c ∈ Cj := g.2
    set QG : Subgroup G := (Q : Subgroup Cj).map Cj.subtype with hQG
    have hQGC : QG ≤ Cj := map_subtype_le _
    set A₁ : Subgroup G := A₀.map (MulAut.conj c).toMonoidHom with hA₁
    have hA₁Q : A₁ ≤ QG := by
      rintro _ ⟨a, haA₀, rfl⟩
      have hmem : (MulAut.conj g) ⟨a, hA₀C haA₀⟩ ∈ (Q : Subgroup Cj) := by
        rw [← hg]
        exact smul_mem_pointwise_smul _ (MulAut.conj g) (P : Subgroup Cj) (hP haA₀)
      exact ⟨_, hmem, rfl⟩
    have hEQ : E ≤ QG := fun e he => ⟨⟨e, hEC he⟩, hQ he, rfl⟩
    have htwo : IsPGroup 2 QG :=
      Q.2.of_equiv ((Q : Subgroup Cj).equivMapOfInjective Cj.subtype Cj.subtype_injective)
    have hA₁card : Nat.card A₁ = 8 := by
      rw [hA₁, card_map_of_injective (MulAut.conj c).injective, hA₀card]
    have hA₁el : CFSG.Assembly.IsElemAbelian 2 A₁ := SectionRank.isElemAbelian_map hA₀ _
    have hA₁S := isElemAbelian_two_subgroupOf (H := QG) hA₁el
    have hA₁Scard : Nat.card (A₁.subgroupOf QG) = 8 := by
      rw [← hA₁card]
      exact Nat.card_congr (subgroupOfEquivOfLe hA₁Q).toEquiv
    have hES := isElemAbelian_two_subgroupOf (H := QG) hE
    have hEScard : Nat.card (E.subgroupOf QG) = 8 := by
      rw [← hEcard]
      exact Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv
    have hrank : 3 ≤ CFSG.Open.twoRank QG :=
      SectionRank.le_pRank (p := 2) (by norm_num) le_top hA₁S (by rw [hA₁Scard]; norm_num)
    obtain ⟨n, path, h0, hlast, hpath, hinter⟩ :=
      CFSG.LargeEvenClassification.Helpers.rank_three_elementary_subgroup_connectivity QG htwo
        hrank (A₁.subgroupOf QG) (E.subgroupOf QG) hA₁S hA₁Scard hES hEScard
    have hwit : ∀ i : Fin (n + 1), ∀ x ∈ path i, x ≠ 1 →
        CFSG.Assembly.IsComponentOf J (centralizer ({(x : G)} : Set G)) := by
      intro i
      induction i using Fin.induction with
      | zero =>
        intro x hx hx1
        rw [h0] at hx
        obtain ⟨a, haA₀, hax⟩ := hx
        have hax' : c * a * c⁻¹ = (x : G) := hax
        have ha1 : a ≠ 1 := by
          rintro rfl
          apply hx1
          apply Subtype.ext
          rw [← hax']
          simp
        have h := isComponentOf_centralizer_conj_of_mem_centralizer hcC (hJA a (hA₀A haA₀) ha1)
        rwa [hax'] at h
      | succ i ih =>
        intro x hx hx1
        set W : Subgroup QG := path i.castSucc ⊓ path i.succ with hW
        have hWel : CFSG.Assembly.IsElemAbelian 2 W :=
          isElemAbelian_two_of_le inf_le_right (hpath i.succ).1
        refine known_four_group_eliminates_diagonal_pump hC hpump hK hB (U := W.map QG.subtype)
          ?_ (SectionRank.isElemAbelian_map hWel _) ?_ ?_ hmax (hQGC x.2) ?_ ?_
        · exact (map_subtype_le W).trans hQGC
        · rw [card_map_of_injective QG.subtype_injective]
          exact hinter i
        · rintro _ ⟨w, hw, rfl⟩ hw1
          exact ih w (mem_inf.1 hw).1 fun h => hw1 (by rw [h]; rfl)
        · rw [Subgroup.orderOf_coe]
          exact orderOf_eq_two_of_isElemAbelian (hpath i.succ).1 hx hx1
        · rintro _ ⟨w, hw, rfl⟩
          rw [mem_centralizer_singleton_iff]
          exact congrArg (fun z : path i.succ => ((z : QG) : G))
            ((hpath i.succ).1.1.is_comm.comm ⟨w, (mem_inf.1 hw).2⟩ ⟨x, hx⟩)
    have htS : (⟨t, hEQ htE⟩ : QG) ∈ path (Fin.last n) := by
      rw [hlast]
      exact htE
    exact hwit (Fin.last n) _ htS fun h => by
      have h1 : t = 1 := congrArg Subtype.val h
      rw [h1, orderOf_one] at ht
      norm_num at ht
  have hderived : ∀ t ∈ ⁅Cj, Cj⁆, orderOf t = 2 →
      CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) := by
    intro t ht ht2
    rw [← map_subtype_commutator] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    have hrank : 3 ≤ CFSG.Assembly.twoRank Cj :=
      SectionRank.le_pRank (p := 2) (by norm_num) le_top
        (isElemAbelian_two_subgroupOf (H := Cj) hA₀) (by
          rw [show Nat.card (A₀.subgroupOf Cj) = Nat.card A₀ from
            Nat.card_congr (subgroupOfEquivOfLe hA₀C).toEquiv, hA₀card]
          norm_num)
    have ht'2 : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
    obtain ⟨E, hE, hEcard, htE⟩ :=
      CFSG.Assembly.Dichotomy.derivedInvolutionCoverage hrank ht' ht'2
    refine hmain (E.map Cj.subtype) (map_subtype_le E) (SectionRank.isElemAbelian_map hE _) ?_
      _ ⟨t', htE, rfl⟩ ht2
    rw [card_map_of_injective Cj.subtype_injective, hEcard]
  refine ⟨hmain, hderived, fun t htC ht hnot => ⟨fun htd => hnot (hderived t htd ht), ?_⟩⟩
  intro B hBC hBel htB
  by_contra hB4
  push Not at hB4
  obtain ⟨E, hEB, hEel, hEcard, htE⟩ := exists_card_eight_mem_of_isElemAbelian hBel hB4 htB ht
  exact hnot (hmain E (hEB.trans hBC) hEel hEcard t htE ht)

end CFSG.LocalAnalysis.ComponentInitial
