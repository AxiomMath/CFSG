module

public import CFSG.GH74.Generic.BProg.B2.Defs

import CFSG.GH74.Generic.BProg.B2.Lemma82
import CFSG.GH74.Generic.BProg.B2.Lemma83
import CFSG.GH74.Generic.BProg.B1.Lift0
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GH74.GLS.C3.Layer1.BackConj

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

open CFSG.GH74.GLS.C3.Layer1.Back (pRank_conjugate' isElementaryAbelian_conjugate)

namespace Lemma83Bar

variable {G : Type} [Group G]

theorem mem_barIn_iff {M H : Subgroup G} {y : Mbar M} :
    y ∈ barIn M H ↔ ∃ x : ↥M, (x : G) ∈ H ∧ QuotientGroup.mk' (pPrimeCore 2 ↥M) x = y := by
  unfold barIn
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mk_mem_normalizer_barIn {M X : Subgroup G} {g : ↥M} (hg : (g : G) ∈ normalizer (X : Set G)) :
    QuotientGroup.mk' (pPrimeCore 2 ↥M) g ∈ normalizer (barIn M X : Set (Mbar M)) := by
  have key : ∀ g : ↥M, (g : G) ∈ normalizer (X : Set G) → ∀ n ∈ barIn M X,
      QuotientGroup.mk' (pPrimeCore 2 ↥M) g * n * (QuotientGroup.mk' (pPrimeCore 2 ↥M) g)⁻¹ ∈
        barIn M X := by
    intro g hg n hn
    obtain ⟨x, hx, rfl⟩ := mem_barIn_iff.1 hn
    refine mem_barIn_iff.2 ⟨g * x * g⁻¹, ?_, by simp⟩
    have hcoe : ((g * x * g⁻¹ : ↥M) : G) = (g : G) * x * (g : G)⁻¹ := by simp
    rw [hcoe]
    exact (mem_normalizer_iff.1 hg x).1 hx
  refine Lemma82.mem_normalizer_of_forall (key g hg) (fun n hn => ?_)
  have hginv : ((g⁻¹ : ↥M) : G) ∈ normalizer (X : Set G) := by
    rw [Subgroup.coe_inv]
    exact inv_mem hg
  simpa using key g⁻¹ hginv n hn

theorem barIn_ne_bot_of_not_le {M X : Subgroup G} (hXM : X ≤ M) (hX : ¬ X ≤ pPrimeCoreOf 2 M) :
    barIn M X ≠ ⊥ := by
  intro hbot
  apply hX
  intro x hx
  have hxM : x ∈ M := hXM hx
  have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩ ∈ barIn M X :=
    mem_barIn_iff.2 ⟨⟨x, hxM⟩, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨⟨x, hxM⟩, hmem, rfl⟩

theorem odd_card_barIn {M X : Subgroup G} (hX : Odd (Nat.card ↥X)) : Odd (Nat.card ↥(barIn M X)) := by
  refine Odd.of_dvd_nat hX ((Subgroup.card_map_dvd _ _).trans ?_)
  exact Subgroup.card_comap_dvd_of_injective X M.subtype M.subtype_injective

theorem injOn_mk_of_isPGroup [Finite G] {M : Subgroup G} {K : Subgroup ↥M} (hK : IsPGroup 2 ↥K) :
    ∀ x ∈ K, QuotientGroup.mk' (pPrimeCore 2 ↥M) x = 1 → x = 1 := by
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(pPrimeCore 2 ↥M)) := by
    rw [hn]
    exact Nat.Coprime.pow_left n pPrimeCore_coprime_card
  intro x hx hx1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
  have : x ∈ K ⊓ pPrimeCore 2 ↥M := ⟨hx, hx1⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at this
  exact this

theorem pRank_map_mk [Finite G] {M : Subgroup G} {K : Subgroup ↥M} (hK : IsPGroup 2 ↥K) :
    pRank 2 ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) = pRank 2 ↥K := by
  have hinj : Function.Injective ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).subgroupMap K) := by
    intro a b hab
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) (a : ↥M) = QuotientGroup.mk' (pPrimeCore 2 ↥M) (b : ↥M) :=
      congrArg Subtype.val hab
    have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ((a : ↥M) * (b : ↥M)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := injOn_mk_of_isPGroup hK _ (K.mul_mem a.2 (K.inv_mem b.2)) h2
    exact Subtype.ext (mul_inv_eq_one.1 h3)
  exact (CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two
    (MulEquiv.ofBijective _ ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩)).symm

theorem pRank_barIn [Finite G] {M D : Subgroup G} (hDM : D ≤ M) (hD : IsPGroup 2 ↥D) :
    pRank 2 ↥(barIn M D) = pRank 2 ↥D := by
  have hD0 : IsPGroup 2 ↥(D.subgroupOf M) := by
    refine hD.of_equiv (Subgroup.subgroupOfEquivOfLe hDM).symm
  unfold barIn
  rw [pRank_map_mk hD0]
  have := CFSG.RankThree.PartOne.Quotient36.pRank_map_subtype (G := G) (q := 2) one_lt_two
    (X := M) (D.subgroupOf M)
  rw [Subgroup.map_subgroupOf_eq_of_le hDM] at this
  exact this.symm

end Lemma83Bar

open Lemma83Bar

theorem sym8A_bar {G : Type} [Group G] [Finite G] {M B : Subgroup G} {h : G}
    (S : Sym8A M B h) (hnot : normalizer (pPrimeCoreOf 2 M : Set G) ≠ ⊤) :
    pPrimeCore 2 (Mbar M) = ⊥ ∧
      CFSG.IsElementaryAbelian 2 ↥(barIn M (conjugate B h)) ∧
      (pRank 2 ↥(barIn M (conjugate B h)) = 2 ∨ pRank 2 ↥(barIn M (conjugate B h)) = 3) ∧
      Odd (Nat.card ↥(barIn M (sigX M h))) ∧ barIn M (sigX M h) ≠ ⊥ ∧
      barIn M (conjugate B h) ≤ normalizer (barIn M (sigX M h) : Set (Mbar M)) ∧
      ∀ E : Subgroup (Mbar M), E ≤ barIn M (conjugate B h) →
        pRank 2 ↥(barIn M (conjugate B h)) - 1 ≤ pRank 2 ↥E →
          centralizer (E : Set (Mbar M)) ≤ normalizer (barIn M (sigX M h) : Set (Mbar M)) := by
  obtain ⟨-, -, h3, -, h5, h6, -⟩ := lemma82 S hnot
  have hDM : conjugate B h ≤ M := S.D_le
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := S.hB.1.2.1
  have hDel : CFSG.IsElementaryAbelian 2 ↥(conjugate B h) := isElementaryAbelian_conjugate hBel h
  have hD2 : IsPGroup 2 ↥(conjugate B h) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  set φ : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  set D₀ : Subgroup ↥M := (conjugate B h).subgroupOf M
  have hD₀el : CFSG.IsElementaryAbelian 2 ↥D₀ := by
    have : CFSG.IsElementaryAbelian 2 ↥(conjugate B h) := hDel
    exact CFSG.IsElementaryAbelian.subgroupOf hDM
  have hD₀2 : IsPGroup 2 ↥D₀ := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hDrank : pRank 2 ↥(barIn M (conjugate B h)) = pRank 2 ↥B := by
    rw [pRank_barIn hDM hD2, pRank_conjugate']
  refine ⟨CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two, ?_, hDrank ▸ S.hB.2.1, odd_card_barIn h5,
    barIn_ne_bot_of_not_le (h3.trans inf_le_left) h6, ?_, ?_⟩
  ·
    have : CFSG.IsElementaryAbelian 2 ↥D₀ := hD₀el
    exact CFSG.IsElementaryAbelian.map φ
  ·
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_barIn_iff.1 hy
    exact mk_mem_normalizer_barIn (conjugate_B_le_normalizer_sigX S hx)
  ·
    intro E' hE'D hrk c hc
    rw [hDrank] at hrk
    set E₀ : Subgroup ↥M := E'.comap φ ⊓ D₀
    have hE₀D : E₀ ≤ D₀ := inf_le_right
    have hE₀map : E₀.map φ = E' := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
        exact hx
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hE'D hy
        exact ⟨x, ⟨hy, hx⟩, rfl⟩
    have hE₀2 : IsPGroup 2 ↥E₀ := hD₀2.to_le hE₀D
    set E : Subgroup G := E₀.map M.subtype
    have hED : E ≤ conjugate B h := by
      rintro _ ⟨x, hx, rfl⟩
      exact hE₀D hx
    have hErk : pRank 2 ↥B - 1 ≤ pRank 2 ↥E := by
      have h1 : pRank 2 ↥E = pRank 2 ↥E₀ :=
        CFSG.RankThree.PartOne.Quotient36.pRank_map_subtype (G := G) (q := 2) one_lt_two (X := M) E₀
      have h2 : pRank 2 ↥E' = pRank 2 ↥E₀ := by
        rw [← hE₀map]
        exact pRank_map_mk hE₀2
      rw [h1, ← h2]
      exact hrk
    have hcomm : ∀ a ∈ E₀, φ a * c = c * φ a := by
      intro a ha
      have : φ a ∈ E' := hE₀map ▸ Subgroup.mem_map_of_mem φ ha
      exact mem_centralizer_iff.1 hc (φ a) this
    obtain ⟨g, rfl, hg⟩ := B1.centralizer_quotient_of_pGroup (pPrimeCore 2 ↥M) hNodd hE₀2 hcomm
    have hgcent : (g : G) ∈ centralizer (E : Set G) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (hg a ha)
    exact mk_mem_normalizer_barIn
      (inf_centralizer_le_normalizer_sigX_conjugate S hED hErk ⟨g.2, hgcent⟩)

theorem exists_component_Mbar {G : Type} [Group G] [Finite G] {M B : Subgroup G} {h : G}
    (S : Sym8A M B h) (hnot : normalizer (pPrimeCoreOf 2 M : Set G) ≠ ⊤) :
    ∃ J : Subgroup (Mbar M), IsComponent J ∧
      ¬ barIn M (sigX M h) ≤ centralizer (J : Set (Mbar M)) := by
  obtain ⟨hO, hD, hrk, hW, hW1, hDW, hgam⟩ := sym8A_bar S hnot
  have hr : 2 ≤ pRank 2 ↥(barIn M (conjugate B h)) := by
    rcases hrk with h2 | h2 <;> omega
  exact exists_component_not_centralized hO hD hr hW hW1 hDW hgam

theorem exists_component_Mbar_of_simple {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    {M B : Subgroup G} {h : G} (S : Sym8A M B h) :
    ∃ J : Subgroup (Mbar M), IsComponent J ∧
      ¬ barIn M (sigX M h) ≤ centralizer (J : Set (Mbar M)) :=
  exists_component_Mbar S (normalizer_pPrimeCoreOf_ne_top hG S.maxM S.O_ne)

end CFSG.GH74.Generic.BProg.B2
