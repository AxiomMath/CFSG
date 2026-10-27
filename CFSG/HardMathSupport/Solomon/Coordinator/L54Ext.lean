module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16ExtUps
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16Ext

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

theorem isInGMinusOne_of_hyperplane_ext (h2316 : Input23_16At3Ext) (h224 : Input22_4)
    {G' : Type} [Group G'] [Finite G'] {X B L : Subgroup G'} (hBX : B ≤ X)
    (hBel : IsElemAbelian 3 B) (hcomp : GLAPComponent 3 X L) {H : Subgroup G'}
    (hH : H ≤ B ⊓ Subgroup.normalizer (L : Set G'))
    (hHcard : Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set G')) = 3 * Nat.card ↥H)
    (hHfield : ∀ h ∈ H, InducesFieldAut 3 L h)
    (hext : IsThreeType (barOf 3 L) →
      IsExtremalType (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) : IsInGMinusOne 3 B L := by
  set N : Subgroup G' := B ⊓ Subgroup.normalizer (L : Set G') with hNdef
  have hNL : N ≤ Subgroup.normalizer (L : Set G') := inf_le_right
  have hN : IsElemAbelian 3 N := isElemAbelian_of_le' hBel inf_le_left
  obtain ⟨j, hj⟩ := exists_card_eq_pow Nat.prime_three hN
  have hHel : IsElemAbelian 3 H := isElemAbelian_of_le' hN hH
  obtain ⟨k, hk⟩ := exists_card_eq_pow Nat.prime_three hHel
  have hkj : k + 1 = j := by
    have h3 : 3 ^ (k + 1) = 3 ^ j := by rw [pow_succ, mul_comm, ← hk, ← hHcard, hj]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  have hN1 : 1 ≤ CFSG.Open.pRank 3 N := by
    rw [pRank_eq_of_card Nat.prime_three hN hj]; omega
  let ρ : ↥N →* MulAut (barOf 3 L) := (barAut 3 L).comp (Subgroup.inclusion hNL)
  set H' : Subgroup ↥N := H.subgroupOf N with hH'
  have hH'card : Nat.card ↥H' = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hH'el : IsElemAbelian 3 H' :=
    isElemAbelian_of_le' (isElemAbelian_top_subgroup hN) le_top
  have hrkH' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) - 1 ≤ CFSG.Open.pRank 3 H' := by
    rw [pRank_top_eq hN, pRank_eq_of_card Nat.prime_three hN hj,
      pRank_eq_of_card Nat.prime_three hH'el (hH'card.trans hk)]
    omega
  have hK : (⊤ : Subgroup (barOf 3 L)) ≤ ⨆ (E : Subgroup ↥N)
      (_ : CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) - 1 ≤ CFSG.Open.pRank 3 E), fixedSubgroup ρ E := by
    by_cases htriv : ∀ h ∈ H', ρ h = 1
    · refine le_trans ?_ (le_iSup₂_of_le H' hrkH' le_rfl)
      intro x _ h hh
      rw [htriv h hh]; rfl
    · push Not at htriv
      obtain ⟨h0, hh0, hρ0⟩ := htriv
      have hfa : IsFieldAutThree (ρ h0) := by
        obtain ⟨_, hf⟩ := hHfield h0.1 (Subgroup.mem_subgroupOf.1 hh0)
        exact hf
      have hT : IsThreeType (barOf 3 L) := IsThreeType.of_isFieldAutThree hfa hρ0
      have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hcomp
      exact h2316 (barOf 3 L) hq (hext hT) ↥N ρ
        (isElemAbelian_top_subgroup hN)
        ⟨H', by rw [hH'card, ← hHcard], fun h hh => by
          obtain ⟨_, hf⟩ := hHfield h.1 (Subgroup.mem_subgroupOf.1 hh)
          exact hf⟩
  have hL := le_gammaPrimeIn_of_quotient hNL hN hN1 hK
  exact h224 G' X B L hBX hBel hcomp hN1 hL

theorem lemma54_of_inputs_ext (h2316 : Input23_16At3Ext) (hU : UpsilonExtremal)
    (h224 : Lemma54Ns.Input22_4)
    (h191 : Lemma54Ns.Input19_1_2) (h197 : Lemma54Ns.Input19_7_3d)
    (h7 : Lemma54Ns.Input7_FieldInnDiag) : Lemma54 := by
  intro G _ _ m hS hC B hB b hb hb1 L hL A hAB hA
  by_contra hrk
  have hrk3 : 3 ≤ CFSG.Open.pRank 3 A := by omega
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 3 ^ 4 := by
    have := hB.1.2.1
    rwa [hC.2.1] at this
  have hBrank : CFSG.Open.pRank 3 B = 4 := pRank_eq_of_card Nat.prime_three hBel hBcard
  have hAel : IsElemAbelian 3 A := Lemma54Ns.isElemAbelian_of_le' hBel hAB
  obtain ⟨k, hk⟩ := Lemma54Ns.exists_card_eq_pow Nat.prime_three hAel
  have hk3 : 3 ≤ k := (pRank_eq_of_card Nat.prime_three hAel hk) ▸ hrk3
  have hcomp := hL.1
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (L : Set G) := fun a ha => (hA a ha).1
  have hbC : B ≤ Subgroup.centralizer ({b} : Set G) := le_centralizer_of_mem hBel hb
  rcases hL.2 with ⟨hlam, hpsi⟩ | ⟨D, hD, hnot⟩
  ·
    have hnotslob := Lemma54Ns.not_slob_of_le_lambdaOf hcomp hlam
    have hANle : A ≤ B ⊓ Subgroup.normalizer (L : Set G) := fun a ha => ⟨hAB ha, hAN a ha⟩
    obtain ⟨H, hHA, hHcard⟩ := Lemma54Ns.exists_hyperplane hBel hBcard inf_le_left hANle hk hk3
    have hG := isInGMinusOne_of_hyperplane_ext h2316 h224 hbC hBel hcomp
      (fun h hh => hANle (hHA hh)) hHcard (fun h hh => hA h (hHA hh))
      (hU G m hS hC B hB b hb hb1 L hL)
    have hG1 : IsInGOne 3 B L := Lemma54Ns.isInGOne_of_isInGMinusOne hBrank hG
    apply hpsi
    refine (le_sSup ⟨hcomp, hnotslob, hG1⟩ : L ≤ psiOf 3 B b).trans ?_
    exact (le_sup_left.trans le_sup_left : psiOf 3 B b ≤ psiStar 3 B b).trans
      (le_iSup₂_of_le b hb (le_iSup (fun _ : b ≠ 1 => psiStar 3 B b) hb1))
  ·
    obtain ⟨hDB, hDel, hDcard⟩ := hD
    obtain ⟨a, ⟨haA, haD⟩, ha1⟩ := Lemma54Ns.exists_mem_inf_ne_one hAB hDB (by
      rw [hBcard, hk, hDcard]
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      norm_num at this ⊢
      omega)
    obtain ⟨haN, hfa⟩ := hA a haA
    exact Lemma54Ns.false_of_branch_b h191 h197 h7 hS hBel hb hb1 hcomp hDel hDcard hDB hnot haD ha1
      haN hfa

end CFSG.HardMathSupport.Solomon.Coordinator
