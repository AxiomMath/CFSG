module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCentralizers
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open Matrix CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

section Linear

variable {K : Type} [Field K] [Finite K]

theorem linear_odd_centralizer_contains_full_torus (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f) (x : PSL2MatrixGroup K)
    (hx : x ≠ 1) (hxodd : Odd (orderOf x)) :
    ∃ T : Subgroup (PSL2MatrixGroup K),
      IsCyclic T ∧ T ≤ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K)) ∧
      (Nat.card T = Nat.card K - 1 ∨ Nat.card T = Nat.card K + 1) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (PSL2MatrixGroup K) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpart⟩ :=
    huppert_II_8_5_a_psl2_cover (p := 2) (f := f) hcard P
  have hqeven : Even (Nat.card K) := by
    rw [hcard]
    exact even_two.pow_of_ne_zero (by omega)
  have hqodd : Odd (Nat.card K - 1) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hparity := (Nat.even_sub (show 1 ≤ Nat.card K from Nat.card_pos)).mp heven
    exact Nat.not_even_one (hparity.mp hqeven)
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 1 := hqodd.coprime_two_right.gcd_eq_one
  obtain ⟨T, hxT, _⟩ := hpart x hx
  have htorus : ∀ (R : Subgroup (PSL2MatrixGroup K)), IsCyclic R →
      x ∈ R → R ≤ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K)) := by
    intro R hR hxR y hyR
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((@IsMulCommutative.is_comm R _ hR.isMulCommutative).comm
        (⟨y, hyR⟩ : R) (⟨x, hxR⟩ : R)))
  rcases hxT.2 with hP | hU | hS
  · obtain ⟨g, rfl⟩ := hP
    have htwo := P.isPGroup'.map (MulAut.conj g).toMonoidHom
    let y : (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hxT.1⟩
    have hyodd : Odd (orderOf y) := (Subgroup.orderOf_coe y).symm ▸ hxodd
    have hcop := htwo.orderOf_coprime hyodd.coprime_two_left y
    have hyone : y = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl)
    exact False.elim (hx (congrArg Subtype.val hyone))
  · obtain ⟨g, rfl⟩ := hU
    have hcyclic := (MulEquiv.subgroupMap (MulAut.conj g) U).isCyclic.mp hUcyclic
    refine ⟨_, hcyclic, htorus _ hcyclic hxT.1, Or.inl ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hUcard, hgcd, Nat.div_one]
  · obtain ⟨g, rfl⟩ := hS
    have hcyclic := (MulEquiv.subgroupMap (MulAut.conj g) S).isCyclic.mp hScyclic
    refine ⟨_, hcyclic, htorus _ hcyclic hxT.1, Or.inr ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hScard, hgcd, Nat.div_one]

theorem linear_actual_full_centralizer_card {G : Type*} [Group G] [Finite G]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (e : G ≃* GLAProj (GLASLGroup (Fin 2) K))
    (W : Subgroup G) (hWne : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hdiv : Nat.card W ∣ Nat.card K + 1)
    (hcentralizer : ∀ x ∈ W, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = W) :
    Nat.card W = Nat.card K + 1 := by
  let E : G ≃* PSL2MatrixGroup K := e.trans glaSLQuotientEquivPSL
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hwG : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
  have hworder : Odd (orderOf (w : G)) := by
    have h := hWodd.of_dvd_nat (orderOf_dvd_natCard w)
    exact Subgroup.orderOf_coe w ▸ h
  have hEw : E (w : G) ≠ 1 := by
    intro h
    apply hwG
    exact E.injective (h.trans E.map_one.symm)
  have hEworder : Odd (orderOf (E (w : G))) :=
    (orderOf_injective E.toMonoidHom E.injective (w : G)).symm ▸ hworder
  obtain ⟨T, _, hTC, hTcard⟩ :=
    linear_odd_centralizer_contains_full_torus f hf hcard (E w) hEw hEworder
  have hCcard : Nat.card (Subgroup.centralizer ({E (w : G)} : Set (PSL2MatrixGroup K))) =
      Nat.card W := by
    rw [← Nat.card_congr (elementCentralizerEquiv E (w : G)).toEquiv,
      hcentralizer (w : G) w.property hwG]
  have hTdiv : Nat.card T ∣ Nat.card W :=
    hCcard ▸ Subgroup.card_dvd_of_le hTC
  rcases hTcard with hsplit | hnonsplit
  · have hd : Nat.card K - 1 ∣ Nat.card K + 1 := by
      rw [← hsplit]
      exact hTdiv.trans hdiv
    have htwo : Nat.card K - 1 ∣ 2 := by
      have h := Nat.dvd_sub hd (dvd_refl (Nat.card K - 1))
      have hpos : 1 ≤ Nat.card K := Nat.card_pos
      simpa only [show Nat.card K + 1 - (Nat.card K - 1) = 2 by omega] using h
    have hqge : 4 ≤ Nat.card K := by
      rw [hcard]
      exact (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
    have hsmall := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) htwo
    omega
  · rw [hnonsplit] at hTdiv
    exact Nat.dvd_antisymm hdiv hTdiv

end Linear

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
