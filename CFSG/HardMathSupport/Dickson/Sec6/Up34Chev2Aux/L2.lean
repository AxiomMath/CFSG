module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap510
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldBasic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem not_isSolvable_of_isLThreeFour {X : Type} [Group X] (h : IsLThreeFour X) :
    ¬ Group.IsSolvable X := by
  intro hs
  obtain ⟨hsimp, a, b, hab⟩ := isSimpleGroup_of_isLThreeFour h
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := X)).2 hs a b)

theorem two_pow_mul_ne_20160 (g : ℕ) : 2 ^ g * (4 ^ g - 1) ≠ 20160 := by
  intro h
  have hg : g ≤ 6 := by
    by_contra hcon
    push Not at hcon
    have h1 : 2 ^ 7 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hcon
    have h2 : 4 ^ 7 ≤ 4 ^ g := Nat.pow_le_pow_right (by norm_num) hcon
    have h3 : 1 ≤ 4 ^ g - 1 := by omega
    have : 2 ^ g * 1 ≤ 2 ^ g * (4 ^ g - 1) := Nat.mul_le_mul_left _ h3
    have h4 : 128 * 16000 ≤ 2 ^ g * (4 ^ g - 1) := by
      calc 128 * 16000 ≤ 2 ^ 7 * (4 ^ 7 - 1) := by norm_num
        _ ≤ 2 ^ g * (4 ^ g - 1) := Nat.mul_le_mul h1 (by omega)
    omega
  interval_cases g <;> simp at h

theorem Up34Pumpup.not_solvable_fixed {P : Type} [Group P] [Finite P] {β : MulAut P}
    (h : Up34Pumpup P β) : ¬ Group.IsSolvable ↥(fixSubgroup β) := by
  obtain ⟨-, -, I, hI, hI34⟩ := h
  intro hs
  have hI' : Group.IsSolvable ↥I :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hI.1)
      (Subgroup.inclusion_injective hI.1)
  have hb : Group.IsSolvable (↥I ⧸ GLAPPrimeCore 3 ↥I) := inferInstance
  exact not_isSolvable_of_isLThreeFour hI34 hb

theorem up34C2_l2 : Up34Chev2At FamA1 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα
  cases d with
  | A r q =>
    have hr : r = 1 := hF
    subst hr
    have hp2 : q.p = 2 := hc
    exfalso
    have hm : CFSG.Models.LieModel S .PSL 2 q.p q.exponent := CFSG.Models.lieModel_A 1 q hv e
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
      hm.2.resolve_right (fun h => absurd h.1 (by norm_num))
    haveI : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv S eK.toEquiv
    have hP := hα.of_congr eK
    obtain ⟨hβ3, hβ1, I, hI, hI34⟩ := id hP
    set β := MulAut.congr eK α with hβdef
    rcases l2Aut3Classification_holds K β hβ3 with h1 | hsol | ⟨σ, φ, γ, hφ, hβ⟩
    · exact hβ1 h1
    · exact hP.not_solvable_fixed hsol
    · obtain ⟨F₀, _, _, hcard, ⟨ψ0⟩⟩ := l2FieldFixed_holds K β hβ3 hβ1 σ φ γ hφ hβ
      by_cases h4 : 4 ≤ Nat.card F₀
      · obtain ⟨hQ₀, hZ₀⟩ := l2fld_isQuasisimple_psl2 h4
        have hCq : CFSG.Open.IsQuasisimple ↥(fixSub β) := isQuasisimple_open_of_mulEquiv ψ0 hQ₀
        have hI' : GLAPComponent 3 (fixSub β) I := hI
        have hIC : I = fixSub β :=
          eq_of_isSubnormal_of_quasisimple hCq hI'.2.1 (glaPComponent_perfect hI')
            (glaPComponent_ne_bot hI')
        subst hIC
        have hZC : Subgroup.center ↥(fixSub β) = ⊥ := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.center_eq_bot_of_mulEquiv' ψ0 hZ₀
        have hOC : GLAPPrimeCore 3 ↥(fixSub β) = ⊥ :=
          glaPPrimeCore_eq_bot_of_quasisimple hCq
            (fun z hz => by rw [hZC, Subgroup.mem_bot] at hz; rw [hz, one_pow])
            (by rw [Nat.card_congr ψ0.toEquiv]; exact l2fld_three_dvd_card_psl2)
        have hL34 : IsLThreeFour (StatedProj (StatedSL 2 F₀)) :=
          IsLThreeFour.of_mulEquiv (((barEquivOfCore hOC).symm).trans ψ0) hI34
        have h20160 := card_eq_of_isLThreeFour hL34
        have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, hp2]
        obtain ⟨g, hg⟩ : ∃ g : ℕ, Nat.card F₀ = 2 ^ g := by
          have hdvd : Nat.card F₀ ∣ 2 ^ q.exponent := by
            rw [← hK2, hcard]
            exact dvd_pow_self _ (by norm_num)
          obtain ⟨g, -, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
          exact ⟨g, hg⟩
        have hg1 : 1 ≤ g := by
          rcases Nat.eq_zero_or_pos g with h0 | h0
          · rw [h0] at hg; omega
          · exact h0
        have hodd : Odd (2 ^ g - 1) := by
          obtain ⟨c, hc'⟩ := dvd_pow_self 2 (show g ≠ 0 by omega)
          have hpos : 0 < 2 ^ g := Nat.two_pow_pos g
          exact ⟨c - 1, by omega⟩
        have hgcd : Nat.gcd 2 (2 ^ g - 1) = 1 := Nat.coprime_two_left.2 hodd
        have hord := l514c_card_psl2 (F := F₀)
        rw [h20160, hg, hgcd, mul_one] at hord
        have hsq : (2 ^ g) ^ 2 = 4 ^ g := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [hsq] at hord
        exact two_pow_mul_ne_20160 g hord.symm
      · haveI : Group.IsSolvable (StatedProj (StatedSL 2 F₀)) :=
          l2fld_isSolvable_psl2_of_card_le_three (F := F₀) (by omega)
        exact hP.not_solvable_fixed
          (Group.isSolvable_of_isSolvable_injective (f := ψ0.toMonoidHom) ψ0.injective)
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6
