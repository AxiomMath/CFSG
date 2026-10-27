module

public import CFSG.ClassicalInvolution.AschTight.S19MCenter
public import CFSG.ClassicalInvolution.AschTight.S19MLift
public import CFSG.ClassicalInvolution.AschTight.S19MInv
public import CFSG.ClassicalInvolution.AschTight.S19MFund

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19M

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits

variable {p : ℕ} [Fact p.Prime]

theorem involutionsConj_modelUniv (hp2 : p ≠ 2) {t : StatedLieTag} {k e : ℕ}
    (ht : S1911.IsT6Tag t k) (hadm : StatedLieAdmissible t k p e) :
    InvolutionsConj (modelUniv t k p e Fact.out).K := by
  have he : 1 ≤ e := hadm.2.1
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact involutionsConj_sl3 (ModelFacts.two_ne_zero_galoisField e hp2)
  · have hF := card_galoisField_two_mul p e he
    have h : modelUniv .PSU 3 p e Fact.out =
        ⟨Unitary.SU (unitaryInvolution (GaloisField p (2 * e)) p e) 3,
          Unitary.rootDatum hF 3⟩ := by
      simp only [modelUniv, lieUniversal, he, ↓reduceDIte]
    have key : ∀ (U : LieUniversal) (_ : modelUniv .PSU 3 p e Fact.out = U),
        InvolutionsConj U.K → InvolutionsConj (modelUniv .PSU 3 p e Fact.out).K := by
      intro U hU hU'
      subst hU
      exact hU'
    exact key _ h (involutionsConj_SU3 hF (ModelFacts.two_ne_zero_galoisField (2 * e) hp2))
  · intro x y hx hy hx1 hy1
    exact Balance.Bootstrap.g2_involutions_conj (odd_natCard_galoisField hp2 he) hx hy hx1 hy1
  · intro x y hx hy hx1 hy1
    exact Balance.Bootstrap.trialityD4_involutions_conj hp2 he hx hy hx1 hy1

theorem factM2 : S1911.FactM2 := by
  intro p e _ hp2 _ E _ _ _ Ω t k e' ht hM hne x hx hx1
  obtain ⟨M⟩ := hM
  have hadm := M.admissible
  have : Finite (modelUniv t k p e' Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (ih8_isFundTag_mf M.isFundTag) hadm
  have hker : Odd (Nat.card M.ψ.ker) :=
    odd_natCard_ker M.ker_le_center (factM3 p e' Fact.out hp2 t k ht hadm)
  obtain ⟨y, hy, hy1, rfl⟩ := exists_involution_lift M.surj hker hx hx1
  obtain ⟨R₀, hR₀⟩ := M.cls_nonempty hne
  obtain ⟨c₀, hc₀⟩ := exists_isUniqueInvolution_of_mem_fund hp2 ht hadm (M.cls_sub hR₀)
  obtain ⟨g, hg⟩ := involutionsConj_modelUniv hp2 ht hadm c₀ y hc₀.sq hy hc₀.ne_one hy1
  have hc : IsUniqueInvolution (conjSub g R₀) y := by
    have h := hc₀.conj g
    rwa [hg] at h
  exact ⟨_, M.map_mem (M.cls_conj R₀ hR₀ g), isUniqueInvolution_map hker hc⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19M
