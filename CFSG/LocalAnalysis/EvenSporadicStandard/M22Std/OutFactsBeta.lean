module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsRho
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsTab
public import Certificates.Certificate24801

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.RankThree.Native CFSG.Monster.B.Co2
  CFSG.ComponentClassification.RankTwoSporadic.M22 CFSG.EvenSporadicStandard.M22Std.TabCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.Blueprint.NativeSporadic

section AutTab

@[expose] noncomputable def autTab (α : MulAut (Carrier .M22)) : Tab := tabP (rho α)

@[expose] noncomputable def autTabMap : TabMap (MulAut (Carrier .M22)) where
  tb := autTab
  mul g h := by simp only [autTab, map_mul, tabP_mul]
  one := by simp only [autTab, map_one, tabP_one]
  inj := fun _ _ h => rho_injective (tabP_injective h)

theorem autTab_conj (y : Carrier .M22) : autTab (MulAut.conj y) = tab y := by
  rw [autTab, rho_conj]
  rfl

theorem autTab_inv (α : MulAut (Carrier .M22)) : autTab α⁻¹ = tabP (rho α)⁻¹ := by
  rw [autTab, map_inv]

end AutTab

section Beta

theorem betaArr_valid : validA 24 betaArr = true := by
  have h := (Certificates.certificate24801 : autA betaArr = true)
  simp only [autA, Bool.and_eq_true] at h
  exact h.1.1

theorem betaArr_apply (j : Fin 24) : (permOfArr 24 betaArr j : ℕ) = betaArr[(j : ℕ)]! :=
  ((rep_of_validA betaArr_valid) j).symm

theorem betaPerm_mem : permOfArr 24 betaArr ∈ AutPerm :=
  mem_AutPerm_of_autA Certificates.certificate24801

theorem betaPerm_zero : permOfArr 24 betaArr 0 = 1 := by
  refine Fin.ext ?_
  rw [betaArr_apply]
  rfl

theorem betaPerm_one : permOfArr 24 betaArr 1 = 0 := by
  refine Fin.ext ?_
  rw [betaArr_apply]
  rfl

@[expose] noncomputable def betaPerm : Ppair :=
  ⟨⟨permOfArr 24 betaArr, betaPerm_mem⟩,
    (mem_Ppair_iff _).2 (Or.inr ⟨betaPerm_zero, betaPerm_one⟩)⟩

theorem coe_betaPerm : ((betaPerm : AutPerm) : Equiv.Perm (Fin 24)) = permOfArr 24 betaArr := rfl

private theorem jCat_val (i : Fin 22) : (jCat i : ℕ) = jCatList.getD i.val 0 := by
  revert i
  decide

private theorem betaArr_jCat (i : Fin 22) :
    betaArr[jCatList.getD i.val 0]! = jCatList.getD (betaTab.getD i.val 0) 0 := by
  revert i
  decide

private theorem betaTab_lt (i : Fin 22) : betaTab.getD i.val 0 < 22 := by
  revert i
  decide

theorem sigHom_betaPerm (i : Fin 22) : (sigHom betaPerm i : ℕ) = betaTab.getD i.val 0 := by
  have h1 : jCat (sigHom betaPerm i) = jCat ⟨betaTab.getD i.val 0, betaTab_lt i⟩ := by
    refine Fin.ext ?_
    rw [jCat_sigHom, coe_betaPerm, betaArr_apply, jCat_val i, betaArr_jCat, jCat_val]
  exact congrArg Fin.val (jCat_injective h1)

section

@[expose] noncomputable def betaAut : MulAut (Carrier .M22) := autEmbed betaPerm

theorem autTab_betaAut : autTab betaAut = betaTab := by
  rw [autTab, betaAut, rho_autEmbed]
  refine List.ext_getElem (by rw [length_tabP]; rfl) fun i h1 h2 => ?_
  have h3 : i < 22 := by rw [length_tabP] at h1; exact h1
  have := getD_tabP (sigHom betaPerm) ⟨i, h3⟩
  rw [List.getD_eq_getElem _ _ h1] at this
  rw [this, sigHom_betaPerm, List.getD_eq_getElem _ _ h2]

theorem betaAut_sq : betaAut * betaAut = 1 := by
  refine autTabMap.inj ?_
  have h : tmul betaTab betaTab = idTab := by decide
  have e1 : autTab (betaAut * betaAut) = tmul (autTab betaAut) (autTab betaAut) :=
    autTabMap.mul _ _
  have e2 : autTab (1 : MulAut (Carrier .M22)) = idTab := autTabMap.one
  show autTab (betaAut * betaAut) = autTab 1
  rw [e1, e2, autTab_betaAut]
  exact h

theorem betaAut_not_inner : betaAut ∉ innerImage (Carrier .M22) ⊤ := by
  intro h
  have h1 := ((autEmbed_mem_innerImage_iff betaPerm).1 h).1
  rw [coe_betaPerm, betaPerm_zero] at h1
  exact absurd (congrArg Fin.val h1) (by decide)

end

end Beta

end CFSG.EvenSporadicStandard.M22Std
