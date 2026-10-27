module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.KClassJ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Census
public import CFSG.Sporadic.FischerOddCore.Basic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus (fixP)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section


theorem orderOf_fiJP_a : orderOf (fiJP CFSG.Sporadic.Fi22.a) = 2 := by
  rw [MulEquiv.orderOf_eq, CFSG.Sporadic.Fi22.orderOf_a]


theorem card_centralizer_fiJP_a :
    Nat.card (Subgroup.centralizer ({fiJP CFSG.Sporadic.Fi22.a} : Set fi22P)) =
      18393661440 := by
  rw [card_centralizer_mulEquiv, ← CFSG.Sporadic.Fi22.card_Ca]


theorem isConj_fi22OuterZP_fiJP_a : IsConj fi22OuterZP (fiJP CFSG.Sporadic.Fi22.a) := by
  rcases fi22P_involution_isConj (fiJP CFSG.Sporadic.Fi22.a) orderOf_fiJP_a with h | ⟨i, hi⟩
  · exact h
  · exfalso
    have hc := card_centralizer_of_isConj hi
    rw [card_centralizer_fiJP_a] at hc
    fin_cases i
    · have := card_centralizer_x₁
      rw [← fi22OuterXP_zero] at this
      simp only [Fin.zero_eta] at hc
      omega
    · have := card_centralizer_x₂
      rw [← fi22OuterXP_one] at this
      simp only [Fin.mk_one] at hc
      omega

theorem fixP_fiJP (g : CFSG.Sporadic.Fi22.J) :
    fixP ((fiJP g : fi22P) : Equiv.Perm (Fin 3510)) = fixD g := by
  classical
  set σ : fi22P := fiJP g with hσ
  let ρ : Fin 3510 → CFSG.Sporadic.Fi22.J := fun i => fiJP.symm (fi22Theta i : fi22P)
  have hconjZ : ∀ i, IsConj fi22OuterZP ((fi22Theta i : fi22P)) := by
    intro i
    obtain ⟨c, hc⟩ := (fi22Theta i).2
    exact isConj_iff.2 ⟨c, hc⟩
  have hρD : ∀ i, ρ i ∈ CFSG.Sporadic.Fi22.D := by
    intro i
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_fi22OuterZP_fiJP_a.symm.trans (hconjZ i))
    have hρc : ρ i = fiJP.symm c * CFSG.Sporadic.Fi22.a * (fiJP.symm c)⁻¹ := by
      show fiJP.symm (fi22Theta i : fi22P) = _
      rw [← hc, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [hρc]
    exact isConj_iff.2 ⟨fiJP.symm c, rfl⟩
  have hρinj : Function.Injective ρ := by
    intro i j h
    have h' : (fi22Theta i : fi22P) = (fi22Theta j : fi22P) := fiJP.symm.injective h
    exact fi22Theta.injective (Subtype.ext h')
  have hρsurj : ∀ x ∈ CFSG.Sporadic.Fi22.D, ∃ i, ρ i = x := by
    intro x hx
    have h1 : IsConj (fiJP CFSG.Sporadic.Fi22.a) (fiJP x) :=
      (fiJP : CFSG.Sporadic.Fi22.J →* fi22P).map_isConj hx
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_fi22OuterZP_fiJP_a.trans h1)
    have hmem : (fiJP x : fi22P) ∈ fi22ZClass := ⟨c, hc⟩
    refine ⟨fi22Theta.symm ⟨_, hmem⟩, ?_⟩
    show fiJP.symm ((fi22Theta (fi22Theta.symm ⟨_, hmem⟩) : fi22ZClass) : fi22P) = x
    rw [Equiv.apply_symm_apply]
    exact MulEquiv.symm_apply_apply fiJP x
  have hρeq : ∀ i, ρ ((σ : Equiv.Perm (Fin 3510)) i) = g * ρ i * g⁻¹ := by
    intro i
    show fiJP.symm (fi22Theta ((σ : Equiv.Perm (Fin 3510)) i) : fi22P) = _
    rw [fi22Theta_equivariant σ i, map_mul, map_mul, map_inv, hσ, MulEquiv.symm_apply_apply]
  have hbij : Function.Bijective
      (fun i : Fin 3510 => CFSG.Sporadic.Fi22.ptD.symm (⟨ρ i, hρD i⟩ : CFSG.Sporadic.Fi22.D)) := by
    refine ⟨fun i j h => hρinj ?_, fun j => ?_⟩
    · have := CFSG.Sporadic.Fi22.ptD.symm.injective h
      exact congrArg Subtype.val this
    · obtain ⟨i, hi⟩ := hρsurj _ (CFSG.Sporadic.Fi22.ptD j).2
      refine ⟨i, ?_⟩
      have : (⟨ρ i, hρD i⟩ : CFSG.Sporadic.Fi22.D) = CFSG.Sporadic.Fi22.ptD j := Subtype.ext hi
      simp only [this, Equiv.symm_apply_apply]
  let ι : Fin 3510 ≃ Fin 3510 := Equiv.ofBijective _ hbij
  have hιval : ∀ i, CFSG.Sporadic.Fi22.conjPt (ι i).val = ρ i := by
    intro i
    have := CFSG.Sporadic.Fi22.ptD.apply_symm_apply (⟨ρ i, hρD i⟩ : CFSG.Sporadic.Fi22.D)
    exact congrArg Subtype.val this
  have hfix : ∀ i, ((σ : Equiv.Perm (Fin 3510)) i = i) ↔ g • (ι i) = ι i := by
    intro i
    have hsm : ∀ j : Fin 3510, g • j = j ↔
        g * CFSG.Sporadic.Fi22.conjPt j.val * g⁻¹ = CFSG.Sporadic.Fi22.conjPt j.val := by
      intro j
      rw [← CFSG.Sporadic.Fi22.conjPt_smul g j]
      constructor
      · intro h
        rw [h]
      · intro h
        have : CFSG.Sporadic.Fi22.ptD (g • j) = CFSG.Sporadic.Fi22.ptD j := Subtype.ext h
        exact CFSG.Sporadic.Fi22.ptD.injective this
    rw [hsm, hιval]
    constructor
    · intro h
      rw [← hρeq, h]
    · intro h
      exact hρinj (by rw [hρeq]; exact h)
  rw [fixP, Fintype.card_congr (Equiv.subtypeEquiv (p := fun i => (σ : Equiv.Perm (Fin 3510)) i = i)
    (q := fun j => g • j = j) ι hfix), Fintype.card_subtype]
  rfl

theorem fixP_fiJP_mul_of_comm {x y : CFSG.Sporadic.Fi22.J}
    (hx : x ∈ CFSG.Sporadic.Fi22.D) (hy : y ∈ CFSG.Sporadic.Fi22.D) (hne : x ≠ y)
    (hc : x * y = y * x) :
    fixP ((fiJP (x * y) : fi22P) : Equiv.Perm (Fin 3510)) = 182 := by
  rw [fixP_fiJP, fixD_mul_of_comm hx hy hne hc]

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
