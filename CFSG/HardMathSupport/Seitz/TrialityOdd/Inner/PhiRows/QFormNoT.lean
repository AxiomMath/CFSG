module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.QForm
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ExtractUNoT

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed

section QFormNoT


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

include hσ in
theorem exists_short_of_short_pair
    [Finite K]
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hlong : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (a₂ a₄ : K)
    (hs : d4X hσ 2 a₂ * d4X hσ 4 a₄ ∈ H) (hne : a₂ ≠ 0 ∨ a₄ ≠ 0) : HasShortRoot H := by
  have e1 : d4X hσ 1 (0 : fixedField σ.toRingHom) = 1 := (d4X_eq_one_iff hσ).2 rfl
  have e3 : d4X hσ 3 (0 : fixedField σ.toRingHom) = 1 := (d4X_eq_one_iff hσ).2 rfl
  have e5 : d4X hσ 5 (0 : fixedField σ.toRingHom) = 1 := (d4X_eq_one_iff hσ).2 rfl
  refine exists_short_of_Q_element hσ ha H hlong 0 0 0 a₂ a₄ ?_ hne
  rw [e1, e3, e5]
  convert hs using 1

include hσ in
theorem exists_short_of_Q_point
    [Finite K]
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hlong : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (a₂ a₄ : K) (hne : a₂ ≠ 0 ∨ a₄ ≠ 0)
    (hX : ∀ x ∈ hexGroup (twistedX σ.toRingHom) (-4),
      (d4X hσ 2 a₂ * d4X hσ 4 a₄) * x * (d4X hσ 2 a₂ * d4X hσ 4 a₄)⁻¹ ∈ H) : HasShortRoot H := by
  have R := d4Rel_model hσ
  have RG := d4RGD2 σ.toRingHom hσ
  obtain ⟨b, hb⟩ := ha
  obtain ⟨h, hhT, hhS, hfix2, hfix4⟩ := exists_theta_torus hσ b hb
  set s : twistedGroup σ.toRingHom := d4X hσ 2 a₂ * d4X hσ 4 a₄ with hs
  have hsU : s ∈ posUnipotent (g2Shape (twistedX σ.toRingHom)) :=
    mul_mem (d4X_mem_posUnipotent hσ 2 a₂) (d4X_mem_posUnipotent hσ 4 a₄)
  have hconj : h ∈ H.comap (MulAut.conj s).toMonoidHom := by
    have hle : hexGroup (twistedX σ.toRingHom) 4 ⊔ hexGroup (twistedX σ.toRingHom) (-4) ≤
        H.comap (MulAut.conj s).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro x hx
        have hc := commute_posUnipotent_hexGroup_four hσ hsU hx
        have : s * x * s⁻¹ = x := by rw [hc]; group
        show s * x * s⁻¹ ∈ H
        rw [this]
        exact hlong (root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (4 : ℤ)) (by norm_num) hx)
      · intro x hx
        exact hX x hx
    exact hle hhS
  have hconj' : s * h * s⁻¹ ∈ H := hconj
  have hhH : h ∈ H := hlong (by
    refine (sup_le ?_ ?_ : hexGroup (twistedX σ.toRingHom) 4 ⊔ hexGroup (twistedX σ.toRingHom) (-4) ≤
      longSub 6 (hexGroup (twistedX σ.toRingHom))) hhS
    · exact fun x hx => root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (4 : ℤ)) (by norm_num) hx
    · exact fun x hx => root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (-4 : ℤ)) (by norm_num) hx)
  have hyH : s * h * s⁻¹ * h⁻¹ ∈ H := H.mul_mem hconj' (H.inv_mem hhH)
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : K, h * d4X hσ 2 a₂ * h⁻¹ = d4X hσ 2 c₂ := by
    have hm := RG.invariant 3 ⟨by norm_num, by norm_num⟩ h hhT _
      (d4X_mem_hexGroup' hσ 2 a₂ (by norm_num))
    obtain ⟨c, hc⟩ := (mem_hexGroup_iff' hσ 2 (by norm_num : ((2 : Fin 6) : ℤ) + 1 = 3)).1 hm
    exact ⟨c, hc.symm⟩
  obtain ⟨c₄, hc₄⟩ : ∃ c₄ : K, h * d4X hσ 4 a₄ * h⁻¹ = d4X hσ 4 c₄ := by
    have hm := RG.invariant 5 ⟨by norm_num, by norm_num⟩ h hhT _
      (d4X_mem_hexGroup' hσ 4 a₄ (by norm_num))
    obtain ⟨c, hc⟩ := (mem_hexGroup_iff' hσ 4 (by norm_num : ((4 : Fin 6) : ℤ) + 1 = 5)).1 hm
    exact ⟨c, hc.symm⟩
  have hd2 : a₂ ≠ 0 → a₂ - c₂ ≠ 0 := by
    intro ha₂ hz
    have : c₂ = a₂ := (sub_eq_zero.1 hz).symm
    apply ha₂
    apply hfix2 a₂
    rw [hc₂, this]
  have hd4 : a₄ ≠ 0 → a₄ - c₄ ≠ 0 := by
    intro ha₄ hz
    have : c₄ = a₄ := (sub_eq_zero.1 hz).symm
    apply ha₄
    apply hfix4 a₄
    rw [hc₄, this]
  set d₂ : K := a₂ - c₂ with hd₂
  set d₄ : K := a₄ - c₄ with hd₄
  have hX2 : d4X hσ 2 d₂ = d4X hσ 2 a₂ * (d4X hσ 2 c₂)⁻¹ := by
    refine eq_mul_inv_of_mul_eq ?_
    exact (d4X_add hσ 2 d₂ c₂).symm.trans (congrArg (d4X hσ 2) (sub_add_cancel a₂ c₂))
  have hX4 : d4X hσ 4 d₄ = d4X hσ 4 a₄ * (d4X hσ 4 c₄)⁻¹ := by
    refine eq_mul_inv_of_mul_eq ?_
    exact (d4X_add hσ 4 d₄ c₄).symm.trans (congrArg (d4X hσ 4) (sub_add_cancel a₄ c₄))
  obtain ⟨e, he⟩ : ∃ e : fixedField σ.toRingHom,
      ⁅d4X hσ 4 d₄, (d4X hσ 2 c₂)⁻¹⁆ = d4X hσ 3 e := by
    have h24 := R.r24 (-c₂) d₄
    dsimp only at h24
    refine ⟨-(-d43Tr hσ (-c₂ * d₄)), ?_⟩
    have n2 : d4X hσ 2 (-c₂) = (d4X hσ 2 c₂)⁻¹ := d4X_neg' hσ 2 c₂
    have step1 : ⁅d4X hσ 4 d₄, (d4X hσ 2 c₂)⁻¹⁆ = (⁅d4X hσ 2 (-c₂), d4X hσ 4 d₄⁆)⁻¹ := by
      rw [← n2]
      exact (commutatorElement_inv _ _).symm
    exact step1.trans ((congrArg (·⁻¹) h24).trans (d4X_neg' hσ 3 (-d43Tr hσ (-c₂ * d₄))).symm)
  have hsh : s * h * s⁻¹ * h⁻¹ = d4X hσ 3 e * (d4X hσ 2 d₂ * d4X hσ 4 d₄) := by
    have e1 : h * s * h⁻¹ = d4X hσ 2 c₂ * d4X hσ 4 c₄ := by
      rw [hs, ← hc₂, ← hc₄]; group
    have e2 : s * h * s⁻¹ * h⁻¹ = s * (d4X hσ 2 c₂ * d4X hσ 4 c₄)⁻¹ := by
      rw [← e1]; group
    have c23 : d4X hσ 2 a₂ * d4X hσ 3 e = d4X hσ 3 e * d4X hσ 2 a₂ := (R.c23 a₂ e).eq
    have hcomm : d4X hσ 4 d₄ * (d4X hσ 2 c₂)⁻¹ =
        d4X hσ 3 e * ((d4X hσ 2 c₂)⁻¹ * d4X hσ 4 d₄) := by
      rw [← he, commutatorElement_def]; group
    calc s * h * s⁻¹ * h⁻¹ = s * (d4X hσ 2 c₂ * d4X hσ 4 c₄)⁻¹ := e2
      _ = d4X hσ 2 a₂ * (d4X hσ 4 a₄ * (d4X hσ 4 c₄)⁻¹) * (d4X hσ 2 c₂)⁻¹ := by rw [hs]; group
      _ = d4X hσ 2 a₂ * d4X hσ 4 d₄ * (d4X hσ 2 c₂)⁻¹ := by rw [hX4]
      _ = d4X hσ 2 a₂ * (d4X hσ 4 d₄ * (d4X hσ 2 c₂)⁻¹) := by group
      _ = d4X hσ 2 a₂ * (d4X hσ 3 e * ((d4X hσ 2 c₂)⁻¹ * d4X hσ 4 d₄)) := by rw [hcomm]
      _ = (d4X hσ 2 a₂ * d4X hσ 3 e) * ((d4X hσ 2 c₂)⁻¹ * d4X hσ 4 d₄) := by group
      _ = d4X hσ 3 e * (d4X hσ 2 a₂ * (d4X hσ 2 c₂)⁻¹ * d4X hσ 4 d₄) := by rw [c23]; group
      _ = d4X hσ 3 e * (d4X hσ 2 d₂ * d4X hσ 4 d₄) := by rw [hX2]
  have hX3 : d4X hσ 3 e ∈ H :=
    hlong (root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (4 : ℤ)) (by norm_num)
      (d4X_mem_hexGroup' hσ 3 e (by norm_num)))
  have hpair : d4X hσ 2 d₂ * d4X hσ 4 d₄ ∈ H := by
    have : d4X hσ 2 d₂ * d4X hσ 4 d₄ = (d4X hσ 3 e)⁻¹ * (s * h * s⁻¹ * h⁻¹) := by
      rw [hsh]; group
    rw [this]
    exact H.mul_mem (H.inv_mem hX3) hyH
  refine exists_short_of_short_pair hσ ⟨b, hb⟩ H hlong d₂ d₄ hpair ?_
  rcases hne with h | h
  · exact Or.inl (hd2 h)
  · exact Or.inr (hd4 h)

end QFormNoT

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
