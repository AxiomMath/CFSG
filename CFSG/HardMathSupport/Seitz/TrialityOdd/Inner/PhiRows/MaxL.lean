module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.QForm
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.MaxLAbstract
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.ConjStableNormalizer

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

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed

section MaxL


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

section Comm


include hσ in
theorem comm_hex_pos :
    (∀ x ∈ hexGroup (twistedX σ.toRingHom) 6, ∀ y ∈ hexGroup (twistedX σ.toRingHom) 6, x * y = y * x) ∧
    (∀ x ∈ hexGroup (twistedX σ.toRingHom) 4, ∀ y ∈ hexGroup (twistedX σ.toRingHom) 6, x * y = y * x) ∧
    (∀ x ∈ hexGroup (twistedX σ.toRingHom) 5, ∀ y ∈ hexGroup (twistedX σ.toRingHom) 6, x * y = y * x) ∧
    (∀ x ∈ hexGroup (twistedX σ.toRingHom) 1, ∀ y ∈ hexGroup (twistedX σ.toRingHom) 2, x * y = y * x) ∧
    (∀ x ∈ hexGroup (twistedX σ.toRingHom) 1, ∀ y ∈ hexGroup (twistedX σ.toRingHom) 4, x * y = y * x) := by
  have R := d4Rel_model hσ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_hexGroup_iff' hσ 5 (by norm_num : ((5 : Fin 6) : ℤ) + 1 = 6)).1 hx
    obtain ⟨b, rfl⟩ := (mem_hexGroup_iff' hσ 5 (by norm_num : ((5 : Fin 6) : ℤ) + 1 = 6)).1 hy
    rw [← d4X_add hσ 5, ← d4X_add hσ 5]
    exact congrArg (d4X hσ 5) (add_comm a b)
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_hexGroup_iff' hσ 3 (by norm_num : ((3 : Fin 6) : ℤ) + 1 = 4)).1 hx
    obtain ⟨b, rfl⟩ := (mem_hexGroup_iff' hσ 5 (by norm_num : ((5 : Fin 6) : ℤ) + 1 = 6)).1 hy
    exact (R.c35 a b).eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_hexGroup_iff' hσ 4 (by norm_num : ((4 : Fin 6) : ℤ) + 1 = 5)).1 hx
    obtain ⟨b, rfl⟩ := (mem_hexGroup_iff' hσ 5 (by norm_num : ((5 : Fin 6) : ℤ) + 1 = 6)).1 hy
    exact (R.c45 a b).eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_hexGroup_iff' hσ 0 (by norm_num : ((0 : Fin 6) : ℤ) + 1 = 1)).1 hx
    obtain ⟨b, rfl⟩ := (mem_hexGroup_iff' hσ 1 (by norm_num : ((1 : Fin 6) : ℤ) + 1 = 2)).1 hy
    exact (R.c01 a b).eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_hexGroup_iff' hσ 0 (by norm_num : ((0 : Fin 6) : ℤ) + 1 = 1)).1 hx
    obtain ⟨b, rfl⟩ := (mem_hexGroup_iff' hσ 3 (by norm_num : ((3 : Fin 6) : ℤ) + 1 = 4)).1 hy
    exact (R.c03 a b).eq

include hσ in
theorem comm_hex_neg :
    (∀ b ∈ hexGroup (twistedX σ.toRingHom) (-6), ∀ z ∈ hexGroup (twistedX σ.toRingHom) (-6),
      b * z = z * b) ∧
    (∀ b ∈ hexGroup (twistedX σ.toRingHom) (-6), ∀ z ∈ hexGroup (twistedX σ.toRingHom) (-4),
      b * z = z * b) ∧
    (∀ b ∈ hexGroup (twistedX σ.toRingHom) (-1), ∀ z ∈ hexGroup (twistedX σ.toRingHom) 6,
      b * z = z * b) ∧
    (∀ b ∈ hexGroup (twistedX σ.toRingHom) (-1), ∀ z ∈ hexGroup (twistedX σ.toRingHom) (-2),
      b * z = z * b) ∧
    (∀ b ∈ hexGroup (twistedX σ.toRingHom) 1, ∀ z ∈ hexGroup (twistedX σ.toRingHom) (-4),
      b * z = z * b) := by
  have R := d4RGD2 σ.toRingHom hσ
  obtain ⟨c55, c35, c45, c01, c03⟩ := comm_hex_pos hσ
  have n₀ := actsPos_rot_six R
  obtain ⟨w₅, -, w₁, -, w₃, -, -, -, ⟨hw₃, -⟩⟩ := exists_three_weyl R
  have hm₂ := actsPos_r₂' R
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := commute_transfer n₀ (q₁ := 11) (q₂ := 11) (p₁ := 5) (p₂ := 5)
      (by decide) (by decide) (by
        intro x hx y hy
        rw [show Rt 6 5 = 6 by decide] at hx hy
        exact c55 x hx y hy)
    rw [show Rt 6 11 = -6 by decide] at h
    exact h
  · have h := commute_transfer n₀ (q₁ := 11) (q₂ := 9) (p₁ := 5) (p₂ := 3)
      (by decide) (by decide) (by
        intro x hx y hy
        rw [show Rt 6 5 = 6 by decide] at hx
        rw [show Rt 6 3 = 4 by decide] at hy
        exact (c35 y hy x hx).symm)
    rw [show Rt 6 11 = -6 by decide, show Rt 6 9 = -4 by decide] at h
    exact h
  · have m := ActsPos.mul n₀ hm₂
    have h := commute_transfer m (q₁ := 6) (q₂ := 5) (p₁ := 4) (p₂ := 5)
      (by decide) (by decide) (by
        intro x hx y hy
        rw [show Rt 6 4 = 5 by decide] at hx
        rw [show Rt 6 5 = 6 by decide] at hy
        exact c45 x hx y hy)
    rw [show Rt 6 6 = -1 by decide, show Rt 6 5 = 6 by decide] at h
    exact h
  · have h := commute_transfer n₀ (q₁ := 6) (q₂ := 7) (p₁ := 0) (p₂ := 1)
      (by decide) (by decide) (by
        intro x hx y hy
        rw [show Rt 6 0 = 1 by decide] at hx
        rw [show Rt 6 1 = 2 by decide] at hy
        exact c01 x hx y hy)
    rw [show Rt 6 6 = -1 by decide, show Rt 6 7 = -2 by decide] at h
    exact h
  · have h := commute_transfer hw₃ (q₁ := 0) (q₂ := 9) (p₁ := 0) (p₂ := 3)
      (by decide) (by decide) (by
        intro x hx y hy
        rw [show Rt 6 0 = 1 by decide] at hx
        rw [show Rt 6 3 = 4 by decide] at hy
        exact c03 x hx y hy)
    rw [show Rt 6 0 = 1 by decide, show Rt 6 9 = -4 by decide] at h
    exact h

include hσ in
theorem pointClosed_neg4 [Finite K] (h2 : (2 : K) ≠ 0)
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1) :
    PointClosed (⨆ i, hHat σ.toRingHom i) (posUnipotent (g2Shape (twistedX σ.toRingHom)))
      (hexGroup (twistedX σ.toRingHom)) (-4) := by
  have R := d4Rel_model hσ
  have RG := d4RGD2 σ.toRingHom hσ
  obtain ⟨-, -, -, -, c14m⟩ := comm_hex_neg hσ
  intro H₀ hL hT v hv hH hnP
  obtain ⟨a, ha1, c₂, h₂, c₃, h₃, c₄, h₄, c₅, h₅, c₆, h₆, rfl⟩ := U_decomp_right RG hv
  obtain ⟨e₁, rfl⟩ := (mem_hexGroup_iff' hσ 1 (by norm_num : ((1 : Fin 6) : ℤ) + 1 = 2)).1 h₂
  obtain ⟨a₂, rfl⟩ := (mem_hexGroup_iff' hσ 2 (by norm_num : ((2 : Fin 6) : ℤ) + 1 = 3)).1 h₃
  obtain ⟨e₃, rfl⟩ := (mem_hexGroup_iff' hσ 3 (by norm_num : ((3 : Fin 6) : ℤ) + 1 = 4)).1 h₄
  obtain ⟨a₄, rfl⟩ := (mem_hexGroup_iff' hσ 4 (by norm_num : ((4 : Fin 6) : ℤ) + 1 = 5)).1 h₅
  obtain ⟨e₅, rfl⟩ := (mem_hexGroup_iff' hσ 5 (by norm_num : ((5 : Fin 6) : ℤ) + 1 = 6)).1 h₆
  set q : twistedGroup σ.toRingHom :=
    d4X hσ 1 e₁ * (d4X hσ 2 a₂ * (d4X hσ 3 e₃ * (d4X hσ 4 a₄ * d4X hσ 5 e₅))) with hq
  set ℓ : twistedGroup σ.toRingHom := d4X hσ 1 e₁ * (d4X hσ 3 e₃ * d4X hσ 5 e₅) with hℓ
  set s : twistedGroup σ.toRingHom := d4X hσ 2 a₂ * d4X hσ 4 a₄ with hs
  have hlongX : ∀ (i : Fin 6) (c : d43Par σ.toRingHom i) (k : ℤ), (i : ℤ) + 1 = k → k % 2 = 0 →
      IsRoot 6 k → d4X hσ i c ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) :=
    fun i c k hk hk2 hkr => root_le_longSub hkr hk2 (d4X_mem_hexGroup' hσ i c hk)
  have hℓL : ℓ ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) :=
    mul_mem (hlongX 1 e₁ 2 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩)
      (mul_mem (hlongX 3 e₃ 4 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩)
        (hlongX 5 e₅ 6 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩))
  have hqℓs : q = ℓ * s := by
    have c23 : d4X hσ 2 a₂ * d4X hσ 3 e₃ = d4X hσ 3 e₃ * d4X hσ 2 a₂ := (R.c23 a₂ e₃).eq
    have c45 : d4X hσ 4 a₄ * d4X hσ 5 e₅ = d4X hσ 5 e₅ * d4X hσ 4 a₄ := (R.c45 a₄ e₅).eq
    have c25 : d4X hσ 2 a₂ * d4X hσ 5 e₅ = d4X hσ 5 e₅ * d4X hσ 2 a₂ := (R.c25 a₂ e₅).eq
    rw [hq, hℓ, hs]
    calc d4X hσ 1 e₁ * (d4X hσ 2 a₂ * (d4X hσ 3 e₃ * (d4X hσ 4 a₄ * d4X hσ 5 e₅)))
        = d4X hσ 1 e₁ * ((d4X hσ 2 a₂ * d4X hσ 3 e₃) * (d4X hσ 4 a₄ * d4X hσ 5 e₅)) := by group
      _ = d4X hσ 1 e₁ * (d4X hσ 3 e₃ * ((d4X hσ 2 a₂ * (d4X hσ 5 e₅ * d4X hσ 4 a₄)))) := by
          rw [c23, c45]; group
      _ = d4X hσ 1 e₁ * (d4X hσ 3 e₃ * ((d4X hσ 2 a₂ * d4X hσ 5 e₅) * d4X hσ 4 a₄)) := by group
      _ = d4X hσ 1 e₁ * (d4X hσ 3 e₃ * ((d4X hσ 5 e₅ * d4X hσ 2 a₂) * d4X hσ 4 a₄)) := by rw [c25]
      _ = d4X hσ 1 e₁ * (d4X hσ 3 e₃ * d4X hσ 5 e₅) * (d4X hσ 2 a₂ * d4X hσ 4 a₄) := by group
  have hvq : ∀ y ∈ hexGroup (twistedX σ.toRingHom) (-4), q * a * y * (q * a)⁻¹ = q * y * q⁻¹ := by
    intro y hy
    have hc := c14m a ha1 y hy
    calc q * a * y * (q * a)⁻¹ = q * (a * y * a⁻¹) * q⁻¹ := by group
      _ = q * y * q⁻¹ := by rw [hc]; group
  refine eq_top_of_Q_point hσ h2 ha H₀ hL hT a₂ a₄ ?_ ?_
  · by_contra hcon
    push Not at hcon
    obtain ⟨h20, h40⟩ := hcon
    obtain ⟨y, hy, hyn⟩ := hnP
    apply hyn
    have e2 : d4X hσ 2 a₂ = 1 := (d4X_eq_one_iff hσ).2 h20
    have e4 : d4X hσ 4 a₄ = 1 := (d4X_eq_one_iff hσ).2 h40
    have hs1 : s = 1 := by rw [hs, e2, e4]; group
    refine ⟨q, ?_, -4, ⟨by norm_num, by norm_num⟩, by norm_num, y, hy, hvq y hy ▸ rfl⟩
    rw [hqℓs, hs1, mul_one]
    exact hℓL
  · intro y hy
    have h1 := hH y hy
    rw [hvq y hy] at h1
    have e : s * y * s⁻¹ = ℓ⁻¹ * (q * y * q⁻¹) * ℓ := by rw [hqℓs]; group
    rw [e]
    exact H₀.mul_mem (H₀.mul_mem (H₀.inv_mem (hL hℓL)) h1) (hL hℓL)

include hσ in
theorem eq_top_of_point_not_mem [Finite K] (h2 : (2 : K) ≠ 0)
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hL : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (hT : (⨆ i, hHat σ.toRingHom i) ≤ H) {g x : twistedGroup σ.toRingHom} (hg : g ∈ H)
    (hx : x ∈ hexGroup (twistedX σ.toRingHom) 4)
    (hn : g * x * g⁻¹ ∉ PLset (hexGroup (twistedX σ.toRingHom))) : H = ⊤ := by
  have RG := d4RGD2 σ.toRingHom hσ
  obtain ⟨c66, c64, c16, c12, -⟩ := comm_hex_neg hσ
  have chain := pointClosed_chain RG c66 c64 c16 c12 (pointClosed_neg4 hσ h2 ha)
  obtain ⟨k, hk, v, hv, hfor, hback⟩ := bruhat_point hσ g
  have hX4 : ∀ y ∈ hexGroup (twistedX σ.toRingHom) 4, y ∈ H := fun y hy =>
    hL (root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (4 : ℤ)) (by norm_num) hy)
  have hHk : ∀ y' ∈ hexGroup (twistedX σ.toRingHom) k, v * y' * v⁻¹ ∈ H := by
    intro y' hy'
    obtain ⟨y, hy, he⟩ := hback y' hy'
    rw [← he]
    exact H.mul_mem (H.mul_mem hg (hX4 y hy)) (H.inv_mem hg)
  obtain ⟨x', hx', hxx'⟩ := hfor x hx
  have hnP : v * x' * v⁻¹ ∉ PLset (hexGroup (twistedX σ.toRingHom)) := by
    rw [← hxx']; exact hn
  have hfin : ∃ y ∈ hexGroup (twistedX σ.toRingHom) k,
      v * y * v⁻¹ ∉ PLset (hexGroup (twistedX σ.toRingHom)) := ⟨x', hx', hnP⟩
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact chain.2.2.2 H hL hT v hv hHk hfin
  · exfalso
    apply hnP
    have hc := commute_posUnipotent_hexGroup_four hσ hv hx'
    have e : v * x' * v⁻¹ = x' := by rw [hc]; group
    rw [e]
    exact ⟨1, one_mem _, 4, ⟨by norm_num, by norm_num⟩, by norm_num, x', hx', by group⟩
  · exact chain.2.2.1 H hL hT v hv hHk hfin
  · exact chain.1 H hL hT v hv hHk hfin
  · exact pointClosed_neg4 hσ h2 ha H hL hT v hv hHk hfin
  · exact chain.2.1 H hL hT v hv hHk hfin

include hσ in
theorem eq_top_of_not_normalizes [Finite K] (h2 : (2 : K) ≠ 0)
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hL : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (hT : (⨆ i, hHat σ.toRingHom i) ≤ H) {j : twistedGroup σ.toRingHom} (hj : j ∈ H)
    (hjN : j ∉ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom))) : H = ⊤ := by
  have RG := d4RGD2 σ.toRingHom hσ
  have hgen : Subgroup.closure (PLset (hexGroup (twistedX σ.toRingHom))) =
      longSub 6 (hexGroup (twistedX σ.toRingHom)) := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨ℓ, hℓ, k, hk, hk2, y, hy, rfl⟩
      exact mul_mem (mul_mem hℓ (root_le_longSub hk hk2 hy)) (inv_mem hℓ)
    · refine Subgroup.closure_mono ?_
      rintro x ⟨k, hk, hk2, hx⟩
      exact ⟨1, one_mem _, k, hk, hk2, x, hx, by group⟩
  obtain ⟨z, hzP, hzn⟩ := CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.exists_generator_conj_not_mem_of_not_normalizes
    (longSub 6 (hexGroup (twistedX σ.toRingHom))) (PLset (hexGroup (twistedX σ.toRingHom))) hgen j hjN
  obtain ⟨ℓ, hℓ, k, hk, hk2, y, hy, rfl⟩ := hzP
  obtain ⟨m, hm, hmy⟩ := exists_conj_to_four RG hk hk2
  refine eq_top_of_point_not_mem hσ h2 ha H hL hT (g := j * ℓ * m⁻¹) (x := m * y * m⁻¹)
    (mul_mem (mul_mem hj (hL hℓ)) (inv_mem (hL hm))) (hmy y hy) ?_
  have e : j * ℓ * m⁻¹ * (m * y * m⁻¹) * (j * ℓ * m⁻¹)⁻¹ = j * (ℓ * y * ℓ⁻¹) * j⁻¹ := by group
  rw [e]
  exact hzn

end Comm

end MaxL

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
