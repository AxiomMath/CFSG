module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.MaxL
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.QFormNoT
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.MaxLAbstractNoT

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

section MaxLNoT


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)


@[expose] def ShortUpToNL (H₀ : Subgroup (twistedGroup σ.toRingHom)) : Prop :=
  ∃ m ∈ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)),
    HasShortRoot (H₀.map (MulAut.conj m).toMonoidHom)

theorem shortUpToNL_of_hasShort {H₀ : Subgroup (twistedGroup σ.toRingHom)}
    (h : HasShortRoot H₀) : ShortUpToNL (σ := σ) H₀ := by
  refine ⟨1, one_mem _, ?_⟩
  obtain ⟨k, hk, x, hx, hxH, hx1⟩ := h
  exact ⟨k, hk, x, hx, ⟨x, hxH, by show (1 : twistedGroup σ.toRingHom) * x * 1⁻¹ = x; group⟩, hx1⟩

theorem shortUpToNL_pullback {r : twistedGroup σ.toRingHom}
    (hr : r ∈ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)))
    (H₀ : Subgroup (twistedGroup σ.toRingHom))
    (h : ShortUpToNL (σ := σ) (H₀.map (MulAut.conj r).toMonoidHom)) : ShortUpToNL (σ := σ) H₀ := by
  obtain ⟨m, hm, hs⟩ := h
  refine ⟨m * r, mul_mem hm hr, ?_⟩
  have e : (H₀.map (MulAut.conj r).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      H₀.map (MulAut.conj (m * r)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  rwa [← e]

include hσ in
theorem r_mem_normalizer {r₁ r₂ : twistedGroup σ.toRingHom} {H : Subgroup (twistedGroup σ.toRingHom)}
    {U : Subgroup (twistedGroup σ.toRingHom)}
    (R : RGD2 6 H r₁ r₂ U (hexGroup (twistedX σ.toRingHom))) :
    r₁ ∈ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)) ∧
    r₂ ∈ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)) := by
  have hn : ∀ {r : twistedGroup σ.toRingHom}, GoodActEven 6 (hexGroup (twistedX σ.toRingHom)) r →
      r ∈ Subgroup.normalizer
        (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_longSub (by norm_num) (by norm_num) hr hx
    · intro hx
      have := conj_mem_longSub (by norm_num) (by norm_num) hr.inv hx
      have e : r⁻¹ * (r * x * r⁻¹) * r⁻¹⁻¹ = x := by group
      rwa [e] at this
  exact ⟨hn (R.goodActEven_r₁ (by norm_num : 6 % 2 = 0)),
    hn (R.goodActEven_r₂ (by norm_num : 6 % 2 = 0))⟩

section Comm


include hσ in
theorem pointClosedP_neg4 [Finite K]
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1) :
    PointClosedP (ShortUpToNL (σ := σ)) (posUnipotent (g2Shape (twistedX σ.toRingHom)))
      (hexGroup (twistedX σ.toRingHom)) (-4) := by
  have R := d4Rel_model hσ
  have RG := d4RGD2 σ.toRingHom hσ
  obtain ⟨-, -, -, -, c14m⟩ := comm_hex_neg hσ
  intro H₀ hL v hv hH hnP
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
  refine shortUpToNL_of_hasShort (exists_short_of_Q_point hσ ha H₀ hL a₂ a₄ ?_ ?_)
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
theorem shortUpToNL_of_point_not_mem [Finite K]
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hL : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    {g x : twistedGroup σ.toRingHom} (hg : g ∈ H)
    (hx : x ∈ hexGroup (twistedX σ.toRingHom) 4)
    (hn : g * x * g⁻¹ ∉ PLset (hexGroup (twistedX σ.toRingHom))) : ShortUpToNL (σ := σ) H := by
  have RG := d4RGD2 σ.toRingHom hσ
  obtain ⟨c66, c64, c16, c12, -⟩ := comm_hex_neg hσ
  obtain ⟨hn₁, hn₂⟩ := r_mem_normalizer hσ RG
  have chain := pointClosedP_chain RG (P := ShortUpToNL (σ := σ))
    (shortUpToNL_pullback hn₁) (shortUpToNL_pullback hn₂) c66 c64 c16 c12 (pointClosedP_neg4 hσ ha)
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
  · exact chain.2.2.2 H hL v hv hHk hfin
  · exfalso
    apply hnP
    have hc := commute_posUnipotent_hexGroup_four hσ hv hx'
    have e : v * x' * v⁻¹ = x' := by rw [hc]; group
    rw [e]
    exact ⟨1, one_mem _, 4, ⟨by norm_num, by norm_num⟩, by norm_num, x', hx', by group⟩
  · exact chain.2.2.1 H hL v hv hHk hfin
  · exact chain.1 H hL v hv hHk hfin
  · exact pointClosedP_neg4 hσ ha H hL v hv hHk hfin
  · exact chain.2.1 H hL v hv hHk hfin

include hσ in
theorem shortUpToNL_of_not_normalizes [Finite K]
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hL : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    {j : twistedGroup σ.toRingHom} (hj : j ∈ H)
    (hjN : j ∉ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom))) : ShortUpToNL (σ := σ) H := by
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
  refine shortUpToNL_of_point_not_mem hσ ha H hL (g := j * ℓ * m⁻¹) (x := m * y * m⁻¹)
    (mul_mem (mul_mem hj (hL hℓ)) (inv_mem (hL hm))) (hmy y hy) ?_
  have e : j * ℓ * m⁻¹ * (m * y * m⁻¹) * (j * ℓ * m⁻¹)⁻¹ = j * (ℓ * y * ℓ⁻¹) * j⁻¹ := by group
  rw [e]
  exact hzn

end Comm

end MaxLNoT

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
