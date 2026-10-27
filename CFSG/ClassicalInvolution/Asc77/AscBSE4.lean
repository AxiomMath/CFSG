module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscBSD4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSE

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Asc77 (ih8_eq_of_map_eq)
open CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false

section SpinFund

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure SpinFund (Q : QuadraticForm F V) (𝓕 : Set (Subgroup (spinGroup Q))) : Prop where
  odd : Odd (Nat.card F)
  range : (spinAction Q).range = elementaryGroup Q
  scalar : CenterScalar Q
  nontrivial : Nontrivial V
  corr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q
  lift : ∀ L ∈ fundSet Q, ∃ R ∈ 𝓕, R.map (spinAction Q) = L
  perf : ∀ R ∈ 𝓕, R ≤ ⁅R, R⁆
  nc : ∀ R ∈ 𝓕, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1
  single : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g, R' = conjSub g R
  conj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕

namespace SpinFund

variable {𝓕 : Set (Subgroup (spinGroup Q))} (h : SpinFund Q 𝓕)

include h

theorem inj {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕) {r : spinGroup Q} (hr : r ∈ R)
    (h1 : spinAction Q r = 1) : r = 1 :=
  h.nc R hR r hr (ker_spinAction_le_center Q (MonoidHom.mem_ker.mpr h1))

theorem fund_of_inv {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕) {r : spinGroup Q}
    (hr : r ∈ R) (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    IsFundamental Q (R.map (spinAction Q)) (spinAction Q r) := by
  obtain ⟨i, hi⟩ := h.corr R hR
  have hmem : spinAction Q r ∈ R.map (spinAction Q) := Subgroup.mem_map_of_mem _ hr
  have hsq : spinAction Q r * spinAction Q r = 1 := by rw [← map_mul, hr2, map_one]
  have hne : spinAction Q r ≠ 1 := fun h1 => hr1 (h.inj hR hr h1)
  have hord : orderOf (spinAction Q r) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have := hi.eq_of_orderOf_eq_two h.odd hmem hord
  rw [this]
  exact hi

theorem inv_unique {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕) {x y : spinGroup Q}
    (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hy : y ∈ R) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    x = y := by
  have hfx := h.fund_of_inv hR hx hx2 hx1
  have hmem : spinAction Q y ∈ R.map (spinAction Q) := Subgroup.mem_map_of_mem _ hy
  have hsq : spinAction Q y * spinAction Q y = 1 := by rw [← map_mul, hy2, map_one]
  have hne : spinAction Q y ≠ 1 := fun h1 => hy1 (h.inj hR hy h1)
  have hord : orderOf (spinAction Q y) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have h1 : spinAction Q y = spinAction Q x := hfx.eq_of_orderOf_eq_two h.odd hmem hord
  have h2 : x⁻¹ * y ∈ R := R.mul_mem (R.inv_mem hx) hy
  have h3 : x⁻¹ * y = 1 := h.inj hR h2 (by rw [map_mul, map_inv, h1, inv_mul_cancel])
  exact inv_mul_eq_one.mp h3

theorem false_of_three {R₀ R₁ R₂ : Subgroup (spinGroup Q)} (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕)
    (h₂ : R₂ ∈ 𝓕) (e01 : R₀ ≠ R₁) (e02 : R₀ ≠ R₂) (e12 : R₁ ≠ R₂) {r₀ r₁ r₂ : spinGroup Q}
    (hr₀ : r₀ ∈ R₀) (hr₀2 : r₀ * r₀ = 1) (hr₀1 : r₀ ≠ 1) (hr₁ : r₁ ∈ R₁) (hr₁2 : r₁ * r₁ = 1)
    (hr₁1 : r₁ ≠ 1) (hr₂ : r₂ ∈ R₂) (hr₂2 : r₂ * r₂ = 1) (hr₂1 : r₂ ≠ 1)
    (s01 : spinAction Q r₁ = spinAction Q r₀) (s02 : spinAction Q r₂ = spinAction Q r₀) :
    False := by
  have f₀ := h.fund_of_inv h₀ hr₀ hr₀2 hr₀1
  have f₁ : IsFundamental Q (R₁.map (spinAction Q)) (spinAction Q r₀) :=
    s01 ▸ h.fund_of_inv h₁ hr₁ hr₁2 hr₁1
  have f₂ : IsFundamental Q (R₂.map (spinAction Q)) (spinAction Q r₀) :=
    s02 ▸ h.fund_of_inv h₂ hr₂ hr₂2 hr₂1
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin h.odd f₀
  have ker := ker_spinAction_le_center Q
  rcases huniq _ f₁ with a1 | a1
  · exact e01 (ih8_eq_of_map_eq _ ker (h.perf R₀ h₀) (h.perf R₁ h₁) a1.symm)
  rcases huniq _ f₂ with a2 | a2
  · exact e02 (ih8_eq_of_map_eq _ ker (h.perf R₀ h₀) (h.perf R₂ h₂) a2.symm)
  exact e12 (ih8_eq_of_map_eq _ ker (h.perf R₁ h₁) (h.perf R₂ h₂) (a1.trans a2.symm))

theorem neg_mul_ne (s : V ≃ₗ[F] V) : LinearEquiv.neg F * s ≠ s := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd h.odd
  have := h.nontrivial
  intro hs
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have h1 := congrArg (fun g : V ≃ₗ[F] V => g (s.symm w)) hs
  simp only [LinearEquiv.mul_apply, LinearEquiv.neg_apply, LinearEquiv.apply_symm_apply] at h1
  have h3 : (2 : F) • w = 0 := by
    rw [two_smul]
    nth_rewrite 2 [← h1]
    exact add_neg_cancel w
  exact hw ((smul_eq_zero.mp h3).resolve_left h2)

theorem eq_or_neg {r₀ r₁ : spinGroup Q} (hr₀2 : r₀ * r₀ = 1) (hr₁2 : r₁ * r₁ = 1)
    (hc : r₁ * r₀⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    spinAction Q r₁ = spinAction Q r₀ ∨
      spinAction Q r₁ = LinearEquiv.neg F * spinAction Q r₀ := by
  have := h.nontrivial
  obtain ⟨μ, hμ⟩ := exists_smul_of_central h.range h.scalar hc
  have hsq₀ : spinAction Q r₀ * spinAction Q r₀ = 1 := by rw [← map_mul, hr₀2, map_one]
  have hsq₁ : spinAction Q r₁ * spinAction Q r₁ = 1 := by rw [← map_mul, hr₁2, map_one]
  have hs₀ : ∀ w, spinAction Q r₀ (spinAction Q r₀ w) = w := fun w => by
    have := congrArg (fun g : V ≃ₗ[F] V => g w) hsq₀
    simpa using this
  have hs₁ : ∀ w, spinAction Q r₁ (spinAction Q r₁ w) = w := fun w => by
    have := congrArg (fun g : V ≃ₗ[F] V => g w) hsq₁
    simpa using this
  have hinv : (spinAction Q r₀)⁻¹ = spinAction Q r₀ := inv_eq_of_mul_eq_one_right hsq₀
  have hrel : ∀ w, spinAction Q r₁ w = μ • spinAction Q r₀ w := by
    intro w
    have h1 := hμ (spinAction Q r₀ w)
    rw [map_mul, map_inv, hinv] at h1
    simpa only [LinearEquiv.mul_apply, hs₀] using h1
  have hμ2 : μ * μ = 1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have h1 := hs₁ w
    rw [hrel w, map_smul, hrel (spinAction Q r₀ w), smul_smul, hs₀] at h1
    have h4 : (μ * μ - 1) • w = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hw)
  rcases mul_self_eq_one_iff.mp hμ2 with h1 | h1
  · left
    exact LinearEquiv.ext fun w => by rw [hrel, h1, one_smul]
  · right
    exact LinearEquiv.ext fun w => by
      rw [hrel, h1, LinearEquiv.mul_apply, LinearEquiv.neg_apply, neg_one_smul]

theorem exists_partner {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕) {r : spinGroup Q} (hr : r ∈ R)
    (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    ∃ R' ∈ 𝓕, R' ≠ R ∧ ∃ r' ∈ R', r' * r' = 1 ∧ r' ≠ 1 ∧ spinAction Q r' = spinAction Q r ∧
      ∀ R'' ∈ 𝓕, ∀ r'' ∈ R'', r'' * r'' = 1 → r'' ≠ 1 → spinAction Q r'' = spinAction Q r →
        R'' = R ∨ R'' = R' := by
  have f₀ := h.fund_of_inv hR hr hr2 hr1
  obtain ⟨L', hL', hne, -, huniq⟩ := IsFundamental.exists_twin h.odd f₀
  have ker := ker_spinAction_le_center Q
  obtain ⟨R', hR', hR'L⟩ := h.lift L' ⟨_, hL'⟩
  have hθr : spinAction Q r ∈ R'.map (spinAction Q) := hR'L ▸ hL'.mem
  obtain ⟨r', hr', hθr'⟩ := hθr
  have hsq : spinAction Q r * spinAction Q r = 1 := by rw [← map_mul, hr2, map_one]
  refine ⟨R', hR', fun e => hne (by rw [← hR'L, e]), r', hr', ?_, ?_, hθr', ?_⟩
  · exact h.inj hR' (R'.mul_mem hr' hr') (by rw [map_mul, hθr', hsq])
  · intro h1
    apply hr1
    exact h.inj hR hr (by rw [← hθr', h1, map_one])
  · intro R'' hR'' r'' hr'' hr''2 hr''1 hθ
    have f'' := h.fund_of_inv hR'' hr'' hr''2 hr''1
    rw [hθ] at f''
    rcases huniq _ f'' with a | a
    · exact Or.inl (ih8_eq_of_map_eq _ ker (h.perf R'' hR'') (h.perf R hR) a)
    · exact Or.inr (ih8_eq_of_map_eq _ ker (h.perf R'' hR'') (h.perf R' hR')
        (a.trans hR'L.symm))

theorem exists_partner_ratio {R_a R_b R_c : Subgroup (spinGroup Q)} (ha : R_a ∈ 𝓕) (hb : R_b ∈ 𝓕)
    (hc : R_c ∈ 𝓕) (hab : R_a ≠ R_b) {r_a r_b r_c : spinGroup Q} (hra : r_a ∈ R_a)
    (hra2 : r_a * r_a = 1) (hra1 : r_a ≠ 1) (hrb : r_b ∈ R_b) (hrb2 : r_b * r_b = 1)
    (hrb1 : r_b ≠ 1) (hrc : r_c ∈ R_c) (hrc2 : r_c * r_c = 1) (hrc1 : r_c ≠ 1)
    (hθ : spinAction Q r_b = spinAction Q r_a)
    (hcen : r_b * r_a⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ R₃ ∈ 𝓕, R₃ ≠ R_c ∧ ∃ r₃ ∈ R₃, r₃ * r₃ = 1 ∧ r₃ ≠ 1 ∧
      spinAction Q r₃ = spinAction Q r_c ∧ r₃ * r_c⁻¹ = r_b * r_a⁻¹ := by
  obtain ⟨R₃, hR₃, hne3, r₃, hr₃, hr₃2, hr₃1, hθ₃, huniq⟩ := h.exists_partner hc hrc hrc2 hrc1
  obtain ⟨g, hg⟩ := h.single R_a ha R_c hc
  have hinv_conj : ∀ {x : spinGroup Q}, x * x = 1 → x ≠ 1 →
      g * x * g⁻¹ * (g * x * g⁻¹) = 1 ∧ g * x * g⁻¹ ≠ 1 := by
    intro x hx2 hx1
    refine ⟨?_, ?_⟩
    · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    · intro h1
      apply hx1
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e, h1]
      group
  have hca : g * r_a * g⁻¹ ∈ R_c := by
    rw [hg]
    exact conj_mem_conjSub hra
  have hcb : g * r_b * g⁻¹ ∈ conjSub g R_b := conj_mem_conjSub hrb
  obtain ⟨hca2, hca1⟩ := hinv_conj hra2 hra1
  obtain ⟨hcb2, hcb1⟩ := hinv_conj hrb2 hrb1
  have hrc_eq : r_c = g * r_a * g⁻¹ := h.inv_unique hc hrc hrc2 hrc1 hca hca2 hca1
  have hθcb : spinAction Q (g * r_b * g⁻¹) = spinAction Q r_c := by
    rw [hrc_eq]
    simp only [map_mul, map_inv, hθ]
  have hmemcb : conjSub g R_b ∈ 𝓕 := h.conj R_b hb g
  have hcases := huniq (conjSub g R_b) hmemcb (g * r_b * g⁻¹) hcb hcb2 hcb1 hθcb
  have hR3eq : conjSub g R_b = R₃ := by
    rcases hcases with e | e
    · exfalso
      apply hab
      rw [hg] at e
      exact (BSD.conjSub_inj g e).symm
    · exact e
  have hr₃eq : r₃ = g * r_b * g⁻¹ := by
    refine h.inv_unique hR₃ hr₃ hr₃2 hr₃1 ?_ hcb2 hcb1
    rw [← hR3eq]
    exact hcb
  refine ⟨R₃, hR₃, hne3, r₃, hr₃, hr₃2, hr₃1, hθ₃, ?_⟩
  have hcentral := Subgroup.mem_center_iff.mp hcen g
  rw [hr₃eq, hrc_eq]
  calc g * r_b * g⁻¹ * (g * r_a * g⁻¹)⁻¹ = g * (r_b * r_a⁻¹) * g⁻¹ := by group
    _ = r_b * r_a⁻¹ := by
      rw [hcentral]
      group

theorem exists_fourth {X : Type*} [Group X] (φ : spinGroup Q →* X)
    (hφ : φ.ker ≤ Subgroup.center (spinGroup Q)) {R₀ R₁ R₂ : Subgroup (spinGroup Q)}
    (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕) (h₂ : R₂ ∈ 𝓕) (e01 : R₀ ≠ R₁) (e02 : R₀ ≠ R₂)
    (e12 : R₁ ≠ R₂) {r₀ r₁ r₂ : spinGroup Q} (hr₀ : r₀ ∈ R₀) (hr₀2 : r₀ * r₀ = 1)
    (hr₀1 : r₀ ≠ 1) (hr₁ : r₁ ∈ R₁) (hr₁2 : r₁ * r₁ = 1) (hr₁1 : r₁ ≠ 1) (hr₂ : r₂ ∈ R₂)
    (hr₂2 : r₂ * r₂ = 1) (hr₂1 : r₂ ≠ 1) (p01 : φ r₀ = φ r₁) (p12 : φ r₁ = φ r₂) :
    ∃ R₃ ∈ 𝓕, R₃ ≠ R₀ ∧ R₃ ≠ R₁ ∧ R₃ ≠ R₂ ∧ ∃ r₃ ∈ R₃, r₃ * r₃ = 1 ∧ r₃ ≠ 1 ∧
      φ r₃ = φ r₀ := by
  have hcen : ∀ {x y : spinGroup Q}, φ x = φ y → x * y⁻¹ ∈ Subgroup.center (spinGroup Q) :=
    fun hxy => hφ (by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel])
  have p02 : φ r₀ = φ r₂ := p01.trans p12
  have hnegneg : LinearEquiv.neg F * LinearEquiv.neg F = (1 : V ≃ₗ[F] V) :=
    LinearEquiv.ext fun w => by simp
  have key : ∀ {R_a R_b R_c : Subgroup (spinGroup Q)} {r_a r_b r_c : spinGroup Q},
      R_a ∈ 𝓕 → R_b ∈ 𝓕 → R_c ∈ 𝓕 → R_a ≠ R_b → R_a ≠ R_c → R_b ≠ R_c →
      r_a ∈ R_a → r_a * r_a = 1 → r_a ≠ 1 → r_b ∈ R_b → r_b * r_b = 1 → r_b ≠ 1 →
      r_c ∈ R_c → r_c * r_c = 1 → r_c ≠ 1 → φ r_a = φ r_b → φ r_a = φ r_c →
      spinAction Q r_b = spinAction Q r_a →
      spinAction Q r_c = LinearEquiv.neg F * spinAction Q r_a →
      ∃ R₃ ∈ 𝓕, R₃ ≠ R_a ∧ R₃ ≠ R_b ∧ R₃ ≠ R_c ∧ ∃ r₃ ∈ R₃, r₃ * r₃ = 1 ∧ r₃ ≠ 1 ∧
        φ r₃ = φ r_a := by
    intro R_a R_b R_c r_a r_b r_c ha hb hc hab hac hbc hra hra2 hra1 hrb hrb2 hrb1 hrc hrc2
      hrc1 pab pac sab sac
    obtain ⟨R₃, hR₃, hne3, r₃, hr₃, hr₃2, hr₃1, hθ₃, hratio⟩ :=
      h.exists_partner_ratio ha hb hc hab hra hra2 hra1 hrb hrb2 hrb1 hrc hrc2 hrc1 sab
        (hcen pab.symm)
    refine ⟨R₃, hR₃, ?_, ?_, hne3, r₃, hr₃, hr₃2, hr₃1, ?_⟩
    · rintro rfl
      have := h.inv_unique hR₃ hr₃ hr₃2 hr₃1 hra hra2 hra1
      rw [this, sac] at hθ₃
      exact h.neg_mul_ne _ hθ₃.symm
    · rintro rfl
      have := h.inv_unique hR₃ hr₃ hr₃2 hr₃1 hrb hrb2 hrb1
      rw [this, sab, sac] at hθ₃
      exact h.neg_mul_ne _ hθ₃.symm
    · have e : r₃ = r_b * r_a⁻¹ * r_c := by rw [← hratio]; group
      rw [e, map_mul, map_mul, map_inv, ← pab, ← pac, mul_inv_cancel, one_mul]
  rcases h.eq_or_neg hr₀2 hr₁2 (hcen p01.symm) with s1 | s1 <;>
    rcases h.eq_or_neg hr₀2 hr₂2 (hcen p02.symm) with s2 | s2
  · exact (h.false_of_three h₀ h₁ h₂ e01 e02 e12 hr₀ hr₀2 hr₀1 hr₁ hr₁2 hr₁1 hr₂ hr₂2 hr₂1 s1
      s2).elim
  · obtain ⟨R₃, hR₃, n0, n1, n2, r₃, hr₃, hr₃2, hr₃1, hφ₃⟩ := key h₀ h₁ h₂ e01 e02 e12 hr₀ hr₀2
      hr₀1 hr₁ hr₁2 hr₁1 hr₂ hr₂2 hr₂1 p01 p02 s1 s2
    exact ⟨R₃, hR₃, n0, n1, n2, r₃, hr₃, hr₃2, hr₃1, hφ₃⟩
  · obtain ⟨R₃, hR₃, n0, n2, n1, r₃, hr₃, hr₃2, hr₃1, hφ₃⟩ := key h₀ h₂ h₁ e02 e01 e12.symm hr₀
      hr₀2 hr₀1 hr₂ hr₂2 hr₂1 hr₁ hr₁2 hr₁1 p02 p01 s2 s1
    exact ⟨R₃, hR₃, n0, n1, n2, r₃, hr₃, hr₃2, hr₃1, hφ₃⟩
  · have s12 : spinAction Q r₂ = spinAction Q r₁ := by rw [s1, s2]
    have s10 : spinAction Q r₀ = LinearEquiv.neg F * spinAction Q r₁ := by
      rw [s1, ← mul_assoc, hnegneg, one_mul]
    obtain ⟨R₃, hR₃, n1, n2, n0, r₃, hr₃, hr₃2, hr₃1, hφ₃⟩ := key h₁ h₂ h₀ e12 e01.symm
      e02.symm hr₁ hr₁2 hr₁1 hr₂ hr₂2 hr₂1 hr₀ hr₀2 hr₀1 p12 p01.symm s12 s10
    exact ⟨R₃, hR₃, n0, n1, n2, r₃, hr₃, hr₃2, hr₃1, by rw [hφ₃, p01]⟩

theorem false_of_five {X : Type*} [Group X] (φ : spinGroup Q →* X)
    (hφ : φ.ker ≤ Subgroup.center (spinGroup Q)) (R : Fin 5 → Subgroup (spinGroup Q))
    (r : Fin 5 → spinGroup Q) (hR : ∀ i, R i ∈ 𝓕) (hRinj : Function.Injective R)
    (hr : ∀ i, r i ∈ R i) (hr2 : ∀ i, r i * r i = 1) (hr1 : ∀ i, r i ≠ 1)
    (hφr : ∀ i, φ (r i) = φ (r 0)) : False := by
  classical
  have hcen : ∀ i, r i * (r 0)⁻¹ ∈ Subgroup.center (spinGroup Q) := fun i =>
    hφ (by rw [MonoidHom.mem_ker, map_mul, map_inv, hφr i, mul_inv_cancel])
  let c : Fin 5 → Bool := fun i => decide (spinAction Q (r i) = spinAction Q (r 0))
  have hc : ∀ i j, c i = c j → spinAction Q (r i) = spinAction Q (r j) := by
    have key : ∀ i, (c i = true → spinAction Q (r i) = spinAction Q (r 0)) ∧
        (c i = false → spinAction Q (r i) = LinearEquiv.neg F * spinAction Q (r 0)) := by
      intro i
      rcases h.eq_or_neg (hr2 0) (hr2 i) (hcen i) with e | e
      · exact ⟨fun _ => e, fun hf => by simp [c, e] at hf⟩
      · refine ⟨fun ht => ?_, fun _ => e⟩
        have : spinAction Q (r i) = spinAction Q (r 0) := by simpa [c] using ht
        exact absurd (this.symm.trans e) (h.neg_mul_ne _).symm
    intro i j hij
    cases hci : c i
    · have hcj : c j = false := hij ▸ hci
      rw [(key i).2 hci, (key j).2 hcj]
    · have hcj : c j = true := hij ▸ hci
      rw [(key i).1 hci, (key j).1 hcj]
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (Finset.univ : Finset (Fin 5))) (t := (Finset.univ : Finset Bool)) (f := c) (n := 2)
    (fun _ _ => Finset.mem_univ _) (by simp)
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hd
  exact h.false_of_three (hR a) (hR b) (hR d) (fun e => hab (hRinj e)) (fun e => had (hRinj e))
    (fun e => hbd (hRinj e)) (hr a) (hr2 a) (hr1 a) (hr b) (hr2 b) (hr1 b) (hr d) (hr2 d) (hr1 d)
    (hc b a (hb.trans ha.symm)) (hc d a (hd.trans ha.symm))

end SpinFund

end SpinFund

end CFSG.ClassicalInvolution.Asc77.BSC.BSE
