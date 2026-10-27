module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.OuterInv
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.OuterG

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule


section ChiPow

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem chi_hatH_pow {k V : Type*} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup V]
    [Module k V] {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {μ : Fin TwistTag.E6.foldedTag.rank → k}
    (hμ : (twistedE6CoverData hf hK σ hσ).datum.IsCurtisType ρ y χ μ)
    (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ) (N : ℕ) :
    χ (hatH hf hK σ hσ a (w ^ N)) = χ (hatH hf hK σ hσ a w) ^ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction N with
  | zero =>
    rw [pow_zero, pow_zero]
    have h1 : hatH hf hK σ hσ a (1 : (orbitField TwistTag.E6 K σ a)ˣ) = 1 :=
      (twistedE6CoverRankOne hf hK σ hσ).hh_one a
    rw [h1]
    exact hμ.chi_one
  | succ N ih =>
    rw [pow_succ, pow_succ, ← ih]
    have h1 : hatH hf hK σ hσ a (w ^ N * w) =
        hatH hf hK σ hσ a (w ^ N) * hatH hf hK σ hσ a w :=
      (twistedE6CoverRankOne hf hK σ hσ).hh_mul a _ _
    rw [h1]
    exact hμ.chi_mul ((twistedE6CoverRankOne hf hK σ hσ).hh_mem a _)
      ((twistedE6CoverRankOne hf hK σ hσ).hh_mem a _)

end ChiPow

section Twist

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σe : K ≃+* K) (hσ : ∀ c, σe.toRingHom c = c ^ (2 ^ f))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
include hf hK hσ in
theorem chi_pow_of_twist {L : Type} [Group L] [Finite L]
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (eS : L ⧸ Subgroup.center L ≃* ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom))
    (φ : ↥(TwistedE6.fixedGroup K σe.toRingHom) →* L)
    (hφ : ∀ x, eS (QuotientGroup.mk (φ x)) = coverHom hf hK σe.toRingHom hσ x)
    (β : MulAut L) (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom))
    (hαβ : ∀ l, α (eS (QuotientGroup.mk l)) = eS (QuotientGroup.mk (β l)))
    (g : ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σe.toRingHom a)ˣ)
    (hα : α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σe.toRingHom u *
      fieldActor (t := TwistTag.E6) σe σe)
    {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}
    {ρ : Representation k L (Fin m → k)}
    (hρ : IsSimpleRep (ρ.comp φ)) {y : Fin m → k}
    {χ : ↥(TwistedE6.fixedGroup K σe.toRingHom) → k}
    {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σe.toRingHom hσ) (ρ.comp φ) y χ J)
    (B : Module.End k (Fin m → k)) (hB : IsUnit B) (hBρ : ∀ l, B * ρ l = ρ (β l) * B)
    (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σe.toRingHom a)ˣ) :
    χ (hatH hf hK σe.toRingHom hσ a w) ^ (2 ^ f) = χ (hatH hf hK σe.toRingHom hσ a w) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(TwistedE6.fixedGroup K σe.toRingHom) := finite_fixedGroup σe.toRingHom
  have hcc := isCentralCover_of_odd_center hodd eS
  have hq2 : ∀ {l₁ l₂ : L}, IsPElt 2 l₁ → IsPElt 2 l₂ →
      eS (QuotientGroup.mk l₁) = eS (QuotientGroup.mk l₂) → l₁ = l₂ :=
    fun h1 h2 h => hcc.eq_of_isPElt_of_map_eq h1 h2 h
  obtain ⟨ĝ, hĝ⟩ := (isCentralCover_coverHom hf hK σe.toRingHom hσ).surj g
  have hX : ∀ (b : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σe.toRingHom b),
      β (φ (hatX hf hK σe.toRingHom hσ b c)) =
      φ (ĝ * hatX hf hK σe.toRingHom hσ b ((u b : orbitField TwistTag.E6 K σe.toRingHom b) *
        orbitFieldRestrict TwistTag.E6 σe σe b c) * ĝ⁻¹) := by
    intro b c
    refine hq2 (isPElt_two_of_sq ?_) (isPElt_two_of_sq ?_) ?_
    · rw [← map_pow, ← map_pow, hatX_sq hf hK σe.toRingHom hσ, map_one, map_one]
    · rw [← map_pow, conj_pow, hatX_sq hf hK σe.toRingHom hσ, mul_one, mul_inv_cancel, map_one]
    · calc eS (QuotientGroup.mk (β (φ (hatX hf hK σe.toRingHom hσ b c))))
          = α (eS (QuotientGroup.mk (φ (hatX hf hK σe.toRingHom hσ b c)))) := (hαβ _).symm
        _ = α (coverHom hf hK σe.toRingHom hσ (hatX hf hK σe.toRingHom hσ b c)) := by rw [hφ]
        _ = α (xC TwistTag.E6 K σe.toRingHom b c) := by rw [coverHom_hatX]
        _ = g * xC TwistTag.E6 K σe.toRingHom b ((u b : orbitField TwistTag.E6 K σe.toRingHom b) *
            orbitFieldRestrict TwistTag.E6 σe σe b c) * g⁻¹ := by rw [hα]; exact nf_xC σe g u b c
        _ = _ := by
          rw [hφ, map_mul, map_mul, coverHom_hatX, map_inv, hĝ]
  have hY : ∀ (b : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σe.toRingHom b),
      β (φ (hatY hf hK σe.toRingHom hσ b c)) =
      φ (ĝ * hatY hf hK σe.toRingHom hσ b
        (((u b)⁻¹ : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ) *
        orbitFieldRestrict TwistTag.E6 σe σe b c) * ĝ⁻¹) := by
    intro b c
    refine hq2 (isPElt_two_of_sq ?_) (isPElt_two_of_sq ?_) ?_
    · rw [← map_pow, ← map_pow, hatY_sq hf hK σe.toRingHom hσ, map_one, map_one]
    · rw [← map_pow, conj_pow, hatY_sq hf hK σe.toRingHom hσ, mul_one, mul_inv_cancel, map_one]
    · calc eS (QuotientGroup.mk (β (φ (hatY hf hK σe.toRingHom hσ b c))))
          = α (eS (QuotientGroup.mk (φ (hatY hf hK σe.toRingHom hσ b c)))) := (hαβ _).symm
        _ = α (coverHom hf hK σe.toRingHom hσ (hatY hf hK σe.toRingHom hσ b c)) := by rw [hφ]
        _ = α (yC TwistTag.E6 K σe.toRingHom b c) := by rw [coverHom_hatY]
        _ = g * yC TwistTag.E6 K σe.toRingHom b
            (((u b)⁻¹ : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ) *
            orbitFieldRestrict TwistTag.E6 σe σe b c) * g⁻¹ := by rw [hα]; exact nf_yC σe g u b c
        _ = _ := by
          rw [hφ, map_mul, map_mul, coverHom_hatY, map_inv, hĝ]
  have hH : ∀ (b : Fin TwistTag.E6.foldedTag.rank)
      (w : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ),
      β (φ (hatH hf hK σe.toRingHom hσ b w)) =
      φ (ĝ * hatH hf hK σe.toRingHom hσ b
        (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w) * ĝ⁻¹) := by
    intro b w
    obtain ⟨μ, hμ⟩ : ∃ μ : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ,
        (μ : orbitField TwistTag.E6 K σe.toRingHom b) ^ 2 =
          (u b : orbitField TwistTag.E6 K σe.toRingHom b) := by
      obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq _ 2)
        (u b : orbitField TwistTag.E6 K σe.toRingHom b)
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact (u b).ne_zero (by rw [hr, mul_zero])
      exact ⟨Units.mk0 r hr0, by rw [Units.val_mk0, pow_two, hr]⟩
    set τ := orbitFieldRestrict TwistTag.E6 σe σe b with hτ
    let ψ₁ : SL2 (orbitField TwistTag.E6 K σe.toRingHom b) →* L :=
      (β.toMonoidHom.comp φ).comp (Rhat hf hK σe.toRingHom hσ b)
    let ψ₂ : SL2 (orbitField TwistTag.E6 K σe.toRingHom b) →* L :=
      ((MulAut.conj (φ ĝ)).toMonoidHom.comp φ).comp
        ((Rhat hf hK σe.toRingHom hσ b).comp (slAut τ μ))
    have hψ : ψ₁ = ψ₂ := by
      apply hom_ext_SL2
      · intro c
        show β (φ (Rhat hf hK σe.toRingHom hσ b (uSL c))) =
          φ ĝ * φ (Rhat hf hK σe.toRingHom hσ b (slAut τ μ (uSL c))) * (φ ĝ)⁻¹
        rw [slAut_uSL, hμ, Rhat_uSL, Rhat_uSL, hX, map_mul, map_mul, map_inv]
      · intro c
        show β (φ (Rhat hf hK σe.toRingHom hσ b (vSL c))) =
          φ ĝ * φ (Rhat hf hK σe.toRingHom hσ b (slAut τ μ (vSL c))) * (φ ĝ)⁻¹
        have hμ' : ((μ⁻¹ : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ) :
            orbitField TwistTag.E6 K σe.toRingHom b) ^ 2 =
            (((u b)⁻¹ : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ) :
              orbitField TwistTag.E6 K σe.toRingHom b) := by
          rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hμ, inv_pow]
        rw [slAut_vSL, hμ', Rhat_vSL, Rhat_vSL, hY, map_mul, map_mul, map_inv]
    have h1 := congrArg (fun F => F (HSL w)) hψ
    simp only [ψ₁, ψ₂, MonoidHom.comp_apply] at h1
    rw [slAut_HSL, Rhat_HSL, Rhat_HSL] at h1
    have h2 : β (φ (hatH hf hK σe.toRingHom hσ b w)) = (MulAut.conj (φ ĝ))
        (φ (hatH hf hK σe.toRingHom hσ b (Units.map τ.toRingHom.toMonoidHom w))) := h1
    rw [h2, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hU : ∀ u' ∈ (twistedE6CoverData hf hK σe.toRingHom hσ).datum.U,
      ∃ x'' ∈ (twistedE6CoverData hf hK σe.toRingHom hσ).datum.U,
        β (φ x'') = φ (ĝ * u' * ĝ⁻¹) := by
    intro u' hu'
    have hu'1 : coverHom hf hK σe.toRingHom hσ u' ∈ (twistedE6Datum hf hK σe.toRingHom hσ).U :=
      hu'.1
    obtain ⟨x, hxU, hx⟩ := nf_exists_U σe g u hu'1
    obtain ⟨x'', hx''U, hπx''⟩ := (twistedE6CoverData hf hK σe.toRingHom hσ).exists_lift
      (hP := (twistedE6Datum hf hK σe.toRingHom hσ).isPGroup_U) hxU
    refine ⟨x'', hx''U, hq2 ((hx''U.2.map φ).map β.toMonoidHom) ((hu'.2.conj ĝ).map φ) ?_⟩
    calc eS (QuotientGroup.mk (β (φ x'')))
        = α (eS (QuotientGroup.mk (φ x''))) := (hαβ _).symm
      _ = α (coverHom hf hK σe.toRingHom hσ x'') := by rw [hφ]
      _ = α x := by rw [hπx'']
      _ = g * coverHom hf hK σe.toRingHom hσ u' * g⁻¹ := by rw [hα]; exact hx
      _ = _ := by rw [hφ, map_mul, map_mul, hĝ, map_inv, hĝ]
  have hρunit : ∀ s, IsUnit (ρ s) := fun s =>
    ⟨⟨ρ s, ρ s⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by
      rw [← map_mul, inv_mul_cancel, map_one]⟩, rfl⟩
  obtain ⟨μs, hμs⟩ := ht.exists_mu hρ (twistedCover_split hf hK σe.toRingHom hσ k)
  set B' : Module.End k (Fin m → k) := ρ (φ ĝ⁻¹) * B with hB'
  have hB'unit : IsUnit B' := (hρunit _).mul hB
  have hBρ' : ∀ l, ρ (β l) * B = B * ρ l := fun l => (hBρ l).symm
  have hfix : B' y ∈ (twistedE6CoverData hf hK σe.toRingHom hσ).datum.fixU (ρ.comp φ) := by
    intro u' hu'
    obtain ⟨x'', hx''U, hx''⟩ := hU u' hu'
    have e1 : ρ (φ u') * ρ (φ ĝ⁻¹) = ρ (φ ĝ⁻¹) * ρ (φ (ĝ * u' * ĝ⁻¹)) := by
      have hg : u' * ĝ⁻¹ = ĝ⁻¹ * (ĝ * u' * ĝ⁻¹) := by group
      calc ρ (φ u') * ρ (φ ĝ⁻¹) = ρ (φ (u' * ĝ⁻¹)) := by rw [map_mul, map_mul]
        _ = ρ (φ (ĝ⁻¹ * (ĝ * u' * ĝ⁻¹))) := by rw [hg]
        _ = _ := by rw [map_mul, map_mul]
    have hy : ρ (φ x'') y = y := ht.1 x'' hx''U
    show ρ (φ u') (B' y) = B' y
    calc ρ (φ u') (B' y) = (ρ (φ u') * ρ (φ ĝ⁻¹)) (B y) := rfl
      _ = ρ (φ ĝ⁻¹) (ρ (φ (ĝ * u' * ĝ⁻¹)) (B y)) := by rw [e1]; rfl
      _ = ρ (φ ĝ⁻¹) (ρ (β (φ x'')) (B y)) := by rw [hx'']
      _ = ρ (φ ĝ⁻¹) (B (ρ (φ x'') y)) := by
        have := congrArg (fun F : Module.End k (Fin m → k) => F y) (hBρ' (φ x''))
        simp only [Module.End.mul_apply] at this
        rw [this]
      _ = B' y := by rw [hy]; rfl
  obtain ⟨c, hc⟩ := (twistedE6CoverData hf hK σe.toRingHom hσ).datum.fixU_eq_smul hρ hμs hfix
  have hy0 : y ≠ 0 := ht.2.1
  have hB'y : B' y ≠ 0 := by
    intro h0
    have hbij := (Module.End.isUnit_iff B').1 hB'unit
    exact hy0 (hbij.injective (by rw [h0, map_zero]))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hB'y (by rw [hc, zero_smul])
  have hrel : ∀ (b : Fin TwistTag.E6.foldedTag.rank)
      (w : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ),
      ρ (φ (hatH hf hK σe.toRingHom hσ b
        (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w))) * B' =
      B' * ρ (φ (hatH hf hK σe.toRingHom hσ b w)) := by
    intro b w
    set h' := hatH hf hK σe.toRingHom hσ b
      (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w)
    set h := hatH hf hK σe.toRingHom hσ b w
    have e1 : ρ (φ h') * ρ (φ ĝ⁻¹) = ρ (φ ĝ⁻¹) * ρ (φ (ĝ * h' * ĝ⁻¹)) := by
      have hg : h' * ĝ⁻¹ = ĝ⁻¹ * (ĝ * h' * ĝ⁻¹) := by group
      calc ρ (φ h') * ρ (φ ĝ⁻¹) = ρ (φ (h' * ĝ⁻¹)) := by rw [map_mul, map_mul]
        _ = ρ (φ (ĝ⁻¹ * (ĝ * h' * ĝ⁻¹))) := by rw [hg]
        _ = _ := by rw [map_mul, map_mul]
    rw [hB', ← mul_assoc, e1, mul_assoc, ← hH b w, mul_assoc, hBρ' (φ h)]
  have hχ : ∀ (b : Fin TwistTag.E6.foldedTag.rank)
      (w : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ),
      χ (hatH hf hK σe.toRingHom hσ b
        (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w)) =
      χ (hatH hf hK σe.toRingHom hσ b w) := by
    intro b w
    have hmem : ∀ v : (orbitField TwistTag.E6 K σe.toRingHom b)ˣ,
        hatH hf hK σe.toRingHom hσ b v ∈
          (twistedE6Datum hf hK σe.toRingHom hσ).H.comap (coverHom hf hK σe.toRingHom hσ) :=
      fun v => (twistedE6CoverRankOne hf hK σe.toRingHom hσ).hh_mem b v
    have e1 : ρ (φ (hatH hf hK σe.toRingHom hσ b
        (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w))) (B' y) =
        χ (hatH hf hK σe.toRingHom hσ b w) • B' y := by
      have := congrArg (fun F : Module.End k (Fin m → k) => F y) (hrel b w)
      simp only [Module.End.mul_apply] at this
      rw [this]
      have hh := ht.2.2.1 _ (hmem w)
      show B' (ρ (φ (hatH hf hK σe.toRingHom hσ b w)) y) = _
      have hh' : ρ (φ (hatH hf hK σe.toRingHom hσ b w)) y =
          χ (hatH hf hK σe.toRingHom hσ b w) • y := hh
      rw [hh', map_smul]
    have e2 : ρ (φ (hatH hf hK σe.toRingHom hσ b
        (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w))) (B' y) =
        χ (hatH hf hK σe.toRingHom hσ b
          (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w)) •
          B' y := by
      have hh := ht.2.2.1 _ (hmem (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w))
      have hh' : ρ (φ (hatH hf hK σe.toRingHom hσ b
          (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w))) y =
          χ (hatH hf hK σe.toRingHom hσ b
            (Units.map (orbitFieldRestrict TwistTag.E6 σe σe b).toRingHom.toMonoidHom w)) • y := hh
      rw [hc, map_smul, hh', smul_comm]
    exact smul_left_injective k hB'y (e2.symm.trans e1)
  have hpow := chi_hatH_pow hf hK σe.toRingHom hσ hμs a w
  have hwq : Units.map (orbitFieldRestrict TwistTag.E6 σe σe a).toRingHom.toMonoidHom w =
      w ^ (2 ^ f) := by
    refine Units.ext (Subtype.ext ?_)
    show σe ((w : orbitField TwistTag.E6 K σe.toRingHom a) : K) =
      (((w : orbitField TwistTag.E6 K σe.toRingHom a)) : K) ^ (2 ^ f)
    exact hσ _
  rw [← hpow (2 ^ f), ← hwq]
  exact hχ a w


end Twist

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
