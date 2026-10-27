module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.TriXSplit
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311v
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311x
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.TwistedTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311y

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec19 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape CFSG.RankThree.PartOne.KE
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner (frameConj frameConj_apply)

set_option linter.unusedSectionVars false

section Statements

@[expose] def FrameCoreTransvection :
    Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → (ℓ ^ f) % 3 = 2 → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (Φ : D4PhiFrame K σ (ℓ ^ f) (-1)) (x y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      frameConj Φ x ∈ twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr) →
      frameConj Φ y ∈ twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr) →
      x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 → y ∉ Subgroup.zpowers x →
      ∃ r ∈ Subgroup.closure {k | k * x = x * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1},
        r * x * r⁻¹ = x ∧ (r * y * r⁻¹ = x * y ∨ r * y * r⁻¹ = x⁻¹ * y)

end Statements

section Abstract

variable {G : Type} [Group G]

theorem rCent_conj_subset_inputs2311y {ℓ : ℕ} {H : Subgroup G} {w c : G}
    (hC : {k : G | k * w = w * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G)) (hc : c ∈ H) :
    {k : G | k * (c * w * c⁻¹) = c * w * c⁻¹ * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G) := by
  rintro k ⟨hk, n, hn⟩
  have hk' : c⁻¹ * k * c ∈ {k : G | k * w = w * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} := by
    refine ⟨?_, n, ?_⟩
    · calc c⁻¹ * k * c * w = c⁻¹ * (k * (c * w * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * w * c⁻¹) * k) * c := by rw [hk]
        _ = w * (c⁻¹ * k * c) := by group
    · rw [show c⁻¹ * k * c = c⁻¹ * k * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hn, mul_one, mul_inv_cancel]
  have hmem : c * (c⁻¹ * k * c) * c⁻¹ ∈ H := H.mul_mem (H.mul_mem hc (hC hk')) (H.inv_mem hc)
  rwa [show c * (c⁻¹ * k * c) * c⁻¹ = k by group] at hmem

private theorem rCent_sq_subset_inputs2311y {ℓ : ℕ} {w : G} (hw3 : w ^ 3 = 1) :
    {k : G | k * w ^ 2 = w ^ 2 * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆
      {k : G | k * w = w * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} := by
  rintro k ⟨hk, hn⟩
  refine ⟨?_, hn⟩
  have hw : w = (w ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hw3, one_mul]
  have h2 : Commute k ((w ^ 2) ^ 2) := (show Commute k (w ^ 2) from hk).pow_right 2
  rw [← hw] at h2
  exact h2.eq

theorem rCent_subset_of_mem_closure_pair_inputs2311y {ℓ : ℕ} {x y : G} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) {H : Subgroup G}
    (hCx : {k : G | k * x = x * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G))
    (hCy : {k : G | k * y = y * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G))
    (hCxy : {k : G | k * (x * y) = x * y * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G))
    (hCx2y : {k : G | k * (x ^ 2 * y) = x ^ 2 * y * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G))
    {f : G} (hf : f ∈ Subgroup.closure ({x, y} : Set G)) (hf1 : f ≠ 1) :
    {k : G | k * f = f * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G) := by
  have hc : Commute x y := hxy
  have hcube : ∀ w : G, w ∈ Subgroup.closure ({x, y} : Set G) → w ^ 3 = 1 := fun w hw =>
    (closure_pair_comm_cube hx3 hy3 hxy).2 w hw
  have hxF : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyF : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hsq : ∀ w, w ∈ Subgroup.closure ({x, y} : Set G) →
      {k : G | k * w = w * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G) →
      {k : G | k * w ^ 2 = w ^ 2 * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set G) :=
    fun w hw hC => (rCent_sq_subset_inputs2311y (hcube w hw)).trans hC
  obtain ⟨a, b, ha, hb, rfl⟩ := closure_pair_normal_form hx3 hy3 hxy hf
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hf1
  · rw [show x ^ 0 * y ^ 1 = y by simp]
    exact hCy
  · rw [show x ^ 0 * y ^ 2 = y ^ 2 by simp]
    exact hsq y hyF hCy
  · rw [show x ^ 1 * y ^ 0 = x by simp]
    exact hCx
  · rw [show x ^ 1 * y ^ 1 = x * y by simp]
    exact hCxy
  ·
    have e : x ^ 1 * y ^ 2 = (x ^ 2 * y) ^ 2 := by
      rw [(hc.pow_left 2).mul_pow, ← pow_mul]
      rw [show x ^ (2 * 2) = x ^ 1 by rw [show 2 * 2 = 3 + 1 from rfl, pow_add, hx3, one_mul]]
    rw [e]
    exact hsq _ (mul_mem (pow_mem hxF 2) hyF) hCx2y
  · rw [show x ^ 2 * y ^ 0 = x ^ 2 by simp]
    exact hsq x hxF hCx
  · rw [show x ^ 2 * y ^ 1 = x ^ 2 * y by simp]
    exact hCx2y
  ·
    have e : x ^ 2 * y ^ 2 = (x * y) ^ 2 := by rw [hc.mul_pow]
    rw [e]
    exact hsq _ (mul_mem hxF hyF) hCxy

end Abstract

section TwoLine


theorem uniTwoLineGen_of_core (hCore : FrameCoreTransvection) :
    ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → (ℓ ^ f) % 3 = 2 →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
      ∀ x g : C0 σ, x ^ 3 = 1 → x ≠ 1 → TriOddIsClassX σ x →
        (g * x * g⁻¹) * x = x * (g * x * g⁻¹) → g * x * g⁻¹ ∉ Subgroup.zpowers x →
        ∀ H : Subgroup (C0 σ), {k : C0 σ | k * x = x * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set (C0 σ)) →
          g ∈ H → H = ⊤ := by
  intro ℓ f hℓ hℓ2 hℓ3 hf hq K _ _ hK σ hσ x g hx3 hx1 hxX hcomm hnot H hCH hgH
  classical
  set y := g * x * g⁻¹ with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, conj_pow, hx3]; group
  have hy1 : y ≠ 1 := fun h => hnot (h ▸ one_mem _)
  have hyX : TriOddIsClassX σ y := by
    obtain ⟨h, hh⟩ := hxX
    refine ⟨h * g⁻¹, ?_⟩
    rw [show h * g⁻¹ * y * (h * g⁻¹)⁻¹ = h * x * h⁻¹ by rw [hy]; group]
    exact hh
  have hxy : x * y = y * x := hcomm.symm
  have hCy : {k : C0 σ | k * y = y * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set (C0 σ)) :=
    rCent_conj_subset_inputs2311y hCH hgH
  set F := Subgroup.closure ({x, y} : Set (C0 σ)) with hF
  have hxF : x ∈ F := Subgroup.subset_closure (by simp)
  have hyF : y ∈ F := Subgroup.subset_closure (by simp)
  rcases d4Minus_plane_dichotomy hℓ hℓ2 hℓ3 hf hq K hK σ hσ F
      (isElementaryAbelian_closure_pair hx3 hy3 hxy) (card_closure_pair hx3 hx1 hy3 hxy hnot) with
    hT | ⟨β, ⟨Φ, c₀, hc₀⟩, -⟩
  · exact (not_twistedTorus_of_two_classX hℓ hℓ2 hℓ3 hf hq hK σ hσ hx3 hx1 hxX hy3 hy1 hyX hnot
      hT).elim
  set ψ : MulAut (C0 σ) := MulAut.conj c₀ * β⁻¹ with hψ
  have hψapp : ∀ e, ψ e = c₀ * β⁻¹ e * c₀⁻¹ := fun e => rfl
  have hψT : ∀ e ∈ F, frameConj Φ (ψ e) ∈
      twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr) := by
    intro e he
    rw [frameConj_apply, hψapp]
    exact hc₀ (β⁻¹ e) ⟨e, he, rfl⟩
  set x' := ψ x with hx'
  set y' := ψ y with hy'
  have hx'3 : x' ^ 3 = 1 := by rw [hx', ← map_pow, hx3, map_one]
  have hy'3 : y' ^ 3 = 1 := by rw [hy', ← map_pow, hy3, map_one]
  have hx'1 : x' ≠ 1 := fun h => hx1 (ψ.injective (h.trans (map_one ψ).symm))
  have hx'y' : x' * y' = y' * x' := by rw [hx', hy', ← map_mul, ← map_mul, hxy]
  have hy'x' : y' ∉ Subgroup.zpowers x' := by
    intro hmem
    apply hnot
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ψ.injective ?_⟩
    rw [map_zpow, ← hx', hn]
  obtain ⟨r, hrcl, hrx, hry⟩ := hCore ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ Φ x' y' (hψT x hxF)
    (hψT y hyF) hx'3 hx'1 hy'3 hy'x'
  set H' : Subgroup (C0 σ) := H.map ψ.toMonoidHom with hH'
  have hmem : ∀ k, k ∈ H' ↔ ψ⁻¹ k ∈ H := by
    intro k
    constructor
    · rintro ⟨v, hv, rfl⟩
      show ψ⁻¹ (ψ v) ∈ H
      rw [MulAut.inv_apply_self]
      exact hv
    · intro hk
      exact ⟨ψ⁻¹ k, hk, MulAut.apply_inv_self _ _ _⟩
  have hCmap : ∀ w : C0 σ, {k : C0 σ | k * w = w * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H : Set (C0 σ)) →
      {k : C0 σ | k * ψ w = ψ w * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H' : Set (C0 σ)) := by
    rintro w hw k ⟨hk, n, hn⟩
    show k ∈ H'
    rw [hmem]
    refine hw ⟨?_, n, ?_⟩
    · apply ψ.injective
      rw [map_mul, map_mul, MulAut.apply_inv_self]
      exact hk
    · apply ψ.injective
      rw [map_pow, MulAut.apply_inv_self, hn, map_one]
  have hCx' : {k : C0 σ | k * x' = x' * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H' : Set (C0 σ)) :=
    hCmap x hCH
  have hCy' : {k : C0 σ | k * y' = y' * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H' : Set (C0 σ)) :=
    hCmap y hCy
  have hrH' : r ∈ H' := (Subgroup.closure_le H').2 hCx' hrcl
  have hrxc : ∀ w, r * (x' * w) * r⁻¹ = x' * (r * w * r⁻¹) := fun w => by
    calc r * (x' * w) * r⁻¹ = (r * x' * r⁻¹) * (r * w * r⁻¹) := by group
      _ = x' * (r * w * r⁻¹) := by rw [hrx]
  have hrxc' : ∀ w, r * (x'⁻¹ * w) * r⁻¹ = x'⁻¹ * (r * w * r⁻¹) := fun w => by
    calc r * (x'⁻¹ * w) * r⁻¹ = (r * x' * r⁻¹)⁻¹ * (r * w * r⁻¹) := by group
      _ = x'⁻¹ * (r * w * r⁻¹) := by rw [hrx]
  have hxinv : x'⁻¹ = x' ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx'3]
  have hlines :
      {k : C0 σ | k * (x' * y') = x' * y' * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆ (H' : Set (C0 σ)) ∧
      {k : C0 σ | k * (x' ^ 2 * y') = x' ^ 2 * y' * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} ⊆
        (H' : Set (C0 σ)) := by
    have h1 := rCent_conj_subset_inputs2311y hCy' hrH'
    have h2 := rCent_conj_subset_inputs2311y h1 hrH'
    rcases hry with h | h
    · have e2 : r * (r * y' * r⁻¹) * r⁻¹ = x' ^ 2 * y' := by
        rw [h, hrxc, h, ← mul_assoc, ← sq]
      rw [h] at h1
      rw [e2] at h2
      exact ⟨h1, h2⟩
    · have e1 : r * y' * r⁻¹ = x' ^ 2 * y' := by rw [h, hxinv]
      have e2 : r * (r * y' * r⁻¹) * r⁻¹ = x' * y' := by
        rw [h, hrxc', h, ← mul_assoc, hxinv, ← pow_add,
          show x' ^ (2 + 2) = x' by rw [show 2 + 2 = 3 + 1 from rfl, pow_add, hx'3, one_mul, pow_one]]
      rw [e1] at h1
      rw [e2] at h2
      exact ⟨h2, h1⟩
  set F' := Subgroup.closure ({x', y'} : Set (C0 σ)) with hF'
  have hF'T : F' ≤ (twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr)).comap
      (frameConj Φ) := by
    rw [hF', Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hψT x hxF
    · exact hψT y hyF
  have hdvd : (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ ^ f = 3 * k + 2 := ⟨ℓ ^ f / 3, by omega⟩
    rw [hk]
    exact ⟨3 * k ^ 2 + 3 * k + 1, by push_cast; ring⟩
  have hq4 : 4 ≤ ℓ ^ f := by
    have := Inputs2311v.five_le_pow_inputs2311v hℓ hℓ2 hℓ3 hf
    omega
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, -, hsimple, -⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f hℓ hf K hK (AlgebraicClosure K) 1
      (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
      (iterateFrobenius (AlgebraicClosure K) ℓ f) (fun c => iterateFrobenius_def ℓ f c)
  haveI : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := hsimple
  have hgen := Inputs2311k.rClosure_eq_top_frame_three hℓ hℓ3 hf hq4 K hK σ hσ (Or.inr rfl) hdvd F'
    (isElementaryAbelian_closure_pair hx'3 hy'3 hx'y') (card_closure_pair hx'3 hx'1 hy'3 hx'y' hy'x')
    ⟨Φ, 1, fun e he => by
      have := hF'T he
      rw [Subgroup.mem_comap, frameConj_apply] at this
      rw [one_mul, inv_one, mul_one]
      exact this⟩
  have htop : H' = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro k ⟨e, he, he1, hke, n, hn⟩
    exact rCent_subset_of_mem_closure_pair_inputs2311y hx'3 hy'3 hx'y' hCx' hCy' hlines.1 hlines.2 he
      he1 ⟨hke.eq, n, hn⟩
  rw [eq_top_iff]
  intro w _
  have hw : ψ w ∈ H' := by rw [htop]; exact Subgroup.mem_top _
  rw [hmem, MulAut.inv_apply_self] at hw
  exact hw

end TwoLine

section Planes


theorem uniPlaneClosure_eq_top_minus_inputs2311y (hCore : FrameCoreTransvection) (ℓ f : ℕ)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (x : C0 σ) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ)) (hng : ¬ TriOddHasGLine σ E)
    (hnc : ∀ γ : MulAut (C0 σ), TriOddIsGLine σ γ → ¬ ∀ α ∈ E, α * γ = γ * α)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hcx : MulAut.conj x ∈ E) (hX : TriOddIsClassX σ x)
    (_hbp : ∀ ψ : MulAut (C0 σ), ¬ ∀ φ ∈ E.map (MulAut.congr ψ).toMonoidHom,
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
        (graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hq : (ℓ ^ f) % 3 = 2) :
    uniPlaneClosure ℓ E = ⊤ := by
  classical
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
  have hcx1 : MulAut.conj x ≠ 1 := fun h0 => hx1 (hinj (h0.trans (map_one _).symm))
  obtain ⟨β, hβE, hβ1, y, hyc, hmove, hcomm⟩ :=
    Inputs2311x.exists_moving_rElt_minus_inputs2311x Inputs2311v.triOddA2Escape_holds hℓ hℓ2 hℓ3 hf hq
      hK σ hσ E x hE hcard hout hng hnc hx3 hx1 hcx
  refine uniTwoLineGen_of_core hCore ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ x y hx3 hx1 hX hcomm hmove
    (uniPlaneClosure ℓ E) ?_ ?_
  ·
    rintro k ⟨hkx, n, hn⟩
    refine mem_uniPlaneClosure hcx hcx1 ?_ hn
    rw [MulAut.conj_apply, ← hkx, mul_inv_cancel_right]
  ·
    refine (Subgroup.closure_le _).2 ?_ hyc
    rintro w ⟨hw, n, hn⟩
    exact mem_uniPlaneClosure hβE hβ1 hw hn

theorem triXNoGCentUniPlanesAt_two_of_core (hCore : FrameCoreTransvection) :
    TriXPlus.TriXNoGCentUniPlanesAt 2 := by
  intro ℓ f hℓ hℓ2 hℓ3 hf hq K _ _ hK σ hσ E x hE hcard hout hng hnc hx3 hx1 hcx hX hbp
  exact uniPlaneClosure_eq_top_minus_inputs2311y hCore ℓ f hℓ hℓ2 hℓ3 hf K hK σ hσ E x hE hcard hout
    hng hnc hx3 hx1 hcx hX hbp hq

end Planes

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311y
