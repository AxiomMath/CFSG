module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenInLambda2 LargeEvenLabel
  LargeEvenRawDatum)

section Abstract

theorem l154_exists_centralQuotient {K G : Type} [Group K] [Group G] (hK : CFSG.IsQuasisimple K)
    {φ : K →* G} (hsurj : Function.Surjective φ) (hne : ∃ k, φ k ≠ 1) :
    ∃ θ : K ⧸ Subgroup.center K ≃* G ⧸ Subgroup.center G,
      ∀ k, θ (QuotientGroup.mk k) = QuotientGroup.mk (φ k) := by
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hK hne
  have hcen := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hK hsurj hker
  have hc : Subgroup.center K ≤ (Subgroup.center G).comap φ := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hsurj g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  let θ₀ : K ⧸ Subgroup.center K →* G ⧸ Subgroup.center G :=
    QuotientGroup.map (Subgroup.center K) (Subgroup.center G) φ hc
  have hθ₀ : ∀ k, θ₀ (QuotientGroup.mk k) = QuotientGroup.mk (φ k) := fun k => rfl
  have hinj : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [hθ₀, QuotientGroup.eq_one_iff, hcen] at hq
      obtain ⟨z, hz, hzk⟩ := hq
      have hzk' : z⁻¹ * k ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzk, inv_mul_cancel]
      have hk : k = z * (z⁻¹ * k) := by group
      rw [QuotientGroup.eq_one_iff, hk]
      exact (Subgroup.center K).mul_mem hz (hker hzk')
  have hsurj' : Function.Surjective θ₀ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, rfl⟩ := hsurj g
      exact ⟨QuotientGroup.mk k, rfl⟩
  exact ⟨MulEquiv.ofBijective θ₀ ⟨hinj, hsurj'⟩, hθ₀⟩

variable {M G C : Type} [Group M] [Group G] [Group C]

theorem l154_realized_of_map {j : G →* M} (hinj : Function.Injective j) {Q₀ : Subgroup G}
    (hX : CFSG.IsQuasisimple ↥(Q₀.map j)) (Ad : ↥Q₀ →* C) (hAd : Function.Surjective Ad)
    (hne : ∃ q, Ad q ≠ 1) {I : Set (MulAut (C ⧸ Subgroup.center C))}
    (hI : ∀ φ ∈ I, ∃ (α : MulAut C) (Wq : G),
      (∀ c, QuotientGroup.mk (α c) = φ (QuotientGroup.mk c)) ∧
      Wq ∈ Subgroup.normalizer (Q₀ : Set G) ∧
      ∀ q q' : ↥Q₀, Wq * (q : G) * Wq⁻¹ = (q' : G) → Ad q' = α (Ad q)) :
    CFSG.IsQuasisimple C ∧
      ∃ θ : ↥(Q₀.map j) ⧸ Subgroup.center ↥(Q₀.map j) ≃* C ⧸ Subgroup.center C,
        ∀ φ ∈ I, ∃ w ∈ Subgroup.normalizer ((Q₀.map j : Subgroup M) : Set M),
          LargeEvenInduces θ (fun r r' : ↥(Q₀.map j) => w * (r : M) * w⁻¹ = (r' : M)) φ := by
  classical
  let e : ↥Q₀ ≃* ↥(Q₀.map j) := Q₀.equivMapOfInjective j hinj
  let ψ : ↥(Q₀.map j) →* C := Ad.comp e.symm.toMonoidHom
  have hψs : Function.Surjective ψ := hAd.comp e.symm.surjective
  have hψe : ∀ q, ψ (e q) = Ad q := fun q => by simp [ψ]
  have hψ1 : ∃ x, ψ x ≠ 1 := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨e q, by rwa [hψe]⟩
  obtain ⟨θ, hmk⟩ := l154_exists_centralQuotient hX hψs hψ1
  refine ⟨CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hX hψs hψ1, θ, fun φ hφ => ?_⟩
  obtain ⟨α, Wq, hα, hW, hrel⟩ := hI φ hφ
  have hWinv : Wq⁻¹ ∈ Subgroup.normalizer (Q₀ : Set G) := Subgroup.inv_mem _ hW
  have hcoe : ∀ q : ↥Q₀, ((e q : ↥(Q₀.map j)) : M) = j (q : G) := fun q => rfl
  refine ⟨j Wq, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨Wq * q * Wq⁻¹, (Subgroup.mem_normalizer_iff.1 hW q).1 hq, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨q, hq, hqx⟩
      have h1 : x = j (Wq⁻¹ * q * Wq) := by
        simp only [map_mul, map_inv, hqx]
        group
      refine ⟨Wq⁻¹ * q * Wq, ?_, h1.symm⟩
      have := (Subgroup.mem_normalizer_iff.1 hWinv q).1 hq
      simpa using this
  · intro r r' hrr
    obtain ⟨q, rfl⟩ := e.surjective r
    obtain ⟨q', rfl⟩ := e.surjective r'
    have h1 : Wq * (q : G) * Wq⁻¹ = (q' : G) := by
      apply hinj
      rw [map_mul, map_mul, map_inv]
      simpa only [hcoe] using hrr
    rw [hmk, hmk, hψe, hψe, ← hα, hrel q q' h1]

theorem l154_realized_of_range {j : G →* M} (hj : Function.Injective j) {P : Type} [Group P]
    {ι : P →* G} (hι : Function.Injective ι) (hX : CFSG.IsQuasisimple ↥(j.comp ι).range)
    (Ad : P →* C) (hAd : Function.Surjective Ad) (hne : ∃ p, Ad p ≠ 1)
    {I : Set (MulAut (C ⧸ Subgroup.center C))}
    (hI : ∀ φ ∈ I, ∃ (α : MulAut C) (Wq : G),
      (∀ c, QuotientGroup.mk (α c) = φ (QuotientGroup.mk c)) ∧
      (∀ p, ∃ p', Wq * ι p * Wq⁻¹ = ι p') ∧ (∀ p, ∃ p', Wq⁻¹ * ι p * Wq = ι p') ∧
      ∀ p p', Wq * ι p * Wq⁻¹ = ι p' → Ad p' = α (Ad p)) :
    CFSG.IsQuasisimple C ∧
      ∃ θ : ↥(j.comp ι).range ⧸ Subgroup.center ↥(j.comp ι).range ≃* C ⧸ Subgroup.center C,
        ∀ φ ∈ I, ∃ w ∈ Subgroup.normalizer ((j.comp ι).range : Set M),
          LargeEvenInduces θ (fun r r' : ↥(j.comp ι).range => w * (r : M) * w⁻¹ = (r' : M)) φ := by
  classical
  have hjι : Function.Injective (j.comp ι) := hj.comp hι
  let e : P ≃* ↥(j.comp ι).range := MonoidHom.ofInjective hjι
  let ψ : ↥(j.comp ι).range →* C := Ad.comp e.symm.toMonoidHom
  have hψs : Function.Surjective ψ := hAd.comp e.symm.surjective
  have hψe : ∀ p, ψ (e p) = Ad p := fun p => by simp [ψ]
  have hψ1 : ∃ x, ψ x ≠ 1 := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨e p, by rwa [hψe]⟩
  obtain ⟨θ, hmk⟩ := l154_exists_centralQuotient hX hψs hψ1
  refine ⟨CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hX hψs hψ1, θ, fun φ hφ => ?_⟩
  obtain ⟨α, Wq, hα, hW, hW', hrel⟩ := hI φ hφ
  have hcoe : ∀ p, ((e p : ↥(j.comp ι).range) : M) = j (ι p) := fun p => rfl
  refine ⟨j Wq, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨p', hp'⟩ := hW p
      refine ⟨p', ?_⟩
      simp only [MonoidHom.comp_apply, ← hp', map_mul, map_inv]
    · rintro ⟨p, hpx⟩
      obtain ⟨p', hp'⟩ := hW' p
      refine ⟨p', ?_⟩
      have h1 : x = j (Wq⁻¹ * ι p * Wq) := by
        simp only [MonoidHom.comp_apply, map_mul, map_inv] at hpx ⊢
        rw [hpx]
        group
      rw [h1, hp']
      rfl
  · intro r r' hrr
    obtain ⟨p, rfl⟩ := e.surjective r
    obtain ⟨p', rfl⟩ := e.surjective r'
    have h1 : Wq * ι p * Wq⁻¹ = ι p' := by
      apply hj
      rw [map_mul, map_mul, map_inv]
      simpa only [hcoe] using hrr
    rw [hmk, hmk, hψe, hψe, ← hα, hrel p p' h1]

end Abstract

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
