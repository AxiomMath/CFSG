module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerAbs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section FaithfulInner

variable {X P : Type} [Group X] [Group P] {θ : X →* MulAut P} {ι : P →* X}

theorem mulAut_conj_conj (φ : MulAut P) (p : P) :
    φ * MulAut.conj p * φ⁻¹ = MulAut.conj (φ p) := by
  ext q
  simp [MulAut.conj_apply]

theorem ι_injective (hι : ∀ p, θ (ι p) = MulAut.conj p)
    (hZ : ∀ p : P, (∀ q, p * q = q * p) → p = 1) : Function.Injective ι := by
  rw [injective_iff_map_eq_one]
  intro p hp
  apply hZ
  intro q
  have h1 : MulAut.conj p = 1 := by rw [← hι, hp, map_one]
  have h2 := congrArg (fun φ : MulAut P => φ q) h1
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  calc p * q = (p * q * p⁻¹) * p := by group
    _ = q * p := by rw [h2]

theorem conj_ι (hθ : Function.Injective θ) (hι : ∀ p, θ (ι p) = MulAut.conj p) (x : X) (p : P) :
    x * ι p * x⁻¹ = ι (θ x p) := by
  apply hθ
  rw [map_mul, map_mul, map_inv, hι, hι]
  exact mulAut_conj_conj (θ x) p

theorem range_normal (hθ : Function.Injective θ) (hι : ∀ p, θ (ι p) = MulAut.conj p) :
    ι.range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hn
  rw [conj_ι hθ hι]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem ι_commute_iff (hθ : Function.Injective θ) (hι : ∀ p, θ (ι p) = MulAut.conj p)
    (hι' : Function.Injective ι) (a : X) (p : P) :
    a * ι p = ι p * a ↔ θ a p = p := by
  constructor
  · intro h
    have h1 : a * ι p * a⁻¹ = ι p := by rw [h]; group
    rw [conj_ι hθ hι] at h1
    exact hι' h1
  · intro h
    have h1 := conj_ι hθ hι a p
    rw [h] at h1
    calc a * ι p = (a * ι p * a⁻¹) * a := by group
      _ = ι p * a := by rw [h1]

end FaithfulInner

theorem openQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

section FaithfulInner

variable {X P : Type} [Group X] [Group P] {θ : X →* MulAut P} {ι : P →* X}

theorem layerData_of_fix [Finite X] (hθ : Function.Injective θ)
    (hι : ∀ p, θ (ι p) = MulAut.conj p) (hZ : ∀ p : P, (∀ q, p * q = q * p) → p = 1)
    {B : Subgroup X} {a : X} {Q : Subgroup P} (hfix : ∀ q ∈ Q, θ a q = q)
    (hnorm : ∀ g : P, θ a g = g → ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hperf : Q ≤ ⁅Q, Q⁆)
    (hgen : ∃ 𝓗 : Set (Subgroup P), (∀ H ∈ 𝓗, H ≤ Q ∧ CFSG.Open.IsQuasisimple ↥H ∧
      ∀ p ∈ Q, ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧ Q ≤ ⨆ H ∈ 𝓗, H)
    (hcover : B ≤ Subgroup.zpowers a ⊔ Q.map ι) :
    LayerData ι.range B a (Q.map ι) := by
  have hι' := ι_injective hι hZ
  refine ⟨?_, ?_, ?_, ?_, hcover⟩
  · rintro _ ⟨q, hq, rfl⟩
    refine ⟨⟨q, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (ι_commute_iff hθ hι hι' y q).mpr (hfix q hq)
  · rintro _ ⟨hxr, hxc⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨g, rfl⟩ := hxr
    have hc : a * ι g = ι g * a :=
      (Subgroup.mem_centralizer_iff.mp hxc a rfl)
    have hg : θ a g = g := (ι_commute_iff hθ hι hι' a g).mp hc
    refine ⟨g * q * g⁻¹, hnorm g hg q hq, ?_⟩
    simp
  · have := Subgroup.map_mono (f := ι) hperf
    rwa [Subgroup.map_commutator] at this
  · obtain ⟨𝓗, h𝓗, hQ⟩ := hgen
    refine ⟨(fun H => H.map ι) '' 𝓗, ?_, ?_⟩
    · rintro _ ⟨H, hH, rfl⟩
      obtain ⟨hHQ, hHq, hHn⟩ := h𝓗 H hH
      refine ⟨Subgroup.map_mono hHQ, ?_, ?_⟩
      · exact openQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective H ι hι') hHq
      · rintro _ ⟨q, hq, rfl⟩ _ ⟨h, hh, rfl⟩
        exact ⟨q * h * q⁻¹, hHn q hq h hh, by simp⟩
    · refine (Subgroup.map_mono hQ).trans ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun H => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hH => ?_
      exact le_iSup₂_of_le (H.map ι) ⟨H, hH, rfl⟩ le_rfl

theorem eq_one_of_fix_of_sup_eq_top (hθ : Function.Injective θ)
    (hι : ∀ p, θ (ι p) = MulAut.conj p) (hZ : ∀ p : P, (∀ q, p * q = q * p) → p = 1)
    {Q₁ Q₂ : Subgroup P} (hsup : Q₁ ⊔ Q₂ = ⊤) {x : X}
    (h₁ : ∀ p ∈ Q₁.map ι, x * p = p * x) (h₂ : ∀ p ∈ Q₂.map ι, x * p = p * x) : x = 1 := by
  have hι' := ι_injective hι hZ
  have hle : Q₁ ⊔ Q₂ ≤ MonoidHom.eqLocus (θ x : MulAut P).toMonoidHom (MonoidHom.id P) := by
    refine sup_le (fun q hq => ?_) (fun q hq => ?_)
    · exact (ι_commute_iff hθ hι hι' x q).mp (h₁ (ι q) ⟨q, hq, rfl⟩)
    · exact (ι_commute_iff hθ hι hι' x q).mp (h₂ (ι q) ⟨q, hq, rfl⟩)
  have hθx : θ x = 1 := by
    ext q
    have := hle (hsup ▸ Subgroup.mem_top q)
    simpa using this
  exact hθ (hθx.trans (map_one θ).symm)

end FaithfulInner

end CFSG.ClassicalInvolution.ModelFacts.Orth15
