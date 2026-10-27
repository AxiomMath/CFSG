module

public import CFSG.GH74.Uniqueness.Section7Prop74Def
public import CFSG.GH74.Uniqueness.Section7ZStar
public import CFSG.GH74.Uniqueness.Section7Lemma311

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem conjSet_eq_of_mem_normalizer {K : Set X} {u : X} (hu : u ∈ normalizer K) :
    conjSet K u = K := by
  have hu' : u⁻¹ ∈ normalizer K := (normalizer K).inv_mem hu
  change ∀ n : X, n ∈ K ↔ u * n * u⁻¹ ∈ K at hu
  change ∀ n : X, n ∈ K ↔ u⁻¹ * n * u⁻¹⁻¹ ∈ K at hu'
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have := (hu' k).mp hk
    rwa [inv_inv] at this
  · intro hy
    refine ⟨u * y * u⁻¹, (hu y).mp hy, ?_⟩
    group

theorem ZDSetup.prop74_of_not_centralizer_le
    (S : ZDSetup X Z M) {z : X} {p : ℕ}
    {W : Subgroup X} (hW : T4Cand Z M z p W)
    (hC : ¬ centralizer (CFSG.OddInversion.invertedSet W z : Set X) ≤ M) :
    ∃ Γ : Set (Subgroup X), Prop74Spec Z M z W Γ := by
  have hZ := S.invariant
  have h := S.prodDisc
  have hz := hW.mem_Z
  have hzM := hW.mem_M
  have hz2 : orderOf z = 2 := hZ.1 z hz
  have hzz : z * z = 1 := hZ.mul_self_eq_one hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hKW : Subgroup.closure (CFSG.OddInversion.invertedSet W z) = W :=
    hW.closure_invertedSet hZ
  have hZS := S.isZStarIn_centralizer_sup hW hC
  have hzHs : z ∈ centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hHsM : ¬ (centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z ≤ M) :=
    fun hle => hC (le_sup_left.trans hle)
  have hcentHs : ∀ c ∈ centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z,
      c * z = z * c → c ∈ M := fun c _ hc =>
    h.centralizer_le_of_mem hz hzM (Subgroup.mem_centralizer_singleton_iff.mpr hc)
  obtain ⟨R, hRHs, hcard, hzΓ, hfix, hswap⟩ := lemma311_omega h hz2 hzHs hZS hHsM hcentHs
  refine ⟨omegaOrbit M R, ?_⟩
  have hzK : z ∈ normalizer (CFSG.OddInversion.invertedSet W z : Set X) := by
    change ∀ n : X, n ∈ CFSG.OddInversion.invertedSet W z ↔
      z * n * z⁻¹ ∈ CFSG.OddInversion.invertedSet W z
    intro k
    constructor
    · intro hk
      rw [hk.2]
      exact CFSG.OddInversion.invertedSet_inv hk
    · intro hk
      have e : z * (z * k * z⁻¹) * z⁻¹ = k := by
        rw [hzi]
        calc z * (z * k * z) * z = (z * z) * k * (z * z) := by group
          _ = k := by rw [hzz]; group
      have e2 : z * (z * k * z⁻¹) * z⁻¹ = (z * k * z⁻¹)⁻¹ := hk.2
      rw [e] at e2
      rw [e2]
      exact CFSG.OddInversion.invertedSet_inv hk
  have hHsK : centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z ≤
      normalizer (CFSG.OddInversion.invertedSet W z : Set X) :=
    sup_le (Subgroup.centralizer_le_normalizer _) (by rw [Subgroup.zpowers_le]; exact hzK)
  have hHsW : centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z ≤
      normalizer (W : Set X) := by
    refine sup_le (fun c hc => ?_) (by rw [Subgroup.zpowers_le]; exact hW.normalizes)
    have h1 := Subgroup.centralizer_closure (CFSG.OddInversion.invertedSet W z)
    rw [hKW] at h1
    exact Subgroup.centralizer_le_normalizer _ (h1 ▸ hc)
  have hbase : M ∈ omegaOrbit M R := ⟨1, R.one_mem, conjugate_one M⟩
  have hsub : omegaOrbit M R ⊆ omegaFix M (W : Set X) := by
    rintro β ⟨ρ, hρ, rfl⟩
    refine h.mem_omegaFix_iff.mpr ⟨⟨ρ, rfl⟩, fun w hw => ?_⟩
    have hρN := hHsW (hRHs hρ)
    have := (Subgroup.mem_normalizer_iff.mp hρN w).mp hw
    exact mem_conjugate_iff.mpr (hW.le_M this)
  refine ⟨hsub, hbase, hcard, hzΓ, ?_, ?_⟩
  ·
    intro β hβ γ hγ hβγ x hx
    have hxHs : x ∈ centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z :=
      Subgroup.mem_sup_left hx.1.1
    exact hfix β hβ γ hγ hβγ x hxHs hx.1.2 hx.2 M hbase
  ·
    intro β hβ hβM
    have hβΩ : β ∈ omegaFix M (W : Set X) := hsub hβ
    have hβz : conjugate β z ∈ omegaFix M (W : Set X) := hsub (hzΓ β hβ)
    have hWβ : W ≤ β := (h.mem_omegaFix_iff.mp hβΩ).2
    have hWβz : W ≤ conjugate β z := (h.mem_omegaFix_iff.mp hβz).2
    have hWE : W ≤ M ⊓ β ⊓ conjugate β z := le_inf (le_inf hW.le_M hWβ) hWβz
    obtain ⟨σ, hσR, hσ⟩ := hswap β hβ hβM
    have htZ : σ⁻¹ * z * σ ∈ Z := hZ.2 z hz σ
    have htHs : σ⁻¹ * z * σ ∈ centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔
        zpowers z :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hRHs hσR)) hzHs) (hRHs hσR)
    have huHs : z⁻¹ * (σ⁻¹ * z * σ) * z ∈
        centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzHs) htHs) hzHs
    have hconj : conjSet (CFSG.OddInversion.invertedSet W z) (z⁻¹ * (σ⁻¹ * z * σ) * z) =
        CFSG.OddInversion.invertedSet W z :=
      conjSet_eq_of_mem_normalizer (hHsK huHs)
    refine ⟨σ⁻¹ * z * σ, htZ, hσ, ?_, ?_, ?_⟩
    · rw [hconj]
      intro k hk
      exact hWE hk.1
    · rw [hconj]
      rintro x ⟨⟨hxC, hxM⟩, hxβ⟩
      have hxHs : x ∈ centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z :=
        Subgroup.mem_sup_left hxC
      have hxβz : x ∈ conjugate β z :=
        hfix M hbase β hβ (Ne.symm hβM) x hxHs hxM hxβ (conjugate β z) (hzΓ β hβ)
      exact ⟨⟨hxM, hxβ⟩, hxβz⟩
    · obtain ⟨ρ, hρR, hρ⟩ := hzΓ β hβ
      obtain ⟨σ', hσ'R, hσ'⟩ := hβ
      refine ⟨ρ⁻¹, ?_, ?_⟩
      · rw [← hρ, conjugate_conjugate, mul_inv_cancel, conjugate_one]
      · exact ⟨σ' * ρ⁻¹, R.mul_mem hσ'R (R.inv_mem hρR), by rw [← hσ', conjugate_conjugate]⟩

end CFSG.GH74.Uniqueness
