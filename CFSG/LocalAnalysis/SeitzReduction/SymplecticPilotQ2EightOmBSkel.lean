module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (coords)

@[expose] def SpTwoAToralAt (N j : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → ∀ hN : 1 ≤ N,
    ∀ (H : Type) [Group H] (Φ₁ Φ₂ : StatedSp N K →* H), Function.Injective Φ₁ →
      Function.Injective Φ₂ → Φ₁ (spARep N j) = Φ₂ (spARep N j) →
      (∀ y ∈ centralizer ({spARep N j} : Set (StatedSp N K)), Odd (orderOf y) →
        Φ₁ y ∈ (centralizer ({spARep N j} : Set (StatedSp N K))).map Φ₂) →
      (∀ y ∈ centralizer ({spARep N j} : Set (StatedSp N K)), Odd (orderOf y) →
        Φ₂ y ∈ (centralizer ({spARep N j} : Set (StatedSp N K))).map Φ₁) →
      ∃ P : Subgroup (StatedSp N K), ⁅P, P⁆ = P ∧
        P ≤ centralizer ((((nsTorusSp K (⟨N - 1, by omega⟩ : Fin N)).map Φ₁).comap Φ₂ :
          Subgroup (StatedSp N K)) : Set (StatedSp N K)) ∧
        ¬ P ≤ centralizer ({spARep N j} : Set (StatedSp N K))

section Torus

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem false_of_planeTorus_of_at {N j : ℕ} (hmodel : SpTwoAToralAt N j) (hK : Nat.card K = 2)
    (hN : 1 ≤ N) (e : L ≃* StatedSp N K) {G₀ : Subgroup G} (hLG : L ≤ G₀)
    (hnb : centralizerPerfectCore (modelToG e (nsTorusSp K (⟨N - 1, by omega⟩ : Fin N))) ≤ G₀)
    (hjN : 2 * j < N) {t' c' : G} (hc'L : c' ∈ L)
    (Φ₂ : StatedSp N K →* G) (hΦ₂ : Function.Injective Φ₂)
    (hΦ₂t : ∀ y, Φ₂ y * t' = t' * Φ₂ y)
    (hxa : c'⁻¹ * ((e.symm (spARep N j) : L) : G) * c' = Φ₂ (spARep N j))
    (hodd₁ : ∀ y ∈ centralizer ({spARep N j} : Set (StatedSp N K)), Odd (orderOf y) →
      ∃ y' ∈ centralizer ({spARep N j} : Set (StatedSp N K)),
        Φ₂ y' = c'⁻¹ * ((e.symm y : L) : G) * c')
    (hodd₂ : ∀ y ∈ centralizer ({spARep N j} : Set (StatedSp N K)), Odd (orderOf y) →
      ∃ y' ∈ centralizer ({spARep N j} : Set (StatedSp N K)),
        c'⁻¹ * ((e.symm y' : L) : G) * c' = Φ₂ y)
    (hfin : ∀ z ∈ G₀, z * t' = t' * z → z * Φ₂ (spARep N j) = Φ₂ (spARep N j) * z) :
    False := by
  set a : StatedSp N K := spARep N j with ha
  set Φ₁ : StatedSp N K →* G :=
    (MulAut.conj c'⁻¹).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom) with hΦ₁
  have hΦ₁apply : ∀ y, Φ₁ y = c'⁻¹ * ((e.symm y : L) : G) * c' := fun y => by
    simp [hΦ₁]
  have hΦ₁inj : Function.Injective Φ₁ := by
    intro y y' h
    rw [hΦ₁apply, hΦ₁apply] at h
    have h1 : ((e.symm y : L) : G) = ((e.symm y' : L) : G) := by
      have := congrArg (fun z => c' * z * c'⁻¹) h
      simpa [mul_assoc] using this
    exact e.symm.injective (Subtype.ext h1)
  obtain ⟨P, hPperf, hPc, hPa⟩ := hmodel K hK hN G Φ₁ Φ₂ hΦ₁inj hΦ₂
    (by rw [hΦ₁apply, hxa])
    (fun y hy hyo => by
      obtain ⟨y', hy', h⟩ := hodd₁ y hy hyo
      exact ⟨y', hy', by rw [h, hΦ₁apply]⟩)
    (fun y hy hyo => by
      obtain ⟨y', hy', h⟩ := hodd₂ y hy hyo
      exact ⟨y', hy', by rw [hΦ₁apply, h]⟩)
  set X : Subgroup (StatedSp N K) := nsTorusSp K (⟨N - 1, by omega⟩ : Fin N) with hX
  have hXC : X ≤ centralizer ({a} : Set (StatedSp N K)) :=
    nsTorusSp_le_centralizer_spARep (by simp only; omega)
  have hXodd : ∀ ξ ∈ X, Odd (orderOf ξ) := by
    intro ξ hξ
    have h1 : orderOf (⟨ξ, hξ⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hX, card_nsTorusSp] at h1
    exact Odd.of_dvd_nat (by decide) h1
  have hPX : ∀ p ∈ P, ∀ ξ ∈ X, Φ₁ ξ * Φ₂ p = Φ₂ p * Φ₁ ξ := by
    intro p hp ξ hξ
    obtain ⟨ξ', hξ'C, hξ'⟩ := hodd₁ ξ (hXC hξ) (hXodd ξ hξ)
    have hmem : ξ' ∈ (X.map Φ₁).comap Φ₂ := by
      show Φ₂ ξ' ∈ X.map Φ₁
      exact ⟨ξ, hξ, by rw [hξ', hΦ₁apply]⟩
    have h1 := mem_centralizer_iff.1 (hPc hp) ξ' hmem
    rw [hΦ₁apply, ← hξ', ← map_mul, ← map_mul, h1]
  set P₁ : Subgroup G := (P.map Φ₂).map (MulAut.conj c').toMonoidHom with hP₁
  have hP₁perf : ⁅P₁, P₁⁆ = P₁ := by
    rw [hP₁, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hPperf]
  have hP₁C : P₁ ≤ centralizer (modelToG e X : Set G) := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨ξ, hξ, rfl⟩ := (mem_modelToG e).1 hh
    have h1 := hPX p hp ξ hξ
    rw [hΦ₁apply] at h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc ((e.symm ξ : L) : G) * (c' * Φ₂ p * c'⁻¹) =
        c' * ((c'⁻¹ * ((e.symm ξ : L) : G) * c') * Φ₂ p) * c'⁻¹ := by group
      _ = c' * (Φ₂ p * (c'⁻¹ * ((e.symm ξ : L) : G) * c')) * c'⁻¹ := by rw [h1]
      _ = c' * Φ₂ p * c'⁻¹ * ((e.symm ξ : L) : G) := by group
  have hP₁G : P₁ ≤ G₀ := (F4Pilot.le_centralizerPerfectCore hP₁perf hP₁C).trans hnb
  apply hPa
  intro p hp
  have hc'G : c' ∈ G₀ := hLG hc'L
  have hpG : Φ₂ p ∈ G₀ := by
    have h1 : c' * Φ₂ p * c'⁻¹ ∈ G₀ := hP₁G ⟨Φ₂ p, ⟨p, hp, rfl⟩, rfl⟩
    have h2 := G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hc'G) h1) hc'G
    simpa [mul_assoc] using h2
  have h3 := hfin (Φ₂ p) hpG (hΦ₂t p)
  rw [← map_mul, ← map_mul] at h3
  exact mem_centralizer_singleton_iff.2 (hΦ₂ h3)

end Torus

end CFSG.SeitzReduction.SymplecticPilot
