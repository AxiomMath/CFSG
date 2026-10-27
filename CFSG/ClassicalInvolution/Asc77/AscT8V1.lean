module

public import CFSG.ClassicalInvolution.SmallCases.DSplitEdge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups commutatorElement

namespace T8V

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem commutator_mem_oddCoreIn_of_pow (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {N : Subgroup G} {z : G} (hN : IsClassicalMember p f N z) {R : Subgroup G}
    (hR : IsSylow2In R N) {a : G} (haN : a ∈ Subgroup.normalizer (N : Set G)) {m : ℕ}
    (ham : a ^ 2 ^ m = 1) (haR : ∀ r ∈ R, a * r = r * a) :
    ∀ x ∈ N, ⁅a, x⁆ ∈ oddCoreIn N := by
  obtain ⟨e⟩ := hN.nonempty_equiv
  set O : Subgroup ↥N := classicalInvolutionOddCore ↥N with hO
  set α : MulAut ↥N := N.normalizerMonoidHom ⟨a, haN⟩ with hα
  have hαO : O.map α.toMonoidHom = O :=
    CFSG.ComponentClassification.OddCore.char_invariant α
  set ᾱ : MulAut (↥N ⧸ O) := QuotientGroup.congr O O α hαO with hᾱ
  set β : MulAut SL(2, GaloisField p f) := MulAut.congr e ᾱ with hβ
  have hαapp : ∀ y : ↥N, ((α y : ↥N) : G) = a * (y : G) * a⁻¹ := by
    intro y
    rw [hα]
    simp
  have hαα : α ^ 2 ^ m = 1 := by
    rw [hα, ← map_pow]
    have : (⟨a, haN⟩ ^ 2 ^ m : ↥(Subgroup.normalizer (N : Set G))) = 1 :=
      Subtype.ext ham
    rw [this, map_one]
  have hkey : ∀ y : ↥N, ᾱ (QuotientGroup.mk y) = QuotientGroup.mk (α y) := fun y => rfl
  have hkeyk : ∀ (k : ℕ) (y : ↥N), (ᾱ ^ k) (QuotientGroup.mk y) = QuotientGroup.mk ((α ^ k) y) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, hkey, ih, pow_succ, MulAut.mul_apply]
  have hᾱ2 : ᾱ ^ 2 ^ m = 1 := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [hkeyk, hαα]
      rfl
  have hβ2 : β ^ 2 ^ m = 1 := by
    rw [hβ, ← map_pow, hᾱ2, map_one]
  let φ : ↥N →* SL(2, GaloisField p f) := e.toMonoidHom.comp (QuotientGroup.mk' O)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective O)
  let P : Sylow 2 SL(2, GaloisField p f) := Sylow.mapSurjective hφ (sylowOf2In hR)
  have hfix : ∀ x ∈ P, β x = x := by
    intro x hx
    have hx' : x ∈ (sylowOf2In hR : Subgroup ↥N).map φ := by
      have := Sylow.coe_mapSurjective hφ (sylowOf2In hR)
      rw [← this]
      exact hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hrR : (r : G) ∈ R := hr
    have hαr : α r = r := by
      apply Subtype.ext
      rw [hαapp]
      have := haR r hrR
      calc a * (r : G) * a⁻¹ = (r : G) * a * a⁻¹ := by rw [this]
        _ = r := by group
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [hβ, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hkey, hαr]
  have hβ1 : β = 1 := AscL62.mulAut_eq_one_of_pow_two_pow_eq_one hp2 hq P m β hβ2 hfix
  intro x hx
  have h1 : ᾱ (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨x, hx⟩ := by
    have h2 : β (e (QuotientGroup.mk ⟨x, hx⟩)) = e (QuotientGroup.mk ⟨x, hx⟩) := by
      rw [hβ1]
      rfl
    rw [hβ, MulAut.congr_apply] at h2
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    exact e.injective h2
  rw [hkey] at h1
  have h4 : α ⟨x, hx⟩ / ⟨x, hx⟩ ∈ O := QuotientGroup.eq_iff_div_mem.mp h1
  refine ⟨α ⟨x, hx⟩ / ⟨x, hx⟩, h4, ?_⟩
  have h5 : N.subtype (α ⟨x, hx⟩ / ⟨x, hx⟩) = ((α ⟨x, hx⟩ : ↥N) : G) / x := by
    rw [map_div]
    rfl
  rw [h5, hαapp, commutatorElement_def]
  simp [div_eq_mul_inv]

end T8V

end CFSG.ClassicalInvolution.Asc77
