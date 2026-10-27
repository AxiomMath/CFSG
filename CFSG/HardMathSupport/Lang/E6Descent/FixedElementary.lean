module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeGroup

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.AGLEmbedding.FixedThree

theorem card_le_card_ker_cube {A : Type*} [Group A] [Finite A] (φ : A →* A)
    (h3 : ∀ a, φ (φ (φ a)) = 1) : Nat.card A ≤ Nat.card φ.ker ^ 3 := by
  have hA := Subgroup.card_ker_mul_card_range φ
  let ψ : φ.range →* φ.range :=
    (φ.comp φ.range.subtype).codRestrict φ.range fun x => ⟨x.1, rfl⟩
  have hψ : ∀ x : φ.range, ((ψ x : φ.range) : A) = φ x := fun x => rfl
  have hR := Subgroup.card_ker_mul_card_range ψ
  have hker : Nat.card ψ.ker ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : φ.range) : A), ?_⟩) ?_
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx ⊢
      have := congrArg (fun y : φ.range => (y : A)) hx
      simpa [hψ] using this
    · intro a b hab
      have := congrArg (fun y : φ.ker => (y : A)) hab
      exact Subtype.ext (Subtype.ext this)
  have hrange : Nat.card ψ.range ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective (fun y => ⟨(((y : ψ.range) : φ.range) : A), ?_⟩) ?_
    · obtain ⟨y', w, rfl⟩ := y
      obtain ⟨z, a, rfl⟩ := w
      show φ (φ (φ a)) = 1
      exact h3 a
    · intro a b hab
      have := congrArg (fun y : φ.ker => (y : A)) hab
      exact Subtype.ext (Subtype.ext this)
  have hRle : Nat.card φ.range ≤ Nat.card φ.ker ^ 2 := by
    rw [← hR, pow_two]
    exact Nat.mul_le_mul hker hrange
  rw [← hA, pow_succ, pow_two]
  have := Nat.mul_le_mul_left (Nat.card φ.ker) hRle
  calc Nat.card φ.ker * Nat.card φ.range
      ≤ Nat.card φ.ker * Nat.card φ.ker ^ 2 := this
    _ = Nat.card φ.ker * Nat.card φ.ker * Nat.card φ.ker := by ring

end CFSG.HardMathSupport.Lang.E6Descent

namespace CFSG.HardMathSupport.Lang.E6Descent

theorem commutator_cube_eq_one {E : Type*} [CommGroup E] (c : E →* E) (hc : ∀ a, c (c (c a)) = a)
    (hexp : ∀ a : E, a ^ 3 = 1) (a : E) :
    let φ : E →* E := c / MonoidHom.id E
    φ (φ (φ a)) = 1 := by
  intro φ
  have h1 : ∀ x, φ x = c x * x⁻¹ := fun x => by simp [φ, div_eq_mul_inv]
  have key : φ (φ (φ a)) = (c a) ^ 3 * ((c (c a)) ^ 3)⁻¹ := by
    simp only [h1, map_mul, map_inv, hc, mul_inv_rev, inv_inv]
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
    simp only [mul_assoc, mul_comm, mul_left_comm]
    simp
  rw [key, hexp, hexp]
  simp

end CFSG.HardMathSupport.Lang.E6Descent

namespace CFSG.HardMathSupport.Lang.E6Descent

theorem card_le_card_centralizer_cube {X : Type*} [Group X] (E : Subgroup X) [Finite E]
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ 3 = 1)
    {u : X} (hu : u ^ 3 = 1) (hN : u ∈ Subgroup.normalizer (E : Set X)) :
    Nat.card E ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({u} : Set X)) ^ 3 := by
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hmem : ∀ e : E, u * (e : X) * u⁻¹ ∈ E := fun e =>
    (Subgroup.mem_normalizer_iff.mp hN e).1 e.2
  let c : E →* E :=
    { toFun := fun e => ⟨u * (e : X) * u⁻¹, hmem e⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hc3 : ∀ a, c (c (c a)) = a := fun a => Subtype.ext (by
    show u * (u * (u * (a : X) * u⁻¹) * u⁻¹) * u⁻¹ = a
    have : u * (u * (u * (a : X) * u⁻¹) * u⁻¹) * u⁻¹ = u ^ 3 * (a : X) * (u ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [this, hu]; simp)
  set φ : E →* E := c / MonoidHom.id E with hφ
  have hφ3 : ∀ a, φ (φ (φ a)) = 1 := fun a =>
    commutator_cube_eq_one c hc3 (fun x => Subtype.ext (by simpa using hexp x x.2)) a
  have := card_le_card_ker_cube φ hφ3
  have : Finite ↥(E ⊓ Subgroup.centralizer ({u} : Set X)) :=
    Finite.of_injective (fun x : ↥(E ⊓ Subgroup.centralizer ({u} : Set X)) => (⟨x.1, x.2.1⟩ : E))
      (fun a b h => Subtype.ext (congrArg (fun y : E => (y : X)) h))
  refine (card_le_card_ker_cube φ hφ3).trans (Nat.pow_le_pow_left ?_ 3)
  refine Nat.card_le_card_of_injective (fun x => ⟨((x : E) : X), ?_⟩) ?_
  · have hx := x.2
    rw [MonoidHom.mem_ker] at hx
    refine ⟨(x : E).2, ?_⟩
    show ((x : E) : X) ∈ Subgroup.centralizer ({u} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c x * (x : E)⁻¹ = 1 := by simpa [hφ, div_eq_mul_inv] using hx
    have h2 : c x = x := mul_inv_eq_one.mp h1
    have h3 := congrArg (fun y : E => (y : X)) h2
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk] at h3
    have h4 : u * ((x : E) : X) = ((x : E) : X) * u := by
      calc u * ((x : E) : X) = (u * ((x : E) : X) * u⁻¹) * u := by group
        _ = ((x : E) : X) * u := by rw [h3]
    exact h4.symm
  · intro a b hab
    have := congrArg (fun y : ↥(E ⊓ Subgroup.centralizer ({u} : Set X)) => (y : X)) hab
    exact Subtype.ext (Subtype.ext this)

end CFSG.HardMathSupport.Lang.E6Descent
