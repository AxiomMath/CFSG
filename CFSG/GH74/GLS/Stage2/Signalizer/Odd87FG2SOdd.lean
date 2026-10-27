module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem split_of_involutive {A : Type*} [CommGroup A] (φ : A →* A) (hφ : ∀ x, φ (φ x) = x)
    {k : ℕ} (w : A) (hk : w ^ (2 * k) = w) :
    ∃ a b : A, φ a = a ∧ φ b = b⁻¹ ∧ w = a * b := by
  refine ⟨(w * φ w) ^ k, (w * (φ w)⁻¹) ^ k, ?_, ?_, ?_⟩
  · rw [map_pow, map_mul, hφ, mul_comm]
  · rw [map_pow, map_mul, map_inv, hφ, ← inv_pow, mul_inv, inv_inv, mul_comm]
  · rw [← mul_pow, mul_mul_mul_comm, mul_inv_cancel, mul_one, ← sq, ← pow_mul, hk]

theorem odd_abelian_split {K : Type} [Group K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (W : Subgroup K)
    (hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hexp : ∀ w ∈ W, w ^ p = 1) (e : K) (he : e * e = 1)
    (hnorm : ∀ w ∈ W, e * w * e⁻¹ ∈ W) :
    ∀ w ∈ W, ∃ a ∈ W, ∃ b ∈ W, e * a * e⁻¹ = a ∧ e * b * e⁻¹ = b⁻¹ ∧ w = a * b := by
  let _ : CommGroup W :=
    { (inferInstance : Group W) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  let φ : W →* W :=
    { toFun := fun x => ⟨e * x * e⁻¹, hnorm x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hφ : ∀ x, φ (φ x) = x := fun x => Subtype.ext (by
    show e * (e * (x : K) * e⁻¹) * e⁻¹ = x
    rw [heinv]
    calc e * (e * (x : K) * e) * e = (e * e) * (x : K) * (e * e) := by simp only [mul_assoc]
      _ = x := by rw [he]; simp)
  intro w hw
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hk : (⟨w, hw⟩ : W) ^ (2 * (m + 1)) = ⟨w, hw⟩ := by
    have h1 : ((⟨w, hw⟩ : W)) ^ p = 1 := Subtype.ext (hexp w hw)
    calc (⟨w, hw⟩ : W) ^ (2 * (m + 1)) = (⟨w, hw⟩ : W) ^ (p + 1) := by congr 1; omega
      _ = ⟨w, hw⟩ := by rw [pow_succ, h1, one_mul]
  obtain ⟨a, b, ha, hb, hab⟩ := split_of_involutive φ hφ _ hk
  refine ⟨a, a.2, b, b.2, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val ha
  · exact congrArg Subtype.val hb
  · exact congrArg Subtype.val hab

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
