module

public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusData
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.ClassicalInvolution.WeakCT.SU4

namespace CompsPTwoDKlein

section General

variable {F K : Type} [Field F] [Field K] [Algebra F K] (σ₀ : K ≃+* K)

theorem exists_kleinData_of_fixed (hσσ : ∀ x, σ₀ (σ₀ x) = x)
    (hfix : ∀ r : F, σ₀ (algebraMap F K r) = algebraMap F K r)
    (hfix' : ∀ y : K, σ₀ y = y → ∃ r : F, algebraMap F K r = y) (hne : ∃ y : K, σ₀ y ≠ y)
    (h2 : (2 : K) ≠ 0) :
    ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧ Nonempty (KleinData F K σ₀ b c) := by
  obtain ⟨x, hx⟩ := hne
  have hsum : σ₀ (-(x + σ₀ x)) = -(x + σ₀ x) := by rw [map_neg, map_add, hσσ]; ring
  have hprod : σ₀ (x * σ₀ x) = x * σ₀ x := by rw [map_mul, hσσ]; ring
  obtain ⟨b, hb⟩ := hfix' _ hsum
  obtain ⟨c, hc⟩ := hfix' _ hprod
  have hd : x - σ₀ x ≠ 0 := sub_ne_zero.2 (fun h => hx h.symm)
  have h2' : algebraMap F K (2 : F) = (2 : K) := map_ofNat (algebraMap F K) 2
  have hωsq : x ^ 2 + algebraMap F K b * x + algebraMap F K c = 0 := by
    rw [hb, hc]
    ring
  have hσω : σ₀ x = -algebraMap F K b - x := by
    rw [hb]
    ring
  have hspan : ∀ y : K, ∃ u v : F, y = algebraMap F K u - algebraMap F K v * x := by
    intro y
    obtain ⟨t, htdef⟩ : ∃ t : K, t * (x - σ₀ x) = y - σ₀ y :=
      ⟨(y - σ₀ y) / (x - σ₀ x), div_mul_cancel₀ _ hd⟩
    have hs : σ₀ (y + σ₀ y) = y + σ₀ y := by rw [map_add, hσσ]; ring
    have ht : σ₀ t = t := by
      have h1 := congrArg σ₀ htdef
      rw [map_mul, map_sub, map_sub, hσσ, hσσ] at h1
      apply mul_right_cancel₀ hd
      linear_combination -h1 - htdef
    obtain ⟨s', hs'⟩ := hfix' _ hs
    obtain ⟨t', ht'⟩ := hfix' _ ht
    refine ⟨(s' + t' * b) / 2, -t', ?_⟩
    have e1 : algebraMap F K ((s' + t' * b) / 2) =
        (algebraMap F K s' + algebraMap F K t' * algebraMap F K b) / 2 := by
      rw [map_div₀, map_add, map_mul, h2']
    rw [e1, map_neg, hs', ht', hb]
    apply mul_left_cancel₀ h2
    have e2 : (2 : K) * ((y + σ₀ y + t * -(x + σ₀ x)) / 2) = y + σ₀ y + t * -(x + σ₀ x) := by
      field_simp
    rw [mul_sub, e2]
    linear_combination (-1 : K) * htdef
  have hdisc : b ^ 2 - 4 * c ≠ 0 := by
    intro h
    apply hd
    have h' := congrArg (algebraMap F K) h
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat] at h'
    rw [hb, hc] at h'
    have h'' : (x - σ₀ x) ^ 2 = 0 := by linear_combination h'
    exact (pow_eq_zero_iff two_ne_zero).1 h''
  refine ⟨b, c, ?_, ⟨⟨x, hσσ, hfix, hωsq, hσω, hspan, h2, hdisc⟩⟩⟩
  intro s hs
  have hS : (algebraMap F K s - x) * (algebraMap F K s - σ₀ x) = 0 := by
    have h' := congrArg (algebraMap F K) hs
    simp only [map_add, map_mul, map_pow, map_zero] at h'
    rw [hb, hc] at h'
    linear_combination h'
  rcases mul_eq_zero.1 hS with h | h
  · have h1 : x = algebraMap F K s := (sub_eq_zero.1 h).symm
    apply hx
    rw [h1, hfix]
  · have h1 : σ₀ x = algebraMap F K s := (sub_eq_zero.1 h).symm
    apply hx
    have h3 := hσσ x
    rw [h1, hfix] at h3
    rw [h1]
    exact h3

end General

section Frobenius

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]

open CFSG.LieType.Chevalley

theorem frobFixed_le (e : ℕ) :
    frobeniusFixedField k p e ≤ frobeniusFixedField k p (e * 2) := by
  intro x hx
  rw [mem_frobeniusFixedField] at hx ⊢
  calc x ^ p ^ (e * 2) = x ^ (p ^ e * p ^ e) := by rw [mul_two, pow_add]
    _ = (x ^ p ^ e) ^ p ^ e := by rw [pow_mul]
    _ = x := by rw [hx, hx]

instance frobFixedAlgebra (e : ℕ) :
    Algebra ↥(frobeniusFixedField k p e) ↥(frobeniusFixedField k p (e * 2)) :=
  (Subfield.inclusion (frobFixed_le (k := k) (p := p) e)).toAlgebra

@[expose] noncomputable def frobHom (e : ℕ) :
    ↥(frobeniusFixedField k p (e * 2)) →+* ↥(frobeniusFixedField k p (e * 2)) :=
  ((iterateFrobenius k p e).comp (frobeniusFixedField k p (e * 2)).subtype).codRestrict _
    (fun x => by
      have hx := mem_frobeniusFixedField.1 x.2
      rw [RingHom.comp_apply, iterateFrobenius_def, mem_frobeniusFixedField]
      show ((x : k) ^ p ^ e) ^ p ^ (e * 2) = (x : k) ^ p ^ e
      have h1 : ((x : k) ^ p ^ e) ^ p ^ (e * 2) = ((x : k) ^ p ^ (e * 2)) ^ p ^ e := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (p ^ e) (p ^ (e * 2))]
      rw [h1, hx])

theorem coe_frobHom (e : ℕ) (x : ↥(frobeniusFixedField k p (e * 2))) :
    ((frobHom e x : ↥(frobeniusFixedField k p (e * 2))) : k) = (x : k) ^ p ^ e :=
  rfl

theorem frobHom_frobHom (e : ℕ) (x : ↥(frobeniusFixedField k p (e * 2))) :
    frobHom e (frobHom e x) = x := by
  refine Subtype.ext ?_
  have hx := mem_frobeniusFixedField.1 x.2
  rw [coe_frobHom, coe_frobHom, ← pow_mul, ← pow_add, ← mul_two, hx]

@[expose] noncomputable def frobInvol (e : ℕ) :
    ↥(frobeniusFixedField k p (e * 2)) ≃+* ↥(frobeniusFixedField k p (e * 2)) where
  toFun := frobHom e
  invFun := frobHom e
  left_inv := frobHom_frobHom e
  right_inv := frobHom_frobHom e
  map_mul' := map_mul (frobHom e)
  map_add' := map_add (frobHom e)

theorem exists_kleinData_frob {e : ℕ} (he : 0 < e) (hp2 : p ≠ 2) :
    ∃ b c : ↥(frobeniusFixedField k p e), (∀ s, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (KleinData ↥(frobeniusFixedField k p e) ↥(frobeniusFixedField k p (e * 2))
        (frobInvol e) b c) := by
  have hσσ : ∀ x, frobInvol (k := k) (p := p) e (frobInvol e x) = x := frobHom_frobHom e
  have hfix : ∀ r : ↥(frobeniusFixedField k p e),
      frobInvol e (algebraMap _ ↥(frobeniusFixedField k p (e * 2)) r) =
        algebraMap _ ↥(frobeniusFixedField k p (e * 2)) r := fun r => by
    refine Subtype.ext ?_
    show ((r : k) ^ p ^ e) = (r : k)
    exact mem_frobeniusFixedField.1 r.2
  have hfix' : ∀ y : ↥(frobeniusFixedField k p (e * 2)), frobInvol e y = y →
      ∃ r : ↥(frobeniusFixedField k p e),
        algebraMap _ ↥(frobeniusFixedField k p (e * 2)) r = y := fun y hy => by
    refine ⟨⟨(y : k), mem_frobeniusFixedField.2 ?_⟩, rfl⟩
    have := congrArg Subtype.val hy
    exact this
  have hne : ∃ y : ↥(frobeniusFixedField k p (e * 2)), frobInvol e y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hle : frobeniusFixedField k p (e * 2) ≤ frobeniusFixedField k p e := fun x hx =>
      mem_frobeniusFixedField.2 (congrArg Subtype.val (hcon ⟨x, hx⟩))
    haveI : Finite ↥(frobeniusFixedField k p e) :=
      Nat.finite_of_card_ne_zero (by rw [card_frobeniusFixedField he]; exact (pow_pos (Fact.out : p.Prime).pos e).ne')
    have hinj : Function.Injective (Subfield.inclusion hle) := (Subfield.inclusion hle).injective
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [card_frobeniusFixedField (by omega), card_frobeniusFixedField he] at h1
    have h2 : p ^ e < p ^ (e * 2) :=
      Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    omega
  have h2K : (2 : ↥(frobeniusFixedField k p (e * 2))) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by
      have := congrArg (frobeniusFixedField k p (e * 2)).subtype h
      rw [map_ofNat, map_zero] at this
      exact_mod_cast this
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).1 h'
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 hd
    exact hp2 this
  exact exists_kleinData_of_fixed (frobInvol e) hσσ hfix hfix' hne h2K

end Frobenius

end CompsPTwoDKlein

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
