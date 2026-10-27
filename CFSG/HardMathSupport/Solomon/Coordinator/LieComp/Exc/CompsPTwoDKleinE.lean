module

public import CFSG.RankThree.PartOne.CTP.SU4EvenData
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDKlein

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.RankThree.PartOne.CTP.SU4Even

namespace CompsPTwoDKleinE

section General

variable {F K : Type} [Field F] [Field K] [Algebra F K] (σ₀ : K ≃+* K)

@[expose] def kleinDataEven_of_norm_trace (hσσ : ∀ x, σ₀ (σ₀ x) = x)
    (hfix : ∀ r : F, σ₀ (algebraMap F K r) = algebraMap F K r)
    (hfix' : ∀ y : K, σ₀ y = y → ∃ r : F, algebraMap F K r = y)
    (x : K) (hx : σ₀ x ≠ x) {b c : F}
    (hb : algebraMap F K b = -(x + σ₀ x))
    (hc : algebraMap F K c = x * σ₀ x) : KleinDataEven F K σ₀ b c := by
  have hd : x - σ₀ x ≠ 0 := sub_ne_zero.2 (fun h => hx h.symm)
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
    have ht : σ₀ t = t := by
      have h1 := congrArg σ₀ htdef
      rw [map_mul, map_sub, map_sub, hσσ, hσσ] at h1
      apply mul_right_cancel₀ hd
      linear_combination -h1 - htdef
    have hu : σ₀ (y - t * x) = y - t * x := by
      rw [map_sub, map_mul, ht]
      linear_combination htdef
    obtain ⟨u, hu'⟩ := hfix' _ hu
    obtain ⟨v', hv'⟩ := hfix' _ ht
    refine ⟨u, -v', ?_⟩
    rw [map_neg, hu', hv']
    ring
  have hdisc : b ^ 2 - 4 * c ≠ 0 := by
    intro h
    apply hd
    have h' := congrArg (algebraMap F K) h
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat] at h'
    rw [hb, hc] at h'
    have h'' : (x - σ₀ x) ^ 2 = 0 := by linear_combination h'
    exact (pow_eq_zero_iff two_ne_zero).1 h''
  exact ⟨x, hσσ, hfix, hωsq, hσω, hspan, hdisc⟩

theorem kleinDataEven_of_root (hσσ : ∀ x, σ₀ (σ₀ x) = x)
    (hfix : ∀ r : F, σ₀ (algebraMap F K r) = algebraMap F K r)
    (hfix' : ∀ y : K, σ₀ y = y → ∃ r : F, algebraMap F K r = y)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {x : K} (hroot : x ^ 2 + algebraMap F K b * x + algebraMap F K c = 0) :
    Nonempty (KleinDataEven F K σ₀ b c) := by
  have hx : σ₀ x ≠ x := by
    intro h
    obtain ⟨s, hs⟩ := hfix' x h
    apply hirr s
    apply (algebraMap F K).injective
    simpa only [map_add, map_pow, map_mul, map_zero, hs] using hroot
  have hroot' : (σ₀ x) ^ 2 + algebraMap F K b * σ₀ x + algebraMap F K c = 0 := by
    simpa only [map_add, map_pow, map_mul, map_zero, hfix] using congrArg σ₀ hroot
  have hmul : (σ₀ x - x) * (σ₀ x + x + algebraMap F K b) = 0 := by
    linear_combination hroot' - hroot
  have hsum : σ₀ x + x + algebraMap F K b = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hx)
  have hb : algebraMap F K b = -(x + σ₀ x) := by linear_combination hsum
  have hc : algebraMap F K c = x * σ₀ x := by linear_combination hroot - x * hsum
  exact ⟨kleinDataEven_of_norm_trace σ₀ hσσ hfix hfix' x hx hb hc⟩

theorem exists_kleinDataEven_of_fixed (hσσ : ∀ x, σ₀ (σ₀ x) = x)
    (hfix : ∀ r : F, σ₀ (algebraMap F K r) = algebraMap F K r)
    (hfix' : ∀ y : K, σ₀ y = y → ∃ r : F, algebraMap F K r = y) (hne : ∃ y : K, σ₀ y ≠ y) :
    ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧ Nonempty (KleinDataEven F K σ₀ b c) := by
  obtain ⟨x, hx⟩ := hne
  have hsum : σ₀ (-(x + σ₀ x)) = -(x + σ₀ x) := by rw [map_neg, map_add, hσσ]; ring
  have hprod : σ₀ (x * σ₀ x) = x * σ₀ x := by rw [map_mul, hσσ]; ring
  obtain ⟨b, hb⟩ := hfix' _ hsum
  obtain ⟨c, hc⟩ := hfix' _ hprod
  refine ⟨b, c, ?_, ⟨kleinDataEven_of_norm_trace σ₀ hσσ hfix hfix' x hx hb hc⟩⟩
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

open CFSG.LieType.Chevalley CompsPTwoDKlein

theorem exists_kleinDataEven_frob {e : ℕ} (he : 0 < e) :
    ∃ b c : ↥(frobeniusFixedField k p e), (∀ s, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (KleinDataEven ↥(frobeniusFixedField k p e) ↥(frobeniusFixedField k p (e * 2))
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
      Nat.finite_of_card_ne_zero (by
        rw [card_frobeniusFixedField he]
        exact (pow_pos (Fact.out : p.Prime).pos e).ne')
    have hinj : Function.Injective (Subfield.inclusion hle) := (Subfield.inclusion hle).injective
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [card_frobeniusFixedField (by omega), card_frobeniusFixedField he] at h1
    have h2 : p ^ e < p ^ (e * 2) :=
      Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    omega
  exact exists_kleinDataEven_of_fixed (frobInvol e) hσσ hfix hfix' hne

end Frobenius

end CompsPTwoDKleinE

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
