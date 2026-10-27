module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Words
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.ANineSylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv

theorem alternating_eq_of_perm {x y : alternatingGroup (Fin 9)}
    (h : (x : Perm (Fin 9)) = (y : Perm (Fin 9))) : x = y := Subtype.ext h

theorem aNineSylow_c3Relations :
    C3Relations aNineSylowGenA aNineSylowGenB aNineSylowGenC aNineSylowGenD aNineSylowGenE
      aNineSylowGenF where
  a_sq := alternating_eq_of_perm (by decide)
  b_sq := alternating_eq_of_perm (by decide)
  c_sq := alternating_eq_of_perm (by decide)
  d_sq := alternating_eq_of_perm (by decide)
  e_sq := alternating_eq_of_perm (by decide)
  f_sq := alternating_eq_of_perm (by decide)
  ab := alternating_eq_of_perm (by decide)
  ac := alternating_eq_of_perm (by decide)
  ad := alternating_eq_of_perm (by decide)
  bc := alternating_eq_of_perm (by decide)
  bd := alternating_eq_of_perm (by decide)
  cd := alternating_eq_of_perm (by decide)
  ef := alternating_eq_of_perm (by decide)
  ea := alternating_eq_of_perm (by decide)
  eb := alternating_eq_of_perm (by decide)
  ec := alternating_eq_of_perm (by decide)
  ed := alternating_eq_of_perm (by decide)
  fa := alternating_eq_of_perm (by decide)
  fb := alternating_eq_of_perm (by decide)
  fc := alternating_eq_of_perm (by decide)
  fd := alternating_eq_of_perm (by decide)

theorem c3Word_aNineSylowGen (v : Fin 64) :
    c3Word aNineSylowGenA aNineSylowGenB aNineSylowGenC aNineSylowGenD aNineSylowGenE
      aNineSylowGenF v = aNineSylowWord v := rfl

theorem aNineSylowWord_mul (v w : Fin 64) :
    aNineSylowWord v * aNineSylowWord w = aNineSylowWord (c3Mul v w) := by
  rw [← c3Word_aNineSylowGen, ← c3Word_aNineSylowGen, ← c3Word_aNineSylowGen]
  exact aNineSylow_c3Relations.c3Word_mul v w

theorem aNineSylowEquiv_zero : aNineSylowEquiv 0 = 1 := by
  apply Subtype.ext
  simp [aNineSylowWord]

variable {H : Type*} [Group H] {a b c d e f : H}

@[expose] noncomputable def c3Hom (h : C3Relations a b c d e f) : ANineSylow →* H where
  toFun x := c3Word a b c d e f (aNineSylowEquiv.symm x)
  map_one' := by
    rw [← aNineSylowEquiv_zero, Equiv.symm_apply_apply]
    simp [c3Word]
  map_mul' x y := by
    obtain ⟨v, rfl⟩ := aNineSylowEquiv.surjective x
    obtain ⟨w, rfl⟩ := aNineSylowEquiv.surjective y
    have hvw : aNineSylowEquiv v * aNineSylowEquiv w = aNineSylowEquiv (c3Mul v w) :=
      Subtype.ext (by simp [aNineSylowWord_mul])
    rw [hvw, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      h.c3Word_mul]

theorem c3Hom_apply (h : C3Relations a b c d e f) (v : Fin 64) :
    c3Hom h (aNineSylowEquiv v) = c3Word a b c d e f v := by
  simp [c3Hom]

theorem c3Hom_injective (h : C3Relations a b c d e f)
    (hker : ∀ v : Fin 64, c3Word a b c d e f v = 1 → v = 0) : Function.Injective (c3Hom h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨v, rfl⟩ := aNineSylowEquiv.surjective x
  rw [c3Hom_apply] at hx
  rw [hker v hx, aNineSylowEquiv_zero]

theorem c3Word_bijective_onto (h : C3Relations a b c d e f)
    (hker : ∀ v : Fin 64, c3Word a b c d e f v = 1 → v = 0) {S : Subgroup H}
    (hS : Nat.card S = 64) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (he : e ∈ S)
    (hf : f ∈ S) :
    Function.Injective (c3Word a b c d e f) ∧ (∀ v, c3Word a b c d e f v ∈ S) ∧
      ∀ s ∈ S, ∃ v, c3Word a b c d e f v = s := by
  have hmem : ∀ v, c3Word a b c d e f v ∈ S := fun v => by
    simp only [c3Word]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.pow_mem ha _)
      (S.pow_mem hb _)) (S.pow_mem hc _)) (S.pow_mem hd _)) (S.pow_mem he _)) (S.pow_mem hf _)
  have hinj : Function.Injective (c3Word a b c d e f) := fun v w hvw => by
    have := c3Hom_injective h hker (a₁ := aNineSylowEquiv v) (a₂ := aNineSylowEquiv w)
      (by rw [c3Hom_apply, c3Hom_apply, hvw])
    exact aNineSylowEquiv.injective this
  have hrange : (c3Hom h).range = S := by
    have hle : (c3Hom h).range ≤ S := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨v, rfl⟩ := aNineSylowEquiv.surjective x
      rw [c3Hom_apply]
      exact hmem v
    have : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hS, ← Nat.card_congr (MonoidHom.ofInjective (c3Hom_injective h hker)).toEquiv,
      card_aNineSylow]
  refine ⟨hinj, hmem, fun s hs => ?_⟩
  rw [← hrange] at hs
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨v, rfl⟩ := aNineSylowEquiv.surjective x
  exact ⟨v, (c3Hom_apply h v).symm⟩

theorem c3Relations_of {W : Subgroup H} (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hW2 : ∀ x ∈ W, x * x = 1) (ha : a ∈ W) (hb : b ∈ W) (hfW : ∀ w ∈ W, f * w * f⁻¹ ∈ W)
    (he2 : e * e = 1) (hf2 : f * f = 1) (hef : e * f = f * e) (hea : e * a * e⁻¹ = a)
    (heb : e * b * e⁻¹ = a * b) : C3Relations a b (f * a * f⁻¹) (f * b * f⁻¹) e f := by
  have hfe : f⁻¹ * e⁻¹ = e⁻¹ * f⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hef]
  have hconj : ∀ g : H, e * (f * g * f⁻¹) * e⁻¹ = f * (e * g * e⁻¹) * f⁻¹ := fun g => by
    calc e * (f * g * f⁻¹) * e⁻¹ = (e * f) * g * (f⁻¹ * e⁻¹) := by group
      _ = (f * e) * g * (e⁻¹ * f⁻¹) := by rw [hef, hfe]
      _ = f * (e * g * e⁻¹) * f⁻¹ := by group
  have hff : ∀ g : H, f * (f * g * f⁻¹) * f⁻¹ = g := fun g => by
    calc f * (f * g * f⁻¹) * f⁻¹ = (f * f) * g * (f * f)⁻¹ := by group
      _ = g := by rw [hf2]; group
  have hsqc : ∀ g ∈ W, f * g * f⁻¹ * (f * g * f⁻¹) = 1 := fun g hg => by
    rw [show f * g * f⁻¹ * (f * g * f⁻¹) = f * (g * g) * f⁻¹ by group, hW2 g hg]
    group
  exact
    { a_sq := hW2 a ha
      b_sq := hW2 b hb
      c_sq := hsqc a ha
      d_sq := hsqc b hb
      e_sq := he2
      f_sq := hf2
      ab := hW a ha b hb
      ac := hW a ha _ (hfW a ha)
      ad := hW a ha _ (hfW b hb)
      bc := hW b hb _ (hfW a ha)
      bd := hW b hb _ (hfW b hb)
      cd := hW _ (hfW a ha) _ (hfW b hb)
      ef := hef
      ea := hea
      eb := heb
      ec := by rw [hconj, hea]
      ed := by rw [hconj, heb]; group
      fa := rfl
      fb := rfl
      fc := hff a
      fd := hff b }

theorem c3Word_eq_one {W T₀ P Q : Subgroup H} (hWT : W ≤ T₀) (hPW : P ≤ W) (hQW : Q ≤ W)
    (hPQ : ∀ g ∈ P, g ∈ Q → g = 1) (ha : a ∈ P) (hb : b ∈ P) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab1 : a * b ≠ 1) (hfP : ∀ p ∈ P, f * p * f⁻¹ ∈ Q) (heT : e ∈ T₀) (heW : e ∉ W)
    (hfT : f ∉ T₀) (v : Fin 64) (hv : c3Word a b (f * a * f⁻¹) (f * b * f⁻¹) e f v = 1) :
    v = 0 := by
  have hbit : ∀ n : ℕ, n % 2 = 0 ∨ n % 2 = 1 := fun n => Nat.mod_two_eq_zero_or_one n
  have hconj1 : ∀ g : H, f * g * f⁻¹ = 1 → g = 1 := fun g hg => by
    rw [show g = f⁻¹ * (f * g * f⁻¹) * f by group, hg]
    group
  have hpair : ∀ {x y : H} (i j : ℕ), x ≠ 1 → y ≠ 1 → x * y ≠ 1 → (i % 2 = 0 ∨ i % 2 = 1) →
      (j % 2 = 0 ∨ j % 2 = 1) → x ^ (i % 2) * y ^ (j % 2) = 1 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro x y i j hx hy hxy hi hj h'
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj] at h' ⊢ <;>
      simp only [pow_zero, pow_one, one_mul, mul_one] at h'
    · exact ⟨rfl, rfl⟩
    · exact absurd h' hy
    · exact absurd h' hx
    · exact absurd h' hxy
  simp only [c3Word] at hv
  set i := v.val / 32 % 2
  set j := v.val / 16 % 2
  set k := v.val / 8 % 2
  set l := v.val / 4 % 2
  set m := v.val / 2 % 2
  set n := v.val % 2
  have hwP : a ^ i * b ^ j ∈ P := P.mul_mem (P.pow_mem ha _) (P.pow_mem hb _)
  have hwQ : (f * a * f⁻¹) ^ k * (f * b * f⁻¹) ^ l ∈ Q :=
    Q.mul_mem (Q.pow_mem (hfP a ha) _) (Q.pow_mem (hfP b hb) _)
  have hw : a ^ i * b ^ j * (f * a * f⁻¹) ^ k * (f * b * f⁻¹) ^ l ∈ W := by
    rw [mul_assoc (a ^ i * b ^ j)]
    exact W.mul_mem (hPW hwP) (hQW hwQ)
  have hn : n = 0 := by
    rcases hbit v.val with h0 | h0
    · exact h0
    · exfalso
      apply hfT
      have hfn : f = (a ^ i * b ^ j * (f * a * f⁻¹) ^ k * (f * b * f⁻¹) ^ l * e ^ m)⁻¹ := by
        refine eq_inv_of_mul_eq_one_right ?_
        rw [← hv]
        change _ = _ * f ^ (v.val % 2)
        rw [h0, pow_one]
      rw [hfn]
      exact T₀.inv_mem (T₀.mul_mem (hWT hw) (T₀.pow_mem heT _))
  rw [hn, pow_zero, mul_one] at hv
  have hm : m = 0 := by
    rcases hbit (v.val / 2) with h0 | h0
    · exact h0
    · exfalso
      apply heW
      have hem : e = (a ^ i * b ^ j * (f * a * f⁻¹) ^ k * (f * b * f⁻¹) ^ l)⁻¹ := by
        refine eq_inv_of_mul_eq_one_right ?_
        rw [← hv]
        change _ = _ * e ^ (v.val / 2 % 2)
        rw [h0, pow_one]
      rw [hem]
      exact W.inv_mem hw
  rw [hm, pow_zero, mul_one] at hv
  have hPpart : a ^ i * b ^ j = 1 := by
    have hinv : a ^ i * b ^ j = ((f * a * f⁻¹) ^ k * (f * b * f⁻¹) ^ l)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact hv
    exact hPQ _ hwP (hinv ▸ Q.inv_mem hwQ)
  have hQpart : (f * a * f⁻¹) ^ k * (f * b * f⁻¹) ^ l = 1 := by
    rw [mul_assoc, hPpart, one_mul] at hv
    exact hv
  obtain ⟨hi, hj⟩ := hpair (v.val / 32) (v.val / 16) ha1 hb1 hab1 (hbit _) (hbit _) hPpart
  obtain ⟨hk, hl⟩ := hpair (v.val / 8) (v.val / 4) (fun h' => ha1 (hconj1 a h'))
    (fun h' => hb1 (hconj1 b h'))
    (fun h' => hab1 (hconj1 (a * b) (by rw [← h']; group))) (hbit _) (hbit _) hQpart
  apply Fin.ext
  have hv64 := v.isLt
  simp only [Fin.val_zero]
  omega

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
