module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.ExcFrames

variable {Ω : Type} [Field Ω] {q : ℕ} [NeZero q]

@[expose] def twE6Cast (v : Fin 6 → ZMod q) : Fin Tag.E6.rank → ZMod q :=
  fun i => v (Fin.cast (by rfl : Tag.E6.rank = 6) i)

theorem twE6Cast_add (v w : Fin 6 → ZMod q) :
    twE6Cast (q := q) (v + w) = twE6Cast v + twE6Cast w := rfl

theorem twE6Cast_zero : twE6Cast (q := q) (0 : Fin 6 → ZMod q) = 0 := by
  funext i
  simp [twE6Cast]

theorem twE6Cast_injective : Function.Injective (twE6Cast (q := q)) := by
  intro v w h
  funext i
  have hcast : Fin.cast (by rfl : Tag.E6.rank = 6)
      (Fin.cast (by rfl : 6 = Tag.E6.rank) i) = i := rfl
  simpa [twE6Cast, hcast] using congrFun h (Fin.cast (by rfl : 6 = Tag.E6.rank) i)

@[expose] def twE6QVec (ζ : Ωˣ) (hζ : ζ ^ q = 1) (v : Fin 6 → ZMod q) : ModGL Tag.E6 Ω :=
  rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ hζ (twE6Cast v))

private theorem zetaVec_zero_eq_one (ζ : Ωˣ) (hζ : ζ ^ q = 1) :
    zetaVec (τ := Tag.E6) ζ hζ (0 : Fin Tag.E6.rank → ZMod q) = 1 := by
  funext i
  rw [zetaVec_apply]
  simp

theorem twE6QVec_add (ζ : Ωˣ) (hζ : ζ ^ q = 1) (v w : Fin 6 → ZMod q) :
    twE6QVec ζ hζ (v + w) = twE6QVec ζ hζ v * twE6QVec ζ hζ w := by
  simp only [twE6QVec, twE6Cast_add, zetaVec_add, rootDiagUnit_mul]

theorem twE6QVec_zero (ζ : Ωˣ) (hζ : ζ ^ q = 1) :
    twE6QVec ζ hζ 0 = 1 := by
  rw [twE6QVec, twE6Cast_zero, zetaVec_zero_eq_one, rootDiagUnit_one]

@[expose] def twE6B0Mat : Matrix (Fin 4) (Fin 6) ℤ :=
  !![0, 2, 0, -1, 0, 0;
     -1, 0, 2, -1, 0, 0;
     0, -1, -1, 2, -1, 0;
     0, 0, 0, -2, 3, 0]

@[expose] def twE6B0Vec (j : Fin 4) : Fin 6 → ZMod q :=
  fun i => (twE6B0Mat j i : ZMod q)

theorem twE6B0Vec_last (j : Fin 4) : twE6B0Vec (q := q) j 5 = 0 := by
  fin_cases j <;> simp [twE6B0Vec, twE6B0Mat]

@[expose] def twE6B0Comb (c : Fin 4 → ZMod q) : Fin 6 → ZMod q :=
  ∑ j : Fin 4, c j • twE6B0Vec j

theorem twE6B0Comb_apply (c : Fin 4 → ZMod q) (i : Fin 6) :
    twE6B0Comb c i = ∑ j : Fin 4, c j * twE6B0Vec j i := by
  simp only [twE6B0Comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem twE6B0Comb_zero : twE6B0Comb (0 : Fin 4 → ZMod q) = 0 := by
  funext i
  simp [twE6B0Comb]

theorem twE6B0Comb_add (c d : Fin 4 → ZMod q) :
    twE6B0Comb (c + d) = twE6B0Comb c + twE6B0Comb d := by
  funext i
  simp only [twE6B0Comb_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem twE6B0Comb_neg (c : Fin 4 → ZMod q) : twE6B0Comb (-c) = -twE6B0Comb c := by
  funext i
  simp only [twE6B0Comb_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem twE6B0Comb_last (c : Fin 4 → ZMod q) : twE6B0Comb c 5 = 0 := by
  rw [twE6B0Comb_apply]
  simp [twE6B0Vec_last]

@[expose] def twE6BZeroHom (ζ : Ωˣ) (hζ : ζ ^ q = 1) :
    Multiplicative (Fin 4 → ZMod q) →* ModGL Tag.E6 Ω where
  toFun c := twE6QVec ζ hζ (twE6B0Comb (Multiplicative.toAdd c))
  map_one' := by
    have h1 : Multiplicative.toAdd (1 : Multiplicative (Fin 4 → ZMod q)) = 0 := rfl
    rw [h1, twE6B0Comb_zero, twE6QVec_zero]
  map_mul' c d := by
    have h1 : Multiplicative.toAdd (c * d) =
        Multiplicative.toAdd c + Multiplicative.toAdd d := rfl
    rw [h1, twE6B0Comb_add, twE6QVec_add]

@[expose] def twE6BZero (ζ : Ωˣ) (hζ : ζ ^ q = 1) : Subgroup (ModGL Tag.E6 Ω) :=
  (twE6BZeroHom ζ hζ).range

theorem twE6B0Comb_mem (ζ : Ωˣ) (hζ : ζ ^ q = 1) (c : Fin 4 → ZMod q) :
    twE6QVec ζ hζ (twE6B0Comb c) ∈ twE6BZero ζ hζ := by
  refine MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd c, ?_⟩
  have h1 : Multiplicative.toAdd (Multiplicative.ofAdd c) = c := rfl
  show twE6QVec ζ hζ (twE6B0Comb (Multiplicative.toAdd (Multiplicative.ofAdd c))) =
    twE6QVec ζ hζ (twE6B0Comb c)
  rw [h1]

private theorem twE6B0Comb_coord0 (c : Fin 4 → ZMod q) :
    (4 : ZMod q) * c 0 =
      -4 * twE6B0Comb c 0 + 2 * twE6B0Comb c 1 - 2 * twE6B0Comb c 2 := by
  simp [twE6B0Comb_apply, twE6B0Vec, twE6B0Mat, Fin.sum_univ_four]
  ring

private theorem twE6B0Comb_coord1 (c : Fin 4 → ZMod q) :
    (4 : ZMod q) * c 1 = -4 * twE6B0Comb c 0 := by
  simp [twE6B0Comb_apply, twE6B0Vec, twE6B0Mat, Fin.sum_univ_four]

private theorem twE6B0Comb_coord2 (c : Fin 4 → ZMod q) :
    (4 : ZMod q) * c 2 = -8 * twE6B0Comb c 0 - 4 * twE6B0Comb c 2 := by
  simp [twE6B0Comb_apply, twE6B0Vec, twE6B0Mat, Fin.sum_univ_four]
  ring

private theorem twE6B0Comb_coord3 (c : Fin 4 → ZMod q) :
    (4 : ZMod q) * c 3 = -4 * twE6B0Comb c 0 - twE6B0Comb c 1 -
      3 * twE6B0Comb c 2 - 2 * twE6B0Comb c 3 := by
  simp [twE6B0Comb_apply, twE6B0Vec, twE6B0Mat, Fin.sum_univ_four]
  ring

private theorem four_ne_zero_zmod (hq : q.Prime) (hq2 : q ≠ 2) : (4 : ZMod q) ≠ 0 := by
  intro h0
  have hdvd : q ∣ 4 := (ZMod.natCast_eq_zero_iff 4 q).1 h0
  have hdvd2 : q ∣ 2 := by
    have h2 : q ∣ 2 ^ 2 := by norm_num at hdvd ⊢; exact hdvd
    exact hq.dvd_of_dvd_pow h2
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hdvd2)

theorem twE6B0Comb_injective (hq : q.Prime) (hq2 : q ≠ 2)
    {c : Fin 4 → ZMod q} (h : twE6B0Comb c = 0) : c = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h4 : (4 : ZMod q) ≠ 0 := four_ne_zero_zmod hq hq2
  have h0 : twE6B0Comb c 0 = 0 := by rw [h]; rfl
  have h1 : twE6B0Comb c 1 = 0 := by rw [h]; rfl
  have h2 : twE6B0Comb c 2 = 0 := by rw [h]; rfl
  have h3 : twE6B0Comb c 3 = 0 := by rw [h]; rfl
  have e0 := twE6B0Comb_coord0 c
  have e1 := twE6B0Comb_coord1 c
  have e2 := twE6B0Comb_coord2 c
  have e3 := twE6B0Comb_coord3 c
  simp only [h0, h1, h2, h3, mul_zero, sub_self, add_zero, sub_zero] at e0 e1 e2 e3
  funext j
  fin_cases j
  · simpa using (mul_eq_zero.1 e0).resolve_left h4
  · simpa using (mul_eq_zero.1 e1).resolve_left h4
  · simpa using (mul_eq_zero.1 e2).resolve_left h4
  · simpa using (mul_eq_zero.1 e3).resolve_left h4

section Certs


theorem twE6QVec_injective (ζ : Ωˣ) (hζ : ζ ^ q = 1) (hζo : orderOf ζ = q) :
    Function.Injective (twE6QVec (Ω := Ω) (q := q) ζ hζ) := by
  intro v w h
  have h1 : zetaVec (τ := Tag.E6) ζ hζ (twE6Cast v) = zetaVec ζ hζ (twE6Cast w) :=
    rootDiagUnit_injective h
  exact twE6Cast_injective (zetaVec_injective hζo hζ h1)

theorem natCard_twE6BZero (hq : q.Prime) (hq2 : q ≠ 2) (ζ : Ωˣ) (hζ : ζ ^ q = 1)
    (hζo : orderOf ζ = q) :
    Nat.card ↥(twE6BZero ζ hζ) = q ^ 4 := by
  have hinj : Function.Injective (twE6BZeroHom ζ hζ) := by
    intro c d h
    have h1 : twE6QVec ζ hζ (twE6B0Comb (Multiplicative.toAdd c)) =
        twE6QVec ζ hζ (twE6B0Comb (Multiplicative.toAdd d)) := h
    have h2 : twE6B0Comb (Multiplicative.toAdd c) =
        twE6B0Comb (Multiplicative.toAdd d) :=
      twE6QVec_injective ζ hζ hζo h1
    have h3 : twE6B0Comb (Multiplicative.toAdd c - Multiplicative.toAdd d) = 0 := by
      rw [sub_eq_add_neg, twE6B0Comb_add, twE6B0Comb_neg, h2, add_neg_cancel]
    have h4 := twE6B0Comb_injective hq hq2 h3
    exact Multiplicative.toAdd.injective (sub_eq_zero.1 h4)
  rw [twE6BZero, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj,
    Subgroup.card_top]
  have hc : Nat.card (Multiplicative (Fin 4 → ZMod q)) = Nat.card (Fin 4 → ZMod q) :=
    (Nat.card_congr (Multiplicative.ofAdd (α := Fin 4 → ZMod q))).symm
  rw [hc, Nat.card_fun, Nat.card_fin]
  have hz : Nat.card (ZMod q) = q := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card q
  rw [hz]

end Certs

theorem isElemAbelian_twE6BZero (hq : q.Prime) (ζ : Ωˣ) (hζ : ζ ^ q = 1) :
    CFSG.Open.IsElemAbelian q (twE6BZero ζ hζ) := by
  change CFSG.Open.IsElemAbelian q (twE6BZeroHom ζ hζ).range
  refine ⟨⟨⟨fun p q => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := p
    obtain ⟨b, hb⟩ := q
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    apply Subtype.ext
    change a * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    exact congrArg (twE6BZeroHom ζ hζ) (mul_comm x y)
  · intro z hz
    obtain ⟨x, hx⟩ := hz
    have hxq : x ^ q = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      show q • x.toAdd i = 0
      rw [nsmul_eq_mul (α := ZMod q), ZMod.natCast_self, zero_mul]
    rw [← hx, ← map_pow, hxq, map_one]

end CFSG.LocalAnalysis.GLTheoremA.Y10F
