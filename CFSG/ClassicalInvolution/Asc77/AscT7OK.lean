module

public import CFSG.ClassicalInvolution.Asc77.AscT7OJ
public import CFSG.ClassicalInvolution.Asc77.AscT7OD
public import CFSG.ClassicalInvolution.Asc77.AscT7OI

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.Dichotomy QuadraticMap
open scoped MatrixGroups

section Twist

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Finite F] [FiniteDimensional F V] {X : Type} [Group X] [Finite X]

theorem alphaOf_klein_of_twist (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (fr : Frame Q) (hV : 7 ≤ Module.finrank F V)
    (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e) [e.range.Normal]
    {w : V ≃ₗ[F] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hwspan : ∀ x ∈ fr.span, w x = x) (hww : ∀ u, w (w u) = -(fr.La (-1) u)) {v : X}
    (hconj : ∀ g h : ↥(elementaryGroup Q), (h : V ≃ₗ[F] V) = w * g * w⁻¹ →
      v * e g * v⁻¹ = e h)
    (hvv : v * v = e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩) {a : SL(2, F)}
    (haa : a * a = -1)
    (hz : ∀ n ∈ involutionOddCore (e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩), n = 1) :
    alphaOf (Subgroup.closure ({e ⟨fr.La a, fr.La_mem_elementaryGroup a⟩ * v,
      e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩} : Set X)) = ⊥ := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set zE : ↥(elementaryGroup Q) := ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ with hzE
  have hLaE : ∀ b : SL(2, F), fr.La b ∈ elementaryGroup Q := fun b => fr.La_mem_elementaryGroup b
  have hLinv : (fr.La (-1))⁻¹ = fr.La (-1) := inv_eq_of_mul_eq_one_right fr.La_neg_one_mul_self
  have hLL : ∀ u, fr.La (-1) (fr.La (-1) u) = u := fun u =>
    congrArg (fun m : V ≃ₗ[F] V => m u) fr.La_neg_one_mul_self
  have hz2 : zE * zE = 1 := Subtype.ext fr.La_neg_one_mul_self
  have hperp : fr.perp ≠ ⊥ := perp_ne_bot fr (by omega)
  set κ : X := e ⟨fr.La a, hLaE a⟩ with hκdef
  have haa' : (a : Matrix (Fin 2) (Fin 2) F) * a = -1 := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) haa
    simpa using this
  have hκκ : κ * κ = e zE := by
    rw [hκdef, ← map_mul]
    congr 1
    apply Subtype.ext
    change fr.La a * fr.La a = fr.La (-1)
    rw [← map_mul, haa]
  set A : V ≃ₗ[F] V := fr.La a * w with hAdef
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (Frame.La_mem_orthogonalGroup fr a) hwO
  have hwLa := w_comm_La fr hwO hwspan
  have hwSw := w_comm_swap_La fr hwO hwspan
  have hA2 : ∀ u, A (A u) = -u := by
    intro u
    have h1 : ∀ t, w (fr.La a t) = fr.La a (w t) := fun t =>
      (congrArg (fun m : V ≃ₗ[F] V => m t) (hwLa a)).symm
    have hLaa : ∀ t, fr.La a (fr.La a t) = fr.La (-1) t := fun t => by
      rw [← LinearEquiv.mul_apply, ← map_mul, haa]
    simp only [hAdef, LinearEquiv.mul_apply]
    rw [h1, hLaa, hww, map_neg, hLL]
  have hAz : A * fr.La (-1) = fr.La (-1) * A := by
    calc A * fr.La (-1) = fr.La a * (w * fr.La (-1)) := by rw [hAdef, mul_assoc]
      _ = fr.La a * (fr.La (-1) * w) := by rw [← hwLa (-1)]
      _ = (fr.La a * fr.La (-1)) * w := by rw [mul_assoc]
      _ = (fr.La (-1) * fr.La a) * w := by rw [fr.La_neg_one_comm a]
      _ = fr.La (-1) * A := by rw [hAdef, mul_assoc]
  have hAK : ∀ B : SL(2, F), A * fr.swap.La B = fr.swap.La B * A := by
    intro B
    calc A * fr.swap.La B = fr.La a * (w * fr.swap.La B) := by rw [hAdef, mul_assoc]
      _ = fr.La a * (fr.swap.La B * w) := by rw [← hwSw B]
      _ = (fr.La a * fr.swap.La B) * w := by rw [mul_assoc]
      _ = (fr.swap.La B * fr.La a) * w := by rw [Frame.La_comm_La_swap fr a B]
      _ = fr.swap.La B * A := by rw [hAdef, mul_assoc]
  set y : X := κ * v with hydef
  have hy : ActsAs e y A := by
    intro g h hgh
    have hmem : w * (g : V ≃ₗ[F] V) * w⁻¹ ∈ elementaryGroup Q :=
      conj_mem_elementaryGroup hwO g.2
    have h1 := hconj g ⟨w * g * w⁻¹, hmem⟩ rfl
    have hh : (h : V ≃ₗ[F] V) = fr.La a * (w * g * w⁻¹) * (fr.La a)⁻¹ := by
      rw [hgh, hAdef, mul_inv_rev]; group
    calc y * e g * y⁻¹ = κ * (v * e g * v⁻¹) * κ⁻¹ := by rw [hydef]; group
      _ = κ * e ⟨w * g * w⁻¹, hmem⟩ * κ⁻¹ := by rw [h1]
      _ = e h := by
          rw [hκdef, e_conj]
          congr 1
          exact Subtype.ext hh.symm
  have hvκ : v * κ = κ * v := by
    have h1 := hconj ⟨fr.La a, hLaE a⟩ ⟨fr.La a, hLaE a⟩ (by
      change fr.La a = w * fr.La a * w⁻¹
      rw [eq_comm, mul_inv_eq_iff_eq_mul]
      exact (hwLa a).symm)
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  have hy2 : y * y = 1 := by
    have h2' : e zE * e zE = 1 := by rw [← map_mul, hz2, map_one]
    calc y * y = κ * (v * κ) * v := by rw [hydef]; group
      _ = κ * (κ * v) * v := by rw [hvκ]
      _ = (κ * κ) * (v * v) := by group
      _ = 1 := by rw [hκκ, hvv, h2']
  obtain ⟨b, hb⟩ := not_central_of_sq_neg_one h2 haa'
  have hAb : A * fr.La b * A⁻¹ = fr.La (a * b * a⁻¹) := by
    have h1 : w * fr.La b = fr.La b * w := (hwLa b).symm
    rw [hAdef, mul_inv_rev, map_mul, map_mul, map_inv]
    calc fr.La a * w * fr.La b * (w⁻¹ * (fr.La a)⁻¹)
        = fr.La a * (w * fr.La b * w⁻¹) * (fr.La a)⁻¹ := by group
      _ = fr.La a * fr.La b * (fr.La a)⁻¹ := by
          rw [h1, mul_assoc (fr.La b) w w⁻¹, mul_inv_cancel, mul_one]
  have hcontra : (∀ g : ↥(elementaryGroup Q), (g : V ≃ₗ[F] V) = fr.La b →
      y * e g * y⁻¹ = e g) → False := by
    intro hall
    have hgm : (A * fr.La b * A⁻¹) ∈ elementaryGroup Q := by
      rw [hAb]; exact hLaE _
    have h1 := hall ⟨fr.La b, hLaE b⟩ rfl
    have h2' := hy ⟨fr.La b, hLaE b⟩ ⟨A * fr.La b * A⁻¹, hgm⟩ rfl
    have h3 := eq_of_e_eq_of_fix_perp hker hperp (g := ⟨A * fr.La b * A⁻¹, hgm⟩)
      (h := ⟨fr.La b, hLaE b⟩) (by rw [← h2', h1])
      (fun u hu => by
        change (A * fr.La b * A⁻¹) u = u
        rw [hAb]; exact La_fix_perp fr _ hu)
      (fun u hu => La_fix_perp fr b hu)
    have h4 : fr.La (a * b * a⁻¹) = fr.La b := by
      have h4' : A * fr.La b * A⁻¹ = fr.La b := congrArg Subtype.val h3
      rwa [hAb] at h4'
    have h5 := fr.La_injective h4
    apply hb
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5
  have hy1 : y ≠ 1 := fun h1 => hcontra fun g _ => by rw [h1]; group
  have hzy1 : e zE * y ≠ 1 := by
    intro h1
    have hyz : y = e zE := by
      have h2' : y = (e zE)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2']
      exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, hz2, map_one])
    refine hcontra fun g hg => ?_
    rw [hyz, e_conj]
    congr 1
    apply Subtype.ext
    change fr.La (-1) * (g : V ≃ₗ[F] V) * (fr.La (-1))⁻¹ = g
    rw [hg, hLinv, fr.La_neg_one_comm b, mul_assoc, fr.La_neg_one_mul_self, mul_one]
  have hz1 : e zE ≠ 1 := by
    have D : LocalData e zE fr.span fr.perp :=
      ⟨splitInv_frame fr hQ, hker, span_ne_bot fr, hperp⟩
    exact D.ne_one h2
  have key := alphaOf_klein_of_complex hodd h5 hQ fr hV e hker hAO hA2 hAz hAK hy hy2 hy1 hzy1
    hz1 hz
  rw [Set.pair_comm] at key
  exact key

end Twist

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
