module

public import CFSG.GroupTheory.KleinFourAutomorphism
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

namespace ReciprocalFusion

theorem card_sup_eq_mul_of_disjoint (A B : Subgroup X) (hnormal : B ≤ normalizer (A : Set X))
    (hdisjoint : Disjoint A B) : Nat.card (A ⊔ B : Subgroup X) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↑(A ⊔ B) := fun z =>
    ⟨(z.1 : X) * (z.2 : X), mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    exact mul_injective_of_disjoint hdisjoint (congrArg Subtype.val hxy)
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : X) ∈ (A : Set X) * (B : Set X) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    obtain ⟨a, ha, b, hb, hab⟩ := hz
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc Nat.card (A ⊔ B : Subgroup X) = Nat.card (A × B) :=
        Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

theorem eq_one_or_eq_of_mem_zpowers [Finite X] {a x : X} (ha : orderOf a = 2)
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  interval_cases k <;> simp

theorem isKleinFour_closure_pair [Finite X] {a t : X} (ha : orderOf a = 2) (ht : orderOf t = 2)
    (hcomm : a * t = t * a) (hne : a ≠ t) : IsKleinFour (closure {a, t}) := by
  have hcl : closure {a, t} = zpowers a ⊔ zpowers t := by
    rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hnorm : zpowers t ≤ normalizer (zpowers a : Set X) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left hcomm k)).eq
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact absurd ha (by decide)
  have hdisj : Disjoint (zpowers a) (zpowers t) := by
    rw [disjoint_def]
    intro x hxa hxt
    rcases eq_one_or_eq_of_mem_zpowers ha hxa with h | rfl
    · exact h
    · rcases eq_one_or_eq_of_mem_zpowers ht hxt with h | h
      · exact h
      · exact absurd h hne
  have hcard : Nat.card (closure {a, t}) = 4 := by
    rw [hcl, card_sup_eq_mul_of_disjoint _ _ hnorm hdisj, Nat.card_zpowers, Nat.card_zpowers,
      ha, ht]
  have hsq : ∀ v : closure {a, t}, v ^ 2 = 1 := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    have hv' : v ∈ ((zpowers a ⊔ zpowers t : Subgroup X) : Set X) := by
      rw [← hcl]
      exact hv
    rw [coe_mul_of_right_le_normalizer_left _ _ hnorm] at hv'
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hv'
    have hxy : Commute x y := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left hcomm i).zpow_right j
    have hx2 : x ^ 2 = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers ha hx with rfl | rfl
      · exact one_pow 2
      · rw [← ha]; exact pow_orderOf_eq_one _
    have hy2 : y ^ 2 = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers ht hy with rfl | rfl
      · exact one_pow 2
      · rw [← ht]; exact pow_orderOf_eq_one _
    change (x * y) ^ 2 = 1
    rw [hxy.mul_pow, hx2, hy2, one_mul]
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent (closure {a, t}) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have hsub := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : closure {a, t})
    omega
  · exact h

theorem mem_normalizer_closure_pair [Finite X] {a t g : X} (ha : g * a * g⁻¹ ∈ closure {a, t})
    (ht : g * t * g⁻¹ ∈ closure {a, t}) : g ∈ normalizer (closure {a, t} : Set X) := by
  apply mem_normalizer_fintype
  intro n hn
  have hle : closure {a, t} ≤ (closure {a, t}).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · simpa [MulAut.conj_apply] using ha
    · simpa [MulAut.conj_apply] using ht
  simpa [MulAut.conj_apply] using hle hn

theorem normalizerMonoidHom_eq_one_of_commute {a t : X}
    (n : normalizer (closure {a, t} : Set X)) (ha : (n : X) * a = a * n)
    (ht : (n : X) * t = t * n) : (closure {a, t}).normalizerMonoidHom n = 1 := by
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf, centralizer_closure,
    mem_centralizer_iff]
  rintro x (rfl | rfl)
  · exact ha.symm
  · exact ht.symm

theorem odd_card_of_isPerfect {a t : X} (U : Subgroup (centralizer ({a} : Set X))) [U.Normal]
    (hU : Odd (Nat.card U)) (htH : t ∈ centralizer ({a} : Set X))
    (hsolv : Group.IsSolvable (centralizer ({(⟨t, htH⟩ : centralizer ({a} : Set X))} :
      Set (centralizer ({a} : Set X))) ⧸ U.subgroupOf (centralizer {⟨t, htH⟩})))
    (P : Subgroup X) (hP : P ≤ centralizer ({a} : Set X) ⊓ centralizer {t})
    [Group.IsPerfect P] : Odd (Nat.card P) := by
  set t' : centralizer ({a} : Set X) := ⟨t, htH⟩
  set C := centralizer ({t'} : Set (centralizer ({a} : Set X)))
  have hPa : ∀ p : P, (p : X) ∈ centralizer ({a} : Set X) := fun p => (hP p.2).1
  have hPt : ∀ p : P, (⟨p, hPa p⟩ : centralizer ({a} : Set X)) ∈ C := by
    intro p
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hP p.2).2
  let f : P →* C :=
    { toFun := fun p => ⟨⟨p, hPa p⟩, hPt p⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g : P →* C ⧸ U.subgroupOf C := (QuotientGroup.mk' _).comp f
  have hrange : Subsingleton g.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    have : Group.IsPerfect g.range := Group.IsPerfect.range g
    exact Group.IsPerfect.not_isSolvable g.range inferInstance
  have hU' : ∀ p : P, (⟨p, hPa p⟩ : centralizer ({a} : Set X)) ∈ U := by
    intro p
    have h1 : g p = 1 := by
      have := Subsingleton.elim (⟨g p, ⟨p, rfl⟩⟩ : g.range) 1
      exact congrArg Subtype.val this
    have h2 : f p ∈ U.subgroupOf C := by
      rw [← QuotientGroup.ker_mk' (U.subgroupOf C), MonoidHom.mem_ker]
      exact h1
    exact mem_subgroupOf.mp h2
  let k : P →* U :=
    { toFun := fun p => ⟨⟨p, hPa p⟩, hU' p⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro p q hpq
    apply Subtype.ext
    have := congrArg (fun u : U => ((u : centralizer ({a} : Set X)) : X)) hpq
    exact this
  exact Odd.of_dvd_nat hU (card_dvd_of_injective k hk)

end ReciprocalFusion

open ReciprocalFusion

theorem reciprocal_involution_fusion_four_normalizer [Finite X] {a : X} (ha : orderOf a = 2)
    (U : Subgroup (centralizer ({a} : Set X))) [U.Normal] (hU : Odd (Nat.card U))
    {t : X} (htH : t ∈ centralizer ({a} : Set X)) (ht : orderOf t = 2) (hta : t ≠ a)
    (hconj : IsConj a t) (hat : ∃ h ∈ centralizer ({a} : Set X), h * t * h⁻¹ = a * t)
    (hsolv : Group.IsSolvable (centralizer ({(⟨t, htH⟩ : centralizer ({a} : Set X))} :
      Set (centralizer ({a} : Set X))) ⧸ U.subgroupOf (centralizer {⟨t, htH⟩})))
    (hobs : ∀ r : X, r ∈ centralizer ({a} : Set X) → IsConj a r → r ≠ a →
      (¬ ∃ h ∈ centralizer ({a} : Set X), h * r * h⁻¹ = t) →
      2 ^ (Nat.card (centralizer ({a} : Set X) ⊓ centralizer {r} : Subgroup X)).factorization 2 ≠
          2 ^ (Nat.card (centralizer ({a} : Set X) ⊓ centralizer {t} :
            Subgroup X)).factorization 2 ∨
        ∃ P : Subgroup X, P ≤ centralizer ({a} : Set X) ⊓ centralizer {r} ∧
          Group.IsPerfect P ∧ Even (Nat.card P)) :
    (∀ g : X, g⁻¹ * a * g = t →
      ∃ h ∈ centralizer ({a} : Set X), h * (g * a * g⁻¹) * h⁻¹ = t) ∧
    IsKleinFour (closure {a, t}) ∧
    (∃ b ∈ normalizer (closure {a, t} : Set X),
      b * a * b⁻¹ = t ∧ b * t * b⁻¹ = a ∧ b * (a * t) * b⁻¹ = a * t) ∧
    (∃ c ∈ normalizer (closure {a, t} : Set X),
      c * a * c⁻¹ = a ∧ c * t * c⁻¹ = a * t ∧ c * (a * t) * c⁻¹ = t) ∧
    Function.Surjective (closure {a, t}).normalizerMonoidHom ∧
    Nonempty (normalizer (closure {a, t} : Set X) ⧸
      (centralizer (closure {a, t} : Set X)).subgroupOf (normalizer (closure {a, t} : Set X)) ≃*
        Equiv.Perm (Fin 3)) := by
  have hcomm : a * t = t * a := (mem_centralizer_singleton_iff.mp htH).symm
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hnoPerfect : ∀ P : Subgroup X, P ≤ centralizer ({a} : Set X) ⊓ centralizer {t} →
      Group.IsPerfect P → ¬ Even (Nat.card P) := by
    intro P hP hperf heven
    have hodd := odd_card_of_isPerfect U hU htH hsolv P hP
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hrecip : ∀ g : X, g⁻¹ * a * g = t →
      ∃ h ∈ centralizer ({a} : Set X), h * (g * a * g⁻¹) * h⁻¹ = t := by
    intro g hg
    set r := g * a * g⁻¹ with hr
    have hgt : g * t * g⁻¹ = a := by rw [← hg]; group
    have hrH : r ∈ centralizer ({a} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc r * a = g * (a * t) * g⁻¹ := by rw [hr, ← hgt]; group
        _ = g * (t * a) * g⁻¹ := by rw [hcomm]
        _ = a * r := by rw [hr, ← hgt]; group
    have hrconj : IsConj a r := isConj_iff.mpr ⟨g, rfl⟩
    have hra : r ≠ a := by
      intro h
      apply hta
      rw [← hg]
      calc g⁻¹ * a * g = g⁻¹ * r * g := by rw [h]
        _ = a := by rw [hr]; group
    let φ : X ≃* X := MulAut.conj g⁻¹
    have hmap : (centralizer ({a} : Set X) ⊓ centralizer {r}).map φ.toMonoidHom =
        centralizer ({a} : Set X) ⊓ centralizer {t} := by
      ext y
      rw [mem_map_equiv, mem_inf, mem_inf, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff]
      have hsymm : φ.symm y = g * y * g⁻¹ := by
        simp [φ]
      rw [hsymm]
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · calc y * a = g⁻¹ * (g * y * g⁻¹ * r) * g := by rw [hr]; group
            _ = g⁻¹ * (r * (g * y * g⁻¹)) * g := by rw [h2]
            _ = a * y := by rw [hr]; group
        · calc y * t = g⁻¹ * (g * y * g⁻¹ * a) * g := by rw [← hg]; group
            _ = g⁻¹ * (a * (g * y * g⁻¹)) * g := by rw [h1]
            _ = t * y := by rw [← hg]; group
      · rintro ⟨h1, h2⟩
        constructor
        · calc g * y * g⁻¹ * a = g * (y * t) * g⁻¹ := by rw [← hgt]; group
            _ = g * (t * y) * g⁻¹ := by rw [h2]
            _ = a * (g * y * g⁻¹) := by rw [← hgt]; group
        · calc g * y * g⁻¹ * r = g * (y * a) * g⁻¹ := by rw [hr]; group
            _ = g * (a * y) * g⁻¹ := by rw [h1]
            _ = r * (g * y * g⁻¹) := by rw [hr]; group
    have hcard : Nat.card (centralizer ({a} : Set X) ⊓ centralizer {r} : Subgroup X) =
        Nat.card (centralizer ({a} : Set X) ⊓ centralizer {t} : Subgroup X) := by
      rw [← hmap, card_map_of_injective φ.injective]
    by_contra hnot
    rcases hobs r hrH hrconj hra hnot with h2 | ⟨P, hP, hperf, heven⟩
    · exact h2 (by rw [hcard])
    · apply hnoPerfect (P.map φ.toMonoidHom)
      · rw [← hmap]
        exact map_mono hP
      · exact Group.IsPerfect.map (H := P) φ.toMonoidHom
      · rwa [card_map_of_injective φ.injective]
  refine ⟨hrecip, ?_⟩
  have hKlein : IsKleinFour (closure {a, t}) :=
    isKleinFour_closure_pair ha ht hcomm hta.symm
  set E := closure ({a, t} : Set X) with hE
  have haE : a ∈ E := subset_closure (Set.mem_insert a {t})
  have htE : t ∈ E := subset_closure (Set.mem_insert_of_mem a rfl)
  have hatE : a * t ∈ E := E.mul_mem haE htE
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hconj
  obtain ⟨h, hhH, hh⟩ := hrecip g₀⁻¹ (by rw [inv_inv]; exact hg₀)
  have hha : h * a = a * h := mem_centralizer_singleton_iff.mp hhH
  set b := g₀ * h⁻¹ with hb
  have hba : b * a * b⁻¹ = t := by
    calc b * a * b⁻¹ = g₀ * (h⁻¹ * a * h) * g₀⁻¹ := by rw [hb]; group
      _ = g₀ * a * g₀⁻¹ := by
        congr 2
        calc h⁻¹ * a * h = h⁻¹ * (h * a) := by rw [hha]; group
          _ = a := by group
      _ = t := hg₀
  have hbt : b * t * b⁻¹ = a := by
    calc b * t * b⁻¹ = g₀ * (h⁻¹ * t * h) * g₀⁻¹ := by rw [hb]; group
      _ = g₀ * (g₀⁻¹ * a * g₀⁻¹⁻¹) * g₀⁻¹ := by rw [← hh]; group
      _ = a := by group
  have hbat : b * (a * t) * b⁻¹ = a * t := by
    calc b * (a * t) * b⁻¹ = (b * a * b⁻¹) * (b * t * b⁻¹) := by group
      _ = a * t := by rw [hba, hbt, hcomm]
  have hbN : b ∈ normalizer (E : Set X) :=
    mem_normalizer_closure_pair (by rw [hba]; exact htE) (by rw [hbt]; exact haE)
  obtain ⟨c, hcH, hc⟩ := hat
  have hca : c * a * c⁻¹ = a := by
    rw [mem_centralizer_singleton_iff.mp hcH, mul_inv_cancel_right]
  have hcat : c * (a * t) * c⁻¹ = t := by
    calc c * (a * t) * c⁻¹ = (c * a * c⁻¹) * (c * t * c⁻¹) := by group
      _ = t := by rw [hca, hc, ← mul_assoc, ha2, one_mul]
  have hcN : c ∈ normalizer (E : Set X) :=
    mem_normalizer_closure_pair (by rw [hca]; exact haE) (by rw [hc]; exact hatE)
  refine ⟨hKlein, ⟨b, hbN, hba, hbt, hbat⟩, ⟨c, hcN, hca, hc, hcat⟩, ?_⟩
  set ρ := E.normalizerMonoidHom with hρ
  have hρapply : ∀ (n : normalizer (E : Set X)) (x : E), ((ρ n x : E) : X) = n * x * n⁻¹ :=
    fun n x => normalizerMonoidHom_apply_apply_coe E n x
  let bN : normalizer (E : Set X) := ⟨b, hbN⟩
  let cN : normalizer (E : Set X) := ⟨c, hcN⟩
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  have hρb2 : ρ bN ^ 2 = 1 := by
    rw [← map_pow]
    apply normalizerMonoidHom_eq_one_of_commute
    · show b ^ 2 * a = a * b ^ 2
      rw [sq]
      calc b * b * a = b * (b * a * b⁻¹) * b⁻¹ * (b * b) := by group
        _ = a * (b * b) := by rw [hba, hbt]
    · show b ^ 2 * t = t * b ^ 2
      rw [sq]
      calc b * b * t = b * (b * t * b⁻¹) * b⁻¹ * (b * b) := by group
        _ = t * (b * b) := by rw [hbt, hba]
  have hρb1 : ρ bN ≠ 1 := by
    intro h1
    have := congrArg (fun φ : MulAut E => ((φ ⟨a, haE⟩ : E) : X)) h1
    simp only [hρapply, MulAut.one_apply] at this
    have h' : b * a * b⁻¹ = a := this
    exact hta (hba.symm.trans h')
  have hρb : orderOf (ρ bN) = 2 := orderOf_eq_prime hρb2 hρb1
  have hρbc : (ρ bN * ρ cN) ^ 2 ≠ 1 := by
    intro h1
    have h2 : ρ ((bN * cN) ^ 2) = 1 := by rw [map_pow, map_mul]; exact h1
    have h3 := congrArg (fun φ : MulAut E => ((φ ⟨a, haE⟩ : E) : X)) h2
    simp only [hρapply, MulAut.one_apply] at h3
    have h4 : (b * c) ^ 2 * a * ((b * c) ^ 2)⁻¹ = a := h3
    have hval : (b * c) ^ 2 * a * ((b * c) ^ 2)⁻¹ = a * t := by
      rw [sq]
      calc b * c * (b * c) * a * (b * c * (b * c))⁻¹ =
            b * (c * (b * (c * a * c⁻¹) * b⁻¹) * c⁻¹) * b⁻¹ := by group
        _ = a * t := by rw [hca, hba, hc, hbat]
    rw [hval] at h4
    apply ht1
    calc t = a⁻¹ * (a * t) := by group
      _ = 1 := by rw [h4, inv_mul_cancel]
  have hsurj : Function.Surjective ρ := by
    have hcases := CFSG.kleinFour_automorphism_subgroup_card E ρ.range (ρ bN)
      ⟨bN, rfl⟩ hρb
    rw [← MonoidHom.range_eq_top]
    rcases hcases with h2 | h6
    · exfalso
      apply hρbc
      have hmem : ρ bN * ρ cN ∈ ρ.range := ρ.range.mul_mem ⟨bN, rfl⟩ ⟨cN, rfl⟩
      have := pow_card_eq_one' (G := ρ.range) (x := ⟨_, hmem⟩)
      rw [h2] at this
      exact congrArg Subtype.val this
    · apply eq_top_of_card_eq
      rw [h6, CFSG.kleinFour_automorphism_card E]
  refine ⟨hsurj, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq (normalizerMonoidHom_ker E)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)).trans
      (CFSG.kleinFourAutomorphismEquivSymmetricThree E)

end CFSG.ComponentClassification.UnbalancedGS
