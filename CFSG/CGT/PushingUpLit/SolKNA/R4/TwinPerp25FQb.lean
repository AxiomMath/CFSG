module

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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

theorem exists_multHom {G : Type*} [Group G] {x : G} {m : ℕ} (hm : orderOf x = m) (hm0 : 0 < m)
    (H : Subgroup G) (hH : ∀ h ∈ H, h * x * h⁻¹ ∈ Subgroup.zpowers x) :
    ∃ α : H →* (ZMod m)ˣ, ∀ h : H, (h : G) * x * (h : G)⁻¹ = x ^ ((α h : ZMod m).val) := by
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hinj : ∀ p q : ℕ, x ^ p = x ^ q → (p : ZMod m) = (q : ZMod m) := by
    intro p q hpq
    rw [pow_eq_pow_iff_modEq, hm] at hpq
    exact (ZMod.natCast_eq_natCast_iff p q m).2 hpq
  have hzpow : ∀ k : ℤ, x ^ k = x ^ ((k : ZMod m).val) := by
    intro k
    rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, hm, ← ZMod.intCast_eq_intCast_iff,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have hex : ∀ h : H, ∃ a : ZMod m, (h : G) * x * (h : G)⁻¹ = x ^ a.val := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hH (h : G) h.2)
    exact ⟨(k : ZMod m), by rw [← hk]; exact hzpow k⟩
  choose e he using hex
  have hunique : ∀ (h : H) (a : ZMod m) (p : ℕ), (p : ZMod m) = a →
      (h : G) * x * (h : G)⁻¹ = x ^ p → e h = a := by
    intro h a p hpa hp
    have h3 := hinj p _ (hp.symm.trans (he h))
    rw [ZMod.natCast_zmod_val] at h3
    rw [← hpa]
    exact h3.symm
  have he1 : e 1 = 1 := hunique 1 1 1 (by simp) (by simp)
  have hmul : ∀ h₁ h₂ : H, e (h₁ * h₂) = e h₁ * e h₂ := by
    intro h₁ h₂
    refine hunique (h₁ * h₂) (e h₁ * e h₂) ((e h₁).val * (e h₂).val) ?_ ?_
    · rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    · calc ((h₁ * h₂ : H) : G) * x * ((h₁ * h₂ : H) : G)⁻¹
          = (h₁ : G) * ((h₂ : G) * x * (h₂ : G)⁻¹) * (h₁ : G)⁻¹ := by
            rw [Subgroup.coe_mul]; group
        _ = (h₁ : G) * x ^ (e h₂).val * (h₁ : G)⁻¹ := by rw [he h₂]
        _ = ((h₁ : G) * x * (h₁ : G)⁻¹) ^ (e h₂).val := by rw [conj_pow]
        _ = (x ^ (e h₁).val) ^ (e h₂).val := by rw [he h₁]
        _ = x ^ ((e h₁).val * (e h₂).val) := by rw [pow_mul]
  let φ : H →* ZMod m := { toFun := e, map_one' := he1, map_mul' := hmul }
  exact ⟨φ.toHomUnits, fun h => he h⟩

theorem exists_extHom {Y : Type*} [Group Y] {A : Type*} [CommGroup A] {P N : Subgroup Y}
    (hNP : N ≤ P) {t' : Y} (ht'P : t' ∈ P) (ht'2 : t' * t' = 1) (ht'N : t' ∉ N)
    (hcov : ∀ g ∈ P, g ∈ N ∨ t' * g ∈ N) (hconj : ∀ g ∈ N, t' * g * t'⁻¹ ∈ N)
    (ψ : ↥N →* A)
    (hinv : ∀ (g : Y) (hg : g ∈ N) (hg' : t' * g * t'⁻¹ ∈ N),
      ψ ⟨t' * g * t'⁻¹, hg'⟩ = ψ ⟨g, hg⟩) :
    ∃ Ψ : ↥P →* A, (∀ (g : Y) (hgP : g ∈ P) (hg : g ∈ N), Ψ ⟨g, hgP⟩ = ψ ⟨g, hg⟩) ∧
      ∀ (g : Y) (hgP : g ∈ P) (hg : t' * g ∈ N), Ψ ⟨g, hgP⟩ = ψ ⟨t' * g, hg⟩ := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : Y → A, ∀ g : Y, F g =
      if hg : g ∈ N then ψ ⟨g, hg⟩ else if hg' : t' * g ∈ N then ψ ⟨t' * g, hg'⟩ else 1 :=
    ⟨fun g => if hg : g ∈ N then ψ ⟨g, hg⟩ else if hg' : t' * g ∈ N then ψ ⟨t' * g, hg'⟩ else 1,
      fun g => rfl⟩
  have hFN : ∀ g : Y, ∀ hg : g ∈ N, F g = ψ ⟨g, hg⟩ := fun g hg => by
    rw [hF, dif_pos hg]
  have hFnN : ∀ g : Y, ∀ hg : g ∉ N, ∀ hg' : t' * g ∈ N, F g = ψ ⟨t' * g, hg'⟩ :=
    fun g hg hg' => by rw [hF, dif_neg hg, dif_pos hg']
  have hnN : ∀ g : Y, g ∈ N → t' * g ∉ N := by
    intro g hg htg
    apply ht'N
    have h2 : t' * g * g⁻¹ ∈ N := N.mul_mem htg (N.inv_mem hg)
    simpa using h2
  have hmul : ∀ g ∈ P, ∀ h ∈ P, F (g * h) = F g * F h := by
    intro g hgP h hhP
    by_cases hg : g ∈ N <;> by_cases hh : h ∈ N
    · rw [hFN g hg, hFN h hh, hFN (g * h) (N.mul_mem hg hh)]
      exact map_mul ψ ⟨g, hg⟩ ⟨h, hh⟩
    · have hth : t' * h ∈ N := (hcov h hhP).resolve_left hh
      have hgh : g * h ∉ N := fun hc => hh (by simpa using N.mul_mem (N.inv_mem hg) hc)
      have htgh : t' * (g * h) ∈ N := by
        have h2 := N.mul_mem (hconj g hg) hth
        have e : t' * g * t'⁻¹ * (t' * h) = t' * (g * h) := by group
        rwa [e] at h2
      calc F (g * h) = ψ ⟨t' * (g * h), htgh⟩ := hFnN _ hgh htgh
        _ = ψ (⟨t' * g * t'⁻¹, hconj g hg⟩ * ⟨t' * h, hth⟩) :=
            congrArg ψ (Subtype.ext (by
              show t' * (g * h) = t' * g * t'⁻¹ * (t' * h)
              group))
        _ = ψ ⟨t' * g * t'⁻¹, hconj g hg⟩ * ψ ⟨t' * h, hth⟩ := map_mul ψ _ _
        _ = ψ ⟨g, hg⟩ * ψ ⟨t' * h, hth⟩ := by rw [hinv g hg (hconj g hg)]
        _ = F g * F h := by rw [hFN g hg, hFnN h hh hth]
    · have htg : t' * g ∈ N := (hcov g hgP).resolve_left hg
      have hgh : g * h ∉ N := fun hc => hg (by simpa using N.mul_mem hc (N.inv_mem hh))
      have htgh : t' * (g * h) ∈ N := by
        have h2 := N.mul_mem htg hh
        rwa [mul_assoc] at h2
      calc F (g * h) = ψ ⟨t' * (g * h), htgh⟩ := hFnN _ hgh htgh
        _ = ψ (⟨t' * g, htg⟩ * ⟨h, hh⟩) :=
            congrArg ψ (Subtype.ext (by
              show t' * (g * h) = t' * g * h
              group))
        _ = ψ ⟨t' * g, htg⟩ * ψ ⟨h, hh⟩ := map_mul ψ _ _
        _ = F g * F h := by rw [hFnN g hg htg, hFN h hh]
    · have htg : t' * g ∈ N := (hcov g hgP).resolve_left hg
      have hth : t' * h ∈ N := (hcov h hhP).resolve_left hh
      have e : t' * (t' * g) * t'⁻¹ * (t' * h) = g * h := by
        calc t' * (t' * g) * t'⁻¹ * (t' * h) = (t' * t') * g * (t'⁻¹ * t') * h := by group
          _ = g * h := by rw [ht'2, inv_mul_cancel, one_mul, mul_one]
      have hgh : g * h ∈ N := by
        have h2 := N.mul_mem (hconj (t' * g) htg) hth
        rwa [e] at h2
      calc F (g * h) = ψ ⟨g * h, hgh⟩ := hFN _ hgh
        _ = ψ (⟨t' * (t' * g) * t'⁻¹, hconj (t' * g) htg⟩ * ⟨t' * h, hth⟩) :=
            congrArg ψ (Subtype.ext (by
              show g * h = t' * (t' * g) * t'⁻¹ * (t' * h)
              rw [e]))
        _ = ψ ⟨t' * (t' * g) * t'⁻¹, hconj (t' * g) htg⟩ * ψ ⟨t' * h, hth⟩ := map_mul ψ _ _
        _ = ψ ⟨t' * g, htg⟩ * ψ ⟨t' * h, hth⟩ := by
            rw [hinv (t' * g) htg (hconj (t' * g) htg)]
        _ = F g * F h := by rw [hFnN g hg htg, hFnN h hh hth]
  refine ⟨MonoidHom.mk' (fun g : ↥P => F g) (fun a b => hmul a a.2 b b.2), ?_, ?_⟩
  · intro g _ hg
    exact hFN g hg
  · intro g _ hg
    exact hFnN g (fun hgN => hnN g hgN hg) hg

theorem exists_conj_of_inv_odd {G : Type*} [Group G] {s o : G} (hs : s * s = 1)
    (ho : Odd (orderOf o)) (hso : s * o * s⁻¹ = o⁻¹) :
    ∃ w ∈ Subgroup.zpowers o, o * s = w * s * w⁻¹ := by
  obtain ⟨k, hk⟩ := ho
  have hw : o ^ (k + 1) * o ^ (k + 1) = o := by
    rw [← pow_add]
    have h2 : k + 1 + (k + 1) = orderOf o + 1 := by omega
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hconjw : s * o ^ (k + 1) * s⁻¹ = (o ^ (k + 1))⁻¹ := by
    rw [← conj_pow, hso, inv_pow]
  have h1 : s * (o ^ (k + 1))⁻¹ * s⁻¹ = o ^ (k + 1) := by
    rw [show s * (o ^ (k + 1))⁻¹ * s⁻¹ = (s * o ^ (k + 1) * s⁻¹)⁻¹ by group, hconjw, inv_inv]
  refine ⟨o ^ (k + 1), pow_mem (Subgroup.mem_zpowers o) (k + 1), ?_⟩
  calc o * s = o ^ (k + 1) * o ^ (k + 1) * s := by rw [hw]
    _ = o ^ (k + 1) * (s * (o ^ (k + 1))⁻¹ * s⁻¹) * s := by rw [h1]
    _ = o ^ (k + 1) * s * (o ^ (k + 1))⁻¹ := by group

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
