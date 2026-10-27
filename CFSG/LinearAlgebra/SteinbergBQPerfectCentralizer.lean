module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Module

theorem eq_one_of_commute_of_perfect {G M : Type*} [Group G] [Monoid M] {P : Subgroup G}
    (hP : ⁅P, P⁆ = P) (φ : P →* M) (hcomm : ∀ g h : P, φ g * φ h = φ h * φ g) (g : P) :
    φ g = 1 := by
  have hK : ⁅P, P⁆ ≤ φ.ker.map P.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩)⁻¹ * (⟨b, hb⟩)⁻¹, ?_, ?_⟩
    · change φ _ = 1
      rw [map_mul, map_mul, map_mul, hcomm ⟨a, ha⟩ ⟨b, hb⟩, mul_assoc (φ _),
        ← map_mul, mul_inv_cancel, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]
    · simp [commutatorElement_def]
  have hgP : (g : G) ∈ ⁅P, P⁆ := by
    rw [hP]
    exact g.2
  obtain ⟨g', hg', hgg'⟩ := hK hgP
  have : g' = g := Subtype.ext hgg'
  rw [← this]
  exact hg'

section Commutant

variable {k X : Type*} [Field k] [AddCommGroup X] [Module k X]

theorem aeval_mul_comm (T : Module.End k X) (p : Polynomial k) :
    Polynomial.aeval T p * T = T * Polynomial.aeval T p := by
  have h : T = Polynomial.aeval T (Polynomial.X : Polynomial k) := (Polynomial.aeval_X T).symm
  calc Polynomial.aeval T p * T = Polynomial.aeval T p * Polynomial.aeval T Polynomial.X := by
        rw [← h]
    _ = Polynomial.aeval T Polynomial.X * Polynomial.aeval T p := by
        rw [← map_mul, ← map_mul, mul_comm]
    _ = T * Polynomial.aeval T p := by rw [← h]

theorem exists_aeval_of_span {T : Module.End k X} {x : X}
    (hx : Submodule.span k (Set.range ![x, T x, T (T x)]) = ⊤) {S : Module.End k X}
    (hS : S * T = T * S) : ∃ p : Polynomial k, S = Polynomial.aeval T p := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1
    (hx ▸ Submodule.mem_top : S x ∈ Submodule.span k (Set.range ![x, T x, T (T x)]))
  set p : Polynomial k := Polynomial.C (c 0) + Polynomial.C (c 1) * Polynomial.X +
    Polynomial.C (c 2) * Polynomial.X ^ 2 with hp
  refine ⟨p, LinearMap.ext_on_range hx fun i => ?_⟩
  have hpx : Polynomial.aeval T p x = S x := by
    rw [← hc, Fin.sum_univ_three]
    simp [hp, pow_two]
  have hST : ∀ y, S (T y) = T (S y) := fun y => by
    rw [← Module.End.mul_apply, hS, Module.End.mul_apply]
  have hPT : ∀ y, Polynomial.aeval T p (T y) = T (Polynomial.aeval T p y) := fun y => by
    rw [← Module.End.mul_apply, aeval_mul_comm, Module.End.mul_apply]
  fin_cases i
  · exact hpx.symm
  · change S (T x) = Polynomial.aeval T p (T x)
    rw [hST, hPT, hpx]
  · change S (T (T x)) = Polynomial.aeval T p (T (T x))
    rw [hST, hST, hPT, hPT, hpx]

theorem exists_span_eq_top_of_no_eigenvector [FiniteDimensional k X]
    (hX : finrank k X = 2 ∨ finrank k X = 3) {T : Module.End k X}
    (heig : ∀ (c : k) (x : X), x ≠ 0 → T x ≠ c • x)
    (hquad : ∀ a b : k, (∃ x : X, x ≠ 0 ∧ T (T x) = a • x + b • T x) →
      ∀ y, T (T y) = a • y + b • T y) :
    ∃ x : X, Submodule.span k (Set.range ![x, T x, T (T x)]) = ⊤ := by
  have hpos : 0 < finrank k X := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hpair : ∀ y : X, y ≠ 0 → finrank k (Submodule.span k {y, T y}) = 2 := by
    intro y hy
    have hli : LinearIndependent k ![y, T y] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · rw [ht, zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.1 hst).resolve_right hy, ht⟩
      · exfalso
        apply heig (-(s / t)) y hy
        have e : T y = t⁻¹ • (t • T y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [e, eq_neg_of_add_eq_zero_right hst, smul_neg, neg_smul, smul_smul, div_eq_inv_mul]
    have := finrank_span_eq_card hli
    rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Fintype.card_fin] at this
  have hrange : ∀ y : X, Set.range ![y, T y, T (T y)] = {y, T y, T (T y)} := fun y => by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union, Set.singleton_union]
  have hle : ∀ y : X, Submodule.span k {y, T y} ≤ Submodule.span k {y, T y, T (T y)} :=
    fun y => Submodule.span_mono (Set.insert_subset_insert
      (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  rcases hX with h2 | h3
  · refine ⟨x, ?_⟩
    rw [hrange]
    refine Submodule.eq_top_of_finrank_eq ?_
    have h1 := Submodule.finrank_mono (hle x)
    have h2' := Submodule.finrank_le (Submodule.span k {x, T x, T (T x)})
    rw [hpair x hx] at h1
    omega
  · by_cases hin : T (T x) ∈ Submodule.span k {x, T x}
    · exfalso
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hin
      have hq := hquad a b ⟨x, hx, hab.symm⟩
      have hlt : Submodule.span k {x, T x} < ⊤ := by
        refine lt_top_iff_ne_top.2 fun h => ?_
        have := finrank_top k X
        rw [← h, hpair x hx] at this
        omega
      obtain ⟨y, -, hy⟩ := IsConcreteLE.exists_of_lt hlt
      have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
      have hinv : ∀ z : X, ∀ w ∈ Submodule.span k {z, T z}, T w ∈ Submodule.span k {z, T z} := by
        intro z w hw
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hw
        rw [map_add, map_smul, map_smul, hq z, smul_add, smul_smul, smul_smul]
        refine Submodule.mem_span_pair.2 ⟨t * a, s + t * b, ?_⟩
        rw [add_smul]
        abel
      set U1 := Submodule.span k {x, T x} with hU1
      set U2 := Submodule.span k {y, T y} with hU2
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq U1 U2
      have hsup := Submodule.finrank_le (U1 ⊔ U2)
      rw [hpair x hx, hpair y hy0] at hdim
      rw [h3] at hsup
      have hyU2 : y ∈ U2 := Submodule.subset_span (by simp)
      have hne : U1 ⊓ U2 ≠ U1 := by
        intro h
        have hle' : U1 ≤ U2 := h ▸ inf_le_right
        have heq : U1 = U2 :=
          Submodule.eq_of_le_of_finrank_eq hle' (by rw [hpair x hx, hpair y hy0])
        exact hy (heq ▸ hyU2)
      have hinf2 : finrank k ↥(U1 ⊓ U2) ≠ 2 := by
        intro h
        exact hne (Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h, hpair x hx]))
      have hinf1 : finrank k ↥(U1 ⊓ U2) = 1 := by
        have := Submodule.finrank_mono (inf_le_left : U1 ⊓ U2 ≤ U1)
        rw [hpair x hx] at this
        omega
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := U1 ⊓ U2)
        (fun h => by rw [h, finrank_bot] at hinf1; omega)
      have hTz : T z ∈ U1 ⊓ U2 := ⟨hinv x z hz.1, hinv y z hz.2⟩
      have hspan : Submodule.span k {z} = U1 ⊓ U2 :=
        Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hz)
          (by rw [finrank_span_singleton hz0, hinf1])
      rw [← hspan] at hTz
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hTz
      exact heig c z hz0 hc.symm
    · refine ⟨x, ?_⟩
      rw [hrange]
      refine Submodule.eq_top_of_finrank_eq ?_
      have hlt : Submodule.span k {x, T x} < Submodule.span k {x, T x, T (T x)} := by
        refine lt_of_le_of_ne (hle x) fun h => hin ?_
        rw [h]
        exact Submodule.subset_span (by simp)
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2' := Submodule.finrank_le (Submodule.span k {x, T x, T (T x)})
      rw [hpair x hx] at h1
      omega

theorem eq_smul_one_of_irreducible {G : Type*} [Group G] (hX : finrank k X = 2 ∨ finrank k X = 3)
    (φ : G →* Module.End k X) (hperf : (∀ g h, φ g * φ h = φ h * φ g) → ∀ g, φ g = 1)
    (hirr : ∀ U : Submodule k X, (∀ g, ∀ u ∈ U, φ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (T : Module.End k X) (hT : ∀ g, T * φ g = φ g * T) : ∃ c : k, T = c • 1 := by
  have hfin : FiniteDimensional k X := Module.finite_of_finrank_pos (by omega)
  have hkerinv : ∀ Q : Module.End k X, (∀ g, Q * φ g = φ g * Q) →
      ∀ g, ∀ u ∈ LinearMap.ker Q, φ g u ∈ LinearMap.ker Q := by
    intro Q hQ g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← Module.End.mul_apply, hQ g, Module.End.mul_apply, hu, map_zero]
  by_cases heig : ∃ c : k, ∃ x : X, x ≠ 0 ∧ T x = c • x
  · obtain ⟨c, x, hx0, hTx⟩ := heig
    refine ⟨c, ?_⟩
    have hQ : ∀ g, (T - c • 1) * φ g = φ g * (T - c • 1) := fun g => by
      rw [sub_mul, mul_sub, hT g, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rcases hirr _ (hkerinv _ hQ) with h | h
    · exfalso
      have hxk : x ∈ LinearMap.ker (T - c • 1) := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hTx, LinearMap.smul_apply,
          Module.End.one_apply, sub_self]
      rw [h, Submodule.mem_bot] at hxk
      exact hx0 hxk
    · refine LinearMap.ext fun y => ?_
      have hy : y ∈ LinearMap.ker (T - c • 1) := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hy
      exact hy
  · push Not at heig
    exfalso
    have hquad : ∀ a b : k, (∃ x : X, x ≠ 0 ∧ T (T x) = a • x + b • T x) →
        ∀ y, T (T y) = a • y + b • T y := by
      rintro a b ⟨x, hx0, hx⟩ y
      set Q := T * T - a • 1 - b • T with hQdef
      have hQ : ∀ g, Q * φ g = φ g * Q := fun g => by
        rw [hQdef, sub_mul, sub_mul, mul_sub, mul_sub, mul_assoc, hT g, ← mul_assoc, hT g,
          mul_assoc, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_mul_assoc,
          mul_smul_comm, hT g]
      rcases hirr _ (hkerinv _ hQ) with h | h
      · have hxk : x ∈ LinearMap.ker Q := by
          rw [LinearMap.mem_ker, hQdef, LinearMap.sub_apply, LinearMap.sub_apply,
            Module.End.mul_apply, hx, LinearMap.smul_apply, LinearMap.smul_apply,
            Module.End.one_apply]
          abel
        rw [h, Submodule.mem_bot] at hxk
        exact absurd hxk hx0
      · have hy : y ∈ LinearMap.ker Q := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker, hQdef, LinearMap.sub_apply, LinearMap.sub_apply,
          Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
          Module.End.one_apply, sub_sub, sub_eq_zero] at hy
        exact hy
    obtain ⟨x, hx⟩ := exists_span_eq_top_of_no_eigenvector hX heig hquad
    have hcomm : ∀ g h, φ g * φ h = φ h * φ g := by
      intro g h
      obtain ⟨p, hp⟩ := exists_aeval_of_span hx (hT g).symm
      obtain ⟨p', hp'⟩ := exists_aeval_of_span hx (hT h).symm
      rw [hp, hp', ← map_mul, ← map_mul, mul_comm]
    have h1 := hperf hcomm
    obtain ⟨y, hy⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < finrank k X)
    rcases hirr (Submodule.span k {y}) (fun g u hu => by rw [h1 g]; exact hu) with h | h
    · rw [Submodule.span_singleton_eq_bot] at h
      exact hy h
    · have := finrank_span_singleton (K := k) hy
      rw [h, finrank_top] at this
      omega

end Commutant

section Segment

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

@[expose] def segMap {A B : Submodule k V} (f : V →ₗ[k] V) (hfB : ∀ b ∈ B, f b ∈ B)
    (hfA : ∀ a ∈ A, f a ∈ A) : Module.End k (B ⧸ A.comap B.subtype) :=
  (A.comap B.subtype).mapQ (A.comap B.subtype) (f.restrict hfB) fun _ hx => hfA _ hx

theorem segMap_mk {A B : Submodule k V} (f : V →ₗ[k] V) (hfB : ∀ b ∈ B, f b ∈ B)
    (hfA : ∀ a ∈ A, f a ∈ A) (b : B) :
    segMap f hfB hfA (Submodule.Quotient.mk b) = Submodule.Quotient.mk ⟨f b, hfB b b.2⟩ :=
  rfl

@[expose] def segRep {A B : Submodule k V} (P : Subgroup (LinearMap.GeneralLinearGroup k V))
    (hPB : ∀ g ∈ P, ∀ b ∈ B, (g : V →ₗ[k] V) b ∈ B)
    (hPA : ∀ g ∈ P, ∀ a ∈ A, (g : V →ₗ[k] V) a ∈ A) :
    P →* Module.End k (B ⧸ A.comap B.subtype) where
  toFun g := segMap ((g : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) (hPB g g.2) (hPA g g.2)
  map_one' := by
    refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun b => ?_
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun b => ?_
    rfl

theorem segRep_mk {A B : Submodule k V} {P : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hPB : ∀ g ∈ P, ∀ b ∈ B, (g : V →ₗ[k] V) b ∈ B)
    (hPA : ∀ g ∈ P, ∀ a ∈ A, (g : V →ₗ[k] V) a ∈ A) (g : P) (b : B) :
    segRep P hPB hPA g (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk
        ⟨((g : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) b, hPB g g.2 b b.2⟩ :=
  rfl

theorem exists_scalar_of_irreducible_segment [FiniteDimensional k V]
    {P : Subgroup (LinearMap.GeneralLinearGroup k V)} (hPperf : ⁅P, P⁆ = P)
    {A B : Submodule k V} (hAB : A ≤ B)
    (hdim : finrank k B = finrank k A + 2 ∨ finrank k B = finrank k A + 3)
    (hPB : ∀ g ∈ P, ∀ b ∈ B, (g : V →ₗ[k] V) b ∈ B)
    (hPA : ∀ g ∈ P, ∀ a ∈ A, (g : V →ₗ[k] V) a ∈ A)
    (hirr : ∀ D : Submodule k V, A ≤ D → D ≤ B →
      (∀ g ∈ P, ∀ d ∈ D, (g : V →ₗ[k] V) d ∈ D) → D = A ∨ D = B)
    {c : V →ₗ[k] V} (hcB : ∀ b ∈ B, c b ∈ B) (hcA : ∀ a ∈ A, c a ∈ A)
    (hcP : ∀ g ∈ P, ∀ v, c ((g : V →ₗ[k] V) v) = (g : V →ₗ[k] V) (c v)) :
    ∃ α : k, ∀ b ∈ B, c b - α • b ∈ A := by
  set A' := A.comap B.subtype with hA'
  have hA'dim : finrank k A' = finrank k A :=
    (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq
  have hQdim := Submodule.finrank_quotient_add_finrank A'
  have hQ : finrank k (B ⧸ A') = 2 ∨ finrank k (B ⧸ A') = 3 := by omega
  have hmkA : ∀ b : B, (Submodule.Quotient.mk b : B ⧸ A') = 0 ↔ (b : V) ∈ A := fun b => by
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  have hirrQ : ∀ U : Submodule k (B ⧸ A'),
      (∀ g, ∀ u ∈ U, segRep P hPB hPA g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    set D : Submodule k V := (U.comap A'.mkQ).map B.subtype with hD
    have hmemD : ∀ b : B, (b : V) ∈ D ↔ (Submodule.Quotient.mk b : B ⧸ A') ∈ U := by
      intro b
      constructor
      · rintro ⟨b', hb', hbb'⟩
        rw [← Subtype.ext hbb']
        exact hb'
      · intro hb
        exact ⟨b, hb, rfl⟩
    have hAD : A ≤ D := fun a ha => by
      have := (hmemD ⟨a, hAB ha⟩).2 (by rw [(hmkA ⟨a, hAB ha⟩).2 ha]; exact U.zero_mem)
      exact this
    have hDB : D ≤ B := by
      rintro _ ⟨b, -, rfl⟩
      exact b.2
    have hDinv : ∀ g ∈ P, ∀ d ∈ D, (g : V →ₗ[k] V) d ∈ D := by
      intro g hg d hd
      obtain ⟨b, hb, rfl⟩ := hd
      have := (hmemD ⟨(g : V →ₗ[k] V) b, hPB g hg b b.2⟩).2 (by
        have h1 := hU ⟨g, hg⟩ _ hb
        exact h1)
      exact this
    rcases hirr D hAD hDB hDinv with h | h
    · left
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.mem_bot, hmkA]
      rw [← h]
      exact (hmemD b).2 hq
    · right
      rw [eq_top_iff]
      have hBD : ∀ b : B, (b : V) ∈ D := fun b => by
        rw [h]
        exact b.2
      exact fun q _ => Submodule.Quotient.induction_on _ q fun b => (hmemD b).1 (hBD b)
  obtain ⟨α, hα⟩ := eq_smul_one_of_irreducible hQ (segRep P hPB hPA)
    (eq_one_of_commute_of_perfect hPperf _) hirrQ (segMap c hcB hcA) (fun g => by
      refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun b => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, segRep_mk, segMap_mk, segMap_mk, segRep_mk]
      congr 1
      exact Subtype.ext (hcP g g.2 b))
  refine ⟨α, fun b hb => ?_⟩
  have h1 := LinearMap.congr_fun hα (Submodule.Quotient.mk ⟨b, hb⟩)
  rw [segMap_mk, LinearMap.smul_apply, Module.End.one_apply, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq] at h1
  exact h1

theorem exists_scalar_of_finrank_succ [FiniteDimensional k V] {A B : Submodule k V}
    (hAB : A ≤ B) (hdim : finrank k B = finrank k A + 1) {f : V →ₗ[k] V}
    (hfA : ∀ a ∈ A, f a ∈ A) (hfB : ∀ b ∈ B, f b ∈ B) : ∃ α : k, ∀ b ∈ B, f b - α • b ∈ A := by
  have hlt : A < B := lt_of_le_of_ne hAB fun h => by rw [h] at hdim; omega
  obtain ⟨b₀, hb₀B, hb₀A⟩ := IsConcreteLE.exists_of_lt hlt
  have hsup : A ⊔ Submodule.span k {b₀} = B := by
    refine Submodule.eq_of_le_of_finrank_le (sup_le hAB
      ((Submodule.span_singleton_le_iff_mem _ _).2 hb₀B)) ?_
    have h1 : A < A ⊔ Submodule.span k {b₀} := lt_of_le_of_ne le_sup_left fun h =>
      hb₀A (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self b₀))
    have := Submodule.finrank_lt_finrank_of_lt h1
    omega
  have hdec : ∀ b ∈ B, ∃ a ∈ A, ∃ t : k, b = a + t • b₀ := by
    intro b hb
    rw [← hsup] at hb
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 hb
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨a, ha, t, rfl⟩
  obtain ⟨a₀, ha₀, α, hα⟩ := hdec _ (hfB b₀ hb₀B)
  refine ⟨α, fun b hb => ?_⟩
  obtain ⟨a, ha, t, rfl⟩ := hdec b hb
  have e : f (a + t • b₀) - α • (a + t • b₀) = (f a - α • a) + t • a₀ := by
    rw [map_add, map_smul, hα, smul_add, smul_add, smul_smul, smul_smul, mul_comm t α]
    abel
  rw [e]
  exact A.add_mem (A.sub_mem (hfA a ha) (A.smul_mem α ha)) (A.smul_mem t ha₀)

theorem sub_mem_of_commute_mod {P : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hPperf : ⁅P, P⁆ = P) {A B : Submodule k V}
    (hPB : ∀ g ∈ P, ∀ b ∈ B, (g : V →ₗ[k] V) b ∈ B)
    (hPA : ∀ g ∈ P, ∀ a ∈ A, (g : V →ₗ[k] V) a ∈ A)
    (hcomm : ∀ g ∈ P, ∀ h ∈ P, ∀ b ∈ B,
      (g : V →ₗ[k] V) ((h : V →ₗ[k] V) b) - (h : V →ₗ[k] V) ((g : V →ₗ[k] V) b) ∈ A)
    {g : LinearMap.GeneralLinearGroup k V} (hg : g ∈ P) {b : V} (hb : b ∈ B) :
    (g : V →ₗ[k] V) b - b ∈ A := by
  have h1 := eq_one_of_commute_of_perfect hPperf (segRep P hPB hPA) (fun g h => by
    refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun b => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, segRep_mk, segRep_mk, segRep_mk, segRep_mk,
      Submodule.Quotient.eq]
    exact hcomm g g.2 h h.2 b b.2) ⟨g, hg⟩
  have h2 := LinearMap.congr_fun h1 (Submodule.Quotient.mk ⟨b, hb⟩)
  rw [segRep_mk, Module.End.one_apply, Submodule.Quotient.eq] at h2
  exact h2

end Segment

end CFSG.LinearAlgebra.SteinbergBQ

namespace CFSG.LinearAlgebra

open Module SteinbergBQ

theorem degree_three_perfect_matrix_subgroup_centralizer_metabelian {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (hV : finrank k V = 3)
    (P : Subgroup (LinearMap.GeneralLinearGroup k V)) (hP1 : P ≠ ⊥) (hPperf : ⁅P, P⁆ = P) :
    (∀ x ∈ ⁅Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V)),
        Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V))⁆,
      ∀ y ∈ ⁅Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V)),
        Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V))⁆, x * y = y * x) ∧
    Group.IsSolvable (Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V))) := by
  classical
  have : FiniteDimensional k V := Module.finite_of_finrank_pos (by omega)
  set C := Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V)) with hCdef
  have hCP : ∀ c ∈ C, ∀ g ∈ P, ∀ v,
      (c : V →ₗ[k] V) ((g : V →ₗ[k] V) v) = (g : V →ₗ[k] V) ((c : V →ₗ[k] V) v) := by
    intro c hc g hg v
    have h := (Subgroup.mem_centralizer_iff.1 hc) g hg
    have h2 := congrArg (fun x : LinearMap.GeneralLinearGroup k V => (x : V →ₗ[k] V) v) h
    simpa [Units.val_mul] using h2.symm
  let Inv : Submodule k V → Prop := fun U => ∀ g ∈ P, ∀ u ∈ U, (g : V →ₗ[k] V) u ∈ U
  have hInvbot : Inv ⊥ := fun g _ u hu => by
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  have hInvtop : Inv ⊤ := fun _ _ _ _ => Submodule.mem_top
  have hseg1 : ∀ A B : Submodule k V, A ≤ B → Inv A → Inv B → finrank k B = finrank k A + 1 →
      ∀ g ∈ P, ∀ b ∈ B, (g : V →ₗ[k] V) b - b ∈ A := by
    intro A B hAB hA hB hdim g hg b hb
    refine sub_mem_of_commute_mod hPperf hB hA (fun g hg h hh b hb => ?_) hg hb
    obtain ⟨α, hα⟩ := exists_scalar_of_finrank_succ hAB hdim (hA g hg) (hB g hg)
    obtain ⟨β, hβ⟩ := exists_scalar_of_finrank_succ hAB hdim (hA h hh) (hB h hh)
    have e1 := hα _ (hB h hh b hb)
    have e2 := hβ _ (hB g hg b hb)
    have e3 := hα b hb
    have e4 := hβ b hb
    have e : (g : V →ₗ[k] V) ((h : V →ₗ[k] V) b) - (h : V →ₗ[k] V) ((g : V →ₗ[k] V) b) =
        (((g : V →ₗ[k] V) ((h : V →ₗ[k] V) b) - α • (h : V →ₗ[k] V) b) +
          α • ((h : V →ₗ[k] V) b - β • b)) -
        (((h : V →ₗ[k] V) ((g : V →ₗ[k] V) b) - β • (g : V →ₗ[k] V) b) +
          β • ((g : V →ₗ[k] V) b - α • b)) := by
      simp only [smul_sub, smul_smul, mul_comm α β]
      abel
    rw [e]
    exact A.sub_mem (A.add_mem e1 (A.smul_mem α e4)) (A.add_mem e2 (A.smul_mem β e3))
  have hseg2 : ∀ A M B : Submodule k V, A ≤ M → M ≤ B → Inv A → Inv B →
      (∀ g ∈ P, ∀ m ∈ M, (g : V →ₗ[k] V) m - m ∈ A) →
      (∀ g ∈ P, ∀ b ∈ B, (g : V →ₗ[k] V) b - b ∈ M) →
      ∀ g ∈ P, ∀ b ∈ B, (g : V →ₗ[k] V) b - b ∈ A := by
    intro A M B hAM hMB hA hB hM hBM g hg b hb
    refine sub_mem_of_commute_mod hPperf hB hA (fun g hg h hh b hb => ?_) hg hb
    have e1 := hM g hg _ (hBM h hh b hb)
    have e2 := hM h hh _ (hBM g hg b hb)
    have e : (g : V →ₗ[k] V) ((h : V →ₗ[k] V) b) - (h : V →ₗ[k] V) ((g : V →ₗ[k] V) b) =
        ((g : V →ₗ[k] V) ((h : V →ₗ[k] V) b - b) - ((h : V →ₗ[k] V) b - b)) -
        ((h : V →ₗ[k] V) ((g : V →ₗ[k] V) b - b) - ((g : V →ₗ[k] V) b - b)) := by
      simp only [map_sub]
      abel
    rw [e]
    exact A.sub_mem e1 e2
  have hflag : ∀ U₁ U₂ : Submodule k V, U₁ ≤ U₂ → Inv U₁ → Inv U₂ → finrank k U₁ = 1 →
      finrank k U₂ = 2 → False := by
    intro U₁ U₂ h12 h1 h2 hd1 hd2
    have s1 := hseg1 ⊥ U₁ bot_le hInvbot h1 (by rw [finrank_bot, hd1])
    have s2 := hseg1 U₁ U₂ h12 h1 h2 (by rw [hd1, hd2])
    have s3 := hseg1 U₂ ⊤ le_top h2 hInvtop (by rw [finrank_top, hV, hd2])
    have t1 := hseg2 ⊥ U₁ U₂ bot_le h12 hInvbot h2 s1 s2
    have t2 := hseg2 ⊥ U₂ ⊤ bot_le le_top hInvbot hInvtop t1 s3
    apply hP1
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine Units.ext (LinearMap.ext fun v => ?_)
    have := t2 g hg v Submodule.mem_top
    rw [Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hmain : ∀ W : Submodule k V,
      (∀ c ∈ C, ∀ w ∈ W, (c : V →ₗ[k] V) w ∈ W) →
      (∀ c ∈ C, ∃ α : k, ∀ w ∈ W, (c : V →ₗ[k] V) w = α • w) →
      (∀ c ∈ C, ∃ β : k, ∀ v, (c : V →ₗ[k] V) v - β • v ∈ W) →
      ∀ x ∈ ⁅C, C⁆, ∀ y ∈ ⁅C, C⁆, x * y = y * x := by
    intro W hstab hα hβ
    let K : Subgroup (LinearMap.GeneralLinearGroup k V) :=
      { carrier := {g | (∀ w ∈ W, (g : V →ₗ[k] V) w = w) ∧ ∀ v, (g : V →ₗ[k] V) v - v ∈ W}
        mul_mem' := by
          rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
          refine ⟨fun w hw => ?_, fun v => ?_⟩
          · rw [Units.val_mul, Module.End.mul_apply, hh1 w hw, hg1 w hw]
          · rw [Units.val_mul, Module.End.mul_apply]
            have e : (g : V →ₗ[k] V) ((h : V →ₗ[k] V) v) - v =
                ((g : V →ₗ[k] V) ((h : V →ₗ[k] V) v) - (h : V →ₗ[k] V) v) +
                  ((h : V →ₗ[k] V) v - v) := by abel
            rw [e]
            exact W.add_mem (hg2 _) (hh2 v)
        one_mem' := ⟨fun w _ => rfl, fun v => by
          rw [Units.val_one, Module.End.one_apply, sub_self]
          exact W.zero_mem⟩
        inv_mem' := by
          rintro g ⟨hg1, hg2⟩
          have hgg : ∀ v, (g : V →ₗ[k] V) (((g⁻¹ : LinearMap.GeneralLinearGroup k V) :
              V →ₗ[k] V) v) = v := fun v => by
            rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Module.End.one_apply]
          refine ⟨fun w hw => ?_, fun v => ?_⟩
          · have h1 := hgg w
            have h2 := hg2 (((g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w)
            rw [h1] at h2
            have h3 : ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w ∈ W := by
              have := W.sub_mem hw h2
              rwa [sub_sub_cancel] at this
            exact (hg1 _ h3).symm.trans h1
          · have h2 := hg2 (((g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) v)
            rw [hgg] at h2
            have := W.neg_mem h2
            rwa [neg_sub] at this }
    have hK : ∀ g, g ∈ K ↔
        (∀ w ∈ W, (g : V →ₗ[k] V) w = w) ∧ ∀ v, (g : V →ₗ[k] V) v - v ∈ W := fun g => Iff.rfl
    have hKcomm : ∀ g ∈ K, ∀ h ∈ K, g * h = h * g := by
      intro g hg h hh
      obtain ⟨hg1, hg2⟩ := (hK g).1 hg
      obtain ⟨hh1, hh2⟩ := (hK h).1 hh
      refine Units.ext (LinearMap.ext fun v => ?_)
      rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
      have e1 : (g : V →ₗ[k] V) ((h : V →ₗ[k] V) v) =
          (g : V →ₗ[k] V) v + ((h : V →ₗ[k] V) v - v) := by
        rw [← hg1 _ (hh2 v), ← map_add, add_sub_cancel]
      have e2 : (h : V →ₗ[k] V) ((g : V →ₗ[k] V) v) =
          (h : V →ₗ[k] V) v + ((g : V →ₗ[k] V) v - v) := by
        rw [← hh1 _ (hg2 v), ← map_add, add_sub_cancel]
      rw [e1, e2]
      abel
    have hCK : ⁅C, C⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro c hc c' hc'
      obtain ⟨α, hα'⟩ := hα c hc
      obtain ⟨α', hα''⟩ := hα c' hc'
      obtain ⟨β, hβ'⟩ := hβ c hc
      obtain ⟨β', hβ''⟩ := hβ c' hc'
      set p := c * c' with hp
      set q := c' * c with hq
      have hcomm' : c * c' * c⁻¹ * c'⁻¹ = p * q⁻¹ := by
        rw [hp, hq]
        group
      have hqC : q⁻¹ ∈ C := C.inv_mem (C.mul_mem hc' hc)
      have hpq : ∀ w ∈ W, (p : V →ₗ[k] V) w = (q : V →ₗ[k] V) w := by
        intro w hw
        rw [hp, hq, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
          hα'' w hw, map_smul, hα' w hw, map_smul, hα'' w hw, smul_smul, smul_smul,
          mul_comm]
      have hpq' : ∀ v, (p : V →ₗ[k] V) v - (q : V →ₗ[k] V) v ∈ W := by
        intro v
        rw [hp, hq, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
        have e : (c : V →ₗ[k] V) ((c' : V →ₗ[k] V) v) - (c' : V →ₗ[k] V) ((c : V →ₗ[k] V) v) =
            ((c : V →ₗ[k] V) ((c' : V →ₗ[k] V) v - β' • v) + β' • ((c : V →ₗ[k] V) v - β • v)) -
            ((c' : V →ₗ[k] V) ((c : V →ₗ[k] V) v - β • v) + β • ((c' : V →ₗ[k] V) v - β' • v)) := by
          simp only [map_sub, map_smul, smul_sub, smul_smul, mul_comm β β']
          abel
        rw [e]
        exact W.sub_mem (W.add_mem (hstab c hc _ (hβ'' v)) (W.smul_mem β' (hβ' v)))
          (W.add_mem (hstab c' hc' _ (hβ' v)) (W.smul_mem β (hβ'' v)))
      have hqq : ∀ v, (q : V →ₗ[k] V) (((q⁻¹ : LinearMap.GeneralLinearGroup k V) :
          V →ₗ[k] V) v) = v := fun v => by
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply]
      rw [commutatorElement_def, hcomm']
      refine (hK _).2 ⟨fun w hw => ?_, fun v => ?_⟩
      · rw [Units.val_mul, Module.End.mul_apply, hpq _ (hstab _ hqC w hw), hqq]
      · rw [Units.val_mul, Module.End.mul_apply]
        have := hpq' (((q⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) v)
        rwa [hqq] at this
    intro x hx y hy
    exact hKcomm x (hCK hx) y (hCK hy)
  have habel : ∀ x ∈ ⁅C, C⁆, ∀ y ∈ ⁅C, C⁆, x * y = y * x := by
    by_cases hirr : ∀ U : Submodule k V, Inv U → U = ⊥ ∨ U = ⊤
    ·
      have hscal : ∀ c ∈ C, ∃ α : k, ∀ v, (c : V →ₗ[k] V) v = α • v := by
        intro c hc
        obtain ⟨α, hα⟩ := exists_scalar_of_irreducible_segment hPperf bot_le
          (by rw [finrank_bot, finrank_top, hV]; omega) (fun g hg b _ => Submodule.mem_top)
          hInvbot (fun D _ _ hD => hirr D hD) (fun _ _ => Submodule.mem_top)
          (fun a ha => by rw [Submodule.mem_bot] at ha ⊢; rw [ha, map_zero])
          (fun g hg v => hCP c hc g hg v)
        exact ⟨α, fun v => by
          have := hα v Submodule.mem_top
          rwa [Submodule.mem_bot, sub_eq_zero] at this⟩
      intro x hx y hy
      have hxC := Subgroup.commutator_le_self (H := C) hx
      have hyC := Subgroup.commutator_le_self (H := C) hy
      obtain ⟨α, hα⟩ := hscal x hxC
      obtain ⟨β, hβ⟩ := hscal y hyC
      refine Units.ext (LinearMap.ext fun v => ?_)
      simp only [Units.val_mul, Module.End.mul_apply, hα, hβ, smul_smul, mul_comm]
    · push Not at hirr
      obtain ⟨U, hU, hU0, hUtop⟩ := hirr
      have hUpos : 0 < finrank k U :=
        Nat.pos_of_ne_zero fun h => hU0 (Submodule.finrank_eq_zero.1 h)
      have hUlt : finrank k U < 3 := by
        rw [← hV]
        exact Submodule.finrank_lt hUtop
      have hmapInv : ∀ c ∈ C, ∀ D : Submodule k V, Inv D →
          Inv (D.map (c : V →ₗ[k] V)) := by
        intro c hc D hD g hg u hu
        obtain ⟨d, hd, rfl⟩ := Submodule.mem_map.1 hu
        rw [← hCP c hc g hg d]
        exact Submodule.mem_map_of_mem (hD g hg d hd)
      have hmapdim : ∀ c ∈ C, ∀ D : Submodule k V,
          finrank k (D.map (c : V →ₗ[k] V)) = finrank k D := by
        intro c _ D
        exact LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv k V c) D
      rcases (by omega : finrank k U = 1 ∨ finrank k U = 2) with h1 | h2
      ·
        have huniq : ∀ L : Submodule k V, Inv L → finrank k L = 1 → L = U := by
          intro L hL hLd
          by_contra hne
          have hinf : finrank k ↥(U ⊓ L) = 0 := by
            have := Submodule.finrank_mono (inf_le_left : U ⊓ L ≤ U)
            rw [h1] at this
            by_contra h0
            have h3 : finrank k ↥(U ⊓ L) = 1 := by omega
            have := Submodule.eq_of_le_of_finrank_eq (inf_le_left : U ⊓ L ≤ U) (by rw [h3, h1])
            have := Submodule.eq_of_le_of_finrank_eq (inf_le_right : U ⊓ L ≤ L) (by rw [h3, hLd])
            exact hne (by rw [← ‹U ⊓ L = L›, ‹U ⊓ L = U›])
          have hsup := Submodule.finrank_sup_add_finrank_inf_eq U L
          rw [hinf, h1, hLd, add_zero] at hsup
          exact hflag U (U ⊔ L) le_sup_left hU
            (fun g hg x hx => by
              obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
              rw [map_add]
              exact Submodule.add_mem_sup (hU g hg y hy) (hL g hg z hz)) h1 hsup
        refine hmain U (fun c hc w hw => ?_) (fun c hc => ?_) (fun c hc => ?_)
        · have h := huniq _ (hmapInv c hc U hU) (by rw [hmapdim c hc, h1])
          rw [← h]
          exact Submodule.mem_map_of_mem hw
        · have hstabc : ∀ w ∈ U, (c : V →ₗ[k] V) w ∈ U := fun w hw => by
            have h := huniq _ (hmapInv c hc U hU) (by rw [hmapdim c hc, h1])
            rw [← h]
            exact Submodule.mem_map_of_mem hw
          obtain ⟨α, hα⟩ := exists_scalar_of_finrank_succ bot_le (by rw [finrank_bot, h1])
            (fun a ha => by rw [Submodule.mem_bot] at ha ⊢; rw [ha, map_zero]) hstabc
          exact ⟨α, fun w hw => by
            have := hα w hw
            rwa [Submodule.mem_bot, sub_eq_zero] at this⟩
        · have hstabc : ∀ w ∈ U, (c : V →ₗ[k] V) w ∈ U := fun w hw => by
            have h := huniq _ (hmapInv c hc U hU) (by rw [hmapdim c hc, h1])
            rw [← h]
            exact Submodule.mem_map_of_mem hw
          obtain ⟨β, hβ⟩ := exists_scalar_of_irreducible_segment hPperf le_top
            (by rw [finrank_top, hV, h1]; omega) (fun _ _ _ _ => Submodule.mem_top) hU
            (fun D hUD _ hD => by
              by_cases hDU : D = U
              · exact Or.inl hDU
              · right
                have hlt : U < D := lt_of_le_of_ne hUD (Ne.symm hDU)
                have h3 := Submodule.finrank_lt_finrank_of_lt hlt
                rw [h1] at h3
                by_contra hDt
                have h5 := Submodule.finrank_lt hDt
                rw [hV] at h5
                exact hflag U D hUD hU hD h1 (by omega))
            (fun _ _ => Submodule.mem_top) hstabc (fun g hg v => hCP c hc g hg v)
          exact ⟨β, fun v => hβ v Submodule.mem_top⟩
      ·
        have huniq : ∀ L : Submodule k V, Inv L → finrank k L = 2 → L = U := by
          intro L hL hLd
          by_contra hne
          have hsup := Submodule.finrank_sup_add_finrank_inf_eq U L
          have hsle := Submodule.finrank_le (U ⊔ L)
          rw [h2, hLd] at hsup
          rw [hV] at hsle
          have hinf1 : finrank k ↥(U ⊓ L) ≠ 2 := by
            intro h3
            have e1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : U ⊓ L ≤ U) (by rw [h3, h2])
            have e2 :=
              Submodule.eq_of_le_of_finrank_eq (inf_le_right : U ⊓ L ≤ L) (by rw [h3, hLd])
            exact hne (by rw [← e2, e1])
          have hinfle := Submodule.finrank_mono (inf_le_left : U ⊓ L ≤ U)
          rw [h2] at hinfle
          exact hflag (U ⊓ L) U inf_le_left
            (fun g hg x hx => ⟨hU g hg x hx.1, hL g hg x hx.2⟩) hU (by omega) h2
        have hstabc : ∀ c ∈ C, ∀ w ∈ U, (c : V →ₗ[k] V) w ∈ U := fun c hc w hw => by
          have h := huniq _ (hmapInv c hc U hU) (by rw [hmapdim c hc, h2])
          rw [← h]
          exact Submodule.mem_map_of_mem hw
        refine hmain U hstabc (fun c hc => ?_) (fun c hc => ?_)
        · obtain ⟨α, hα⟩ := exists_scalar_of_irreducible_segment hPperf bot_le
            (by rw [finrank_bot, h2]; omega) hU hInvbot
            (fun D _ hDU hD => by
              by_cases hD0 : D = ⊥
              · exact Or.inl hD0
              · right
                by_contra hDU'
                have h3 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hDU hDU')
                have h4 : 0 < finrank k D :=
                  Nat.pos_of_ne_zero fun h => hD0 (Submodule.finrank_eq_zero.1 h)
                rw [h2] at h3
                exact hflag D U hDU hD hU (by omega) h2)
            (hstabc c hc) (fun a ha => by rw [Submodule.mem_bot] at ha ⊢; rw [ha, map_zero])
            (fun g hg v => hCP c hc g hg v)
          exact ⟨α, fun w hw => by
            have := hα w hw
            rwa [Submodule.mem_bot, sub_eq_zero] at this⟩
        · obtain ⟨β, hβ⟩ := exists_scalar_of_finrank_succ le_top (by rw [finrank_top, hV, h2])
            (hstabc c hc) (fun _ _ => Submodule.mem_top)
          exact ⟨β, fun v => hβ v Submodule.mem_top⟩
  refine ⟨habel, ?_⟩
  have hcommC : ∀ a b : commutator C, a * b = b * a := by
    intro a b
    have hmap : ∀ z : commutator C, ((z : C) : LinearMap.GeneralLinearGroup k V) ∈ ⁅C, C⁆ := by
      intro z
      have h1 : (commutator C).map C.subtype = ⁅C, C⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      rw [← h1]
      exact Subgroup.mem_map_of_mem _ z.2
    exact Subtype.ext (Subtype.ext (habel _ (hmap a) _ (hmap b)))
  have : Group.IsSolvable (commutator C) := Group.isSolvable_of_comm hcommC
  exact Group.isSolvable_of_ker_le_range (commutator C).subtype (Abelianization.of (G := C))
    (by rw [Abelianization.ker_of, Subgroup.range_subtype])

end CFSG.LinearAlgebra
