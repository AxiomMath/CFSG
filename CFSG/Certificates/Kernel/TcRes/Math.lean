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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.KC.TcRes

section Reduced

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def IsLead (v : Fin n → F) (j : Fin n) : Prop :=
  v j = 1 ∧ ∀ i, j < i → v i = 0

@[expose] def IsReduced (u1 u2 : Fin n → F) : Prop :=
  ∃ i j : Fin n, j < i ∧ IsLead u1 i ∧ IsLead u2 j ∧ u1 j = 0

theorem IsReduced.indep {u1 u2 : Fin n → F} (h : IsReduced u1 u2) {s t : F}
    (hst : s • u1 + t • u2 = 0) : s = 0 ∧ t = 0 := by
  obtain ⟨i, j, hji, ⟨h1i, h1⟩, ⟨h2j, h2⟩, h1j⟩ := h
  have hi := congrFun hst i
  have hj := congrFun hst j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi hj
  rw [h1i, h2 i hji] at hi
  rw [h1j, h2j] at hj
  have hs : s = 0 := by simpa using hi
  exact ⟨hs, by simpa using hj⟩

theorem IsReduced.span_eq {P : Submodule F (Fin n → F)} (hP : Module.finrank F P = 2)
    {u1 u2 : Fin n → F} (h : IsReduced u1 u2) (h1 : u1 ∈ P) (h2 : u2 ∈ P) :
    Submodule.span F (Set.range ![u1, u2]) = P := by
  have hli : LinearIndependent F ![u1, u2] :=
    LinearIndependent.pair_iff.2 fun s t hst => h.indep hst
  have hle : Submodule.span F (Set.range ![u1, u2]) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · simpa using h1
    · simpa using h2
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hli, hP]
  simp

theorem IsReduced.mem_iff {P : Submodule F (Fin n → F)} (hP : Module.finrank F P = 2)
    {u1 u2 : Fin n → F} (h : IsReduced u1 u2) (h1 : u1 ∈ P) (h2 : u2 ∈ P) (v : Fin n → F) :
    v ∈ P ↔ ∃ s t : F, v = s • u1 + t • u2 := by
  rw [← h.span_eq hP h1 h2, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c 0, c 1, by simp [Fin.sum_univ_two]⟩
  · rintro ⟨s, t, rfl⟩
    exact ⟨![s, t], by simp [Fin.sum_univ_two]⟩

theorem exists_top_of_ne {Q : Set (Fin n → F)} {x : Fin n → F} (hx : x ∈ Q) (hx0 : x ≠ 0) :
    ∃ i : Fin n, ∃ v ∈ Q, v i ≠ 0 ∧ ∀ w ∈ Q, ∀ k, i < k → w k = 0 := by
  classical
  obtain ⟨k0, hk0⟩ := Function.ne_iff.1 hx0
  let T := Finset.univ.filter fun k : Fin n => ∃ v ∈ Q, v k ≠ 0
  have hT : T.Nonempty := ⟨k0, Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, hk0⟩⟩
  obtain ⟨v, hvQ, hv⟩ := (Finset.mem_filter.1 (T.max'_mem hT)).2
  refine ⟨T.max' hT, v, hvQ, hv, fun w hw k hk => ?_⟩
  by_contra hne
  have hkT : k ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, w, hw, hne⟩
  exact absurd (T.le_max' k hkT) (not_le.2 hk)

theorem exists_reduced {P : Submodule F (Fin n → F)} (hP : Module.finrank F P = 2) :
    ∃ u1 ∈ P, ∃ u2 ∈ P, IsReduced u1 u2 := by
  classical
  have hne : P ≠ ⊥ := by
    rintro rfl
    simp at hP
  obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).1 hne
  obtain ⟨i, v, hvP, hvi, htop⟩ := exists_top_of_ne (Q := (P : Set (Fin n → F))) hxP hx0
  set a : Fin n → F := (v i)⁻¹ • v with ha
  have haP : a ∈ P := P.smul_mem _ hvP
  have hai : a i = 1 := by
    simp only [ha, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hvi
  have hatop : ∀ k, i < k → a k = 0 := by
    intro k hk
    simp only [ha, Pi.smul_apply, smul_eq_mul, htop v hvP k hk, mul_zero]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at hai
    exact zero_ne_one hai
  have hnot : ¬ P ≤ F ∙ a := by
    intro hle
    have hmono := Submodule.finrank_mono hle
    rw [hP, finrank_span_singleton ha0] at hmono
    omega
  obtain ⟨b, hbP, hba⟩ := SetLike.not_le_iff_exists.1 hnot
  set b' : Fin n → F := b - b i • a with hb'
  have hb'P : b' ∈ P := P.sub_mem hbP (P.smul_mem _ haP)
  have hb'i : b' i = 0 := by
    simp only [hb', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hai, mul_one, sub_self]
  have hb'top : ∀ k, i < k → b' k = 0 := by
    intro k hk
    simp only [hb', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, htop b hbP k hk, hatop k hk,
      mul_zero, sub_self]
  have hb'0 : b' ≠ 0 := by
    intro h0
    apply hba
    have hb : b = b i • a := sub_eq_zero.1 h0
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  obtain ⟨j, w, hw, hwj, htopj⟩ := exists_top_of_ne (Q := ({b'} : Set (Fin n → F)))
    (Set.mem_singleton b') hb'0
  rw [Set.mem_singleton_iff.1 hw] at hwj
  have htopj' : ∀ k, j < k → b' k = 0 := fun k hk => htopj b' (Set.mem_singleton b') k hk
  have hji : j < i := by
    rcases lt_or_ge j i with h | h
    · exact h
    · exfalso
      rcases h.lt_or_eq with h' | h'
      · exact hwj (hb'top j h')
      · rw [← h'] at hwj
        exact hwj hb'i
  have e2 : (b' j)⁻¹ * b' j = 1 := inv_mul_cancel₀ hwj
  refine ⟨a - a j • ((b' j)⁻¹ • b'), P.sub_mem haP (P.smul_mem _ (P.smul_mem _ hb'P)),
    (b' j)⁻¹ • b', P.smul_mem _ hb'P, i, j, hji, ⟨?_, fun k hk => ?_⟩, ⟨?_, fun k hk => ?_⟩, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hai, hb'i, mul_zero, sub_zero]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hatop k hk,
      htopj' k (hji.trans hk), mul_zero, sub_zero]
  · simp only [Pi.smul_apply, smul_eq_mul, e2]
  · simp only [Pi.smul_apply, smul_eq_mul, htopj' k hk, mul_zero]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e2, mul_one, sub_self]

end Reduced

section Minor

open Matrix

variable {F : Type*} [Field F] {n m k d : ℕ}

theorem linearIndependent_of_pivots (b : Fin d → Fin n → F) (pv : Fin d → Fin n)
    (hpv : ∀ i k, b i (pv k) = if i = k then 1 else 0) : LinearIndependent F b := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h := congrFun hc (pv k)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpv, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at h
  exact h

theorem le_finrank_range_vecMul (A : Matrix (Fin n) (Fin m) F) (ma : Fin k → Fin n)
    (jb : Fin k → Fin m) (B : Matrix (Fin k) (Fin k) F) (hB : A.submatrix ma jb * B = 1) :
    k ≤ Module.finrank F (LinearMap.range (Matrix.vecMulLinear A)) := by
  classical
  let g : (Fin m → F) →ₗ[F] (Fin k → F) := LinearMap.funLeft F F jb
  let E : Matrix (Fin k) (Fin n) F := Matrix.of fun a r => if ma a = r then 1 else 0
  have hBM : B * A.submatrix ma jb = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hB
  have hsurj : Function.Surjective (g ∘ₗ Matrix.vecMulLinear A) := by
    intro y
    refine ⟨(y ᵥ* B) ᵥ* E, ?_⟩
    ext b
    simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.coe_vecMulLinear, g,
      LinearMap.funLeft_apply]
    rw [Matrix.vecMul_vecMul]
    have hEA : (E * A) = A.submatrix ma id := by
      ext a c
      simp [E, Matrix.mul_apply]
    rw [hEA]
    have h2 : (y ᵥ* B ᵥ* A.submatrix ma id) (jb b) = (y ᵥ* B ᵥ* A.submatrix ma jb) b := by
      simp [Matrix.vecMul, dotProduct]
    rw [h2, Matrix.vecMul_vecMul, hBM, Matrix.vecMul_one]
  have hrange : LinearMap.range (g ∘ₗ Matrix.vecMulLinear A) = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hk : Module.finrank F (LinearMap.range (g ∘ₗ Matrix.vecMulLinear A)) = k := by
    rw [hrange, finrank_top, Module.finrank_fin_fun]
  rw [LinearMap.range_comp] at hk
  rw [← hk]
  exact Submodule.finrank_map_le g _

theorem ker_vecMul_eq_span (A : Matrix (Fin n) (Fin m) F) (ma : Fin k → Fin n)
    (jb : Fin k → Fin m) (B : Matrix (Fin k) (Fin k) F) (hB : A.submatrix ma jb * B = 1)
    (b : Fin d → Fin n → F) (hb : LinearIndependent F b) (hbK : ∀ i, b i ᵥ* A = 0)
    (hdk : d + k = n) :
    LinearMap.ker (Matrix.vecMulLinear A) = Submodule.span F (Set.range b) := by
  have hle : Submodule.span F (Set.range b) ≤ LinearMap.ker (Matrix.vecMulLinear A) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hbK i
  have hrk := le_finrank_range_vecMul A ma jb B hB
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.vecMulLinear A)
  rw [Module.finrank_fin_fun] at hrn
  have hspan : Module.finrank F (Submodule.span F (Set.range b)) = d := by
    rw [finrank_span_eq_card hb]
    simp
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  omega

theorem mem_span_of_vecMul_eq_zero (A : Matrix (Fin n) (Fin m) F) (ma : Fin k → Fin n)
    (jb : Fin k → Fin m) (B : Matrix (Fin k) (Fin k) F) (hB : A.submatrix ma jb * B = 1)
    (b : Fin d → Fin n → F) (hb : LinearIndependent F b) (hbK : ∀ i, b i ᵥ* A = 0)
    (hdk : d + k = n) {u : Fin n → F} (hu : u ᵥ* A = 0) :
    ∃ c : Fin d → F, u = ∑ i, c i • b i := by
  have hmem : u ∈ LinearMap.ker (Matrix.vecMulLinear A) := hu
  rw [ker_vecMul_eq_span A ma jb B hB b hb hbK hdk, Submodule.mem_span_range_iff_exists_fun]
    at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

end Minor

section Search

theorem mem_of_chain {nd : ℕ → List ℕ} {tot L β : ℕ} {ok : List ℕ → ℕ → Prop}
    (h0 : 0 < tot ∧ nd 0 = [β])
    (hch : ∀ j < tot, (nd j).length < L → ∀ x, ok (nd j) x → ∃ c < tot, nd c = nd j ++ [x])
    (t : List ℕ) (ht0 : t.head? = some β) (htL : t.length ≤ L)
    (hok : ∀ k (hk : k < t.length), 1 ≤ k → ok (t.take k) t[k]) :
    ∃ j < tot, nd j = t := by
  have key : ∀ k, 1 ≤ k → k ≤ t.length → ∃ j < tot, nd j = t.take k := by
    intro k hk1 hkl
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · refine ⟨0, h0.1, ?_⟩
        rw [h0.2]
        cases t with
        | nil => simp at ht0
        | cons a t' =>
          simp only [List.head?_cons, Option.some.injEq] at ht0
          simp [ht0]
      · obtain ⟨j, hj, hjeq⟩ := ih hkpos (by omega)
        have hklt : k < t.length := by omega
        have hlen : (nd j).length < L := by
          rw [hjeq, List.length_take]
          omega
        obtain ⟨c, hc, hceq⟩ := hch j hj hlen t[k] (by rw [hjeq]; exact hok k hklt hkpos)
        refine ⟨c, hc, ?_⟩
        rw [hceq, hjeq, List.take_succ, List.getElem?_eq_getElem hklt]
        rfl
  have hpos : 1 ≤ t.length := by
    cases t with
    | nil => simp at ht0
    | cons a t' => simp
  obtain ⟨j, hj, hjeq⟩ := key t.length hpos le_rfl
  exact ⟨j, hj, by rw [hjeq, List.take_length]⟩

end Search

theorem surjective_of_injective_card {G : Type*} [Finite G] {N : ℕ} (hN : Nat.card G = N)
    (f : Fin N → G) (hf : Function.Injective f) : Function.Surjective f := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hN
  exact ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [hN]⟩).2

end CFSG.KC.TcRes

end
