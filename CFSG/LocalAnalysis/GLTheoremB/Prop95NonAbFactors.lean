module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb

open Subgroup

variable {Q : Type*} [Group Q]

abbrev cj (q : Q) (T : Subgroup Q) : Subgroup Q := T.map (MulAut.conj q).toMonoidHom

theorem mem_cj {q x : Q} {T : Subgroup Q} : x ∈ cj q T ↔ q⁻¹ * x * q ∈ T := by
  unfold cj
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem cj_mul (q q' : Q) (T : Subgroup Q) : cj (q * q') T = cj q (cj q' T) := by
  ext x
  simp only [mem_cj, mul_inv_rev]
  simp [mul_assoc]

theorem cj_one (T : Subgroup Q) : cj 1 T = T := by
  ext x; simp [mem_cj]

theorem mem_normalizer_of_cj_eq {q : Q} {T : Subgroup Q} (h : cj q T = T) :
    q ∈ Subgroup.normalizer (T : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : q * x * q⁻¹ ∈ cj q T := mem_cj.2 (by simpa [mul_assoc] using hx)
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    simpa [mem_cj, mul_assoc] using mem_cj.1 hx

theorem cj_eq_of_mem_normalizer {q : Q} {T : Subgroup Q} (h : q ∈ Subgroup.normalizer (T : Set Q)) :
    cj q T = T := by
  ext x
  rw [mem_cj]
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h) x)
  simpa [mul_assoc] using this.symm

theorem commute_of_inf_eq_bot {N A B : Subgroup Q} (hA : A ≤ N) (hB : B ≤ N)
    (hAn : N ≤ Subgroup.normalizer (A : Set Q)) (hBn : N ≤ Subgroup.normalizer (B : Set Q))
    (h : A ⊓ B = ⊥) {x y : Q} (hx : x ∈ A) (hy : y ∈ B) : x * y = y * x := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ B := by
    have := (Subgroup.mem_normalizer_iff.1 (hBn (hA hx)) y).1 hy
    exact B.mul_mem this (B.inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (hAn (hB hy)) x⁻¹).1 (A.inv_mem hx)
    have h3 : y * x⁻¹ * y⁻¹ ∈ A := by simpa using this
    simpa [mul_assoc] using A.mul_mem hx h3
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ A ⊓ B := ⟨h2, h1⟩
  rw [h, Subgroup.mem_bot] at h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem eq_bot_or_eq_of_simple {N T A : Subgroup Q} [IsSimpleGroup T] (hAT : A ≤ T) (hTN : T ≤ N)
    (hA : N ≤ Subgroup.normalizer (A : Set Q)) : A = ⊥ ∨ A = T := by
  have hnorm : (A.subgroupOf T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hA (hTN g.2)) (n : Q)).1 hn
    simpa using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf T) with h | h
  · left
    refine eq_bot_iff.2 fun a ha => ?_
    have : (⟨a, hAT ha⟩ : T) ∈ A.subgroupOf T := ha
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · right
    refine le_antisymm hAT fun t ht => ?_
    have : (⟨t, ht⟩ : T) ∈ A.subgroupOf T := by rw [h]; trivial
    exact this

structure IsFactorization {ι : Type*} (N : Subgroup Q) (S : ι → Subgroup Q) : Prop where
  le : ∀ i, S i ≤ N
  simple : ∀ i, IsSimpleGroup (S i)
  nonab : ∀ i, ∃ a b : S i, a * b ≠ b * a
  normal : ∀ i, N ≤ Subgroup.normalizer (S i : Set Q)
  indep : iSupIndep S
  iSup_eq : ⨆ i, S i = N
  perm : ∀ (q : Q) (i : ι), ∃ j, S j = cj q (S i)

section Fact

variable {ι : Type*} {N : Subgroup Q} {S : ι → Subgroup Q}

theorem IsFactorization.ne_bot (hF : IsFactorization N S) (i : ι) : S i ≠ ⊥ := by
  have := hF.simple i
  exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance

theorem IsFactorization.injective (hF : IsFactorization N S) : Function.Injective S :=
  hF.indep.injective hF.ne_bot

theorem IsFactorization.commute (hF : IsFactorization N S) {i j : ι} (hij : i ≠ j) {x y : Q}
    (hx : x ∈ S i) (hy : y ∈ S j) : x * y = y * x := by
  refine commute_of_inf_eq_bot (hF.le i) (hF.le j) (hF.normal i) (hF.normal j) ?_ hx hy
  exact disjoint_iff.1 (hF.indep.pairwiseDisjoint hij)

theorem IsFactorization.commute_biSup (hF : IsFactorization N S) {A B : Set ι} (hAB : Disjoint A B)
    {x y : Q} (hx : x ∈ ⨆ j ∈ A, S j) (hy : y ∈ ⨆ j ∈ B, S j) : x * y = y * x := by
  have h1 : ∀ j ∈ A, S j ≤ Subgroup.centralizer ((⨆ j ∈ B, S j : Subgroup Q) : Set Q) := by
    intro j hj
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun l hl => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hjl : j ≠ l := by
      rintro rfl
      exact Set.disjoint_left.1 hAB hj hl
    exact hF.commute hjl hx hy
  have h2 : (⨆ j ∈ A, S j) ≤ Subgroup.centralizer ((⨆ j ∈ B, S j : Subgroup Q) : Set Q) :=
    iSup₂_le h1
  have := h2 hx
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this y hy).symm

theorem IsFactorization.comm_pairwise (hF : IsFactorization N S) :
    Pairwise fun i j => ∀ x y : Q, x ∈ S i → y ∈ S j → Commute x y :=
  fun _ _ hij _ _ hx hy => hF.commute hij hx hy

noncomputable def IsFactorization.prod [Fintype ι] (hF : IsFactorization N S) :
    (∀ i, S i) →* Q :=
  Subgroup.noncommPiCoprod hF.comm_pairwise

theorem IsFactorization.prod_injective [Fintype ι] (hF : IsFactorization N S) :
    Function.Injective hF.prod :=
  Subgroup.injective_noncommPiCoprod_of_iSupIndep hF.indep

theorem IsFactorization.prod_mulSingle [Fintype ι] [DecidableEq ι] (hF : IsFactorization N S)
    (i : ι) (y : S i) : hF.prod (Pi.mulSingle i y) = (y : Q) :=
  Subgroup.noncommPiCoprod_mulSingle i y

theorem IsFactorization.disjoint_biSup_biSup [Finite ι] (hF : IsFactorization N S) {A B : Set ι}
    (hAB : Disjoint A B) : Disjoint (⨆ j ∈ A, S j) (⨆ j ∈ B, S j) := by
  classical
  have := Fintype.ofFinite ι
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  let P : Set ι → Subgroup (∀ i, S i) := fun A =>
    { carrier := {f | ∀ j, j ∉ A → f j = 1}
      one_mem' := fun j _ => rfl
      mul_mem' := fun {f g} hf hg j hj => by simp [hf j hj, hg j hj]
      inv_mem' := fun {f} hf j hj => by simp [hf j hj] }
  have key : ∀ A : Set ι, (⨆ j ∈ A, S j) ≤ (P A).map hF.prod := by
    intro A
    refine iSup₂_le fun j hj y hy => ?_
    refine ⟨Pi.mulSingle j ⟨y, hy⟩, fun l hl => ?_, ?_⟩
    · have : l ≠ j := fun h => hl (h ▸ hj)
      simp [Pi.mulSingle_eq_of_ne this]
    · exact hF.prod_mulSingle j ⟨y, hy⟩
  obtain ⟨f, hf, hfx⟩ := key A hxA
  obtain ⟨g, hg, hgx⟩ := key B hxB
  have hfg : f = g := hF.prod_injective (hfx.trans hgx.symm)
  have h1 : f = 1 := by
    funext j
    by_cases hj : j ∈ A
    · have : j ∉ B := Set.disjoint_left.1 hAB hj
      rw [hfg]; exact hg j this
    · exact hf j hj
  rw [← hfx, h1, map_one]

@[expose] noncomputable def IsFactorization.act' (hF : IsFactorization N S) (q : Q) (i : ι) : ι :=
  Classical.choose (hF.perm q i)

theorem IsFactorization.act'_spec (hF : IsFactorization N S) (q : Q) (i : ι) :
    S (hF.act' q i) = cj q (S i) :=
  Classical.choose_spec (hF.perm q i)

theorem IsFactorization.act'_mul (hF : IsFactorization N S) (q q' : Q) (i : ι) :
    hF.act' (q * q') i = hF.act' q (hF.act' q' i) :=
  hF.injective (by rw [hF.act'_spec, hF.act'_spec, hF.act'_spec, cj_mul])

theorem IsFactorization.act'_one (hF : IsFactorization N S) (i : ι) : hF.act' 1 i = i :=
  hF.injective (by rw [hF.act'_spec, cj_one])

@[expose] noncomputable def IsFactorization.actHom (hF : IsFactorization N S) : Q →* Equiv.Perm ι where
  toFun q :=
    { toFun := hF.act' q
      invFun := hF.act' q⁻¹
      left_inv := fun i => by rw [← hF.act'_mul, inv_mul_cancel, hF.act'_one]
      right_inv := fun i => by rw [← hF.act'_mul, mul_inv_cancel, hF.act'_one] }
  map_one' := Equiv.ext fun i => hF.act'_one i
  map_mul' q q' := Equiv.ext fun i => hF.act'_mul q q' i

theorem IsFactorization.S_actHom (hF : IsFactorization N S) (q : Q) (i : ι) :
    S (hF.actHom q i) = cj q (S i) :=
  hF.act'_spec q i

theorem IsFactorization.S_actHom_pow (hF : IsFactorization N S) (q : Q) (k : ℕ) (i : ι) :
    S ((hF.actHom q ^ k) i) = cj (q ^ k) (S i) := by
  rw [← map_pow, hF.S_actHom]

theorem IsFactorization.actHom_eq_iff (hF : IsFactorization N S) {q : Q} {i : ι} :
    hF.actHom q i = i ↔ q ∈ Subgroup.normalizer (S i : Set Q) :=
  ⟨fun h => mem_normalizer_of_cj_eq (by rw [← hF.S_actHom, h]),
    fun h => hF.injective (by rw [hF.S_actHom, cj_eq_of_mem_normalizer h])⟩

theorem perm_pow_apply_of_comm {σ τ : Equiv.Perm ι} (hc : σ * τ = τ * σ) {i : ι} {m : ℕ}
    (h : τ i = (σ ^ m) i) (k : ℕ) : (τ ^ k) i = (σ ^ (m * k)) i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc' : ∀ n : ℕ, (σ ^ n) * τ = τ * (σ ^ n) := fun n => (Commute.pow_left (hc : Commute σ τ) n).eq
    calc (τ ^ (k + 1)) i = τ ((τ ^ k) i) := by rw [pow_succ', Equiv.Perm.mul_apply]
      _ = τ ((σ ^ (m * k)) i) := by rw [ih]
      _ = (σ ^ (m * k)) (τ i) := by
        have := congrArg (fun f : Equiv.Perm ι => f i) (hc' (m * k))
        simpa [Equiv.Perm.mul_apply] using this.symm
      _ = (σ ^ (m * (k + 1))) i := by
        rw [h, ← Equiv.Perm.mul_apply, ← pow_add, mul_add, mul_one]

theorem perm_pow_fix {σ : Equiv.Perm ι} {i : ι} {n : ℕ} (h : (σ ^ n) i = i) (u : ℕ) :
    ((σ ^ n) ^ u) i = i := by
  have : σ ^ n ∈ MulAction.stabilizer (Equiv.Perm ι) i := by
    rw [MulAction.mem_stabilizer_iff]; exact h
  have := (MulAction.stabilizer (Equiv.Perm ι) i).pow_mem this u
  rwa [MulAction.mem_stabilizer_iff] at this

theorem perm_apply_eq_of_orbit {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ τ : Equiv.Perm ι}
    (hσ : σ ^ p = 1) {e : ℕ} (hτ : τ ^ (2 ^ e) = 1) (hc : σ * τ = τ * σ) {i : ι}
    (h : ∃ m : ℕ, τ i = (σ ^ m) i) : τ i = i := by
  obtain ⟨m, hm⟩ := h
  have h1 := perm_pow_apply_of_comm hc hm (2 ^ e)
  rw [hτ] at h1
  simp only [Equiv.Perm.coe_one, id_eq] at h1
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hσ) with h1' | hp'
  · have : σ = 1 := orderOf_eq_one_iff.1 h1'
    rw [hm, this, one_pow]
    rfl
  · by_cases hpm : p ∣ m
    · obtain ⟨c, rfl⟩ := hpm
      rw [hm, pow_mul, hσ, one_pow]
      rfl
    · have hcop : Nat.Coprime (m * 2 ^ e) (orderOf σ) := by
        rw [hp']
        refine Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm ?_
        refine Nat.Coprime.pow_left _ ?_
        exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
          hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)).symm
      obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
      have h2 : σ i = i := by
        have := perm_pow_fix h1.symm u
        rwa [hu] at this
      have h3 : (σ ^ m) i = i := by
        have := perm_pow_fix (σ := σ) (n := 1) (by simpa using h2) m
        simpa using this
      rw [hm, h3]

end Fact

theorem mem_normalizer_inf' {g : Q} {A B : Subgroup Q} (hA : g ∈ Subgroup.normalizer (A : Set Q))
    (hB : g ∈ Subgroup.normalizer (B : Set Q)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 := Subgroup.mem_normalizer_iff.1 hA z
  have h2 := Subgroup.mem_normalizer_iff.1 hB z
  simp only [Subgroup.mem_inf]
  rw [h1, h2]

theorem exists_factorization [Finite Q] {N : Subgroup Q} (hNn : N.Normal) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup Q, M.Normal → M ≤ N → M = ⊥ ∨ M = N)
    (hnab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) :
    ∃ (r : ℕ) (S : Fin r → Subgroup Q), IsFactorization N S := by
  classical
  obtain ⟨r, S, hr, hSN, hsimple, hconj, hnormN, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN1 hmin
  have hnorm : ∀ i, N ≤ Subgroup.normalizer (S i : Set Q) := fun i =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hSN i)).1 (hnormN i)
  have hmul : ∀ (i : Fin r) (a : S i), ((e (Pi.mulSingle i a) : N) : Q) = a := fun i a => by
    simpa using he i (Pi.mulSingle i a) (fun k hk => Pi.mulSingle_eq_of_ne hk _)
  have hindep : iSupIndep S := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hxi hxrest
    let P : Subgroup ((j : Fin r) → S j) := (Pi.evalMonoidHom (fun j => (S j : Type _)) i).ker
    let E : Subgroup Q := (P.map e.toMonoidHom).map N.subtype
    have hE : ∀ j, j ≠ i → S j ≤ E := by
      intro j hj y hy
      refine ⟨⟨y, hSN j hy⟩, ⟨Pi.mulSingle j ⟨y, hy⟩, ?_, ?_⟩, rfl⟩
      · simp [P, Pi.mulSingle_eq_of_ne hj.symm]
      · exact Subtype.ext (hmul j ⟨y, hy⟩)
    have hrest : (⨆ j, ⨆ (_ : j ≠ i), S j) ≤ E := iSup₂_le hE
    obtain ⟨_, ⟨f, hf, rfl⟩, hfx⟩ := hrest hxrest
    have h1 : e (Pi.mulSingle i ⟨x, hxi⟩) = ⟨x, hSN i hxi⟩ := Subtype.ext (hmul i ⟨x, hxi⟩)
    have h2 : e f = ⟨x, hSN i hxi⟩ := Subtype.ext hfx
    have h3 : f = Pi.mulSingle i ⟨x, hxi⟩ := e.injective (h2.trans h1.symm)
    have h4 : f i = 1 := hf
    rw [h3] at h4
    simpa using congrArg Subtype.val h4
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x := fun i j hij x hx y hy =>
    commute_of_inf_eq_bot (hSN i) (hSN j) (hnorm i) (hnorm j)
      (disjoint_iff.1 (hindep.pairwiseDisjoint hij)) hx hy
  have hsup : ⨆ i, S i = N := by
    let ψ : (∀ i, S i) →* Q := Subgroup.noncommPiCoprod (H := S)
      (fun i j hij x y hx hy => hcomm i j hij x hx y hy)
    have hψ : ψ = N.subtype.comp e.toMonoidHom := by
      refine MonoidHom.pi_ext fun i a => ?_
      rw [show ψ (Pi.mulSingle i a) = (a : Q) from Subgroup.noncommPiCoprod_mulSingle i a]
      exact (hmul i a).symm
    have hrange : ψ.range = ⨆ i, S i := Subgroup.noncommPiCoprod_range
    refine le_antisymm (iSup_le hSN) fun x hx => ?_
    rw [← hrange]
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    rw [hψ]
    simp
  have hZ : ∀ z ∈ N, (∀ n ∈ N, z * n = n * z) → z = 1 := by
    intro z hz hzc
    let Z : Subgroup Q := N ⊓ Subgroup.centralizer (N : Set Q)
    have hZn : Z.Normal := by
      refine ⟨fun x hx g => Subgroup.mem_inf.2 ⟨hNn.conj_mem x (Subgroup.mem_inf.1 hx).1 g, ?_⟩⟩
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hn' : g⁻¹ * n * g ∈ N := by
        have := hNn.conj_mem n hn g⁻¹
        simpa using this
      have h1 := (Subgroup.mem_inf.1 hx).2
      rw [Subgroup.mem_centralizer_iff] at h1
      have h2 := h1 _ hn'
      calc n * (g * x * g⁻¹) = g * ((g⁻¹ * n * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * n * g)) * g⁻¹ := by rw [h2]
        _ = g * x * g⁻¹ * n := by group
    rcases hmin Z hZn inf_le_left with h | h
    · have : z ∈ Z := Subgroup.mem_inf.2 ⟨hz, by
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact (hzc n hn).symm⟩
      rw [h] at this
      simpa using this
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hnab
      have : a ∈ Z := by rw [h]; exact ha
      have := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 this).2) b hb
      exact hab this.symm
  have hperm : ∀ (q : Q) (i : Fin r), ∃ j, S j = cj q (S i) := by
    intro q i
    set T : Subgroup Q := cj q (S i) with hT
    have hTN : T ≤ N := by
      intro x hx
      rw [hT, mem_cj] at hx
      have := hNn.conj_mem _ (hSN i hx) q
      simpa [mul_assoc] using this
    have hTn : N ≤ Subgroup.normalizer (T : Set Q) := by
      intro n hn
      refine mem_normalizer_of_cj_eq ?_
      have h1 : q⁻¹ * n * q ∈ Subgroup.normalizer (S i : Set Q) := by
        refine hnorm i ?_
        have := hNn.conj_mem n hn q⁻¹
        simpa using this
      calc cj n T = cj (n * q) (S i) := by rw [hT, cj_mul]
        _ = cj (q * (q⁻¹ * n * q)) (S i) := by congr 1; group
        _ = cj q (cj (q⁻¹ * n * q) (S i)) := cj_mul _ _ _
        _ = cj q (S i) := by rw [cj_eq_of_mem_normalizer h1]
    have hTs : IsSimpleGroup T := by
      haveI := hsimple i
      exact MulEquiv.isSimpleGroup
        ((S i).equivMapOfInjective (MulAut.conj q).toMonoidHom (MulAut.conj q).injective).symm
    have hT1 : T ≠ ⊥ := by
      haveI := hTs
      exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
    have hex : ∃ j, T ⊓ S j ≠ ⊥ := by
      by_contra hno
      push Not at hno
      apply hT1
      refine eq_bot_iff.2 fun t ht => ?_
      rw [Subgroup.mem_bot]
      refine hZ t (hTN ht) fun n hn => ?_
      have hle : N ≤ Subgroup.centralizer ({t} : Set Q) := by
        rw [← hsup]
        refine iSup_le fun j y hy => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact commute_of_inf_eq_bot hTN (hSN j) hTn (hnorm j) (hno j) ht hy |>.symm
      have := hle hn
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
    obtain ⟨j, hj⟩ := hex
    have hAn : N ≤ Subgroup.normalizer ((T ⊓ S j : Subgroup Q) : Set Q) := fun n hn =>
      mem_normalizer_inf' (hTn hn) (hnorm j hn)
    haveI := hTs
    haveI := hsimple j
    refine ⟨j, ?_⟩
    rcases eq_bot_or_eq_of_simple (N := N) (T := T) (A := T ⊓ S j) inf_le_left hTN hAn with h | h
    · exact absurd h hj
    rcases eq_bot_or_eq_of_simple (N := N) (T := S j) (A := T ⊓ S j) inf_le_right (hSN j) hAn
      with h' | h'
    · exact absurd h' hj
    · rw [← h', h]
  have hnab' : ∀ i, ∃ a b : S i, a * b ≠ b * a := by
    by_contra hno
    push Not at hno
    obtain ⟨i, hi⟩ := hno
    have hcommS : ∀ j, ∀ x ∈ S j, ∀ y ∈ S j, x * y = y * x := by
      intro j x hx y hy
      obtain ⟨g, hg⟩ := hconj i j
      have hg' : S j = cj g⁻¹ (S i) := hg
      rw [hg', mem_cj] at hx hy
      have := hi ⟨_, hx⟩ ⟨_, hy⟩
      simp only [inv_inv] at this
      have h2 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h2
      calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h2]
        _ = y * x := by group
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    apply hab
    have hle1 : ∀ j, N ≤ Subgroup.centralizer (S j : Set Q) := by
      intro j
      rw [← hsup]
      refine iSup_le fun k x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      by_cases hkj : k = j
      · subst hkj
        exact (hcommS k x hx y hy).symm
      · exact (hcomm k j hkj x hx y hy).symm
    have hle : N ≤ Subgroup.centralizer (N : Set Q) := by
      rw [← hsup]
      exact iSup_le fun j => Subgroup.le_centralizer_iff.2 (by rw [hsup]; exact hle1 j)
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm
  exact ⟨r, S, ⟨hSN, hsimple, hnab', hnorm, hindep, hsup, hperm⟩⟩

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb
