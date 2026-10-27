module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open MulAction

def i1312FixSet {P X : Type} [Group P] [MulAction P X] (M : Subgroup P) : Set X :=
  {x | ∀ m ∈ M, m • x = x}

theorem i1312_index_stab {P X : Type} [Group P] [Finite P] [Finite X] [MulAction P X] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hP : IsPGroup p P) (hX : Nat.card X ≤ 8) (x : X) :
    (stabilizer P x).index = 1 ∨ (stabilizer P x).index = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : (stabilizer P x).index ∣ Nat.card P := Subgroup.index_dvd_card _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hle : (stabilizer P x).index ≤ Nat.card X := by
    rw [MulAction.index_stabilizer, ← Set.ncard_univ X]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · left
      simpa using hj
    · right
      simpa using hj
  · exfalso
    have h9 : 9 ≤ p ^ j := by
      have h2 : 9 ≤ p ^ 2 := by nlinarith [hp.two_le]
      exact h2.trans (Nat.pow_le_pow_right hp.pos hj2)
    omega

theorem i1312_dvd_eight {n : ℕ} (hn : n ∣ 8) : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  have : n ≤ 8 := Nat.le_of_dvd (by norm_num) hn
  interval_cases n <;> omega

theorem i1312_card_le_of_fix {P X : Type} [Group P] [Finite P] [Finite X] [MulAction P X] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hP : IsPGroup p P) (hcomm : ∀ x y : P, x * y = y * x)
    (hX : Nat.card X ∣ 8) (hfaith : ∀ g : P, (∀ x : X, g • x = x) → g = 1)
    (hfix : ∀ M : Subgroup P, Nat.card (i1312FixSet (X := X) M) ∣ 8) : Nat.card P ≤ p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite P
  by_contra hlt
  push_neg at hlt
  have hX8 : Nat.card X ≤ 8 := Nat.le_of_dvd (by norm_num) hX
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · rw [pow_zero] at hk; omega
      · rw [pow_one] at hk; omega
    · exact h
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : Finset X, X₀ = Finset.univ.filter fun x => stabilizer P x = ⊤ := ⟨_, rfl⟩
  obtain ⟨𝓜, h𝓜⟩ : ∃ 𝓜 : Finset (Subgroup P),
      𝓜 = (Finset.univ.filter fun x : X => stabilizer P x ≠ ⊤).image fun x => stabilizer P x :=
    ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Subgroup P → Finset X,
      ∀ M, A M = Finset.univ.filter fun x => stabilizer P x = M := ⟨_, fun M => rfl⟩
  have hmemX₀ : ∀ x : X, x ∈ X₀ ↔ stabilizer P x = ⊤ := by
    intro x; rw [hX₀, Finset.mem_filter]; simp
  have hmemA : ∀ M : Subgroup P, ∀ x : X, x ∈ A M ↔ stabilizer P x = M := by
    intro M x; rw [hA, Finset.mem_filter]; simp
  have hmem𝓜 : ∀ M : Subgroup P, M ∈ 𝓜 ↔ ∃ x : X, stabilizer P x = M ∧ stabilizer P x ≠ ⊤ := by
    intro M
    rw [h𝓜, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.mem_filter] at hx
      exact ⟨x, rfl, hx.2⟩
    · rintro ⟨x, rfl, hx⟩
      exact ⟨x, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have h𝓜idx : ∀ M ∈ 𝓜, M.index = p := by
    intro M hM
    obtain ⟨x, rfl, hx⟩ := (hmem𝓜 M).1 hM
    exact (i1312_index_stab hp hp3 hP hX8 x).resolve_left fun h1 => hx (Subgroup.index_eq_one.1 h1)
  have h𝓜ne : ∀ M ∈ 𝓜, M ≠ ⊤ := by
    intro M hM hMt
    have := h𝓜idx M hM
    rw [hMt, Subgroup.index_top] at this
    exact hp.one_lt.ne this
  have h𝓜bot : ∀ M ∈ 𝓜, M ≠ ⊥ := by
    intro M hM hMb
    have h1 := h𝓜idx M hM
    have hc := Subgroup.card_mul_index M
    rw [hMb] at h1 hc
    rw [Subgroup.card_bot, one_mul, h1, hk] at hc
    have h2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
    have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
    linarith
  have hconj : ∀ (g y : P), (MulAut.conj g).toMonoidHom y = y := by
    intro g y
    simp [MulAut.conj_apply, hcomm g y]
  have hstab_conj : ∀ (x : X) (g : P), stabilizer P (g • x) = stabilizer P x := by
    intro x g
    rw [stabilizer_smul_eq_stabilizer_map_conj]
    ext h
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hconj g y]; exact hy
    · intro hh
      exact ⟨h, hh, hconj g h⟩
  have hAp : ∀ M ∈ 𝓜, p ∣ (A M).card := by
    intro M hM
    let Y : SubMulAction P X :=
      { carrier := {x | stabilizer P x = M}
        smul_mem' := fun g x hx => by
          show stabilizer P (g • x) = M
          rw [hstab_conj]; exact hx }
    have hfixempty : MulAction.fixedPoints P Y = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have hall : ∀ g : P, g • (y : X) = (y : X) := fun g => by
        have h := congrArg Subtype.val (hy g)
        exact h
      have htop : stabilizer P (y : X) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        exact (MulAction.mem_stabilizer_iff).2 (hall g)
      have hyM : stabilizer P (y : X) = M := y.2
      exact h𝓜ne M hM (hyM.symm.trans htop)
    have hmod := IsPGroup.card_modEq_card_fixedPoints hP Y
    have h0 : Nat.card (↥(∅ : Set Y)) = 0 := by simp
    rw [hfixempty, h0] at hmod
    have hYcard : Nat.card Y = (A M).card := by
      rw [hA M, Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
    rw [hYcard] at hmod
    exact Nat.modEq_zero_iff_dvd.1 hmod
  have hfixset : ∀ M : Subgroup P, Nat.card (i1312FixSet (X := X) M) =
      (Finset.univ.filter fun x : X => ∀ m ∈ M, m • x = x).card := by
    intro M
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [i1312FixSet, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  have hfixcard : ∀ M ∈ 𝓜, Nat.card (i1312FixSet (X := X) M) = X₀.card + (A M).card := by
    intro M hM
    have hset : (Finset.univ.filter fun x : X => ∀ m ∈ M, m • x = x) = X₀ ∪ A M := by
      ext x
      rw [Finset.mem_filter, Finset.mem_union, hmemX₀, hmemA]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro hx
        by_cases htop : stabilizer P x = ⊤
        · exact Or.inl htop
        · right
          have hMle : M ≤ stabilizer P x := fun m hm => MulAction.mem_stabilizer_iff.2 (hx m hm)
          have hidx : (stabilizer P x).index = p :=
            (i1312_index_stab hp hp3 hP hX8 x).resolve_left fun h1 => htop (Subgroup.index_eq_one.1 h1)
          have c1 := Subgroup.card_mul_index M
          have c2 := Subgroup.card_mul_index (stabilizer P x)
          rw [h𝓜idx M hM, hk] at c1
          rw [hidx, hk] at c2
          have hcard : Nat.card (stabilizer P x) = Nat.card M :=
            Nat.eq_of_mul_eq_mul_right hp.pos (c2.trans c1.symm)
          exact (Subgroup.eq_of_le_of_card_ge hMle hcard.le).symm
      · rintro (h | h)
        · intro m _
          exact MulAction.mem_stabilizer_iff.1 (by rw [h]; exact Subgroup.mem_top m)
        · intro m hm
          exact MulAction.mem_stabilizer_iff.1 (by rw [h]; exact hm)
    rw [hfixset, hset, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hmemX₀] at hx1
    rw [hmemA] at hx2
    exact h𝓜ne M hM (hx2.symm.trans hx1)
  have hsplit : Nat.card X = X₀.card + ∑ M ∈ 𝓜, (A M).card := by
    have h1 : Finset.univ.card = (Finset.univ.filter fun x : X => stabilizer P x = ⊤).card +
        (Finset.univ.filter fun x : X => ¬ stabilizer P x = ⊤).card :=
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun x : X => stabilizer P x = ⊤)).symm
    have h2 : (Finset.univ.filter fun x : X => ¬ stabilizer P x = ⊤).card =
        ∑ M ∈ 𝓜, ((Finset.univ.filter fun x : X => ¬ stabilizer P x = ⊤).filter
          fun x => stabilizer P x = M).card := by
      rw [h𝓜]
      exact Finset.card_eq_sum_card_image _ _
    have h3 : ∀ M ∈ 𝓜, ((Finset.univ.filter fun x : X => ¬ stabilizer P x = ⊤).filter
        fun x => stabilizer P x = M) = A M := by
      intro M hM
      ext x
      rw [Finset.mem_filter, Finset.mem_filter, hmemA]
      constructor
      · rintro ⟨⟨-, -⟩, h⟩
        exact h
      · intro h
        refine ⟨⟨Finset.mem_univ _, ?_⟩, h⟩
        rw [h]
        exact h𝓜ne M hM
    have h4 : ∑ M ∈ 𝓜, ((Finset.univ.filter fun x : X => ¬ stabilizer P x = ⊤).filter
        fun x => stabilizer P x = M).card = ∑ M ∈ 𝓜, (A M).card :=
      Finset.sum_congr rfl fun M hM => by rw [h3 M hM]
    have hcu : Nat.card X = (Finset.univ : Finset X).card := by
      rw [Nat.card_eq_fintype_card, Finset.card_univ]
    rw [hcu, h1, hX₀, h2, h4]
  have hX₀card : X₀.card = Nat.card (i1312FixSet (X := X) (⊤ : Subgroup P)) := by
    rw [hfixset, hX₀]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h m _
      exact MulAction.mem_stabilizer_iff.1 (by rw [h]; exact Subgroup.mem_top m)
    · intro h
      rw [eq_top_iff]
      intro m _
      exact MulAction.mem_stabilizer_iff.2 (h m (Subgroup.mem_top m))
  have hX₀pos : 0 < X₀.card := by
    have h := hfix ⊤
    rw [← hX₀card] at h
    rcases Nat.eq_zero_or_pos X₀.card with h0 | h0
    · rw [h0] at h; norm_num at h
    · exact h0
  have hAge : ∀ M ∈ 𝓜, p ≤ (A M).card := by
    intro M hM
    have hpos : 0 < (A M).card := by
      obtain ⟨x, hx, -⟩ := (hmem𝓜 M).1 hM
      exact Finset.card_pos.2 ⟨x, (hmemA M x).2 hx⟩
    exact Nat.le_of_dvd hpos (hAp M hM)
  have hXle : X₀.card + ∑ M ∈ 𝓜, (A M).card ≤ 8 := by
    rw [← hsplit]; exact hX8
  obtain h0 | h1 | h2 | h3 : 𝓜.card = 0 ∨ 𝓜.card = 1 ∨ 𝓜.card = 2 ∨ 3 ≤ 𝓜.card := by omega
  ·
    rw [Finset.card_eq_zero] at h0
    have hall : ∀ x : X, stabilizer P x = ⊤ := by
      intro x
      by_contra hx
      have hmem : stabilizer P x ∈ 𝓜 := (hmem𝓜 _).2 ⟨x, rfl, hx⟩
      rw [h0] at hmem
      simp at hmem
    have hone : ∀ g : P, g = 1 := fun g =>
      hfaith g fun x => MulAction.mem_stabilizer_iff.1 (by rw [hall x]; exact Subgroup.mem_top g)
    haveI : Subsingleton P := ⟨fun a b => by rw [hone a, hone b]⟩
    rw [Nat.card_of_subsingleton (1 : P)] at hlt
    omega
  ·
    obtain ⟨M, hM⟩ := Finset.card_eq_one.1 h1
    have hMmem : M ∈ 𝓜 := by rw [hM]; simp
    have hall : ∀ g ∈ M, ∀ x : X, g • x = x := by
      intro g hg x
      apply MulAction.mem_stabilizer_iff.1
      by_cases hx : stabilizer P x = ⊤
      · rw [hx]; exact Subgroup.mem_top g
      · have hmem : stabilizer P x ∈ 𝓜 := (hmem𝓜 _).2 ⟨x, rfl, hx⟩
        rw [hM, Finset.mem_singleton] at hmem
        rw [hmem]; exact hg
    have hMbot : M = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      exact Subgroup.mem_bot.2 (hfaith g (hall g hg))
    have c := Subgroup.card_mul_index M
    rw [h𝓜idx M hMmem, hMbot, Subgroup.card_bot, one_mul] at c
    omega
  ·
    obtain ⟨M₁, M₂, hne, hM⟩ := Finset.card_eq_two.1 h2
    have h1mem : M₁ ∈ 𝓜 := by rw [hM]; simp
    have h2mem : M₂ ∈ 𝓜 := by rw [hM]; simp
    have hsum2 : ∑ M ∈ 𝓜, (A M).card = (A M₁).card + (A M₂).card := by
      rw [hM, Finset.sum_pair hne]
    have hA1 := hAge M₁ h1mem
    have hA2 := hAge M₂ h2mem
    have hp3' : p = 3 := by omega
    have hd1 := hfixcard M₁ h1mem
    have hd2 := hfixcard M₂ h2mem
    have hf1 := hfix M₁
    have hf2 := hfix M₂
    rw [hd1] at hf1
    rw [hd2] at hf2
    have hdvd1 : 3 ∣ (A M₁).card := by rw [← hp3']; exact hAp M₁ h1mem
    have hdvd2 : 3 ∣ (A M₂).card := by rw [← hp3']; exact hAp M₂ h2mem
    have hXdvd := hX
    rw [hsplit, hsum2] at hXdvd
    have e1 := i1312_dvd_eight hf1
    have e2 := i1312_dvd_eight hf2
    have e3 := i1312_dvd_eight hXdvd
    have hX₀' := hX₀pos
    omega
  ·
    have hsum : 𝓜.card * p ≤ ∑ M ∈ 𝓜, (A M).card := by
      have := Finset.card_nsmul_le_sum 𝓜 (fun M => (A M).card) p hAge
      simpa [smul_eq_mul] using this
    have h9 : 3 * 3 ≤ 𝓜.card * p := Nat.mul_le_mul h3 hp3
    have hX₀' := hX₀pos
    linarith

def i1312FixSub {T : Type} [Group T] (N : Subgroup (MulAut T)) : Subgroup T where
  carrier := {x | ∀ m ∈ N, m x = x}
  mul_mem' := fun {a b} ha hb m hm => by
    simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
    rw [ha m hm, hb m hm]
  one_mem' := fun m _ => map_one m
  inv_mem' := fun {a} ha m hm => by
    simp only [Set.mem_setOf_eq, map_inv] at ha ⊢
    rw [ha m hm]

theorem i1312_card_le_mulAut {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hT : Nat.card T ∣ 8) (P : Subgroup (MulAut T)) (hP : IsPGroup p P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : Nat.card P ≤ p := by
  letI : MulAction P T := MulAction.compHom T P.subtype
  have hsm : ∀ (g : P) (x : T), g • x = (g : MulAut T) x := fun g x => rfl
  refine i1312_card_le_of_fix hp hp3 hP ?_ hT ?_ ?_
  · intro x y
    exact Subtype.ext (hcomm x.1 x.2 y.1 y.2)
  · intro g hg
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have := hg x
    rw [hsm] at this
    rw [this]
    rfl
  · intro M
    have hset : ∀ x : T, x ∈ i1312FixSet (X := T) M ↔ x ∈ i1312FixSub (M.map P.subtype) := by
      intro x
      constructor
      · intro h n hn
        obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
        have h1 := h m hm
        rw [hsm] at h1
        exact h1
      · intro h m hm
        rw [hsm]
        exact h _ (Subgroup.mem_map.2 ⟨m, hm, rfl⟩)
    have hEq : i1312FixSet (X := T) M = ((i1312FixSub (M.map P.subtype) : Subgroup T) : Set T) :=
      Set.ext fun x => hset x
    rw [hEq]
    exact (Subgroup.card_subgroup_dvd_card _).trans hT

theorem i1312_exists_ker_card_le {B T : Type} [Group B] [Finite B] [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hB : IsPGroup p B) (hBc : ∀ x y : B, x * y = y * x)
    (hT : Nat.card T ∣ 8) (φ : B →* MulAut T) :
    ∃ K : Subgroup B, Nat.card B ≤ p * Nat.card K ∧ ∀ c ∈ K, φ c = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨φ.ker, ?_, fun c hc => hc⟩
  have hsplit : Nat.card B = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hdvd : Nat.card φ.range ∣ Nat.card B := by
    rw [hsplit]; exact Dvd.intro _ rfl
  have hR : IsPGroup p φ.range := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hB
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact IsPGroup.of_card hj
  have hRc : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hBc a b]
  have hcard := i1312_card_le_mulAut hp hp3 hT φ.range hR hRc
  rw [hsplit]
  exact Nat.mul_le_mul_right _ hcard

end CFSG.LocalAnalysis.GLTheoremA
