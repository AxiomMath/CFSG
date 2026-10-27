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
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv Equiv.Perm
open scoped Pointwise

@[expose] def JordanPrimeCycle : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (K : Subgroup (Perm α)) (p : ℕ), p.Prime →
    p + 3 ≤ Fintype.card α → MulAction.IsPreprimitive K α →
    (∃ σ ∈ K, σ.IsCycle ∧ σ.support.card = p) → alternatingGroup α ≤ K

theorem three_dvd_card_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    (h : 3 ≤ Fintype.card α) : 3 ∣ Nat.card (alternatingGroup α) := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have h2 : Nat.card (alternatingGroup α) = (Fintype.card α).factorial / 2 :=
    by rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  rw [h2]
  have h6 : 6 ∣ (Fintype.card α).factorial := by
    have := Nat.factorial_dvd_factorial h
    exact Nat.dvd_trans (by decide : 6 ∣ Nat.factorial 3) this
  obtain ⟨m, hm⟩ := h6
  rw [hm]
  exact ⟨m, by omega⟩

theorem jordan_action (hJ : JordanPrimeCycle) {G X : Type} [Group G] [Finite G] [Fintype X]
    [DecidableEq X] [MulAction G X] [MulAction.IsPreprimitive G X] {p : ℕ} (hp : p.Prime)
    (hX : p + 3 ≤ Fintype.card X) (g : G) (hg : (MulAction.toPermHom G X g).IsCycle)
    (hs : (MulAction.toPermHom G X g).support.card = p) : 3 ∣ Nat.card G := by
  set K : Subgroup (Perm X) := (MulAction.toPermHom G X).range with hK
  let φ : G →* K := (MulAction.toPermHom G X).rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective _
  have hprim : MulAction.IsPreprimitive K X := by
    exact MulAction.IsPreprimitive.of_surjective (φ := ⇑φ) (f := ⟨id, fun m x => rfl⟩)
      Function.surjective_id
  have hA := hJ X K p hp hX hprim ⟨MulAction.toPermHom G X g, ⟨g, rfl⟩, hg, hs⟩
  have h3 : 3 ∣ Nat.card (alternatingGroup X) := three_dvd_card_alternatingGroup (by omega)
  have h4 : Nat.card (alternatingGroup X) ∣ Nat.card K := Subgroup.card_dvd_of_le hA
  have h5 : Nat.card K ∣ Nat.card G := Subgroup.card_range_dvd _
  exact h3.trans (h4.trans h5)


theorem isPreprimitive_orbit_of_cycle {α : Type} [Fintype α] [DecidableEq α]
    (H : Subgroup (Perm α)) (a : α) {p : ℕ} (hp : p.Prime) (σ : Perm α) (hσH : σ ∈ H)
    (hσc : σ.IsCycle) (hσs : σ.support.card = p)
    (hsupp : ∀ x ∈ σ.support, x ∈ MulAction.orbit H a)
    (h2p : Nat.card (MulAction.orbit H a) < 2 * p) :
    MulAction.IsPreprimitive H (MulAction.orbit H a) where
  isTrivialBlock_of_isBlock := by
    intro B hB
    classical
    by_contra hnt
    simp only [MulAction.IsTrivialBlock, not_or] at hnt
    obtain ⟨hns, hnu⟩ := hnt
    obtain ⟨x₀, hx₀⟩ : σ.support.Nonempty := by
      rw [← Finset.card_pos, hσs]; exact hp.pos
    let y₀ : MulAction.orbit H a := ⟨x₀, hsupp x₀ hx₀⟩
    set g : H := ⟨σ, hσH⟩ with hg
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      have : σ ^ p = 1 := by rw [← hσs, ← hσc.orderOf]; exact pow_orderOf_eq_one σ
      simpa using this
    obtain ⟨b, hb⟩ : B.Nonempty := (Set.not_subsingleton_iff.mp hns).nonempty
    obtain ⟨s₀, hs₀⟩ := MulAction.exists_smul_eq H b y₀
    set B' : Set (MulAction.orbit H a) := s₀ • B with hB'
    have hB'b : MulAction.IsBlock H B' := hB.translate s₀
    have hy₀ : y₀ ∈ B' := ⟨b, hb, hs₀⟩
    have hB'nt : ¬ B'.Subsingleton ∧ B' ≠ Set.univ := by
      have := (MulAction.IsTrivialBlock.smul_iff (B := B) s₀)
      simp only [MulAction.IsTrivialBlock] at this
      rw [hB'] ; tauto
    clear_value B'
    have hF1 : 2 * B'.ncard < 2 * p := by
      obtain ⟨y, hy⟩ : ∃ y, y ∉ B' := by
        by_contra h; push Not at h; exact hB'nt.2 (Set.eq_univ_of_forall h)
      obtain ⟨s, hs⟩ := MulAction.exists_smul_eq H y₀ y
      have hne : s • B' ≠ B' := by
        intro h
        apply hy
        rw [← h]
        exact ⟨y₀, hy₀, hs⟩
      have hdisj : Disjoint (s • B') B' := by
        rw [Set.disjoint_iff_inter_eq_empty]
        by_contra h
        exact hne (MulAction.isBlock_iff_smul_eq_of_nonempty.mp hB'b (Set.nonempty_iff_ne_empty.mpr h))
      have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
      rw [Set.ncard_smul_set] at h1
      have h2 : (s • B' ∪ B').ncard ≤ Nat.card (MulAction.orbit H a) := by
        rw [← Set.ncard_univ]
        exact Set.ncard_le_ncard (Set.subset_univ _)
      omega
    have hblk : ∀ s t : H, ((s • B') ∩ (t • B')).Nonempty → s • B' = t • B' := by
      intro s t ⟨x, hxs, hxt⟩
      obtain ⟨b1, hb1, hx1⟩ := hxs
      obtain ⟨b2, hb2, hx2⟩ := hxt
      have h1 : ((t⁻¹ * s) • B' ∩ B').Nonempty := ⟨b2, ⟨b1, hb1, by
        show (t⁻¹ * s) • b1 = b2
        rw [mul_smul]
        have hx1' : s • b1 = x := hx1
        have hx2' : t • b2 = x := hx2
        rw [hx1', ← hx2', inv_smul_smul]⟩, hb2⟩
      have h2 := MulAction.isBlock_iff_smul_eq_of_nonempty.mp hB'b h1
      calc s • B' = t • ((t⁻¹ * s) • B') := by rw [smul_smul, mul_inv_cancel_left]
        _ = t • B' := by rw [h2]
    have hpow_iter : ∀ (k m : ℕ), g ^ k • B' = B' → (g ^ k) ^ m • B' = B' := by
      intro k m hk
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, mul_smul, hk, ih]
    have hk : ∀ k : ℕ, 0 < k → k < p → g ^ k • B' = B' → g • B' = B' := by
      intro k hk0 hkp hk
      have hcop : Nat.Coprime k p := (Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun hd => absurd (Nat.le_of_dvd hk0 hd) (by omega)) |>.symm
      obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
      have hkm : g = (g ^ k) ^ m := by
        rw [← pow_mul]
        have : k * m = p * (k * m / p) + 1 := by
          have := Nat.div_add_mod (k * m) p
          omega
        rw [this, pow_add, pow_mul, hgp, one_pow, one_mul, pow_one]
      rw [hkm]
      exact hpow_iter k m hk
    have hgB : g • B' = B' := by
      by_contra hne
      have hinj_idx : ∀ i j : ℕ, i < p → j < p → g ^ i • B' = g ^ j • B' → i = j := by
        have key : ∀ i j : ℕ, i < j → j < p → g ^ i • B' = g ^ j • B' → False := by
          intro i j hij hjp h
          have h1 : g ^ (j - i) • B' = B' := by
            have : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add]; congr 1; omega
            rw [this, mul_smul] at h
            have h2 := congrArg (fun X => (g ^ i)⁻¹ • X) h
            simpa using h2.symm
          exact hne (hk (j - i) (by omega) (by omega) h1)
        intro i j hi hj h
        rcases lt_trichotomy i j with h1 | h1 | h1
        · exact (key i j h1 hj h).elim
        · exact h1
        · exact (key j i h1 hi h.symm).elim
      obtain ⟨u, hu, v, hv, huv⟩ := Set.not_subsingleton_iff.mp hB'nt.1
      let f : Fin p × Bool → MulAction.orbit H a :=
        fun ie => (g ^ (ie.1 : ℕ)) • (if ie.2 then u else v)
      have hinj : Function.Injective f := by
        rintro ⟨i, e⟩ ⟨j, e'⟩ hf
        have hmem : ∀ e : Bool, (if e then u else v) ∈ B' := by
          intro e; cases e <;> simp [hu, hv]
        have hne' : ((g ^ (i : ℕ)) • B' ∩ (g ^ (j : ℕ)) • B').Nonempty :=
          ⟨f (i, e), ⟨_, hmem e, rfl⟩, by
            rw [hf]; exact ⟨_, hmem e', rfl⟩⟩
        have hij := hinj_idx i j i.2 j.2 (hblk _ _ hne')
        have hij' : i = j := Fin.ext hij
        subst hij'
        have : (if e then u else v) = (if e' then u else v) := by
          have := hf
          simp only [f] at this
          exact MulAction.injective _ this
        cases e <;> cases e' <;> simp at this <;> first | rfl | exact absurd this.symm huv | exact absurd this huv
      have := Fintype.card_le_of_injective f hinj
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at this
      rw [← Nat.card_eq_fintype_card] at this
      omega
    have hzp : ∀ i : ℤ, g ^ i • B' = B' := by
      intro i
      have hs : g ∈ MulAction.stabilizer H B' := MulAction.mem_stabilizer_iff.mpr hgB
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpow_mem _ hs i)
    have hmem : ∀ y ∈ σ.support, ∃ h : y ∈ MulAction.orbit H a, (⟨y, h⟩ : MulAction.orbit H a) ∈ B' := by
      intro y hy
      have hsc : σ.SameCycle x₀ y := hσc.sameCycle (Equiv.Perm.mem_support.mp hx₀)
        (Equiv.Perm.mem_support.mp hy)
      obtain ⟨i, hi⟩ := hsc
      have hyo : y ∈ MulAction.orbit H a := hsupp y hy
      refine ⟨hyo, ?_⟩
      have : (g ^ i) • y₀ = ⟨y, hyo⟩ := by
        apply Subtype.ext
        show (((g ^ i : H) : Perm α)) x₀ = y
        simpa using hi
      rw [← this, ← hzp i]
      exact ⟨y₀, hy₀, rfl⟩
    let F : α → MulAction.orbit H a := fun y => if h : y ∈ MulAction.orbit H a then ⟨y, h⟩ else y₀
    have hF : ∀ y ∈ (σ.support : Set α), F y ∈ B' := by
      intro y hy
      obtain ⟨h, hh⟩ := hmem y hy
      simp only [F, h, dite_true]
      exact hh
    have hFinj : Set.InjOn F (σ.support : Set α) := by
      intro y hy z hz hyz
      obtain ⟨h1, -⟩ := hmem y hy
      obtain ⟨h2, -⟩ := hmem z hz
      simp only [F, h1, h2, dite_true] at hyz
      exact congrArg Subtype.val hyz
    have hle := Set.ncard_le_ncard_of_injOn F hF hFinj (Set.toFinite _)
    rw [Set.ncard_coe_finset, hσs] at hle
    omega


theorem supp_subset_orbit {α : Type} [Fintype α] [DecidableEq α] (H : Subgroup (Perm α))
    {ρ : Perm α} (hρH : ρ ∈ H) (hρc : ρ.IsCycle) {a : α} (ha : a ∈ ρ.support) :
    ∀ x ∈ ρ.support, x ∈ MulAction.orbit H a := by
  intro x hx
  obtain ⟨i, hi⟩ := hρc.sameCycle (Equiv.Perm.mem_support.mp ha) (Equiv.Perm.mem_support.mp hx)
  rw [MulAction.mem_orbit_iff]
  refine ⟨(⟨ρ, hρH⟩ : H) ^ i, ?_⟩
  show (((⟨ρ, hρH⟩ : H) ^ i : H) : Perm α) a = x
  simpa using hi

theorem core_false (hJ : JordanPrimeCycle) {α : Type} [Fintype α] [DecidableEq α]
    (H : Subgroup (Perm α)) (h3 : ¬ 3 ∣ Nat.card H) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (σ τ : Perm α) (hσH : σ ∈ H) (hτH : τ ∈ H) (hσ : σ.IsCycle ∧ σ.support.card = p)
    (hτ : τ.IsCycle ∧ τ.support.card = q)
    (hpq : Fintype.card α < p + q) (hqp : q + 3 ≤ p) : False := by
  classical
  obtain ⟨a, ha⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hσ.2]; exact hp.pos
  obtain ⟨b, hb⟩ : τ.support.Nonempty := by
    rw [← Finset.card_pos, hτ.2]; exact hq.pos
  set O : Set α := MulAction.orbit H a with hO
  have hσO : ∀ x ∈ σ.support, x ∈ O := supp_subset_orbit H hσH hσ.1 ha
  have hcardO_ge : p ≤ O.ncard := by
    have := Set.ncard_le_ncard (show (σ.support : Set α) ⊆ O from fun x hx => hσO x hx)
      (Set.toFinite _)
    rwa [Set.ncard_coe_finset, hσ.2] at this
  have hcardO_le : O.ncard ≤ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  have hτO : ∀ x ∈ τ.support, x ∈ O := by
    by_cases hbO : b ∈ O
    · have heq : MulAction.orbit H b = O := (MulAction.orbit_eq_iff.mpr hbO)
      intro x hx
      rw [← heq]; exact supp_subset_orbit H hτH hτ.1 hb x hx
    · exfalso
      set O' : Set α := MulAction.orbit H b
      have hdisj : Disjoint O O' := by
        rw [Set.disjoint_left]
        intro x hxO hxO'
        apply hbO
        have e1 : MulAction.orbit H x = MulAction.orbit H a := MulAction.orbit_eq_iff.mpr hxO
        have e2 : MulAction.orbit H x = MulAction.orbit H b := MulAction.orbit_eq_iff.mpr hxO'
        exact MulAction.orbit_eq_iff.mp (e2.symm.trans e1)
      have hq' : q ≤ O'.ncard := by
        have := Set.ncard_le_ncard (show (τ.support : Set α) ⊆ O' from fun x hx =>
          supp_subset_orbit H hτH hτ.1 hb x hx) (Set.toFinite _)
        rwa [Set.ncard_coe_finset, hτ.2] at this
      have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
      have h2 : (O ∪ O').ncard ≤ Fintype.card α := by
        rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
        exact Set.ncard_le_ncard (Set.subset_univ _)
      omega
  let _ : Fintype ↥O := Fintype.ofFinite _
  have hcardX : Fintype.card ↥O = O.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hprim : MulAction.IsPreprimitive H O :=
    isPreprimitive_orbit_of_cycle H a hp σ hσH hσ.1 hσ.2 hσO (by
      rw [show Nat.card ↥(MulAction.orbit H a) = Nat.card ↥O from rfl, Nat.card_eq_fintype_card,
        hcardX]; omega)
  let g : H := ⟨τ, hτH⟩
  have hcoe : ∀ (k : ℤ) (x : ↥O), (((g ^ k) • x : ↥O) : α) = (τ ^ k) (x : α) := by
    intro k x
    show (((g ^ k : H) : Perm α)) (x : α) = _
    simp [g]
  have hg1 : ∀ x : ↥O, (((MulAction.toPermHom H ↥O g) x : ↥O) : α) = τ (x : α) := fun x => rfl
  have hcyc : (MulAction.toPermHom H ↥O g).IsCycle := by
    have hbO : b ∈ O := hτO b hb
    refine ⟨⟨b, hbO⟩, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      have h' : (τ b) = b := by rw [hg1] at this; exact this
      exact (Equiv.Perm.mem_support.mp hb) h'
    · intro y hy
      have hy' : τ (y : α) ≠ (y : α) := by
        intro h
        apply hy
        apply Subtype.ext
        rw [hg1]; exact h
      obtain ⟨i, hi⟩ := hτ.1.sameCycle (Equiv.Perm.mem_support.mp hb) hy'
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have := hcoe i ⟨b, hbO⟩
      rw [← map_zpow]
      simpa [MulAction.toPermHom_apply] using this.trans hi
  have hcards : (MulAction.toPermHom H ↥O g).support.card = q := by
    rw [← hτ.2]
    apply Finset.card_bij (fun (x : ↥O) _ => (x : α))
    · intro x hx
      rw [Equiv.Perm.mem_support] at hx ⊢
      intro h
      apply hx
      apply Subtype.ext
      rw [hg1]; exact h
    · intro x _ y _ h
      exact Subtype.ext h
    · intro z hz
      refine ⟨⟨z, hτO z hz⟩, ?_, rfl⟩
      rw [Equiv.Perm.mem_support] at hz ⊢
      intro h
      apply hz
      have := congrArg Subtype.val h
      rw [hg1] at this; exact this
  exact h3 (jordan_action hJ hq (by omega) g hcyc hcards)


theorem isCycle_of_orderOf_prime {N p : ℕ} (hp : p.Prime) (σ : Perm (Fin N)) (hσ : orderOf σ = p)
    (hN : N < 2 * p) : σ.IsCycle ∧ σ.support.card = p := by
  have hp' : (orderOf σ).Prime := hσ ▸ hp
  obtain ⟨n, hn⟩ := cycleType_prime_order hp'
  have hsum := sum_cycleType σ
  rw [hn, hσ, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hle : σ.support.card ≤ N := by
    have := Finset.card_le_univ σ.support
    simpa using this
  have hn0 : n = 0 := by
    by_contra h
    have : 2 * p ≤ (n + 1) * p := Nat.mul_le_mul_right _ (by omega)
    omega
  subst hn0
  refine ⟨?_, by simpa using hsum.symm⟩
  rw [← card_cycleType_eq_one, hn]
  simp

theorem exists_cycle_perm (N q : ℕ) (hq : q.Prime) (hqN : q ≤ N) :
    ∃ c : Perm (Fin N), c.IsCycle ∧ c.support.card = q := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by have := hq.two_le; omega⟩
  let e : Fin (n + 2) ↪ Fin N := Fin.castLEEmb hqN
  let f : Fin (n + 2) ≃ Subtype (· ∈ Set.range e) := Equiv.ofInjective e e.injective
  let c : Perm (Fin N) := (finRotate (n + 2)).extendDomain f
  have hc : c.IsCycle := isCycle_finRotate.extendDomain f
  refine ⟨c, hc, ?_⟩
  have h1 : c.cycleType = (finRotate (n + 2)).cycleType := cycleType_extendDomain f
  have h2 := sum_cycleType c
  rw [h1, isCycle_finRotate.cycleType] at h2
  simpa using h2.symm

theorem exists_cycle_mem_of_dvd {N q : ℕ} (hq : q.Prime) (hqN : q ≤ N)
    (H : Subgroup (Perm (Fin N))) (hdvd : q ^ (N.factorial).factorization q ∣ Nat.card H) :
    ∃ τ ∈ H, τ.IsCycle ∧ τ.support.card = q := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨c, hc, hcs⟩ := exists_cycle_perm N q hq hqN
  have hcard : Nat.card (Perm (Fin N)) = N.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  let P : Sylow q H := default
  let PH : Subgroup (Perm (Fin N)) := P.toSubgroup.map H.subtype
  have hPHcard : Nat.card PH = q ^ (N.factorial).factorization q := by
    rw [show PH = P.toSubgroup.map H.subtype from rfl,
      Subgroup.card_map_of_injective H.subtype_injective, P.card_eq_multiplicity]
    have hH : Nat.card H ∣ N.factorial := by
      rw [← hcard]; exact Subgroup.card_subgroup_dvd_card H
    have h1 : (N.factorial).factorization q ≤ (Nat.card H).factorization q := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hq (Nat.card_pos.ne')).mp hdvd
      exact this
    have h2 : (Nat.card H).factorization q ≤ (N.factorial).factorization q :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (Nat.factorial_ne_zero N)).mpr hH q
    rw [le_antisymm h2 h1]
  let Pyl : Sylow q (Perm (Fin N)) := Sylow.ofCard PH (hPHcard.trans (by rw [hcard]))
  have hcq : orderOf c = q := hc.orderOf.trans hcs
  have hz : IsPGroup q (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcq]; simp)
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin N)) Q Pyl
  have hmem : g * c * g⁻¹ ∈ PH := by
    have h1 : g * c * g⁻¹ ∈ ((g • Q : Sylow q (Perm (Fin N))) : Subgroup (Perm (Fin N))) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact Subgroup.mem_map.mpr ⟨c, hQ (Subgroup.mem_zpowers c), by simp [MulAut.conj_apply]⟩
    rw [hg] at h1
    exact h1
  obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp hmem
  refine ⟨x.1, x.2, ?_⟩
  have : x.1 = g * c * g⁻¹ := hx
  rw [this]
  exact ⟨hc.conj, by rw [card_support_conj, hcs]⟩


theorem exists_cycle_of_dvd_prime {N p : ℕ} (hp : p.Prime) (hN : N < 2 * p)
    (H : Subgroup (Perm (Fin N))) (hdvd : p ∣ Nat.card H) :
    ∃ σ ∈ H, σ.IsCycle ∧ σ.support.card = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨x.1, x.2, isCycle_of_orderOf_prime hp x.1 ?_ hN⟩
  rw [← hx]
  exact (Subgroup.orderOf_coe x)

theorem no_small_index_12 (hJ : JordanPrimeCycle) (H : Subgroup (Perm (Fin 12)))
    (h3 : ¬ 3 ∣ Nat.card H) (hd : Nat.card H ∣ 239500800)
    (hb : 239500800 ≤ 1024 * Nat.card H) : False := by
  obtain ⟨j, hj⟩ := hd
  set n := Nat.card H with hn
  have hn0 : 0 < n := Nat.card_pos
  have hcop : Nat.Coprime (3 ^ 5) n := Nat.Coprime.pow_left 5
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have h243 : 3 ^ 5 ∣ j := by
    have : 3 ^ 5 ∣ n * j := ⟨985600, by rw [← hj]; norm_num⟩
    exact hcop.dvd_of_dvd_mul_left this
  obtain ⟨j', rfl⟩ := h243
  have hjle : 3 ^ 5 * j' ≤ 1024 := by
    by_contra hcon
    push Not at hcon
    have : 1024 * n < n * (3 ^ 5 * j') := by nlinarith
    omega
  have hj'0 : 0 < j' := by
    rcases Nat.eq_zero_or_pos j' with h | h
    · subst h; omega
    · exact h
  have hj'4 : j' ≤ 4 := by omega
  have h7 : 7 ∣ n ∧ 11 ∣ n := by
    interval_cases j' <;> constructor <;> omega
  obtain ⟨σ, hσH, hσ⟩ := exists_cycle_of_dvd_prime (N := 12) (p := 11) (by norm_num) (by norm_num) H
    h7.2
  obtain ⟨τ, hτH, hτ⟩ := exists_cycle_of_dvd_prime (N := 12) (p := 7) (by norm_num) (by norm_num) H
    h7.1
  exact core_false hJ H h3 (p := 11) (q := 7) (by norm_num) (by norm_num) σ τ hσH hτH hσ hτ
    (by simp) (by omega)

theorem factorization_16_five : (Nat.factorial 16).factorization 5 = 3 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.factorization_def _ (by norm_num : Nat.Prime 5)]
  rw [padicValNat_factorial (b := 3) (by norm_num [Nat.log])]
  decide

theorem factorization_16_seven : (Nat.factorial 16).factorization 7 = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Nat.factorization_def _ (by norm_num : Nat.Prime 7)]
  rw [padicValNat_factorial (b := 3) (by norm_num [Nat.log])]
  decide

theorem no_small_index_16 (hJ : JordanPrimeCycle) (H : Subgroup (Perm (Fin 16)))
    (h3 : ¬ 3 ∣ Nat.card H) (hd : Nat.card H ∣ 10461394944000)
    (hb : 10461394944000 ≤ 16384 * Nat.card H) : False := by
  obtain ⟨j, hj⟩ := hd
  set n := Nat.card H with hn
  have hn0 : 0 < n := Nat.card_pos
  have hcop : Nat.Coprime (3 ^ 6) n := Nat.Coprime.pow_left 6
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have h729 : 3 ^ 6 ∣ j := by
    have : 3 ^ 6 ∣ n * j := ⟨14350336000, by rw [← hj]; norm_num⟩
    exact hcop.dvd_of_dvd_mul_left this
  obtain ⟨j', rfl⟩ := h729
  have hjle : 3 ^ 6 * j' ≤ 16384 := by
    by_contra hcon
    push Not at hcon
    have : 16384 * n < n * (3 ^ 6 * j') := by nlinarith
    omega
  have hj'0 : 0 < j' := by
    rcases Nat.eq_zero_or_pos j' with h | h
    · subst h; omega
    · exact h
  have hj'22 : j' ≤ 22 := by omega
  have hcases : (j' = 13 ∧ 11 ∣ n ∧ 49 ∣ n) ∨ (j' ≠ 13 ∧ 13 ∣ n ∧ 125 ∣ n) ∨
      (j' ≠ 13 ∧ 13 ∣ n ∧ 49 ∣ n) := by
    interval_cases j' <;> omega
  rcases hcases with ⟨-, h11, h49⟩ | ⟨-, h13, h125⟩ | ⟨-, h13, h49⟩
  · obtain ⟨σ, hσH, hσ⟩ := exists_cycle_of_dvd_prime (N := 16) (p := 11) (by norm_num)
      (by norm_num) H h11
    obtain ⟨τ, hτH, hτ⟩ := exists_cycle_mem_of_dvd (N := 16) (q := 7) (by norm_num) (by norm_num) H
      (by rw [factorization_16_seven]; exact h49)
    exact core_false hJ H h3 (p := 11) (q := 7) (by norm_num) (by norm_num) σ τ hσH hτH hσ hτ
      (by simp) (by omega)
  · obtain ⟨σ, hσH, hσ⟩ := exists_cycle_of_dvd_prime (N := 16) (p := 13) (by norm_num)
      (by norm_num) H h13
    obtain ⟨τ, hτH, hτ⟩ := exists_cycle_mem_of_dvd (N := 16) (q := 5) (by norm_num) (by norm_num) H
      (by rw [factorization_16_five]; exact h125)
    exact core_false hJ H h3 (p := 13) (q := 5) (by norm_num) (by norm_num) σ τ hσH hτH hσ hτ
      (by simp) (by omega)
  · obtain ⟨σ, hσH, hσ⟩ := exists_cycle_of_dvd_prime (N := 16) (p := 13) (by norm_num)
      (by norm_num) H h13
    obtain ⟨τ, hτH, hτ⟩ := exists_cycle_mem_of_dvd (N := 16) (q := 7) (by norm_num) (by norm_num) H
      (by rw [factorization_16_seven]; exact h49)
    exact core_false hJ H h3 (p := 13) (q := 7) (by norm_num) (by norm_num) σ τ hσH hτH hσ hτ
      (by simp) (by omega)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
