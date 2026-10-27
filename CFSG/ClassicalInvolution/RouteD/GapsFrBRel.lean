module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.ModelFacts (map_conj_map map_longSL2_range La_range_eq_map_conj)
open scoped MatrixGroups commutatorElement

section Commute

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

theorem commutes_rootSL2_disjoint (F₀ : HypFrame Q m) {a b c d : ℕ} (ha : a < m) (hb : b < m)
    (hc : c < m) (hd : d < m) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (s t u v : Bool) :
    Commutes (rootSL2 F₀ a b ha hb hab s t) (rootSL2 F₀ c d hc hd hcd u v) := by
  have hab' : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have hcd' : (⟨c, hc⟩ : Fin m) ≠ ⟨d, hd⟩ := fun h => hcd (congrArg Fin.val h)
  have key : ∀ {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l), i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      ∀ (s t u v : Bool), Commutes (F₀.longRoot hij s t).range (F₀.longRoot hkl u v).range := by
    rintro i j k l hij hkl hik hil hjk hjl s t u v _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x' : K, x = Multiplicative.ofAdd x' := ⟨Multiplicative.toAdd x, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y' : K, y = Multiplicative.ofAdd y' := ⟨Multiplicative.toAdd y, rfl⟩
    exact (HypFrame.commute_longRoot_longRoot_of_disjoint F₀ hij hkl hik hil hjk hjl s t u v x y).eq
  have hne : ∀ {i j : Fin m}, i ≠ j → j ≠ i := fun h e => h e.symm
  unfold rootSL2
  rw [longSL2_range_eq_sup, longSL2_range_eq_sup, CFSG.ClassicalInvolution.RouteD.commutes_sup_left,
    CFSG.ClassicalInvolution.RouteD.commutes_sup_right,
    CFSG.ClassicalInvolution.RouteD.commutes_sup_right]
  have i1 : (⟨a, ha⟩ : Fin m) ≠ ⟨c, hc⟩ := fun h => hac (congrArg Fin.val h)
  have i2 : (⟨a, ha⟩ : Fin m) ≠ ⟨d, hd⟩ := fun h => had (congrArg Fin.val h)
  have i3 : (⟨b, hb⟩ : Fin m) ≠ ⟨c, hc⟩ := fun h => hbc (congrArg Fin.val h)
  have i4 : (⟨b, hb⟩ : Fin m) ≠ ⟨d, hd⟩ := fun h => hbd (congrArg Fin.val h)
  exact ⟨⟨key hab' hcd' i1 i2 i3 i4 _ _ _ _, key hab' hcd'.symm i2 i1 i4 i3 _ _ _ _⟩,
    ⟨key hab'.symm hcd' i3 i4 i1 i2 _ _ _ _, key hab'.symm hcd'.symm i4 i3 i2 i1 _ _ _ _⟩⟩

theorem commutes_rootSL2_twin (F₀ : HypFrame Q m) {a b : ℕ} (ha : a < m) (hb : b < m)
    (hab : a ≠ b) (s : Bool) :
    Commutes (rootSL2 F₀ a b ha hb hab s false) (rootSL2 F₀ a b ha hb hab s true) := by
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have key1 : Commutes (F₀.longRoot hij s false).range (F₀.longRoot hij s true).range := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x' : K, x = Multiplicative.ofAdd x' := ⟨Multiplicative.toAdd x, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y' : K, y = Multiplicative.ofAdd y' := ⟨Multiplicative.toAdd y, rfl⟩
    exact (HypFrame.commute_longRoot_longRoot_left F₀ hij hij s false true x y).eq
  have swap_range : ∀ (u v : Bool), (F₀.longRoot hij.symm u v).range =
      (F₀.longRoot hij v u).range := by
    intro u v
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Multiplicative.ofAdd (-(Multiplicative.toAdd x)), ?_⟩
      have h := HypFrame.longRoot_swap F₀ hij v u (-(Multiplicative.toAdd x))
      rw [neg_neg] at h
      exact h
    · rintro ⟨x, rfl⟩
      refine ⟨Multiplicative.ofAdd (-(Multiplicative.toAdd x)), ?_⟩
      have h := HypFrame.longRoot_swap F₀ hij v u (Multiplicative.toAdd x)
      exact h.symm
  have right : ∀ (t u w : Bool), Commutes (F₀.longRoot hij t w).range
      (F₀.longRoot hij u w).range := by
    rintro t u w _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x' : K, x = Multiplicative.ofAdd x' := ⟨Multiplicative.toAdd x, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y' : K, y = Multiplicative.ofAdd y' := ⟨Multiplicative.toAdd y, rfl⟩
    exact (HypFrame.commute_longRoot_longRoot_right F₀ hij hij t w u x y).eq
  have right' : ∀ (t u w : Bool), Commutes (F₀.longRoot hij.symm t w).range
      (F₀.longRoot hij.symm u w).range := by
    rintro t u w _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x' : K, x = Multiplicative.ofAdd x' := ⟨Multiplicative.toAdd x, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y' : K, y = Multiplicative.ofAdd y' := ⟨Multiplicative.toAdd y, rfl⟩
    exact (HypFrame.commute_longRoot_longRoot_right F₀ hij.symm hij.symm t w u x y).eq
  unfold rootSL2
  rw [longSL2_range_eq_sup, longSL2_range_eq_sup, CFSG.ClassicalInvolution.RouteD.commutes_sup_left,
    CFSG.ClassicalInvolution.RouteD.commutes_sup_right,
    CFSG.ClassicalInvolution.RouteD.commutes_sup_right]
  refine ⟨⟨key1, ?_⟩, ⟨?_, ?_⟩⟩
  ·
    rw [Bool.not_true, swap_range]
    exact right s (!s) false
  · rw [Bool.not_false, swap_range]
    exact right (!s) s true
  · simp only [Bool.not_false, Bool.not_true]
    exact right' true false (!s)

theorem rootSL2_congr (F₀ : HypFrame Q m) {a a' b b' : ℕ} (ha : a < m) (hb : b < m) (hab : a ≠ b)
    (ha' : a' < m) (hb' : b' < m) (hab' : a' ≠ b') (e : a = a') (e' : b = b') (s t : Bool) :
    rootSL2 F₀ a b ha hb hab s t = rootSL2 F₀ a' b' ha' hb' hab' s t := by
  subst e e'
  rfl

end Commute


section Mem

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

omit [FiniteDimensional (GaloisField p f) V] in
theorem rootSL2_conj_mem_gen (hq : 4 ≤ p ^ f) {𝓕 : Set (Subgroup (spinGroup Q))}
    {Z' : Subgroup (V ≃ₗ[GaloisField p f] V)}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) Z') {m : ℕ} (F₀ : HypFrame Q m) {a b : ℕ}
    (ha : a < m) (hb : b < m) (hab : a ≠ b) (s t : Bool) (x : spinGroup Q) :
    (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom ∈ 𝓕 := by
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have hg : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hLa : ∀ A : SL(2, GaloisField p f), ((F₀.toFrame hij s t).map hg).La A =
      spinAction Q x * (F₀.toFrame hij s t).La A * (spinAction Q x)⁻¹ := fun A =>
    Frame.map_La _ hg A
  have himg : ((rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom).map
      (spinAction Q) = ((F₀.toFrame hij s t).map hg).La.range := by
    rw [La_range_eq_map_conj hLa, map_conj_map]
    congr 1
    exact map_longSL2_range F₀ hij s t
  have hL : ((rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom).map
      (spinAction Q) ∈ fundSet Q := by
    rw [himg]
    exact ⟨_, IsFundamental.of_frame ((F₀.toFrame hij s t).map hg)⟩
  obtain ⟨R, hR, hRe⟩ := cq.surj _ hL
  have hperf := rootSL2_map_conj_perfect_gen hq F₀ a b ha hb hab s t x
  have hRR := CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect (spinAction Q)
    cq.ker_le (cq.perf R hR) hperf hRe
  rw [← hRR]
  exact hR

end Mem

section Weyl

variable {K : Type} [Field K] {m : ℕ}

theorem map_conj_weylB_rootSL2 {k : Fin m} (hk : ¬ k.val + 1 < m) {a b : ℕ} (ha : a < m)
    (hb : b < m) (hab : a ≠ b) (s t : Bool) :
    (rootSL2 (oddFrame m K).toHypFrame a b ha hb hab s t).map
        (MulAut.conj (weylB K k)).toMonoidHom =
      rootSL2 (oddFrame m K).toHypFrame a b ha hb hab (shortWeylBool k ⟨a, ha⟩ s)
        (shortWeylBool k ⟨b, hb⟩ t) := by
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have key : ∀ {i j : Fin m} (hij : i ≠ j) (s t : Bool),
      ((oddFrame m K).longRoot hij s t).range.map (MulAut.conj (weylB K k)).toMonoidHom =
        ((oddFrame m K).longRoot hij (shortWeylBool k i s) (shortWeylBool k j t)).range := by
    intro i j hij s t
    have hε : (longWeylSign k i : K) * longWeylSign k j ≠ 0 := by
      unfold longWeylSign
      split_ifs <;> simp
    ext y
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd ((longWeylSign k i : K) * longWeylSign k j *
        Multiplicative.toAdd c), ?_⟩
      have h := weylB_conj_longRoot_of_not_lt K hk hij s t (Multiplicative.toAdd c)
      exact h.symm
    · rintro ⟨c, rfl⟩
      refine ⟨_, ⟨Multiplicative.ofAdd (((longWeylSign k i : K) * longWeylSign k j)⁻¹ *
        Multiplicative.toAdd c), rfl⟩, ?_⟩
      have h := weylB_conj_longRoot_of_not_lt K hk hij s t
        (((longWeylSign k i : K) * longWeylSign k j)⁻¹ * Multiplicative.toAdd c)
      rw [← mul_assoc, mul_inv_cancel₀ hε, one_mul] at h
      exact h
  have hnot : ∀ (j : Fin m) (t : Bool), shortWeylBool k j (!t) = !(shortWeylBool k j t) := by
    intro j t
    unfold shortWeylBool
    split_ifs <;> simp
  unfold rootSL2
  rw [longSL2_range_eq_sup, longSL2_range_eq_sup, Subgroup.map_sup, key hij s t,
    key hij.symm (!t) (!s), hnot, hnot]

end Weyl

end CFSG.ClassicalInvolution.RouteD.Gaps
