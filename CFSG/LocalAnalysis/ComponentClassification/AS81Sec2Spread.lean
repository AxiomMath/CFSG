module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec2

theorem exists_mem_inv_mul_mem_of_relIndex_le {V X Y : Subgroup G} (hXV : X ≤ V)
    (h : Y.relIndex V ≤ Y.relIndex X) {f : G} (hf : f ∈ V) : ∃ x ∈ X, x⁻¹ * f ∈ Y := by
  let φ := quotientSubgroupOfEmbeddingOfLE Y hXV
  have hbij : Function.Bijective φ := φ.injective.bijective_of_nat_card_le h
  obtain ⟨q, hq⟩ := hbij.2 (QuotientGroup.mk (⟨f, hf⟩ : ↥V))
  induction q using QuotientGroup.induction_on with
  | H x =>
    refine ⟨x, x.2, ?_⟩
    rw [quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, mem_subgroupOf] at hq
    simpa using hq

theorem mem_or_of_relIndex_eq_four {W Z : Subgroup G} (h4 : Z.relIndex W = 4) {a b c w : G}
    (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hw : w ∈ W) (h1a : a ∉ Z) (h1b : b ∉ Z)
    (h1c : c ∉ Z) (hab : a⁻¹ * b ∉ Z) (hac : a⁻¹ * c ∉ Z) (hbc : b⁻¹ * c ∉ Z) :
    w ∈ Z ∨ a⁻¹ * w ∈ Z ∨ b⁻¹ * w ∈ Z ∨ c⁻¹ * w ∈ Z := by
  classical
  set Q := ↥W ⧸ Z.subgroupOf W
  have : Fintype Q := Fintype.ofFinite Q
  let q : ↥W → Q := QuotientGroup.mk
  have hq : ∀ u v : ↥W, q u = q v ↔ (u : G)⁻¹ * v ∈ Z := fun u v => by
    rw [QuotientGroup.eq, mem_subgroupOf]
    simp
  set s : Finset Q := {q 1, q ⟨a, ha⟩, q ⟨b, hb⟩, q ⟨c, hc⟩}
  have hs : s.card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · rw [Ne, hq]
      exact hbc
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or, hq]
      exact ⟨hab, hac⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or, hq, OneMemClass.coe_one,
        inv_one, one_mul]
      exact ⟨h1a, h1b, h1c⟩
  have hcard : Fintype.card Q = 4 := by
    rw [Fintype.card_eq_nat_card]
    exact h4
  have huniv : s = Finset.univ := Finset.eq_univ_of_card s (by rw [hs, hcard])
  have hw' : q ⟨w, hw⟩ ∈ s := huniv ▸ Finset.mem_univ _
  simp only [s, Finset.mem_insert, Finset.mem_singleton] at hw'
  rcases hw' with h | h | h | h
  · left
    have := (hq _ _).mp h.symm
    simpa using this
  · exact Or.inr (Or.inl ((hq _ _).mp h.symm))
  · exact Or.inr (Or.inr (Or.inl ((hq _ _).mp h.symm)))
  · exact Or.inr (Or.inr (Or.inr ((hq _ _).mp h.symm)))

omit [Finite G] in
theorem mem_centralizer_of_odd_orderOf {S Z : Subgroup G} (hZ2 : ∀ z ∈ Z, z * z = 1) {w : G}
    (hwZ : w ∈ centralizer (Z : Set G)) (hwS : ∀ s ∈ S, s⁻¹ * (w⁻¹ * s * w) ∈ Z)
    (hw : Odd (orderOf w)) : w ∈ centralizer (S : Set G) := by
  rw [mem_centralizer_iff]
  intro s hs
  set z := s⁻¹ * (w⁻¹ * s * w) with hzdef
  have hz := hwS s hs
  have key : ∀ k : ℕ, (w ^ k)⁻¹ * s * w ^ k = s * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs' : w⁻¹ * s * w = s * z := by rw [hzdef]; group
      have hzk : w⁻¹ * z ^ k * w = z ^ k := by
        have hc : Commute (z ^ k) w := Commute.pow_left (mem_centralizer_iff.mp hwZ z hz) k
        calc w⁻¹ * z ^ k * w = w⁻¹ * (z ^ k * w) := by group
          _ = z ^ k := by rw [hc.eq]; group
      calc (w ^ (k + 1))⁻¹ * s * w ^ (k + 1) = w⁻¹ * ((w ^ k)⁻¹ * s * w ^ k) * w := by
            rw [pow_succ]; group
        _ = w⁻¹ * (s * z ^ k) * w := by rw [ih]
        _ = (w⁻¹ * s * w) * (w⁻¹ * z ^ k * w) := by group
        _ = s * z * z ^ k := by rw [hs', hzk]
        _ = s * z ^ (k + 1) := by rw [pow_succ', mul_assoc]
  obtain ⟨m, hm⟩ := hw
  have h1 := key (orderOf w)
  rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one, hm] at h1
  have hz1 : z ^ (2 * m + 1) = 1 := by
    have := congrArg (s⁻¹ * ·) h1
    simpa using this.symm
  have hzz : z * z = 1 := hZ2 z hz
  have hz1' : z = 1 := by
    rw [pow_succ, pow_mul, sq, hzz, one_pow, one_mul] at hz1
    exact hz1
  have : w⁻¹ * s * w = s := by
    have h2 : w⁻¹ * s * w = s * z := by rw [hzdef]; group
    rw [h2, hz1', mul_one]
  calc s * w = w * (w⁻¹ * s * w) := by group
    _ = w * s := by rw [this]

structure FourLines (V Z : Subgroup G) (W : Fin 4 → Subgroup G) : Prop where
  elem : IsElemAbelian 2 V
  card : Nat.card V = 64
  cardZ : Nat.card Z = 4
  Z_le : ∀ i, Z ≤ W i
  le : ∀ i, W i ≤ V
  cardW : ∀ i, Nat.card (W i) = 16
  inf : ∀ i j, i ≠ j → W i ⊓ W j = Z

namespace FourLines

variable {V Z : Subgroup G} {W : Fin 4 → Subgroup G} (hL : FourLines V Z W)
include hL

omit [Finite G] in
theorem comm {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  congrArg Subtype.val (hL.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

omit [Finite G] in
theorem mul_self {a : G} (ha : a ∈ V) : a * a = 1 := by
  rw [← sq]
  exact hL.elem.2 a ha

omit [Finite G] in
theorem inv_eq {a : G} (ha : a ∈ V) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (hL.mul_self ha)

omit [Finite G] in
theorem inv_mul_mul_mem {a a' b b' : G} (ha : a ∈ V) (hb : b ∈ V) (ha' : a' ∈ V)
    (h1 : a⁻¹ * a' ∈ Z) (h2 : b⁻¹ * b' ∈ Z) : (a * b)⁻¹ * (a' * b') ∈ Z := by
  have hc := hL.comm (V.inv_mem hb) (V.mul_mem (V.inv_mem ha) ha')
  have : (a * b)⁻¹ * (a' * b') = (a⁻¹ * a') * (b⁻¹ * b') := by
    calc (a * b)⁻¹ * (a' * b') = (b⁻¹ * (a⁻¹ * a')) * b' := by group
      _ = ((a⁻¹ * a') * b⁻¹) * b' := by rw [hc]
      _ = (a⁻¹ * a') * (b⁻¹ * b') := by group
  rw [this]
  exact Z.mul_mem h1 h2

omit [Finite G] in
theorem relIndex_V (i : Fin 4) : (W i).relIndex V = 4 := by
  have h := relIndex_mul_card (W i) V
  rw [inf_eq_left.mpr (hL.le i), hL.cardW, hL.card] at h
  omega

omit [Finite G] in
theorem relIndex_W {i j : Fin 4} (hij : i ≠ j) : (W j).relIndex (W i) = 4 := by
  have h := relIndex_mul_card (W j) (W i)
  rw [hL.inf j i hij.symm, hL.cardW, hL.cardZ] at h
  omega

omit [Finite G] in
theorem relIndex_Z (i : Fin 4) : Z.relIndex (W i) = 4 := by
  have h := relIndex_mul_card Z (W i)
  rw [inf_eq_left.mpr (hL.Z_le i), hL.cardW, hL.cardZ] at h
  omega

theorem exists_mul {i j : Fin 4} (hij : i ≠ j) {f : G} (hf : f ∈ V) :
    ∃ a ∈ W i, ∃ b ∈ W j, f = a * b := by
  obtain ⟨a, ha, hab⟩ := exists_mem_inv_mul_mem_of_relIndex_le (hL.le i)
    (by rw [hL.relIndex_V, hL.relIndex_W hij]) hf
  exact ⟨a, ha, a⁻¹ * f, hab, by group⟩

private def Psi (W : Fin 4 → Subgroup G) (v v' : G) : Prop :=
  ∃ u ∈ W 1, v * u ∈ W 3 ∧ v' * u ∈ W 2

private theorem psi_exists {v : G} (hv : v ∈ W 0) : ∃ v' ∈ W 0, Psi W v v' := by
  obtain ⟨a, ha, b, hb, hvab⟩ := hL.exists_mul (i := 1) (j := 3) (by decide) (hL.le 0 hv)
  have haV := hL.le 1 ha
  obtain ⟨c, hc, d, hd, had⟩ := hL.exists_mul (i := 0) (j := 2) (by decide) haV
  refine ⟨c, hc, a⁻¹, (W 1).inv_mem ha, ?_, ?_⟩
  · have : v * a⁻¹ = b := by
      rw [hvab, hL.comm haV (hL.le 3 hb)]
      group
    rw [this]
    exact hb
  · have hdV : d⁻¹ ∈ V := V.inv_mem (hL.le 2 hd)
    have : c * a⁻¹ = d⁻¹ := by
      calc c * a⁻¹ = c * d⁻¹ * c⁻¹ := by rw [had]; group
        _ = d⁻¹ * c * c⁻¹ := by rw [hL.comm (hL.le 0 hc) hdV]
        _ = d⁻¹ := by group
    rw [this]
    exact (W 2).inv_mem hd

omit [Finite G] in
private theorem psi_unique {v v' v'' : G} (hv' : v' ∈ W 0) (hv'' : v'' ∈ W 0)
    (h1 : Psi W v v') (h2 : Psi W v v'') : v'⁻¹ * v'' ∈ Z := by
  obtain ⟨u, hu, hvu, hv'u⟩ := h1
  obtain ⟨u', hu', hvu', hv''u'⟩ := h2
  have huu : u⁻¹ * u' ∈ Z := by
    have h3 : u⁻¹ * u' = (v * u)⁻¹ * (v * u') := by group
    have h4 : u⁻¹ * u' ∈ W 1 ⊓ W 3 :=
      ⟨(W 1).mul_mem ((W 1).inv_mem hu) hu', h3 ▸ (W 3).mul_mem ((W 3).inv_mem hvu) hvu'⟩
    rwa [hL.inf 1 3 (by decide)] at h4
  have hX : v'⁻¹ * v'' ∈ V := V.mul_mem (V.inv_mem (hL.le 0 hv')) (hL.le 0 hv'')
  have hc := hL.comm hX (hL.le 1 hu)
  have h5 : v'⁻¹ * v'' = (v' * u)⁻¹ * (v'' * u') * (u⁻¹ * u')⁻¹ := by
    calc v'⁻¹ * v'' = u⁻¹ * (v'⁻¹ * v'' * u) := by rw [hc]; group
      _ = (v' * u)⁻¹ * (v'' * u') * (u⁻¹ * u')⁻¹ := by group
  have h6 : v'⁻¹ * v'' ∈ W 0 ⊓ W 2 := ⟨(W 0).mul_mem ((W 0).inv_mem hv') hv'',
    h5 ▸ (W 2).mul_mem ((W 2).mul_mem ((W 2).inv_mem hv'u) hv''u')
      ((W 2).inv_mem (hL.Z_le 2 huu))⟩
  rwa [hL.inf 0 2 (by decide)] at h6

omit [Finite G] hL in
private theorem psi_conj {n : G} (hnW : ∀ i, n ∈ normalizer ((W i : Subgroup G) : Set G))
    {v v' : G} (h : Psi W v v') : Psi W (n⁻¹ * v * n) (n⁻¹ * v' * n) := by
  obtain ⟨u, hu, h1, h2⟩ := h
  have hc : ∀ i, ∀ w ∈ W i, n⁻¹ * w * n ∈ W i := fun i w hw => by
    simpa using (mem_normalizer_iff.mp (inv_mem (hnW i)) w).mp hw
  refine ⟨n⁻¹ * u * n, hc 1 u hu, ?_, ?_⟩
  · have : n⁻¹ * v * n * (n⁻¹ * u * n) = n⁻¹ * (v * u) * n := by group
    rw [this]
    exact hc 3 _ h1
  · have : n⁻¹ * v' * n * (n⁻¹ * u * n) = n⁻¹ * (v' * u) * n := by group
    rw [this]
    exact hc 2 _ h2

omit [Finite G] in
private theorem psi_congr {v v' w w' : G} (hv : v ∈ V) (hv' : v' ∈ V) (hw : w ∈ V)
    (hw' : w' ∈ V) (h : Psi W v v') (hvw : v⁻¹ * w ∈ Z) (hvw' : v'⁻¹ * w' ∈ Z) :
    Psi W w w' := by
  obtain ⟨u, hu, h1, h2⟩ := h
  have huV := hL.le 1 hu
  refine ⟨u, hu, ?_, ?_⟩
  · have : w * u = v * u * (v⁻¹ * w) := by
      calc w * u = u * w := hL.comm hw huV
        _ = u * v * (v⁻¹ * w) := by group
        _ = v * u * (v⁻¹ * w) := by rw [hL.comm huV hv]
    rw [this]
    exact (W 3).mul_mem h1 (hL.Z_le 3 hvw)
  · have : w' * u = v' * u * (v'⁻¹ * w') := by
      calc w' * u = u * w' := hL.comm hw' huV
        _ = u * v' * (v'⁻¹ * w') := by group
        _ = v' * u * (v'⁻¹ * w') := by rw [hL.comm huV hv']
    rw [this]
    exact (W 2).mul_mem h2 (hL.Z_le 2 hvw')

omit [Finite G] in
private theorem psi_mul {a a' b b' : G} (hb : b ∈ V) (hb' : b' ∈ V) (h1 : Psi W a a')
    (h2 : Psi W b b') : Psi W (a * b) (a' * b') := by
  obtain ⟨u, hu, hau, ha'u⟩ := h1
  obtain ⟨u', hu', h3, h4⟩ := h2
  have huV := hL.le 1 hu
  refine ⟨u * u', (W 1).mul_mem hu hu', ?_, ?_⟩
  · have : a * b * (u * u') = (a * u) * (b * u') := by
      calc a * b * (u * u') = a * (b * u) * u' := by group
        _ = a * (u * b) * u' := by rw [hL.comm hb huV]
        _ = (a * u) * (b * u') := by group
    rw [this]
    exact (W 3).mul_mem hau h3
  · have : a' * b' * (u * u') = (a' * u) * (b' * u') := by
      calc a' * b' * (u * u') = a' * (b' * u) * u' := by group
        _ = a' * (u * b') * u' := by rw [hL.comm hb' huV]
        _ = (a' * u) * (b' * u') := by group
    rw [this]
    exact (W 2).mul_mem ha'u h4

omit [Finite G] in
private theorem psi_ne {v v' : G} (hv : v ∈ W 0) (hvZ : v ∉ Z) (hv' : v' ∈ W 0)
    (h : Psi W v v') : v' ∉ Z ∧ v⁻¹ * v' ∉ Z := by
  obtain ⟨u, hu, h1, h2⟩ := h
  have hvV := hL.le 0 hv
  have huV := hL.le 1 hu
  constructor
  · intro hv'Z
    have hu2 : u ∈ W 2 := by
      have : u = v'⁻¹ * (v' * u) := by group
      rw [this]
      exact (W 2).mul_mem ((W 2).inv_mem (hL.Z_le 2 hv'Z)) h2
    have huZ : u ∈ Z := by
      have : u ∈ W 1 ⊓ W 2 := ⟨hu, hu2⟩
      rwa [hL.inf 1 2 (by decide)] at this
    have hv3 : v ∈ W 3 := by
      have : v = v * u * u⁻¹ := by group
      rw [this]
      exact (W 3).mul_mem h1 ((W 3).inv_mem (hL.Z_le 3 huZ))
    have : v ∈ W 0 ⊓ W 3 := ⟨hv, hv3⟩
    rw [hL.inf 0 3 (by decide)] at this
    exact hvZ this
  · intro hvv'
    have hv'V : v'⁻¹ ∈ V := V.inv_mem (hL.le 0 hv')
    have h3 : v * u ∈ W 2 := by
      have : v * u = v' * u * (v⁻¹ * v')⁻¹ := by
        calc v * u = u * v := hL.comm hvV huV
          _ = v' * (v'⁻¹ * u) * v := by group
          _ = v' * (u * v'⁻¹) * v := by rw [hL.comm huV hv'V]
          _ = v' * u * (v⁻¹ * v')⁻¹ := by group
      rw [this]
      exact (W 2).mul_mem h2 ((W 2).inv_mem (hL.Z_le 2 hvv'))
    have h4 : v * u ∈ Z := by
      have : v * u ∈ W 2 ⊓ W 3 := ⟨h3, h1⟩
      rwa [hL.inf 2 3 (by decide)] at this
    have hv1 : v ∈ W 1 := by
      have : v = v * u * u⁻¹ := by group
      rw [this]
      exact (W 1).mul_mem (hL.Z_le 1 h4) ((W 1).inv_mem hu)
    have : v ∈ W 0 ⊓ W 1 := ⟨hv, hv1⟩
    rw [hL.inf 0 1 (by decide)] at this
    exact hvZ this

omit [Finite G] in
private theorem psi_not_swap {a b : G} (ha : a ∈ W 0) (haZ : a ∉ Z) (hb : b ∈ W 0)
    (h1 : Psi W a b) (h2 : Psi W b a) : False := by
  have hab := (psi_ne hL ha haZ hb h1).2
  obtain ⟨u, hu, hau, hbu⟩ := h1
  obtain ⟨u', hu', hbu', hau'⟩ := h2
  have haV := hL.le 0 ha
  have hbV := hL.le 0 hb
  have huV := hL.le 1 hu
  have hu'V := hL.le 1 hu'
  have heq : a * u * (b * u') = b * u * (a * u') := by
    calc a * u * (b * u') = a * (u * b) * u' := by group
      _ = a * (b * u) * u' := by rw [hL.comm huV hbV]
      _ = (a * b) * u * u' := by group
      _ = (b * a) * u * u' := by rw [hL.comm haV hbV]
      _ = b * (a * u) * u' := by group
      _ = b * (u * a) * u' := by rw [hL.comm haV huV]
      _ = b * u * (a * u') := by group
  have h3 : a * u * (b * u') ∈ Z := by
    have : a * u * (b * u') ∈ W 2 ⊓ W 3 :=
      ⟨heq ▸ (W 2).mul_mem hbu hau', (W 3).mul_mem hau hbu'⟩
    rwa [hL.inf 2 3 (by decide)] at this
  have h4 : a * b ∈ W 1 := by
    have : a * b = a * u * (b * u') * (u * u')⁻¹ := by
      calc a * b = a * (b * u) * u' * (u * u')⁻¹ := by group
        _ = a * (u * b) * u' * (u * u')⁻¹ := by rw [hL.comm hbV huV]
        _ = a * u * (b * u') * (u * u')⁻¹ := by group
    rw [this]
    exact (W 1).mul_mem (hL.Z_le 1 h3) ((W 1).inv_mem ((W 1).mul_mem hu hu'))
  have h5 : a * b ∈ Z := by
    have : a * b ∈ W 0 ⊓ W 1 := ⟨(W 0).mul_mem ha hb, h4⟩
    rwa [hL.inf 0 1 (by decide)] at this
  apply hab
  rw [hL.inv_eq haV]
  exact h5

theorem forall_mem_of_fix {n : G} (hnZ : n ∈ normalizer (Z : Set G))
    (hnW : ∀ i, n ∈ normalizer ((W i : Subgroup G) : Set G)) {v : G} (hv : v ∈ W 0)
    (hvZ : v ∉ Z) (hfix : v⁻¹ * (n⁻¹ * v * n) ∈ Z) : ∀ f ∈ V, f⁻¹ * (n⁻¹ * f * n) ∈ Z := by
  have hc : ∀ i, ∀ w ∈ W i, n⁻¹ * w * n ∈ W i := fun i w hw => by
    simpa using (mem_normalizer_iff.mp (inv_mem (hnW i)) w).mp hw
  have hcZ : ∀ z ∈ Z, n⁻¹ * z * n ∈ Z := fun z hz => by
    simpa using (mem_normalizer_iff.mp (inv_mem hnZ) z).mp hz
  have hvV := hL.le 0 hv
  have hFmul : ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * (n⁻¹ * a * n) ∈ Z → b⁻¹ * (n⁻¹ * b * n) ∈ Z →
      (a * b)⁻¹ * (n⁻¹ * (a * b) * n) ∈ Z := by
    intro a ha b hb h1 h2
    have hcV : ∀ w ∈ V, n⁻¹ * w * n ∈ V := fun w hw => by
      obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := hL.exists_mul (i := 0) (j := 1) (by decide) hw
      have : n⁻¹ * (w₀ * w₁) * n = (n⁻¹ * w₀ * n) * (n⁻¹ * w₁ * n) := by group
      rw [this]
      exact V.mul_mem (hL.le 0 (hc 0 _ hw₀)) (hL.le 1 (hc 1 _ hw₁))
    have := hL.inv_mul_mul_mem ha hb (hcV a ha) h1 h2
    have e : n⁻¹ * (a * b) * n = (n⁻¹ * a * n) * (n⁻¹ * b * n) := by group
    rwa [e]
  have hFZ : ∀ z ∈ Z, z⁻¹ * (n⁻¹ * z * n) ∈ Z := fun z hz => Z.mul_mem (Z.inv_mem hz) (hcZ z hz)
  have hFcos : ∀ a ∈ V, ∀ w ∈ V, a⁻¹ * (n⁻¹ * a * n) ∈ Z → a⁻¹ * w ∈ Z →
      w⁻¹ * (n⁻¹ * w * n) ∈ Z := fun a ha w hw h1 h2 => by
    have h3 := hFmul a ha (a⁻¹ * w) (V.mul_mem (V.inv_mem ha) hw) h1 (hFZ _ h2)
    rwa [mul_inv_cancel_left] at h3
  obtain ⟨v₁, hv₁, hψ⟩ := psi_exists hL hv
  obtain ⟨hv₁Z, hvv₁⟩ := psi_ne hL hv hvZ hv₁ hψ
  have hv₁V := hL.le 0 hv₁
  have hψ' := psi_conj hnW hψ
  have hψ'' : Psi W v (n⁻¹ * v₁ * n) := psi_congr hL (hL.le 0 (hc 0 v hv))
    (hL.le 0 (hc 0 v₁ hv₁)) hvV (hL.le 0 (hc 0 v₁ hv₁)) hψ'
    (by have := Z.inv_mem hfix; rwa [mul_inv_rev, inv_inv] at this)
    (by rw [inv_mul_cancel]; exact Z.one_mem)
  have hfix₁ : v₁⁻¹ * (n⁻¹ * v₁ * n) ∈ Z :=
    psi_unique hL hv₁ (hc 0 v₁ hv₁) hψ hψ''
  have hvv₁' : v * v₁ ∉ Z := fun h => hvv₁ (by rw [hL.inv_eq hvV]; exact h)
  have hW0 : ∀ w ∈ W 0, w⁻¹ * (n⁻¹ * w * n) ∈ Z := by
    intro w hw
    have hwV := hL.le 0 hw
    have h12 : v⁻¹ * (v * v₁) ∉ Z := by rw [inv_mul_cancel_left]; exact hv₁Z
    have h13 : v₁⁻¹ * (v * v₁) ∉ Z := by
      rw [hL.comm hvV hv₁V, inv_mul_cancel_left]
      exact hvZ
    rcases mem_or_of_relIndex_eq_four (hL.relIndex_Z 0) hv hv₁ ((W 0).mul_mem hv hv₁) hw hvZ
      hv₁Z hvv₁' hvv₁ h12 h13 with h | h | h | h
    · exact hFZ w h
    · exact hFcos v hvV w hwV hfix h
    · exact hFcos v₁ hv₁V w hwV hfix₁ h
    · exact hFcos (v * v₁) (V.mul_mem hvV hv₁V) w hwV (hFmul v hvV v₁ hv₁V hfix hfix₁) h
  have hW1 : ∀ u ∈ W 1, u⁻¹ * (n⁻¹ * u * n) ∈ Z := by
    intro u hu
    have huV := hL.le 1 hu
    obtain ⟨c, hc0, d, hd, hcd⟩ := hL.exists_mul (i := 0) (j := 2) (by decide) (V.inv_mem huV)
    have hcV := hL.le 0 hc0
    have hdV := hL.le 2 hd
    have hcu : c * u ∈ W 2 := by
      have : c * u = d⁻¹ := by
        have hu' : u = (c * d)⁻¹ := by rw [← hcd, inv_inv]
        calc c * u = c * d⁻¹ * c⁻¹ := by rw [hu']; group
          _ = d⁻¹ * c * c⁻¹ := by rw [hL.comm hcV (V.inv_mem hdV)]
          _ = d⁻¹ := by group
      rw [this]
      exact (W 2).inv_mem hd
    have h1 : (n⁻¹ * c * n) * (n⁻¹ * u * n) ∈ W 2 := by
      have := hc 2 _ hcu
      have e : n⁻¹ * (c * u) * n = (n⁻¹ * c * n) * (n⁻¹ * u * n) := by group
      rwa [e] at this
    have hfc := hW0 c hc0
    set c' := n⁻¹ * c * n with hc'
    set u' := n⁻¹ * u * n with hu'
    have hc'V : c' ∈ V := hL.le 0 (hc 0 c hc0)
    have hu'V : u' ∈ V := hL.le 1 (hc 1 u hu)
    have hcomm := hL.comm hu'V (V.mul_mem (V.inv_mem hc'V) hcV)
    have h2 : u⁻¹ * u' = (c * u)⁻¹ * (c' * u') * (c⁻¹ * c')⁻¹ := by
      calc u⁻¹ * u' = u⁻¹ * (c⁻¹ * c' * ((c'⁻¹ * c) * u')) := by group
        _ = u⁻¹ * (c⁻¹ * c' * (u' * (c'⁻¹ * c))) := by rw [hcomm]
        _ = (c * u)⁻¹ * (c' * u') * (c⁻¹ * c')⁻¹ := by group
    have h3 : u⁻¹ * u' ∈ W 1 ⊓ W 2 := ⟨(W 1).mul_mem ((W 1).inv_mem hu) (hc 1 u hu),
      h2 ▸ (W 2).mul_mem ((W 2).mul_mem ((W 2).inv_mem hcu) h1) ((W 2).inv_mem (hL.Z_le 2 hfc))⟩
    rwa [hL.inf 1 2 (by decide)] at h3
  intro f hf
  obtain ⟨a, ha, b, hb, rfl⟩ := hL.exists_mul (i := 0) (j := 1) (by decide) hf
  exact hFmul a (hL.le 0 ha) b (hL.le 1 hb) (hW0 a ha) (hW1 b hb)

theorem forall_mem_cube {n : G} (hnZ : n ∈ normalizer (Z : Set G))
    (hnW : ∀ i, n ∈ normalizer ((W i : Subgroup G) : Set G)) :
    ∀ f ∈ V, f⁻¹ * ((n ^ 3)⁻¹ * f * n ^ 3) ∈ Z := by
  have hc : ∀ i, ∀ w ∈ W i, n⁻¹ * w * n ∈ W i := fun i w hw => by
    simpa using (mem_normalizer_iff.mp (inv_mem (hnW i)) w).mp hw
  have hcZ : ∀ z ∈ Z, n⁻¹ * z * n ∈ Z := fun z hz => by
    simpa using (mem_normalizer_iff.mp (inv_mem hnZ) z).mp hz
  have hcong : ∀ a b : G, a⁻¹ * b ∈ Z → (n⁻¹ * a * n)⁻¹ * (n⁻¹ * b * n) ∈ Z := fun a b h => by
    have e : (n⁻¹ * a * n)⁻¹ * (n⁻¹ * b * n) = n⁻¹ * (a⁻¹ * b) * n := by group
    rw [e]
    exact hcZ _ h
  have htrans : ∀ a b c : G, a⁻¹ * b ∈ Z → b⁻¹ * c ∈ Z → a⁻¹ * c ∈ Z := fun a b c h1 h2 => by
    have := Z.mul_mem h1 h2
    rwa [mul_assoc, mul_inv_cancel_left] at this
  have hsymm : ∀ a b : G, a⁻¹ * b ∈ Z → b⁻¹ * a ∈ Z := fun a b h => by
    have := Z.inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  have hrefl : ∀ a : G, a⁻¹ * a ∈ Z := fun a => by rw [inv_mul_cancel]; exact Z.one_mem
  obtain ⟨v, hv, hvZ⟩ : ∃ v ∈ W 0, v ∉ Z := by
    by_contra hno
    push Not at hno
    have h := Subgroup.card_le_of_le (show W 0 ≤ Z from hno)
    rw [hL.cardW, hL.cardZ] at h
    omega
  have hvV := hL.le 0 hv
  obtain ⟨v₁, hv₁, hψ⟩ := psi_exists hL hv
  obtain ⟨hv₁Z, hvv₁⟩ := psi_ne hL hv hvZ hv₁ hψ
  have hv₁V := hL.le 0 hv₁
  set v₂ := v * v₁ with hv₂
  have hv₂W : v₂ ∈ W 0 := (W 0).mul_mem hv hv₁
  have hv₂V := hL.le 0 hv₂W
  have hv₂Z : v₂ ∉ Z := fun h => hvv₁ (by rw [hL.inv_eq hvV]; exact h)
  have h12 : v⁻¹ * v₂ ∉ Z := by rw [hv₂, inv_mul_cancel_left]; exact hv₁Z
  have h13 : v₁⁻¹ * v₂ ∉ Z := by rw [hv₂, hL.comm hvV hv₁V, inv_mul_cancel_left]; exact hvZ
  have hψ₁ : Psi W v₁ v₂ := by
    obtain ⟨w, hw, hψw⟩ := psi_exists hL hv₁
    obtain ⟨hwZ, hv₁w⟩ := psi_ne hL hv₁ hv₁Z hw hψw
    have hwV := hL.le 0 hw
    have hvw : v⁻¹ * w ∉ Z := fun h => psi_not_swap hL hv hvZ hv₁ hψ
      (psi_congr hL hv₁V hwV hv₁V hvV hψw (hrefl v₁) (hsymm _ _ h))
    rcases mem_or_of_relIndex_eq_four (hL.relIndex_Z 0) hv hv₁ hv₂W hw hvZ hv₁Z hv₂Z hvv₁ h12
      h13 with h | h | h | h
    · exact absurd h hwZ
    · exact absurd h hvw
    · exact absurd h hv₁w
    · exact psi_congr hL hv₁V hwV hv₁V hv₂V hψw (hrefl v₁) (hsymm _ _ h)
  have e₁ : v₁ * v₂ = v := by
    rw [hv₂, ← mul_assoc, hL.comm hv₁V hvV, mul_assoc, hL.mul_self hv₁V, mul_one]
  have e₂ : v₂ * v = v₁ := by
    rw [hv₂, hL.comm hvV hv₁V, mul_assoc, hL.mul_self hvV, mul_one]
  have hψ₂ : Psi W v₂ v := by
    have h := psi_mul hL hv₁V hv₂V hψ hψ₁
    rwa [e₁] at h
  have hcv := hc 0 v hv
  have hcv₁ := hc 0 v₁ hv₁
  have hcvZ : n⁻¹ * v * n ∉ Z := fun h => hvZ (by
    have := (mem_normalizer_iff.mp hnZ _).mp h
    simpa [mul_assoc] using this)
  have hψc := psi_conj hnW hψ
  have hcv₂ : n⁻¹ * v₂ * n = (n⁻¹ * v * n) * (n⁻¹ * v₁ * n) := by rw [hv₂]; group
  have hfix : v⁻¹ * ((n ^ 3)⁻¹ * v * n ^ 3) ∈ Z := by
    have hpow : (n ^ 3)⁻¹ * v * n ^ 3 = n⁻¹ * (n⁻¹ * (n⁻¹ * v * n) * n) * n := by
      rw [pow_three]
      group
    rw [hpow]
    rcases mem_or_of_relIndex_eq_four (hL.relIndex_Z 0) hv hv₁ hv₂W hcv hvZ hv₁Z hv₂Z hvv₁ h12
      h13 with h | h | h | h
    · exact absurd h hcvZ
    · exact htrans _ _ _ (htrans _ _ _ h (hcong _ _ h)) (hcong _ _ (hcong _ _ h))
    ·
      have hA : Psi W v₁ (n⁻¹ * v₁ * n) := psi_congr hL (hL.le 0 hcv) (hL.le 0 hcv₁) hv₁V
        (hL.le 0 hcv₁) hψc (hsymm _ _ h) (hrefl _)
      have hB : v₂⁻¹ * (n⁻¹ * v₁ * n) ∈ Z := psi_unique hL hv₂W hcv₁ hψ₁ hA
      have hC : v⁻¹ * (n⁻¹ * v₂ * n) ∈ Z := by
        rw [hcv₂]
        have := hL.inv_mul_mul_mem hv₁V hv₂V (hL.le 0 hcv) h hB
        rwa [e₁] at this
      have h1 : v₂⁻¹ * (n⁻¹ * (n⁻¹ * v * n) * n) ∈ Z := htrans _ _ _ hB (hcong _ _ h)
      exact htrans _ _ _ hC (hcong _ _ h1)
    ·
      have hA : Psi W v₂ (n⁻¹ * v₁ * n) := psi_congr hL (hL.le 0 hcv) (hL.le 0 hcv₁) hv₂V
        (hL.le 0 hcv₁) hψc (hsymm _ _ h) (hrefl _)
      have hB : v⁻¹ * (n⁻¹ * v₁ * n) ∈ Z := psi_unique hL hv hcv₁ hψ₂ hA
      have hC : v₁⁻¹ * (n⁻¹ * v₂ * n) ∈ Z := by
        rw [hcv₂]
        have := hL.inv_mul_mul_mem hv₂V hvV (hL.le 0 hcv) h hB
        rwa [e₂] at this
      have h1 : v₁⁻¹ * (n⁻¹ * (n⁻¹ * v * n) * n) ∈ Z := htrans _ _ _ hC (hcong _ _ h)
      exact htrans _ _ _ hB (hcong _ _ h1)
  exact hL.forall_mem_of_fix (pow_mem hnZ 3) (fun i => pow_mem (hnW i) 3) hv hvZ hfix

theorem forall_mem_of_pow_two {n : G} (hnZ : n ∈ normalizer (Z : Set G))
    (hnW : ∀ i, n ∈ normalizer ((W i : Subgroup G) : Set G)) {m : ℕ} (hm : n ^ 2 ^ m = 1) :
    ∀ f ∈ V, f⁻¹ * (n⁻¹ * f * n) ∈ Z := by
  set C := centralizerMod ⊤ V Z with hC
  have h3 : n ^ 3 ∈ C := mem_centralizerMod.mpr ⟨mem_top _, pow_mem hnZ 3, fun f hf => by
    have := hL.forall_mem_cube hnZ hnW f hf
    simpa [mul_assoc] using this⟩
  have h2 : n ^ 2 ^ m ∈ C := by rw [hm]; exact C.one_mem
  have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  have hab := Nat.gcd_eq_gcd_ab 3 (2 ^ m)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hab
  have hn : n = (n ^ 3) ^ (Nat.gcdA 3 (2 ^ m)) * (n ^ 2 ^ m) ^ (Nat.gcdB 3 (2 ^ m)) := by
    rw [← zpow_natCast n 3, ← zpow_natCast n (2 ^ m), ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← hab, zpow_one]
  have hnC : n ∈ C := by
    rw [hn]
    exact C.mul_mem (C.zpow_mem h3 _) (C.zpow_mem h2 _)
  intro f hf
  have := (mem_centralizerMod.mp hnC).2.2 f hf
  simpa [mul_assoc] using this

end FourLines

open scoped IsMulCommutative in
theorem eq_one_of_mem_ker_of_pow_prime {Γ A : Type*} [Group Γ] [Finite Γ] [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hgen : closure {g : Γ | ∃ k : ℕ, g ^ 2 ^ k = 1} = ⊤) (f : Γ →* A)
    (hsq : ¬ p ^ 2 ∣ Nat.card f.range)
    (hcen : ∀ m ∈ f.ker, (∃ k : ℕ, m ^ p ^ k = 1) → m ∈ center Γ)
    {z : Γ} (hz : z ∈ f.ker) (hzp : ∃ k : ℕ, z ^ p ^ k = 1) : z = 1 := by
  obtain ⟨Q⟩ : Nonempty (Sylow p Γ) := inferInstance
  have hgen0 : ∃ q₀ ∈ Q, ∀ a ∈ Q, ∃ i : ℤ, f q₀ ^ i = f a := by
    have hQp : IsPGroup p (Q.map f) := Q.isPGroup'.map f
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hdvd : Nat.card (Q.map f) ∣ Nat.card f.range :=
      Subgroup.card_dvd_of_le (map_le_range f (Q : Subgroup Γ))
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      apply hsq
      exact (pow_dvd_pow p hk2).trans (hk ▸ hdvd)
    interval_cases k
    · rw [pow_zero, Subgroup.card_eq_one] at hk
      refine ⟨1, Q.one_mem, fun a ha => ⟨0, ?_⟩⟩
      have : f a ∈ Q.map f := mem_map_of_mem f ha
      rw [hk, mem_bot] at this
      rw [zpow_zero, this]
    · rw [pow_one] at hk
      have := isCyclic_of_prime_card hk
      obtain ⟨⟨g₀, hg₀⟩, hgen1⟩ := IsCyclic.exists_generator (α := Q.map f)
      obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hg₀
      refine ⟨q₀, hq₀, fun a ha => ?_⟩
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hgen1 ⟨f a, mem_map_of_mem f ha⟩)
      exact ⟨i, by simpa using congrArg Subtype.val hi⟩
  obtain ⟨q₀, hq₀, hq₀gen⟩ := hgen0
  have hrep : ∀ a ∈ Q, ∃ i : ℤ, ∃ c ∈ center Γ, a = q₀ ^ i * c := by
    intro a ha
    obtain ⟨i, hi⟩ := hq₀gen a ha
    have hmem : (q₀ ^ i)⁻¹ * a ∈ Q := Q.mul_mem (Q.inv_mem (Q.zpow_mem hq₀ i)) ha
    refine ⟨i, (q₀ ^ i)⁻¹ * a, hcen _ ?_ ?_, by group⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hi, inv_mul_cancel]
    · obtain ⟨k, hk⟩ := Q.isPGroup' ⟨_, hmem⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, c, hc, rfl⟩ := hrep a ha
    obtain ⟨j, d, hd, rfl⟩ := hrep b hb
    rw [mem_center_iff] at hc hd
    have e1 : q₀ ^ i * c * (q₀ ^ j * d) = q₀ ^ i * q₀ ^ j * (c * d) := by
      rw [mul_assoc (q₀ ^ i) c, ← mul_assoc c, (hc (q₀ ^ j)).symm]
      simp only [mul_assoc]
    have e2 : q₀ ^ j * d * (q₀ ^ i * c) = q₀ ^ j * q₀ ^ i * (d * c) := by
      rw [mul_assoc (q₀ ^ j) d, ← mul_assoc d, (hd (q₀ ^ i)).symm]
      simp only [mul_assoc]
    rw [e1, e2, zpow_mul_comm, hc d]
  have : IsMulCommutative Q := ⟨⟨fun a b => Subtype.ext (hQcomm a a.2 b b.2)⟩⟩
  have hT : ∀ g : Γ, MonoidHom.transfer (MonoidHom.id Q) g = 1 := by
    have hle : closure {g : Γ | ∃ k : ℕ, g ^ 2 ^ k = 1} ≤
        (MonoidHom.transfer (MonoidHom.id Q)).ker := by
      rw [closure_le]
      rintro g ⟨k, hk⟩
      have h1 : (MonoidHom.transfer (MonoidHom.id Q) g) ^ 2 ^ k = 1 := by
        rw [← map_pow, hk, map_one]
      obtain ⟨l, hl⟩ := Q.isPGroup' (MonoidHom.transfer (MonoidHom.id Q) g)
      have hcop : Nat.Coprime (2 ^ k) (p ^ l) := Nat.Coprime.pow _ _
        ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
      have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hl)
      rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    intro g
    exact hle (hgen ▸ mem_top g)
  have hkey : ∀ (k : ℕ) (g₀ : Γ), g₀⁻¹ * z ^ k * g₀ ∈ Q → g₀⁻¹ * z ^ k * g₀ = z ^ k :=
    fun k g₀ _ => by
      have hzc := mem_center_iff.mp (pow_mem (hcen z hz hzp) k) g₀
      rw [mul_assoc, ← hzc, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id Q) z hkey
  rw [hT z] at h1
  have hzi : z ^ (Q : Subgroup Γ).index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  obtain ⟨k, hk⟩ := hzp
  have hcop : Nat.Coprime (Q : Subgroup Γ).index (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr Q.not_dvd_index).symm
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzi) (orderOf_dvd_of_pow_eq_one hk)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

end Sec2

end CFSG.ComponentClassification.AS81
