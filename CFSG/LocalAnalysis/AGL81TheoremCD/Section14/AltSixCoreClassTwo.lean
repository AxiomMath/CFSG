module

public import Mathlib.GroupTheory.Sylow
import CFSG.Foundations.MaxOrderThompson
import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

open Subgroup
open scoped commutatorElement

theorem map_center_subtype_eq_inf_centralizer {G : Type*} [Group G] (D : Subgroup G) :
    (Subgroup.center ↥D).map D.subtype = D ⊓ Subgroup.centralizer (D : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)⟩
  · rintro ⟨hxD, hxcent⟩
    exact ⟨⟨x, hxD⟩,
      Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcent y y.2),
      rfl⟩

variable {G : Type*} [Group G] [Finite G]

private theorem commutator_le_center_of_mem_center {D : Type*} [Group D]
    (hclass : ∀ x y : D, ⁅x, y⁆ ∈ Subgroup.center D) :
    commutator D ≤ Subgroup.center D := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  exact fun x _ y _ => hclass x y

private theorem exists_card_pow_relation {r : ℕ} [Fact r.Prime] {D : Type*} [Group D]
    [Finite D] {B Z : Subgroup D} (hBp : IsPGroup r B) (hZp : IsPGroup r Z) (hZB : Z ≤ B)
    {k : ℕ} (hBcard : Nat.card B = Nat.card Z * r ^ (k + 1)) :
    ∃ b z : ℕ, Nat.card B = r ^ b ∧ Nat.card Z = r ^ z ∧
      b = z + (k + 1) ∧ z ≤ b - 1 := by
  obtain ⟨b, hb⟩ := hBp.exists_card_eq
  obtain ⟨z, hz⟩ := hZp.exists_card_eq
  have hzb : z ≤ b := by
    rw [← Nat.pow_le_pow_iff_right (Fact.out : r.Prime).one_lt, ← hz, ← hb]
    exact Subgroup.card_le_of_le hZB
  have hb_eq : b = z + (k + 1) := by
    have h := hBcard
    rw [hb, hz, ← pow_add] at h
    exact Nat.pow_right_injective (Fact.out : r.Prime).two_le h
  exact ⟨b, z, hb, hz, hb_eq, by omega⟩

private theorem exists_subgroup_lt_card_mul_pow {r : ℕ} [Fact r.Prime] {D : Type*}
    [Group D] [Finite D] {B Z : Subgroup D} (hBp : IsPGroup r B) (hZp : IsPGroup r Z)
    (hZB : Z ≤ B) {k : ℕ} (hBcard : Nat.card B = Nat.card Z * r ^ (k + 1)) :
    ∃ K : Subgroup D, Z ≤ K ∧ K < B ∧ Nat.card K = Nat.card Z * r ^ k := by
  classical
  obtain ⟨b, z, hb, hz, hb_eq, hzle⟩ := exists_card_pow_relation hBp hZp hZB hBcard
  have hdvd : r ^ (b - 1) ∣ Nat.card B := by
    rw [hb]
    exact Nat.pow_dvd_pow r (by omega)
  have hZsubcard : Nat.card (Z.subgroupOf B) = r ^ z := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv, hz]
  obtain ⟨K', hK'card, hZK'⟩ := Sylow.exists_subgroup_card_pow_prime_le (p := r)
    (n := z) (m := b - 1) hdvd (Z.subgroupOf B) hZsubcard hzle
  let K : Subgroup D := K'.map B.subtype
  have hKB : K ≤ B := Subgroup.map_subtype_le K'
  have hZK : Z ≤ K := by
    intro y hy
    exact ⟨⟨y, hZB hy⟩, hZK' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hKpow : Nat.card K = r ^ (z + k) := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hK'card,
      show b - 1 = z + k by omega]
  have hKcard : Nat.card K = Nat.card Z * r ^ k := by
    rw [hKpow, hz, ← pow_add]
  have hKltB : K < B := by
    refine lt_of_le_of_ne hKB ?_
    intro hEq
    have hcardEq : Nat.card K = Nat.card B := by rw [hEq]
    rw [hKpow, hb, hb_eq] at hcardEq
    have := Nat.pow_right_injective (Fact.out : r.Prime).two_le hcardEq
    omega
  exact ⟨K, hZK, hKltB, hKcard⟩

private theorem relIndex_eq_of_card_eq_mul {r : ℕ} [Fact r.Prime] {D : Type*} [Group D]
    [Finite D] {B K : Subgroup D} (hKB : K ≤ B) (hcard : Nat.card B = r * Nat.card K) :
    K.relIndex B = r := by
  have h1 := Subgroup.relIndex_mul_card (H := K) (K := B)
  rw [inf_of_le_left hKB, hcard] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

private theorem eq_sup_zpowers_of_relIndex_prime {r : ℕ} [Fact r.Prime] {D : Type*}
    [Group D] {B K : Subgroup D} (hKB : K ≤ B) (hKrel : K.relIndex B = r)
    {x : D} (hxB : x ∈ B) (hxK : x ∉ K) :
    K ⊔ Subgroup.zpowers x = B := by
  let H : Subgroup D := K ⊔ Subgroup.zpowers x
  have hHleB : H ≤ B := sup_le hKB (Subgroup.zpowers_le.mpr hxB)
  have hKH : K ≤ H := le_sup_left
  have hKltH : K < H := by
    refine lt_of_le_of_ne hKH ?_
    intro hEq
    exact hxK (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hprod := Subgroup.relIndex_mul_relIndex K H B hKH hHleB
  rw [hKrel] at hprod
  have hdvd : H.relIndex B ∣ r :=
    ⟨K.relIndex H, by rw [mul_comm]; exact hprod.symm⟩
  have hHrel_one : H.relIndex B = 1 := by
    rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp hdvd with h | h
    · exact h
    · exfalso
      rw [h] at hprod
      have hKrelH : K.relIndex H = 1 :=
        Nat.eq_of_mul_eq_mul_right (Fact.out : r.Prime).pos (by simpa using hprod)
      exact hxK ((Subgroup.relIndex_eq_one.mp hKrelH)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  exact le_antisymm hHleB (Subgroup.relIndex_eq_one.mp hHrel_one)

private theorem centralizer_sup_zpowers_eq_inf {D : Type*} [Group D]
    (K : Subgroup D) (x : D) :
    Subgroup.centralizer ((K ⊔ Subgroup.zpowers x : Subgroup D) : Set D) =
      Subgroup.centralizer (K : Set D) ⊓ Subgroup.centralizer ({x} : Set D) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext d
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Or.inl hy), fun y hy => by
      rw [hy]
      exact h x (Or.inr (Subgroup.mem_zpowers x))⟩
  · rintro ⟨hK, hx⟩ y (hyK | hyZ)
    · exact hK y hyK
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyZ
      exact (Commute.zpow_right (show Commute d x from (hx x rfl).symm) n).eq.symm

private theorem index_centralizer_le_mul_of_lt {r : ℕ} [Fact r.Prime] {D : Type*}
    [Group D] {B K : Subgroup D} {x : D} {n : ℕ}
    (hKB : K ≤ B) (hKrel : K.relIndex B = r) (hxB : x ∈ B) (hxK : x ∉ K)
    (hKbound : (Subgroup.centralizer (K : Set D)).index ≤ n)
    (hxbound : (Subgroup.centralizer ({x} : Set D)).index ≤
      Nat.card (Subgroup.center D)) :
    (Subgroup.centralizer (B : Set D)).index ≤ n * Nat.card (Subgroup.center D) := by
  have hH : K ⊔ Subgroup.zpowers x = B :=
    eq_sup_zpowers_of_relIndex_prime hKB hKrel hxB hxK
  have hcent := centralizer_sup_zpowers_eq_inf K x
  have hstep : (Subgroup.centralizer (B : Set D)).index ≤
      (Subgroup.centralizer (K : Set D)).index *
        (Subgroup.centralizer ({x} : Set D)).index := by
    rw [← hH, hcent]
    exact Subgroup.index_inf_le
  exact hstep.trans (Nat.mul_le_mul hKbound hxbound)

private theorem centralizer_index_le_card_center {D : Type*}
    [Group D] [Finite D] (hclass : ∀ x y : D, ⁅x, y⁆ ∈ Subgroup.center D) {x : D} :
    (Subgroup.centralizer ({x} : Set D)).index ≤ Nat.card (Subgroup.center D) := by
  have hcomm : commutator D ≤ Subgroup.center D :=
    commutator_le_center_of_mem_center hclass
  have hZcent : Subgroup.center D ≤ Subgroup.centralizer ((⊤ : Subgroup D) : Set D) := by
    change Subgroup.center D ≤ Subgroup.centralizer (Set.univ : Set D)
    rw [Subgroup.centralizer_univ]
  have := CFSG.LocalAnalysis.EvenBN.Common.relIndex_inf_centralizer_le
    (D := (⊤ : Subgroup D)) (Z := Subgroup.center D) (A := ⊤) hcomm hZcent le_rfl
    (Subgroup.mem_top x)
  simpa [Subgroup.relIndex_top_right] using this

private theorem index_centralizer_le_pow_card_center {r : ℕ} [Fact r.Prime] {D : Type*}
    [Group D] [Finite D] (hexp : ∀ x : D, x ^ r = 1)
    (hclass : ∀ x y : D, ⁅x, y⁆ ∈ Subgroup.center D) :
    ∀ (B : Subgroup D), IsMulCommutative B → Subgroup.center D ≤ B → ∀ k : ℕ,
      Nat.card B = Nat.card (Subgroup.center D) * r ^ k →
      (Subgroup.centralizer (B : Set D)).index ≤ (Nat.card (Subgroup.center D)) ^ k := by
  have hDp : IsPGroup r D := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  intro B hB hZB k
  induction k generalizing B with
  | zero =>
      intro hBcard
      have hBZ : B = Subgroup.center D := by
        refine (Subgroup.eq_of_le_of_card_ge hZB ?_).symm
        rw [hBcard, pow_zero, mul_one]
      rw [hBZ, Subgroup.centralizer_center, Subgroup.index_top, pow_zero]
  | succ k ih =>
      intro hBcard
      obtain ⟨K, hZK, hKltB, hKcard⟩ := exists_subgroup_lt_card_mul_pow
        (hDp.to_subgroup B) (hDp.to_subgroup (Subgroup.center D)) hZB hBcard
      have hKrel : K.relIndex B = r := by
        apply relIndex_eq_of_card_eq_mul (le_of_lt hKltB)
        rw [hBcard, hKcard]
        ring
      obtain ⟨x, hxB, hxK⟩ := SetLike.exists_of_lt hKltB
      have hKabel : IsMulCommutative K :=
        ⟨⟨fun x y => Subtype.ext (by
          show (x : D) * (y : D) = (y : D) * (x : D)
          exact congrArg Subtype.val (hB.is_comm.comm
            ⟨x.1, le_of_lt hKltB x.2⟩ ⟨y.1, le_of_lt hKltB y.2⟩))⟩⟩
      calc (Subgroup.centralizer (B : Set D)).index
          ≤ (Nat.card (Subgroup.center D)) ^ k * Nat.card (Subgroup.center D) :=
            index_centralizer_le_mul_of_lt (le_of_lt hKltB) hKrel hxB hxK
              (ih K hKabel hZK hKcard) (centralizer_index_le_card_center hclass (x := x))
        _ = (Nat.card (Subgroup.center D)) ^ (k + 1) := by ring

private theorem pow_mul_add_le_four {z k : ℕ} (h : z + k ≤ 3) : z * k + k ≤ 4 := by
  have hk3 : k ≤ 3 := by omega
  interval_cases k <;> omega

private theorem center_index_le_pow_four {r : ℕ} [Fact r.Prime] {D : Type*} [Group D]
    [Finite D] {B : Subgroup D} {z k : ℕ} (hzk3 : z + k ≤ 3)
    (hBZcard : Nat.card B = Nat.card (Subgroup.center D) * r ^ k)
    (hInd : B.index ≤ r ^ (z * k)) :
    (Subgroup.center D).index ≤ r ^ 4 := by
  have hZidx : (Subgroup.center D).index = B.index * r ^ k := by
    have h1 := Subgroup.index_mul_card (H := B)
    have h2 := Subgroup.index_mul_card (H := Subgroup.center D)
    have hEq : (B.index * r ^ k) * Nat.card (Subgroup.center D) =
        (Subgroup.center D).index * Nat.card (Subgroup.center D) := by
      calc (B.index * r ^ k) * Nat.card (Subgroup.center D)
          = B.index * (Nat.card (Subgroup.center D) * r ^ k) := by ring
        _ = B.index * Nat.card B := by rw [hBZcard]
        _ = Nat.card D := h1
        _ = (Subgroup.center D).index * Nat.card (Subgroup.center D) := h2.symm
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hEq).symm
  have hExp : z * k + k ≤ 4 := pow_mul_add_le_four hzk3
  calc (Subgroup.center D).index = B.index * r ^ k := hZidx
    _ ≤ r ^ (z * k) * r ^ k := Nat.mul_le_mul hInd le_rfl
    _ = r ^ (z * k + k) := by rw [← pow_add]
    _ ≤ r ^ 4 := Nat.pow_le_pow_right (Fact.out : r.Prime).pos hExp

theorem card_quot_center_le_of_class_two {r : ℕ} [Fact r.Prime] {D : Type*} [Group D]
    [Finite D] (hexp : ∀ x : D, x ^ r = 1)
    (hclass : ∀ x y : D, ⁅x, y⁆ ∈ Subgroup.center D)
    (hab : ∀ B : Subgroup D, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → Nat.card B ≤ r ^ 3) :
    Nat.card (D ⧸ Subgroup.center D) ≤ r ^ 4 := by
  classical
  obtain ⟨B, hBmem⟩ := CFSG.maxOrderAbelianFamily_nonempty (G := D)
  have hB : IsMulCommutative B := hBmem.1
  have hZB : Subgroup.center D ≤ B := CFSG.center_le_of_mem_maxOrderAbelianFamily hBmem
  have hBself : Subgroup.centralizer (B : Set D) = B :=
    CFSG.centralizer_eq_self_of_mem_maxOrderAbelianFamily hBmem
  have hBcard_le : Nat.card B ≤ r ^ 3 :=
    hab B (fun x hx y hy => congrArg Subtype.val (hB.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hDp : IsPGroup r D := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  obtain ⟨b, hb⟩ := (hDp.to_subgroup B).exists_card_eq
  obtain ⟨z, hz⟩ := (hDp.to_subgroup (Subgroup.center D)).exists_card_eq
  have hzb : z ≤ b := by
    rw [← Nat.pow_le_pow_iff_right (Fact.out : r.Prime).one_lt, ← hz, ← hb]
    exact Subgroup.card_le_of_le hZB
  let k : ℕ := b - z
  have hBZcard : Nat.card B = Nat.card (Subgroup.center D) * r ^ k := by
    rw [hb, hz, ← pow_add, Nat.add_sub_of_le hzb]
  have hInd := index_centralizer_le_pow_card_center (r := r) hexp hclass B hB hZB k hBZcard
  rw [hBself] at hInd
  have hBidx_le : B.index ≤ r ^ (z * k) := by
    simpa [hz, pow_mul] using hInd
  have hzk3 : z + k ≤ 3 := by
    have hzk : z + k = b := Nat.add_sub_of_le hzb
    have hb3 : b ≤ 3 := by
      rw [← Nat.pow_le_pow_iff_right (Fact.out : r.Prime).one_lt, ← hb]
      exact hBcard_le
    omega
  simpa [Subgroup.index_eq_card] using center_index_le_pow_four hzk3 hBZcard hBidx_le

private theorem pow_eq_one_subtype {G : Type*} [Group G] {r : ℕ} {D : Subgroup G}
    (hexp : ∀ x ∈ D, x ^ r = 1) : ∀ x : ↥D, x ^ r = 1 :=
  fun x => Subtype.ext (hexp x.1 x.2)

private theorem commutator_mem_center_subtype {G : Type*} [Group G] {D : Subgroup G}
    (hclass : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ D ⊓ Subgroup.centralizer (D : Set G)) :
    ∀ x y : ↥D, ⁅x, y⁆ ∈ Subgroup.center ↥D := by
  intro x y
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp
    (Subgroup.mem_inf.mp (hclass x.1 x.2 y.1 y.2)).2 z.1 z.2

private theorem abelian_card_le_subtype {G : Type*} [Group G] {r : ℕ} {D : Subgroup G}
    (hab : ∀ B : Subgroup G, B ≤ D → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      Nat.card B ≤ r ^ 3) :
    ∀ B : Subgroup ↥D, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → Nat.card B ≤ r ^ 3 := by
  intro B hB
  have hBD : B.map D.subtype ≤ D := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hBcomm : ∀ x ∈ B.map D.subtype, ∀ y ∈ B.map D.subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hB x hx y hy)
  have h := hab (B.map D.subtype) hBD hBcomm
  rwa [Subgroup.card_map_of_injective D.subtype_injective] at h

theorem card_le_pow_four_mul_card_inf_centralizer {r : ℕ} [Fact r.Prime] {D : Subgroup G}
    (hexp : ∀ x ∈ D, x ^ r = 1)
    (hclass : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ D ⊓ Subgroup.centralizer (D : Set G))
    (hab : ∀ B : Subgroup G, B ≤ D → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      Nat.card B ≤ r ^ 3) :
    Nat.card D ≤ r ^ 4 * Nat.card ↥(D ⊓ Subgroup.centralizer (D : Set G)) := by
  classical
  have hquot := card_quot_center_le_of_class_two (r := r)
    (pow_eq_one_subtype hexp) (commutator_mem_center_subtype hclass)
    (abelian_card_le_subtype hab)
  have hcenter_card : Nat.card (Subgroup.center ↥D) =
      Nat.card ↥(D ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [← map_center_subtype_eq_inf_centralizer D,
      Subgroup.card_map_of_injective D.subtype_injective]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥D)
  calc Nat.card D = Nat.card (↥D ⧸ Subgroup.center ↥D) *
        Nat.card (Subgroup.center ↥D) := hcard
    _ ≤ r ^ 4 * Nat.card (Subgroup.center ↥D) := Nat.mul_le_mul_right _ hquot
    _ = r ^ 4 * Nat.card ↥(D ⊓ Subgroup.centralizer (D : Set G)) := by rw [hcenter_card]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core
