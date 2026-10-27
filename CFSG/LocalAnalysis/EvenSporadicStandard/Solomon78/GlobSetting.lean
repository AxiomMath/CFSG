module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardCentralizer

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem twoAdic_autCentralizer_le {L K : Subgroup G} (hout : OutTwo ↥L)
    (hC : Nat.card (centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2) :
    twoAdic (autCentralizer L K) ≤ 2 := by
  set A := autCentralizer L K with hA
  set I : Subgroup (MulAut ↥L) := A ⊓ (MulAut.conj : ↥L →* MulAut ↥L).range with hI
  have hfix : ∀ l : ↥L, MulAut.conj l ∈ A ↔
      l ∈ centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro l
    constructor
    · intro hl
      rw [mem_centralizer_iff]
      intro k hk
      have h1 : (MulAut.conj l) k = k := hl k (mem_subgroupOf.1 hk)
      rw [MulAut.conj_apply] at h1
      calc k * l = (l * k * l⁻¹) * l := by rw [h1]
        _ = l * k := by group
    · intro hl k hk
      have h1 : k * l = l * k := mem_centralizer_iff.1 hl k (mem_subgroupOf.2 hk)
      rw [MulAut.conj_apply]
      calc l * k * l⁻¹ = (k * l) * l⁻¹ := by rw [h1]
        _ = k := by group
  have hIcard : Nat.card I ≤ 2 := by
    have hsurj : Function.Surjective
        (fun l : centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) =>
          (⟨MulAut.conj (l : ↥L), (hfix l).2 l.2, l, rfl⟩ : I)) := by
      rintro ⟨α, hαA, l, rfl⟩
      exact ⟨⟨l, (hfix l).1 hαA⟩, rfl⟩
    exact (Nat.card_le_card_of_surjective _ hsurj).trans hC
  have hIA : I ≤ A := inf_le_left
  have hidx : Nat.card (A ⧸ I.subgroupOf A) ≤ 2 := by
    by_cases hall : ∀ α ∈ A, α ∈ I
    · have : Subsingleton (A ⧸ I.subgroupOf A) := by
        refine ⟨fun x y => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        rw [QuotientGroup.eq]
        exact mem_subgroupOf.2 (hall _ (mul_mem (inv_mem a.2) b.2))
      rw [Nat.card_unique]
      norm_num
    · push Not at hall
      obtain ⟨α₀, hα₀A, hα₀I⟩ := hall
      have hsurj : Function.Surjective (fun b : Bool =>
          if b then (QuotientGroup.mk (⟨α₀, hα₀A⟩ : A) : A ⧸ I.subgroupOf A)
          else QuotientGroup.mk 1) := by
        intro x
        obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective x
        have hα₀inn : ¬ ∃ l : ↥L, α₀ = MulAut.conj l := fun ⟨l, hl⟩ =>
          hα₀I ⟨hα₀A, l, hl.symm⟩
        rcases hout α₀ β with h | ⟨l, hl⟩ | ⟨l, hl⟩
        · exact absurd h hα₀inn
        · refine ⟨false, ?_⟩
          show QuotientGroup.mk 1 = QuotientGroup.mk β
          rw [QuotientGroup.eq]
          refine mem_subgroupOf.2 ⟨?_, l, hl.symm⟩
          simp
        · refine ⟨true, ?_⟩
          show QuotientGroup.mk ⟨α₀, hα₀A⟩ = QuotientGroup.mk β
          rw [QuotientGroup.eq]
          refine mem_subgroupOf.2 ⟨?_, l, hl.symm⟩
          simpa using mul_mem (inv_mem hα₀A) β.2
      exact (Nat.card_le_card_of_surjective _ hsurj).trans (by simp)
  have hAcard : Nat.card A ≤ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (I.subgroupOf A)
    have h2 : Nat.card (I.subgroupOf A) = Nat.card I :=
      Nat.card_congr (subgroupOfEquivOfLe hIA).toEquiv
    rw [h1, h2]
    calc Nat.card (A ⧸ I.subgroupOf A) * Nat.card I ≤ 2 * 2 := Nat.mul_le_mul hidx hIcard
      _ = 4 := by norm_num
  unfold twoAdic
  by_contra hlt
  push Not at hlt
  have hd : 2 ^ (Nat.card A).factorization 2 ∣ Nat.card A := Nat.ordProj_dvd _ _
  have h3 : 2 ^ 3 ≤ 2 ^ (Nat.card A).factorization 2 := Nat.pow_le_pow_right (by norm_num) hlt
  have h4 := Nat.le_of_dvd Nat.card_pos hd
  omega


omit [Finite G] in
theorem subgroupOf_eq_centralizer {L K : Subgroup G} {u : G} (hu : u ∈ L)
    (hKeq : K = L ⊓ centralizer ({u} : Set G)) :
    K.subgroupOf L = centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) := by
  ext x
  rw [mem_subgroupOf, hKeq, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨x.2, congrArg Subtype.val h⟩

theorem card_centralizer_le_of_center {Y : Type*} [Group Y] [Finite Y] {z : Y} {H : Subgroup Y}
    (hH : H = centralizer ({z} : Set Y)) (hzH : z ∈ H) (hZ : Nat.card (center H) ≤ 2) :
    Nat.card (centralizer (H : Set Y)) ≤ 2 := by
  have hle : centralizer (H : Set Y) ≤ H := by
    intro w hw
    rw [hH]
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hw z hzH).symm
  have hmem : ∀ w : centralizer (H : Set Y), (⟨(w : Y), hle w.2⟩ : H) ∈ center H := by
    intro w
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (mem_centralizer_iff.1 w.2 (h : Y) h.2)
  let f : centralizer (H : Set Y) → center H := fun w => ⟨⟨w, hle w.2⟩, hmem w⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun x => ((x : H) : Y)) (congrArg Subtype.val h))
  exact (Nat.card_le_card_of_injective f hf).trans hZ

theorem standard_subgroupOf_centralizer {L K : Subgroup G} {u : G} (hu : u ∈ L)
    (hu2 : orderOf u = 2) (hKeq : K = L ⊓ centralizer ({u} : Set G))
    (hq : CFSG.Open.IsQuasisimple ↥(K.subgroupOf L))
    (hZ : Nat.card (center ↥(K.subgroupOf L)) ≤ 2) :
    standardComponentIsStandard (K.subgroupOf L) := by
  set z : ↥L := ⟨u, hu⟩ with hz
  have hz2 : orderOf z = 2 := by rw [hz, Subgroup.orderOf_mk]; exact hu2
  have hKz : K.subgroupOf L = centralizer ({z} : Set ↥L) := subgroupOf_eq_centralizer hu hKeq
  have hHn : ((K.subgroupOf L).subgroupOf (centralizer ({z} : Set ↥L))).Normal := by
    rw [hKz, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  refine (M24Std.standardComponentIsStandard_of_normal hz2 hq hKz.le hHn ?_).1
  intro U hU hUle
  have hUH : U ≤ K.subgroupOf L := hKz ▸ hUle.trans inf_le_left
  have hmem : ∀ w : U, (⟨w.1, hUH w.2⟩ : ↥(K.subgroupOf L)) ∈ center ↥(K.subgroupOf L) := by
    intro w
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (mem_centralizer_iff.1 (hUle w.2).2 (h : ↥L) h.2)
  let f : U → center ↥(K.subgroupOf L) := fun w => ⟨⟨w.1, hUH w.2⟩, hmem w⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun x => ((x : ↥(K.subgroupOf L)) : ↥L)) (congrArg Subtype.val h))
  exact (Nat.card_le_card_of_injective f hf).trans hZ

end CFSG.EvenSporadicStandard.Solomon78
