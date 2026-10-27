module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndBasic

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup

variable {G : Type*} [Group G]

@[expose] def conjR (X : Subgroup G) (g : G) : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjR {X : Subgroup G} {g x : G} : x ∈ conjR X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem conj_mem_conjR {X : Subgroup G} {g y : G} (hy : y ∈ X) : g⁻¹ * y * g ∈ conjR X g := by
  rw [mem_conjR]
  simpa [mul_assoc] using hy

theorem conjR_one (X : Subgroup G) : conjR X 1 = X := by
  ext x
  simp [mem_conjR]

theorem conjR_mul (X : Subgroup G) (g h : G) : conjR X (g * h) = conjR (conjR X g) h := by
  ext x
  simp only [mem_conjR, mul_inv_rev]
  group

theorem conjR_inf (A B : Subgroup G) (g : G) : conjR (A ⊓ B) g = conjR A g ⊓ conjR B g := by
  ext x
  simp [mem_conjR]

theorem conjR_mono {A B : Subgroup G} (h : A ≤ B) (g : G) : conjR A g ≤ conjR B g :=
  map_mono h

theorem conjR_sup (A B : Subgroup G) (g : G) : conjR (A ⊔ B) g = conjR A g ⊔ conjR B g :=
  Subgroup.map_sup _ _ _

theorem card_conjR (X : Subgroup G) (g : G) : Nat.card (conjR X g) = Nat.card X :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjR_eq_self {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    conjR X g = X := by
  ext x
  rw [mem_conjR]
  exact ((mem_normalizer_iff.mp hg) x).symm

theorem conjR_commutator (A B : Subgroup G) (g : G) :
    conjR ⁅A, B⁆ g = ⁅conjR A g, conjR B g⁆ :=
  map_commutator _ _ _

theorem card_mul_card_le_inf [Finite G] {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C) :
    Nat.card A * Nat.card B ≤ Nat.card (A ⊓ B : Subgroup G) * Nat.card C := by
  have h1 := Subgroup.relIndex_inf_le (H := A) (K := B) (L := C)
  have hA' := Subgroup.relIndex_mul_card A C
  have hB' := Subgroup.relIndex_mul_card B C
  have hAB' := Subgroup.relIndex_mul_card (A ⊓ B) C
  rw [inf_of_le_left hA] at hA'
  rw [inf_of_le_left hB] at hB'
  rw [inf_of_le_left (inf_le_left.trans hA)] at hAB'
  have hC : 0 < Nat.card C := Nat.card_pos
  have hpos : 0 < Nat.card (A ⊓ B : Subgroup G) := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have key : Nat.card C * (Nat.card A * Nat.card B) ≤
      Nat.card C * (Nat.card (A ⊓ B : Subgroup G) * Nat.card C) := by
    calc Nat.card C * (Nat.card A * Nat.card B)
        = (A ⊓ B).relIndex C * Nat.card (A ⊓ B : Subgroup G) * (Nat.card A * Nat.card B) := by
          rw [hAB']
      _ ≤ A.relIndex C * B.relIndex C * Nat.card (A ⊓ B : Subgroup G) *
          (Nat.card A * Nat.card B) := by gcongr
      _ = (A.relIndex C * Nat.card A) * (B.relIndex C * Nat.card B) *
          Nat.card (A ⊓ B : Subgroup G) := by ring
      _ = Nat.card C * (Nat.card (A ⊓ B : Subgroup G) * Nat.card C) := by rw [hA', hB']; ring
  exact Nat.le_of_mul_le_mul_left key hC

theorem card_inf_conjR_ge [Finite G] {P Q : Subgroup G} {g : G} (s : G) (hQ : Q ≤ conjR P g) :
    Nat.card Q * Nat.card (P ⊓ conjR P s : Subgroup G) ≤
      Nat.card (Q ⊓ conjR P (s * g) : Subgroup G) * Nat.card P := by
  have hle : conjR (P ⊓ conjR P s) g ≤ conjR P g := conjR_mono inf_le_left g
  have h := card_mul_card_le_inf hQ hle
  rw [card_conjR, card_conjR] at h
  have heq : Q ⊓ conjR (P ⊓ conjR P s) g = Q ⊓ conjR P (s * g) := by
    rw [conjR_inf, ← conjR_mul, ← inf_assoc, inf_of_le_left hQ]
  rwa [heq] at h

theorem eq_bot_of_inf_centralizer_eq_bot [Finite G] {T : Subgroup G} {t : G}
    (hT : IsPGroup 2 T) (htT : t ∈ normalizer (T : Set G)) (ht : t * t = 1)
    (hfix : T ⊓ centralizer ({t} : Set G) = ⊥) : T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (zpowers t) := by
    rcases eq_or_ne t 1 with h1 | h1
    · rw [h1, zpowers_one_eq_bot]
      exact IsPGroup.of_bot
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [sq]; exact ht) h1
  have hzN : zpowers t ≤ normalizer (T : Set G) := by rw [zpowers_le]; exact htT
  set M := T ⊔ zpowers t with hM
  have hMp : IsPGroup 2 M := IsPGroup.to_sup_of_normal_left' hT hz hzN
  have : Group.IsNilpotent M := hMp.isNilpotent
  have hMN : M ≤ normalizer (T : Set G) := sup_le le_normalizer hzN
  have hnormal : (T.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hMN
  by_contra hne
  have hne' : T.subgroupOf M ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, le_sup_left (a := T) hx⟩ : M) ∈ T.subgroupOf M := hx
    rw [hbot, mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨⟨z, hzT, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  apply hz1
  have htM : (⟨t, mem_sup_right (mem_zpowers t)⟩ : M) * z = z * ⟨t, _⟩ :=
    (mem_center_iff.mp hzZ) _
  have hzc : (z : G) ∈ T ⊓ centralizer ({t} : Set G) :=
    ⟨hzT, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val htM).symm⟩
  rw [hfix, mem_bot] at hzc
  exact Subtype.ext (Subtype.ext hzc)

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
