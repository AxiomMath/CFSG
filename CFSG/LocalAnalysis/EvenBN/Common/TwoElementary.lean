module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup

variable {G : Type*} [Group G]

private theorem mul_comm_of_mem {H : Subgroup G} [IsMulCommutative H] {x y : G} (hx : x ∈ H)
    (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : H) ⟨y, hy⟩)

private theorem mul_self_eq_one_of_mem {H : Subgroup G} [IsElementaryAbelian 2 H] {x : G} (hx : x ∈ H) :
    x * x = 1 := by
  rw [← sq]
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem exists_mul_of_le_normalizer {A B : Subgroup G} (hBA : B ≤ normalizer (A : Set G)) :
    ∀ s ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  intro s hs
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A B hBA, Set.mem_mul] at hs
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_mul_of_le_normalizer' {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) :
    ∀ s ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  intro s hs
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A B hAB, Set.mem_mul] at hs
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  exact ⟨a, ha, b, hb, rfl⟩

structure TwoElementaryProduct (S A B : Subgroup G) : Prop where
  le_left : A ≤ S
  le_right : B ≤ S
  exists_mul : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b
  isElementaryAbelian_left : IsElementaryAbelian 2 A
  isElementaryAbelian_right : IsElementaryAbelian 2 B
  exists_mul_ne : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x
  inf_centralizer_left : ∀ a ∈ A, a ∉ B → S ⊓ centralizer ({a} : Set G) = A

namespace TwoElementaryProduct

variable {S A B : Subgroup G} (h : TwoElementaryProduct S A B)
include h

theorem exists_mul' {s : G} (hs : s ∈ S) : ∃ b ∈ B, ∃ a ∈ A, s = b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := h.exists_mul s⁻¹ (S.inv_mem hs)
  refine ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, ?_⟩
  rw [← mul_inv_rev, ← hab, inv_inv]

theorem inf_le_centralizer : A ⊓ B ≤ centralizer (S : Set G) := by
  have := h.isElementaryAbelian_left
  have := h.isElementaryAbelian_right
  intro z hz
  rw [mem_centralizer_iff]
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul s hs
  calc a * b * z = a * (z * b) := by rw [mul_assoc, mul_comm_of_mem hb hz.2]
    _ = z * (a * b) := by rw [← mul_assoc, mul_comm_of_mem ha hz.1, mul_assoc]

theorem not_le_left : ¬ A ≤ B := by
  have := h.isElementaryAbelian_right
  intro hAB
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_ne
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul x hx
  obtain ⟨a', ha', b', hb', rfl⟩ := h.exists_mul y hy
  exact hxy (mul_comm_of_mem (B.mul_mem (hAB ha) hb) (B.mul_mem (hAB ha') hb'))

theorem not_le_right : ¬ B ≤ A := by
  have := h.isElementaryAbelian_left
  intro hBA
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_ne
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul x hx
  obtain ⟨a', ha', b', hb', rfl⟩ := h.exists_mul y hy
  exact hxy (mul_comm_of_mem (A.mul_mem ha (hBA hb)) (A.mul_mem ha' (hBA hb')))

theorem inf_centralizer_right {b : G} (hb : b ∈ B) (hbA : b ∉ A) :
    S ⊓ centralizer ({b} : Set G) = B := by
  have := h.isElementaryAbelian_right
  apply le_antisymm
  · rintro x ⟨hxS, hxb⟩
    obtain ⟨a', ha', b', hb', rfl⟩ := h.exists_mul x hxS
    have hab : b * a' = a' * b := by
      have h1 : b * (a' * b') = (a' * b') * b := (mem_centralizer_singleton_iff.mp hxb).symm
      calc b * a' = b * (a' * b') * b'⁻¹ := by group
        _ = a' * b' * b * b'⁻¹ := by rw [h1]
        _ = a' * (b * b') * b'⁻¹ := by rw [mul_assoc a', mul_comm_of_mem hb' hb]
        _ = a' * b := by group
    by_cases ha'B : a' ∈ B
    · exact B.mul_mem ha'B hb'
    · have hbC : b ∈ S ⊓ centralizer ({a'} : Set G) :=
        ⟨h.le_right hb, mem_centralizer_singleton_iff.mpr hab⟩
      rw [h.inf_centralizer_left a' ha' ha'B] at hbC
      exact absurd hbC hbA
  · intro x hx
    exact ⟨h.le_right hx, mem_centralizer_singleton_iff.mpr (mul_comm_of_mem hb hx).symm⟩

theorem symm : TwoElementaryProduct S B A where
  le_left := h.le_right
  le_right := h.le_left
  exists_mul := fun _ hs => h.exists_mul' hs
  isElementaryAbelian_left := h.isElementaryAbelian_right
  isElementaryAbelian_right := h.isElementaryAbelian_left
  exists_mul_ne := h.exists_mul_ne
  inf_centralizer_left := fun _ hb hbA => h.inf_centralizer_right hb hbA

theorem inf_centralizer_self : S ⊓ centralizer (S : Set G) = A ⊓ B := by
  apply le_antisymm
  · rintro z ⟨hzS, hz⟩
    obtain ⟨a, ha, haB⟩ := Set.not_subset.mp h.not_le_left
    obtain ⟨b, hb, hbA⟩ := Set.not_subset.mp h.not_le_right
    have hza : z ∈ S ⊓ centralizer ({a} : Set G) :=
      ⟨hzS, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz a (h.le_left ha)).symm⟩
    have hzb : z ∈ S ⊓ centralizer ({b} : Set G) :=
      ⟨hzS, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz b (h.le_right hb)).symm⟩
    rw [h.inf_centralizer_left a ha haB] at hza
    rw [h.inf_centralizer_right hb hbA] at hzb
    exact ⟨hza, hzb⟩
  · exact le_inf (inf_le_left.trans h.le_left) h.inf_le_centralizer

theorem map_center : (center S).map S.subtype = A ⊓ B := by
  rw [← h.inf_centralizer_self]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val (mem_center_iff.mp hy ⟨s, hs⟩)⟩
  · rintro ⟨hzS, hz⟩
    refine ⟨⟨z, hzS⟩, mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.mp hz s s.2

theorem mem_or_mem_of_mul_self_eq_one {x : G} (hx : x ∈ S) (hx2 : x * x = 1) :
    x ∈ A ∨ x ∈ B := by
  have := h.isElementaryAbelian_left
  have := h.isElementaryAbelian_right
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul x hx
  by_cases haB : a ∈ B
  · exact Or.inr (B.mul_mem haB hb)
  · left
    have ha2 := mul_self_eq_one_of_mem ha
    have hb2 := mul_self_eq_one_of_mem hb
    have hab : b * a = a * b := by
      have e : a * (a * b * (a * b)) * b = b * a := by
        calc a * (a * b * (a * b)) * b = (a * a) * (b * a) * (b * b) := by group
          _ = b * a := by rw [ha2, hb2, one_mul, mul_one]
      rw [← e, hx2, mul_one]
    have hbC : b ∈ S ⊓ centralizer ({a} : Set G) :=
      ⟨h.le_right hb, mem_centralizer_singleton_iff.mpr hab⟩
    rw [h.inf_centralizer_left a ha haB] at hbC
    exact A.mul_mem ha hbC

theorem le_or_le {E : Subgroup G} (hES : E ≤ S) [IsElementaryAbelian 2 E] : E ≤ A ∨ E ≤ B := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨e₁, he₁, he₁A⟩ := Set.not_subset.mp hne.1
  obtain ⟨e₂, he₂, he₂B⟩ := Set.not_subset.mp hne.2
  have he₂A : e₂ ∈ A :=
    (h.mem_or_mem_of_mul_self_eq_one (hES he₂) (mul_self_eq_one_of_mem he₂)).resolve_right he₂B
  have he₁C : e₁ ∈ S ⊓ centralizer ({e₂} : Set G) :=
    ⟨hES he₁, mem_centralizer_singleton_iff.mpr (mul_comm_of_mem he₁ he₂)⟩
  rw [h.inf_centralizer_left e₂ he₂A he₂B] at he₁C
  exact he₁A he₁C

theorem maximal_iff (E : Subgroup G) :
    Maximal (fun F : Subgroup G => F ≤ S ∧ IsElementaryAbelian 2 F) E ↔ E = A ∨ E = B := by
  have hA : A ≤ S ∧ IsElementaryAbelian 2 A := ⟨h.le_left, h.isElementaryAbelian_left⟩
  have hB : B ≤ S ∧ IsElementaryAbelian 2 B := ⟨h.le_right, h.isElementaryAbelian_right⟩
  constructor
  · rintro ⟨⟨hES, hE⟩, hmax⟩
    rcases h.le_or_le hES with hEA | hEB
    · exact Or.inl (le_antisymm hEA (hmax hA hEA))
    · exact Or.inr (le_antisymm hEB (hmax hB hEB))
  · rintro (rfl | rfl)
    · refine ⟨hA, fun F ⟨hFS, hF⟩ hEF => ?_⟩
      rcases h.le_or_le hFS with hFA | hFB
      · exact hFA
      · exact absurd (hEF.trans hFB) h.not_le_left
    · refine ⟨hB, fun F ⟨hFS, hF⟩ hEF => ?_⟩
      rcases h.le_or_le hFS with hFA | hFB
      · exact absurd (hEF.trans hFA) h.not_le_right
      · exact hFB

theorem inf_inf_centralizer {x : G} (hx : x ∈ S) (hxA : x ∉ A) :
    A ⊓ (S ⊓ centralizer ({x} : Set G)) = A ⊓ B := by
  apply le_antisymm
  · rintro a ⟨ha, -, hax⟩
    refine ⟨ha, ?_⟩
    by_contra haB
    have hxC : x ∈ S ⊓ centralizer ({a} : Set G) :=
      ⟨hx, mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hax).symm⟩
    rw [h.inf_centralizer_left a ha haB] at hxC
    exact hxA hxC
  · rintro z hz
    refine ⟨hz.1, h.le_left hz.1, mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mem_centralizer_iff.mp (h.inf_le_centralizer hz) x hx).symm

theorem relIndex_left_eq : A.relIndex S = A.relIndex B := by
  let f := quotientSubgroupOfEmbeddingOfLE A h.le_right
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨s, hs⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb, a, ha, rfl⟩ := h.exists_mul' hs
    refine ⟨QuotientGroup.mk ⟨b, hb⟩, ?_⟩
    rw [quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, mem_subgroupOf]
    simpa using ha
  exact (Nat.card_congr (Equiv.ofBijective f ⟨f.injective, hf⟩)).symm

theorem normalizer_inf_le_normalizer_right :
    Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (B : Set G) := by
  have hconj (x : G) (hxS : x ∈ Subgroup.normalizer (S : Set G))
      (hxA : x ∈ Subgroup.normalizer (A : Set G)) : ∀ b ∈ B, x * b * x⁻¹ ∈ B := by
    intro b hb
    let E : Subgroup G := B.map (MulAut.conj x).toMonoidHom
    have hES : E ≤ S := by
      intro e he
      rw [Subgroup.mem_map] at he
      obtain ⟨b', hb', rfl⟩ := he
      have hmap : S.map (MulAut.conj x).toMonoidHom = S :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hxS
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ (h.le_right hb')
    have hEel : IsElementaryAbelian 2 E := by
      have hBel : IsElementaryAbelian 2 B := h.isElementaryAbelian_right
      exact IsElementaryAbelian.map (A := B) (MulAut.conj x).toMonoidHom
    have hEeli : IsElementaryAbelian 2 E := hEel
    rcases h.le_or_le hES with hEA | hEB
    · exfalso
      apply h.not_le_right
      intro b' hb'
      have hmem : (MulAut.conj x) b' ∈ A := hEA (Subgroup.mem_map_of_mem _ hb')
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
        (Subgroup.normalizer (A : Set G)).inv_mem hxA
      have hmap : A.map (MulAut.conj x⁻¹).toMonoidHom = A :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hxinv
      have hmem' : (MulAut.conj x⁻¹) ((MulAut.conj x) b') ∈ A := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hmem
      have hmem'' : b' ∈ A := by
        convert hmem' using 2
        simp [MulAut.conj_apply]
        group
      exact hmem''
    · exact hEB (Subgroup.mem_map_of_mem _ hb)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact hconj g hg.1 hg.2 b hb
  · intro hb
    have hg'S : g⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normalizer (S : Set G)).inv_mem hg.1
    have hg'A : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hg.2
    have hb' : g⁻¹ * (g * b * g⁻¹) * (g⁻¹)⁻¹ ∈ B :=
      hconj g⁻¹ hg'S hg'A (g * b * g⁻¹) hb
    convert hb' using 2
    group

variable [Finite G]

theorem card_inf_centralizer_le_right {x : G} (hx : x ∈ S) (hxA : x ∉ A) :
    Nat.card (S ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ Nat.card B := by
  set C := S ⊓ centralizer ({x} : Set G)
  have h1 := relIndex_mul_card A C
  have h2 := relIndex_mul_card A B
  rw [h.inf_inf_centralizer hx hxA] at h1
  have : A.IsFiniteRelIndex S := isFiniteRelIndex_of_finiteIndex
  have h3 : A.relIndex C ≤ A.relIndex S := relIndex_le_of_le_right inf_le_left relIndex_ne_zero
  rw [h.relIndex_left_eq] at h3
  rw [← h1, ← h2]
  exact Nat.mul_le_mul_right _ h3

theorem card_inf_centralizer_le {x : G} (hx : x ∈ S) (hxA : x ∉ A) (hxB : x ∉ B) :
    Nat.card (S ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ min (Nat.card A) (Nat.card B) :=
  le_min (h.symm.card_inf_centralizer_le_right hx hxB) (h.card_inf_centralizer_le_right hx hxA)

theorem card_le_of_isMulCommutative {X : Subgroup G} (hXS : X ≤ S) [IsMulCommutative X] :
    Nat.card X ≤ max (Nat.card A) (Nat.card B) := by
  by_cases hX : ∀ x ∈ X, x ∈ A ∨ x ∈ B
  · by_cases hXA : X ≤ A
    · exact (card_le_of_le hXA).trans (le_max_left _ _)
    · have hXB : X ≤ B := by
        intro y hy
        obtain ⟨x, hx, hxA⟩ := Set.not_subset.mp hXA
        have hxB : x ∈ B := (hX x hx).resolve_left hxA
        by_contra hyB
        have hyA : y ∈ A := (hX y hy).resolve_right hyB
        rcases hX (x * y) (X.mul_mem hx hy) with hxy | hxy
        · exact hxA (by simpa using A.mul_mem hxy (A.inv_mem hyA))
        · exact hyB (by simpa using B.mul_mem (B.inv_mem hxB) hxy)
      exact (card_le_of_le hXB).trans (le_max_right _ _)
  · push Not at hX
    obtain ⟨x, hx, hxA, hxB⟩ := hX
    have hXC : X ≤ S ⊓ centralizer ({x} : Set G) := fun y hy =>
      ⟨hXS hy, mem_centralizer_singleton_iff.mpr (mul_comm_of_mem hy hx)⟩
    exact (card_le_of_le hXC).trans ((h.card_inf_centralizer_le (hXS hx) hxA hxB).trans
      min_le_max)

end TwoElementaryProduct

end CFSG.LocalAnalysis.EvenBN.Common
