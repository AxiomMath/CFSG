module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.FusionInterface

public section

namespace CFSG.EvenSporadicStandard.J4Std.MFusion

open Subgroup CFSG.EvenSporadicStandard.J4Std

variable {G : Type} [Group G]

theorem mem_conjSub_iff {g x : G} {A : Subgroup G} : x ∈ conjSub g A ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    show g⁻¹ * (g * a * g⁻¹) * g ∈ A
    rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
  · intro h
    exact ⟨g⁻¹ * x * g, h, by show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩

theorem conj_mem_conjSub {g a : G} {A : Subgroup G} (ha : a ∈ A) : g * a * g⁻¹ ∈ conjSub g A :=
  mem_conjSub_iff.2 (by rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group])

theorem card_conjSub (g : G) (A : Subgroup G) : Nat.card (conjSub g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conj_inv_mem_of_involution {t : G} (ht : t * t = 1) {B : Subgroup G}
    (hn : ∀ b ∈ B, t * b * t⁻¹ ∈ B) {b : G} (hb : b ∈ B) : t⁻¹ * b * t ∈ B := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have := hn b hb
  rw [hti] at this
  rw [hti]
  exact this

@[expose] def adjoinInv (B : Subgroup G) (t : G) (ht : t * t = 1)
    (hn : ∀ b ∈ B, t * b * t⁻¹ ∈ B) : Subgroup G where
  carrier := {x | x ∈ B ∨ ∃ b ∈ B, x = t * b}
  mul_mem' := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rintro x x' (hx | ⟨b, hb, rfl⟩) (hx' | ⟨b', hb', rfl⟩)
    · exact Or.inl (B.mul_mem hx hx')
    · refine Or.inr ⟨(t⁻¹ * x * t) * b', B.mul_mem (conj_inv_mem_of_involution ht hn hx) hb', ?_⟩
      group
    · refine Or.inr ⟨b * x', B.mul_mem hb hx', ?_⟩
      group
    · refine Or.inl ?_
      have : t * b * (t * b') = (t * b * t⁻¹) * b' := by
        calc t * b * (t * b') = t * b * t * b' := by group
          _ = (t * b * t⁻¹) * b' := by rw [hti]
      rw [this]
      exact B.mul_mem (hn b hb) hb'
  one_mem' := Or.inl B.one_mem
  inv_mem' := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rintro x (hx | ⟨b, hb, rfl⟩)
    · exact Or.inl (B.inv_mem hx)
    · refine Or.inr ⟨t⁻¹ * b⁻¹ * t, conj_inv_mem_of_involution ht hn (B.inv_mem hb), ?_⟩
      calc (t * b)⁻¹ = b⁻¹ * t⁻¹ := mul_inv_rev _ _
        _ = b⁻¹ * t := by rw [hti]
        _ = t * (t⁻¹ * b⁻¹ * t) := by group

theorem mem_adjoinInv_iff {B : Subgroup G} {t : G} {ht : t * t = 1}
    {hn : ∀ b ∈ B, t * b * t⁻¹ ∈ B} {x : G} :
    x ∈ adjoinInv B t ht hn ↔ x ∈ B ∨ ∃ b ∈ B, x = t * b := Iff.rfl

theorem le_adjoinInv {B : Subgroup G} {t : G} {ht : t * t = 1}
    {hn : ∀ b ∈ B, t * b * t⁻¹ ∈ B} : B ≤ adjoinInv B t ht hn := fun _ hx => Or.inl hx

theorem mul_mem_adjoinInv {B : Subgroup G} {t : G} {ht : t * t = 1}
    {hn : ∀ b ∈ B, t * b * t⁻¹ ∈ B} {b : G} (hb : b ∈ B) : t * b ∈ adjoinInv B t ht hn :=
  Or.inr ⟨b, hb, rfl⟩

theorem card_adjoinInv [Finite G] {B : Subgroup G} {t : G} {ht : t * t = 1}
    {hn : ∀ b ∈ B, t * b * t⁻¹ ∈ B} (htB : t ∉ B) :
    Nat.card (adjoinInv B t ht hn) = 2 * Nat.card B := by
  have hinl : ∀ b : B, (b : G) ∈ adjoinInv B t ht hn := fun b => Or.inl b.2
  have hinr : ∀ b : B, t * (b : G) ∈ adjoinInv B t ht hn := fun b => Or.inr ⟨b, b.2, rfl⟩
  let e : (B ⊕ B) ≃ adjoinInv B t ht hn :=
    Equiv.ofBijective
      (fun s => match s with
        | Sum.inl b => ⟨b, hinl b⟩
        | Sum.inr b => ⟨t * b, hinr b⟩)
      ⟨by
        rintro (b | b) (b' | b') h
        · have h' := congrArg Subtype.val h
          exact congrArg Sum.inl (Subtype.ext h')
        · exfalso
          have h' : (b : G) = t * b' := congrArg Subtype.val h
          apply htB
          have : t = (b : G) * (b' : G)⁻¹ := by rw [h']; group
          rw [this]
          exact B.mul_mem b.2 (B.inv_mem b'.2)
        · exfalso
          have h' : t * (b : G) = b' := congrArg Subtype.val h
          apply htB
          have : t = (b' : G) * (b : G)⁻¹ := by rw [← h']; group
          rw [this]
          exact B.mul_mem b'.2 (B.inv_mem b.2)
        · have h' : t * (b : G) = t * b' := congrArg Subtype.val h
          exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h')),
       by
        rintro ⟨x, hx | ⟨b, hb, rfl⟩⟩
        · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
        · exact ⟨Sum.inr ⟨b, hb⟩, rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_sum, two_mul]

section Psi

variable (Y : Subgroup G) (y : G)

@[expose] def psiHom (hy : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y) (hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) :
    Y →* Y where
  toFun a := ⟨a * (y * a * y⁻¹), Y.mul_mem a.2 (hy a a.2)⟩
  map_one' := by
    apply Subtype.ext
    show (1 : G) * (y * 1 * y⁻¹) = 1
    group
  map_mul' a b := by
    apply Subtype.ext
    have hba : (b : G) * (y * a * y⁻¹) = (y * a * y⁻¹) * b := hc b b.2 _ (hy a a.2)
    show ((a : G) * b) * (y * ((a : G) * b) * y⁻¹) =
      ((a : G) * (y * a * y⁻¹)) * ((b : G) * (y * b * y⁻¹))
    calc ((a : G) * b) * (y * ((a : G) * b) * y⁻¹)
        = a * (b * (y * a * y⁻¹)) * (y * b * y⁻¹) := by group
      _ = a * ((y * a * y⁻¹) * b) * (y * b * y⁻¹) := by rw [hba]
      _ = ((a : G) * (y * a * y⁻¹)) * ((b : G) * (y * b * y⁻¹)) := by group

variable {Y y}

theorem psi_eq_one_iff (hsq : ∀ a ∈ Y, a * a = 1) {a : G} (ha : a ∈ Y) :
    a * (y * a * y⁻¹) = 1 ↔ a * y = y * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  constructor
  · intro h
    have h1 : y * a * y⁻¹ = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hai] at h1
    calc a * y = (y * a * y⁻¹) * y := by rw [h1]
      _ = y * a := by group
  · intro h
    calc a * (y * a * y⁻¹) = (a * y) * a * y⁻¹ := by group
      _ = (y * a) * a * y⁻¹ := by rw [h]
      _ = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group

theorem ker_psiHom {hy : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y} {hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a}
    (hsq : ∀ a ∈ Y, a * a = 1) :
    (psiHom Y y hy hc).ker = (Y ⊓ centralizer ({y} : Set G)).subgroupOf Y := by
  ext a
  rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : (a : G) * (y * a * y⁻¹) = 1 := congrArg Subtype.val h
    exact ⟨a.2, (psi_eq_one_iff hsq a.2).1 h1⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext ((psi_eq_one_iff hsq a.2).2 h)

theorem range_psiHom_le {hy : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y} {hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a}
    (hy2 : y * y = 1) :
    (psiHom Y y hy hc).range ≤ (Y ⊓ centralizer ({y} : Set G)).subgroupOf Y := by
  rintro _ ⟨a, rfl⟩
  rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  refine ⟨(psiHom Y y hy hc a).2, ?_⟩
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hb : y * a * y⁻¹ ∈ Y := hy a a.2
  have hab : (a : G) * (y * a * y⁻¹) = (y * a * y⁻¹) * a := hc _ a.2 _ hb
  have hyb : y * (y * a * y⁻¹) = a * y⁻¹ := by
    calc y * (y * a * y⁻¹) = (y * y) * a * y⁻¹ := by group
      _ = a * y⁻¹ := by rw [hy2, one_mul]
  show (a : G) * (y * a * y⁻¹) * y = y * ((a : G) * (y * a * y⁻¹))
  calc (a : G) * (y * a * y⁻¹) * y = (y * a * y⁻¹) * a * y := by rw [hab]
    _ = (y * a * y⁻¹) * a * y⁻¹ := by rw [hyi]
    _ = (y * a * y⁻¹) * (a * y⁻¹) := by group
    _ = (y * a * y⁻¹) * (y * (y * a * y⁻¹)) := by rw [hyb]
    _ = y * (a * (y * a * y⁻¹)) := by group

abbrev cenIn (Y : Subgroup G) (y : G) : Subgroup G := Y ⊓ centralizer ({y} : Set G)

theorem mem_cenIn {a : G} : a ∈ cenIn Y y ↔ a ∈ Y ∧ a * y = y * a := by
  rw [mem_inf, mem_centralizer_singleton_iff]

theorem cenIn_le_left : cenIn Y y ≤ Y := inf_le_left

theorem card_cenIn_mul {hy : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y} {hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a}
    (hsq : ∀ a ∈ Y, a * a = 1) :
    Nat.card (cenIn Y y) * Nat.card (psiHom Y y hy hc).range = Nat.card Y := by
  have h1 := Subgroup.card_ker_mul_card_range (psiHom Y y hy hc)
  rw [ker_psiHom hsq, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  exact h1

variable [Finite G]

theorem card_le_sq_cenIn {hy : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y} {hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a}
    (hsq : ∀ a ∈ Y, a * a = 1) (hy2 : y * y = 1) :
    Nat.card Y ≤ Nat.card (cenIn Y y) ^ 2 := by
  have h1 := card_cenIn_mul (hy := hy) (hc := hc) hsq
  have hrange : Nat.card (psiHom Y y hy hc).range ≤ Nat.card (cenIn Y y) := by
    calc Nat.card (psiHom Y y hy hc).range
        ≤ Nat.card ((cenIn Y y).subgroupOf Y) := Subgroup.card_le_of_le (range_psiHom_le hy2)
      _ = Nat.card (cenIn Y y) := Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h1, sq]
  exact Nat.mul_le_mul_left _ hrange

theorem exists_psi_eq {hy : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y} {hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a}
    (hsq : ∀ a ∈ Y, a * a = 1) (hy2 : y * y = 1) (hcard : Nat.card Y = Nat.card (cenIn Y y) ^ 2)
    {c : G} (hc' : c ∈ cenIn Y y) : ∃ a ∈ Y, c = a * (y * a * y⁻¹) := by
  have h1 := card_cenIn_mul (hy := hy) (hc := hc) hsq
  have hpos : 0 < Nat.card (cenIn Y y) := Nat.card_pos
  have hr : Nat.card (psiHom Y y hy hc).range = Nat.card (cenIn Y y) := by
    rw [hcard, sq] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have heq : (psiHom Y y hy hc).range = (cenIn Y y).subgroupOf Y := by
    refine Subgroup.eq_of_le_of_card_ge (range_psiHom_le hy2) ?_
    rw [hr, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hmem : (⟨c, (mem_cenIn.1 hc').1⟩ : Y) ∈ (psiHom Y y hy hc).range := by
    rw [heq, mem_subgroupOf]
    exact hc'
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, a.2, (congrArg Subtype.val ha).symm⟩

end Psi

end CFSG.EvenSporadicStandard.J4Std.MFusion
