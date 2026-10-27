module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LieType.Multipliers.U43Bridge

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type*} [Group G]

@[expose] def NonabSimple (A : Subgroup G) : Prop :=
  IsSimpleGroup ↥A ∧ ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a

@[expose] def IsA6 (A : Subgroup G) : Prop := Nonempty (↥A ≃* A6)

namespace NonabSimple

variable {A : Subgroup G}

theorem eq_bot_or_eq_self (h : NonabSimple A) (S : Subgroup G) (hS : S ≤ A)
    (hn : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S) : S = ⊥ ∨ S = A := by
  have hnorm : (S.subgroupOf A).Normal :=
    (normal_subgroupOf_iff hS).2 fun s a hs ha => hn a ha s hs
  rcases h.1.eq_bot_or_eq_top_of_normal (S.subgroupOf A) with h0 | h0
  · refine Or.inl (eq_bot_iff.2 fun s hs => ?_)
    have hmem : (⟨s, hS hs⟩ : A) ∈ S.subgroupOf A := mem_subgroupOf.2 hs
    rw [h0, mem_bot] at hmem
    exact mem_bot.2 (congrArg Subtype.val hmem)
  · refine Or.inr (le_antisymm hS fun a ha => ?_)
    have hmem : (⟨a, ha⟩ : A) ∈ S.subgroupOf A := by rw [h0]; exact mem_top _
    exact mem_subgroupOf.1 hmem

theorem perfect (h : NonabSimple A) : ⁅A, A⁆ = A := by
  have hle : ⁅A, A⁆ ≤ A := commutator_le_of_le le_rfl le_rfl
  rcases h.eq_bot_or_eq_self ⁅A, A⁆ hle fun a ha s hs =>
    (mem_normalizer_iff.1 (normalizer_commutator_ge_left A A ha) s).1 hs with h0 | h0
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := h.2
    have hmem : ⁅a, b⁆ ∈ ⁅A, A⁆ := commutator_mem_commutator ha hb
    rw [h0, mem_bot] at hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hmem)
  · exact h0

theorem center_eq_one (h : NonabSimple A) :
    ∀ a ∈ A, (∀ x ∈ A, a * x = x * a) → a = 1 := by
  intro a ha hc
  have hn : ∀ x ∈ A, ∀ s ∈ A ⊓ centralizer (A : Set G),
      x * s * x⁻¹ ∈ A ⊓ centralizer (A : Set G) := by
    intro x hx s hs
    rw [mem_centralizer_iff.1 (mem_inf.1 hs).2 x hx, mul_inv_cancel_right]
    exact hs
  rcases h.eq_bot_or_eq_self (A ⊓ centralizer (A : Set G)) inf_le_left hn with h0 | h0
  · have hmem : a ∈ A ⊓ centralizer (A : Set G) :=
      mem_inf.2 ⟨ha, mem_centralizer_iff.2 fun x hx => (hc x hx).symm⟩
    rwa [h0, mem_bot] at hmem
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := h.2
    have hmem : x ∈ A ⊓ centralizer (A : Set G) := by rw [h0]; exact hx
    exact hxy (mem_centralizer_iff.1 (mem_inf.1 hmem).2 y hy).symm

theorem of_mulEquiv {H : Type*} [Group H] [IsSimpleGroup H] (e : ↥A ≃* H)
    (hH : ¬ (Nat.card H).Prime) : NonabSimple A := by
  refine ⟨e.isSimpleGroup, ?_⟩
  by_contra hab
  push Not at hab
  apply hH
  have hcomm : IsMulCommutative H := ⟨⟨fun x y => by
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hab x' x'.2 y' y'.2))⟩⟩
  exact Group.is_simple_iff_prime_card.1 inferInstance

end NonabSimple

theorem card_a6 : Nat.card A6 = 360 := by
  have h : 2 * Nat.card A6 = Nat.factorial 6 :=
    CFSG.LieType.SteinbergBR.SmallAlt.card_alternating (m := 6) (by norm_num)
  rw [show Nat.factorial 6 = 720 by decide] at h
  omega

theorem a6_simple : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)

namespace IsA6

variable {A : Subgroup G}

theorem card (h : IsA6 A) : Nat.card A = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_a6]

theorem nonabSimple (h : IsA6 A) : NonabSimple A := by
  obtain ⟨e⟩ := h
  have := a6_simple
  exact NonabSimple.of_mulEquiv e (by rw [card_a6]; norm_num)

theorem outer (h : IsA6 A) : IsPGroup 2 (Outer ↥A) := by
  obtain ⟨e⟩ := h
  exact CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six.of_equiv
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e.symm)

end IsA6

theorem u43_simple : IsSimpleGroup U43 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
    (CFSG.LieType.Multipliers.U43.F9) 3 1
    (by rw [Nat.card_eq_fintype_card, CFSG.LieType.Multipliers.U43.F9.card_eq]; norm_num) 4
    (by norm_num) (by simp)
  rw [pow_one] at h
  exact h

theorem card_u43 : Nat.card U43 = 3265920 := CFSG.LieType.Multipliers.U43.card_X₀

theorem u43_nonabSimple {N : Subgroup G} (e : ↥N ≃* U43) : NonabSimple N := by
  have := u43_simple
  exact NonabSimple.of_mulEquiv e (by rw [card_u43]; norm_num)

structure ProdSplit (N A B : Subgroup G) : Prop where
  le_A : A ≤ N
  le_B : B ≤ N
  conj_A : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A
  conj_B : ∀ n ∈ N, ∀ b ∈ B, n * b * n⁻¹ ∈ B
  comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  inf_eq_bot : A ⊓ B = ⊥
  prod : ∀ n ∈ N, ∃ a ∈ A, ∃ b ∈ B, n = a * b
  isA : IsA6 A
  isB : IsA6 B

theorem exists_prodSplit {N : Subgroup G} (e : ↥N ≃* (A6 × A6)) :
    ∃ A B : Subgroup G, ProdSplit N A B := by
  let ι : A6 × A6 →* G := N.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hsurj : ∀ n ∈ N, ∃ m : A6 × A6, ι m = n := fun n hn => ⟨e ⟨n, hn⟩, by simp [ι]⟩
  let ιA : A6 →* G := ι.comp (MonoidHom.inl A6 A6)
  let ιB : A6 →* G := ι.comp (MonoidHom.inr A6 A6)
  have hA : Function.Injective ιA := hι.comp fun x y h => by simpa using congrArg Prod.fst h
  have hB : Function.Injective ιB := hι.comp fun x y h => by simpa using congrArg Prod.snd h
  have hmem : ∀ m : A6 × A6, ι m ∈ N := fun m => (e.symm m).2
  refine ⟨ιA.range, ιB.range, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨(MonoidHom.ofInjective hA).symm⟩,
    ⟨(MonoidHom.ofInjective hB).symm⟩⟩
  · rintro _ ⟨x, rfl⟩
    exact hmem (x, 1)
  · rintro _ ⟨x, rfl⟩
    exact hmem (1, x)
  · rintro n hn _ ⟨x, rfl⟩
    obtain ⟨m, rfl⟩ := hsurj n hn
    refine ⟨m.1 * x * m.1⁻¹, ?_⟩
    show ι (m.1 * x * m.1⁻¹, 1) = ι m * ι (x, 1) * (ι m)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg ι (Prod.ext (by simp) (by simp))
  · rintro n hn _ ⟨x, rfl⟩
    obtain ⟨m, rfl⟩ := hsurj n hn
    refine ⟨m.2 * x * m.2⁻¹, ?_⟩
    show ι (1, m.2 * x * m.2⁻¹) = ι m * ι (1, x) * (ι m)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg ι (Prod.ext (by simp) (by simp))
  · rintro _ ⟨x, rfl⟩ _ ⟨z, rfl⟩
    show ι (x, 1) * ι (1, z) = ι (1, z) * ι (x, 1)
    rw [← map_mul, ← map_mul]
    exact congrArg ι (Prod.ext (by simp) (by simp))
  · refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨⟨x, rfl⟩, ⟨z, hz⟩⟩ := mem_inf.1 hg
    have hz' : ι (1, z) = ι (x, 1) := hz
    have hx : x = 1 := (Prod.mk.inj (hι hz')).1.symm
    subst hx
    exact mem_bot.2 (map_one ιA)
  · intro n hn
    obtain ⟨m, rfl⟩ := hsurj n hn
    refine ⟨ιA m.1, ⟨m.1, rfl⟩, ιB m.2, ⟨m.2, rfl⟩, ?_⟩
    show ι m = ι (m.1, 1) * ι (1, m.2)
    rw [← map_mul]
    exact congrArg ι (Prod.ext (by simp) (by simp))

namespace ProdSplit

variable {N A B : Subgroup G}

theorem swap (h : ProdSplit N A B) : ProdSplit N B A where
  le_A := h.le_B
  le_B := h.le_A
  conj_A := h.conj_B
  conj_B := h.conj_A
  comm b hb a ha := (h.comm a ha b hb).symm
  inf_eq_bot := by rw [inf_comm]; exact h.inf_eq_bot
  prod n hn := by
    obtain ⟨a, ha, b, hb, rfl⟩ := h.prod n hn
    exact ⟨b, hb, a, ha, h.comm a ha b hb⟩
  isA := h.isB
  isB := h.isA

theorem centralizes_eq (h : ProdSplit N A B) :
    ∀ n ∈ N, (∀ a ∈ A, n * a = a * n) → n ∈ B := by
  intro n hn hc
  obtain ⟨a', ha', b', hb', rfl⟩ := h.prod n hn
  have h1 : a' = 1 := by
    refine h.isA.nonabSimple.center_eq_one a' ha' fun x hx => ?_
    have h2 : a' * x * b' = x * a' * b' :=
      calc a' * x * b' = a' * (x * b') := mul_assoc _ _ _
        _ = a' * (b' * x) := by rw [h.comm x hx b' hb']
        _ = a' * b' * x := (mul_assoc _ _ _).symm
        _ = x * (a' * b') := hc x hx
        _ = x * a' * b' := (mul_assoc _ _ _).symm
    exact mul_right_cancel h2
  rw [h1, one_mul]
  exact hb'

theorem conj_mem_other (h : ProdSplit N A B) (hN : ∀ g : G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hA : ∀ g : G, ∀ a ∈ A, g * a * g⁻¹ ∈ A) : ∀ g : G, ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
  intro g b hb
  refine h.centralizes_eq _ (hN g b (h.le_B hb)) fun a ha => ?_
  have h1 : g⁻¹ * a * g ∈ A := by simpa using hA g⁻¹ a ha
  have h2 := h.comm _ h1 b hb
  calc g * b * g⁻¹ * a = g * (b * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * a * g * b) * g⁻¹ := by rw [h2]
    _ = a * (g * b * g⁻¹) := by group

theorem eq_of_le_of_inf_eq_bot (h : ProdSplit N A B) {M : Subgroup G} (hM : M ≤ N)
    (hAM : A ≤ M) (hMB : M ⊓ B = ⊥) : M = A := by
  refine le_antisymm (fun m hm => ?_) hAM
  obtain ⟨a, ha, b, hb, rfl⟩ := h.prod m (hM hm)
  have hbM : b ∈ M := by simpa using M.mul_mem (M.inv_mem (hAM ha)) hm
  have hb1 : b ∈ M ⊓ B := mem_inf.2 ⟨hbM, hb⟩
  rw [hMB, mem_bot] at hb1
  rw [hb1, mul_one]
  exact ha

theorem sup_eq (h : ProdSplit N A B) : A ⊔ B = N := by
  refine le_antisymm (sup_le h.le_A h.le_B) fun n hn => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := h.prod n hn
  exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem le_of_le (h : ProdSplit N A B) {M : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) : N ≤ M := by
  rw [← h.sup_eq]
  exact sup_le hA hB

theorem centralizes_of_inf_eq_bot (h : ProdSplit N A B) {M : Subgroup G} (hM : M ≤ N)
    (hMn : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (hMA : M ⊓ A = ⊥) :
    ∀ m ∈ M, ∀ a ∈ A, m * a = a * m := by
  intro m hm a ha
  have h1 : m * a * m⁻¹ * a⁻¹ ∈ A := mul_mem (h.conj_A m (hM hm) a ha) (inv_mem ha)
  have h2 : m * (a * m⁻¹ * a⁻¹) ∈ M := mul_mem hm (hMn a (h.le_A ha) m⁻¹ (inv_mem hm))
  have h3 : m * a * m⁻¹ * a⁻¹ ∈ M ⊓ A := mem_inf.2 ⟨by simpa [mul_assoc] using h2, h1⟩
  rw [hMA, mem_bot] at h3
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)

theorem centralizes_of_inf_eq_bot_right (h : ProdSplit N A B) {M : Subgroup G} (hM : M ≤ N)
    (hMn : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (hMB : M ⊓ B = ⊥) :
    ∀ m ∈ M, ∀ b ∈ B, m * b = b * m :=
  h.swap.centralizes_of_inf_eq_bot hM hMn hMB

theorem eq_bot_of_inf_eq_bot (h : ProdSplit N A B) {M : Subgroup G} (hM : M ≤ N)
    (hMn : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (hMA : M ⊓ A = ⊥) (hMB : M ⊓ B = ⊥) :
    ∀ m ∈ M, ∀ n ∈ N, m * n = n * m := by
  intro m hm n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := h.prod n hn
  rw [← mul_assoc, h.centralizes_of_inf_eq_bot hM hMn hMA m hm a ha, mul_assoc,
    h.centralizes_of_inf_eq_bot_right hM hMn hMB m hm b hb, ← mul_assoc]

theorem inf_pow_eq_one (h : ProdSplit N A B) {a b : G} {n : ℕ} (ha : a ∈ A) (hb : b ∈ B)
    (hn : (a * b) ^ n = 1) : a ^ n = 1 ∧ b ^ n = 1 := by
  rw [Commute.mul_pow (h.comm a ha b hb)] at hn
  have h1 : a ^ n ∈ A ⊓ B := by
    refine mem_inf.2 ⟨pow_mem ha n, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hn]
    exact inv_mem (pow_mem hb n)
  rw [h.inf_eq_bot, mem_bot] at h1
  refine ⟨h1, ?_⟩
  rwa [h1, one_mul] at hn

end ProdSplit

end CFSG.EvenSporadicStandard.RuStd.S2.Close
