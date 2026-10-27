module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeFStarSimple
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace Bridge

@[expose] def NoAlt57Image (Γ : Type) [Group Γ] : Prop :=
  ∀ (H : Type) [Group H] (π : Γ →* H), Function.Surjective π → ∀ L : Subgroup H, L.Normal →
    (∀ h : H, h ^ 2 ∈ L) → ∀ m : ℕ, (m = 5 ∨ m = 7) →
      ¬ Nonempty (↥L ≃* alternatingGroup (Fin m))

structure Alt57ModelFacts : Prop where
  sp4 : ∀ (K : Type) [Field K] [Finite K], (∃ n : ℕ, Nat.card K = 2 ^ n) →
    NoAlt57Image ↥(StatedSp 2 K)
  g2 : ∀ (K : Type) [Field K] [Finite K], (∃ n : ℕ, Nat.card K = 2 ^ n) →
    NoAlt57Image ↥(quasithinG2 K)

theorem exists_mulEquiv_of_surjective_of_simple {Γ H : Type} [Group Γ] [Group H] [IsSimpleGroup Γ]
    [Nontrivial H] (π : Γ →* H) (hπ : Function.Surjective π) : Nonempty (Γ ≃* H) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 h, hπ⟩⟩
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne (1 : H)
    obtain ⟨g, rfl⟩ := hπ a
    exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide

namespace Alt57

variable {S : Type} [CommGroup S] [Finite S] {G L : Subgroup (MulAut S)} {m : ℕ}

structure Ctx (G L : Subgroup (MulAut S)) (m : ℕ) : Prop where
  m_cases : m = 5 ∨ m = 7
  iso : Nonempty (↥L ≃* alternatingGroup (Fin m))
  hF : L = quasithinGenFitting G
  hsq : ∀ y ∈ G, y ^ 2 ∈ L

namespace Ctx

variable (C : Ctx G L m)

include C

omit [Finite S] in
theorem five_le : 5 ≤ m := by rcases C.m_cases with h | h <;> omega

omit [Finite S] in
theorem simple : IsSimpleGroup ↥L := by
  obtain ⟨e⟩ := C.iso
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact C.five_le)
  exact e.isSimpleGroup

omit [Finite S] in
theorem nonab : ∃ a b : ↥L, a * b ≠ b * a := by
  obtain ⟨e⟩ := C.iso
  have h4 : 4 ≤ Nat.card (Fin m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]; have := C.five_le; omega
  have hc := alternatingGroup.center_eq_bot h4
  have : Nontrivial (alternatingGroup (Fin m)) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin m))
  have hxc : x ∈ Subgroup.center (alternatingGroup (Fin m)) :=
    Subgroup.mem_center_iff.2 fun g => by
      have := h (e.symm g) (e.symm x)
      exact e.symm.injective (by rw [map_mul, map_mul]; exact this)
  rw [hc] at hxc
  exact hx (Subgroup.mem_bot.1 hxc)

omit [Finite S] in
theorem le_G : L ≤ G :=
  FStarSimple.le_G C.hF

omit [Finite S] in
theorem normal : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L :=
  FStarSimple.normal C.hF

omit [Finite S] in
theorem center_bot : Subgroup.center ↥L = ⊥ :=
  have := C.simple
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup C.nonab).2

theorem cent_trivial : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1 :=
  FStarSimple.cent_trivial C.hF C.center_bot

theorem comm_eq {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) : ⁅L, A⁆ = L :=
  FStarSimple.comm_eq C.hF C.simple C.center_bot hA

theorem le_ffJ {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) : L ≤ ffJ G :=
  FStarSimple.le_ffJ C.hF C.simple C.center_bot hA

omit [Finite S] in
theorem card_eq : Nat.card ↥L = Nat.card (alternatingGroup (Fin m)) := by
  obtain ⟨e⟩ := C.iso
  exact Nat.card_congr e.toEquiv

omit [Finite S] in
theorem card_cases : Nat.card ↥L = 60 ∨ Nat.card ↥L = 2520 := by
  rw [C.card_eq]
  rcases C.m_cases with rfl | rfl
  · exact Or.inl card_alt_five
  · exact Or.inr card_alt_seven

end Ctx

end Alt57

end Bridge

end CFSG.QuasithinUnique
