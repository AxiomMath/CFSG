module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBoundsGL
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SingerCoord
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.GL4Rep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix

variable {G : Type} [Group G] [Finite G] {L S A B : Subgroup G} {z : G}

namespace SylowBounds

theorem exists_action (W : ThLocalIn L S A B z) {Y : Subgroup G} (hYL : Y ≤ L)
    (hYn : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ ∈ A) :
    ∃ ρ : ↥Y →* GL (Fin 4) (ZMod 2),
      (∀ y : Y, ρ y = 1 ↔ (y : G) ∈ B) ∧
      ∀ y : Y, fixCard ((ρ y : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        Nat.card ↥(A ⊓ centralizer ({(y : G)} : Set G)) := by
  obtain ⟨k, c, j, hkL, hkA, hkodd, hkfix, hj, hcmul, hcinj, hconto, hck⟩ :=
    exists_singer_coord W.A_comm W.A_sq W.A_card W.surj
  have hc : IsCoord A c := ⟨hcmul, hcinj, hconto⟩
  obtain ⟨m, hm⟩ := hc.exists_matHom Y hYn
  refine ⟨m.toHomUnits, fun y => ?_, fun y => ?_⟩
  · have hy1 : ((m.toHomUnits y : GL (Fin 4) (ZMod 2)) = 1) ↔ m y = 1 := by
      rw [Units.ext_iff]
      rfl
    rw [hy1]
    constructor
    · intro h1
      refine (W.mem_B_iff y (hYL y.2)).2 fun a ha => ?_
      have h2 : c ((y : G) * a * (y : G)⁻¹) = c a := by
        rw [hm y a ha, h1, Matrix.one_mulVec]
      have h3 := hc.inj _ (hYn y y.2 a ha) _ ha h2
      calc (y : G) * a = ((y : G) * a * (y : G)⁻¹) * y := by group
        _ = a * y := by rw [h3]
    · intro hyB
      have hcomm := (W.mem_B_iff y (hYL y.2)).1 hyB
      refine hc.rep_unique (hm y) fun a ha => ?_
      rw [Matrix.one_mulVec]
      have : (y : G) * a * (y : G)⁻¹ = a := by rw [hcomm a ha]; group
      rw [this]
  · rw [fixCard_eq_natCard]
    have hval : ((m.toHomUnits y : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        m y := rfl
    rw [hval]
    have hconj : ∀ a ∈ A, (y : G) * a * (y : G)⁻¹ = a ↔ (y : G) * a = a * y := fun a _ => by
      constructor
      · intro h
        calc (y : G) * a = ((y : G) * a * (y : G)⁻¹) * y := by group
          _ = a * y := by rw [h]
      · intro h
        rw [h]
        group
    have hfix : ∀ a : ↥(A ⊓ centralizer ({(y : G)} : Set G)), m y *ᵥ c a = c a := fun a => by
      have h1 := hm y a a.2.1
      have h2 := (hconj a a.2.1).2 (mem_centralizer_singleton_iff.1 a.2.2).symm
      rw [← h1, h2]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun a : ↥(A ⊓ centralizer ({(y : G)} : Set G)) =>
        (⟨c a, hfix a⟩ : {v : Fin 4 → ZMod 2 // m y *ᵥ v = v})) ⟨?_, ?_⟩)).symm
    · intro a a' h
      have h' : c a = c a' := congrArg Subtype.val h
      exact Subtype.ext (hc.inj _ a.2.1 _ a'.2.1 h')
    · rintro ⟨v, hv⟩
      obtain ⟨a, haA, rfl⟩ := hc.onto v
      have h1 := hm y a haA
      have h2 : c ((y : G) * a * (y : G)⁻¹) = c a := by rw [h1]; exact hv
      have h3 := hc.inj _ (hYn y y.2 a haA) _ haA h2
      have h4 := (hconj a haA).1 h3
      exact ⟨⟨a, haA, mem_centralizer_singleton_iff.2 h4.symm⟩, rfl⟩

omit [Finite G] in
theorem natCard_ker_eq_natCard_inf {Y : Subgroup G} {H : Type*} [Group H] (ρ : ↥Y →* H)
    (hρ : ∀ y : Y, ρ y = 1 ↔ (y : G) ∈ B) : Nat.card ρ.ker = Nat.card ↥(Y ⊓ B) := by
  have h : ρ.ker.map Y.subtype = Y ⊓ B := by
    ext x
    simp only [mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype, mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hρ y).1 hy⟩
    · rintro ⟨hxY, hxB⟩
      exact ⟨⟨x, hxY⟩, (hρ ⟨x, hxY⟩).2 hxB, rfl⟩
  rw [← h, Subgroup.card_map_of_injective Y.subtype_injective]

omit [Finite G] in
theorem natCard_eq_mul_natCard_inf {Y : Subgroup G} {H : Type*} [Group H] (ρ : ↥Y →* H)
    (hρ : ∀ y : Y, ρ y = 1 ↔ (y : G) ∈ B) :
    Nat.card Y = Nat.card ρ.range * Nat.card ↥(Y ⊓ B) := by
  rw [← natCard_ker_eq_natCard_inf ρ hρ, mul_comm]
  exact (Subgroup.card_ker_mul_card_range ρ).symm

end SylowBounds

end CFSG.EvenSporadicStandard.ThStd
