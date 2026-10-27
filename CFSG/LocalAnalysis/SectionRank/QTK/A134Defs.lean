module

public import CFSG.Quasithin.Background.A3Structure38Facts
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.SectionRank.QTK

open Subgroup CFSG.LocalCores

@[expose] def IsoComponentBound (H : Type) [Group H] [Finite H] (r : ℕ) : Prop :=
  (∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ ≠ L₂ →
      Nonempty (↥L₁ ≃* ↥L₂) → ∀ R : Subgroup (↥L₁ ⧸ center ↥L₁), R ≠ ⊥ → IsPGroup 2 R →
        CFSG.Open.pRank r (normalizer (R : Set (↥L₁ ⧸ center ↥L₁))) +
          CFSG.Open.pRank r (⊤ : Subgroup (↥L₂ ⧸ center ↥L₂)) ≤ 2) ∧
    (∀ L₁ L₂ L₃ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → CFSG.IsComponent L₃ →
      L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → Nonempty (↥L₁ ≃* ↥L₂) → Nonempty (↥L₁ ≃* ↥L₃) →
        ∀ R : Subgroup (↥L₁ ⧸ center ↥L₁), R ≠ ⊥ → IsPGroup 2 R →
          CFSG.Open.pRank r (normalizer (R : Set (↥L₁ ⧸ center ↥L₁))) +
            CFSG.Open.pRank r (⊤ : Subgroup (↥L₂ ⧸ center ↥L₂)) +
              CFSG.Open.pRank r (⊤ : Subgroup (↥L₃ ⧸ center ↥L₃)) ≤ 2)

@[expose] def QTLayerCentreFactOne : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Quasithin.IsQuasithin H →
    CFSG.SectionRank.IsKGroupCat H →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥(CFSG.layer H)) →
      IsoComponentBound H r ∨
      (r = 3 ∧ ∃ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ ∧ CFSG.IsComponent L₂ ∧ L₁ ≠ L₂ ∧
        CFSG.layer H = L₁ ⊔ L₂ ∧ (Nonempty (↥L₁ ≃* ↥L₂) →
          CFSG.Quasithin.IsSU3 8 ↥L₁ ∧ CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3))

@[expose] def QTA134List : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Milestones.SQTKSimpleList S →
    (∀ r : ℕ, r.Prime → r ≠ 2 → ∀ R : Subgroup S, R ≠ ⊥ → IsPGroup 2 R →
      CFSG.Open.pRank r (normalizer (R : Set S)) + CFSG.Open.pRank r (⊤ : Subgroup S) ≤ 2) →
    CFSG.Quasithin.A134Types S

theorem eq_or_eq_of_layer_eq_sup {H : Type} [Group H] [Finite H] {L₁ L₂ L : Subgroup H}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (hlayer : CFSG.layer H = L₁ ⊔ L₂)
    (hL : CFSG.IsComponent L) : L = L₁ ∨ L = L₂ := by
  by_contra hcon
  push Not at hcon
  have c1 : ⁅L, L₁⁆ = ⊥ := (distinct_components_commute hL h₁).resolve_left hcon.1
  have c2 : ⁅L, L₂⁆ = ⊥ := (distinct_components_commute hL h₂).resolve_left hcon.2
  have hcen : L₁ ⊔ L₂ ≤ centralizer (L : Set H) := sup_le
    (commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact c1))
    (commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact c2))
  have hLL : ⁅L, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((component_le_layer hL).trans (hlayer.le.trans hcen))
  have hperf : ⁅L, L⁆ = L := by
    have h := hL.1.1.commutator_eq_top
    rw [_root_.commutator_def] at h
    have := congrArg (Subgroup.map L.subtype) h
    rwa [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at this
  have hbot : L = ⊥ := hperf.symm.trans hLL
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ a.2))
  have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ b.2))
  exact hab (by rw [ha, hb])

theorem isSU3_of_mulEquiv {X Y : Type} [Group X] [Group Y] {q : ℕ} (e : X ≃* Y)
    (h : CFSG.Quasithin.IsSU3 q Y) : CFSG.Quasithin.IsSU3 q X := by
  obtain ⟨K, hF, hfin, hK, ⟨e'⟩⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨e.trans e'⟩⟩

theorem isElemAbelian_zpowers {G : Type*} [Group G] {x : G} {r : ℕ} (hx : x ^ r = 1) :
    CFSG.Open.IsElemAbelian r (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

end CFSG.SectionRank.QTK
