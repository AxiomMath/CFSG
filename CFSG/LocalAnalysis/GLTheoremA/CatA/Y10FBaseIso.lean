module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Iso

variable {X Y : Type} [Group X] [Group Y]

theorem isElemAbelian_map_iff_of_injective {p : ℕ} {ι : X →* Y} (hι : Function.Injective ι)
    (H : Subgroup X) : IsElemAbelian p (H.map ι) ↔ IsElemAbelian p H := by
  constructor
  · intro h
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have h1 := isElemAbelian_commute h (Subgroup.mem_map_of_mem ι a.2)
        (Subgroup.mem_map_of_mem ι b.2)
      exact hι (by rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]; exact h1)
    · exact hι (by rw [map_pow, map_one]; exact h.2 (ι x) (Subgroup.mem_map_of_mem ι hx))
  · intro h
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
      show (a : Y) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, isElemAbelian_commute h ha' hb']
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      rw [← map_pow, h.2 x hx, map_one]

theorem pRank_map_of_injective [Finite X] [Finite Y] {p : ℕ} {ι : X →* Y}
    (hι : Function.Injective ι) (H : Subgroup X) :
    CFSG.Open.pRank p (H.map ι) = CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hE, hEA, hcard⟩
    have hEr : E ≤ ι.range := hE.trans (Subgroup.map_le_range ι H)
    refine ⟨E.comap ι, ?_, (isElemAbelian_map_iff_of_injective hι _).1 ?_, ?_⟩
    · intro x hx
      have := hE hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 this
      have : y = x := hι hyx
      exact this ▸ hy
    · rw [Subgroup.map_comap_eq_self hEr]; exact hEA
    · rw [← hcard, ← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hEr]
  · rintro ⟨E', hE', hE'A, hcard⟩
    refine ⟨E'.map ι, Subgroup.map_mono hE', (isElemAbelian_map_iff_of_injective hι _).2 hE'A, ?_⟩
    rw [Subgroup.card_map_of_injective hι]; exact hcard

theorem pRank_top_congr [Finite X] [Finite Y] {p : ℕ} (e : X ≃* Y) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) = CFSG.Open.pRank p (⊤ : Subgroup X) := by
  rw [← pRank_map_of_injective (ι := e.toMonoidHom) e.injective (⊤ : Subgroup X),
    Subgroup.map_top_of_surjective _ e.surjective]

theorem twoRank_congr [Finite X] [Finite Y] (e : X ≃* Y) :
    CFSG.Open.twoRank Y = CFSG.Open.twoRank X :=
  pRank_top_congr e

theorem card_center_congr (e : X ≃* Y) :
    Nat.card (Subgroup.center Y) = Nat.card (Subgroup.center X) := by
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.card_map_of_injective e.injective

theorem card_quot_center_congr (e : X ≃* Y) :
    Nat.card (Y ⧸ Subgroup.center Y) = Nat.card (X ⧸ Subgroup.center X) :=
  Nat.card_congr
    (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
      (Subgroup.map_center_eq e)).symm.toEquiv

theorem center_eq_bot_congr (e : X ≃* Y) :
    Subgroup.center Y = ⊥ ↔ Subgroup.center X = ⊥ := by
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) (f := (e : X →* Y)) e.injective

theorem trivialMultiplier_congr (e : X ≃* Y) :
    (∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ → ∀ π : E →* X, Function.Surjective π →
        π.ker ≤ Subgroup.center E → π.ker = ⊥) ↔
      (∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ → ∀ π : E →* Y, Function.Surjective π →
        π.ker ≤ Subgroup.center E → π.ker = ⊥) := by
  constructor
  · intro h E _ _ hE π hπ hker
    have := h E hE (e.symm.toMonoidHom.comp π) (e.symm.surjective.comp hπ) (by
      intro z hz
      apply hker
      simpa using hz)
    have hk : (e.symm.toMonoidHom.comp π).ker = π.ker := by
      ext z; simp
    rw [← hk]; exact this
  · intro h E _ _ hE π hπ hker
    have := h E hE (e.toMonoidHom.comp π) (e.surjective.comp hπ) (by
      intro z hz
      apply hker
      simpa using hz)
    have hk : (e.toMonoidHom.comp π).ker = π.ker := by
      ext z; simp
    rw [← hk]; exact this

end Iso

end CFSG.LocalAnalysis.GLTheoremA.Y10F
