module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

variable {X : Type} [Group X]

structure Hyp42 (G T S : Subgroup X) : Prop where
  frame : Frame G T
  sylow : IsSylowOf 2 S (G ⊔ T)
  le : T ≤ S
  closed : ∀ g ∈ G, rightConjugate T g ≤ S → rightConjugate T g = T

theorem map_rightConjugate {Y : Type*} [Group Y] (f : X →* Y) (P : Subgroup X) (g : X) :
    (rightConjugate P g).map f = rightConjugate (P.map f) (f g) := by
  ext y
  rw [Subgroup.mem_map, mem_rightConjugate_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_rightConjugate_iff] at hx
    exact ⟨g * x * g⁻¹, hx, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hx
    · rw [map_mul, map_mul, map_inv, hxy]
      group

theorem Frame.commutator_le {G T : Subgroup X} (hF : Frame G T) : ⁅G, T⁆ ≤ G := by
  rw [Subgroup.commutator_le]
  intro g hg t ht
  rw [commutatorElement_def]
  have h1 : t * g⁻¹ * t⁻¹ ∈ G :=
    (Subgroup.mem_normalizer_iff.mp (hF.le_normalizer ht) _).mp (G.inv_mem hg)
  simpa [mul_assoc] using G.mul_mem hg h1

theorem oddCore_eq_componentClassificationOddCore (H : Type*) [Group H] :
    CFSG.oddCore H = CFSG.Open.componentClassificationOddCore H := rfl

theorem odd_card_oddCore (H : Type*) [Group H] [Finite H] : Odd (Nat.card (CFSG.oddCore H)) :=
  OddCore.odd_card H

theorem map_oddCore_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.oddCore A).map e.toMonoidHom = CFSG.oddCore B :=
  OddCore.equiv_invariant e

theorem comap_oddCore_le {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B)
    (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) :
    (CFSG.oddCore B).comap φ ≤ CFSG.oddCore A := by
  have : Finite B := Finite.of_surjective φ hφ
  set L := (CFSG.oddCore B).comap φ
  have hLn : L.Normal := Subgroup.Normal.comap (CFSG.oddCore_normal B) φ
  have hkerL : φ.ker ≤ L := Subgroup.ker_le_comap φ _
  have hmap : L.map φ = CFSG.oddCore B := Subgroup.map_comap_eq_self_of_surjective hφ _
  have hcard : Nat.card φ.ker * φ.ker.relIndex L = Nat.card L := by
    have hmul := (φ.ker.subgroupOf L).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerL).toEquiv] at hmul
    exact hmul
  have hindex : φ.ker.relIndex L = Nat.card (CFSG.oddCore B) := by
    have hrel := Subgroup.relIndex_ker L φ
    rw [hmap] at hrel
    exact hrel
  have hodd : Odd (Nat.card L) := by
    rw [← hcard, hindex]
    exact hker.mul (odd_card_oddCore B)
  exact le_sSup ⟨hLn, hodd⟩

theorem le_map_oddCore {G P : Subgroup X} (hPG : P ≤ G)
    (hN : G ≤ Subgroup.normalizer (P : Set X)) (hodd : Odd (Nat.card P)) :
    P ≤ (CFSG.oddCore G).map G.subtype := by
  have hn : (P.subgroupOf G).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPG).mpr hN
  have hodd' : Odd (Nat.card (P.subgroupOf G)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv]
  have hle : P.subgroupOf G ≤ CFSG.oddCore G := le_sSup ⟨hn, hodd'⟩
  intro x hx
  exact ⟨⟨x, hPG hx⟩, hle hx, rfl⟩

namespace Hyp42

variable {G T S : Subgroup X}

theorem restrict [Finite X] (h : Hyp42 G T S) :
    Hyp42 (G.subgroupOf (G ⊔ T)) (T.subgroupOf (G ⊔ T)) (S.subgroupOf (G ⊔ T)) where
  frame :=
    { le_normalizer := by
        rw [← Subgroup.subgroupOf_normalizer_eq le_sup_left]
        exact fun x hx => h.frame.le_normalizer hx
      inf_eq_bot := by
        rw [eq_bot_iff]
        rintro x ⟨hxT, hxG⟩
        have hmem : (x : X) ∈ T ⊓ G := ⟨hxT, hxG⟩
        rw [h.frame.inf_eq_bot, Subgroup.mem_bot] at hmem
        exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
      isPGroup := h.frame.isPGroup.comap_subtype }
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self,
      isSylowOf_iff]
    obtain ⟨-, hS2, hdvd⟩ := isSylowOf_iff.mp h.sylow
    exact ⟨le_top, hS2.comap_subtype, by rwa [Subgroup.relIndex_top_right]⟩
  le := fun x hx => h.le hx
  closed := by
    intro g hg hle
    set L := G ⊔ T
    have hTL : T ≤ L := le_sup_right
    have hSL : S ≤ L := h.sylow.le
    have hmapT : (T.subgroupOf L).map L.subtype = T := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTL]
    have hmapS : (S.subgroupOf L).map L.subtype = S := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSL]
    have hle' := Subgroup.map_mono (f := L.subtype) hle
    rw [map_rightConjugate, hmapT, hmapS] at hle'
    apply Subgroup.map_injective L.subtype_injective
    rw [map_rightConjugate, hmapT]
    exact h.closed _ hg hle'

end Hyp42

theorem commutator_le_oddCore_of_restrict {G T : Subgroup X}
    (h : ⁅G.subgroupOf (G ⊔ T), T.subgroupOf (G ⊔ T)⁆ ≤
      (CFSG.oddCore (G.subgroupOf (G ⊔ T))).map (G.subgroupOf (G ⊔ T)).subtype) :
    ⁅G, T⁆ ≤ (CFSG.oddCore G).map G.subtype := by
  set L := G ⊔ T
  have hmap := Subgroup.map_mono (f := L.subtype) h
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (le_sup_left : G ≤ L), inf_eq_left.mpr (le_sup_right : T ≤ L)] at hmap
  refine hmap.trans ?_
  rw [Subgroup.map_map]
  let e : G.subgroupOf L ≃* G := Subgroup.subgroupOfEquivOfLe le_sup_left
  have hcomp : L.subtype.comp (G.subgroupOf L).subtype = G.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, map_oddCore_equiv e]

namespace Hyp42

variable {G T S : Subgroup X}

theorem quotient [Finite X] (h : Hyp42 G T S) (htop : G ⊔ T = ⊤) (N : Subgroup X) [N.Normal]
    (hTG : ∀ t ∈ T, ∀ g ∈ G, g⁻¹ * t ∈ N → g ∈ N)
    (hwc : ∀ g ∈ G, rightConjugate T g ≤ S ⊔ N →
      ∃ m ∈ N, rightConjugate T g = rightConjugate T m) :
    Hyp42 (G.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N))
      (S.map (QuotientGroup.mk' N)) where
  frame :=
    { le_normalizer := (Subgroup.map_mono h.frame.le_normalizer).trans
        (Subgroup.le_normalizer_map _)
      inf_eq_bot := by
        rw [eq_bot_iff]
        rintro x ⟨⟨t, ht, rfl⟩, ⟨g, hg, hgt⟩⟩
        have hmem : g⁻¹ * t ∈ N := QuotientGroup.eq.mp hgt
        have hgN := hTG t ht g hg hmem
        rw [Subgroup.mem_bot, ← hgt]
        exact (QuotientGroup.eq_one_iff g).mpr hgN
      isPGroup := h.frame.isPGroup.map _ }
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Subgroup.map_sup, htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
      isSylowOf_iff]
    obtain ⟨-, hS2, hdvd⟩ := isSylowOf_iff.mp h.sylow
    rw [htop, Subgroup.relIndex_top_right] at hdvd
    refine ⟨le_top, hS2.map _, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact fun hdvd' => hdvd (hdvd'.trans
      (Subgroup.index_map_dvd S (QuotientGroup.mk'_surjective N)))
  le := Subgroup.map_mono h.le
  closed := by
    rintro _ ⟨g, hg, rfl⟩ hle
    rw [← map_rightConjugate] at hle ⊢
    have hle' : rightConjugate T g ≤ S ⊔ N := by
      rw [← QuotientGroup.ker_mk' N, ← Subgroup.comap_map_eq]
      exact Subgroup.map_le_iff_le_comap.mp hle
    obtain ⟨m, hm, heq⟩ := hwc g hg hle'
    rw [heq, map_rightConjugate, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff m).mpr hm,
      rightConjugate_one]

end Hyp42

theorem commutator_le_oddCore_of_quotient [Finite X] {G T : Subgroup X} (hF : Frame G T)
    (N : Subgroup X) [N.Normal] (hodd : Odd (Nat.card (N ⊓ G : Subgroup X)))
    (h : ⁅G.map (QuotientGroup.mk' N), T.map (QuotientGroup.mk' N)⁆ ≤
      (CFSG.oddCore (G.map (QuotientGroup.mk' N))).map (G.map (QuotientGroup.mk' N)).subtype) :
    ⁅G, T⁆ ≤ (CFSG.oddCore G).map G.subtype := by
  set π := QuotientGroup.mk' N
  intro x hx
  have hxG : x ∈ G := hF.commutator_le hx
  have hπx : π x ∈ (CFSG.oddCore (G.map π)).map (G.map π).subtype := by
    apply h
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem π hx
  obtain ⟨y, hy, hyx⟩ := hπx
  set φ := π.subgroupMap G
  have hker : φ.ker = N.subgroupOf G := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (N := N) (z : X)]
    constructor
    · intro hz
      have := congrArg Subtype.val hz
      rwa [MonoidHom.subgroupMap_apply_coe] at this
    · intro hz
      exact Subtype.ext (by rw [MonoidHom.subgroupMap_apply_coe]; exact hz)
  have hkerodd : Odd (Nat.card φ.ker) := by
    rw [hker, ← Subgroup.card_map_of_injective G.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact hodd
  have hle := comap_oddCore_le φ (π.subgroupMap_surjective G) hkerodd
  have hφx : φ ⟨x, hxG⟩ = y :=
    Subtype.ext (by rw [MonoidHom.subgroupMap_apply_coe]; exact hyx.symm)
  have hmem : (⟨x, hxG⟩ : G) ∈ (CFSG.oddCore (G.map π)).comap φ := by
    rw [Subgroup.mem_comap, hφx]
    exact hy
  exact ⟨⟨x, hxG⟩, hle hmem, rfl⟩

theorem card_quotient_lt [Finite X] {N : Subgroup X} [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (X ⧸ N) < Nat.card X := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  have h1 : 1 < Nat.card N := by
    rw [Finite.one_lt_card_iff_nontrivial, Subgroup.nontrivial_iff_ne_bot]
    exact hN
  have h2 : 0 < Nat.card (X ⧸ N) := Nat.card_pos
  calc Nat.card (X ⧸ N) = Nat.card (X ⧸ N) * 1 := (mul_one _).symm
    _ < Nat.card (X ⧸ N) * Nat.card N := Nat.mul_lt_mul_of_pos_left h1 h2

end CFSG.ComponentClassification.AschbacherTheorem3
