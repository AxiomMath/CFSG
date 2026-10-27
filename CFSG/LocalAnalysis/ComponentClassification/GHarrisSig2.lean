module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSig1
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem

variable {G : Type} [Group G]

@[expose] def sigW4 (B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), oddCent (zpowers b)

theorem oddCent_le_sigW4 {B : Subgroup G} {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    oddCent (zpowers b) ≤ sigW4 B :=
  le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl))

theorem sigW4_map (φ : G ≃* G) (B : Subgroup G) :
    sigW4 (B.map φ.toMonoidHom) = (sigW4 B).map φ.toMonoidHom := by
  apply le_antisymm
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    obtain ⟨c, hc, rfl⟩ := hb
    have hc1 : c ≠ 1 := fun h => hb1 (by rw [h]; exact map_one _)
    rw [← MonoidHom.map_zpowers, oddCent_map]
    exact map_mono (oddCent_le_sigW4 hc hc1)
  · rw [sigW4, Subgroup.map_iSup]
    refine iSup_le fun b => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hb => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hb1 => ?_
    rw [← oddCent_map, MonoidHom.map_zpowers]
    exact oddCent_le_sigW4 ⟨b, hb, rfl⟩ fun h => hb1 (φ.injective (h.trans (map_one φ).symm))

theorem normalizer_le_sigW4 (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer (sigW4 B : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  have h := sigW4_map (MulAut.conj g) B
  rw [MulEquiv.toMonoidHom_eq_coe] at h
  rw [← h, hg]

variable [Finite G]

theorem sigW_eq_sigW4 {A B : Subgroup G} (hA : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A)
    (hch : CharTwoAt A) (hBA : B ≤ A) (h4 : 4 ≤ Nat.card B) : sigW A = sigW4 B := by
  obtain ⟨⟨hcop, hnorm⟩, hcap⟩ := sigW_spec hA h8 hch
  have hB : IsElemAbelian 2 B := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hA.2 x (hBA hx)⟩
    show (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, hBA a.2⟩ ⟨b, hBA b.2⟩)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hB (by simpa using h4) (hBA.trans hnorm) hcop
  rw [← hgen]
  refine iSup_congr fun b => iSup_congr fun hb => iSup_congr fun hb1 => ?_
  have hS : zpowers b ∈ signalizerFunctorEk 2 1 A := by
    refine ⟨zpowers_le.mpr (hBA hb), ?_⟩
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (hA.2 b (hBA hb)) hb1
  rw [← hcap _ hS, zpowers_eq_closure, centralizer_closure]

end CFSG.ComponentClassification.GHarris
