module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpBasic
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpUnitary

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.BorelTits CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.ComponentInitial
  Module
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Spaces

@[expose] noncomputable def te6Minus (p f : ℕ) [Fact p.Prime] :
    Submodule (GaloisField p (2 * f)) (Fin (5 + 1) → GaloisField p (2 * f)) :=
  minusSpaceSU (te6Inv p f)

@[expose] noncomputable def te6Plus (p f : ℕ) [Fact p.Prime] :
    Submodule (GaloisField p (2 * f)) (Fin (5 + 1) → GaloisField p (2 * f)) :=
  perp (unitaryInvolution (GaloisField p (2 * f)) p f) (te6Minus p f)

theorem unitaryFieldData_te6 (hf : 1 ≤ f) : UnitaryFieldData p f (GaloisField p (2 * f)) :=
  ⟨Fact.out, hf, GaloisField.card p (2 * f) (by omega)⟩

theorem te6Minus_nondeg (hp2 : p ≠ 2) :
    Nondeg (unitaryInvolution (GaloisField p (2 * f)) p f) (te6Minus p f) :=
  (isLongRootSU2_te6Node hp2).nondeg_minusSpaceSU hp2

theorem finrank_te6Minus (hp2 : p ≠ 2) : finrank (GaloisField p (2 * f)) (te6Minus p f) = 2 :=
  (isLongRootSU2_te6Node hp2).finrank_minusSpaceSU (two_ne_zero_te6 hp2)

theorem te6Plus_nondeg (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Nondeg (unitaryInvolution (GaloisField p (2 * f)) p f) (te6Plus p f) :=
  nondeg_herm_perp (isUnitaryInvolution_unitaryInvolution (card_galoisField_two_mul p f hf))
    (te6Minus_nondeg hp2)

theorem finrank_te6Plus (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    finrank (GaloisField p (2 * f)) (te6Plus p f) = 4 := by
  have := finrank_add_finrank_herm_perp
    (isUnitaryInvolution_unitaryInvolution (card_galoisField_two_mul p f hf))
    (te6Minus_nondeg hp2)
  rw [finrank_te6Minus hp2] at this
  unfold te6Plus
  omega

theorem te6Node_eq (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    te6Node p f = planeGroupU (GaloisField p (2 * f)) p f (te6Minus p f) := by
  have hK := card_galoisField_two_mul p f hf
  have hnode := isLongRootSU2_te6Node (p := p) (f := f) hp2
  ext x
  rw [hnode.mem_iff_fix hK hp2]
  unfold planeGroupU te6Minus
  rw [mem_fixingSubgroup_iff, hnode.perp_minusSpaceSU hK hp2]
  rfl

theorem ne_te6Minus_of_le (hp2 : p ≠ 2)
    {P : Submodule (GaloisField p (2 * f)) (Fin (5 + 1) → GaloisField p (2 * f))}
    (hP2 : finrank (GaloisField p (2 * f)) P = 2) (hle : P ≤ te6Plus p f) : P ≠ te6Minus p f := by
  intro hPE
  have h0 : P = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro s hs
    exact te6Minus_nondeg hp2 s (hPE ▸ hs) fun t ht => hle hs t ht
  rw [h0, finrank_bot] at hP2
  omega

theorem planeGroupU_le_centralizer (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {P : Submodule (GaloisField p (2 * f)) (Fin (5 + 1) → GaloisField p (2 * f))}
    (hP : Nondeg (unitaryInvolution (GaloisField p (2 * f)) p f) P)
    (hP2 : finrank (GaloisField p (2 * f)) P = 2) (hle : P ≤ te6Plus p f) :
    planeGroupU (GaloisField p (2 * f)) p f P ≤ Subgroup.centralizer ({te6Inv p f} : Set _) := by
  have hK := card_galoisField_two_mul p f hf
  have hc := (commutes_planeGroupU_iff hK hp2 (by norm_num : 2 ≤ 5 + 1)
    (by norm_num : 3 ≤ 5 + 1) hP hP2 (te6Minus_nondeg hp2) (finrank_te6Minus hp2)
    (ne_te6Minus_of_le hp2 hP2 hle)).mpr fun u hu v hv => hle hu v hv
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hmem : te6Inv p f ∈ planeGroupU (GaloisField p (2 * f)) p f (te6Minus p f) :=
    (te6Node_eq hp2 hf) ▸ (isLongRootSU2_te6Node hp2).mem
  exact (hc x hx _ hmem).symm

end Spaces

section Count

@[expose] noncomputable def layerOfPlane (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Option (Planes (GaloisField p (2 * f)) p f (te6Plus p f)) →
      {x : TE6Layer p f // x ≠ none}
  | none => ⟨te6NodePoint hp2, te6NodePoint_ne_none hp2⟩
  | some P => ⟨some ⟨planeGroupU (GaloisField p (2 * f)) p f P.1,
      planeGroupU_mem (card_galoisField_two_mul p f hf) hp2 (by norm_num) P.2.1 P.2.2.1,
      planeGroupU_le_centralizer hp2 hf P.2.1 P.2.2.1 P.2.2.2⟩, Option.some_ne_none _⟩

theorem layerOfPlane_bijective (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Function.Bijective (layerOfPlane hp2 hf) := by
  have hK := card_galoisField_two_mul p f hf
  have hn : 2 ≤ 5 + 1 := by norm_num
  have hn3 : 3 ≤ 5 + 1 := by norm_num
  have hnode := te6Node_eq hp2 hf
  have hE := te6Minus_nondeg (p := p) (f := f) hp2
  have hE2 := finrank_te6Minus (p := p) (f := f) hp2
  refine ⟨?_, ?_⟩
  · rintro (_ | P) (_ | P') h
    · rfl
    · exfalso
      have h1 : te6Node p f = planeGroupU (GaloisField p (2 * f)) p f P'.1 := by
        simp only [layerOfPlane, te6NodePoint, Subtype.mk.injEq, Option.some.injEq] at h
        exact h
      exact ne_te6Minus_of_le hp2 P'.2.2.1 P'.2.2.2
        (planeGroupU_injective hK hp2 hn P'.2.1 P'.2.2.1 hE hE2 (h1.symm.trans hnode))
    · exfalso
      have h1 : planeGroupU (GaloisField p (2 * f)) p f P.1 = te6Node p f := by
        simp only [layerOfPlane, te6NodePoint, Subtype.mk.injEq, Option.some.injEq] at h
        exact h
      exact ne_te6Minus_of_le hp2 P.2.2.1 P.2.2.2
        (planeGroupU_injective hK hp2 hn P.2.1 P.2.2.1 hE hE2 (h1.trans hnode))
    · have h1 : planeGroupU (GaloisField p (2 * f)) p f P.1 =
          planeGroupU (GaloisField p (2 * f)) p f P'.1 := by
        simp only [layerOfPlane, Subtype.mk.injEq, Option.some.injEq] at h
        exact h
      exact congrArg some (Subtype.ext (planeGroupU_injective hK hp2 hn P.2.1 P.2.2.1
        P'.2.1 P'.2.2.1 h1))
  · rintro ⟨_ | ⟨R, hR, hRc⟩, hx⟩
    · exact absurd rfl hx
    · by_cases hRn : R = te6Node p f
      · subst hRn
        exact ⟨none, Subtype.ext rfl⟩
      · obtain ⟨P, hPnd, hP2, rfl⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp hR
        have hPne : P ≠ te6Minus p f := fun e => hRn (by rw [hnode, e])
        have hcomm : Commutes (planeGroupU (GaloisField p (2 * f)) p f P) (te6Node p f) :=
          TE6Layer.rel_node hp2 hf (some ⟨_, hR, hRc⟩) (fun e => hRn (congrArg Subtype.val
            (Option.some.inj e)))
        have hOrth := (commutes_planeGroupU_iff hK hp2 hn hn3 hPnd hP2 hE hE2 hPne).mp
          (hnode ▸ hcomm)
        exact ⟨some ⟨P, hPnd, hP2, fun u hu v hv => hOrth u hu v hv⟩, Subtype.ext rfl⟩

theorem card_te6Layer (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Nat.card (TE6Layer p f) = Nat.card (Planes (GaloisField p (2 * f)) p f (te6Plus p f)) + 2 := by
  rw [← card_ne_none_add_one, ← Nat.card_eq_of_bijective _ (layerOfPlane_bijective hp2 hf)]
  have := Fintype.ofFinite (Planes (GaloisField p (2 * f)) p f (te6Plus p f))
  simp [Nat.card_eq_fintype_card, Fintype.card_option]

theorem card_te6Layer_eq (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 2 ≤ p ^ f) :
    Nat.card (TE6Layer p f) = te6Core (p ^ f) + 2 := by
  rw [card_te6Layer hp2 hf, card_planes (unitaryFieldData_te6 hf) (te6Plus_nondeg hp2 hf)
    (finrank_te6Plus hp2 hf) hq]

end Count

end CFSG.ClassicalInvolution.RouteD.NonClassical
