module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Setup
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG.Open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem commutator_equiv_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (φ : K ≃* K') :
    Nonempty (↥(commutator K) ≃* ↥(commutator K')) := by
  have h1 : commutator K = ⁅(⊤ : Subgroup K), ⊤⁆ := rfl
  have h2 : commutator K' = ⁅(⊤ : Subgroup K'), ⊤⁆ := rfl
  have h : (commutator K).map φ.toMonoidHom = commutator K' := by
    rw [h1, h2, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  exact ⟨((commutator K).equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr h)⟩

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} [S.Normal] {t : G}

theorem harris_fixed_data (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Nat.card ↥(CFSG.EvenSporadicStandard.HSStd.autCentralizer
        (MulAut.conjNormal t : MulAut ↥S)) ≤ 5760 ∧
      Nonempty (↥(commutator ↥(CFSG.EvenSporadicStandard.HSStd.autCentralizer
        (MulAut.conjNormal t : MulAut ↥S))) ≃* alternatingGroup (Fin 6)) := by
  let φ : ↥(CFSG.EvenSporadicStandard.HSStd.autCentralizer (MulAut.conjNormal t : MulAut ↥S)) ≃*
      ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) :=
    MulEquiv.subgroupCongr (autCentralizer_eq_fixedSubgroup _)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr φ.toEquiv]
    have := Nat.le_of_dvd (by norm_num) (card_fixed_dvd (S := S) ζ)
    omega
  · obtain ⟨e⟩ := commutator_fixed_equiv h ζ
    obtain ⟨c⟩ := commutator_equiv_of_mulEquiv φ
    exact ⟨c.trans e⟩

theorem harris_a6Hyp (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    ∃ D : Subgroup ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)),
      D = commutator ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) ∧
        A6Hyp (MulAut.conjNormal t : MulAut ↥S) D := by
  obtain ⟨-, ⟨e⟩⟩ := harris_fixed_data h ζ
  exact a6Hyp_of_derived _ e

theorem card_fixed_values {N : ℕ} (h360 : 360 ∣ N) (hdvd : N ∣ 2880) :
    N = 360 ∨ N = 720 ∨ N = 1440 ∨ N = 2880 := by
  obtain ⟨m, rfl⟩ := h360
  have hm : m ≤ 8 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases m <;> omega

theorem mem_of_card_fixed_eq (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    (hN : Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) = 2880) : t ∈ S := by
  have hinf : Nat.card ↥(S ⊓ centralizer ({t} : Set G)) =
      Nat.card ↥(centralizer ({t} : Set G)) := by
    rw [← card_fixedSubgroup_eq t, hN, card_centralizer_eq ζ]
  have hEq : S ⊓ centralizer ({t} : Set G) = centralizer ({t} : Set G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_right hinf.ge
  have htC : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have : t ∈ S ⊓ centralizer ({t} : Set G) := by
    rw [hEq]
    exact htC
  exact this.1

theorem excl_of_sharp (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    (hA : Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) ≠ 1440 ∧
      ((MulAut.conjNormal t : MulAut ↥S) ∈ (MulAut.conj : ↥S →* MulAut ↥S).range →
        Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) ≠ 2880))
    (hB : ¬ OuterKlein (MulAut.conjNormal t : MulAut ↥S)) : False := by
  have hcases := card_fixed_values (dvd_card_fixed h ζ) (card_fixed_dvd (S := S) ζ)
  rcases hcases with h1 | h1 | h1 | h1
  · exact hB (outerKlein_of_card_le h ζ (by omega))
  · exact hB (outerKlein_of_card_le h ζ (by omega))
  · exact hA.1 h1
  · exact hA.2 ((conjNormal_mem_range_iff h.cent t).2 (mem_of_card_fixed_eq ζ h1)) h1

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
