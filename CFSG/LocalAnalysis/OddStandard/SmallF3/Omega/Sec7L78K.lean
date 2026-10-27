module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78F1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l78_exists_K [Finite G] (h36 : Asc82Lemma36) (h61 : Asc82Lemma61) (hP : Asc82Tab6P)
    (hOm5 : Sec8T84FactOm5Out) {t : G} {L S : Subgroup G} {z g : G} {B P' D : Subgroup G}
    (hc : Sec7Choice G t L S z g B) (hsL : Sec7L78Side L (S ⊓ L) B (ASub S B) t)
    (hsL' : Sec7L78Side (CFSG.conjugate L g) P' D (ASub S B) (g⁻¹ * t * g)) {r : G}
    (hrA : r ∈ ASub S B) (hr1 : r ≠ 1) (hrt : r ≠ t) (hrs : r ≠ g⁻¹ * t * g)
    (hrN₁ : ∀ n ∈ L ⊓ normalizer (B : Set G), r * n = n * r)
    (hrN₂ : ∀ n ∈ CFSG.conjugate L g ⊓ normalizer (D : Set G), r * n = n * r) :
    ∃ K : Subgroup G, twoRes (L ⊓ normalizer (B : Set G)) ≤ K ∧
      twoRes (CFSG.conjugate L g ⊓ normalizer (D : Set G)) ≤ K ∧
      ((K ≤ L ∧ K ≤ CFSG.conjugate L g) ∨ IsOm6P K) := by
  have hr2 : orderOf r = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsL.A_sq r hrA) hr1
  have hrCt : r ∈ centralizer ({t} : Set G) := sec7l78_A_le_cent_t hc hrA
  have hsA : g⁻¹ * t * g ∈ ASub S B := sec7l78_s_mem_A hP h36 hc
  have hrCs : r ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hsL.A_comm r hrA _ hsA)
  have hrNL : r ∈ normalizer (L : Set G) := hsL.A_N hrA
  have hrNL' : r ∈ normalizer (CFSG.conjugate L g : Set G) := hsL'.A_N hrA
  obtain ⟨α, hα⟩ := hsL.type hP hrA hrN₁ hr1 hrt
  obtain ⟨α', hα'⟩ := hsL'.type hP hrA hrN₂ hr1 hrs
  have hY₁5 : IsOmega5 (layerCent L r) := hP.layer_i1 G L hsL.om r hr2 hrNL ⟨α, hα⟩
  have hY₂5 : IsOmega5 (layerCent (CFSG.conjugate L g) r) :=
    hP.layer_i1 G (CFSG.conjugate L g) hsL'.om r hr2 hrNL' ⟨α', hα'⟩
  obtain ⟨I₁, hI₁, hY₁le, hI₁shape⟩ :=
    h61 G t L hc.ctx.toSec3SettingLB hc.ctx.omega6 r hr2 hrCt hY₁5
  obtain ⟨I₂, hI₂, hY₂le, hI₂shape⟩ :=
    h61 G (g⁻¹ * t * g) (CFSG.conjugate L g)
      (hc.ctx.toSec3SettingLB.conjugate g) (hc.ctx.conjugate g).omega6 r hr2 hrCs hY₂5
  have hI₁F : InF I₁ := by
    rcases hI₁shape with h | h
    · exact ⟨hI₁.isQuasisimple, Or.inl (Or.inl h)⟩
    · exact ⟨hI₁.isQuasisimple, Or.inl (Or.inr (Or.inl h))⟩
  have hI₂F : InF I₂ := by
    rcases hI₂shape with h | h
    · exact ⟨hI₂.isQuasisimple, Or.inl (Or.inl h)⟩
    · exact ⟨hI₂.isQuasisimple, Or.inl (Or.inr (Or.inl h))⟩
  obtain ⟨-, hI₁uniq⟩ := h36 G t L hc.ctx.toSec3SettingLB r I₁ hr2 hI₁ (Or.inl hI₁F)
  have hI₂eq : I₂ = I₁ := hI₁uniq I₂ hI₂ (inFStar_of_inF hI₂F)
  have hY₁L : layerCent L r ≤ L :=
    (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({r} : Set G)))).trans inf_le_left
  have hY₂L : layerCent (CFSG.conjugate L g) r ≤ CFSG.conjugate L g :=
    (Subgroup.map_subtype_le
      (CFSG.layer ↥(CFSG.conjugate L g ⊓ centralizer ({r} : Set G)))).trans inf_le_left
  refine ⟨I₁, ?_, ?_, ?_⟩
  · rw [twoRes]
    refine (Subgroup.closure_le (K := I₁)).mpr ?_
    rintro x ⟨hxN, hxodd⟩
    exact hY₁le (sec7l78_odd_in_layer hP hOm5 hsL.om hr2 hrNL ⟨α, hα⟩ hxN.1
      (hrN₁ x hxN).symm hxodd)
  · rw [twoRes]
    refine (Subgroup.closure_le (K := I₁)).mpr ?_
    rintro x ⟨hxN, hxodd⟩
    exact le_of_eq hI₂eq (hY₂le (sec7l78_odd_in_layer hP hOm5 hsL'.om hr2 hrNL' ⟨α', hα'⟩
      hxN.1 (hrN₂ x hxN).symm hxodd))
  · rcases hI₁shape with h5 | h6
    · left
      have hY₁comp : IsComponentIn (layerCent L r) (L ⊓ centralizer ({r} : Set G)) :=
        isComponentIn_layerCent (Or.inl hY₁5)
      have hY₂comp : IsComponentIn (layerCent (CFSG.conjugate L g) r)
          (CFSG.conjugate L g ⊓ centralizer ({r} : Set G)) :=
        isComponentIn_layerCent (Or.inl hY₂5)
      have hY₁eq : layerCent L r = I₁ :=
        eq_of_le_of_ctrQ_eq hI₁.isQuasisimple hY₁le
          (by rw [ctrQ_of_psp4 hY₁comp.isQuasisimple hY₁5,
            ctrQ_of_psp4 hI₁.isQuasisimple h5])
      have hY₂eq : layerCent (CFSG.conjugate L g) r = I₁ :=
        eq_of_le_of_ctrQ_eq hI₁.isQuasisimple (hY₂le.trans (le_of_eq hI₂eq))
          (by rw [ctrQ_of_psp4 hY₂comp.isQuasisimple hY₂5,
            ctrQ_of_psp4 hI₁.isQuasisimple h5])
      exact ⟨hY₁eq ▸ hY₁L, hY₂eq ▸ hY₂L⟩
    · right
      exact ⟨hI₁.isQuasisimple, h6⟩

end CFSG.OddStandard.SmallF3.Omega
