module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.A5Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp
public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.A5Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem Y_le_sup_of_alt5_comp {G : Type} [Group G] [Finite G] {x t : G} {J J₁ : Subgroup G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (ht2 : t * t = 1) (hxt : x * t = t * x)
    (hJc : IsCompIn J (centralizer ({x} : Set G))) (hJ₁c : IsCompIn J₁ (centralizer ({x} : Set G)))
    (hne : J₁ ≠ J) (hJ₁A : Nonempty (J₁ ≃* alternatingGroup (Fin 5)))
    (htJ₁ : J₁.map (MulAut.conj t).toMonoidHom = J₁)
    (hY : Nat.card ↥(centralizer (J : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) = 8) :
    centralizer (J : Set G) ⊓ (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) ≤
      zpowers x ⊔ J₁ := by
  have htJ₁mem : ∀ h ∈ J₁, t * h * t⁻¹ ∈ J₁ := by
    intro h hh
    have h' : (MulAut.conj t).toMonoidHom h ∈ J₁.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hh
    rwa [htJ₁] at h'
  have hFcard := card_inf_centralizer_of_alt5 hJ₁A.some htJ₁mem ht2
  have hF_le_Y : J₁ ⊓ centralizer ({t} : Set G) ≤
      centralizer (J : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) := by
    intro a ha
    rw [Subgroup.mem_inf] at ha
    obtain ⟨haJ₁, hat⟩ := ha
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (IsCompIn.commute_of_ne hJ₁c hJc hne a haJ₁ b hb).symm,
      Subgroup.mem_inf.mpr ⟨hJ₁c.le haJ₁, hat⟩⟩
  have hF4 : Nat.card ↥(J₁ ⊓ centralizer ({t} : Set G)) = 4 := by
    have hdvd := Subgroup.card_dvd_of_le hF_le_Y
    rw [hY] at hdvd
    rcases hFcard with h | h | h
    · exact h
    · rw [h] at hdvd; norm_num at hdvd
    · rw [h] at hdvd; norm_num at hdvd
  have hxY : x ∈ centralizer (J : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun b hb => ?_,
      Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hJc.le hb)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxt
  have hx_not_J₁ : x ∉ J₁ := by
    intro hxJ₁
    refine hx1 (alt5_subgroup_center hJ₁A.some hxJ₁ fun h' hh' => ?_)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hJ₁c.le hh')).symm
  let F : Subgroup G := J₁ ⊓ centralizer ({t} : Set G)
  have hxF : ∀ p ∈ F, x * p * x⁻¹ ∈ F := by
    intro p hp
    change p ∈ J₁ ⊓ centralizer ({t} : Set G) at hp
    rw [Subgroup.mem_inf] at hp
    obtain ⟨hpJ₁, hpt⟩ := hp
    have hxp : p ∈ centralizer ({x} : Set G) := hJ₁c.le hpJ₁
    rw [Subgroup.mem_centralizer_singleton_iff] at hxp
    have hxp' : x * p * x⁻¹ = p := by rw [← hxp, mul_assoc, mul_inv_cancel, mul_one]
    rw [Subgroup.mem_inf, hxp']
    exact ⟨hpJ₁, hpt⟩
  have hcardFX : Nat.card ↥(F ⊔ zpowers x) = 2 * Nat.card F := by
    refine CFSG.Sporadic.SmallOddCore.card_sup_zpowers ?_ hxF ?_
    · rw [pow_two]; exact hx2
    · intro hxF'
      change x ∈ J₁ ⊓ centralizer ({t} : Set G) at hxF'
      exact hx_not_J₁ (Subgroup.mem_inf.mp hxF').1
  have hcardFX8 : Nat.card ↥(F ⊔ zpowers x) = 8 := by
    rw [hcardFX]
    change 2 * Nat.card ↥(J₁ ⊓ centralizer ({t} : Set G)) = 8
    rw [hF4]
  have hFX_le_Y : F ⊔ zpowers x ≤ centralizer (J : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) := by
    refine sup_le ?_ ?_
    · change J₁ ⊓ centralizer ({t} : Set G) ≤ _
      exact hF_le_Y
    · exact Subgroup.zpowers_le.mpr hxY
  have hYeq : F ⊔ zpowers x = centralizer (J : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) := by
    refine Subgroup.eq_of_le_of_card_ge hFX_le_Y (le_of_eq ?_)
    rw [hY, hcardFX8]
  rw [← hYeq]
  refine sup_le (fun a ha => Subgroup.mem_sup_right ?_) le_sup_left
  exact (Subgroup.mem_inf.mp (show a ∈ J₁ ⊓ centralizer ({t} : Set G) from ha)).1

end CFSG.EvenSporadicStandard.M12Std.PropA
