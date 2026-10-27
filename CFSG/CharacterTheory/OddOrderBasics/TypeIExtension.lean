module

public import CFSG.CharacterTheory.OddOrderBasics.TypeIExtensionSupport
public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction

public section

open scoped BigOperators Classical

namespace CFSG.OddOrderBasics

open Wreathed

theorem coprime_abelian_action_character_extension {X : Type} [Group X] [Finite X]
    (H T : Subgroup X) [H.Normal] (hHT : H.IsComplement' T) (hT : IsMulCommutative T)
    (θ : H → ℂ) (hθ : θ ∈ BlocksIrr H) (hinv : ∀ t ∈ T, conjugateNormalCharacter H θ t = θ)
    {d : ℕ} (hd : θ 1 = d) (hcop : d.Coprime (Nat.card T)) :
    ∃ θ' ∈ BlocksIrr X, ∀ h : H, θ' h = θ h := by
  have : Fintype H := Fintype.ofFinite H
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hθ
  have hdV : Module.finrank ℂ V = d := by
    rw [Representation.char_one] at hd
    exact_mod_cast hd
  have hU : ∀ t : T, ∃ U : (Module.End ℂ V)ˣ, ∀ h : H,
      (U : Module.End ℂ V) * ρ h = ρ (MulAut.conjNormal (t : X) h) * U := by
    intro t
    refine exists_unit_intertwining_of_character_eq ρ
      (ρ.comp (MulAut.conjNormal (t : X)).toMonoidHom) hirr (funext fun h => ?_)
    change ρ.character (MulAut.conjNormal (t : X) h) = ρ.character h
    have h1 := congrFun (hinv (t : X)⁻¹ (T.inv_mem t.2)) h
    rw [conjugateNormalCharacter_apply] at h1
    rw [← h1]
    congr 1
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]
  choose U hU using hU
  have hcomm : ∀ s t : T, (U s : Module.End ℂ V) * U t = U t * U s := by
    intro s t
    have hsn : (s : X) ^ orderOf s = 1 := by
      rw [← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have hcop' : (Module.finrank ℂ V).Coprime (orderOf s) := by
      rw [hdV]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard s) hcop
    exact intertwiners_commute_of_coprime ρ hirr (congrArg Subtype.val (hT.is_comm.comm s t))
      hsn hcop' (U s) (U t) (hU s) (hU t)
  obtain ⟨W, hW⟩ := exists_hom_of_commuting_intertwiners ρ hirr T U hU hcomm
  obtain ⟨ρ', hρ'⟩ := exists_extension_of_compatible H T hHT ρ W hW
  have hcomp : ρ'.comp H.subtype = ρ := MonoidHom.ext hρ'
  have hirr' : ρ'.IsIrreducible := isIrreducible_of_comp_subtype ρ' H (by rw [hcomp]; exact hirr)
  refine ⟨ρ'.character, ⟨V, inferInstance, inferInstance, inferInstance, ρ', hirr', rfl⟩,
    fun h => ?_⟩
  change LinearMap.trace ℂ V (ρ' h) = LinearMap.trace ℂ V (ρ h)
  rw [hρ']

end CFSG.OddOrderBasics
