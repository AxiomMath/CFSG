module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeM
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeP

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv CFSG.Sporadic.HeldB

theorem signalizerFivePumpHeldInput_holds :
    SignalizerFivePumpHeldInput := by
  intro X _ _ _ _ _ _ _ t J hpair θ c e₀ he₀ _ _ _ _ hs4 Jc hJcJ _ _ _ χ _ M _ _ hJcM hJcMpc _
    hfix _ _ _ _ _ _ _ _ hHe
  exfalso
  obtain ⟨ψ⟩ := hHe
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have htN : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.2 hfix
  rw [hfix, sup_idem] at hJcM hJcMpc
  have hJcY : Jc ≤ M ⊓ centralizer ({t} : Set X) :=
    le_inf hJcM ((hJcJ.trans inf_le_left).trans hpair.1.2.1)
  set D : Finset (Fin 9) := (coreImage θ he₀).supportᶜ with hDdef
  have hD5 : Nat.card D = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hDdef, Finset.card_compl, Fintype.card_fin,
      hs4]
  have : Nontrivial D := by
    rw [← Finite.one_lt_card_iff_nontrivial, hD5]
    norm_num
  have hA : IsSimpleGroup (alternatingGroup D) := alternatingGroup.isSimpleGroup (by rw [hD5])
  have hA60 : Nat.card (alternatingGroup D) = 60 := by
    rw [nat_card_alternatingGroup, hD5]
    rfl
  have hS := FiveFHe.hasOddA_fixedSubgroup_oddQuotAction htN ht2 hJcY hJcMpc χ
  have hs : TBLit.oddQuotAction M ⟨t, htN⟩ * TBLit.oddQuotAction M ⟨t, htN⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨t, htN⟩ : normalizer (M : Set X)) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
    rw [h1, map_one]
  exact FiveFHe.not_hasOddA_fixedSubgroup_held hA60 (ψ.trans heEquivP) _ hs hS

end CFSG.ComponentClassification.SolMax
