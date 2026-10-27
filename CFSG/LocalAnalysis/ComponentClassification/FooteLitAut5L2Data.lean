module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Center
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5A7Data
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Field

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5L2

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] [Finite Y] (e : Y ≃* PSL2 F)

theorem foote5AutData_l2 {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hL : Blueprint.LieModel Y .PSL 2 p f) : Foote5AutData Y (linL2 e) where
  inn_le := inn_le_linL2 e
  normal := linL2_normal e
  sq_mem := sq_mem_of_linL2 e
  commutator_mem := commutator_mem_l2 hp hp2 hf hL
  conj_involution := conj_involution_l2 e (isOddPrimePower_of hp hp2 hf hF)
  centralizer_sylow := centralizer_sylow_l2 e hp hp2 hf hF
  centralizer_sylow_lin := centralizer_sylow_lin_l2 e (isOddPrimePower_of hp hp2 hf hF)
  not_commute := fun α β hα hαI _ hβ hβ2 => not_commute_l2 e hp hp2 hF α β hα hαI hβ hβ2
  conj_centralizer := conj_centralizer_l2 e hp hp2 hf hF
  pgl_fixed := fun R α hα hαI hα2 _ =>
    pgl_fixed_l2 e (isOddPrimePower_of hp hp2 hf hF) R α hα hαI hα2
  field_inner := field_inner_l2 e hp hp2 hf hF
  center_le := center_le_l2 e hp hp2 hf hF hL
  two_generated := two_generated_l2 e hp hp2 hf hF

theorem exists_foote5AutData_of_l2
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hL : Blueprint.LieModel Y .PSL 2 p f) : ∃ Lin : Subgroup (MulAut Y), Foote5AutData Y Lin := by
  obtain ⟨hp, hf, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
  exact ⟨_, foote5AutData_l2 e hp hp2 hf hF hL⟩

end CFSG.ComponentClassification.FooteLit.Aut5L2

namespace CFSG.ComponentClassification.FooteLit

open CFSG.ComponentClassification.Foote5

theorem foote5AutStructure_holds :
    Foote5AutStructure := by
  intro 𝕊 _ _ h
  rcases h with he | ⟨p, f, -, hp2, -, -, hL⟩
  · obtain ⟨e⟩ := he
    exact Aut5A7.exists_foote5AutData_of_a7 e
  · exact Aut5L2.exists_foote5AutData_of_l2 hp2 hL

end CFSG.ComponentClassification.FooteLit
