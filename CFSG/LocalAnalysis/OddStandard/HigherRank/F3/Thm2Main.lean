module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm2Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Two

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

theorem theorem2ClassB_of (hT1 : Harris82Theorem1KProper) (hID : IdentGenInput) :
    Theorem2ClassB := by
  intro G _ _ _ hnonab hK hcat W hW2 hW4 z₁ hz₁W z₂ hz₂W hz₁1 hz₂1 hne L₁ L₂ hL₁ hL₂ hz₁L hz₂L
    hM hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₁2 : orderOf z₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 z₁ hz₁W) hz₁1
  have hz₂n : z₂ ∉ zpowers z₁ := fun h =>
    (T23.eq_one_or_eq_of_mem_zpowers (hW2 z₁ hz₁W) h).elim hz₂1 hne.symm
  obtain ⟨-, hz₂2, hz₂M, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 hz₁W hz₁1 hz₂W hz₂n
  have hL₁' : IsTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) := hCW ▸ hL₁
  have hL₂' : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) := hCW ▸ hL₂
  set M := centralizer ({z₁} : Set G) with hMdef
  set z₂' : ↥M := ⟨z₂, hz₂M⟩
  have hz₂'2 : orderOf z₂' = 2 := by rw [Subgroup.orderOf_mk]; exact hz₂2
  obtain ⟨K₀, hK₀, hKeq, -⟩ := T23.exists_pumpup hz₂2 hz₂M hL₁'
  have hfix : K₀.map (MulAut.conj z₂').toMonoidHom = K₀ :=
    T23.map_conj_eq_of_mem_twoComponent hz₂'2 (T23.isTwoComponentIn_subgroupOf hz₂M hL₂') hz₂L
      hK₀
  have hKK₀ : ComponentClassification.GSThmB.conjClosure L₁
      (ComponentClassification.GSThmB.layerIn M) = K₀.map M.subtype := by
    rw [hKeq, hfix, sup_idem]
  have hKc : IsTwoComponentIn (K₀.map M.subtype) M := T23.isTwoComponentIn_map_subtype hK₀
  have hL₁K : L₁ ≤ K₀.map M.subtype :=
    hKK₀ ▸ ComponentClassification.GSThmB.B5a.le_conjClosure L₁ _
  have hz₁K : z₁ ∈ K₀.map M.subtype := hL₁K hz₁L
  have hKM : ¬ IsMTypeSchur 3 ↥(K₀.map M.subtype) :=
    not_isMTypeSchur_of_kProper hT1 hnonab hK hcat hz₁2 hKc hz₁K Nat.prime_three (by norm_num)
  have hKv : (K₀.map M.subtype).map (MulAut.conj z₂).toMonoidHom = K₀.map M.subtype := by
    have h := T23.map_subtype_map_conj K₀ z₂'
    rw [hfix] at h
    exact h.symm
  exact hID G hnonab hK hcat z₁ z₂ hz₁2 (hW2 z₂ hz₂W) hz₂n hz₂M L₁ hL₁' hM hS hz₁L
    (K₀.map M.subtype) hKK₀.symm hL₁K hKc hz₁K hKM hKv

end CFSG.OddStandard.HigherRank.F3
