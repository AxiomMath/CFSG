module

public import CFSG.GroupTheory.PermSylowTwo.Sym

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Equiv Equiv.Perm CFSG.QuasithinUnique

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem isPGroup_two_of_pairing_alt [Subsingleton γ] (hβ : 3 ≤ Fintype.card β)
    {S H : Subgroup (Perm ((β × Bool) ⊕ γ))}
    (hS : IsSylowTwoOf S (alternatingGroup ((β × Bool) ⊕ γ)))
    (hsw : ∀ b b', pairSwap β γ b * pairSwap β γ b' ∈ S)
    {R : Subgroup (Perm β)} (hR : IsSylowTwoOf R ⊤)
    (hRS : R.map ((pairCent β γ).subtype.comp (pairLift β γ)) ≤ S) (hSH : S ≤ H)
    (hHA : H ≤ alternatingGroup ((β × Bool) ⊕ γ))
    (h3 : ¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (S : Set (Perm ((β × Bool) ⊕ γ)))) :
    IsPGroup 2 H := by
  have hHC : H ≤ pairCent β γ := by
    intro h hh
    rcases h3 with h3 | h3
    · exact mem_pairCent_of_doubleSwaps (Q := H) (h := h) hβ h3 (fun b b' => hSH (hsw b b'))
        (fun b b' => H.mul_mem (H.mul_mem hh (hSH (hsw b b'))) (H.inv_mem hh))
    · exact mem_pairCent_of_doubleSwaps (Q := S) (h := h) hβ
        (not_three_dvd_card_of_isPGroup_two hS.2.1) hsw
        (fun b b' => (Subgroup.mem_normalizer_iff.mp (h3 hh) _).mp (hsw b b'))
  have hS₁ : IsSylowTwoOf ((S.subgroupOf (pairCent β γ)).map (pairHom β γ)) ⊤ :=
    isSylowTwoOf_map_pairHom (P := S) hS.2.1 hR hRS
  have hH₁ : IsPGroup 2 ((H.subgroupOf (pairCent β γ)).map (pairHom β γ)) :=
    isPGroup_two_of_sylow_le β hS₁
      (Subgroup.map_mono (Subgroup.subgroupOf_mono (pairCent β γ) hSH))
      (map_pairHom_cond (P := S) hHC h3)
  exact isPGroup_two_of_le_pairCent hHC hH₁

end CFSG.GroupTheory.PermSylowTwo
