module

public import CFSG.LargeExtraspecial.S8CBFList
public import CFSG.LargeExtraspecial.S8CBFSmall
public import CFSG.LargeExtraspecial.S8CBFA5
public import CFSG.LargeExtraspecial.S8CBFG2
public import CFSG.LargeExtraspecial.S8CBFJ2
public import CFSG.LargeExtraspecial.S8CBFA5G2
public import CFSG.GH74.Orders.Sporadic
public import CFSG.LargeExtraspecial.S8CBFOut
public import CFSG.LargeExtraspecial.S8CorBA5Statement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint

@[expose] def CorBSectResidual : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], (∃ f, LieModel Y .trialityD4 0 2 f) →
    InvCentSectAbelianSylow Y

@[expose] def CorBA5Residual : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X), orderOf t = 2 →
    IsPGroup 2 (closure (conjCent t)) →
    ⁅⁅closure (conjCent t), closure (conjCent t)⁆, closure (conjCent t)⁆ = ⊥ →
    (∀ τ : X, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ)) →
    (∃ f, LieModel (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))
        .trialityD4 0 2 f) →
    ∀ R N : Subgroup X, N ≤ R → R ≤ normalClosure ({t} : Set X) →
      R ≤ centralizer ({t} : Set X) →
      (∀ c : X, c * t = t * c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
      ⁅R, R⁆ = R → ∀ (_ : (N.subgroupOf R).Normal), t ∈ N →
      IsSimpleGroup (↥R ⧸ N.subgroupOf R) → Nat.card (↥R ⧸ N.subgroupOf R) = 60 →
      IsExtraspecialPGroup 2 N → Nat.card N < 2 ^ 9

theorem invCentSectAbelianSylow_of_corBList (hSect : CorBSectResidual) {Y : Type} [Group Y]
    [Finite Y] (h : CorBList Y) : InvCentSectAbelianSylow Y := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact invCentSectAbelianSylow_of_isSolvable fun s hs =>
      isSolvable_centralizer_of_corBSolvFamily (Or.inl h) hs
  · exact invCentSectAbelianSylow_of_isSolvable fun s hs =>
      isSolvable_centralizer_of_corBSolvFamily (Or.inr (Or.inl h)) hs
  · exact invCentSectAbelianSylow_of_isSolvable fun s hs =>
      isSolvable_centralizer_of_corBSolvFamily (Or.inr (Or.inr (Or.inl h))) hs
  · exact invCentSectAbelianSylow_of_isSolvable fun s hs =>
      isSolvable_centralizer_of_corBSolvFamily (Or.inr (Or.inr (Or.inr (Or.inl h)))) hs
  · obtain ⟨f, h⟩ := h
    exact invCentSectAbelianSylow_of_lieModel_G2 h
  · exact invCentSectAbelianSylow_of_isSolvable fun s hs =>
      isSolvable_centralizer_of_corBSolvFamily (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hs
  · exact hSect Y h
  · exact invCentSectAbelianSylow_of_isSolvable fun s hs =>
      isSolvable_centralizer_of_corBSolvFamily (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) hs
  · exact invCentSectAbelianSylow_of_isSporadic_J2 h

theorem corBListFacts_of (hSect : CorBSectResidual) : CorBListFacts := by
  intro X _ _ U hU hL
  have := hU
  refine ⟨isSimpleGroup_of_corBList hL, fun hperf =>
    exists_derivedSeries_le_sup_centralizer U hperf (outer_solvable_of_corBList hL), ?_⟩
  exact sect_of_invCentSectAbelianSylow U (invCentSectAbelianSylow_of_corBList hSect hL)

theorem corBListA5Facts_of (hA5 : CorBA5Residual) : CorBListA5Facts := by
  intro X _ _ t hto hW2 hW3 hfus hL R N hNR hRU hRt hRn hperf hNn htN hsimple h60 hN
  have hsolv : CorBSolvFamily (↥(normalClosure ({t} : Set X)) ⧸
      center ↥(normalClosure ({t} : Set X))) → Nat.card N < 2 ^ 9 := fun hF =>
    (false_of_section_sixty_of_isSolvable hto
      (fun s hs => isSolvable_centralizer_of_corBSolvFamily hF hs) hNR hRU hRt h60).elim
  rcases hL with h | h | h | h | h | h | h | h | h
  · exact hsolv (Or.inl h)
  · exact hsolv (Or.inr (Or.inl h))
  · exact hsolv (Or.inr (Or.inr (Or.inl h)))
  · exact hsolv (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · obtain ⟨a, b, hab⟩ := exists_mul_ne_of_card_sixty h60
    have hnc := exists_mul_ne_of_section_nonabelian hRU ⟨a, b, hab⟩
    obtain ⟨f, hf⟩ := h
    have htU : t ∈ normalClosure ({t} : Set X) := subset_normalClosure (Set.mem_singleton t)
    exact card_lt_of_a5At htU hto hnc
      (a5At_of_lieModel_G2 hf (orderOf_mk_center_eq_two htU hto hnc)) hNR hRU hRt hperf htN hN
  · exact hsolv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact hA5 X t hto hW2 hW3 hfus h R N hNR hRU hRt hRn hperf hNn htN hsimple h60 hN
  · exact hsolv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · obtain ⟨a, b, hab⟩ := exists_mul_ne_of_card_sixty h60
    have hnc := exists_mul_ne_of_section_nonabelian hRU ⟨a, b, hab⟩
    refine card_lt_of_two_pow_nine_not_dvd hN
      (card_dvd_card_quotient_center_of_extraspecial (hNR.trans hRU) htN hto (hNR.trans hRt)
        hnc hN) ?_
    rw [GH74.card_of_isSporadic_J2 h]
    norm_num

end CFSG.LargeExtraspecial.S8
