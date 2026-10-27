module

public import CFSG.LargeExtraspecial.AS62Iso
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair5
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.LargeExtraspecial.AS62Model2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.CosetTable AS62.Sem

namespace AS62

theorem ΨB_bijective :
    Function.Bijective ΨB :=
  ΨB_surjective.bijective_of_nat_card_le (by rw [U42.card_B0]; exact relsB_card_le)

theorem Ψ1_bijective :
    Function.Bijective Ψ1 :=
  Ψ1_surjective.bijective_of_nat_card_le (by rw [U42.card_P1]; exact rels1_card_le)

theorem Ψ2_bijective :
    Function.Bijective Ψ2 :=
  Ψ2_surjective.bijective_of_nat_card_le (by rw [U42.card_P2]; exact rels2_card_le)

theorem comm_ofBijective {P P' K K' L L' : Type*} [Group P] [Group P'] [Group K] [Group K']
    [Group L] [Group L'] {Φ : P →* K} {Φ' : P' →* K'} {Ψ : P →* L} {Ψ' : P' →* L'}
    {ι : P →* P'} {i : K →* K'} {j : L →* L'} (hΦ : Function.Bijective Φ)
    (hΨ : Function.Bijective Ψ) (hΦ' : Function.Bijective Φ') (hΨ' : Function.Bijective Ψ')
    (hcΦ : i.comp Φ = Φ'.comp ι) (hcΨ : j.comp Ψ = Ψ'.comp ι) (b : K) :
    j (((MulEquiv.ofBijective Φ hΦ).symm.trans (MulEquiv.ofBijective Ψ hΨ)) b) =
      ((MulEquiv.ofBijective Φ' hΦ').symm.trans (MulEquiv.ofBijective Ψ' hΨ')) (i b) := by
  obtain ⟨w, rfl⟩ := hΦ.2 b
  have e1 : (MulEquiv.ofBijective Φ hΦ).symm (Φ w) = w :=
    (MulEquiv.ofBijective Φ hΦ).symm_apply_apply w
  have e2 : i (Φ w) = Φ' (ι w) := DFunLike.congr_fun hcΦ w
  have e3 : (MulEquiv.ofBijective Φ' hΦ').symm (Φ' (ι w)) = ι w :=
    (MulEquiv.ofBijective Φ' hΦ').symm_apply_apply (ι w)
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e1, e2, e3, MulEquiv.ofBijective_apply,
    MulEquiv.ofBijective_apply]
  exact DFunLike.congr_fun hcΨ w

variable {G : Type} [Group G] [Finite G]

namespace Gens

variable {S : Setting G} {H : Subgroup G} (g : Gens S H)

@[expose] noncomputable def iso
    (hc : ConfHyp S H) (h18 : Nat.card S.Mbar = 18) {y : G}
    (hy : g.IsY y) :
    (RankTwoAmalgam.ofSubgroups S.M H).Iso (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2) where
  φ1 := (MulEquiv.ofBijective _ (g.Φ1_bijective hc h18 hy)).symm.trans
    (MulEquiv.ofBijective _ Ψ1_bijective)
  φ12 := (MulEquiv.ofBijective _ (g.ΦB_bijective hc)).symm.trans
    (MulEquiv.ofBijective _ ΨB_bijective)
  φ2 := (MulEquiv.ofBijective _ (g.Φ2_bijective hc)).symm.trans
    (MulEquiv.ofBijective _ Ψ2_bijective)
  comm1 := comm_ofBijective (g.ΦB_bijective hc) ΨB_bijective (g.Φ1_bijective hc h18 hy)
    Ψ1_bijective (g.inclusion_comp_ΦB_left hc hy) ψ_comm1
  comm2 := comm_ofBijective (g.ΦB_bijective hc) ΨB_bijective (g.Φ2_bijective hc)
    Ψ2_bijective (g.inclusion_comp_ΦB_right hc) ψ_comm2

theorem isAmalgamOfGroup
    (hc : ConfHyp S H) (h18 : Nat.card S.Mbar = 18) {y : G}
    (hy : g.IsY y) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups S.M H) (IsLieOverTwo .PSU 4 1) :=
  ⟨U42.Y, inferInstance, U42.lieModel_Y, U42.T, U42.P1, U42.P2, U42.isYAmalgamPair,
    ⟨g.iso hc h18 hy⟩⟩

end Gens

end AS62

end CFSG.LargeExtraspecial
