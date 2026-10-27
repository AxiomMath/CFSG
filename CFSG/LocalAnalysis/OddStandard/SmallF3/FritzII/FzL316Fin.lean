module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316Z3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316G2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316F

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fzl_316_of_str {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) {P : Subgroup G} (hPd : P = ⁅Q, zpowers rho⁆)
    (hTN : T ≤ normalizer (W : Set G)) (hodd : ¬ 2 ∣ T.relIndex (normalizer (W : Set G)))
    (hns : ¬ FzSylow T) :
    ((∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → Nonempty (↥P ≃* FzZ4422)) ∧
      ((¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → Nonempty (↥P ≃* SylSL3_4)) := by
  have hnc : ¬ FzCanon T W := fun hc => hns (fzl_sylow_of_canon hTN h.pgroup_T hodd hc)
  have htP : t ∉ P := fun ht =>
    hnc (fzl_canon_of_phiQ h (fzl_phiQ_eq_W h (hPd ▸ ht)))
  have hPf := fzl_pfacts h hPd htP
  refine ⟨fun hcomm => ?_, fun hna => ?_⟩
  · rcases fzl_abelian_dichotomy hcomm hPf.card_P h.rho_ord hPf.nrm_P_rho hPf.rho_fpf h.ZE
      hPf.EP h.card_E h.card_Z h.E_exp h.E_sq h.E_invol h.Z_sq h.rho_nrm_E hPf.P_sq
      h.E_equiv with h1 | ⟨h2, h3, h4⟩
    · exact h1
    · exact absurd (fzl_canon_of_Z8 h hPf ⟨hcomm, h2, h3, h4⟩) hnc
  · push_neg at hna
    exact fzl_316_nonab h hPf hna

end CFSG.OddStandard.SmallF3.FritzII
