module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaE8Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaArith
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem e8Case_of_witness
    (hW : E8Witness) : E8Case := by
  intro K _ _ ℓ f hmodel hℓ S hS
  have hm : ChevalleyExceptionalModel K .E8 ℓ f :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have hcard : Nat.card K = ordE8 (ℓ ^ f) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hm
  obtain ⟨⟨hℓp, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := hm
  let e' : K ≃* adjointGroup Tag.E8 F := e.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.E8) (K := F))).trans
      QuotientGroup.quotientBot)
  have hv : (Nat.card K).factorization 5 = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h1 := Sylow.card_eq_multiplicity S
    rw [hS] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1).symm
  have h5q : ¬ 5 ∣ ℓ ^ f := fun h =>
    hℓ ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hℓp).1 (Nat.prime_five.dvd_of_dvd_pow h)).symm
  have hord : orderOf (((ℓ ^ f : ℕ) : ℕ) : ZMod 5) = 4 :=
    orderOf_eq_four_of_factorization_ordE8 h5q (by rw [← hcard]; exact hv)
  have hordF : orderOf ((Nat.card F : ℕ) : ZMod 5) = 4 := by rw [hF]; exact hord
  obtain ⟨E, g, hE, hg, hnorm, x, hxE, hx⟩ := hW F hordF
  have hE' : IsElemAbelian 5 (E.map e'.symm.toMonoidHom) := hE.map _
  refine not_isMulCommutative_omega5 (E := E.map e'.symm.toMonoidHom) (g := e'.symm g) hE'
    (by rw [← map_pow, hg, map_one]) ?_ ⟨e'.symm x, Subgroup.mem_map_of_mem _ hxE, ?_⟩ S
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, hnorm y hy, by simp⟩
  · intro h
    exact hx (e'.symm.injective (by simpa using h))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega
