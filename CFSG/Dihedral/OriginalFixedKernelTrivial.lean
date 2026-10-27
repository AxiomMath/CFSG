module

import all CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.OriginalASevenPrimeNormalizer

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem fixedKernel_eq_bot_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (V : Subgroup G) (hV : IsFourGroup V) :
    d.R ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
  let A := d.R ⊓ Subgroup.centralizer (V : Set G)
  by_contra hA
  let : IsCyclic d.R := d.R_isCyclic_of_psl2_model K hK e
  have hAcyclic : IsCyclic A := Subgroup.isCyclic_of_le inf_le_left
  have hmapcyclic := (e.subgroupMap A).isCyclic.mp hAcyclic
  have hmapne : A.map e.toMonoidHom ≠ ⊥ := by
    intro h
    exact hA ((Subgroup.map_eq_bot_iff_of_injective A e.injective).mp h)
  have hmapodd : Odd (Nat.card (A.map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact d.R_odd.of_dvd_nat (Subgroup.card_dvd_of_le (show A ≤ d.R from inf_le_left))
  exact psl2_no_kleinFour_centralizes_odd_cyclic K hK
    (A.map e.toMonoidHom) (V.map e.toMonoidHom) hmapcyclic hmapne hmapodd
    (isKleinFour_map_mulEquiv_cross V (isKleinFour_of_isFourGroup V hV) e)
    (centralizer_map_le_of_mulEquiv e A V
      (Subgroup.le_centralizer_iff.mp (show A ≤ Subgroup.centralizer (V : Set G) from inf_le_right)))

theorem E_eq_bot_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K) (i : Fin 2) :
    d.E i = ⊥ :=
  d.fixedKernel_eq_bot_of_psl2_model K hK e (d.V i)
    (isFourGroup_of_isKleinFour _ (d.V_isKleinFour_general i))

theorem commonE_eq_bot_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K) :
    d.commonE = ⊥ := by
  apply le_antisymm _ bot_le
  calc
    d.commonE ≤ d.E 0 :=
      inf_le_inf_left d.R (Subgroup.centralizer_le (d.V_le_sylow 0))
    _ = ⊥ := d.E_eq_bot_of_psl2_model K hK e 0

theorem commonE_eq_bot [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : d.commonE = ⊥ := by
  rcases gorenstein_walter G hnonab d.S
      ⟨2 ^ (d.n - 1), d.sylow_mulEquiv_dihedral⟩ with hA | hL
  · exact d.commonE_eq_bot_of_aSeven_model hA.some
  · obtain ⟨r, k, hr, hrodd, hsize, ⟨e⟩⟩ := hL
    let _ : Fact r.Prime := hr
    have hk : k ≠ 0 := by
      intro h
      simp [h] at hsize
    have hK : IsOddPrimePower (Nat.card (GaloisField r k)) :=
      ⟨r, k, hr.out, hrodd, by omega, GaloisField.card r k hk⟩
    exact d.commonE_eq_bot_of_psl2_model (GaloisField r k) hK e

end CFSG.DihedralBlueprint.OriginalData
