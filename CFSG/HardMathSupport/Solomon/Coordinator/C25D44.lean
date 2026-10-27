module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25Up
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeDEven
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open TauCeti CFSG.RankThree.PartTwo.Census.Spin

theorem c25d44_le_of_hasWitness {Q Y : Type} [Group Q] [Group Y] [Finite Y] {k : ℕ}
    (e : Y ≃* Q) (h : HasWitness Q 3 k) : k ≤ GLATwoLocalRank 3 Y := by
  obtain ⟨E, P, hEc, hEp, hEcard, hP, hP2, hEP⟩ := h
  let φ : Q →* Y := e.symm.toMonoidHom
  have hφ : Function.Injective φ := e.symm.injective
  have hT : P.map φ ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P hφ]
  have hE : IsElemAbelian 3 (E.map φ) := by
    refine ⟨?_, ?_⟩
    · have := hEc
      infer_instance
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hEp y hy, map_one]
  have hEN : E.map φ ≤ Subgroup.normalizer ((P.map φ : Subgroup Y) : Set Y) :=
    (Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map φ)
  have hk : Nat.card (E.map φ) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective hφ, hEcard]
  exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
    (by norm_num) hT (hP2.map φ) hE hEN hk

theorem input25_4Facts_borel_holds :
    ∀ (Y : Type) [Group Y] [Finite Y], IsCatalogLieIso Y IsD44Index →
      4 ≤ GLATwoLocalRank 3 Y := by
  rintro Y _ _ ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩
  cases idx <;> simp only [IsD44Index] at hd
  rename_i r q
  obtain ⟨rfl, hp, hexp⟩ := hd
  obtain ⟨hchar, hord, -, hrank⟩ := typeD_mk_data 4 q hv
  rw [hp, hexp] at hord
  rw [hp] at hchar
  have hq4 : 4 ≤ (⟨⟨.D 4 q, hv⟩, by simp⟩ : TypeDLieIndex).1.fieldOrder := by
    rw [hord]
    norm_num
  have hsd : 3 ∣ (⟨⟨.D 4 q, hv⟩, by simp⟩ : TypeDLieIndex).1.fieldOrder - 1 := by
    rw [hord]
    norm_num
  have hW := CarrierD.hasWitness_torus _ hchar hq4 Nat.prime_three hsd id id
    (CarrierD.det_full_ne_zero _ hrank Nat.prime_three (by norm_num))
  rw [Fintype.card_fin] at hW
  exact hrank.symm.trans_le (c25d44_le_of_hasWitness e hW)

end CFSG.HardMathSupport.Solomon.Coordinator
