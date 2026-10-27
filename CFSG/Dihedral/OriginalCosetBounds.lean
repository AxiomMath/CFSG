module

public import CFSG.Dihedral.OriginalCosetInvolutions

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem cosetBounds_of_aligned_aSeven_model (hp : d.PureProjectiveNormalizer)
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    d.CosetBounds := by
  intro w epsilon heps hmod i j hij hi
  have hq := d.coordinate_card_of_aligned_aSeven_model hp hR e ht w
  have hepsilon : epsilon = -1 := by
    rw [hq] at hmod
    rcases heps with h | h
    · rw [h] at hmod
      norm_num at hmod
    · exact h
  have hn := d.n_eq_three_of_aSeven_model e
  have hE := d.commonE_eq_bot_of_aSeven_model e
  have hindex := d.commonE_index_of_aSeven_model hR e
  have hcent := d.opposite_reflection_centralizer_card hp hR e ht i j hij hi
  have hfusion := d.involution_fusion_in_original_normalizer hp hR e ht i j hij hi
  have hdistinct := d.original_normalizer_involution_classes_distinct hp hR e i j hij hi
  have hfixed := d.original_normalizer_fixedCoset_card hR e ht
  have hNindex := d.N_index_of_aligned_aSeven_model hR e ht
  have hCindex := d.C_index_of_aSeven_model hR e
  dsimp only
  rw [hq, hepsilon, hindex, hn]
  norm_num only [Int.reduceNeg, Int.reduceAdd, Int.reduceToNat, Nat.reduceDiv,
    Nat.reduceSub, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  refine ⟨d.original_reflection_order j, d.original_opposite_reflection_fixed hp i j hij hi,
    ?_, by decide, by decide, by decide, by decide, by decide, ?_, ?_,
    hfusion, hdistinct, ?_, ?_, ?_⟩
  · simpa only [hE, Subgroup.card_bot, mul_one] using hcent
  · intro p hpprime hpdvd
    have hpone : p = 1 := Nat.dvd_one.mp hpdvd
    exact False.elim (hpprime.ne_one hpone)
  · intro h
    exact False.elim h
  · exact hfixed
  · omega
  · omega

end CFSG.DihedralBlueprint.OriginalData
