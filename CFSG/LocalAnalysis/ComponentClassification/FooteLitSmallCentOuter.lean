module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

theorem iSup_eqLocus_eq_top_of_not_le_range
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (hD : AschbacherKnownGroup.HasDihedralSylowTwo S) {V : Subgroup (MulAut S)}
    (hV : IsKleinFour V) (hVI : ¬ V ≤ (MulAut.conj : S →* MulAut S).range) :
    ⨆ (u : MulAut S) (_ : u ∈ V) (_ : u ≠ 1),
      MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id S) = ⊤ := by
  obtain ⟨-, hZ⟩ := open_isQuasisimple_of_isSimpleGroup hnc
  set c : S →* MulAut S := MulAut.conj with hc
  have hcinj : Function.Injective c := injective_mulAut_conj hZ
  set Inn := c.range with hInn
  let eInn : S ≃* Inn := MonoidHom.ofInjective hcinj
  have : IsSimpleGroup Inn := eInn.symm.isSimpleGroup
  have hInnc : ∃ a b : Inn, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eInn a, eInn b, fun h => hab (eInn.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨hqI, hZI⟩ := open_isQuasisimple_of_isSimpleGroup hInnc
  let eQ : Inn ⧸ center Inn ≃* S :=
    ((QuotientGroup.quotientMulEquivOfEq hZI).trans QuotientGroup.quotientBot).trans eInn.symm
  have hDI : AschbacherKnownGroup.HasDihedralSylowTwo (Inn ⧸ center Inn) :=
    hasDihedralSylowTwo_of_equiv eQ.symm hD
  have hfact : (Nat.card (center Inn)).factorization 2 ≤ 1 := by
    rw [hZI, card_bot]
    simp
  have hV4 : AschbacherKnownGroup.IsFourGroup V :=
    ⟨⟨@IsKleinFour.isMulCommutative V _ hV, fun x hx => sq_eq_one_of_isKleinFour hV hx⟩,
      hV.card_four⟩
  have hgen := hK.dihedral_cover_generation (MulAut S) Inn V hqI hDI hfact
    (le_normalizer_range_conj V) hV4
  have hle : Inn ≤ AschbacherKnownGroup.centralizerJoin V Inn := by
    by_contra hle
    have h1 := (hgen hle).2
    rw [centralizer_range_conj_eq_bot hZ, sup_bot_eq] at h1
    exact hVI h1
  have hjoin : AschbacherKnownGroup.centralizerJoin V Inn =
      (⨆ (u : MulAut S) (_ : u ∈ V) (_ : u ≠ 1),
        MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id S)).map c := by
    unfold AschbacherKnownGroup.centralizerJoin
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun u => iSup_congr fun _ => iSup_congr fun _ =>
      range_inf_centralizer_eq hZ u
  refine eq_top_iff.mpr fun s _ => ?_
  have h1 := hle ⟨s, rfl⟩
  rw [hjoin, mem_map_iff_mem hcinj] at h1
  exact h1

end CFSG.ComponentClassification.FooteLit
