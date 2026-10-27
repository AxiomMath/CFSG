module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSmallGeneric
public import CFSG.HardMathSupport.Curtis.Proving.FixThreeSmallFour

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.HardMathSupport.Curtis.Proving
open scoped commutatorElement

section Solvable

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb : Subgroup Y}

theorem isSolvable_of_overgroupOrder96 (hperf : commutator ↥Lb = ⊤) (hpar : IsParabolicTwo Lb Pb)
    (hne : Pb ≠ Lb) (hord : OvergroupOrder96 (↥Lb ⧸ Subgroup.center ↥Lb)) :
    Group.IsSolvable ↥Pb := by
  obtain ⟨hPL, T, hT, hTN⟩ := hpar
  have hTP : T ≤ Pb := fun x hx => hTN ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
  set π : ↥Lb →* ↥Lb ⧸ Subgroup.center ↥Lb := QuotientGroup.mk' (Subgroup.center ↥Lb) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Jb : Subgroup ↥Lb := Pb.subgroupOf Lb with hJb
  have hJbne : Jb.map π ≠ ⊤ := by
    intro htop
    apply hne
    have hHtop : Jb = ⊤ := by
      refine top_of_mul_central_of_perfect (Subgroup.center ↥Lb) Jb le_rfl hperf ?_
      intro g
      have hg : π g ∈ Jb.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨h', hh', he⟩ := Subgroup.mem_map.1 hg
      exact ⟨h', hh', h'⁻¹ * g, QuotientGroup.eq.1 he, (mul_inv_cancel_left h' g).symm⟩
    rw [hJb, Subgroup.subgroupOf_eq_top] at hHtop
    exact le_antisymm hPL hHtop
  have hT₀ : IsSylowTwoOf ((T.subgroupOf Lb).map π) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT) π hπs
  have hT₀J : (T.subgroupOf Lb).map π ≤ Jb.map π :=
    Subgroup.map_mono (fun x hx => hTP hx)
  have hcard : Nat.card (Jb.map π) ∣ 96 := hord _ _ hT₀ hT₀J hJbne
  set φ : ↥Pb →* ↥Lb ⧸ Subgroup.center ↥Lb := π.comp (Subgroup.inclusion hPL) with hφ
  have hrange : φ.range = Jb.map π := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hsolR : Group.IsSolvable ↥φ.range := by
    rw [hrange]
    exact isSolvable_of_card_dvd_ninetySix hcard
  have hsolK : Group.IsSolvable ↥φ.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have hc : ∀ p : ↥Pb, p ∈ φ.ker → (⟨p.1, hPL p.2⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      intro p hp
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hp)
    have := Subgroup.mem_center_iff.mp (hc a.1 a.2) ⟨b.1.1, hPL b.1.2⟩
    exact Subtype.ext (Subtype.ext (by
      have h2 := congrArg (fun z : ↥Lb => (z : Y)) this
      simpa using h2.symm))
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by
      intro g hg
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker]
      have : φ.rangeRestrict g = 1 := hg
      have h2 := congrArg Subtype.val this
      simpa using h2)

end Solvable

section Void

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem blockIb_false_smallFour
    (hP : BlockIbParab Lb Pb) (hX : IsSmallFourTwo (↥Lb ⧸ Subgroup.center ↥Lb))
    (hD : BlockIbData Lb Pb D x) : False :=
  blockIb_false_of_isSolvable hP hD
    (isSolvable_of_overgroupOrder96 hP.comp.2.2.1 hP.parab hP.ne (ordBound_isSmallFourTwo hX))

end Void

end CFSG.HardMathSupport.Curtis.UnitaryLevi
