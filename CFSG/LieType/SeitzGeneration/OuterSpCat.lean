module

public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.LieType.SeitzGeneration.InnerSymplectic

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP

theorem planeGen_outer_sp_model (hpair : SubfieldPairSpOdd) {d : TauCeti.ValidLieTypeIndex}
    {r ℓ f p : ℕ} {K : Type} [Field K] (e : Cat d ≃* StatedProj (StatedSp r K))
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) {E : Subgroup (MulAut (Cat d))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hout : ¬ InnerPlane d p E) :
    PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hrq' : ¬ (r = 2 ∧ Nat.card K = 2) := fun h => hrq ⟨h.1, by rw [← hK]; exact h.2⟩
  have : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    isSimpleGroup_statedProj_statedSp_of_two_le hr hrq'
  have hnab : ∃ a b : StatedProj (StatedSp r K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hnt : Nontrivial (StatedProj (StatedSp r K)) :=
      (CFSG.LieType.Classical.symplectic_projective_nontrivial K r (by omega)).1
    obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSp r K))
    have hxc : x ∈ Subgroup.center (StatedProj (StatedSp r K)) :=
      Subgroup.mem_center_iff.mpr fun g => h g x
    rw [center_statedProj_statedSp_eq_bot hr, Subgroup.mem_bot] at hxc
    exact hx hxc
  have hd : FieldAutData (StatedProj (StatedSp r K)) p :=
    fieldAutData_projectiveSp_odd hpair hr hℓ hf hK hp hp2
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have hclos := closure_fixUnion_eq_top_of_fieldAutData hnab hp hd
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  exact planeGen_of_outer_model e ((planeGen_iff_closure_fixUnion _).mpr hclos)

theorem seitzOuter_symplectic (hpair : SubfieldPairSpOdd) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsSymplecticIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hsp⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hsp with ⟨q, rfl⟩ | ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  ·
    exact planeGen_outer_sp_model hpair (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      q.prime_p q.exponent_pos (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hp hp2 le_rfl
      (fun h => hrange.2 ⟨h.1, by simpa [TauCeti.PrimePower.card_def] using h.2⟩) hE hc hout
  ·
    exact planeGen_outer_sp_model hpair
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      q.prime_p q.exponent_pos (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hp hp2
      (by omega) (fun h => by omega) hE hc hout
  ·
    have hr3 : 3 ≤ r := hrange.1
    exact planeGen_outer_sp_model hpair (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
      q.prime_p q.exponent_pos (card_fixedField_C r q hv) hp hp2 (by omega)
      (fun h => by omega) hE hc hout

end CFSG.LieType.SeitzGeneration
