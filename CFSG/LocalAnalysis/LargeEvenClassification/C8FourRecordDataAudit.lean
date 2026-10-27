module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupCertificate
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourCharacterCoordinates
public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianGeneratorRank

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem c8Four_record_rank_le_five
    (r : C8FourSubgroupRecord) (hr : c8FourRecordValid r) :
    pGeneratorRank 2 (c8FourRecordSubgroup r hr) ≤ 5 := by
  exact (c8FourRecord_generator_rank_le r hr).trans hr.2.2.2.2.2.2.2

@[expose] def c8FourRecordBinaryHom
    (r : C8FourSubgroupRecord) (hr : c8FourRecordValid r) :
    c8FourRecordSubgroup r hr →* Multiplicative (Fin 5 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (fun k => c8FourPairing (c8FourVector r g.val)
    (Fin.ofNat 32 (2 ^ k.val)))
  map_one' := by
    apply Multiplicative.ofAdd.symm.injective
    funext k
    change c8FourPairing (c8FourVector r 1) _ = 0
    rw [hr.2.2.2.2.2.1, c8FourPairing_zero]
  map_mul' g h := by
    apply Multiplicative.ofAdd.symm.injective
    funext k
    have hmult := hr.2.2.2.2.2.2.1
    have hg := (hr.1 g.val).mp g.property
    have hh := (hr.1 h.val).mp h.property
    have hv := (certificateListAll_iff _ _).mp
      ((certificateListAll_iff _ _).mp hmult g.val hg) h.val hh
    change c8FourVector r (g.val * h.val) = _ at hv
    change c8FourPairing (c8FourVector r (g.val * h.val)) _ =
      c8FourPairing (c8FourVector r g.val) _ + c8FourPairing (c8FourVector r h.val) _
    rw [hv, c8FourPairing_xor]

@[expose] def c8FourRecordBinaryImages (r : C8FourSubgroupRecord) : Finset (Fin 5 → ZMod 2) :=
  (r.elements.map (fun g => fun k : Fin 5 => c8FourPairing (c8FourVector r g)
    (Fin.ofNat 32 (2 ^ k.val)))).toFinset

theorem c8FourRecordBinaryHom_card_range
    (r : C8FourSubgroupRecord) (hr : c8FourRecordValid r) :
    Nat.card (c8FourRecordBinaryHom r hr).range = (c8FourRecordBinaryImages r).card := by
  classical
  let image := c8FourRecordBinaryImages r
  let e : (c8FourRecordBinaryHom r hr).range ≃ image := {
    toFun := fun g => ⟨g.val.toAdd, by
      obtain ⟨x, hx⟩ := g.property
      rw [← hx]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x.val, (hr.1 x.val).mp x.property, rfl⟩)⟩
    invFun := fun g => ⟨Multiplicative.ofAdd g.val, by
      obtain ⟨x, hx, hvalue⟩ := List.mem_map.mp (List.mem_toFinset.mp g.property)
      exact ⟨⟨x, (hr.1 x).mpr hx⟩, congrArg Multiplicative.ofAdd hvalue⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem c8FourRecord_rank_lower_bound
    (r : C8FourSubgroupRecord) (hr : c8FourRecordValid r) :
    Nat.log 2 (c8FourRecordBinaryImages r).card ≤ pGeneratorRank 2 (c8FourRecordSubgroup r hr) := by
  let f := c8FourRecordBinaryHom r hr
  let R := f.range
  let : CommGroup R := { (inferInstance : Group R) with
    mul_comm := fun x y => by apply Subtype.ext; exact mul_comm x.val y.val }
  have hR : ∀ x : R, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
    apply Multiplicative.ofAdd.symm.injective
    funext k
    change x.val.toAdd k + x.val.toAdd k = 0
    exact CharTwo.add_self_eq_zero _
  have hbound := pGeneratorRank_surjective_le Nat.prime_two
    (c8Four_code_isPGroup.to_subgroup (c8FourRecordSubgroup r hr)) f.rangeRestrict f.rangeRestrict_surjective
  change pGeneratorRank 2 R ≤ _ at hbound
  rw [elementary_pGeneratorRank_eq_log_card (Ambient := R) Nat.prime_two hR,
    c8FourRecordBinaryHom_card_range] at hbound
  exact hbound

end CFSG.LargeEvenClassification.Helpers
