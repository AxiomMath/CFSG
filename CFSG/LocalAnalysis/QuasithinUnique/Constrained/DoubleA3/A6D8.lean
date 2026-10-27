module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Final

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Equiv Equiv.Perm

@[expose] def d8Rot : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def d8Ref : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def d8Map : DihedralGroup 4 → alternatingGroup (Fin 6)
  | .r i => d8Rot ^ i.val
  | .sr i => d8Rot ^ (-i).val * d8Ref

theorem d8Map_mul : ∀ x y : DihedralGroup 4, d8Map (x * y) = d8Map x * d8Map y := by
  decide +kernel

theorem d8Map_one : d8Map 1 = 1 := by decide +kernel

theorem d8Map_inj : Function.Injective d8Map := by
  intro x y h
  revert x y
  decide +kernel

theorem d8Map_comm : ∀ d : DihedralGroup 4, d8Map d * alt6X0 = alt6X0 * d8Map d := by
  decide +kernel

@[expose] def d8Hom : DihedralGroup 4 →* alternatingGroup (Fin 6) where
  toFun := d8Map
  map_one' := d8Map_one
  map_mul' := d8Map_mul

theorem d8Hom_range : d8Hom.range = alt6D0 := by
  have hle : d8Hom.range ≤ alt6D0 := by
    rintro _ ⟨d, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (d8Map_comm d)
  have hcard : Nat.card d8Hom.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective d8Map_inj : DihedralGroup 4 ≃* d8Hom.range).toEquiv,
      DihedralGroup.nat_card]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_alt6D0, hcard])

theorem nonempty_dihedral_of_card_eight (D : Subgroup (alternatingGroup (Fin 6)))
    (hD : Nat.card D = 8) : Nonempty (↥D ≃* DihedralGroup 4) := by
  obtain ⟨g, hg⟩ := alt6_exists_conj_of_card_eight D hD
  let ρ : ↥D →* ↥alt6D0 :=
    { toFun := fun x => ⟨g⁻¹ * (x : alternatingGroup (Fin 6)) * g, (hg x).1 x.2⟩
      map_one' := by
        apply Subtype.ext
        show g⁻¹ * 1 * g = 1
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        show g⁻¹ * ((x : alternatingGroup (Fin 6)) * y) * g =
          (g⁻¹ * (x : alternatingGroup (Fin 6)) * g) * (g⁻¹ * (y : alternatingGroup (Fin 6)) * g)
        group }
  have hρinj : Function.Injective ρ := by
    intro x y h
    apply Subtype.ext
    have h1 : g⁻¹ * (x : alternatingGroup (Fin 6)) * g = g⁻¹ * (y : alternatingGroup (Fin 6)) * g :=
      congrArg Subtype.val h
    have h2 := mul_right_cancel h1
    exact mul_left_cancel h2
  have hbij : Function.Bijective ρ :=
    hρinj.bijective_of_nat_card_le (by rw [hD, card_alt6D0])
  let e₁ : ↥D ≃* ↥alt6D0 := MulEquiv.ofBijective ρ hbij
  let e₂ : DihedralGroup 4 ≃* ↥d8Hom.range := MonoidHom.ofInjective d8Map_inj
  let e₃ : ↥d8Hom.range ≃* ↥alt6D0 := MulEquiv.subgroupCongr d8Hom_range
  exact ⟨e₁.trans (e₂.trans e₃).symm⟩

end CFSG.QuasithinUnique.DoubleA3
