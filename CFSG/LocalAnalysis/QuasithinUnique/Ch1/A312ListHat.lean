module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open scoped commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique.Unc25K1.Six

theorem comm_mul_left_of_commute {G : Type*} [Group G] {a c y : G} (h : Commute c y) :
    ⁅a * c, y⁆ = ⁅a, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * c * y * (c⁻¹ * a⁻¹) * y⁻¹ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [h.eq, mul_inv_cancel_right]

theorem comm_mul_right_of_commute {G : Type*} [Group G] {x b d : G} (h : Commute d x) :
    ⁅x, b * d⁆ = ⁅x, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (b * d) * x⁻¹ * (d⁻¹ * b⁻¹) = x * b * (d * x⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = x * b * x⁻¹ * b⁻¹ := by rw [h.inv_right.eq, mul_inv_cancel_right]

theorem eq_top_of_sup_center_eq_top' {G : Type*} [Group G] (hG : commutator G = ⊤)
    {M : Subgroup G} (h : M ⊔ Subgroup.center G = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← hG, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨m', hm', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  rw [comm_mul_left_of_commute (Subgroup.mem_center_iff.mp hz _).symm,
    comm_mul_right_of_commute (Subgroup.mem_center_iff.mp hz' _).symm,
    commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

theorem isSolvable_of_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (M : Subgroup X) (h : Group.IsSolvable ↥(M.map e.toMonoidHom)) : Group.IsSolvable ↥M :=
  Group.isSolvable_of_isSolvable_injective
    (f := (M.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.injective _)

theorem solvable_overgroups_of_isSylowTwoOf {Y : Type} [Group Y] [Finite Y] {T₀ : Subgroup Y}
    (hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf T₀ ⊤)
    (h : ∀ M : Subgroup Y, T₀ ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M) {T : Subgroup Y}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (M : Subgroup Y) (hTM : T ≤ M) (hne : M ≠ ⊤) :
    Group.IsSolvable ↥M := by
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hT hT₀
  let e : Y ≃* Y := MulAut.conj g
  refine isSolvable_of_map_mulEquiv e M (h _ ?_ ?_)
  · rw [← hg]
    exact Subgroup.map_mono hTM
  · intro htop
    apply hne
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this

theorem A312For.of_central_quotient {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple X) (π : X →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X)
    (h : ∀ T : Subgroup Y, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → ∀ M : Subgroup Y, T ≤ M →
      M ≠ ⊤ → Group.IsSolvable ↥M) : A312For X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hT := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine A312For.of_solvable_overgroups hq (P : Subgroup X) hT fun M hPM hMtop => ?_
  have hTY := A312.isSylowTwoOf_top_map π hπ hT
  have hMY : (P : Subgroup X).map π ≤ M.map π := Subgroup.map_mono hPM
  have hne : M.map π ≠ ⊤ := by
    intro htop
    apply hMtop
    have hsup : M ⊔ Subgroup.center X = ⊤ := by
      rw [eq_top_iff]
      calc (⊤ : Subgroup X) = (M.map π).comap π := by rw [htop, Subgroup.comap_top]
        _ = M ⊔ π.ker := Subgroup.comap_map_eq π M
        _ ≤ M ⊔ Subgroup.center X := sup_le_sup_left hker M
    exact eq_top_of_sup_center_eq_top' (Group.isPerfect_def.mp hq.1) hsup
  have hMsolv : Group.IsSolvable ↥(M.map π) := h _ hTY _ hMY hne
  have hkersolv : Group.IsSolvable ↥(π.subgroupMap M).ker := by
    have : IsMulCommutative ↥(π.subgroupMap M).ker := ⟨⟨fun a b => by
      have ha : (a.1 : X) ∈ π.ker := by
        have := a.2
        rw [MonoidHom.mem_ker] at this ⊢
        exact congrArg Subtype.val this
      exact Subtype.ext (Subtype.ext ((Subgroup.mem_center_iff.mp (hker ha)) b.1.1).symm)⟩⟩
    infer_instance
  exact Group.isSolvable_of_ker_le_range (π.subgroupMap M).ker.subtype (π.subgroupMap M)
    (by rw [Subgroup.range_subtype])

theorem hat6 : FamHat6 := by
  intro X _ _ hq h
  obtain ⟨-, -, ⟨e⟩⟩ := h
  let π : X →* ↥A6s := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  refine A312For.of_central_quotient hq π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ ?_
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff x).mp (e.injective (by rw [map_one]; exact hx))
  · intro T hT M hTM hne
    exact solvable_overgroups_of_isSylowTwoOf isSylowTwoOf_T6 isSolvable_of_overgroup_six hT M hTM
      hne

end CFSG.QuasithinUnique.Vol2Native.A312L
