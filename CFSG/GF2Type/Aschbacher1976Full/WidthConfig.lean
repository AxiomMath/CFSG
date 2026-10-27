module

public import CFSG.GF2Type.Aschbacher1976Full.WidthBounds
public import CFSG.GF2Type.Aschbacher1976Full.WidthFused
public import CFSG.GF2Type.CenterFour.Assembly

public section

namespace CFSG.GF2Type.Aschbacher1976Full

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Width

variable {z : G} {w : ℕ} {Z A : Subgroup G}

theorem centerAt_eq_Z (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) :
    centerAt z = Z :=
  Subgroup.ext (fun x => mem_centerAt_iff hD hz hF2)

theorem mem_center_F_iff' (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (x : ↥(Fz z)) : x ∈ Subgroup.center ↥(Fz z) ↔ (x : G) ∈ Z := by
  have hmap : (Subgroup.center ↥(Fz z)).map (Fz z).subtype = Z := by
    rw [← centerAt_eq_Z hD hz hF2]
    have key : ∀ S : Subgroup G, S = Fz z → (Subgroup.center ↥S).map S.subtype =
        (Subgroup.center ↥(Fz z)).map (Fz z).subtype := fun S h => by subst h; rfl
    exact (key _ (coreAt_eq_Fz hF2)).symm
  constructor
  · intro hx
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy

theorem isCyclic_center_F' (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) :
    IsCyclic ↥(Subgroup.center ↥(Fz z)) := by
  have hmap : (Subgroup.center ↥(Fz z)).map (Fz z).subtype = Z := by
    rw [← centerAt_eq_Z hD hz hF2]
    have key : ∀ S : Subgroup G, S = Fz z → (Subgroup.center ↥S).map S.subtype =
        (Subgroup.center ↥(Fz z)).map (Fz z).subtype := fun S h => by subst h; rfl
    exact (key _ (coreAt_eq_Fz hF2)).symm
  have hcyc : IsCyclic ↥((Subgroup.center ↥(Fz z)).map (Fz z).subtype) := by
    rw [hmap]
    exact hD.cyc
  exact isCyclic_of_injective
    (Subgroup.equivMapOfInjective _ (Fz z).subtype (Fz z).subtype_injective).toMonoidHom
    (Subgroup.equivMapOfInjective _ (Fz z).subtype (Fz z).subtype_injective).injective

theorem card_center_F' (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) :
    Nat.card ↥(Subgroup.center ↥(Fz z)) = 4 := by
  have hmap : (Subgroup.center ↥(Fz z)).map (Fz z).subtype = Z := by
    rw [← centerAt_eq_Z hD hz hF2]
    have key : ∀ S : Subgroup G, S = Fz z → (Subgroup.center ↥S).map S.subtype =
        (Subgroup.center ↥(Fz z)).map (Fz z).subtype := fun S h => by subst h; rfl
    exact (key _ (coreAt_eq_Fz hF2)).symm
  rw [← Subgroup.card_map_of_injective (Fz z).subtype_injective, hmap, hD.card_Z]

theorem config_of_z4star [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hD : Z4Data z w Z A)
    (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) (hw : 3 ≤ w) : Config z w := by
  have hF : CData z (Fz z) :=
    { zF := hD.sup_eq ▸ Subgroup.mem_sup_left hD.mem_z
      zc := fun f hf => Z_comm_F hD hD.mem_z hf
      z2 := z_sq hz
      z1 := fun h => by simp [h] at hz
      comm := fun f hf g hg => comm_F hD hz hf hg
      sq := fun f hf => sq_F hD hz hf }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbounds := bounds_F (z := z) hF w (card_Fz hD hz) Z
    (fun x => mem_center_F_iff' hD hz hF2 x) (isCyclic_center_F' hD hz hF2)
    (card_center_F' hD hz hF2)
  refine
    { orderOf_eq := hz
      three_le := hw
      mem_center := (mem_centerAt_iff hD hz hF2).mpr hD.mem_z
      center_cyclic := by rw [centerAt_eq_Z hD hz hF2]; exact hD.cyc
      card_center := by rw [centerAt_eq_Z hD hz hF2, hD.card_Z]
      normalizer_center := normalizer_centerAt hD hz hF2
      selfCentralizing := selfCent_F hF2
      sq_eq := fun x hx => by
        rw [coreAt_eq_Fz hF2] at hx
        exact sq_F hD hz hx
      comm_eq := fun x hx y hy => by
        rw [coreAt_eq_Fz hF2] at hx hy
        exact comm_F hD hz hx hy
      card_core := by rw [coreAt_eq_Fz hF2]; exact card_Fz hD hz
      card_elem_le := fun U hU hUe => hbounds.1 U (by rw [← coreAt_eq_Fz hF2]; exact hU) hUe
      card_elem_le_of_disjoint := fun U hU hUe hUZ =>
        hbounds.2.1 U (by rw [← coreAt_eq_Fz hF2]; exact hU) hUe
          (by rw [← centerAt_eq_Z hD hz hF2]; exact hUZ)
      card_pairwise_le := fun s f hf hpair =>
        hbounds.2.2 s f (fun i => by have := hf i; rw [coreAt_eq_Fz hF2] at this; exact this) hpair
      center_le_iff := fun g => by
        rw [centerAt_eq_Z hD hz hF2, coreAt_eq_Fz hF2]
        constructor
        · intro h
          exact z1_mem_F hD hz hF2 (fun x hx => h (mem_conjugate_iff.mpr (by
            rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
            exact hx)))
        · intro hz1
          have hcomm : g⁻¹ * z * g ∈ centralizer (Z : Set G) :=
            mem_centralizer_iff.mpr (fun k hk => Z_comm_F hD hk hz1)
          intro y hy
          have h1 := conjugate_le_H_of_comm hD hz hcomm (g * y * g⁻¹)
            (mem_conjugate_iff.mp hy)
          rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
          exact h1
      mem_core_of_centralizes := fun g hg => by
        rw [centerAt_eq_Z hD hz hF2] at hg
        rw [coreAt_eq_Fz hF2]
        exact z1_mem_F hD hz hF2 (conjugate_le_H_of_comm hD hz hg)
      exists_fused := exists_fused hnab hD hz hF2 (by omega) }

theorem leafWidthGeThree_holds : Asc76LeafWidthGeThree := by
  intro G _ _ z hS w hw hZ
  obtain ⟨Z, A, hD⟩ := exists_Z4Data hZ
  haveI := hS.1
  exact (config_of_z4star hS.2.1 hD hS.2.2.1 hS.2.2.2.1 hw).false

end Width

end CFSG.GF2Type.Aschbacher1976Full
