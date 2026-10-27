module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GSetup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5g8_exists_sylow_bar {X : Type} [Group X] [Finite X] {Tb : Subgroup X}
    (hSyl : ∃ Pm : Sylow 2 ↥(normalClosure (Tb : Set X)),
      (Pm : Subgroup ↥(normalClosure (Tb : Set X))) =
        Tb.subgroupOf (normalClosure (Tb : Set X))) :
    ∃ Pb : Sylow 2 (Sec5GBar Tb), (Pb : Subgroup (Sec5GBar Tb)) = Sec5GImg Tb := by
  obtain ⟨Pm, hPm⟩ := hSyl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Pb : Sylow 2 (Sec5GBar Tb) :=
    Pm.mapSurjective (f := sec5g_pi Tb) (QuotientGroup.mk'_surjective _)
  have hPb : (Pb : Subgroup (Sec5GBar Tb)) =
      (Pm : Subgroup ↥(normalClosure (Tb : Set X))).map (sec5g_pi Tb) :=
    Sylow.coe_mapSurjective _ _
  refine ⟨Pb, ?_⟩
  rw [hPb, hPm]
  rfl

theorem sec5g8_nonempty_equiv_img {X : Type} [Group X] [Finite X] {Tb : Subgroup X}
    (hTb : IsPGroup 2 ↥Tb) : Nonempty (↥Tb ≃* ↥(Sec5GImg Tb)) := by
  let K : Subgroup ↥(normalClosure (Tb : Set X)) :=
    Tb.subgroupOf (normalClosure (Tb : Set X))
  have hle : Tb ≤ normalClosure (Tb : Set X) := Subgroup.le_normalClosure (H := Tb)
  have hK2 : IsPGroup 2 ↥K := hTb.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  let φ : ↥K →* ↥(Sec5GImg Tb) :=
    ((sec5g_pi Tb).comp K.subtype).codRestrict (Sec5GImg Tb) fun x => by
      rw [Sec5GImg]
      exact Subgroup.mem_map_of_mem _ x.2
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact sec5g_inj_of_pgroup Tb hK2 x.2 y.2 (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.1 (show z.1 ∈ K.map (sec5g_pi Tb) from z.2)
    exact ⟨⟨k, hk⟩, Subtype.ext hkz⟩
  exact ⟨(Subgroup.subgroupOfEquivOfLe hle).symm.trans (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩)⟩

theorem sec5g8_dihedral_bar {X : Type} [Group X] [Finite X] {Tb : Subgroup X}
    (hD : Nonempty (↥Tb ≃* DihedralGroup 4)) :
    Nonempty (↥(Sec5GImg Tb) ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := hD
  have hTb : IsPGroup 2 ↥Tb :=
    (IsPGroup.of_card (n := 3) (by rw [DihedralGroup.nat_card]; norm_num)).of_equiv e.symm
  exact ⟨(sec5g8_nonempty_equiv_img hTb).some.symm.trans e⟩

end CFSG.OddStandard.SmallF3.Omega
