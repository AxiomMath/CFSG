module

public import CFSG.CharacterTheory.Wreathed.OddIndexCentralCoreAction
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterScalars
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.Wreathed.NormalOddIndexFullCenterLayer
universe u v
variable {H : Type u} [Group H]

theorem quasisimple_le_normal_of_odd_index [Finite H]
    (M D : Subgroup H) [D.Normal] (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M))) (hodd : Odd D.index) : M ≤ D := by
  let : Group.IsPerfect M := hM.1
  let : IsSimpleGroup (M ⧸ Subgroup.center M) := hM.2.1
  let K := D.subgroupOf M
  let : K.Normal := inferInstance
  have hKodd : Odd K.index := by
    change Odd (D.comap M.subtype).index
    rw [Subgroup.index_comap, Subgroup.range_subtype]
    exact hodd.of_dvd_nat (Subgroup.relIndex_dvd_index_of_normal D M)
  let S : Sylow 2 M := Sylow.nonempty.some
  have hSK : (S : Subgroup M) ≤ K :=
    OddIndexCentralCoreAction.two_subgroup_le_normal_of_odd_index K S hKodd S.isPGroup'
  have hKtop : K = ⊤ :=
    PrimewisePerfectLift.normal_Sylow_overgroup_eq_top_of_even_simple_central_quotient
      heven K S hSK
  intro m hm
  exact (show (⟨m, hm⟩ : M) ∈ K from hKtop ▸ Subgroup.mem_top _)

theorem center_le_normal_of_odd_index (D : Subgroup H) [D.Normal]
    (htwo : IsPGroup 2 (Subgroup.center H)) (hodd : Odd D.index) : Subgroup.center H ≤ D :=
  OddIndexCentralCoreAction.two_subgroup_le_normal_of_odd_index D _ hodd htwo

theorem center_subgroupOf_eq (M D : Subgroup H)
    (hMD : M ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    (Subgroup.center H).subgroupOf D = Subgroup.center D := by
  ext d
  constructor
  · intro hd
    exact Subgroup.mem_center_iff.mpr (fun e =>
      Subtype.ext (Subgroup.mem_center_iff.mp hd e.val))
  · intro hd
    rw [← hcentralizer]
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hd) (⟨m, hMD hm⟩ : D))

theorem center_map_eq (M D : Subgroup H)
    (hMD : M ≤ D) (hAD : Subgroup.center H ≤ D)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    (Subgroup.center D).map D.subtype = Subgroup.center H := by
  rw [← center_subgroupOf_eq M D hMD hcentralizer,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAD]

@[expose] def quotientInclusion (D : Subgroup H) :
    D ⧸ (Subgroup.center H).subgroupOf D →* H ⧸ Subgroup.center H :=
  QuotientGroup.map _ _ D.subtype le_rfl

theorem quotientInclusion_mk (D : Subgroup H) (d : D) :
    quotientInclusion D (QuotientGroup.mk' ((Subgroup.center H).subgroupOf D) d) =
      QuotientGroup.mk' (Subgroup.center H) (d : H) := rfl

theorem quotientInclusion_injective (D : Subgroup H) :
    Function.Injective (quotientInclusion D) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective ((Subgroup.center H).subgroupOf D) x
  rw [MonoidHom.mem_ker, quotientInclusion_mk] at hx
  have hd : (d : H) ∈ Subgroup.center H := (QuotientGroup.eq_one_iff _).mp hx
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff d).mpr hd)

theorem quotientInclusion_range (D : Subgroup H) :
    (quotientInclusion D).range = D.map (QuotientGroup.mk' (Subgroup.center H)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective ((Subgroup.center H).subgroupOf D) a
    exact Subgroup.mem_map.mpr ⟨(d : H), d.property, quotientInclusion_mk D d⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨QuotientGroup.mk' ((Subgroup.center H).subgroupOf D) (⟨d, hd⟩ : D), rfl⟩

theorem quotientInclusion_normal (D : Subgroup H) [D.Normal] :
    (quotientInclusion D).range.Normal := by
  rw [quotientInclusion_range]
  infer_instance

theorem quotientInclusion_odd_index (D : Subgroup H) (hodd : Odd D.index) :
    Odd (quotientInclusion D).range.index := by
  rw [quotientInclusion_range]
  exact hodd.of_dvd_nat (Subgroup.index_map_dvd D (QuotientGroup.mk'_surjective _))

theorem subgroup_center_comap (M : Subgroup H)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    (Subgroup.center H).subgroupOf M = Subgroup.center M := by
  ext m
  constructor
  · intro hm
    exact Subgroup.mem_center_iff.mpr (fun n =>
      Subtype.ext (Subgroup.mem_center_iff.mp hm n.val))
  · intro hm
    rw [← hcentralizer]
    exact Subgroup.mem_centralizer_iff.mpr (fun n hn =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hm) (⟨n, hn⟩ : M)))

@[expose] def projectiveImageEquiv (M : Subgroup H)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    M ⧸ Subgroup.center M ≃* M.map (QuotientGroup.mk' (Subgroup.center H)) := by
  let q := QuotientGroup.mk' (Subgroup.center H)
  let f := (q.domRestrict M).codRestrict (M.map q)
    (fun m => Subgroup.mem_map_of_mem q m.property)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp x.property
    exact ⟨⟨m, hm⟩, Subtype.ext hmx⟩
  have hk : f.ker = Subgroup.center M := by
    ext m
    change f m = 1 ↔ m ∈ Subgroup.center M
    rw [← Subtype.coe_inj]
    change (((m : H) : H ⧸ Subgroup.center H) = 1) ↔ m ∈ Subgroup.center M
    rw [QuotientGroup.eq_one_iff, ← subgroup_center_comap M hcentralizer]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

theorem projectiveImageEquiv_mk (M : Subgroup H)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) (m : M) :
    (projectiveImageEquiv M hcentralizer (QuotientGroup.mk' (Subgroup.center M) m) :
      H ⧸ Subgroup.center H) = QuotientGroup.mk' (Subgroup.center H) (m : H) := rfl

theorem projectiveImage_centralizer (M : Subgroup H) [Group.IsPerfect M]
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    Subgroup.centralizer (M.map (QuotientGroup.mk' (Subgroup.center H)) :
      Set (H ⧸ Subgroup.center H)) = ⊥ := by
  have h := DegreeThreeModelFullCenter.centralizer_range_eq_bot_of_perfect_image
    M.subtype (QuotientGroup.mk' (Subgroup.center H)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (fun g hg => by
      rw [QuotientGroup.ker_mk', ← hcentralizer]
      exact Subgroup.mem_centralizer_iff.mpr (fun m hm => (hg (⟨m, hm⟩ : M)).eq.symm))
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h

end CFSG.Wreathed.NormalOddIndexFullCenterLayer
