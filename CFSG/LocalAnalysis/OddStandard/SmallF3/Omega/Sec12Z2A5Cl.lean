module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128ClInt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128U34Ord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128U34Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5ClQ

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec128_not_psu34 {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    (Z : Subgroup (MulAut ↥V)) : ¬ LieModel ↥Z .PSU 3 2 2 := by
  intro h
  have h13 : 13 ∣ Nat.card ↥Z := sec128_lieModelPSU34_dvd13 h
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 13 h13
  have hy13 : ((y : MulAut ↥V)) ^ 13 = 1 := by
    have h1 := pow_orderOf_eq_one y
    rw [hy] at h1
    simpa using congrArg Subtype.val h1
  have hy1 : y = 1 := Subtype.ext (sec128_no_order13 hV.2 (y : MulAut ↥V) hy13)
  rw [hy1, orderOf_one] at hy
  norm_num at hy

theorem sec128_closure_typeK {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : IsElemAb2 V 8) (Y Xt : Subgroup (MulAut ↥V)) (hXY : Xt ≤ Y)
    (hXt : Nonempty (↥Xt ≃* ↥(alternatingGroup (Fin 5))))
    (hcent : ∀ o ∈ oddCore ↥Y, ∀ x ∈ Xt.subgroupOf Y, x * o = o * x)
    (hD : Nat.card ↥(Subgroup.centralizer (Xt : Set (MulAut ↥V))) ∣ 6 ∧
      ∀ c ∈ Subgroup.centralizer (Xt : Set (MulAut ↥V)), c ^ 3 = 1 → c ≠ 1 →
        ∀ v : ↥V, c v = v → v = 1)
    (hQ : IsO4Plus4 (↥Y ⧸ oddCore ↥Y) ∨ BenderL34Socle (↥Y ⧸ oddCore ↥Y)) :
    ∃ Z : Subgroup (MulAut ↥V), Z ≤ Y ∧ Xt ≤ Z ∧ (Z.subgroupOf Y).Normal ∧
      (∀ z ∈ Z, ∀ o ∈ oddCore ↥Y, z * (o : MulAut ↥V) = (o : MulAut ↥V) * z) ∧
      Z ⊓ (oddCore ↥Y).map Y.subtype = ⊥ ∧
      (((Z.subgroupOf Y ⊔ oddCore ↥Y).index = 2 ∧
          Nonempty (↥Z ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))))) ∨
        LieModel ↥Z .PSL 2 2 4 ∨ LieModel ↥Z .PSL 3 2 2) := by
  classical
  obtain ⟨eX⟩ := hXt
  set Xy : Subgroup ↥Y := Xt.subgroupOf Y with hXy
  set Zy : Subgroup ↥Y := normalClosure (Xy : Set ↥Y) with hZy
  set O : Subgroup ↥Y := oddCore ↥Y with hO
  haveI hZn : Zy.Normal := Subgroup.normalClosure_normal
  let eXy : ↥Xy ≃* ↥(alternatingGroup (Fin 5)) := (Subgroup.subgroupOfEquivOfLe hXY).trans eX
  have hXperf : ⁅Xy, Xy⁆ = Xy :=
    sec128_comm_eq_of_perfect Xy (sec128_commutator_top_of_mulEquiv eXy sec128_A5_perfect)
  have hXne : Xy ≠ ⊥ := by
    intro hbot
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(alternatingGroup (Fin 5)))
    have hy := (Subgroup.eq_bot_iff_forall Xy).mp hbot _ (eXy.symm x).2
    have h1 : eXy.symm x = 1 := Subtype.ext hy
    exact hx (by simpa using congrArg eXy h1)
  have hXZ : Xy ≤ Zy := Subgroup.le_normalClosure
  have hZperf : ⁅Zy, Zy⁆ = Zy := sec128_normalClosure_perfect Xy hXperf
  have hinter : Zy ⊓ O = ⊥ := sec128_closure_inter V hV Y Xt hXY hXperf hcent hD
  have hle : Zy ≤ centralizer (O : Set ↥Y) := by
    refine Subgroup.normalClosure_le_normal fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro o ho
    exact (hcent o ho x hx).symm
  have hZc : ∀ z ∈ Zy, ∀ o ∈ O, z * o = o * z := fun z hz o ho =>
    ((Subgroup.mem_centralizer_iff.mp (hle hz)) o ho).symm
  have hZne : Zy ≠ ⊥ := fun h => hXne (le_bot_iff.mp (h ▸ hXZ))
  let π : ↥Y →* ↥Y ⧸ O := QuotientGroup.mk' O
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  let P : Subgroup (↥Y ⧸ O) := Zy.map π
  haveI hPn : P.Normal := hZn.map π (QuotientGroup.mk'_surjective O)
  have hPperf : ⁅P, P⁆ = P := by
    rw [← Subgroup.map_commutator, hZperf]
  have hP1 : P ≠ ⊥ := by
    intro h
    apply hZne
    have h1 : Zy ≤ π.ker := (Subgroup.map_eq_bot_iff Zy).mp h
    rw [hker] at h1
    exact le_bot_iff.mp (hinter ▸ le_inf le_rfl h1)
  have htype := sec128_normal_perfect_typeK hQ P hPperf hP1
  have hinj : Function.Injective (π.comp Zy.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine (Subgroup.eq_bot_iff_forall _).mpr fun u hu => ?_
    have hu' : (u : ↥Y) ∈ O := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hu)
    have h2 : (u : ↥Y) ∈ Zy ⊓ O := ⟨u.2, hu'⟩
    rw [hinter, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hrange : (π.comp Zy.subtype).range = P := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eP : ↥Zy ≃* ↥P := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let eZ : ↥Zy ≃* ↥(Zy.map Y.subtype) := Zy.equivMapOfInjective Y.subtype Y.subtype_injective
  let eZP : ↥(Zy.map Y.subtype) ≃* ↥P := eZ.symm.trans eP
  have hZsub : (Zy.map Y.subtype).subgroupOf Y = Zy :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective Zy
  refine ⟨Zy.map Y.subtype, Subgroup.map_subtype_le Zy, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hXY hx⟩, Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · rw [hZsub]
    exact hZn
  · rintro _ ⟨y, hy, rfl⟩ o ho
    exact congrArg Subtype.val (hZc y hy o ho)
  · rw [← Subgroup.map_inf_eq Zy O Y.subtype Y.subtype_injective, hinter, Subgroup.map_bot]
  · rcases htype with ⟨hidx, ⟨f⟩⟩ | h | h | h
    · refine Or.inl ⟨?_, ⟨eZP.trans f⟩⟩
      rw [hZsub]
      have h1 : Zy ⊔ O = P.comap π := by
        rw [Subgroup.comap_map_eq, hker]
      rw [h1, Subgroup.index_comap_of_surjective P (QuotientGroup.mk'_surjective O)]
      exact hidx
    · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eZP.symm h))
    · exact absurd (CFSG.Blueprint.LieModel.of_mulEquiv eZP.symm h)
        (sec128_not_psu34 hV (Zy.map Y.subtype))
    · exact Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv eZP.symm h))

end CFSG.OddStandard.SmallF3.Omega
