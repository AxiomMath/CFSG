module

public import CFSG.GF2Type.Aschbacher1976Full.ShapeStructure
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSymplecticSmallCritical
public import CFSG.LargeExtraspecial.AS35CS63Inn
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
public import CFSG.LocalAnalysis.SteinbergBKSolvableQuaternionWitness
public import CFSG.GF2Type.Aschbacher1976Full.ShapeBasic

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.GorensteinLyons
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Hz_eq_Fz_of_mulAut {z : G} (hF2 : IsPGroup 2 ↥(Fz z))
    (hA : IsPGroup 2 (MulAut ↥(Fz z))) : Hz z = Fz z := by
  have hN : (generalizedFitting ↥(Hz z)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥(Hz z))).2
  let e : ↥(generalizedFitting ↥(Hz z)) ≃* ↥(Fz z) :=
    (generalizedFitting ↥(Hz z)).equivMapOfInjective (Hz z).subtype (Hz z).subtype_injective
  have hNp : IsPGroup 2 ↥(generalizedFitting ↥(Hz z)) := hF2.of_equiv e.symm
  have hAut : IsPGroup 2 (MulAut ↥(generalizedFitting ↥(Hz z))) :=
    hA.of_equiv (MulAut.congr e.symm)
  exact Hz_eq_Fz_of_isPGroup hF2
    (LocalAnalysis.SteinbergBK.isPGroup_of_centralizer_le_of_isPGroup_mulAut hNp
      (centralizer_generalizedFitting_le _) hAut)

theorem nonabelian_of_extraspecial {P : Type*} [Group P] (h : IsExtraspecialPGroup 2 P) :
    ∃ a b : P, a * b ≠ b * a := by
  by_contra hall
  push Not at hall
  have hcomm : commutator P ≤ ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hall a b
  have h1 : center P = ⊥ := by
    rw [← h.2.1]
    exact le_bot_iff.mp hcomm
  have h2 := h.2.2.2
  rw [h1, Subgroup.card_bot] at h2
  exact absurd h2 (by norm_num)

theorem isZ4Star_of_criticalCentralProduct {z : G} {D E R : Subgroup ↥(Fz z)} {zP : ↥(Fz z)}
    (hzP : (zP : G) = z) (cd : CritData D E R zP) {w : ℕ}
    (h : SymplecticSmallCritical.IsCriticalCentralProduct D zP w) : IsZ4Star z w := by
  obtain ⟨-, hZP, hZ4, -, E', hEx, hEcard, hEZ, hEZc, hEZi, -⟩ := h
  refine ⟨lift (Zof D), lift E', isCyclic_lift cd.cyc, ?_, ?_, isExtraspecialPGroup_lift hEx,
    (card_lift E').trans hEcard, ?_, ?_, ?_⟩
  · have : Zof D = center ↥(Fz z) := hZP
    rw [card_lift, this, hZ4]
  · have := mem_lift.mpr cd.z_mem
    rwa [hzP] at this
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 : ⁅e, c⁆ = 1 := by
      have := (Subgroup.commutator_le.mp hEZc.le) e he c hc
      rwa [mem_bot] at this
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact congrArg Subtype.val h1.symm
  · rw [← lift_sup, sup_comm, hEZ, lift_top]
  · rw [← lift_inf, inf_comm, hEZi, lift_zpowers, hzP]

variable {z : G}

@[expose] def zF (z : G) : ↥(Fz z) := ⟨z, z_mem_Fz z⟩

theorem zF_mem_center (z : G) : zF z ∈ center ↥(Fz z) :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Fz_comm_z z g.2)

theorem orderOf_zF (z : G) : orderOf (zF z) = orderOf z := Subgroup.orderOf_mk z _

theorem nontrivial_Fz (hz : orderOf z = 2) : Nontrivial ↥(Fz z) :=
  ⟨⟨zF z, 1, fun h => by
    have h1 : z = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hz
    omega⟩⟩

theorem shape_small (hz : orderOf z = 2) (hsymp : CFSG.Open.GLASymplecticType (Fz z))
    {D : Subgroup ↥(Fz z)} (hD : ThompsonCritical D) (hk : Nat.card (Zof D) ≤ 4) :
    Asc76Shape z := by
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  have hch := hsymp.2
  haveI := nontrivial_Fz hz
  obtain ⟨E, R, zz, cd⟩ := exists_critData hF2 hch hD
  have hzz : zF z = zz := cd.center_uniq _ (zF_mem_center z) ((orderOf_zF z).trans hz)
  subst hzz
  obtain ⟨z₁, hz₁Z, hz₁o, -, htri, -, -, -, -, -⟩ :=
    (symplectic_small_critical_center_structure hF2 hch hD).1 hk
  have hz₁ : z₁ = zF z := cd.z_uniq z₁ hz₁Z hz₁o
  subst hz₁
  rcases htri with ⟨hcyc, -⟩ | hext | ⟨w, hw⟩
  ·
    haveI := hcyc
    have hH : Hz z = Fz z :=
      Hz_eq_Fz_of_mulAut hF2
        (CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup _ hF2)
    exact Asc76Shape.uniqueInvolution hH (Or.inl hcyc)
  ·
    obtain ⟨w, hwc⟩ := LargeExtraspecial.S63.exists_card_extraspecial hext
    have hnab := nonabelian_of_extraspecial hext
    have hw0 : w ≠ 0 := by
      rintro rfl
      have hc2 : Nat.card (center ↥(Fz z)) = Nat.card ↥(Fz z) := by
        rw [hext.2.2.2, hwc]
        norm_num
      have htop : center ↥(Fz z) = ⊤ := Subgroup.eq_top_of_card_eq _ hc2
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : b ∈ center ↥(Fz z) := htop ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp this a)
    by_cases hw2 : 2 ≤ w
    · exact Asc76Shape.extraspecial w hw2 hext hwc
    · have hw1 : w = 1 := by omega
      subst hw1
      have h8 : Nat.card ↥(Fz z) = 8 := by rw [hwc]; norm_num
      rcases ComponentClassification.WalterSchur.dihedral_or_quaternion_of_card_eq_eight h8
        hnab with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · have hA : IsPGroup 2 (MulAut ↥(Fz z)) :=
          (GorensteinWalter.dihedral_mulAut_is_twoGroup (m := 2) le_rfl).of_equiv
            (MulAut.congr e).symm
        have hH : Hz z = Fz z := Hz_eq_Fz_of_mulAut hF2 hA
        exact Asc76Shape.dihedral 3 le_rfl hH ⟨e⟩
      · exact Asc76Shape.quaternion8 ⟨e⟩
  · exact Asc76Shape.z4star w hw.2.2.2.1 (isZ4Star_of_criticalCentralProduct rfl cd hw)

end CFSG.GF2Type.Aschbacher1976Full.Shape
