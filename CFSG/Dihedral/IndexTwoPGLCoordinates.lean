module

public import CFSG.Dihedral.OriginalCyclingQuotients
public import CFSG.Dihedral.OrderTwentyFourCoordinates
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ImageDihedralSylowOddKernel
import all CFSG.Dihedral.BlueprintDefs
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem perfect_subgroup_le_normal_indexTwo (L N : Subgroup X)
    (hL : Group.IsPerfect L) (hN : N.Normal) (hindex : N.index = 2) : L ≤ N := by
  let : N.Normal := hN
  let Q := X ⧸ N
  have hcard : Nat.card Q = 2 := by rwa [← Subgroup.index_eq_card]
  let : IsCyclic Q := isCyclic_of_prime_card hcard
  let : IsMulCommutative Q := IsCyclic.isMulCommutative
  let f : L →* Q := (QuotientGroup.mk' N).comp L.subtype
  let : Group.IsPerfect L := hL
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : IsMulCommutative f.range := inferInstance
  let : Subsingleton f.range := inferInstance
  intro x hx
  have hfx : f ⟨x, hx⟩ = 1 := by
    exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict ⟨x, hx⟩) 1)
  exact (QuotientGroup.eq_one_iff (N := N) x).mp hfx

theorem alternatingFour_orderThree_products :
    ∀ x : alternatingGroup (Fin 4), ∃ a b : alternatingGroup (Fin 4),
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = x := by
  decide +kernel

omit [Finite X] in
theorem not_indexTwo_of_aFour_model (e : X ≃* alternatingGroup (Fin 4)) :
    ¬ ∃ N : Subgroup X, N.Normal ∧ N.index = 2 := by
  rintro ⟨N, hN, hindex⟩
  let : N.Normal := hN
  let Q := X ⧸ N
  have hcard : Nat.card Q = 2 := by rwa [← Subgroup.index_eq_card]
  let f : alternatingGroup (Fin 4) →* Q := (QuotientGroup.mk' N).comp e.symm.toMonoidHom
  have hkill (a : alternatingGroup (Fin 4)) (ha : a ^ 3 = 1) : f a = 1 := by
    have hd2 : orderOf (f a) ∣ 2 := hcard ▸ orderOf_dvd_natCard (f a)
    have hd3 : orderOf (f a) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, ha, map_one])
    have hd1 := Nat.dvd_gcd hd2 hd3
    norm_num at hd1
    exact hd1
  have hf : ∀ a, f a = 1 := by
    intro x
    obtain ⟨a, b, ha, hb, rfl⟩ := alternatingFour_orderThree_products x
    rw [map_mul, hkill a ha, hkill b hb, one_mul]
  have hsurj : Function.Surjective f := (QuotientGroup.mk'_surjective N).comp e.symm.surjective
  have hsub : Subsingleton Q := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    rw [hf x, hf y]⟩
  let : Subsingleton Q := hsub
  have hone : Nat.card Q = 1 := Nat.card_unique
  omega

set_option maxHeartbeats 1200000 in
theorem CoordinateWitness.containsPGL_of_dihedral_indexTwo
    (w : CoordinateWitness X) (hX : HasDihedralSylowTwo X)
    (hindex : ∃ N : Subgroup X, N.Normal ∧ N.index = 2) :
    pGammaL2PGLRange w.K ≤ w.rho.range := by
  let A := w.rho.range
  let e : X ≃* A := MonoidHom.ofInjective w.injective
  let : Finite A := Finite.of_surjective e e.surjective
  have hAd : HasDihedralSylowTwo A := hasDihedralSylowTwo_of_mulEquiv e.symm hX
  obtain ⟨N, hN, hNi⟩ := hindex
  let NA := N.map e.toMonoidHom
  have hNAn : NA.Normal := hN.map e.toMonoidHom e.surjective
  have hNAi : NA.index = 2 := by
    exact (Subgroup.index_map_of_bijective e.bijective N).trans hNi
  let L := pGammaL2LinearKernel w.K A
  let M := L.map A.subtype
  have hPSLM : pGammaL2PSLRange w.K ≤ M := by
    intro x hx
    have hxA : x ∈ A := w.containsPSL hx
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    change pGammaL2FieldProjection w.K A ⟨x, hxA⟩ = 1
    obtain ⟨y, rfl⟩ := hx
    simp [pGammaL2FieldProjection]
  have hMPGL : M ≤ pGammaL2PGLRange w.K := by
    rintro _ ⟨a, ha, rfl⟩
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact ha
  have hrel := pGammaL2_psl_range_relIndex_pgl_eq_two w.K w.oddPrimePower_card
  have hmul := Subgroup.relIndex_mul_relIndex
    (pGammaL2PSLRange w.K) M (pGammaL2PGLRange w.K) hPSLM hMPGL
  rw [hrel] at hmul
  have hcase : M = pGammaL2PSLRange w.K ∨ M = pGammaL2PGLRange w.K := by
    have hdiv : (pGammaL2PSLRange w.K).relIndex M ∣ 2 :=
      ⟨M.relIndex (pGammaL2PGLRange w.K), hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hleft | hleft
    · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp hleft) hPSLM)
    · have hright : M.relIndex (pGammaL2PGLRange w.K) = 1 := by
        rw [hleft] at hmul
        omega
      exact Or.inr (le_antisymm hMPGL (Subgroup.relIndex_eq_one.mp hright))
  rcases hcase with hMPSL | hMPGL'
  · have hcard : 3 < Nat.card w.K ∨ Nat.card w.K = 3 := by
      have hgt : 1 < Nat.card w.K := by
        let : Fintype w.K := Fintype.ofFinite w.K
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      obtain ⟨k, hk⟩ := w.odd
      omega
    rcases hcard with hcard | hthree
    · have hLperf : Group.IsPerfect L := by
        let eL : L ≃* M := L.equivMapOfInjective A.subtype A.subtype_injective
        have ePSL : L ≃* PSL2 w.K := by
          rw [hMPSL] at eL
          exact eL.trans (pGammaL2PSLRangeEquiv w.K).symm
        let : Group.IsPerfect (PSL2 w.K) := psl2_isPerfect_of_card_gt_three w.K hcard
        exact Group.IsPerfect.ofSurjective (f := ePSL.symm.toMonoidHom) ePSL.symm.surjective
      have hLodd : Odd L.index := by
        rw [pGammaL2LinearKernel_index_eq_card_range]
        exact pGammaL2_field_projection_range_odd_of_dihedral w.K w.oddPrimePower_card
          hcard A w.containsPSL hAd
      have hLNA := perfect_subgroup_le_normal_indexTwo L NA hLperf hNAn hNAi
      have hdvd : 2 ∣ L.index := by
        simpa only [hNAi] using Subgroup.index_dvd_of_le hLNA
      exact (hLodd.not_two_dvd_nat hdvd).elim
    · have hLA : L = ⊤ := by
        apply top_le_iff.mp
        intro a _
        change pGammaL2FieldProjection w.K A a = 1
        exact ringAut_eq_one_of_card_three w.K hthree _
      have hAeq : A = pGammaL2PSLRange w.K := by
        change L.map A.subtype = pGammaL2PSLRange w.K at hMPSL
        rw [hLA, Subgroup.map_top, Subgroup.range_subtype] at hMPSL
        exact hMPSL
      let : Fintype w.K := Fintype.ofFinite w.K
      let eK : ZMod 3 ≃+* w.K := ZMod.ringEquivOfPrime w.K Nat.prime_three
        (by rwa [← Nat.card_eq_fintype_card])
      let eA : A ≃* alternatingGroup (Fin 4) :=
        (MulEquiv.subgroupCongr hAeq).trans ((pGammaL2PSLRangeEquiv w.K).symm.trans
          ((FieldTransport.projectiveSpecialLinearGroupMulEquiv eK.symm).trans
            psl2_three_equiv_alternatingGroup))
      exact (not_indexTwo_of_aFour_model eA ⟨NA, hNAn, hNAi⟩).elim
  · rw [← hMPGL']
    exact (Subgroup.map_subtype_le L)

variable {G : Type} [Group G] [Finite G]

theorem oddCore_quotient_has_indexTwo (H : Subgroup G)
    (hindex : HasNormalIndexTwo H) :
    ∃ L : Subgroup (H ⧸ Assembly.oddCore H), L.Normal ∧ L.index = 2 := by
  obtain ⟨N, hN, hNi⟩ := (hasNormalIndexTwo_iff_exists H).mp hindex
  let : N.Normal := hN
  have htwo : IsPGroup 2 (H ⧸ N) := IsPGroup.of_card (n := 1) (by
    rw [← Subgroup.index_eq_card, hNi]
    decide)
  have hmap := odd_le_normal_of_two_quotient (oddCoreOf H) H (oddCoreOf_le H)
    N (oddCoreOf_odd H) htwo
  have hcoreN : Assembly.oddCore H ≤ N := by
    intro x hx
    have hmx := hmap (Subgroup.mem_map_of_mem H.subtype hx)
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmx
    exact (Subtype.ext hyeq : y = x) ▸ hy
  let q : H →* (H ⧸ Assembly.oddCore H) := QuotientGroup.mk' (Assembly.oddCore H)
  have hker : q.ker ≤ N := by rwa [QuotientGroup.ker_mk']
  refine ⟨N.map q, hN.map q (QuotientGroup.mk'_surjective _), ?_⟩
  exact (N.index_map_eq (QuotientGroup.mk'_surjective _) hker).trans hNi

theorem hasPGLCoordinates_of_dihedral_indexTwo (H : Subgroup G)
    (hHd : HasDihedralSylowTwo H) (hcoord : HasCoordinates H)
    (hindex : HasNormalIndexTwo H) : HasPGLCoordinates H := by
  obtain ⟨w⟩ := hcoord
  let q : H →* (H ⧸ Assembly.oddCore H) := QuotientGroup.mk' (Assembly.oddCore H)
  have hkerodd : Odd (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hranged := image_hasDihedralSylowTwo_of_odd_kernel hHd q hkerodd
  have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hQd : HasDihedralSylowTwo (H ⧸ Assembly.oddCore H) := by
    rw [hrange] at hranged
    exact hasDihedralSylowTwo_of_mulEquiv Subgroup.topEquiv.symm hranged
  exact ⟨w, w.containsPGL_of_dihedral_indexTwo hQd (oddCore_quotient_has_indexTwo H hindex)⟩

namespace OriginalData

theorem one_cycle_PGL_and_indexTwo (d : OriginalData G)
    (H : Subgroup G) (hH : H ≠ ⊤) (hSH : (d.S : Subgroup G) ≤ H)
    (i j : Fin 2) (hi : Cycles H (d.V i)) (hj : ¬ Cycles H (d.V j)) :
    HasPGLCoordinates H ∧ HasNormalIndexTwo H := by
  obtain ⟨hcoord, hindex⟩ := d.one_cycle_coordinates_and_indexTwo H hH hSH i j hi hj
  exact ⟨hasPGLCoordinates_of_dihedral_indexTwo H
    (d.has_dihedral_sylow_overgroup H hSH) hcoord hindex, hindex⟩

end OriginalData

end CFSG.DihedralBlueprint
