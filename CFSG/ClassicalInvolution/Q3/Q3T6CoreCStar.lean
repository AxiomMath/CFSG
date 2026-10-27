module

public import CFSG.ClassicalInvolution.AschTight.S19BEnd
public import CFSG.ClassicalInvolution.AschTight.S1911FusB
public import CFSG.ClassicalInvolution.Uniform.UFacade
public import CFSG.ClassicalInvolution.Q3.Q3T6LinFin
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

theorem classicalInvolutionOddCore_sl2Three : classicalInvolutionOddCore SL(2, ZMod 3) = ⊥ := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore SL(2, ZMod 3))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hF : Odd (Nat.card (ZMod 3)) := by rw [Nat.card_zmod]; decide
  rcases sl2Three_normal_cases (classicalInvolutionOddCore SL(2, ZMod 3)) inferInstance with
      h | h | h | h
  · exact h
  · exfalso
    rw [h, natCard_center_of_equiv_sl2 hF (MulEquiv.refl SL(2, ZMod 3))] at hodd
    exact absurd hodd (by decide)
  · exfalso
    rw [h, sl2Three_card_commutator] at hodd
    exact absurd hodd (by decide)
  · exfalso
    rw [h, Subgroup.card_top, natCard_sl2Three] at hodd
    exact absurd hodd (by decide)

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem nonempty_quotEquiv_inf_centralizer_of_cStar
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) {B : Subgroup G}
    (hB2 : IsPGroup 2 B) (hBK : B ≤ centralizerModOdd ⊤ K) :
    Nonempty (↥(K ⊓ Subgroup.centralizer (B : Set G)) ⧸
      classicalInvolutionOddCore ↥(K ⊓ Subgroup.centralizer (B : Set G)) ≃* SL(2, ZMod 3)) := by
  set H : Subgroup G := K ⊓ Subgroup.centralizer (B : Set G) with hH
  let π : ↥H →* K ⧸ classicalInvolutionOddCore K :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)).comp
      (Subgroup.inclusion (inf_le_left : H ≤ K))
  have hπ : Function.Surjective π := S19B.surjective_mk_inf_centralizer hB2 hBK
  let ψ : ↥H →* SL(2, ZMod 3) := e.toMonoidHom.comp π
  have hψ : Function.Surjective ψ := e.surjective.comp hπ
  have hker : Odd (Nat.card ψ.ker) := by
    have hle : ψ.ker.map H.subtype ≤ oddCoreOf K := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : e (π y) = 1 := hy
      have h1 : π y = 1 := e.injective (by rw [hy', map_one])
      exact ⟨⟨(y : G), y.2.1⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    have hcard : Nat.card (ψ.ker.map H.subtype) = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← hcard]
    exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  exact S1911.nonempty_quotEquiv_of_surjective_of_odd ψ hψ hker
    classicalInvolutionOddCore_sl2Three

theorem isClassicalMember3_inf_centralizer_of_cStar {z : G} (hK : Q3.IsClassicalMember3 K z)
    {B : Subgroup G} (hB2 : IsPGroup 2 B) (hBK : B ≤ centralizerModOdd ⊤ K)
    {C : Subgroup G} (hC : C = Subgroup.centralizer (B : Set G)) (hzC : z ∈ C) :
    Q3.IsClassicalMember3 ((K ⊓ C).subgroupOf C) (⟨z, hzC⟩ : C) := by
  subst hC
  set C := Subgroup.centralizer (B : Set G) with hC
  have hKC : K ⊓ C ≤ C := inf_le_right
  refine ⟨?_, Subgroup.mem_subgroupOf.mpr ⟨hK.mem, hzC⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact hK.orderOf_eq_two
  · have h1 : IsSubnormal (K ⊓ C) (Subgroup.centralizer ({z} : Set G) ⊓ C) :=
      isSubnormal_inf hK.subnormal C
    have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ C).subgroupOf C =
        Subgroup.centralizer ({(⟨z, hzC⟩ : C)} : Set C) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h1 C
  · obtain ⟨e⟩ := hK.nonempty_equiv
    obtain ⟨e'⟩ := nonempty_quotEquiv_inf_centralizer_of_cStar e hB2 hBK
    let ε : (K ⊓ C).subgroupOf C ≃* ↥(K ⊓ C) := Subgroup.subgroupOfEquivOfLe hKC
    have hO : (classicalInvolutionOddCore ((K ⊓ C).subgroupOf C)).map ε.toMonoidHom =
        classicalInvolutionOddCore ↥(K ⊓ C) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant ε
    exact ⟨(QuotientGroup.congr _ _ ε hO).trans e'⟩

theorem isClassicalMember3_centralizer_of_cStar {z x : G} (hK : Q3.IsClassicalMember3 K z)
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxK : x ∈ centralizerModOdd ⊤ K)
    (hzx : z ∈ Subgroup.centralizer ({x} : Set G)) :
    Q3.IsClassicalMember3
      ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (Subgroup.centralizer ({x} : Set G)))
      (⟨z, hzx⟩ : Subgroup.centralizer ({x} : Set G)) :=
  isClassicalMember3_inf_centralizer_of_cStar hK hx2 (Subgroup.zpowers_le.mpr hxK)
    (by rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]) hzx

theorem isClassicalMemberU_inf_centralizer_of_cStar {z : G}
    (hK : IsClassicalMemberU (.sl2 3 1) K z) {B : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBK : B ≤ centralizerModOdd ⊤ K) {C : Subgroup G} (hC : C = Subgroup.centralizer (B : Set G))
    (hzC : z ∈ C) : IsClassicalMemberU (.sl2 3 1) ((K ⊓ C).subgroupOf C) (⟨z, hzC⟩ : C) :=
  isClassicalMember3_iff_U.mp
    (isClassicalMember3_inf_centralizer_of_cStar (isClassicalMember3_iff_U.mpr hK) hB2 hBK hC hzC)

theorem surjective_inf_centralizer_proj
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) {B : Subgroup G}
    (hB2 : IsPGroup 2 B) (hBK : B ≤ centralizerModOdd ⊤ K) :
    Function.Surjective (e.toMonoidHom.comp
      ((QuotientGroup.mk' (classicalInvolutionOddCore ↥K)).comp
        (Subgroup.inclusion (inf_le_left : K ⊓ Subgroup.centralizer (B : Set G) ≤ K)))) :=
  e.surjective.comp (S19B.surjective_mk_inf_centralizer hB2 hBK)

end CFSG.ClassicalInvolution.Q3.Q3T6
