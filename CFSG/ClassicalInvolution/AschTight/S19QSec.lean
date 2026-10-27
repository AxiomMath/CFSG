module

public import CFSG.ClassicalInvolution.AschTight.S1911FusG
public import CFSG.ClassicalInvolution.AschTight.S19BEnd

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {F : Type} [Field F]

noncomputable def cStarProj (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (x : G) :
    ↥(K ⊓ Subgroup.centralizer ({x} : Set G)) →* SL(2, F) :=
  (S1911.slProj K e).comp (Subgroup.inclusion inf_le_left)

theorem surjective_cStarProj (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {x : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxK : x ∈ centralizerModOdd ⊤ K) :
    Function.Surjective (cStarProj e x) := by
  have hBL : Subgroup.zpowers x ≤ centralizerModOdd ⊤ K := Subgroup.zpowers_le.mpr hxK
  have hs := S19B.surjective_mk_inf_centralizer hx2 hBL
  intro b
  obtain ⟨y, hy⟩ := hs (e.symm b)
  have hyx : (y : G) ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x)) y.2.2
  refine ⟨⟨y, y.2.1, hyx⟩, ?_⟩
  change e (QuotientGroup.mk' _ (Subgroup.inclusion inf_le_left _)) = b
  have h1 : Subgroup.inclusion (inf_le_left : K ⊓ Subgroup.centralizer ({x} : Set G) ≤ K)
      ⟨y, y.2.1, hyx⟩ = Subgroup.inclusion inf_le_left y := rfl
  rw [h1]
  have h2 := congrArg e hy
  simpa using h2

noncomputable def perfectCoreProj (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (x : G) :
    ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({x} : Set G))) →* SL(2, F) :=
  ((cStarProj e x).comp (Helpers.perfectResidual _).subtype).comp
    (Subgroup.equivMapOfInjective _ _
      (K ⊓ Subgroup.centralizer ({x} : Set G)).subtype_injective).symm.toMonoidHom

omit [Finite G] in
theorem coe_perfectCoreProj (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (x : G)
    (y : ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({x} : Set G)))) :
    perfectCoreProj e x y = S1911.slProj K e ⟨y, (S1911.perfectResidualOf_le _ y.2).1⟩ := by
  set w := (Subgroup.equivMapOfInjective _ _
    (K ⊓ Subgroup.centralizer ({x} : Set G)).subtype_injective).symm y with hw
  have hwy : (((w : ↥(K ⊓ Subgroup.centralizer ({x} : Set G))) : G)) = y := by
    have h := congrArg Subtype.val (MulEquiv.apply_symm_apply (Subgroup.equivMapOfInjective _ _
      (K ⊓ Subgroup.centralizer ({x} : Set G)).subtype_injective) y)
    rw [← hw] at h
    exact h
  change S1911.slProj K e
    (Subgroup.inclusion inf_le_left (w : ↥(K ⊓ Subgroup.centralizer ({x} : Set G)))) = _
  congr 1
  exact Subtype.ext hwy

theorem nonempty_quotEquiv_perfectCore_of_cStar (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    {x : G} (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxK : x ∈ centralizerModOdd ⊤ K)
    (hperf : Group.IsPerfect SL(2, F)) (hO : classicalInvolutionOddCore SL(2, F) = ⊥) :
    Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({x} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({x} : Set G))) ≃*
        SL(2, F)) := by
  have := hperf
  have hsurj : Function.Surjective (perfectCoreProj e x) := by
    have hmap := finite_perfectResidual_surjects_to_perfect_image (cStarProj e x)
      (surjective_cStarProj e hx2 hxK)
    intro b
    have hb : b ∈ (Helpers.perfectResidual _).map (cStarProj e x) := by
      rw [hmap]
      trivial
    obtain ⟨y, hy, hyb⟩ := hb
    set E := Subgroup.equivMapOfInjective (Helpers.perfectResidual _)
      (K ⊓ Subgroup.centralizer ({x} : Set G)).subtype
      (K ⊓ Subgroup.centralizer ({x} : Set G)).subtype_injective with hE
    refine ⟨E ⟨y, hy⟩, ?_⟩
    have e1 : perfectCoreProj e x (E ⟨y, hy⟩) = cStarProj e x y := by
      change cStarProj e x ((Helpers.perfectResidual _).subtype (E.symm (E ⟨y, hy⟩))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    exact e1.trans hyb
  have hker : Odd (Nat.card (perfectCoreProj e x).ker) := by
    have hle : (perfectCoreProj e x).ker.map (perfectResidualOf _).subtype ≤ oddCoreOf K := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : perfectCoreProj e x y = 1 := hy
      rw [coe_perfectCoreProj] at hy'
      exact (S1911.slProj_eq_one_iff e _).mp hy'
    have hcard : Nat.card ((perfectCoreProj e x).ker.map (perfectResidualOf _).subtype) =
        Nat.card (perfectCoreProj e x).ker :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv).symm
    rw [← hcard]
    exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  exact S1911.nonempty_quotEquiv_of_surjective_of_odd _ hsurj hker hO

section Data

variable {p f : ℕ} [Fact p.Prime] {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem isClassicalMember_perfectCore_of_cStar (hd : Sec19Data p f K z S W) {x : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxK : x ∈ centralizerModOdd ⊤ K)
    (hzx : z ∈ Subgroup.centralizer ({x} : Set G)) :
    IsClassicalMember p f ((perfectResidualOf (K ⊓ Subgroup.centralizer ({x} : Set G))).subgroupOf
      (Subgroup.centralizer ({x} : Set G))) ⟨z, hzx⟩ := by
  have hp2 : p ≠ 2 := hd.tight.branch.odd
  have h5 : 5 ≤ p ^ f := hd.tight.branch.five
  obtain ⟨e⟩ := hd.tight.branch.member.nonempty_equiv
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField p f), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField p f))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]; omega)
    exact ⟨s, hs⟩
  have hperf : Group.IsPerfect SL(2, GaloisField p f) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField p f) (n := 2) le_rfl (Or.inr h4)
  have h2ne : (2 : GaloisField p f) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p f) p]; exact hp2)
  have hO : classicalInvolutionOddCore SL(2, GaloisField p f) = ⊥ :=
    ModelFacts.LinearAut.oddCore_sl2_eq_bot h2ne (by rw [hcard]; omega)
  exact S1911.isClassicalMember_perfectCore hd hp2 hzx
    (nonempty_quotEquiv_perfectCore_of_cStar e hx2 hxK hperf hO)

end Data

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
