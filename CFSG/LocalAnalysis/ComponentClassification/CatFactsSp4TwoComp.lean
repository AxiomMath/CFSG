module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CentralProd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

theorem kron_one_injective {g g' : Matrix (Fin 2) (Fin 2) K} (h : kron g 1 = kron g' 1) :
    g = g' := by
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp h
  have e : ∀ {a b : K}, a • (1 : Matrix (Fin 2) (Fin 2) K) = b • 1 → a = b := fun he => by
    simpa using congrFun (congrFun he 0) 0
  ext i j
  fin_cases i <;> fin_cases j
  exacts [e h1, e h2, e h3, e h4]

theorem kron_neg_one_one : kron (-1 : Matrix (Fin 2) (Fin 2) K) 1 = -1 := by
  rw [← neg_one_smul K (1 : Matrix (Fin 2) (Fin 2) K), kron_smul_left, kron, ← fromBlocks_one,
    fromBlocks_neg]
  simp

theorem ker_proj_comp_diagSL :
    ((proj 2 K).comp (diagSL K)).ker = center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff,
    coe_diagSL, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro (h | h)
    · refine ⟨1, one_pow _, ?_⟩
      rw [← kron_one_one] at h
      rw [kron_one_injective h]
      simp
    · refine ⟨-1, by simp, ?_⟩
      rw [← kron_neg_one_one] at h
      rw [kron_one_injective h]
      ext i j
      by_cases hij : i = j <;> simp [hij, one_apply]
  · rintro ⟨r, hr, hg⟩
    rw [Fintype.card_fin, pow_two] at hr
    rw [← hg]
    rcases mul_self_eq_one_iff.mp hr with rfl | rfl
    · left
      rw [map_one, kron_one_one]
    · right
      rw [map_neg, map_one, kron_neg_one_one]

variable (K) in
@[expose] def LEquiv : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Lsub K :=
  (QuotientGroup.quotientMulEquivOfEq ker_proj_comp_diagSL.symm).trans
    ((QuotientGroup.quotientKerEquivRange ((proj 2 K).comp (diagSL K))).trans
      (MulEquiv.subgroupCongr (MonoidHom.range_comp _ _)))

theorem LEquiv_mk (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((LEquiv K (QuotientGroup.mk g) : Lsub K) : StatedProj (StatedSp 2 K)) =
      proj 2 K (diagSL K g) :=
  rfl

theorem isSimpleGroup_Lsub [Finite K] (hK : 4 ≤ Nat.card K) : IsSimpleGroup (Lsub K) :=
  (LEquiv K).isSimpleGroup_congr.mp (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK)

theorem isSolvable_Lsub_of_card_three [Finite K] (hK : Nat.card K = 3) :
    Group.IsSolvable (Lsub K) := by
  have : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hK
  let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eP : Lsub K ≃* alternatingGroup (Fin 4) :=
    (LEquiv K).symm.trans ((CFSG.GorensteinWalter.psl2RingEquiv eK).symm.trans
      CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup)
  have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
  exact Group.isSolvable_of_isSolvable_injective (f := eP.toMonoidHom) eP.injective

theorem two_ne_zero_of_odd_card [Finite K] (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  have : Fintype K := Fintype.ofFinite K
  apply Ring.two_ne_zero
  intro h
  have := (FiniteField.even_card_iff_char_two (F := K)).mp h
  rw [← Nat.card_eq_fintype_card] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr this)

theorem pComponent_centralizer_u2 [Finite K] (hodd : Odd (Nat.card K))
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hMX : M ≤ centralizer {u2 K})
    (hM : CFSG.IsPComponent 2 (M.subgroupOf (centralizer {u2 K}))) :
    M = Lsub K ∧ 5 ≤ Nat.card K := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hperf := commutator_eq_of_isPComponent hMX hM
  have hne := ne_bot_of_isPComponent hM
  have hML := perfect_le_L h2 hMX hperf
  have h3 : Nat.card K ≠ 3 := by
    intro h3
    have := isSolvable_Lsub_of_card_three h3
    have hMs : Group.IsSolvable M :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hML)
        (Subgroup.inclusion_injective hML)
    have : Group.IsPerfect M := Subgroup.isPerfect_iff.mpr hperf
    have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hne
    exact Group.IsPerfect.not_isSolvable M hMs
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h5 : 5 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hodd
    omega
  refine ⟨?_, h5⟩
  set X := centralizer {u2 K}
  have hLX : Lsub K ≤ X := Lsub_le_centralizer
  have : IsSimpleGroup (Lsub K) := isSimpleGroup_Lsub (by omega)
  have hsimp : IsSimpleGroup ((Lsub K).subgroupOf X) :=
    (Subgroup.subgroupOfEquivOfLe hLX).isSimpleGroup_congr.mpr inferInstance
  have hsub : ((M.subgroupOf X).subgroupOf ((Lsub K).subgroupOf X)).IsSubnormal :=
    hM.choose_spec.2.1.subgroupOf
  rcases hsub.eq_bot_or_top_of_isSimpleGroup hsimp with hbot | htop
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    apply hne
    have hle : M.subgroupOf X ≤ (Lsub K).subgroupOf X := Subgroup.subgroupOf_mono _ hML
    have hMb : M.subgroupOf X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact hbot.le_bot ⟨hx, hle hx⟩
    rw [eq_bot_iff]
    intro m hm
    have : (⟨m, hMX hm⟩ : X) ∈ M.subgroupOf X := hm
    rw [hMb] at this
    exact congrArg Subtype.val this
  · rw [Subgroup.subgroupOf_eq_top] at htop
    refine le_antisymm hML fun l hl => ?_
    exact htop (show (⟨l, hLX hl⟩ : X) ∈ (Lsub K).subgroupOf X from hl)

end CFSG.ComponentClassification.CatFactsSp4
