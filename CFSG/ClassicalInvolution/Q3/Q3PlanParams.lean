module

public import CFSG.ClassicalInvolution.Q3.M11Branch
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.Walter.JRFacts
import CFSG.ClassicalInvolution.Q3.OddCentralizerFree
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

@[expose] def ClassicalMemberParameters3At (t : CFSG.Assembly.LowTwoRank.StatedLieTag) : Prop :=
  ∀ (n r e : ℕ) (hr : r.Prime), r ≠ 2 → CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n r e →
    (r ≠ 3 ∨ e ≠ 1) →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n r e hr).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ →
        ∀ (L : Subgroup X) (z : X), ¬ IsClassicalMember3 L z

@[expose] def ClassicalMemberParameters3 : Prop :=
  ∀ t : CFSG.Assembly.LowTwoRank.StatedLieTag, IsFundTag t → ClassicalMemberParameters3At t

@[expose] def SmallUpgrade3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z →
      (CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11) →
      LieSystem3 G (Set.range fun g : G => conjSub g K)

section Basic

variable {Y : Type} [Group Y]

theorem IsClassicalMember3.false_of_commutative {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 L z) (hcomm : ∀ a b : L, a * b = b * a) : False := by
  obtain ⟨e⟩ := h.nonempty_equiv
  apply sl2Three_not_comm (fun a b => ?_)
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm a)
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm b)
  apply e.symm.injective
  rw [map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul, hcomm a' b']

end Basic

section Simple

variable {G : Type} [Group G] [IsSimpleGroup G]

theorem isQuasisimple_of_simple_nonabelian' (hnab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple G := by
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem classicalInvolutionOddCore_eq_bot_of_simple [Finite G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : classicalInvolutionOddCore G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (classicalInvolutionOddCore G) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card (classicalInvolutionOddCore G)) :=
      CFSG.ComponentClassification.OddCore.odd_card G
    rw [h, Subgroup.card_top] at hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)

end Simple

section Ree

open CFSG.ComponentClassification.LiteratureLocal
  (ward_kleidman_small_Ree_involution_centralizer_maximal)

variable {G : Type} [Group G] [Finite G]

theorem false_of_isClassicalMember3_of_reeTitsModel {r e : ℕ}
    (hree : CFSG.Blueprint.ReeTitsModel G .twistedG2 r e) {K : Subgroup G} {z : G}
    (hK : IsClassicalMember3 K z) : False := by
  obtain ⟨-, -, -, hr3, -, h3⟩ := hree.1
  obtain ⟨a, hea, -⟩ := hree.2
  subst hr3 hea
  have ha : 1 ≤ a := by omega
  obtain ⟨-, -, hcen, -⟩ := ward_kleidman_small_Ree_involution_centralizer_maximal a ha G hree
  obtain ⟨L, hLC, hinf, hsup, ⟨eL⟩, -⟩ := hcen z hK.orderOf_eq_two
  have hE4 : 4 ≤ Nat.card (GaloisField 3 (2 * a + 1)) := by
    rw [GaloisField.card 3 (2 * a + 1) (by omega)]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : IsSimpleGroup PSL(2, GaloisField 3 (2 * a + 1)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4
  have : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hLnab : ∃ u v : ↥L, u * v ≠ v * u :=
    CFSG.Walter.exists_mul_ne_mul_of_mulEquiv_psl2 hE4 eL
  have hLq : CFSG.IsQuasisimple ↥L := CFSG.ClassicalInvolution.ModelFacts.native_isQuasisimple
    (isQuasisimple_of_simple_nonabelian' hLnab)
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hK.subnormal
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hK.orderOf_eq_two, pow_two] at this
  have hKL : K ⊓ L = ⊥ := by
    have hsub : IsSubnormal (K ⊓ L) L :=
      CFSG.ClassicalInvolution.ModelFacts.isSubnormal_inf hK.subnormal hLC
    rcases CFSG.ClassicalInvolution.ModelFacts.eq_or_le_center_of_isSubnormal hsub hLq with h | h
    · exfalso
      have hLK : L ≤ K := h ▸ inf_le_left
      have : Group.IsSolvable ↥K := hK.isSolvable
      have hL : Group.IsSolvable ↥L :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLK)
          (Subgroup.inclusion_injective hLK)
      obtain ⟨u, v, huv⟩ := hLnab
      exact huv ((IsSimpleGroup.comm_iff_isSolvable.mpr hL) u v)
    · have hZ : Subgroup.center ↥L = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h' | h'
        · exact h'
        · exfalso
          obtain ⟨u, v, huv⟩ := hLnab
          exact huv ((Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top v)) u)
      rw [hZ, Subgroup.map_bot] at h
      exact le_bot_iff.mp h
  have hsq : ∀ k ∈ K, k * k = 1 := by
    intro k hk
    have hkC := hKC hk
    have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ L, a * b = b * a := by
      intro a ha b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hzb : Commute z b := (Subgroup.mem_centralizer_singleton_iff.mp (hLC hb)).symm
      exact (hzb.zpow_left n).eq
    have hkC' : k ∈ Subgroup.zpowers z ⊔ L := hsup ▸ hkC
    obtain ⟨a, ha, l, hl, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hkC'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcz : Commute (z ^ n) l := hcomm _ ha l hl
    have h1 : (z ^ n * l) * (z ^ n * l) = (z ^ n * z ^ n) * (l * l) :=
      hcz.symm.mul_mul_mul_comm (z ^ n) l
    have h2 : z ^ n * z ^ n = 1 := by
      have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
      rw [← zpow_add, ← two_mul, zpow_mul, hz2', one_zpow]
    have hmemK : (z ^ n * l) * (z ^ n * l) ∈ K := K.mul_mem hk hk
    have hl2 : l * l ∈ K ⊓ L := by
      refine ⟨?_, L.mul_mem hl hl⟩
      rw [h1, h2, one_mul] at hmemK
      exact hmemK
    rw [hKL, Subgroup.mem_bot] at hl2
    rw [h1, h2, hl2, one_mul]
  refine hK.false_of_commutative fun u v => ?_
  have hu := hsq (u : G) u.2
  have hv := hsq (v : G) v.2
  have huv := hsq ((u : G) * v) (K.mul_mem u.2 v.2)
  apply Subtype.ext
  have hu' : (u : G) = (u : G)⁻¹ := eq_inv_of_mul_eq_one_left hu
  have hv' : (v : G) = (v : G)⁻¹ := eq_inv_of_mul_eq_one_left hv
  have huv' : (u : G) * v = ((u : G) * v)⁻¹ := eq_inv_of_mul_eq_one_left huv
  calc (u : G) * v = ((u : G) * v)⁻¹ := huv'
    _ = (v : G)⁻¹ * (u : G)⁻¹ := mul_inv_rev _ _
    _ = v * u := by rw [← hu', ← hv']

end Ree

section Upgrade

variable {G : Type} [Group G] [Finite G]

theorem isFundTag_of_lieModel3 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n r e : ℕ}
    (hr2 : r ≠ 2) (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n r e)
    (hmodel : CFSG.Blueprint.LieModel G t n r e) {K : Subgroup G} {z : G}
    (hK : IsClassicalMember3 K z) : IsFundTag t := by
  rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, hree⟩ | ⟨-, -, hsz⟩
  · simp only [CFSG.Blueprint.classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp only [CFSG.Blueprint.chevalleyExceptionalTags, Finset.mem_insert,
      Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp only [CFSG.Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact (false_of_isClassicalMember3_of_reeTitsModel hree hK).elim
    · exact absurd hadm.2.2.2.1 hr2
    · exact absurd hadm.2.2.2.1 hr2
  · exact absurd hsz.1 hr2

theorem smallUpgrade3_of_model (hfund : ClassicalIsFundamental3)
    (hpar : ClassicalMemberParameters3) : SmallUpgrade3 := by
  intro G _ _ _ hnab K z hK hG
  have hΛ : InClass3 (Set.range fun g : G => conjSub g K) := inClass3_conjugates hK
  rcases hG with ⟨t, n, r, e, hr, hr2, hadm, hmodel⟩ | hm11
  · have hFT : IsFundTag t := isFundTag_of_lieModel3 hr2 hadm hmodel hK
    obtain ⟨ψ, hsurj, hker⟩ := Upgrade.lieModelCentralCover t n r e hr hr2 hFT hadm G hmodel
    by_cases hre : r = 3 ∧ e = 1
    · obtain ⟨rfl, rfl⟩ := hre
      have hfundΛ : ∀ L ∈ Set.range (fun g : G => conjSub g K),
          (∃ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 hr).D, L = R.map ψ) ∧
            Nat.card L = 24 := by
        rintro _ ⟨g, rfl⟩
        exact hfund t n hr hFT hadm G ψ hsurj hker _ _ (hK.conj g)
      refine ⟨Unit, inferInstance, ⟨{
        kind := fun _ => CompData.model t n
        valid := fun _ => Or.inl ⟨t, n, hFT, hadm, rfl⟩
        hom := fun _ => ψ
        ker_le_center := fun _ => hker
        commute := fun i j h => absurd (Subsingleton.elim i j) h
        generate := by
          rw [eq_top_iff]
          intro x _
          obtain ⟨y, rfl⟩ := hsurj x
          exact Subgroup.mem_iSup_of_mem () ⟨y, rfl⟩
        fundamental := fun L hL => ⟨(), (hfundΛ L hL).1⟩
        meets := fun _ => by
          obtain ⟨R, hR, hLR⟩ := (hfundΛ K ⟨1, conjSub_one K⟩).1
          exact ⟨R, hR, by rw [← hLR]; exact ⟨1, conjSub_one K⟩⟩
        card_eq := fun L hL => (hfundΛ L hL).2 }⟩⟩
    · exfalso
      have hne : r ≠ 3 ∨ e ≠ 1 := by
        by_contra h
        push Not at h
        exact hre h
      exact hpar t hFT n r e hr hr2 hadm hne G ψ hsurj hker K z hK
  · obtain ⟨e⟩ := hm11
    refine m11Branch3 G _ hΛ (isQuasisimple_of_simple_nonabelian' hnab)
      (classicalInvolutionOddCore_eq_bot_of_simple hnab)
      ⟨(QuotientGroup.mk' _).comp e.symm.toMonoidHom, ?_⟩
    exact (QuotientGroup.mk'_surjective _).comp e.symm.surjective

end Upgrade

end CFSG.ClassicalInvolution.Q3
