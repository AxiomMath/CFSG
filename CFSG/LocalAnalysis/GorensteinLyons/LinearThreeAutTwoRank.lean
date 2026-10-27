module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBULinearUnitaryOuterExtraspecial
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdOrder
public import CFSG.RankThree.SubgroupLists.ExtraspecialCore
public import CFSG.RankThree.OddKernel.SimpleQuotient

public section

namespace CFSG.LocalAnalysis.GorensteinLyons.LinearUnitaryOuter

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_le_two_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {H : Subgroup C}
    (hH : ∀ x ∈ H, x * x = 1) : Nat.card H ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine RankThree.SubgroupLists.card_le_of_pow_eq_one_of_isCyclic (n := 2) fun c => ?_
  exact Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hH c c.2)

theorem card_le_four_of_closure_pair {Q : Type*} [Group Q] [Finite Q]
    (hQ : ∀ x y : Q, x * y = y * x) {a b : Q} (hab : closure ({a, b} : Set Q) = ⊤)
    {B : Subgroup Q} (hB : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 4 := by
  set C := zpowers a with hC
  have hCn : C.Normal := ⟨fun x hx g => by rw [hQ g x, mul_inv_cancel_right]; exact hx⟩
  set π := QuotientGroup.mk' C with hπ
  have : IsCyclic (Q ⧸ C) := by
    have hle : closure ({a, b} : Set Q) ≤ (zpowers (π b)).comap π := by
      rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, mem_zpowers _⟩
      change π a ∈ zpowers (π b)
      have ha : π a = 1 := (QuotientGroup.eq_one_iff a).mpr (mem_zpowers a)
      rw [ha]
      exact one_mem _
    refine ⟨⟨π b, fun z => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C z
    exact mem_zpowers_iff.mp (hle (hab ▸ mem_top x))
  have hsplit := RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker π B
  rw [QuotientGroup.ker_mk'] at hsplit
  have h1 : Nat.card ↥(B.map π) ≤ 2 := by
    refine card_le_two_of_isCyclic fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_mul, hB x hx, map_one]
  have h2 : Nat.card ↥(B ⊓ C) ≤ 2 := by
    have hle : B ⊓ C ≤ C := inf_le_right
    rw [← Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    refine card_le_two_of_isCyclic fun y hy => Subtype.ext ?_
    rw [mem_subgroupOf] at hy
    simpa using hB y (Subgroup.mem_inf.mp hy).1
  rw [hsplit]
  calc Nat.card ↥(B.map π) * Nat.card ↥(B ⊓ C) ≤ 2 * 2 := Nat.mul_le_mul h1 h2
    _ = 4 := rfl

variable {K : Type} [Field K] [Finite K]

theorem card_le_four_of_outer_projectiveSL_three {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {B : Subgroup (Outer (LinearFlag.projectiveSL 3 K))} (hB : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 4 := by
  have : Finite (MulAut (LinearFlag.projectiveSL 3 K)) :=
    Finite.of_injective (fun f : MulAut (LinearFlag.projectiveSL 3 K) =>
      (f : LinearFlag.projectiveSL 3 K → LinearFlag.projectiveSL 3 K))
      fun f g h => MulEquiv.ext (congrFun h)
  obtain ⟨N, hNn, -, hNcard, hab, a, b, hgen⟩ := linear_outer_filtration (K := K) (n := 3) le_rfl
  have hNodd : Odd (Nat.card N) := by
    refine Odd.of_dvd_nat ?_ (hNcard.trans (Nat.gcd_dvd_right 3 _))
    rw [hK]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h2 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h2
      simp at h2
    · exact Nat.Even.sub_odd h1 (Nat.even_pow.mpr ⟨even_two, hm.ne'⟩) odd_one
  have hBN : ∀ x ∈ B, x ∈ N → x = 1 := by
    intro x hxB hxN
    have h2 : (⟨x, hxN⟩ : N) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]; exact hB x hxB)
    have hdvd : orderOf (⟨x, hxN⟩ : N) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hodd : orderOf (⟨x, hxN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h1 : orderOf (⟨x, hxN⟩ : N) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exact absurd (h ▸ hodd) (by
          rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hNodd)
    have := orderOf_eq_one_iff.mp h1
    exact congrArg Subtype.val this
  set ψ := QuotientGroup.mk' N with hψ
  have hsplit := RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker ψ B
  rw [QuotientGroup.ker_mk'] at hsplit
  have hinf : Nat.card ↥(B ⊓ N) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr (hBN x hx.1 hx.2)
  rw [hsplit, hinf, mul_one]
  refine card_le_four_of_closure_pair hab hgen fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := hy
  rw [← map_mul, hB x hx, map_one]

theorem card_le_of_elemAbelian_mulAut_projectiveSL_three {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (hv : padicValNat 2 (Nat.card (LinearFlag.projectiveSL 3 K)) = 3 * m)
    {A : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))} (hA : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 2 ^ (3 * m + 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := LinearFlag.projectiveSL 3 K
  have : Finite Y := inferInstance
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) fun f g h => MulEquiv.ext (congrFun h)
  set π := QuotientGroup.mk' (inner Y) with hπ
  have hsplit := RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker π A
  rw [QuotientGroup.ker_mk'] at hsplit
  have hout : Nat.card ↥(A.map π) ≤ 4 := by
    refine card_le_four_of_outer_projectiveSL_three hK fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_mul, hA x hx, map_one]
  have hin : Nat.card ↥(A ⊓ inner Y) ≤ 2 ^ (3 * m) := by
    have hpg : IsPGroup 2 ↥(A ⊓ inner Y) := fun x =>
      ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, pow_two]; exact hA x x.2.1)⟩
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hdvd1 : Nat.card ↥(A ⊓ inner Y) ∣ Nat.card ↥(inner Y) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hdvd2 : Nat.card ↥(inner Y) ∣ Nat.card Y := by
      change Nat.card (MulAut.conj : Y →* MulAut Y).range ∣ Nat.card Y
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (MulAut.conj : Y →* MulAut Y)).toEquiv.symm]
      exact Subgroup.card_quotient_dvd_card _
    have hY0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    have hle : k ≤ padicValNat 2 (Nat.card Y) :=
      (padicValNat_dvd_iff_le hY0).mp (hk ▸ hdvd1.trans hdvd2)
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (hv ▸ hle)
  rw [hsplit, pow_add, mul_comm (2 ^ (3 * m))]
  exact Nat.mul_le_mul hout hin

theorem pRank_mulAut_le_of_lieModel_psl_three {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 1 ≤ m) (hX : Blueprint.LieModel X .PSL 3 2 m) : pRank 2 (MulAut X) ≤ 3 * m + 2 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  set Y := LinearFlag.projectiveSL 3 K
  have hv : padicValNat 2 (Nat.card Y) = 3 * m := by
    rw [← Nat.card_congr e.toEquiv]
    exact ComponentClassification.GrSLit.L34Sec5S.padicValNat_card_of_lieModel_psl_three hm hX
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) fun f g h => MulEquiv.ext (congrFun h)
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) fun f g h => MulEquiv.ext (congrFun h)
  calc pRank 2 (MulAut X) ≤ pRank 2 (MulAut Y) :=
        RankThree.OddKernel.pRank_le_of_injective (by norm_num)
          (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    _ ≤ 3 * m + 2 := by
      rw [SectionRank.pRank_eq_open_pRank_top]
      refine SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
      refine card_le_of_elemAbelian_mulAut_projectiveSL_three hK hv fun x hx => ?_
      rw [← pow_two]
      exact hE.2 x hx

end CFSG.LocalAnalysis.GorensteinLyons.LinearUnitaryOuter
