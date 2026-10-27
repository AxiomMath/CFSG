module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7S
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Split
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CentData

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Foote5.OddLieCore.Exc
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.E2
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K]

theorem centModel_e7_t1
    [Finite K] (hK2 : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) :
    CentModel (toralCentralizer .E7 K (bitsTuple e7BitsOne)) := by
  have hb : ∀ j : Fin (Tag.rank .E7), j ≠ CatLeafProof.e7Node 0 → e7BitsOne j = false := by
    decide
  have hci : ∀ j, j ≠ CatLeafProof.e7Node 0 → bitsTuple (K := K) e7BitsOne j = 1 := fun j hj => by
    simp [bitsTuple, hb j hj]
  have hθ : e7Theta ∈ posRoots (rootCharKernel (bitsTuple (K := K) e7BitsOne)) :=
    ⟨⟨isRoot_e7Theta, rootChar_bitsTuple_eq_one (by decide)⟩, by decide⟩
  exact centModel_toral_single hK2 hK5 (bitsTuple_mem _) hci
    (weyl_eq_one_of_fix_posKernel_single hci hθ (by decide))

theorem centModel_e7_t4
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK3 : 3 ≤ Nat.card K) : CentModel (toralCentralizer .E7 K (bitsTuple e7BitsTwo)) := by
  classical
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hc := bitsTuple_mem (K := K) e7BitsTwo
  set c := bitsTuple (K := K) e7BitsTwo with hcdef
  set χ := maskChar (signTupleBits c) with hχdef
  have hkerχ : rootCharKernel c = kernelRoots χ := rootCharKernel_eq_kernelRoots hK2 hc
  have hχ2 : χ = signMaskChar .E7 2 := by
    rw [hχdef, hcdef, signTupleBits_bitsTuple hK2]
    unfold signMaskChar
    congr 1
    funext j
    revert j
    decide
  have hsub : Subsingleton (KernelComponent χ) := by
    rw [hχ2]
    exact ClassicalInvolution.Q3.e7_subsingleton_two
  have hker : ∀ v : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 v →
      (∀ j, e7BitsTwo j = true → Even (v j)) → v ∈ kernelRoots χ := fun v hv he => by
    rw [← hkerχ]
    exact ⟨hv, rootChar_bitsTuple_eq_one he⟩
  have hncard : ∀ ψ : KernelComponent χ, 2 < (componentRoots χ ψ).ncard := by
    intro ψ
    have hmem : ∀ v (hv : v ∈ kernelRoots χ), v ∈ componentRoots χ ψ :=
      fun v hv => ⟨hv, Subsingleton.elim _ _⟩
    have hfin : (componentRoots χ ψ).Finite :=
      (finite_setOf_isRoot .E7).subset fun v hv => by
        obtain ⟨h, -⟩ := hv
        exact h.1
    have h0 := hker (Pi.single (CatLeafProof.e7Node 0) 1) (isRoot_single _ _) (by decide)
    have h2 := hker (Pi.single (CatLeafProof.e7Node 2) 1) (isRoot_single _ _) (by decide)
    have hn0 : -Pi.single (CatLeafProof.e7Node 0) 1 ∈ kernelRoots χ := by
      rw [← hkerχ] at h0 ⊢
      exact neg_mem_rootCharKernel h0
    exact (Set.two_lt_ncard_iff hfin).2 ⟨_, _, _, hmem _ h0, hmem _ hn0, hmem _ h2,
      by decide, by decide, by decide⟩
  have hS : ∀ ψ : KernelComponent χ, IsComponent ((componentRootSpan K χ ψ).subgroupOf
      (toralCentralizer .E7 K c)) := fun ψ =>
    isComponent_componentRootSpan_toral_of_ncard hK2 hc ψ (hncard ψ)
  have : Finite (ModGL .E7 K) := finite_modGL
  set L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have heven : ∀ y ∈ TwE7.e7Gamma2, ∀ j, e7BitsTwo j = true → Even (y.1 j) := by decide
  have hΓker : ∀ y ∈ TwE7.e7Gamma2, y.1 ∈ rootCharKernel c := by
    intro y hy
    obtain ⟨i, hi⟩ := TwE7.e7Gamma2_mem y hy
    exact ⟨hi ▸ TwE7.e7A7Root_isRoot i, rootChar_bitsTuple_eq_one (heven y hy)⟩
  have hdiag : ∀ g : toralCentralizer .E7 K c,
      (∀ ψ : KernelComponent χ, ∀ s ∈ (componentRootSpan K χ ψ).subgroupOf
        (toralCentralizer .E7 K c), s * g = g * s) →
      ∃ b : Fin (Tag.rank .E7) → Lˣ,
        baseChangeGL (algebraMap K L) (g : ModGL .E7 K) = rootDiagUnit .E7 b ∧
          ∀ j, j ≠ CatLeafProof.e7Node 1 → b j = 1 := by
    intro g hg
    have hpin := commute_pinnedX_of_commute_rootFactors hK2 hc hg
    obtain ⟨b, hb, hχb⟩ := e7_rootDiagUnit_of_commute_rootSL2 (L := L) p hK3
      (Subgroup.mem_inf.1 g.2).1 TwE7.e7Gamma2
      (fun y hy => (hΓker y hy).1) 19 (fun α hα => TwE7.e7Gamma2_reg α (mem_rootFinset.2 hα))
      (fun y hy A => commute_rootSL2_of_commute (hΓker y hy).1 (hpin _ (hΓker y hy))
        (hpin _ (neg_mem_rootCharKernel (hΓker y hy))) A)
    refine ⟨b, hb, fun j hj => ?_⟩
    have hmem : ∃ y ∈ TwE7.e7Gamma2, y.1 = Pi.single j 1 := by
      revert j
      decide
    obtain ⟨y, hy, hyj⟩ := hmem
    have h := hχb y hy
    rwa [hyj, rootChar_piSingle_eq_coord] at h
  refine ⟨KernelComponent χ, fun ψ => (componentRootSpan K χ ψ).subgroupOf
      (toralCentralizer .E7 K c), hS, fun ψ => Burgoyne.even_card_of_isQuasisimple (hS ψ).1,
    fun g h hg hh => ?_, fun g h hg hh hg2 hh2 hg1 hh1 => ?_⟩
  · obtain ⟨b, hb, -⟩ := hdiag g hg
    obtain ⟨b', hb', -⟩ := hdiag h hh
    refine Subtype.ext (baseChangeGL_injective (algebraMap K L) ?_)
    change baseChangeGL (algebraMap K L) ((g : ModGL .E7 K) * (h : ModGL .E7 K)) =
      baseChangeGL (algebraMap K L) ((h : ModGL .E7 K) * (g : ModGL .E7 K))
    rw [map_mul, map_mul, hb, hb', ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  · obtain ⟨b, hb, hbj⟩ := hdiag g hg
    obtain ⟨b', hb', hbj'⟩ := hdiag h hh
    have hval2 : ∀ x : toralCentralizer .E7 K c, x * x = 1 →
        baseChangeGL (algebraMap K L) (x : ModGL .E7 K) *
          baseChangeGL (algebraMap K L) (x : ModGL .E7 K) = 1 := fun x hx => by
      rw [← map_mul, show (x : ModGL .E7 K) * x = 1 from congrArg Subtype.val hx, map_one]
    have hval1 : ∀ x : toralCentralizer .E7 K c, x ≠ 1 →
        baseChangeGL (algebraMap K L) (x : ModGL .E7 K) ≠ 1 := fun x hx h1 =>
      hx (Subtype.ext (baseChangeGL_injective (algebraMap K L) (h1.trans (map_one _).symm)))
    refine Subtype.ext (baseChangeGL_injective (algebraMap K L) ?_)
    rw [hb, hb']
    refine rootDiagUnit_eq_of_single hbj hbj' ?_ ?_ ?_ ?_
    · rw [← hb]
      exact hval2 g hg2
    · rw [← hb']
      exact hval2 h hh2
    · rw [← hb]
      exact hval1 g hg1
    · rw [← hb']
      exact hval1 h hh1

theorem centModel_e7_t7
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    CentModel (fixedSubgroup (rootDiagAut .E7 K (bitsTuple e7BitsSix))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, hK3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  set L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set H := fixedSubgroup (rootDiagAut .E7 K (bitsTuple (K := K) e7BitsSix)) with hHdef
  have hle : e7LeviE6 K ≤ H := e7LeviE6_le_fixedSubgroup hK2
  have hQ : IsComponent ((e7LeviE6 K).subgroupOf H) :=
    ⟨(isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hle)).2
        (isQuasisimple_e7LeviE6 hp hp2 hK),
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
        (fixedSubgroup_le_normalizer_e7LeviE6 hK2)).isSubnormal⟩
  have : Finite (ModGL .E7 K) := finite_modGL
  have hdiag : ∀ g : H, (∀ s ∈ (e7LeviE6 K).subgroupOf H, s * g = g * s) →
      ∃ b : Fin (Tag.rank .E7) → Lˣ,
        baseChangeGL (algebraMap K L) ((g : adjointGroup .E7 K) : ModGL .E7 K) =
          rootDiagUnit .E7 b ∧ ∀ j, j ≠ CatLeafProof.e7Node 6 → b j = 1 := by
    intro g hg
    have hcent : ∀ y ∈ e7LeviE6 K, (g : adjointGroup .E7 K) * y = y * g := fun y hy =>
      (congrArg Subtype.val (hg ⟨y, hle hy⟩ (Subgroup.mem_subgroupOf.2 hy))).symm
    have hgT := SRE7.mem_torusGroup_of_centralizes_e7LeviE6 (p := p) hK3 (L := L) hcent
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgT
    refine ⟨b, hb, fun j hj => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k : Fin 6, e7LeviE6Node k = j := by
      revert j
      decide
    have h1 : ((g : adjointGroup .E7 K) : ModGL .E7 K) *
        simpleRootSL2 .E7 K (e7LeviE6Node k) (uSL 1) =
          simpleRootSL2 .E7 K (e7LeviE6Node k) (uSL 1) * ((g : adjointGroup .E7 K) : ModGL .E7 K) :=
      congrArg Subtype.val (hcent _ (SRE7.simpleRootSL2_mem_e7LeviE6 K k (uSL 1)))
    have h2 := congrArg (baseChangeGL (algebraMap K L)) h1
    rw [map_mul, map_mul, RankThree.Chevalley.baseChangeGL_simpleRootSL2, map_uSL, map_one, hb,
      ← TwE7.rootSL2_single] at h2
    have h3 := TwE7.rootChar_eq_one_of_commute (isRoot_single _ _) h2
    rwa [rootChar_piSingle_eq_coord] at h3
  have hval2 : ∀ x : H, x * x = 1 →
      baseChangeGL (algebraMap K L) ((x : adjointGroup .E7 K) : ModGL .E7 K) *
        baseChangeGL (algebraMap K L) ((x : adjointGroup .E7 K) : ModGL .E7 K) = 1 :=
    fun x hx => by
      rw [← map_mul, show ((x : adjointGroup .E7 K) : ModGL .E7 K) *
        ((x : adjointGroup .E7 K) : ModGL .E7 K) = 1 from
        congrArg (fun y : H => ((y : adjointGroup .E7 K) : ModGL .E7 K)) hx, map_one]
  have hval1 : ∀ x : H, x ≠ 1 →
      baseChangeGL (algebraMap K L) ((x : adjointGroup .E7 K) : ModGL .E7 K) ≠ 1 :=
    fun x hx h1 => hx (Subtype.ext (Subtype.ext
      (baseChangeGL_injective (algebraMap K L) (h1.trans (map_one _).symm))))
  refine ⟨Unit, fun _ => (e7LeviE6 K).subgroupOf H, fun _ => hQ,
    fun _ => Burgoyne.even_card_of_isQuasisimple hQ.1, fun g h hg hh => ?_,
    fun g h hg hh hg2 hh2 hg1 hh1 => ?_⟩
  · obtain ⟨b, hb, -⟩ := hdiag g (hg ())
    obtain ⟨b', hb', -⟩ := hdiag h (hh ())
    refine Subtype.ext (Subtype.ext (baseChangeGL_injective (algebraMap K L) ?_))
    change baseChangeGL (algebraMap K L) (((g : adjointGroup .E7 K) : ModGL .E7 K) *
        ((h : adjointGroup .E7 K) : ModGL .E7 K)) =
      baseChangeGL (algebraMap K L) (((h : adjointGroup .E7 K) : ModGL .E7 K) *
        ((g : adjointGroup .E7 K) : ModGL .E7 K))
    rw [map_mul, map_mul, hb, hb', ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  · obtain ⟨b, hb, hbj⟩ := hdiag g (hg ())
    obtain ⟨b', hb', hbj'⟩ := hdiag h (hh ())
    refine Subtype.ext (Subtype.ext (baseChangeGL_injective (algebraMap K L) ?_))
    rw [hb, hb']
    refine rootDiagUnit_eq_of_single hbj hbj' ?_ ?_ ?_ ?_
    · rw [← hb]
      exact hval2 g hg2
    · rw [← hb']
      exact hval2 h hh2
    · rw [← hb]
      exact hval1 g hg1
    · rw [← hb']
      exact hval1 h hh1

theorem centModel_e7_split
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hK5 : 5 ≤ Nat.card K) {m : ℕ} (hm : m = 1 ∨ m = 2 ∨ m = 3) :
    CentModel (fixedSubgroup (rootDiagAut .E7 K (signMaskTuple .E7 K m))) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, hK3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  rcases hm with rfl | rfl | rfl
  · rw [signMaskTuple_one]
    exact centModel_fixedSubgroup_rootDiagAut (centModel_e7_t1 hK2 hK5)
  · rw [signMaskTuple_two]
    exact centModel_fixedSubgroup_rootDiagAut (centModel_e7_t4 p hp2 hK3)
  · rw [signMaskTuple_three]
    obtain ⟨n, hn⟩ := exists_conj_rootDiagAut_three (K := K) hK2
    rw [hn]
    exact (centModel_e7_t7 hp hp2 hK).of_mulEquiv (fixedSubgroupMulConjEquiv _ _).symm

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
