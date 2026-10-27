module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Cyclic
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.CoverLift

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Dickson.Sec6.I923 (isCyclic_hopfMultiplier_psl exceptionalOrders_psl_eq)

section Card

variable {K : Type} [Field K] [Finite K]

theorem gcd_le_card_scalars {n : ℕ} (hn : 1 ≤ n) :
    Nat.gcd n (Nat.card K - 1) ≤ Nat.card (scalars n K) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  set d := Nat.gcd n (Nat.card K - 1) with hd
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgo : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hdq : d ∣ Nat.card K - 1 := Nat.gcd_dvd_right _ _
  have hdn : d ∣ n := Nat.gcd_dvd_left _ _
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
  have hq0 : 0 < Nat.card K - 1 := by
    have := Nat.card_pos (α := K)
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    omega
  set ζ : Kˣ := g ^ ((Nat.card K - 1) / d) with hζ
  have hdiv : (Nat.card K - 1) / d ∣ orderOf g := by rw [hgo]; exact Nat.div_dvd_of_dvd hdq
  have hζo : orderOf ζ = d := by
    rw [hζ, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd0).ne' hdiv, hgo,
      Nat.div_div_self hdq hq0.ne']
  have hζn : ζ ∈ rootsOfUnity n K := by
    rw [mem_rootsOfUnity]
    exact orderOf_dvd_iff_pow_eq_one.1 (hζo ▸ hdn)
  have hcard : Nat.card (scalars n K) = Nat.card (rootsOfUnity n K) := by
    rw [scalars_eq_center]
    have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n) (R := K)
    rw [Fintype.card_fin, max_eq_left hn] at e
    exact Nat.card_congr e.toEquiv
  rw [hcard]
  have h1 : orderOf (⟨ζ, hζn⟩ : rootsOfUnity n K) = d := by
    rw [← hζo]
    exact Subgroup.orderOf_mk ζ hζn
  have h2 := orderOf_dvd_natCard (⟨ζ, hζn⟩ : rootsOfUnity n K)
  rw [h1] at h2
  exact Nat.le_of_dvd Nat.card_pos h2

end Card

section Hopf

variable {K : Type} [Field K] [Finite K]

theorem hopfMultiplier_card_psl (hGA : GriessAllModelsStatement) {n p f : ℕ}
    (hadm : StatedLieAdmissible .PSL n p f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (h322 : ¬(n = 3 ∧ p = 2 ∧ f = 2)) (hdvd : ¬ Nat.Coprime 3 (Nat.gcd n (p ^ f - 1))) :
    Nat.card (hopfMultiplier (projectiveSL n K)) = Nat.gcd n (p ^ f - 1) := by
  have hcl : StatedClassicalModel (projectiveSL n K) .PSL n p f :=
    ⟨hadm, K, inferInstance, inferInstance, hK,
      ⟨(CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv n K).symm⟩⟩
  obtain ⟨-, ⟨e⟩⟩ := hGA (projectiveSL n K) .PSL n p f ⟨hadm, Or.inl hcl⟩
  have hex := exceptionalOrders_psl_eq hn h322 hdvd
  let e' : hopfMultiplier (projectiveSL n K) ≃*
      Multiplier.generic .PSL n p f × Multiplier.exceptional .PSL n p f :=
    (hopfMultiplierEquivGriess (projectiveSL n K)).symm.trans e
  rw [Nat.card_congr e'.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  have hg1 : (Multiplier.genericOrders .PSL n p f).1 = Nat.gcd n (p ^ f - 1) := rfl
  have hg2 : (Multiplier.genericOrders .PSL n p f).2 = 1 := rfl
  have hc : ∀ m : ℕ, Nat.card (Multiplicative (ZMod m)) = m := fun m => by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  simp only [Multiplier.generic, Multiplier.exceptional, hc, hg1, hg2, hex]
  simp

theorem exists_slHom_to_cover (hGA : GriessAllModelsStatement) {n p f : ℕ}
    (hadm : StatedLieAdmissible .PSL n p f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (h322 : ¬(n = 3 ∧ p = 2 ∧ f = 2)) (hdvd : ¬ Nat.Coprime 3 (Nat.gcd n (p ^ f - 1)))
    {Y : Type} [Group Y] [Finite Y] (q : Y →* projectiveSL n K) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center Y) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin n) K →* Y, ∀ g, q (ρ g) = proj n K g := by
  classical
  haveI hSLp : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := K) hn).1
  haveI hPp : Group.IsPerfect (projectiveSL n K) :=
    Group.IsPerfect.ofSurjective (proj_surjective n K)
  have hCproj : (proj n K).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [ker_proj]
    exact scalars_le_center n K
  obtain ⟨-, h, hph, -, hhs, hmap, eM, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier
      (proj n K) (proj_surjective n K) hCproj
  set M := hopfMultiplier (projectiveSL n K) with hM
  set N := (h.comp M.subtype).ker with hN
  have hMcard := hopfMultiplier_card_psl hGA hadm hK hn h322 hdvd
  have hkercard : Nat.gcd n (p ^ f - 1) ≤ Nat.card (proj n K).ker := by
    rw [ker_proj, ← hK]
    exact gcd_le_card_scalars (by omega)
  haveI : Finite M := Nat.finite_of_card_ne_zero (by
    rw [hMcard]
    exact (Nat.gcd_pos_of_pos_left _ (by omega)).ne')
  haveI : Finite N := inferInstance
  have hsplit : Nat.card M = Nat.card (M ⧸ N) * Nat.card N := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (N)
    exact this
  have hquot : Nat.card (M ⧸ N) = Nat.card (proj n K).ker := Nat.card_congr eM.toEquiv
  have hN1 : Nat.card N = 1 := by
    have hpos : 0 < Nat.card (proj n K).ker := Nat.card_pos
    have : Nat.card N ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have h2 : Nat.card (proj n K).ker * 2 ≤ Nat.card M := by
        rw [hsplit, hquot]
        exact Nat.mul_le_mul_left _ hgt
      have : Nat.gcd n (p ^ f - 1) * 2 ≤ Nat.card M := le_trans (Nat.mul_le_mul_right 2 hkercard) h2
      rw [hMcard] at this
      have hg0 : 0 < Nat.gcd n (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
      omega
    exact le_antisymm this Nat.card_pos
  have hNbot : N = ⊥ := Subgroup.card_eq_one.1 hN1
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' : hopfCoverMap (projectiveSL n K) u = 1 := by
      rw [← hph, MonoidHom.comp_apply, hu, map_one]
    have hmem : (⟨u, hu'⟩ : M) ∈ N := by
      show h (⟨u, hu'⟩ : M) = 1
      exact hu
    rw [hNbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  let eh : HopfCover (projectiveSL n K) ≃* Matrix.SpecialLinearGroup (Fin n) K :=
    MulEquiv.ofBijective h ⟨hinj, hhs⟩
  refine ⟨(hopfLift q hq hker).comp eh.symm.toMonoidHom, fun g => ?_⟩
  have h1 : q (hopfLift q hq hker (eh.symm g)) = hopfCoverMap (projectiveSL n K) (eh.symm g) :=
    DFunLike.congr_fun (comp_hopfLift q hq hker) (eh.symm g)
  have h2 : proj n K (h (eh.symm g)) = hopfCoverMap (projectiveSL n K) (eh.symm g) :=
    DFunLike.congr_fun hph (eh.symm g)
  have h3 : h (eh.symm g) = g := eh.apply_symm_apply g
  show q (hopfLift q hq hker (eh.symm g)) = proj n K g
  rw [h1, ← h2, h3]

end Hopf

end CFSG.HardMathSupport.Dickson.Sec6.I1431
