module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightB4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightSpGood
import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open Polynomial CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (quasisimple_or_solvable_spSupported)
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

section Generic

variable {G : Type*} [Group G]

theorem lieSEightSpInn_conj_factor {ι : Type*} (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (i₀ : ι) {g : G}
    (hg : g ∈ ⨆ i, A i) : ∃ a ∈ A i₀, ∀ y ∈ A i₀, g * y * g⁻¹ = a * y * a⁻¹ := by
  refine Subgroup.iSup_induction A
    (C := fun g => ∃ a ∈ A i₀, ∀ y ∈ A i₀, g * y * g⁻¹ = a * y * a⁻¹) hg ?_ ?_ ?_
  · intro i g hg
    by_cases hi : i = i₀
    · subst hi
      exact ⟨g, hg, fun y _ => rfl⟩
    · refine ⟨1, (A i₀).one_mem, fun y hy => ?_⟩
      rw [(hc i i₀ hi g hg y hy).eq]
      group
  · exact ⟨1, (A i₀).one_mem, fun y _ => by simp⟩
  · rintro u v ⟨a, ha, hu⟩ ⟨b, hb, hv⟩
    refine ⟨a * b, (A i₀).mul_mem ha hb, fun y hy => ?_⟩
    have e : u * v * y * (u * v)⁻¹ = u * (v * y * v⁻¹) * u⁻¹ := by group
    rw [e, hv y hy, hu _ ((A i₀).mul_mem ((A i₀).mul_mem hb hy) ((A i₀).inv_mem hb))]
    group

theorem lieSEightSpInn_inner_image {T : Type*} [Group T] (π : G →* T) {A : Subgroup G}
    (hA : ⁅A, A⁆ = A) {g a : G} (ha : a ∈ A) (h : ∀ y ∈ A, g * y * g⁻¹ = a * y * a⁻¹) :
    ∃ j ∈ (⁅A, A⁆).map π, ∀ y ∈ (⁅A, A⁆).map π, π g * y * (π g)⁻¹ = j * y * j⁻¹ := by
  rw [hA]
  refine ⟨π a, Subgroup.mem_map_of_mem π ha, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have := congrArg π (h y hy)
  simpa only [map_mul, map_inv] using this

theorem lieSEightSpInn_commutator_eq_top_of_equiv {X Y : Type*} [Group X] [Group Y]
    (φ : X ≃* Y) (hX : commutator X = ⊤) : commutator Y = ⊤ := by
  rw [← lieSEightSp_map_commutator_mulEquiv φ, hX, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 φ.surjective]

theorem lieSEightSpInn_commutator_self_of_equiv {A : Subgroup G} {X : Type*} [Group X]
    (φ : A ≃* X) (hX : commutator X = ⊤) : ⁅A, A⁆ = A := by
  have h1 : commutator ↥A = ⊤ := lieSEightSpInn_commutator_eq_top_of_equiv φ.symm hX
  rw [← Subgroup.map_subtype_commutator A, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Generic

section Blocks

variable {K : Type} [Field K] [Finite K] {r : ℕ} {xt : StatedSp r K}
  {a : StatedProj (StatedSp r K)}

theorem lieSEightSpInn_fixed_perfect (hK : Nat.card K = 8)
    (hsq : Squarefree (minpoly K (spEnd xt))) (blocks : SpPrimaryBlocks 2 3 3 xt a)
    (h : primaryFactors (spEnd xt)) (h1 : (h : K[X]) = X - 1) :
    ⁅spSupported xt {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported xt {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ =
      spSupported xt {(h : K[X]), reciprocalPolynomial (h : K[X])} := by
  classical
  obtain ⟨h0, hm⟩ := h
  change h0 = X - 1 at h1
  subst h1
  dsimp only
  rw [CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
  obtain ⟨φ, -⟩ := blocks.fixedFactor hm
  have : Nontrivial (primaryComponent (spEnd xt) (X - 1)) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
    (B := (spForm r K).restrict (primaryComponent (spEnd xt) (X - 1)))
    (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
  have hs1 : 1 ≤ s := by
    have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd xt) (X - 1))
    omega
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = 8 := by rw [Fintype.card_eq_nat_card, hK]
  have hperf : commutator (StatedSp s K) = ⊤ := by
    by_cases hs2 : s = 1
    · subst hs2
      have hX := slFactorFacts_holds K 2 le_rfl (fun _ => by rw [hcardK]; norm_num)
      exact lieSEightSpInn_commutator_eq_top_of_equiv
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K) hX.perfect
    · have hne : (s, Fintype.card K) ≠ (2, 2) := by
        intro h
        have := congrArg Prod.snd h
        simp only [hcardK] at this
        omega
      exact (spFactorFacts_holds K s (by omega) hne).perfect
  exact lieSEightSpInn_commutator_self_of_equiv (φ.trans e) hperf

theorem lieSEightSpInn_card_ne (hLO : LieOrderBridge) (hK : Nat.card K = 8)
    (blocks : SpPrimaryBlocks 2 3 3 xt a) (h : primaryFactors (spEnd xt))
    (h1 : (h : K[X]) ≠ X - 1)
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported xt {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported xt {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆)
    {J : Subgroup (StatedProj (StatedSp r K))}
    (hJ : J = (⁅spSupported xt {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported xt {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆).map
        (SymplecticFlag.proj r K)) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 1056706560 := by
  classical
  subst hJ
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO] at hQ ⊢
    obtain ⟨d, hdeg, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ⟩ :=
      (blocks.selfDual h h1 hself).exists_half
    have hd : 1 ≤ d := by
      have hpos : 1 ≤ (h : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
      omega
    exact lieSEightSp_gu_card_ne hLO hE (by omega) hHf hHfl e he φ hQ
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    haveI := Fintype.ofFinite (AdjoinRoot (h : K[X]))
    have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hEc : Fintype.card (AdjoinRoot (h : K[X])) = 2 ^ (3 * (h : K[X]).natDegree) := by
      rw [Fintype.card_eq_nat_card, hP.card_field, pow_mul]
    exact lieSEightSp_gl_card_ne hLO (by omega) hEc φ hQ

end Blocks

theorem lieSEightSpInner_holds (hLO : LieOrderBridge) : LieSEightSpInner := by
  classical
  intro K _ _ hK x hx3 hx1 J hJ hT g hg
  haveI : CharP K 2 := lieSEight_charP_two hK
  haveI := Fintype.ofFinite K
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨xt, rfl⟩ := SymplecticHigher.proj_surjective x
  have hZc : (SymplecticFlag.proj 4 K).ker ≤ Subgroup.center (StatedSp 4 K) :=
    lieSEightSp_ker_proj_le_center
  have hinj : ∀ z : StatedSp 4 K, SymplecticFlag.proj 4 K z = 1 → z = 1 := by
    intro z hz
    have h1 : z ∈ (SymplecticFlag.proj 4 K).ker := hz
    rw [SymplecticHigher.ker_proj] at h1
    have h2 := SymplecticHigher.spScalars_le_center h1
    rw [CFSG.HardMathSupport.Dickson.Bal207.center_statedSp_eq_bot_of_charP_two 4] at h2
    exact h2
  have hxt3 : xt ^ 3 = 1 := hinj _ (by rw [map_pow]; exact hx3)
  have hxt1 : xt ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hxo : orderOf xt = 3 := orderOf_eq_prime hxt3 hxt1
  have ha : orderOf (SymplecticFlag.proj 4 K xt) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hxt3, map_one]) hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two (by norm_num)
    hK' Nat.prime_three (by norm_num) (by norm_num) (by norm_num) _ ha).2 xt rfl hxo
  have hlayer := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_sp
    Nat.prime_two (by norm_num) hK' (by norm_num) Nat.prime_three (by norm_num) (by norm_num) xt
    hxt3
  have hJle := hlayer J hJ.1 (glaPComponent_perfect hJ)
  have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ hJle).1
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    omega
  have hsq := (altPrimaryData_spLin hpK hxt3).squarefree
  haveI : Finite (reciprocalOrbits (spEnd xt)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hc : ∀ i j : reciprocalOrbits (spEnd xt), i ≠ j →
      ∀ a ∈ spSupported xt (i : Set K[X]), ∀ b ∈ spSupported xt (j : Set K[X]), Commute a b :=
    fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  obtain ⟨O, hOq, hJO⟩ := components_conj_of_orbit_family (SymplecticFlag.proj 4 K)
    SymplecticHigher.proj_surjective hZc xt
    (fun O : reciprocalOrbits (spEnd xt) => spSupported xt (O : Set K[X])) hc hjoin
    (fun O => quasisimple_or_solvable_spSupported (by norm_num) (by norm_num) hsq blocks O) J hcomp
  have hcardJ := lieSEight_card_quot_center hLO hJ hcomp.2.2 hT
  have hpinj : Function.Injective (SymplecticFlag.proj 4 K) :=
    (injective_iff_map_eq_one _).2 hinj
  obtain ⟨gt, rfl⟩ := SymplecticHigher.proj_surjective g
  have hgt : gt ∈ Subgroup.centralizer ({xt} : Set (StatedSp 4 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact hpinj (by rw [map_mul, map_mul]; exact hg)
  have hgt' : gt ∈ ⨆ O : reciprocalOrbits (spEnd xt), spSupported xt (O : Set K[X]) := by
    rw [hjoin]
    exact hgt
  obtain ⟨b, hbO, hconj⟩ := lieSEightSpInn_conj_factor _ hc O hgt'
  have hperf : ⁅spSupported xt (O : Set K[X]), spSupported xt (O : Set K[X])⁆ =
      spSupported xt (O : Set K[X]) := by
    obtain ⟨O, h, hh, rfl⟩ := O
    by_cases h1 : h = X - 1
    · exact lieSEightSpInn_fixed_perfect hK hsq blocks ⟨h, hh⟩ h1
    · exact absurd hcardJ (lieSEightSpInn_card_ne hLO hK blocks ⟨h, hh⟩ h1 hOq hJO)
  rw [hJO]
  exact lieSEightSpInn_inner_image (SymplecticFlag.proj 4 K) hperf hbO hconj

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
