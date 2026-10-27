module

public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.AscMuTabD4
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
public import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
public import CFSG.ClassicalInvolution.Asc77.WP3SCVConn
public import CFSG.ClassicalInvolution.Asc77.WP3SCVMoved

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.SCV

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

section Transport

variable {K : Type*} [Group K] {Φ : Set (Subgroup K)}

theorem partners_cover_conj (hΦ : ClosedFamily Φ) {R a b : Subgroup K}
    (h : ∀ S ∈ Partners Φ R, S = a ∨ S = b) (g : K) :
    ∀ S ∈ Partners Φ (conjSub g R), S = conjSub g a ∨ S = conjSub g b := by
  intro S hS
  have hS' : conjSub g⁻¹ S ∈ Partners Φ R := by
    refine ⟨hΦ.conj g⁻¹ S hS.1, ?_, ?_⟩
    · intro hEq
      apply hS.2.1
      calc S = conjSub g (conjSub g⁻¹ S) := (conjSub_conjSub_inv g S).symm
        _ = conjSub g R := by rw [hEq]
    · have := hS.2.2.conjSub g⁻¹
      rwa [conjSub_inv_conjSub] at this
  have hS'' : S = conjSub g (conjSub g⁻¹ S) := (conjSub_conjSub_inv g S).symm
  rcases h _ hS' with h1 | h1
  · left
    rw [hS'', h1]
  · right
    rw [hS'', h1]

end Transport

section Moved

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

theorem zt_z'_mem (hs : ChainFrameSetting p f Ω K J K' z t z') :
    z' ∈ Subgroup.centralizer ({z * t} : Set G) :=
  zt_le_centralizer hs (Subgroup.subset_closure (by simp))

theorem moved_data (hs : ChainFrameSetting p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hmov : MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
      (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range)
    (hj : D.tag j ≠ .trialityD4) :
    ∃ (R_K R_J : Subgroup (compModel D j).K) (r_K r_J : (compModel D j).K),
      R_K ∈ fundamentalSubgroups (D.tag j) (compModel D j).D ∧
      R_J ∈ fundamentalSubgroups (D.tag j) (compModel D j).D ∧
      R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
        modOdd (z * t) (exactCore (z * t) K) ∧
      R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
        modOdd (z * t) (exactCore (z * t) J) ∧
      r_K ∈ R_K ∧ (∀ s ∈ R_K, r_K * s = s * r_K) ∧ r_K ≠ 1 ∧
      r_J ∈ R_J ∧ (∀ s ∈ R_J, r_J * s = s * r_J) ∧ r_J ≠ 1 ∧
      secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j r_K =
        oddQuotMk (z * t) ⟨z, zt_z_mem hs⟩ ∧
      secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j r_J =
        oddQuotMk (z * t) ⟨t, zt_t_mem hs⟩ ∧
      r_K * r_J ∈ Subgroup.center (compModel D j).K ∧ R_K ≠ R_J := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  have hzC := zt_z_mem hs
  have htC := zt_t_mem hs
  have hcC := zt_zt_mem z t
  have hzt : z * t = t * z := hfd.comm_zt hp hΩ
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  have hKmem := zt_memK hs
  have hJmem := zt_memJ hs
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  obtain ⟨R_K, R_J, hR_K, hR_J, hmodK, hmodJ⟩ := moved_contains_KJ hs D j hmov
  obtain ⟨r_K, hrK, hrKc, hrK1, hrKbar⟩ := V.exists_central_lift hKmem hKcl j hj hR_K hmodK.symm
  obtain ⟨r_J, hrJ, hrJc, hrJ1, hrJbar⟩ := V.exists_central_lift hJmem hJcl j hj hR_J hmodJ.symm
  have hKperf : Group.IsPerfect (compModel D j).K :=
    ⟨(CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (D.isFundTag j)
      (D.admissible j)).1.1⟩
  have hrKbar' : oddQuotMk (z * t) ⟨z, hzC⟩ = V.psi j r_K := hrKbar
  have hrJbar' : oddQuotMk (z * t) ⟨t, htC⟩ = V.psi j r_J := hrJbar
  have hcc : V.psi j (r_K * r_J) = oddQuotMk (z * t) ⟨z * t, hcC⟩ := by
    rw [map_mul, ← hrKbar', ← hrJbar', ← map_mul]
    rfl
  have hcenKJ : r_K * r_J ∈ Subgroup.center (compModel D j).K := by
    refine FrameVertex.mem_center_of_commutators_central fun y => ?_
    apply V.psi_ker j
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcc]
    have h1 := oddQuotMk_central hcC (V.psi j y)
    calc oddQuotMk (z * t) ⟨z * t, hcC⟩ * V.psi j y * (oddQuotMk (z * t) ⟨z * t, hcC⟩)⁻¹ *
          (V.psi j y)⁻¹
        = (V.psi j y * oddQuotMk (z * t) ⟨z * t, hcC⟩) * (oddQuotMk (z * t) ⟨z * t, hcC⟩)⁻¹ *
          (V.psi j y)⁻¹ := by rw [h1]
      _ = 1 := by group
  have hKJ : R_K ≠ R_J := by
    intro hRR
    have hU1 := V.isUniqueInvolution_modOdd hKmem hKcl
    have hU2 := V.isUniqueInvolution_modOdd hJmem hJcl
    have himg : modOdd (z * t) (exactCore (z * t) K) = modOdd (z * t) (exactCore (z * t) J) := by
      rw [← hmodK, ← hmodJ, hRR]
    rw [himg] at hU1
    have heq := hU1.eq hU2
    exact hfd.t_ne_z hp hq hΩ (eq_of_oddQuotMk_eq' htC hzC
      (isCentralInvolution_of_isClassicalMember hJcl).sq
      (isCentralInvolution_of_isClassicalMember hKcl).sq hzt.symm heq.symm)
  exact ⟨R_K, R_J, r_K, r_J, hR_K, hR_J, hmodK, hmodJ, hrK, hrKc, hrK1, hrJ, hrJc, hrJ1,
    hrKbar'.symm, hrJbar'.symm, hcenKJ, hKJ⟩

theorem sq_eq_one_of_central_sl2 {M : Type} [Group M] {F : Type} [Field F] {R : Subgroup M}
    (ε : R ≃* SL(2, F)) {r : M} (hr : r ∈ R) (hrc : ∀ s ∈ R, r * s = s * r) : r * r = 1 := by
  have hcen : ε ⟨r, hr⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, rfl⟩ := ε.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hrc s.1 s.2).symm
  obtain ⟨c, hc, hcs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  have hc2 : c * c = 1 := by simpa [pow_two] using hc
  have hsq : ((ε ⟨r, hr⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      ((ε ⟨r, hr⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← hcs, ← map_mul, hc2, map_one]
  have h1 : ε ⟨r, hr⟩ * ε ⟨r, hr⟩ = 1 :=
    Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using hsq)
  have h2 : ε (⟨r, hr⟩ * ⟨r, hr⟩) = ε 1 := by rw [map_mul, map_one]; exact h1
  exact congrArg Subtype.val (ε.injective h2)

theorem fund_central_sq (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t))
    (j : Fin D.card) (hp : p ≠ 2) (hG2 : D.tag j ≠ .G2) (hD4 : D.tag j ≠ .trialityD4)
    {R : Subgroup (compModel D j).K} {r : (compModel D j).K}
    (hR : R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) (hr : r ∈ R)
    (hrc : ∀ s ∈ R, r * s = s * r) : r * r = 1 := by
  obtain ⟨ε⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp (D.isFundTag j)
    (D.admissible j) hG2 hD4 hR
  exact sq_eq_one_of_central_sl2 ε hr hrc

theorem moved_commutes (hs : ChainFrameSetting p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hG2 : D.tag j ≠ .G2) (hD4 : D.tag j ≠ .trialityD4)
    {R_K R_J : Subgroup (compModel D j).K} {r_K r_J : (compModel D j).K}
    (hR_K : R_K ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hR_J : R_J ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hmodJ : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) J))
    (hrK : r_K ∈ R_K) (hrKc : ∀ s ∈ R_K, r_K * s = s * r_K) (hrK1 : r_K ≠ 1)
    (hrJ : r_J ∈ R_J) (hrJc : ∀ s ∈ R_J, r_J * s = s * r_J) (hrJ1 : r_J ≠ 1)
    (hrKb : secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j r_K =
      oddQuotMk (z * t) ⟨z, zt_z_mem hs⟩)
    (hcen : r_K * r_J ∈ Subgroup.center (compModel D j).K) (hKJ : R_K ≠ R_J) :
    Commutes R_K R_J := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  have hzC := zt_z_mem hs
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  have hker : (V.psi j).ker ≤ Subgroup.center (compModel D j).K := V.psi_ker j
  have hq5 : 5 ≤ p ^ D.exp j := by rw [V.exp_eq j hD4]; exact hq
  have hperf : ∀ S ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, S ≤ ⁅S, S⁆ :=
    fun S hS => (V.fund_perfect j hD4 hS).ge
  have hord : ∀ {R : Subgroup (compModel D j).K} {r : (compModel D j).K},
      R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D → r ∈ R → (∀ s ∈ R, r * s = s * r) →
      r ≠ 1 → orderOf r = 2 := by
    intro R r hR hr hrc hr1
    exact orderOf_eq_prime (by rw [pow_two]; exact fund_central_sq D j hp hG2 hD4 hR hr hrc) hr1
  have hlong : ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      R ∈ ModelFacts.longestFundamental (compModel D j).D := fun R hR =>
    ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR
  have hcommr : r_K * r_J = r_J * r_K := by
    have h1 : (r_K * r_J) * r_K = r_K * (r_K * r_J) := (Subgroup.mem_center_iff.mp hcen r_K).symm
    have h2 : r_K * (r_J * r_K) = r_K * (r_K * r_J) := by rw [← mul_assoc]; exact h1
    exact (mul_left_cancel h2).symm
  have hdich := ih8_stdDichotomy (D.isFundTag j) hG2 hD4 (D.admissible j)
  have hmapc := hdich.map_of_commute hp hq5 (V.psi j) hker (hlong R_K hR_K) (hlong R_J hR_J)
    hrK hrJ (hord hR_K hrK hrKc hrK1) (hord hR_J hrJ hrJc hrJ1) hcommr
  have hz2 : z * z = 1 := hfd.hz.sq
  have hz1 : oddQuotMk (z * t) ⟨z, hzC⟩ ≠ 1 := by
    intro h
    have h1 : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) = 1 :=
      eq_one_of_oddQuotMk_eq_one (Subtype.ext hz2) h
    exact hfd.hz.ne_one (congrArg Subtype.val h1)
  have hzR : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ R_K.map (V.psi j) := ⟨r_K, hrK, hrKb⟩
  have hquasiJ : CFSG.Open.IsQuasisimple ↥(modOdd (z * t) (exactCore (z * t) J)) := by
    have h1 : R_J.map (V.psi j) = modOdd (z * t) (exactCore (z * t) J) := hmodJ
    rw [← h1]
    exact isQuasisimple_map_of_ker_le_center _ hker
      (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (V.four_le j hD4) R_J hR_J)
  have hzJ := oddQuotMk_centralizes_modOdd_exactCore hJcl (zt_hc2 hs) (zt_tq_J hs)
    (hfd.tq_z_J hp hq hΩ) hzC hquasiJ
  have hcentJ : ∀ y ∈ R_J.map (V.psi j),
      oddQuotMk (z * t) ⟨z, hzC⟩ * y = y * oddQuotMk (z * t) ⟨z, hzC⟩ := by
    intro y hy
    have h1 : R_J.map (V.psi j) = modOdd (z * t) (exactCore (z * t) J) := hmodJ
    rw [h1] at hy
    exact hzJ y hy
  have hF : 4 ≤ Nat.card (GaloisField p (D.exp j)) := by
    rw [GaloisField.card p (D.exp j) (by have := (D.admissible j).2.1; omega)]
    omega
  rcases hmapc with h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact absurd (ih8_eq_of_map_eq (V.psi j) hker (hperf R_K hR_K) (hperf R_J hR_J) h) hKJ
  · exact ih8_commutes_of_commutes_map (V.psi j) hker (hperf R_K hR_K) h
  · exact absurd (CFSG.ClassicalInvolution.Asc77.LinearBlockStandardPair.eq_one_of_centralizes hF hW
      hzR hcentJ) hz1
  · exact absurd (CFSG.ClassicalInvolution.Asc77.UnitaryBlockStandardPair.eq_one_of_centralizes
      (CFSG.LieType.Universal.card_galoisField_two_mul p (D.exp j) (D.admissible j).2.1) hq5 hW hzR
      hcentJ) hz1

theorem zt_z_ne (hs : ChainFrameSetting p f Ω K J K' z t z') : z ≠ z * t := fun h1 =>
  hs.frame.ht.ne_one (mul_left_cancel (a := z) (b := t) (c := 1) (by rw [mul_one]; exact h1.symm))

theorem z'_data (hs : ChainFrameSetting p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hmov : MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
      (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range)
    (hj : D.tag j ≠ .trialityD4) {R_K : Subgroup (compModel D j).K}
    (hR_K : R_K ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hmodK : R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) K)) :
    oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ ∈ Subgroup.normalizer
        ((secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range :
          Set (OddQuot (z * t))) ∧
      oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ * oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ = 1 ∧
      ∀ s ∈ R_K, oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ *
          secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j s =
        secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j s *
          oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  set B : Subgroup G := Subgroup.closure ({z, t, z'} : Set G) with hB
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have htB : t ∈ B := Subgroup.subset_closure (by simp)
  have hz'B : z' ∈ B := Subgroup.subset_closure (by simp)
  have hztB : z * t ∈ B := Subgroup.mul_mem _ hzB htB
  have hBel : IsElemAbelian 2 B := hfd.isElemAbelian hp hΩ
  have hne1 : z * t ≠ 1 := zt_ne_one hs
  have hz'C := zt_z'_mem hs
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  have hnc : ¬ ({z * t} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hs.nonabelian hne1
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  have hQ : CFSG.IsComponent (V.psi j).range := V.isComponent_range j
  have hmov' : MovedByAll B (z * t) (V.psi j).range := hmov
  have hBN := FrameVertex.modOdd_le_normalizer hp hq hΩ.conjInvariant hΩ.classical hs.below
    (zt_hc2 hs) hnc hBel hztB hne1 hzB hfd.hz.ne_one (zt_z_ne hs) (zt_memK hs) hKcl hQ hmov'
  refine ⟨hBN (oddQuotMk_mem_modOdd hz'B hz'C), ?_, ?_⟩
  · rw [← map_mul]
    have : (⟨z', hz'C⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) * ⟨z', hz'C⟩ = 1 :=
      Subtype.ext hfd.hz'.sq
    rw [this, map_one]
  · intro s hs'
    have hquasiK : CFSG.Open.IsQuasisimple ↥(modOdd (z * t) (exactCore (z * t) K)) := by
      have h1 : R_K.map (V.psi j) = modOdd (z * t) (exactCore (z * t) K) := hmodK
      rw [← h1]
      exact isQuasisimple_map_of_ker_le_center _ (V.psi_ker j)
        (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (V.four_le j hj) R_K hR_K)
    have hz'K := oddQuotMk_centralizes_modOdd_exactCore hKcl (zt_hc2 hs) (zt_tq_K hs)
      (hfd.tq_z' hp hq hΩ) hz'C hquasiK
    apply hz'K
    have h1 : R_K.map (V.psi j) = modOdd (z * t) (exactCore (z * t) K) := hmodK
    rw [← h1]
    exact ⟨s, hs', rfl⟩

theorem false_of_z'_centralizes_J (hs : ChainFrameSetting p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    {R_J : Subgroup (compModel D j).K}
    (hmodJ : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) J))
    (hv : ∀ s ∈ R_J, oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ *
          secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j s =
        secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j s *
          oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩) : False := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  have hz'N : z' ∈ Subgroup.normalizer (J : Set G) :=
    mem_normalizer_of_commutes_involution hΩ.conjInvariant hs.noTwins hfd.memJ hfd.ht
      hfd.htz'.symm
  have hz'J : z' ∈ trivialOnQuot J := by
    refine mem_trivialOnQuot_of_centralizes_modOdd hJcl (zt_hc2 hs) (zt_tq_J hs) (zt_z'_mem hs)
      hz'N ?_
    intro y hy
    have h1 : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
        modOdd (z * t) (exactCore (z * t) J) := hmodJ
    rw [← h1] at hy
    obtain ⟨s, hs', rfl⟩ := hy
    exact hv s hs'
  have hKJne : J ≠ K' := by
    intro h1
    apply hfd.z'_ne_t hΩ
    have h2 : IsUniqueInvolution J z' := by rw [h1]; exact hfd.hz'
    exact h2.eq hfd.ht
  have hJK' : J ∈ omegaNbr Ω K' :=
    mem_omegaNbr_of_trivialOnQuot hp hq hΩ hfd.memK' hfd.hz' hfd.memJ hKJne hz'J
  exact hfd.hperp (Set.mem_insert_of_mem _
    (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hfd.memK' hfd.memJ hJK'))

theorem false_of_d4 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ} (ht : t = .POmegaPlus)
    (hn : n = 4) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e Fact.out).K} (hR : R ∈ ModelFund p t n e)
    (hb : ∃ a b : Subgroup (modelUniv t n p e Fact.out).K,
      ∀ S ∈ Partners (ModelFund p t n e) R, S = a ∨ S = b) : False := by
  subst ht
  subst hn
  obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, -, -, -, -⟩ :=
    MuTab.clique_plus hp2 hq hadm hR
  exact false_of_three_partners hb ⟨h₂, Ne.symm n12, c12⟩ ⟨h₃, Ne.symm n13, c13⟩
    ⟨h₄, Ne.symm n14, c14⟩ n23 n24 n34

end Moved

end CFSG.ClassicalInvolution.Asc77.SCV
