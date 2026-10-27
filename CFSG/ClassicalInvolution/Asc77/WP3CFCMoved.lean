module

public import CFSG.ClassicalInvolution.Asc77.WP3CFCCore
public import CFSG.ClassicalInvolution.Asc77.WP3SCUVCtx
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
import CFSG.ClassicalInvolution.RouteD.NoG2D4Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CFC

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77

section Moved

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}


theorem zt_sq (hs : ChainFrameCore p f Ω K J K' z t z') :
    (z * t) * (z * t) = 1 := by
  have hz2 : z * z = 1 := hs.frame.hz.sq
  have ht2 : t * t = 1 := hs.frame.ht.sq
  have hzt : z * t = t * z := hs.frame.comm_zt hs.odd hs.hyp
  calc (z * t) * (z * t) = z * (t * z) * t := by group
    _ = z * (z * t) * t := by rw [← hzt]
    _ = (z * z) * (t * t) := by group
    _ = 1 := by rw [hz2, ht2, one_mul]

theorem zt_ne_one (hs : ChainFrameCore p f Ω K J K' z t z') : z * t ≠ 1 := by
  intro h1
  have h2 : z = t⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [inv_eq_of_mul_eq_one_right hs.frame.ht.sq] at h2
  exact hs.frame.t_ne_z hs.odd hs.five hs.hyp h2.symm

theorem zt_hc2 (hs : ChainFrameCore p f Ω K J K' z t z') :
    IsPGroup 2 (Subgroup.zpowers (z * t)) :=
  isPGroup_zpowers_of_sq_eq_one (zt_sq hs)

theorem zt_tq_K (hs : ChainFrameCore p f Ω K J K' z t z') : z * t ∈ trivialOnQuot K := by
  have hB : z * t ∈ Subgroup.closure ({z, t, z'} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  exact hs.frame.tq_B hs.odd hs.five hs.hyp hB

theorem zt_tq_J (hs : ChainFrameCore p f Ω K J K' z t z') : z * t ∈ trivialOnQuot J :=
  Subgroup.mul_mem _ (hs.frame.tq_z_J hs.odd hs.five hs.hyp)
    (trivialOnQuot_of_isUniqueInvolution hs.odd hs.five hs.hyp hs.frame.memJ hs.frame.ht)

theorem zt_memK (hs : ChainFrameCore p f Ω K J K' z t z') : K ∈ tqMembers Ω (z * t) :=
  mem_tqMembers_iff.mpr ⟨hs.frame.mem, zt_tq_K hs⟩

theorem zt_memJ (hs : ChainFrameCore p f Ω K J K' z t z') : J ∈ tqMembers Ω (z * t) :=
  mem_tqMembers_iff.mpr ⟨hs.frame.memJ, zt_tq_J hs⟩

noncomputable abbrev ztVertex (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) : VertexCtx p f Ω (z * t) :=
  ⟨hs.hyp, hs.odd, hs.five, zt_hc2 hs, ⟨K, zt_memK hs⟩, D⟩

theorem zt_le_centralizer (hs : ChainFrameCore p f Ω K J K' z t z') :
    Subgroup.closure ({z, t, z'} : Set G) ≤ Subgroup.centralizer ({z * t} : Set G) := by
  have hztB : z * t ∈ Subgroup.closure ({z, t, z'} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  exact Lemma52Proof.le_centralizer_of_mem (hs.frame.isElemAbelian hs.odd hs.hyp) hztB

theorem zt_z_mem (hs : ChainFrameCore p f Ω K J K' z t z') :
    z ∈ Subgroup.centralizer ({z * t} : Set G) :=
  zt_le_centralizer hs (Subgroup.subset_closure (by simp))

theorem zt_t_mem (hs : ChainFrameCore p f Ω K J K' z t z') :
    t ∈ Subgroup.centralizer ({z * t} : Set G) :=
  zt_le_centralizer hs (Subgroup.subset_closure (by simp))

theorem zt_zt_mem (z t : G) : z * t ∈ Subgroup.centralizer ({z * t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem zt_z'_mem (hs : ChainFrameCore p f Ω K J K' z t z') :
    z' ∈ Subgroup.centralizer ({z * t} : Set G) :=
  zt_le_centralizer hs (Subgroup.subset_closure (by simp))

theorem zt_z_ne (hs : ChainFrameCore p f Ω K J K' z t z') : z ≠ z * t := fun h1 =>
  hs.frame.ht.ne_one (mul_left_cancel (a := z) (b := t) (c := 1) (by rw [mul_one]; exact h1.symm))

theorem zt_t_eq (hs : ChainFrameCore p f Ω K J K' z t z') : t = z * (z * t) := by
  have hz2 : z * z = 1 := hs.frame.hz.sq
  rw [← mul_assoc, hz2, one_mul]

theorem moved_contains_KJ (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hmov : MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
      (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range) :
    ∃ R_K R_J : Subgroup (compModel D j).K,
      R_K ∈ fundamentalSubgroups (D.tag j) (compModel D j).D ∧
      R_J ∈ fundamentalSubgroups (D.tag j) (compModel D j).D ∧
      R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
        modOdd (z * t) (exactCore (z * t) K) ∧
      R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
        modOdd (z * t) (exactCore (z * t) J) := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  set B : Subgroup G := Subgroup.closure ({z, t, z'} : Set G) with hB
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have htB : t ∈ B := Subgroup.subset_closure (by simp)
  have hztB : z * t ∈ B := Subgroup.mul_mem _ hzB htB
  have hBel : IsElemAbelian 2 B := hfd.isElemAbelian hp hΩ
  have hne1 : z * t ≠ 1 := zt_ne_one hs
  have hzne : z ≠ z * t := fun h1 =>
    hfd.ht.ne_one (mul_left_cancel (a := z) (b := t) (c := 1) (by rw [mul_one]; exact h1.symm))
  have htne : t ≠ z * t := fun h1 =>
    hfd.hz.ne_one (mul_right_cancel (a := z) (b := t) (c := 1) (by rw [one_mul]; exact h1.symm))
  have hBC := zt_le_centralizer hs
  have hzC : z ∈ Subgroup.centralizer ({z * t} : Set G) := hBC hzB
  have htC : t ∈ Subgroup.centralizer ({z * t} : Set G) := hBC htB
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  have hKmem := zt_memK hs
  have hJmem := zt_memJ hs
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  have hmov' : MovedByAll B (z * t) (V.psi j).range := hmov
  have hnot_z : oddQuotMk (z * t) ⟨z, hzC⟩ ∉ modOdd (z * t) (Subgroup.zpowers (z * t)) :=
    Lemma52Proof.oddQuotMk_not_mem_zpowers hBel hztB hne1 hzB hfd.hz.ne_one hzne hzC
  have hnot_t : oddQuotMk (z * t) ⟨t, htC⟩ ∉ modOdd (z * t) (Subgroup.zpowers (z * t)) :=
    Lemma52Proof.oddQuotMk_not_mem_zpowers hBel hztB hne1 htB hfd.ht.ne_one htne htC
  obtain ⟨jK, R_K, hR_K, hmodK⟩ := V.exists_fund_of_mem hKmem
  obtain ⟨jJ, R_J, hR_J, hmodJ⟩ := V.exists_fund_of_mem hJmem
  have hjK : jK = j := by
    by_contra hne
    have hzmod : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ modOdd (z * t) (exactCore (z * t) K) :=
      oddQuotMk_mem_modOdd (V.involution_mem_exactCore hKmem hKcl) hzC
    rw [← hmodK] at hzmod
    obtain ⟨r, -, hrz⟩ := hzmod
    obtain ⟨y, hy, hxy⟩ := hmov' _ (oddQuotMk_mem_modOdd hzB hzC) hnot_z
    obtain ⟨s, rfl⟩ := hy
    apply hxy
    rw [← hrz]
    exact V.psi_commute hne r s
  have hjJ : jJ = j := by
    by_contra hne
    have htmod : oddQuotMk (z * t) ⟨t, htC⟩ ∈ modOdd (z * t) (exactCore (z * t) J) :=
      oddQuotMk_mem_modOdd (V.involution_mem_exactCore hJmem hJcl) htC
    rw [← hmodJ] at htmod
    obtain ⟨r, -, hrt⟩ := htmod
    obtain ⟨y, hy, hxy⟩ := hmov' _ (oddQuotMk_mem_modOdd htB htC) hnot_t
    obtain ⟨s, rfl⟩ := hy
    apply hxy
    rw [← hrt]
    exact V.psi_commute hne r s
  subst jK jJ
  exact ⟨R_K, R_J, hR_K, hR_J, hmodK, hmodJ⟩

theorem exists_central_product (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    {R_K R_J : Subgroup (compModel D j).K}
    (hmodK : R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) K))
    (hmodJ : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) J)) :
    ∃ r_K ∈ R_K, ∃ r_J ∈ R_J,
      secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j r_K =
        oddQuotMk (z * t) ⟨z, zt_z_mem hs⟩ ∧
      secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j r_J =
        oddQuotMk (z * t) ⟨t, zt_t_mem hs⟩ ∧
      r_K * r_J ∈ Subgroup.center (compModel D j).K := by
  have hΩ := hs.hyp
  have hfd := hs.frame
  have hBC := zt_le_centralizer hs
  have hzC : z ∈ Subgroup.centralizer ({z * t} : Set G) := hBC (Subgroup.subset_closure (by simp))
  have htC : t ∈ Subgroup.centralizer ({z * t} : Set G) := hBC (Subgroup.subset_closure (by simp))
  have hcC : z * t ∈ Subgroup.centralizer ({z * t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  set ψ := secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j with hψ
  have hker : ψ.ker ≤ Subgroup.center (compModel D j).K := V.psi_ker j
  have hzb : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ R_K.map ψ := by
    rw [hmodK]
    exact oddQuotMk_mem_modOdd (V.involution_mem_exactCore (zt_memK hs) hKcl) hzC
  have htb : oddQuotMk (z * t) ⟨t, htC⟩ ∈ R_J.map ψ := by
    rw [hmodJ]
    exact oddQuotMk_mem_modOdd (V.involution_mem_exactCore (zt_memJ hs) hJcl) htC
  obtain ⟨r_K, hrK, hrKz⟩ := hzb
  obtain ⟨r_J, hrJ, hrJt⟩ := htb
  refine ⟨r_K, hrK, r_J, hrJ, hrKz, hrJt, ?_⟩
  have hcc : ψ (r_K * r_J) = oddQuotMk (z * t) ⟨z * t, hcC⟩ := by
    rw [map_mul, hrKz, hrJt, ← map_mul]
    rfl
  have hKperf : Group.IsPerfect (compModel D j).K :=
    ⟨(CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (D.isFundTag j)
      (D.admissible j)).1.1⟩
  refine FrameVertex.mem_center_of_commutators_central fun y => ?_
  apply hker
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcc]
  have h1 := oddQuotMk_central hcC (ψ y)
  calc oddQuotMk (z * t) ⟨z * t, hcC⟩ * ψ y * (oddQuotMk (z * t) ⟨z * t, hcC⟩)⁻¹ *
        (ψ y)⁻¹
      = (ψ y * oddQuotMk (z * t) ⟨z * t, hcC⟩) * (oddQuotMk (z * t) ⟨z * t, hcC⟩)⁻¹ *
        (ψ y)⁻¹ := by rw [h1]
    _ = 1 := by group

theorem false_of_exotic (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hmov : MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
      (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range)
    (ht : D.tag j = .G2 ∨ D.tag j = .trialityD4) : False := by
  obtain ⟨R_K, R_J, hR_K, hR_J, hmodK, hmodJ⟩ := moved_contains_KJ hs D j hmov
  obtain ⟨r_K, hrK, r_J, hrJ, hrKz, hrJt, hcen⟩ := exists_central_product hs D j hmodK hmodJ
  have hZ : Subgroup.center (compModel D j).K = ⊥ :=
    CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hs.odd ht (D.rank j)
      (D.admissible j).2.1
  rw [hZ, Subgroup.mem_bot] at hcen
  have hBC := zt_le_centralizer hs
  have hzC : z ∈ Subgroup.centralizer ({z * t} : Set G) := hBC (Subgroup.subset_closure (by simp))
  have htC : t ∈ Subgroup.centralizer ({z * t} : Set G) := hBC (Subgroup.subset_closure (by simp))
  have hcC : z * t ∈ Subgroup.centralizer ({z * t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have h1 : oddQuotMk (z * t) ⟨z * t, hcC⟩ = 1 := by
    have : oddQuotMk (z * t) ⟨z, hzC⟩ * oddQuotMk (z * t) ⟨t, htC⟩ = 1 := by
      rw [← hrKz, ← hrJt, ← map_mul, hcen, map_one]
    rw [← this, ← map_mul]
    rfl
  have h2 : (⟨z * t, hcC⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) = 1 :=
    eq_one_of_oddQuotMk_eq_one (Subtype.ext (zt_sq hs)) h1
  exact zt_ne_one hs (congrArg Subtype.val h2)

theorem moved_data (hs : ChainFrameCore p f Ω K J K' z t z')
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

end Moved

end CFSG.ClassicalInvolution.Asc77.CFC
