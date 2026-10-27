module

public import CFSG.ClassicalInvolution.Asc77.WP3CFCCore
public import CFSG.ClassicalInvolution.Asc77.WP3SCUVCtx
public import CFSG.ClassicalInvolution.Asc77.WP3SCUVertex
public import CFSG.ClassicalInvolution.Asc77.WP3SCUModel4U
public import CFSG.ClassicalInvolution.Asc77.WP3SCURank
public import CFSG.ClassicalInvolution.Asc77.WP3SCUNG
import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootCtx
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CFC

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77

section Position

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}


theorem toralActionDiag_zt
    (hU : ∀ n e : ℕ, p ≠ 2 → 5 ≤ p ^ e → RankFourFacts .PSU n p e)
    (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hmov : MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
      (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range)
    (htag : D.tag j = .PSL ∨ D.tag j = .PSU) :
    ToralActionDiag 2 (D.tag j) (D.rank j) p (D.exp j) Fact.out
      (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j)
      (modOdd (z * t) (Subgroup.closure ({z, t, z'} : Set G))) := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  have hT := hs.noTwins
  have hj : D.tag j ≠ .trialityD4 := by rcases htag with h | h <;> rw [h] <;> decide
  set B : Subgroup G := Subgroup.closure ({z, t, z'} : Set G) with hB
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have htB : t ∈ B := Subgroup.subset_closure (by simp)
  have hz'B : z' ∈ B := Subgroup.subset_closure (by simp)
  have hztB : z * t ∈ B := Subgroup.mul_mem _ hzB htB
  have hBel : IsElemAbelian 2 B := hfd.isElemAbelian hp hΩ
  have hz2 : z * z = 1 := hfd.hz.sq
  have ht2 : t * t = 1 := hfd.ht.sq
  have hz'2 : z' * z' = 1 := hfd.hz'.sq
  have hzt : z * t = t * z := hfd.comm_zt hp hΩ
  have hsq : (z * t) * (z * t) = 1 := by
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [← hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2, one_mul]
  have hne1 : z * t ≠ 1 := by
    intro h1
    have h2 : z = t⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right ht2] at h2
    exact hfd.t_ne_z hp hq hΩ h2.symm
  have hzne : z ≠ z * t := fun h1 =>
    hfd.ht.ne_one (mul_left_cancel (a := z) (b := t) (c := 1) (by rw [mul_one]; exact h1.symm))
  have htne : t ≠ z * t := fun h1 =>
    hfd.hz.ne_one (mul_right_cancel (a := z) (b := t) (c := 1) (by rw [one_mul]; exact h1.symm))
  have hc2 : IsPGroup 2 (Subgroup.zpowers (z * t)) := isPGroup_zpowers_of_sq_eq_one hsq
  have hBC : B ≤ Subgroup.centralizer ({z * t} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hBel hztB
  have hzC : z ∈ Subgroup.centralizer ({z * t} : Set G) := hBC hzB
  have htC : t ∈ Subgroup.centralizer ({z * t} : Set G) := hBC htB
  have hz'C : z' ∈ Subgroup.centralizer ({z * t} : Set G) := hBC hz'B
  have hcC : z * t ∈ Subgroup.centralizer ({z * t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  have hcK : z * t ∈ trivialOnQuot K := hfd.tq_B hp hq hΩ hztB
  have hcJ : z * t ∈ trivialOnQuot J :=
    Subgroup.mul_mem _ (hfd.tq_z_J hp hq hΩ)
      (trivialOnQuot_of_isUniqueInvolution hp hq hΩ hfd.memJ hfd.ht)
  have hKmem : K ∈ tqMembers Ω (z * t) := mem_tqMembers_iff.mpr ⟨hfd.mem, hcK⟩
  have hJmem : J ∈ tqMembers Ω (z * t) := mem_tqMembers_iff.mpr ⟨hfd.memJ, hcJ⟩
  let V : VertexCtx p f Ω (z * t) := ⟨hΩ, hp, hq, hc2, ⟨K, hKmem⟩, D⟩
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
  have hquasiK : CFSG.Open.IsQuasisimple ↥(modOdd (z * t) (exactCore (z * t) K)) := by
    rw [← hmodK]
    exact isQuasisimple_map_of_ker_le_center _ (V.psi_ker j)
      (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (V.four_le j hj) R_K hR_K)
  have hquasiJ : CFSG.Open.IsQuasisimple ↥(modOdd (z * t) (exactCore (z * t) J)) := by
    rw [← hmodJ]
    exact isQuasisimple_map_of_ker_le_center _ (V.psi_ker j)
      (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (V.four_le j hj) R_J hR_J)
  obtain ⟨r_K, hrK, hrKc, hrK1, hrKbar⟩ := V.exists_central_lift hKmem hKcl j hj hR_K hmodK.symm
  obtain ⟨r_J, hrJ, hrJc, hrJ1, hrJbar⟩ := V.exists_central_lift hJmem hJcl j hj hR_J hmodJ.symm
  have hrKbar' : oddQuotMk (z * t) ⟨z, hzC⟩ = V.psi j r_K := hrKbar
  have hrJbar' : oddQuotMk (z * t) ⟨t, htC⟩ = V.psi j r_J := hrJbar
  have htK := oddQuotMk_centralizes_modOdd_exactCore hKcl hc2 hcK (hfd.tq_t hp hq hΩ) htC hquasiK
  have hz'K := oddQuotMk_centralizes_modOdd_exactCore hKcl hc2 hcK (hfd.tq_z' hp hq hΩ) hz'C
    hquasiK
  have hcenJ : ∀ s ∈ R_K, r_J * s * r_J⁻¹ * s⁻¹ ∈ Subgroup.center (compModel D j).K := by
    intro s hs
    apply V.psi_ker j
    rw [MonoidHom.mem_ker]
    have hsmem : V.psi j s ∈ modOdd (z * t) (exactCore (z * t) K) := by
      rw [← hmodK]; exact ⟨s, hs, rfl⟩
    have h1 := htK _ hsmem
    rw [hrJbar'] at h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  have hKJ : R_K ≠ R_J := by
    intro hRR
    have hU1 := V.isUniqueInvolution_modOdd hKmem hKcl
    have hU2 := V.isUniqueInvolution_modOdd hJmem hJcl
    have himg : modOdd (z * t) (exactCore (z * t) K) = modOdd (z * t) (exactCore (z * t) J) := by
      rw [← hmodK, ← hmodJ, hRR]
    rw [himg] at hU1
    have heq := hU1.eq hU2
    exact hfd.t_ne_z hp hq hΩ (eq_of_oddQuotMk_eq' htC hzC (isCentralInvolution_of_isClassicalMember
      hJcl).sq (isCentralInvolution_of_isClassicalMember hKcl).sq hzt.symm heq.symm)
  have hcc : V.psi j (r_K * r_J) = oddQuotMk (z * t) ⟨z * t, hcC⟩ := by
    rw [map_mul, ← hrKbar', ← hrJbar', ← map_mul]
    rfl
  have hKperf : Group.IsPerfect (compModel D j).K :=
    ⟨(CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (D.isFundTag j)
      (D.admissible j)).1.1⟩
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
  have hrank : D.rank j = 4 := by
    have he : D.exp j = f := V.exp_eq j hj
    have hcp : CentralPairRank (D.tag j) (D.rank j) p (D.exp j) := by
      rcases htag with h | h
      · rw [h]; exact centralPairRank_psl hp _
      · rw [h]; exact centralPairRank_psu hp (by rw [he]; exact hq) _
    exact hcp (D.admissible j) hR_K hR_J hKJ hrK hrKc hrK1 hrJ hrJc hrJ1 hcenKJ
  have hF : RankFourFacts (D.tag j) (D.rank j) p (D.exp j) := by
    have he : D.exp j = f := V.exp_eq j hj
    rcases htag with h | h
    · rw [h]; exact rankFourFacts_psl _ hp (by rw [he]; exact hq)
    · rw [h]; exact hU _ _ hp (by rw [he]; exact hq)
  obtain ⟨hgeom, hdich⟩ := hF hrank
  have hcommJK : ∀ r ∈ R_K, ∀ s ∈ R_J, r * s = s * r := by
    rcases hgeom.centralizes R_J hR_J R_K hR_K r_J hrJ hrJc hrJ1 hcenJ with h1 | h1
    · exact absurd h1 hKJ
    · exact fun r hr s hs => h1 r hr s hs
  have hnc : ¬ ({z * t} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hs.nonabelian hne1
  have hQ : CFSG.IsComponent (V.psi j).range := V.isComponent_range j
  have hBN := FrameVertex.modOdd_le_normalizer hp hq hΩ.conjInvariant hΩ.classical hs.below hc2
    hnc hBel hztB hne1 hzB hfd.hz.ne_one hzne hKmem hKcl hQ hmov'
  have hv2 : oddQuotMk (z * t) ⟨z', hz'C⟩ * oddQuotMk (z * t) ⟨z', hz'C⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z', hz'C⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) * ⟨z', hz'C⟩ = 1 :=
      Subtype.ext hz'2
    rw [this, map_one]
  have hvR : ∀ s ∈ R_K, oddQuotMk (z * t) ⟨z', hz'C⟩ * V.psi j s =
      V.psi j s * oddQuotMk (z * t) ⟨z', hz'C⟩ := by
    intro s hs
    apply hz'K
    rw [← hmodK]
    exact ⟨s, hs, rfl⟩
  rcases hdich (V.psi j) (V.psi_ker j) hR_K (hBN (oddQuotMk_mem_modOdd hz'B hz'C)) hv2 hvR
    with ⟨R'', hR'', hcomm, hv''⟩ | hpos
  ·
    exfalso
    have hR''J : R'' = R_J := hgeom.uniq R_K hR_K R'' hR'' R_J hR_J hcomm hcommJK
    rw [hR''J] at hv''
    have hz'N : z' ∈ Subgroup.normalizer (J : Set G) :=
      mem_normalizer_of_commutes_involution hΩ.conjInvariant hT hfd.memJ hfd.ht hfd.htz'.symm
    have hz'J : z' ∈ trivialOnQuot J := by
      refine mem_trivialOnQuot_of_centralizes_modOdd hJcl hc2 hcJ hz'C hz'N ?_
      intro y hy
      rw [← hmodJ] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact hv'' s hs
    have hKJne : J ≠ K' := by
      intro h1
      apply hfd.z'_ne_t hΩ
      have h2 : IsUniqueInvolution J z' := by rw [h1]; exact hfd.hz'
      exact h2.eq hfd.ht
    have hJK' : J ∈ omegaNbr Ω K' :=
      mem_omegaNbr_of_trivialOnQuot hp hq hΩ hfd.memK' hfd.hz' hfd.memJ hKJne hz'J
    exact hfd.hperp (Set.mem_insert_of_mem _
      (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hfd.memK' hfd.memJ hJK'))
  ·
    apply hpos r_K hrK hrKc
    set T : Subgroup (OddQuot (z * t)) := Subgroup.closure
      (({V.psi j r_K, oddQuotMk (z * t) ⟨z', hz'C⟩} : Set (OddQuot (z * t))) ∪
        (Subgroup.center (OddQuot (z * t)) : Set (OddQuot (z * t)))) with hT'
    have hzT : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ T := by
      rw [hrKbar']
      exact Subgroup.subset_closure (Or.inl (Or.inl rfl))
    have hcbar : oddQuotMk (z * t) ⟨z * t, hcC⟩ ∈ T :=
      Subgroup.subset_closure (Or.inr (Subgroup.mem_center_iff.mpr fun y =>
        (oddQuotMk_central hcC y).symm))
    have htT : oddQuotMk (z * t) ⟨t, htC⟩ ∈ T := by
      have e : oddQuotMk (z * t) ⟨t, htC⟩ =
          oddQuotMk (z * t) ⟨z, hzC⟩ * oddQuotMk (z * t) ⟨z * t, hcC⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show t = z * (z * t)
        rw [← mul_assoc, hz2, one_mul]
      rw [e]
      exact T.mul_mem hzT hcbar
    have hz'T : oddQuotMk (z * t) ⟨z', hz'C⟩ ∈ T :=
      Subgroup.subset_closure (Or.inl (Or.inr rfl))
    have hTg : B ≤
        (T.comap (oddQuotMk (z * t))).map (Subgroup.centralizer ({z * t} : Set G)).subtype := by
      rw [hB, Subgroup.closure_le]
      intro u hu
      rcases hu with rfl | rfl | rfl
      · exact ⟨⟨u, hzC⟩, hzT, rfl⟩
      · exact ⟨⟨u, htC⟩, htT, rfl⟩
      · exact ⟨⟨u, hz'C⟩, hz'T, rfl⟩
    rintro y ⟨k, hk, rfl⟩
    obtain ⟨u, hu, huk⟩ := hTg hk
    have : u = k := Subtype.ext huk
    rw [← this]
    exact hu

theorem posZT_of_tagZT
    (hU : ∀ n e : ℕ, p ≠ 2 → 5 ≤ p ^ e → RankFourFacts .PSU n p e)
    (hs : ChainFrameCore p f Ω K J K' z t z')
    (hTag : ∃ D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t), ∀ j : Fin D.card,
      MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
        D.tag j = .PSL ∨ D.tag j = .PSU) :
    ∃ D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t), ∀ j : Fin D.card,
      MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
        (D.tag j = .PSL ∨ D.tag j = .PSU) ∧
          ToralActionDiag 2 (D.tag j) (D.rank j) p (D.exp j) Fact.out
            (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j)
            (modOdd (z * t) (Subgroup.closure ({z, t, z'} : Set G))) := by
  obtain ⟨D, hD⟩ := hTag
  exact ⟨D, fun j hmov => ⟨hD j hmov, toralActionDiag_zt hU hs D j hmov (hD j hmov)⟩⟩

theorem posZT_of_tagZT_proved
    (hs : ChainFrameCore p f Ω K J K' z t z')
    (hTag : ∃ D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t), ∀ j : Fin D.card,
      MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
        D.tag j = .PSL ∨ D.tag j = .PSU) :
    ∃ D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t), ∀ j : Fin D.card,
      MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
        (D.tag j = .PSL ∨ D.tag j = .PSU) ∧
          ToralActionDiag 2 (D.tag j) (D.rank j) p (D.exp j) Fact.out
            (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j)
            (modOdd (z * t) (Subgroup.closure ({z, t, z'} : Set G))) :=
  posZT_of_tagZT (fun _ _ hp2 h5 => rankFourFacts_psu _ hp2 h5) hs hTag

theorem hyp51At_zt_of_posZT (hs : ChainFrameCore p f Ω K J K' z t z')
    (hpos : ∃ D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t), ∀ j : Fin D.card,
      MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
        (D.tag j = .PSL ∨ D.tag j = .PSU) ∧
          ToralActionDiag 2 (D.tag j) (D.rank j) p (D.exp j) Fact.out
            (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j)
            (modOdd (z * t) (Subgroup.closure ({z, t, z'} : Set G)))) :
    Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) (z * t) := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have htB : t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hzB : z ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hztB : z * t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.mul_mem _ hzB htB
  have hzt : z * t = t * z := hd.comm_zt hp hΩ
  have hsq : (z * t) * (z * t) = 1 := by
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [← hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hd.hz.sq, hd.ht.sq, one_mul]
  have hne1 : z * t ≠ 1 := by
    intro h1
    have h2 : z = t⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right hd.ht.sq] at h2
    exact hd.t_ne_z hp hq hΩ h2.symm
  have hKzt : K ∈ ExactLayer.tqMembers Ω (z * t) :=
    ExactLayer.mem_tqMembers_iff.mpr ⟨hd.mem, hd.tq_B hp hq hΩ hztB⟩
  have hzne : z ≠ z * t := fun h1 =>
    hd.ht.ne_one (mul_left_cancel (a := z) (b := t) (c := 1) (by rw [mul_one]; exact h1.symm))
  exact FrameVertex.hyp51At_of_system_diag hp hq hΩ.conjInvariant hΩ.classical hs.below
    (ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq)
    (Balance.not_subset_center_of_ne_one hs.nonabelian hne1)
    (hd.isElemAbelian hp hΩ) (hd.natCard_eight hp hq hΩ) hztB hne1 hzB hd.hz.ne_one hzne hKzt
    (isClassicalMember_of_twin hΩ hd.mem hd.hz) hpos

theorem hyp51At_zt_of_tagZT (hs : ChainFrameCore p f Ω K J K' z t z')
    (hTag : ∃ D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t), ∀ j : Fin D.card,
      MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
        D.tag j = .PSL ∨ D.tag j = .PSU) :
    Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) (z * t) :=
  hyp51At_zt_of_posZT hs (posZT_of_tagZT_proved hs hTag)

end Position

end CFSG.ClassicalInvolution.Asc77.CFC
