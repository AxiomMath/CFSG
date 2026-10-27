module

public import CFSG.ClassicalInvolution.Q3.Q3T8B14D
public import CFSG.ClassicalInvolution.Q3.Q3T8B14L

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1

section Vertex

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem sectionQuotientHom_s26Act_exact {c : G} (hΦ : SecData3 c (exactFamily3 Ω c)) {w : G}
    (hwC : w ∈ Subgroup.centralizer ({c} : Set G))
    (hwN : w ∈ Subgroup.normalizer ((exactLayer3 Ω c : Subgroup G) : Set G))
    (q : Q3T7.layerQuot3 Ω c) :
    sectionQuotientHom (normalizesLayer_of_secData3 hΦ) (s26Act (exactLayer3 Ω c) ⟨w, hwN⟩ q) =
      oddQuotMk c ⟨w, hwC⟩ * sectionQuotientHom (normalizesLayer_of_secData3 hΦ) q *
        (oddQuotMk c ⟨w, hwC⟩)⁻¹ := by
  induction q using QuotientGroup.induction_on with
  | H k =>
    have hk : w * (k : G) * w⁻¹ ∈ exactLayer3 Ω c := (Subgroup.mem_normalizer_iff.mp hwN k).mp k.2
    rw [s26Act_mk (exactLayer3 Ω c) ⟨w, hwN⟩ k ⟨w * (k : G) * w⁻¹, hk⟩ rfl]
    show oddQuotMk c ⟨w * (k : G) * w⁻¹, exactLayer3_le_centralizer Ω c hk⟩ =
      oddQuotMk c ⟨w, hwC⟩ * oddQuotMk c ⟨(k : G), exactLayer3_le_centralizer Ω c k.2⟩ *
        (oddQuotMk c ⟨w, hwC⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl

theorem layer_conj_dichotomy [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hsmall : ∀ M ∈ Q3T7.layerFam3 Ω (z * t),
      M = Layer.layerImg3 Ω (z * t) K ∨ M = Layer.layerImg3 Ω (z * t) J)
    (q : Q3T7.layerQuot3 Ω (z * t)) :
    q * T8V.layerMk (z * t) z (T8V.z_mem_layerJoin hs) * q⁻¹ =
        T8V.layerMk (z * t) z (T8V.z_mem_layerJoin hs) ∨
      q * T8V.layerMk (z * t) z (T8V.z_mem_layerJoin hs) * q⁻¹ =
        T8V.layerMk (z * t) t (T8V.t_mem_layerJoin hs) := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hXK : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hKt : K ∈ tqMembers3 Ω (z * t) := hXK.mem_tqMembers3 hΩ hx
  have hJt : J ∈ tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hne0 : (tqMembers3 Ω (z * t)).Nonempty := ⟨K, hKt⟩
  have hΦ : HypOmegaModU (.sl2 3 1) (Q3T7.layerFam3 Ω (z * t)) :=
    Q3T7.hypOmegaModU_layerFam3 hs3 hL.hc2 hne0
  have hKΦ : Layer.layerImg3 Ω (z * t) K ∈ Q3T7.layerFam3 Ω (z * t) := Layer.layerImg3_mem hKt
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(exactLayer3 Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hLYK : exactCore3 (z * t) K ≤ exactLayer3 Ω (z * t) := exactCore3_le_exactLayer3 hKt
  have hLYJ : exactCore3 (z * t) J ≤ exactLayer3 Ω (z * t) := exactCore3_le_exactLayer3 hJt
  have hzL : IsUniqueInvolution (exactCore3 (z * t) K) z :=
    Layer.isUniqueInvolution_exactCore3 hXK.2.1 hs.hz
  have htL : IsUniqueInvolution (exactCore3 (z * t) J) t :=
    Layer.isUniqueInvolution_exactCore3 hXJ.2.1 hs.ht
  have hxA : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) K)
      (T8V.layerMk (z * t) z (T8V.z_mem_layerJoin hs)) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf hzL hLYK)
  have hxB : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) J)
      (T8V.layerMk (z * t) t (T8V.t_mem_layerJoin hs)) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf htL hLYJ)
  have hconjK : conjSub q (Layer.layerImg3 Ω (z * t) K) ∈ Q3T7.layerFam3 Ω (z * t) :=
    hΦ.conjInvariant q _ hKΦ
  have hqx := hxA.conj q
  rcases hsmall _ hconjK with h | h
  · left
    have hmem : q * T8V.layerMk (z * t) z (T8V.z_mem_layerJoin hs) * q⁻¹ ∈
        Layer.layerImg3 Ω (z * t) K := h ▸ hqx.mem
    rcases hxA.unique _ hmem hqx.sq with h1 | h1
    · exact absurd h1 hqx.ne_one
    · exact h1
  · right
    have hmem : q * T8V.layerMk (z * t) z (T8V.z_mem_layerJoin hs) * q⁻¹ ∈
        Layer.layerImg3 Ω (z * t) J := h ▸ hqx.mem
    rcases hxB.unique _ hmem hqx.sq with h1 | h1
    · exact absurd h1 hqx.ne_one
    · exact h1

theorem hyp51At_vertexA_of_class [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    {w : G} (hwz : z * w = w * z) (hwt : t * w = w * t)
    (hclass : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t)) →
      ∀ hwN : w ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G),
      ∃ (M : Ih8Model 3 1 (Q3T7.layerFam3 Ω (z * t)) .PSL 4 1)
        (D : GL (Fin 4) (GaloisField 3 1)) (y' : SL(4, GaloisField 3 1)),
        M.ψ y' = T8V.layerMk (z * t) t (T8V.t_mem_layerJoin hs) ∧ y' * y' = 1 ∧ D * D = 1 ∧
          (∀ g, s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨w, hwN⟩ (M.ψ g) =
            M.ψ (Q3NM.conjSLAut D g)) ∧
          (D : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) *
              (y' : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) =
            (y' : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) * D)
    (hshape : LayerShapeAt Ω K J (z * t)) {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian 2 B) (hBgen : B = Subgroup.closure ({z, w, z * t} : Set G)) :
    Hyp51At B (z * t) := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hΩu : HypOmegaModU (.sl2 3 1) Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKt : K ∈ tqMembers3 Ω (z * t) := (Layer.xMem_zt3 hs).mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hc2 : IsPGroup 2 (Subgroup.zpowers (z * t)) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hx
  have hBelow := Q3T7.cit3Below_of_stand3 hs3
  have hΦ : SecData3 (z * t) (exactFamily3 Ω (z * t)) :=
    secData3_exactFamily (Q3T7.inClass3_of_stand3 hs3) hc2 ⟨K, hKt⟩
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, -, hac⟩ := IsConcreteLE.not_le_iff_exists.mp
      (isClassicalMember3_of_uniqueInvolution hΩu hK hs.hz).not_le_center
    rw [Subgroup.mem_center_iff] at hac
    push Not at hac
    obtain ⟨b, hb⟩ := hac
    exact ⟨b, a, hb⟩
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hzne : z ≠ t := T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht
  have hc1 : z * t ≠ 1 := by
    intro h
    exact hzne (by
      calc z = z * t * t := by rw [mul_assoc, hs.ht.sq, mul_one]
        _ = t := by rw [h, one_mul])
  have hnc : ¬ ({z * t} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hnab hc1
  have hzC : z ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * (z * t) = z * (t * z) := by rw [hzt]
      _ = z * t * z := (mul_assoc z t z).symm
  have htC : t ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (z * t) = (t * z) * t := (mul_assoc t z t).symm
      _ = (z * t) * t := by rw [hzt]
  have hcC : z * t ∈ Subgroup.centralizer ({z * t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hwcomm : w * (z * t) = z * t * w := by
    calc w * (z * t) = (w * z) * t := by rw [mul_assoc]
      _ = (z * w) * t := by rw [hwz]
      _ = z * (w * t) := by rw [mul_assoc]
      _ = z * (t * w) := by rw [hwt]
      _ = z * t * w := by rw [mul_assoc]
  have hwcen : w ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr hwcomm
  have hwC : w ∈ Subgroup.centralizer ({z * t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwcomm
  have hwN : w ∈ Subgroup.normalizer ((exactLayer3 Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hwcen)
  have hz1 : z ≠ 1 := hs.hz.ne_one
  have hzc : z ≠ z * t := fun h => hs.ht.ne_one (by
    have : z * t = z * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this)
  have hzB : z ∈ B := hBgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hcB : z * t ∈ B :=
    hBgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hM₀ : exactCore3 (z * t) K ∈ exactFamily3 Ω (z * t) := exactCore3_mem_exactFamily3 hKt
  have hzM : z ∈ exactCore3 (z * t) K :=
    mem_exactCore3 (isClassicalMember3_of_uniqueInvolution hΩu hK hs.hz) hc2 hKt.2
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hnc
  obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D hM₀
  have hbj : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ secComp hΦ D j := hj (oddQuotMk_mem_modOdd hzM hzC)
  refine hyp51At_of_secComp hΦ D j hB hcB hc1 hzB hz1 hzc hzC hbj ?_
  intro hLcomp hmov
  have hN' := normalizesLayer_of_secData3 hΦ
  let θ : Q3T7.layerQuot3 Ω (z * t) →* OddQuot (z * t) := sectionQuotientHom hN'
  have hθinj : Function.Injective θ := sectionQuotientHom_injective hN'
  rcases hshape with hdisc | hsmall
  · obtain ⟨M, Dm, y', hMy, hy'2, hDm2, hDσ, hDy⟩ :=
      hclass hdisc hwN
    let ψ : SL(4, 𝔽₃) →* OddQuot (z * t) := θ.comp M.ψ
    have hker : ψ.ker ≤ Subgroup.center SL(4, 𝔽₃) := by
      intro x hx
      apply M.ker_le_center
      have h1 : θ (M.ψ x) = 1 := hx
      exact hθinj (h1.trans (map_one θ).symm)
    have hSq : CFSG.Open.IsQuasisimple (modelUniv .PSL 4 3 1 Fact.out).K :=
      (ModelFacts.modelClauseZero .PSL 4 3 1 Fact.out trivial M.admissible).1
    have hnc' : ¬ (D.hom j).range ≤ Subgroup.center (Q3T7.layerQuot3 Ω (z * t)) := by
      intro hle
      obtain ⟨y, hyL, hy⟩ := hmov _ (oddQuotMk_mem_modOdd hzB hzC)
        (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hzB hz1 hzc hzC)
      obtain ⟨n, hn⟩ := hbj
      obtain ⟨n', hn'⟩ := hyL
      apply hy
      have hcen := Subgroup.mem_center_iff.mp (hle ⟨n, rfl⟩) (D.hom j n')
      have hn1 : θ (D.hom j n) = oddQuotMk (z * t) ⟨z, hzC⟩ := hn
      have hn1' : θ (D.hom j n') = y := hn'
      have e1 : θ (D.hom j n) * θ (D.hom j n') = θ (D.hom j n') * θ (D.hom j n) :=
        ((map_mul θ _ _).symm.trans (congrArg θ hcen.symm)).trans (map_mul θ _ _)
      rw [← hn1, ← hn1']
      exact e1
    have hN : (D.hom j).range = ⊤ :=
      eq_top_of_normal_of_quasisimple hSq M.ψ M.surj (range_normal_of_lieSystem D j) hnc'
    have hψrange : ψ.range = θ.range := by
      have h1 : ψ.range = M.ψ.range.map θ := MonoidHom.range_comp θ M.ψ
      rw [h1, MonoidHom.range_eq_top.mpr M.surj, Subgroup.map_top]
    have hLrange : secComp hΦ D j = ψ.range := by
      have h1 : secComp hΦ D j = (D.hom j).range.map θ := MonoidHom.range_comp θ (D.hom j)
      rw [h1, hN, Subgroup.map_top, hψrange]
    have hnormal : ψ.range.Normal := by
      have h' : (sectionQuotientHom hN').range.Normal := by
        rw [range_sectionQuotientHom hN']
        exact memberJoin_normal_of_normalizes hN'
      have h : θ.range.Normal := h'
      rw [hψrange]
      exact h
    have hzb : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ ψ.range := hLrange ▸ hbj
    have hzy : ∃ e' ∈ Subgroup.center (OddQuot (z * t)),
        oddQuotMk (z * t) ⟨z, hzC⟩ = ψ y' * e' := by
      refine ⟨oddQuotMk (z * t) ⟨z * t, hcC⟩,
        oddQuotMk_mem_center_of_mem_zpowers (Subgroup.mem_zpowers _) hcC, ?_⟩
      have hψy : ψ y' = oddQuotMk (z * t) ⟨t, htC⟩ := by
        show θ (M.ψ y') = oddQuotMk (z * t) ⟨t, htC⟩
        rw [hMy]
        rfl
      rw [hψy, ← map_mul]
      congr 1
      apply Subtype.ext
      show z = t * (z * t)
      rw [hzt, ← mul_assoc, hs.ht.sq, one_mul]
    have hw' : ∀ g, oddQuotMk (z * t) ⟨w, hwC⟩ * ψ g * (oddQuotMk (z * t) ⟨w, hwC⟩)⁻¹ =
        ψ (conjSLAut Dm g) := by
      intro g
      have h2 : θ (s26Act (exactLayer3 Ω (z * t)) ⟨w, hwN⟩ (M.ψ g)) =
          oddQuotMk (z * t) ⟨w, hwC⟩ * θ (M.ψ g) * (oddQuotMk (z * t) ⟨w, hwC⟩)⁻¹ :=
        sectionQuotientHom_s26Act_exact hΦ hwC hwN (M.ψ g)
      exact h2.symm.trans (congrArg θ (hDσ g))
    exact alphaOf_eq_bot_of_psl4 hB hBgen hc1 hz1 hzc hzC hwC ψ hker hDm2 hy'2 hDy hzb hzy hw'
      hnormal hLrange hmov
  · exfalso
    have hperf : commutator ↥(secComp hΦ D j) = ⊤ :=
      ((CFSG.isComponent_iff_open _).mp hLcomp).2.2.1
    have hzu : oddQuotMk (z * t) ⟨z, hzC⟩ =
        oddQuotMk (z * t) ⟨t, htC⟩ * oddQuotMk (z * t) ⟨z * t, hcC⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show z = t * (z * t)
      rw [hzt, ← mul_assoc, hs.ht.sq, one_mul]
    have hec : (oddQuotMk (z * t) ⟨z * t, hcC⟩)⁻¹ ∈ Subgroup.center (OddQuot (z * t)) :=
      Subgroup.inv_mem _
        (oddQuotMk_mem_center_of_mem_zpowers (Subgroup.mem_zpowers _) hcC)
    have hut : oddQuotMk (z * t) ⟨t, htC⟩ =
        oddQuotMk (z * t) ⟨z, hzC⟩ * (oddQuotMk (z * t) ⟨z * t, hcC⟩)⁻¹ :=
      eq_mul_inv_of_mul_eq hzu.symm
    have key : ∀ q : Q3T7.layerQuot3 Ω (z * t),
        θ q * oddQuotMk (z * t) ⟨z, hzC⟩ * (θ q)⁻¹ = oddQuotMk (z * t) ⟨z, hzC⟩ ∨
          θ q * oddQuotMk (z * t) ⟨z, hzC⟩ * (θ q)⁻¹ =
            oddQuotMk (z * t) ⟨z, hzC⟩ * (oddQuotMk (z * t) ⟨z * t, hcC⟩)⁻¹ := by
      intro q
      rcases layer_conj_dichotomy hs hsmall q with h1 | h1
      · left
        have h2 := congrArg θ h1
        simp only [map_mul, map_inv] at h2
        exact h2
      · right
        have h2 := congrArg θ h1
        simp only [map_mul, map_inv] at h2
        exact h2.trans hut
    have hconj : ∀ g ∈ secComp hΦ D j,
        g * oddQuotMk (z * t) ⟨z, hzC⟩ * g⁻¹ = oddQuotMk (z * t) ⟨z, hzC⟩ ∨
          g * oddQuotMk (z * t) ⟨z, hzC⟩ * g⁻¹ =
            oddQuotMk (z * t) ⟨z, hzC⟩ * (oddQuotMk (z * t) ⟨z * t, hcC⟩)⁻¹ := by
      intro g hg
      obtain ⟨n, rfl⟩ := hg
      exact key (D.hom j n)
    have hcent := centralizes_of_perfect hperf hec hconj
    obtain ⟨y, hyL, hy⟩ := hmov _ (oddQuotMk_mem_modOdd hzB hzC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hzB hz1 hzc hzC)
    exact hy (hcent y hyL).symm

end Vertex

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
