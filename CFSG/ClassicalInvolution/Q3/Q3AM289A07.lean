module

public import CFSG.ClassicalInvolution.Q3.Q3AM289A05
public import CFSG.ClassicalInvolution.Q3.Q3AM289A06
public import CFSG.ClassicalInvolution.Q3.Q3T8B14E
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Rows
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallLift

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

namespace S3A

section Vertex


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem hyp51At_vertex_s3 [IsSimpleGroup G] (hTW : Q3T7.TwinSqAlphaAll3)
    (hs : Std8 Ω K J S R T W z t)
    (hno : ∀ L : Subgroup G, L ∈ omegaNbr Ω K → L ∈ omegaNbr Ω J → False) {w : G}
    (hw2 : w * w = 1) (hwz : z * w = w * z) (hwt : t * w = w * t) (hne : w ≠ t)
    {R₀ : Subgroup G} (hR₀ : IsSylow2In R₀ K) (hwR : ∀ r ∈ R₀, r * w = w * r)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ Ω) (hJ₁w : IsUniqueInvolution J₁ w)
    (hJ₁star : J₁ ∈ omegaStarNbr Ω J) (hJ₁nbr : J₁ ∉ omegaNbr Ω J) {B : Subgroup G}
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

  have hwB : w ∈ B :=
    hBgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  rcases layerShapeD hs hno with hdisc | hsmall
  · obtain ⟨t', k', M, RM, RM', y, y', k₀, hRM, hRM', hne', hcomm', hy, hy2, hy1, hy', hy'2, hy'1,
      hMy, hMy', hk₀R, hk₀sq, hσR, hσR'⟩ :=
      layer_twin_s3 hs hw2 hwz hwt hne hR₀ hwR hJ₁ hJ₁w hJ₁star hJ₁nbr hdisc hwN
    have hSperf : Group.IsPerfect (modelUniv t' k' 3 1 Fact.out).K :=
      Group.isPerfect_def.2
        (ModelFacts.modelClauseZero t' k' 3 1 Fact.out (ih8_isFundTag_mf M.isFundTag)
          M.admissible).1.1
    have : Group.IsPerfect (modelUniv t' k' 3 1 Fact.out).K := hSperf
    let ψ : (modelUniv t' k' 3 1 Fact.out).K →* OddQuot (z * t) := θ.comp M.ψ
    have hker : ψ.ker ≤ Subgroup.center (modelUniv t' k' 3 1 Fact.out).K := by
      intro x hx
      apply M.ker_le_center
      have h1 : θ (M.ψ x) = 1 := hx
      exact hθinj (h1.trans (map_one θ).symm)
    have hSq : CFSG.Open.IsQuasisimple (modelUniv t' k' 3 1 Fact.out).K :=
      (ModelFacts.modelClauseZero t' k' 3 1 Fact.out (ih8_isFundTag_mf M.isFundTag)
        M.admissible).1

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

    have hψy : ψ y = oddQuotMk (z * t) ⟨z, hzC⟩ := by
      show θ (M.ψ y) = oddQuotMk (z * t) ⟨z, hzC⟩
      rw [hMy]
      rfl
    have hψy' : ψ y' = oddQuotMk (z * t) ⟨t, htC⟩ := by
      show θ (M.ψ y') = oddQuotMk (z * t) ⟨t, htC⟩
      rw [hMy']
      rfl
    have hψc : ψ y * ψ y' = oddQuotMk (z * t) ⟨z * t, hcC⟩ := by
      rw [hψy, hψy', ← map_mul]
      rfl
    have hkψ : ψ k₀ * ψ k₀ = ψ y' := by
      show θ (M.ψ k₀) * θ (M.ψ k₀) = θ (M.ψ y')
      rw [← map_mul, hk₀sq]
    have hwbar2 : oddQuotMk (z * t) ⟨w, hwC⟩ * oddQuotMk (z * t) ⟨w, hwC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨w, hwC⟩ * ⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) = 1 :=
        Subtype.ext hw2
      rw [this, map_one]
    have hwRbar : ∀ r ∈ RM, oddQuotMk (z * t) ⟨w, hwC⟩ * ψ r *
        (oddQuotMk (z * t) ⟨w, hwC⟩)⁻¹ = ψ r := by
      intro r hr
      have h : θ (s26Act (exactLayer3 Ω (z * t)) ⟨w, hwN⟩ (M.ψ r)) =
          oddQuotMk (z * t) ⟨w, hwC⟩ * θ (M.ψ r) * (oddQuotMk (z * t) ⟨w, hwC⟩)⁻¹ :=
        sectionQuotientHom_s26Act_exact hΦ hwC hwN (M.ψ r)
      rw [hσR r hr] at h
      exact h.symm
    have hwRbar' : ∀ r ∈ RM', oddQuotMk (z * t) ⟨w, hwC⟩ * ψ r *
        (oddQuotMk (z * t) ⟨w, hwC⟩)⁻¹ = ψ k₀ * ψ r * (ψ k₀)⁻¹ := by
      intro r hr
      have h : θ (s26Act (exactLayer3 Ω (z * t)) ⟨w, hwN⟩ (M.ψ r)) =
          oddQuotMk (z * t) ⟨w, hwC⟩ * θ (M.ψ r) * (oddQuotMk (z * t) ⟨w, hwC⟩)⁻¹ :=
        sectionQuotientHom_s26Act_exact hΦ hwC hwN (M.ψ r)
      rw [hσR' r hr] at h
      simp only [map_mul, map_inv] at h
      exact h.symm
    have hyE : ψ y ∈ modOdd (z * t) B := by
      rw [hψy]
      exact oddQuotMk_mem_modOdd hzB hzC
    have hwE : oddQuotMk (z * t) ⟨w, hwC⟩ ∈ modOdd (z * t) B := oddQuotMk_mem_modOdd hwB hwC
    have hE : ∀ e ∈ modOdd (z * t) B, ∃ d ∈ ({1, ψ y, oddQuotMk (z * t) ⟨w, hwC⟩,
        ψ y * oddQuotMk (z * t) ⟨w, hwC⟩} : Set (OddQuot (z * t))),
        ∃ e' ∈ Subgroup.center (OddQuot (z * t)), e = d * e' := by
      intro e he
      obtain ⟨d, hd, hdC, e', he', hde⟩ := exists_mul_central_of_mem_modOdd hB hBgen he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with h | h | h | h
      · subst h
        refine ⟨1, by simp, e', he', ?_⟩
        rw [hde, show oddQuotMk (z * t) ⟨1, hdC⟩ = 1 from map_one _]
      · have h' : oddQuotMk (z * t) ⟨d, hdC⟩ = ψ y := by
          rw [hψy]
          congr 1
          exact Subtype.ext h
        exact ⟨ψ y, by simp, e', he', by rw [← h']; exact hde⟩
      · have h' : oddQuotMk (z * t) ⟨d, hdC⟩ = oddQuotMk (z * t) ⟨w, hwC⟩ := by
          congr 1
          exact Subtype.ext h
        exact ⟨oddQuotMk (z * t) ⟨w, hwC⟩, by simp, e', he', by rw [← h']; exact hde⟩
      · have h' : oddQuotMk (z * t) ⟨d, hdC⟩ = ψ y * oddQuotMk (z * t) ⟨w, hwC⟩ := by
          rw [hψy, ← map_mul]
          congr 1
          exact Subtype.ext h
        exact ⟨ψ y * oddQuotMk (z * t) ⟨w, hwC⟩, by simp, e', he', by rw [← h']; exact hde⟩
    have hcc : oddQuotMk (z * t) ⟨z * t, hcC⟩ ∈ Subgroup.center (OddQuot (z * t)) :=
      oddQuotMk_mem_center_of_mem_zpowers (Subgroup.mem_zpowers _) hcC
    have hwNbar : oddQuotMk (z * t) ⟨w, hwC⟩ ∈
        Subgroup.normalizer (ψ.range : Set (OddQuot (z * t))) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hnormal]
      exact Subgroup.mem_top _
    rw [hLrange]
    exact alphaOf_inducedImage_eq_bot_of_twin (hTW t' k' M.isFundTag M.admissible) ψ hker rfl hRM
      hRM' hne' hcomm' hy hy2 hy1 hy' hy'2 hy'1 hcc hψc hk₀R hkψ hwbar2 hwNbar hwRbar hwRbar' hyE hwE hE
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

end S3A

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
