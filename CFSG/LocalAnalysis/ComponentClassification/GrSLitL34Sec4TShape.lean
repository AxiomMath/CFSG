module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4TShapeB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowPosition

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit.L34Facts GrS4

structure L34TShapeLocalData (G : Type) [Group G] [Finite G]
    (a : G) (J S B T : Subgroup G) : Prop where
  hJ : ⁅J, J⁆ = J
  hL34 : IsL34Type (J ⧸ Open.fusionZStar J)
  hS : IsSylowTwoIn S (normalizer (J : Set G))
  hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S
  ha2 : orderOf a = 2
  haZ : a ∈ S ⊓ zStarIn J
  hZc : IsCyclic ↥(S ⊓ zStarIn J)
  hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4
  hQc : IsCyclic ↥(S ⊓ coreActionKernel J)
  hBP : B ≤ S ⊓ J
  hB8 : IsEightGroup B
  hBZ : B ⊓ zStarIn J = zpowers a
  hSB : S ≤ normalizer (B : Set G)
  hBiff : ∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔
    y ∈ B ⊔ (S ⊓ zStarIn J)
  hAut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
    n⁻¹ * (b : G) * n = (σ b : G)
  hT : T = S ⊓ centralizer (B : Set G)

theorem l34EndTShapeStep_of_local
    (hExp : L34BFixExponentFact) (hSq : L34BFixOuterSquareFact)
    (hIdx : L34GraphCosetIndexFact)
    {G : Type} [Group G] [Finite G] {a : G} {J S B T : Subgroup G}
    (h : L34TShapeLocalData G a J S B T) :
    T ≤ withKernel J ∨
      ∃ c ∈ S, c * c = 1 ∧ c ∉ withKernel J ∧
        T = S ⊓ J ⊓ centralizer (B : Set G) ⊔ zpowers c := by
  obtain ⟨hJ, hL34, hS, hSyl, ha2, haZ, hZc, hZ4, hQc, hBSJ, hB8, hBZ, hSB, hBc, hAut, hT⟩ := h
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := isSylowTwoIn_inf hS
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := isPGroup_of_isSylowTwoIn hP
  have hPJ : S ⊓ J ≤ J := inf_le_right
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  have hSP : ∀ s ∈ S, s ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) := fun s hs =>
    inf_mem_normalizer (le_normalizer hs) (hSN hs)
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haB : a ∈ B := (show zpowers a ≤ B from hBZ ▸ inf_le_left) (mem_zpowers a)
  have hTS : T ≤ S := hT ▸ inf_le_left
  have hTC : T ≤ centralizer (B : Set G) := hT ▸ inf_le_right
  have hmemT : ∀ y ∈ S, y ∈ centralizer (B : Set G) → y ∈ T := fun y hyS hyC => by
    rw [hT]
    exact mem_inf.mpr ⟨hyS, hyC⟩
  by_cases hTW : T ≤ withKernel J
  · exact Or.inl hTW
  right
  obtain ⟨c₀, hc₀T, hc₀W⟩ : ∃ c₀ ∈ T, c₀ ∉ withKernel J := by
    by_contra h
    push Not at h
    exact hTW h
  have hc₀S : c₀ ∈ S := hTS hc₀T
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT0⟩ := exists_sylow_standard hJ hL34 hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hZiff : ∀ g, g ∈ S ⊓ zStarIn J ↔ g ∈ S ⊓ J ∧ g ∈ zStarIn J := fun g => by
    simp only [mem_inf]
    exact ⟨fun h => ⟨⟨h.1, (map_subtype_le _ : zStarIn J ≤ J) h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  obtain ⟨hkc, hk4⟩ := ker_isCyclic_card_of_std hP hZiff hZc hZ4 hqker hT0
  have hqT0 : ∀ t ∈ T0, ∃ p ∈ S ⊓ J, ∃ hp : p ∈ J, q (jq J ⟨p, hp⟩) = t := fun t ht => by
    obtain ⟨e, rfl⟩ := hqsurj t (T0_le_S ht)
    obtain ⟨p, hpP, hpJ, rfl⟩ := (hT0 e).1 ht
    exact ⟨p, hpP, hpJ, rfl⟩
  obtain ⟨ψ, hψR, hψ⟩ := exists_realization_hom hSN hqS hqsurj hqker
  have hBhat : ∀ e ∈ l34BHat q, ∃ b ∈ B, ∃ hb : b ∈ J, jq J ⟨b, hb⟩ = e := fun e he =>
    exists_of_mem_l34BHat hqker hT0 hBSJ hBc hS2 hB8.1 hZc haZ haa ha1 haB he
  have hβB : ∀ t (ht : t ∈ T), ∀ e ∈ l34BHat q, betaHat J (hSN (hTS ht)) e = e := by
    intro t ht e he
    obtain ⟨b, hb, hbJ, rfl⟩ := hBhat e he
    rw [betaHat_jq]
    congr 1
    apply Subtype.ext
    rw [coe_conjJ]
    calc t⁻¹ * b * t = t⁻¹ * (t * b) := by rw [mul_assoc, mem_centralizer_iff.mp (hTC ht) b hb]
      _ = b := by group
  have hψ4 : ∀ t (ht : t ∈ T), ψ ⟨t, hTS ht⟩ ^ 4 = 1 := by
    intro t ht
    have h := hExp (Jhat J) q l hQ hkc hk4 (ψ ⟨t, hTS ht⟩)⁻¹ (inv_mem (hψR _))
      (fun u hu => by
        rw [inv_inv]
        exact inv_mul_mem_T0_of_realization hSN hqsurj hT0 hψ ⟨t, hTS ht⟩ (hSP t (hTS ht)) u hu)
      (betaHat J (hSN (hTS ht))) (fun e => by rw [hψ ⟨t, hTS ht⟩ e, inv_inv]) (hβB t ht)
    rwa [inv_pow, inv_eq_one] at h
  have hT4K : ∀ t ∈ T, t ^ 4 ∈ coreActionKernel J := by
    intro t ht
    have ht4 : t ^ 4 ∈ T := pow_mem ht 4
    refine mem_coreActionKernel_of_realization_eq_one hJ (hSN (hTS ht4)) hqker fun e => ?_
    have h := hψ ⟨t ^ 4, hTS ht4⟩ e
    rw [show (⟨t ^ 4, hTS ht4⟩ : ↥S) = ⟨t, hTS ht⟩ ^ 4 from rfl, map_pow, hψ4 t ht, inv_one,
      one_mul, mul_one] at h
    exact h
  have hTs : IsSylowTwoIn T (centralizer (B : Set G)) := hT ▸ isSylowTwoIn_inf_centralizer hSyl hSB
  have hT4 := pow_pow_ne_of_four hB8.1 hB8.2 (fun b hb => (mem_inf.mp (hBSJ hb)).2) hBZ haB ha1
    haa hTs hAut hT4K
  have hKT : ∀ k ∈ S ⊓ coreActionKernel J, k ∈ T := fun k hk =>
    hmemT k (mem_inf.mp hk).1 (mem_centralizer_iff.mpr fun b hb =>
      (mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hk).1 (mem_inf.mp hk).2
        (mem_inf.mp (hBSJ hb)).1 (mem_inf.mp (hBSJ hb)).2).symm)
  have hKZ : S ⊓ coreActionKernel J ≤ S ⊓ zStarIn J :=
    le_of_forall_pow_four_ne hQc (hS2.to_le inf_le_left)
      (inf_le_inf_left _ (zStarIn_le_coreActionKernel J)) hZ4
      (inf_le_inf_left _ (zStarIn_le_coreActionKernel J) haZ) haa ha1 fun t ht h4 =>
        hT4 t (hKT t ht) 1 (by rw [pow_one]; exact h4)
  have hT1 : ∀ t ∈ T, t ∈ withKernel J → t ∈ S ⊓ J ⊓ centralizer (B : Set G) := by
    intro t ht htW
    have hle : S ⊓ J ⊔ S ⊓ coreActionKernel J ≤ S ⊓ J :=
      sup_le le_rfl (hKZ.trans (inf_le_inf_left _ (map_subtype_le _ : zStarIn J ≤ J)))
    exact mem_inf.mpr ⟨hle (inf_withKernel_le hS (mem_inf.mpr ⟨hTS ht, htW⟩)), hTC ht⟩
  have hψT0 : ∀ s (hs : s ∈ T), ∀ u ∈ T0, ψ ⟨s, hTS hs⟩ * u * (ψ ⟨s, hTS hs⟩)⁻¹ ∈ T0 :=
    fun s hs => mul_inv_mem_T0_of_realization hSN hqsurj hT0 hψ ⟨s, hTS hs⟩ (hSP s (hTS hs))
  have hψZ : ∀ s (hs : s ∈ T), ∀ z ∈ T0, (∀ u ∈ T0, z * u = u * z) →
      ψ ⟨s, hTS hs⟩ * z = z * ψ ⟨s, hTS hs⟩ := by
    intro s hs z hz hzc
    obtain ⟨b, hb, hbJ, rfl⟩ := exists_of_mem_center_T0 hqker hT0 hqT0 hBSJ hBc hS2 hz hzc
    have e1 := hψ ⟨s, hTS hs⟩ (jq J ⟨b, hbJ⟩)
    rw [hβB s hs _ (jq_mem_l34BHat hqker hT0 hqT0 hBSJ hBc hB8.1 hb)] at e1
    calc ψ ⟨s, hTS hs⟩ * q (jq J ⟨b, hbJ⟩) =
        ψ ⟨s, hTS hs⟩ * ((ψ ⟨s, hTS hs⟩)⁻¹ * q (jq J ⟨b, hbJ⟩) * ψ ⟨s, hTS hs⟩) := by rw [← e1]
      _ = q (jq J ⟨b, hbJ⟩) * ψ ⟨s, hTS hs⟩ := by group
  have hnS : ∀ s (hs : s ∈ T), s ∉ withKernel J →
      ψ ⟨s, hTS hs⟩ ∉ CFSG.ComponentClassification.PSL3Four.S := fun s hs hsW h =>
    hsW (mem_withKernel_of_realization_mem_S hJ hSN hqsurj hqker hψ ⟨s, hTS hs⟩ h)
  have hidx : ∀ t ∈ T, ∀ t' ∈ T, t ∉ withKernel J → t' ∉ withKernel J →
      t * t'⁻¹ ∈ withKernel J := by
    intro t ht t' ht' htW ht'W
    have htt' : t * t'⁻¹ ∈ T := mul_mem ht (inv_mem ht')
    have h4' : (ψ ⟨t, hTS ht⟩ * (ψ ⟨t', hTS ht'⟩)⁻¹) ^ 4 = 1 := by
      rw [← map_inv, ← map_mul]
      exact hψ4 _ htt'
    have h := hIdx _ (hψR _) _ (hψR _) (hψT0 t ht) (hψT0 t' ht')
      (fun z hz hzc => ⟨hψZ t ht z hz hzc, hψZ t' ht' z hz hzc⟩) (hψ4 t ht) (hψ4 t' ht') h4'
      (hnS t ht htW) (hnS t' ht' ht'W)
    rw [← map_inv, ← map_mul] at h
    exact mem_withKernel_of_realization_mem_S hJ hSN hqsurj hqker hψ _ h
  have hc₀2 : c₀ * c₀ ∈ S ⊓ J ⊓ centralizer (B : Set G) := by
    refine hT1 _ (mul_mem hc₀T hc₀T) ?_
    have h := hidx c₀ hc₀T c₀⁻¹ (inv_mem hc₀T) hc₀W (fun h => hc₀W (by simpa using inv_mem h))
    rwa [inv_inv] at h
  have hc₀2J : c₀ * c₀ ∈ J := (mem_inf.mp (mem_inf.mp hc₀2).1).2
  have hc₀N' : c₀⁻¹ ∈ normalizer (J : Set G) := inv_mem (hSN hc₀S)
  have hβy : ∀ e, q (betaHat J hc₀N' e) = ψ ⟨c₀, hc₀S⟩ * q e * (ψ ⟨c₀, hc₀S⟩)⁻¹ := by
    intro e
    have h := hψ ⟨c₀, hc₀S⟩⁻¹ e
    rw [map_inv, inv_inv] at h
    exact h
  have hβB' : ∀ e ∈ l34BHat q, betaHat J hc₀N' e = e := by
    intro e he
    obtain ⟨b, hb, hbJ, rfl⟩ := hBhat e he
    rw [betaHat_jq]
    congr 1
    apply Subtype.ext
    rw [coe_conjJ, inv_inv]
    calc c₀ * b * c₀⁻¹ = b * c₀ * c₀⁻¹ := by rw [mem_centralizer_iff.mp (hTC hc₀T) b hb]
      _ = b := by group
  have hβw : betaHat J hc₀N' (jq J ⟨c₀ * c₀, hc₀2J⟩) = jq J ⟨c₀ * c₀, hc₀2J⟩ := by
    rw [betaHat_jq]
    congr 1
    apply Subtype.ext
    rw [coe_conjJ, inv_inv]
    group
  have hββ : ∀ e, betaHat J hc₀N' (betaHat J hc₀N' e) =
      jq J ⟨c₀ * c₀, hc₀2J⟩ * e * (jq J ⟨c₀ * c₀, hc₀2J⟩)⁻¹ := by
    intro e
    obtain ⟨j, rfl⟩ := jq_surjective J e
    rw [betaHat_jq, betaHat_jq, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [coe_conjJ, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  have hsqx : ∀ x₀ (hx₀ : x₀ ∈ S ⊓ J) (hxt : x₀ * c₀ * (x₀ * c₀) ∈ J),
      jq J ⟨x₀ * c₀ * (x₀ * c₀), hxt⟩ = jq J ⟨x₀, (mem_inf.mp hx₀).2⟩ *
        betaHat J hc₀N' (jq J ⟨x₀, (mem_inf.mp hx₀).2⟩) * jq J ⟨c₀ * c₀, hc₀2J⟩ := by
    intro x₀ hx₀ hxt
    rw [betaHat_jq, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [coe_conjJ, Subgroup.coe_mul, inv_inv]
    group
  have hsqP : ∀ x₀ ∈ S ⊓ J, x₀ * c₀ * (x₀ * c₀) ∈ S ⊓ J := by
    intro x₀ hx₀
    have hc : c₀ * x₀ * c₀⁻¹ ∈ S ⊓ J := by
      have h := conj_mem_of_mem_normalizer (inv_mem (hSP c₀ hc₀S)) hx₀
      rwa [inv_inv] at h
    rw [show x₀ * c₀ * (x₀ * c₀) = x₀ * (c₀ * x₀ * c₀⁻¹) * (c₀ * c₀) by group]
    exact mul_mem (mul_mem hx₀ hc) (mem_inf.mp hc₀2).1
  have hcT : ∀ x₀ ∈ S ⊓ J ⊓ centralizer (B : Set G), x₀ * c₀ ∈ T := fun x₀ hx₀ =>
    mul_mem (hmemT x₀ (mem_inf.mp (mem_inf.mp hx₀).1).1 (mem_inf.mp hx₀).2) hc₀T
  have hcW : ∀ x₀ ∈ S ⊓ J ⊓ centralizer (B : Set G), x₀ * c₀ ∉ withKernel J := by
    intro x₀ hx₀ h
    apply hc₀W
    have hx₀W : x₀ ∈ withKernel J := mem_sup_left (mem_inf.mp (mem_inf.mp hx₀).1).2
    have := mul_mem (inv_mem hx₀W) h
    rwa [inv_mul_cancel_left] at this
  have hZ2 : ∀ u ∈ S ⊓ zStarIn J, u ≠ 1 → u = a ∨ u * u = a := by
    intro u hu hu1
    by_cases huu : u * u = 1
    · exact Or.inl ((eq_one_or_eq_of_isCyclic hZc haZ hu haa ha1 huu).resolve_left hu1)
    · right
      have h4 : u * u * (u * u) = 1 := by
        have h := pow_card_eq_one' (G := ↥(S ⊓ zStarIn J)) (x := ⟨u, hu⟩)
        rw [hZ4] at h
        have h' := congrArg Subtype.val h
        simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h'
        rw [← h']
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      exact (eq_one_or_eq_of_isCyclic hZc haZ (mul_mem hu hu) haa ha1 h4).resolve_left huu
  rcases hSq (Jhat J) q l hQ hkc hk4 (ψ ⟨c₀, hc₀S⟩) (hψR _) (hnS c₀ hc₀T hc₀W) (hψT0 c₀ hc₀T)
      (betaHat J hc₀N') hβy hβB' (jq J ⟨c₀ * c₀, hc₀2J⟩) ((hT0 _).2 ⟨_, (mem_inf.mp hc₀2).1, _,
        rfl⟩) hβw hββ with ⟨v, hv, hv1⟩ | ⟨v, hv, hvk, hv1⟩ | hall
  ·
    obtain ⟨x₀, hx₀P, hx₀C, hx₀J, rfl⟩ :=
      exists_of_mem_l34AHat hqker hT0 hqT0 hBSJ hBc hS2 hB8.1 hv
    have hx₀ : x₀ ∈ S ⊓ J ⊓ centralizer (B : Set G) := mem_inf.mpr ⟨hx₀P, hx₀C⟩
    have hcc : x₀ * c₀ * (x₀ * c₀) = 1 :=
      eq_one_of_jq_eq_one hPJ hP2 (hsqP x₀ hx₀P) ((hsqx x₀ hx₀P _).trans hv1)
    refine ⟨x₀ * c₀, hTS (hcT x₀ hx₀), hcc, hcW x₀ hx₀, le_antisymm (fun t ht => ?_) ?_⟩
    · by_cases htW : t ∈ withKernel J
      · exact mem_sup_left (hT1 t ht htW)
      · have h1 := hT1 _ (mul_mem ht (inv_mem (hcT x₀ hx₀)))
          (hidx t ht _ (hcT x₀ hx₀) htW (hcW x₀ hx₀))
        rw [show t = t * (x₀ * c₀)⁻¹ * (x₀ * c₀) by group]
        exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers _))
    · refine sup_le (fun t ht => hmemT t (mem_inf.mp (mem_inf.mp ht).1).1 (mem_inf.mp ht).2) ?_
      rw [zpowers_le]
      exact hcT x₀ hx₀
  ·
    exfalso
    obtain ⟨x₀, hx₀P, hx₀C, hx₀J, rfl⟩ :=
      exists_of_mem_l34AHat hqker hT0 hqT0 hBSJ hBc hS2 hB8.1 hv
    have hx₀ : x₀ ∈ S ⊓ J ⊓ centralizer (B : Set G) := mem_inf.mpr ⟨hx₀P, hx₀C⟩
    set t := x₀ * c₀ with htdef
    have ht2 := hsqP x₀ hx₀P
    have ht4 : t ^ 4 ∈ S ⊓ J := by
      rw [show t ^ 4 = t * t * (t * t) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact mul_mem ht2 ht2
    have hjq : jq J ⟨t ^ 4, (mem_inf.mp ht4).2⟩ = (jq J ⟨x₀, hx₀J⟩ *
        betaHat J hc₀N' (jq J ⟨x₀, hx₀J⟩) * jq J ⟨c₀ * c₀, hc₀2J⟩) ^ 2 := by
      rw [← hsqx x₀ hx₀P (hPJ ht2), pow_two, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, htdef, pow_succ, pow_zero, one_mul, mul_assoc]
    have hu : t ^ 4 ∈ S ⊓ zStarIn J := by
      refine mem_inf.mpr ⟨(mem_inf.mp ht4).1, (mem_zStarIn_iff (mem_inf.mp ht4).2).2 ?_⟩
      rw [hjq, ← hqker]
      exact hvk
    have hu1 : t ^ 4 ≠ 1 := fun h => hv1 (by
      rw [← hjq]
      have h1 : (⟨t ^ 4, (mem_inf.mp ht4).2⟩ : ↥J) = 1 := Subtype.ext h
      rw [h1, map_one])
    rcases hZ2 _ hu hu1 with h | h
    · exact hT4 t (hcT x₀ hx₀) 1 (by rw [pow_one]; exact h)
    · exact hT4 t (hcT x₀ hx₀) 2 (by rw [pow_two]; exact h)
  ·
    exfalso
    have hsq : ∀ t ∈ T, t ∉ S ⊓ J ⊓ centralizer (B : Set G) → t * t = a := by
      intro t ht ht1
      have htW : t ∉ withKernel J := fun h => ht1 (hT1 t ht h)
      have hx₀ := hT1 _ (mul_mem ht (inv_mem hc₀T)) (hidx t ht c₀ hc₀T htW hc₀W)
      have hx₀P : t * c₀⁻¹ ∈ S ⊓ J := (mem_inf.mp hx₀).1
      obtain ⟨hvk, hv2, hv1⟩ := hall _ (jq_mem_l34AHat hqker hT0 hBSJ hBc hS2 hB8.1 hZc haZ haa
        ha1 haB hx₀P (mem_inf.mp hx₀).2)
      have hxt : t * c₀⁻¹ * c₀ * (t * c₀⁻¹ * c₀) ∈ J := hPJ (hsqP _ hx₀P)
      have e1 := hsqx _ hx₀P hxt
      have htt : t * t ∈ S ⊓ J := by
        have h := hsqP _ hx₀P
        rwa [show t * c₀⁻¹ * c₀ * (t * c₀⁻¹ * c₀) = t * t by group] at h
      have e2 : jq J ⟨t * t, hPJ htt⟩ = jq J ⟨t * c₀⁻¹ * c₀ * (t * c₀⁻¹ * c₀), hxt⟩ := by
        congr 1
        apply Subtype.ext
        show t * t = t * c₀⁻¹ * c₀ * (t * c₀⁻¹ * c₀)
        group
      have e3 := e2.trans e1
      have hu : t * t ∈ S ⊓ zStarIn J := by
        refine mem_inf.mpr ⟨(mem_inf.mp htt).1, (mem_zStarIn_iff (mem_inf.mp htt).2).2 ?_⟩
        rw [← hqker, e3]
        exact hvk
      have huu : t * t * (t * t) = 1 := by
        refine eq_one_of_jq_eq_one hPJ hP2 (mul_mem htt htt) ?_
        rw [show (⟨t * t * (t * t), hPJ (mul_mem htt htt)⟩ : ↥J) =
          ⟨t * t, hPJ htt⟩ * ⟨t * t, hPJ htt⟩ from rfl, map_mul, e3, ← pow_two]
        exact hv2
      have hu1 : t * t ≠ 1 := fun h => hv1 (by
        rw [← e3]
        have h1 : (⟨t * t, hPJ htt⟩ : ↥J) = 1 := Subtype.ext h
        rw [h1, map_one])
      exact (eq_one_or_eq_of_isCyclic hZc haZ hu haa ha1 huu).resolve_left hu1
    obtain ⟨b', hb'B, hb'a⟩ := exists_mem_not_mem_zpowers hB8.2 haa ha1
    have hb'1 : b' ≠ 1 := fun h => hb'a (h ▸ one_mem _)
    obtain ⟨ν, hν, hνa⟩ := exists_mem_normalizer_conj_eq hB8.1 hTs hAut haB hb'B ha1 hb'1
    exact false_of_sq_eq hc₀T (fun h => hc₀W (mem_sup_left (mem_inf.mp (mem_inf.mp h).1).2)) hν
      hνa (fun h => hb'a (h ▸ mem_zpowers a)) hsq

theorem l34EndTShapeStep_of_facts
    (hExp : L34BFixExponentFact) (hSq : L34BFixOuterSquareFact)
    (hIdx : L34GraphCosetIndexFact) : L34EndTShapeStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBSJ hB8 hBZ hSB hBc
    hAut T hT
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hZ4
    norm_num at hZ4
  exact l34EndTShapeStep_of_local hExp hSq hIdx
    { hJ := hJ
      hL34 := hL34
      hS := hS
      hSyl := hSyl
      ha2 := hU3.1
      haZ := hZ hZne
      hZc := hZc
      hZ4 := hZ4
      hQc := hQc
      hBP := hBSJ
      hB8 := hB8
      hBZ := hBZ
      hSB := hSB
      hBiff := hBc
      hAut := hAut
      hT := hT }

end CFSG.ComponentClassification.GrSLit
