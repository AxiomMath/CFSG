module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNormC2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HS4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdFields1

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Group

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_two_of_le_two {A B : Subgroup G} (h2 : A.relIndex B ≤ 2) (hne : ¬ B ≤ A) :
    A.relIndex B = 2 := by
  have h1 : A.relIndex B ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.mp h)
  have h0 : A.relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

end Group

section Fields2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP : Subgroup G}

theorem R0_not_comp (hi : Hyp2519 N i) (c : Case2 N.K Ki t i) (hKP : KP = Ki) :
    ∀ r ∈ Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G), r ≠ 1 → r ^ 2 = 1 →
      ¬ IsComponentIn N.K (Subgroup.centralizer ({r} : Set G)) := by
  intro r hr _ _ hK
  have hKi : Ki ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [← hKP]; exact KP_le_centralizer_of_mem_R0 hr
  have hK' : IsComponentIn N.K Ki := BenderBranch.isComponentIn_of_le hK c.K_le hKi
  have hKeq : N.K = Ki := eq_of_isComponentIn_of_isQuasisimple hK' c.quasisimple
  exact hi.not_comp (hKeq ▸ c.comp)

theorem r0_requirements (hi : Hyp2519 N i) (hsh : Shape N t i Ki KP) (c : Case2 N.K Ki t i)
    (hKP : KP = Ki)
    (hindex : (Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G)).relIndex (Rgrp2519 N i) = 2) :
    ∃ R2 : Subgroup G, R2 ≤ Rgrp2519 N i ∧ R2.relIndex (Rgrp2519 N i) = 2 ∧
      (∀ c' ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G), c' ∈ Subgroup.normalizer (N.K : Set G) →
        c' ∈ Subgroup.normalizer (R2 : Set G)) ∧
      (∀ r ∈ R2, r ≠ 1 → r ^ 2 = 1 → ¬ IsComponentIn N.K (Subgroup.centralizer ({r} : Set G))) := by
  refine ⟨Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G), inf_le_left, hindex,
    fun c' hc' hcK => normalizes_R0 hsh hc' hcK, ?_⟩
  intro r hr h1 h2
  exact R0_not_comp hi c hKP r hr h1 h2

theorem not_isComponentIn_of_r1 {K B Y₁ : Subgroup G}
    (hA : ∃ A : Subgroup G, A = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (B ⊓ Subgroup.centralizer (Y₁ : Set G)) ∧ CFSG.IsQuasisimple ↥A ∧ K < A) :
    ∀ r ∈ Y₁, r ≠ 1 → r ^ 2 = 1 → ¬ IsComponentIn K (Subgroup.centralizer ({r} : Set G)) := by
  obtain ⟨A, hAdef, hAq, hKA⟩ := hA
  intro r hr _ _ hK
  have hAle : A ≤ Subgroup.centralizer ({r} : Set G) := by
    have h1 : A ≤ B ⊓ Subgroup.centralizer (Y₁ : Set G) := by
      rw [hAdef]; exact perfectResidualOf_le _
    refine h1.trans (inf_le_right.trans (Subgroup.centralizer_le ?_))
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact hr
  have hKA' : IsComponentIn K A := BenderBranch.isComponentIn_of_le hK hKA.le hAle
  exact hKA.ne (eq_of_isComponentIn_of_isQuasisimple hKA' hAq)

theorem exists_R2_case2 (hI : Inputs2519) (h : Lv2518 N t zK) (hi : Hyp2519 N i)
    (hsh : Shape N t i Ki KP) (c : Case2 N.K Ki t i) (hKP : KP = Ki) :
    ∃ R2 : Subgroup G, R2 ≤ Rgrp2519 N i ∧ R2.relIndex (Rgrp2519 N i) = 2 ∧
      (N.S ⊓ Subgroup.centralizer (N.K : Set G) ≤ N.S ⊓ Subgroup.centralizer ({i} : Set G) →
        (∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G),
          c ∈ Subgroup.normalizer (N.K : Set G)) →
        (∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) = Nat.card (Rgrp2519 N i) →
          Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G)) ≤
            Nat.card ↥(N.S ⊓ Subgroup.centralizer ({i} : Set G))) →
        (∃ n ∈ N.S ⊓ Subgroup.normalizer (N.K : Set G), n * i ≠ i * n) →
        ∀ c' ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G), c' ∈ Subgroup.normalizer (N.K : Set G) →
          c' ∈ Subgroup.normalizer (R2 : Set G)) ∧
      (∀ r ∈ R2, r ≠ 1 → r ^ 2 = 1 → ¬ IsComponentIn N.K (Subgroup.centralizer ({r} : Set G))) := by
  have hf := h.facts2511
  have hRN : Rgrp2519 N i ≤ Subgroup.normalizer (Ki : Set G) := by
    rw [← hKP]; exact Rgrp_le_normalizer_KP hsh
  have htR : t ∈ Rgrp2519 N i := N.t_mem_R hf hi.mem_S
  have htnot : ¬ Rgrp2519 N i ≤ Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G) := by
    intro hle
    apply c.not_le_centralizer
    intro k hk
    have := (hle htR).2
    rw [hKP] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp this k hk)
  by_cases hHS : PatHS Ki N.K t
  · obtain ⟨hle4, hex4⟩ := hI.autCentHS G Ki N.K t c.quasisimple c.tN c.t_sq c.comm c.K_eq hHS
      (Rgrp2519 N i) hRN (Rgrp2519_le_centralizer_K N i) htR
    have hpgrp : IsPGroup 2 ↥(Rgrp2519 N i) := Rgrp2519_isPGroup N i
    obtain ⟨n, hn⟩ := IsPGroup.index (p := 2) hpgrp
      ((Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).subgroupOf (Rgrp2519 N i))
    have hrel : (Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).relIndex (Rgrp2519 N i) = 2 ∨
        (Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).relIndex (Rgrp2519 N i) = 4 := by
      have h1 : (Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).relIndex (Rgrp2519 N i) ≠ 1 :=
        fun h => htnot (by rw [hKP]; exact Subgroup.relIndex_eq_one.mp h)
      have h0 : (Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).relIndex (Rgrp2519 N i) ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      have hn' : (Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).relIndex (Rgrp2519 N i) =
          2 ^ n := hn
      rw [hn'] at hle4 h1 ⊢
      have hn2 : n ≤ 2 := by
        by_contra hcon
        have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases n <;> simp_all
    rcases hrel with h2 | h4eq
    · obtain ⟨R2, hle, hidx, hnorm, hnc⟩ := r0_requirements hi hsh c hKP (by rw [hKP]; exact h2)
      exact ⟨R2, hle, hidx, fun _ _ _ _ => hnorm, hnc⟩
    · obtain ⟨hexpo, ⟨Y₁, hR0Y, hYR, hidx, htY⟩, hall⟩ := hex4 h4eq
      have hA := hall Y₁ hR0Y hYR hidx htY
      refine ⟨Y₁, hYR, hidx, fun hB hCiK hM2 hn' c' _ _ => ?_, not_isComponentIn_of_r1 hA⟩
      exfalso
      have hi0 : i ∈ Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G) := by
        rw [← hKP]; exact i_mem_R0 hi hsh
      have hbig : 4 < Nat.card (Rgrp2519 N i) := by
        have h1 := Subgroup.card_mul_index
          ((Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).subgroupOf (Rgrp2519 N i))
        have h2 : (Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).relIndex (Rgrp2519 N i) = 4 :=
          h4eq
        have h3 : 1 < Nat.card ↥((Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).subgroupOf
            (Rgrp2519 N i)) := by
          rw [Subgroup.one_lt_card_iff_ne_bot]
          intro hbot
          have hmem : (⟨i, hi.mem_R⟩ : ↥(Rgrp2519 N i)) ∈
              (Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).subgroupOf (Rgrp2519 N i) :=
            Subgroup.mem_subgroupOf.mpr hi0
          rw [hbot, Subgroup.mem_bot] at hmem
          exact hi.ne_one (congrArg Subtype.val hmem)
        have h4 : (Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).relIndex (Rgrp2519 N i) =
            ((Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G)).subgroupOf (Rgrp2519 N i)).index :=
          rfl
        rw [h4] at h2
        rw [h2] at h1
        omega
      exact HS4.hs4_false h hHS.1 hM2 hB hCiK hn' (R0 := Rgrp2519 N i ⊓ Subgroup.centralizer (Ki : Set G))
        inf_le_left
        (fun c'' hc'' hcK'' => by
          have := normalizes_R0 hsh hc'' hcK''
          rwa [hKP] at this)
        (fun r hr h1 h2 => R0_not_comp hi c hKP r (by rw [hKP]; exact hr) h1 h2)
        (fun r hr => ⟨(Rgrp2519 N i).mul_mem hr hr, hexpo r hr⟩) hbig
  · have hpat5 : PatA Ki N.K t ∨ PatB Ki N.K t ∨ PatSp4 Ki N.K ∨ PatL5 Ki N.K ∨ PatA8 Ki N.K t := by
      rcases c.patAll with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact absurd h hHS
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have hle2 := hI.autCent G Ki N.K t c.quasisimple c.tN c.t_sq c.comm c.K_eq hpat5
      (Rgrp2519 N i) hRN (Rgrp2519_le_centralizer_K N i)
    have := relIndex_eq_two_of_le_two hle2 (by rw [← hKP]; exact htnot)
    obtain ⟨R2, hle, hidx, hnorm, hnc⟩ := r0_requirements hi hsh c hKP (by rw [hKP]; exact this)
    exact ⟨R2, hle, hidx, fun _ _ _ _ => hnorm, hnc⟩

theorem ident_case2 (hI : Inputs2519) (h : Lv2518 N t zK) (hi : Hyp2519 N i)
    (hsh : Shape N t i Ki KP) (heq : Ki = CFSG.conjugate Ki t) :
    ∃ R2 : Subgroup G, Ident2519 N t i Ki KP R2 := by
  have hf := h.facts2511
  obtain ⟨hKP, c⟩ := case2_of_shape hI h hi hsh heq
  have hsimple := hs.setting.simple
  have hnonab := hs.setting.nonabelian
  have hq := hs.setting.qtke
  obtain ⟨R2, hR2le, hR2idx, hR2norm, hR2nc⟩ := exists_R2_case2 hI h hi hsh c hKP
  have hRN : Rgrp2519 N i ≤ Subgroup.normalizer (Ki : Set G) := by
    rw [← hKP]; exact Rgrp_le_normalizer_KP hsh
  have hR32 : IsL2pType ↥N.K → PatA Ki N.K t ∨ PatB Ki N.K t := fun hKt =>
    c.pat32 (isL32_of_isL2pType_of_not_big hKt c.nbig)
  have hindex : IsL2pType ↥N.K →
      (Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G)).relIndex (Rgrp2519 N i) = 2 := by
    intro hKt
    have hle2 := hI.autCent G Ki N.K t c.quasisimple c.tN c.t_sq c.comm c.K_eq
      (by rcases hR32 hKt with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')) (Rgrp2519 N i) hRN (Rgrp2519_le_centralizer_K N i)
    have htR : t ∈ Rgrp2519 N i := N.t_mem_R hf hi.mem_S
    rw [hKP]
    refine relIndex_eq_two_of_le_two hle2 fun hle => c.not_le_centralizer ?_
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hle htR).2 k hk)
  refine ⟨R2, ?_⟩
  exact
    { comp := hsh.comp
      K_le := hsh.K_le
      KP_le := hsh.KP_le
      shape := Or.inr ⟨hKP, c.comm⟩
      K_eq := by rw [hKP]; exact c.K_eq
      three_rank := by rw [hKP]; exact c.three_rank hI.threeRank
      center_three := fun x hx h3 => c.center_three (by rwa [hKP] at hx) h3
      R2_le := hR2le
      R2_index := hR2idx
      R2_norm := hR2norm
      R2_not_comp := hR2nc
      R0_index := hindex
      normal_C := fun hKt j hj hj1 hj2 => by
        have hK32 : IsL32 N.K := isL32_of_isL2pType_of_not_big hKt c.nbig
        have hjS : j ∈ N.S := hj.1.1.1
        have hji : j * i = i * j := Subgroup.mem_centralizer_singleton_iff.mp hj.1.1.2
        rw [hKP]
        exact normalC_case2 hI hsimple hnonab hq c hK32 (N.two_dvd_card_K h.facts258)
          (exists_E4_K h.facts258) hi.ne_one hi.mul_self hj1 (by rw [← sq]; exact hj2) hji
          (N.t_comm_of_mem_S hf hjS).symm (by rw [← hKP]; exact hj.2)
      perfect_cent := fun hKt Y hYN hYK hY => by
        rw [hKP] at hYN ⊢
        have hle2 := hI.autCent G Ki N.K t c.quasisimple c.tN c.t_sq c.comm c.K_eq
          (by rcases hR32 hKt with h' | h'
              · exact Or.inl h'
              · exact Or.inr (Or.inl h')) Y hYN hYK
        exact (le_of_perfect_of_relIndex_le_two hY hle2).trans inf_le_right }

end Fields2

end CFSG.QuasithinUnique.Id2519
