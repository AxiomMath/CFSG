module

public import CFSG.ClassicalInvolution.Asc77.AscT7FD
public import CFSG.ClassicalInvolution.Asc77.AscT7FB

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_StarCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        (∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) → MuIsoWylD4 Ω W →
          ∀ M ∈ dstarComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)

variable {p f}

theorem c21_16_of_conj (hE : ThmEWithSylow p f) (h3 : C21_3 p f) (h4 : TwinNormAlpha p f)
    (h13 : C21_13_N p f) (h14 : C21_14_N p f) : C21_16 p f := by
  intro G _ _ _ Ω K K' z u J t W h
  by_contra hα
  have hs : AlphaSteps p f := ⟨h3, h4⟩
  have hstd := stdCent_normalizer_alpha' hs h13 h14 h
  have hD : rLayer Ω (t * z) ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    (rLayer_le_centralizer Ω (t * z)).trans (h13 G Ω K K' z u J t W h)
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G), conjSub x K = M := by
    by_cases heq : dComp Ω K = dstarComp Ω K
    · intro M hM
      rw [← heq] at hM
      exact hs.exists_mem_normalizer h hM
    · have hN : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := fun n hn =>
        mem_normalizer_iff_conjSub_eq.mpr (hs.conj_alpha_of_mem_centralizer h
          (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn))))
      exact h.exists_mem_conj_of_dstarComp heq ((h.mGrp_le_rLayer_tz heq).trans hD) hN
  have htop := thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd htrans
  have hnormal : (alphaOf (Subgroup.closure ({u, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp htop
  have hodd := (h3 G Ω K K' z u J t W h).1
  rcases hnormal.eq_bot_or_eq_top with hbot | htopα
  · exact hα hbot
  · rw [htopα] at hodd
    have hcard : Nat.card ↥(⊤ : Subgroup G) = Nat.card G := Subgroup.card_top
    rw [hcard] at hodd
    have h2 : 2 ∣ Nat.card G := by
      have := orderOf_dvd_natCard (x := z)
      have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.std.hz.sq)
        h.std.hz.ne_one
      rwa [hz2] at this
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem frame_cent_sigmaStarNorm_direct (h13 : C21_13_wyl p f) (h15 : C21_15 p f)
    (h16 : C21_16 p f) (ha : C21_17_cent p f) (hb : C21_E_cent p f) {K K' J W : Subgroup G}
    {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
    Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K ∧
      Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  have hα := h16 G Ω K K' z u J t W h
  by_cases hD : rLayer Ω (t * z) ≤ sigmaGen Ω K
  · exact ha G Ω K K' z u J t W h hα hD (dComp_eq_dstarComp_of_rLayer_le h hD)
  · have hSigC := h15 G Ω K K' z u J t W h hα hD
    have hmu : MuIsoWylD4 Ω W := h13 G Ω K K' z u J t W h hα hD
    obtain ⟨hstar, hu⟩ := hb G Ω K K' z u J t W h hα hD hSigC hmu
    exact ⟨T7A.centralizer_le_sigmaStarNorm_of_eq h.std.stand.hyp.conjInvariant hstar, hu⟩

theorem sigmaStarNorm_eq_top_direct (hE : ThmEWithSylow p f) (h13 : C21_13_wyl p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (ha : C21_17_cent p f) (hb : C21_E_cent p f)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
    sigmaStarNorm Ω K = ⊤ := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have htail : StdCentTail Ω K (sigmaStarNorm Ω K) z :=
    stdCentTail_of_frames hp hq hΩ h fun {_ _ _ _ _ _} _ h₁ =>
      frame_cent_sigmaStarNorm_direct h13 h15 h16 ha hb h₁
  have hstd := stdCent_sigmaStarNorm hp hq hΩ hK h.std.hz h.std.stand.trans htail
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ sigmaStarNorm Ω K, conjSub x K = M := by
    intro M hM
    obtain ⟨x, hx⟩ := h.std.stand.trans M (T3.mem_dstarComp_symm hK hM).1
    exact ⟨x, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hx ▸ hM), hx⟩
  exact thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd htrans

end Steps

variable (p f) in
theorem c21_17_of_direct (hE : ThmEWithSylow p f) (h13 : C21_13_wyl p f) (h15 : C21_15 p f)
    (h16 : C21_16 p f) (ha : C21_17_cent p f) (hb : C21_E_cent p f) : C21_17 p f := by
  intro G _ _ _ Ω K K' z u J t W h hD
  have htop := sigmaStarNorm_eq_top_direct hE h13 h15 h16 ha hb h
  have hSig := dComp_eq_dstarComp_of_rLayer_le h hD
  have hsn : sigmaNorm Ω K = ⊤ := by
    rw [← htop]
    ext g
    exact forall_congr' fun M => by rw [hSig]
  exact h.std.disconnected (dConnected_of_sigmaNorm_eq_top h.std.stand.mem h.std.stand.trans hsn)

variable (p f) in
theorem c21_E_of_direct (hE : ThmEWithSylow p f) (h13 : C21_13_wyl p f) (h15 : C21_15 p f)
    (h16 : C21_16 p f) (ha : C21_17_cent p f) (hb : C21_E_cent p f) : C21_E p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have htop := sigmaStarNorm_eq_top_direct hE h13 h15 h16 ha hb h
  obtain ⟨hstar, -⟩ := hb G Ω K K' z u J t W h hα hD hSigC hmu
  have hall : ∀ M ∈ Ω, M ≤ Subgroup.centralizer ({t * z} : Set G) := by
    intro M hM
    obtain ⟨x, hx⟩ := h.std.stand.trans M hM
    have hxH : x ∈ sigmaStarNorm Ω K := by rw [htop]; exact Subgroup.mem_top x
    have hMS : M ∈ dstarComp Ω K := by
      have := (mem_sigmaStarNorm_iff.mp hxH K).mp Relation.ReflTransGen.refl
      rwa [hx] at this
    exact ((hstar M).mp hMS).2
  have hcent : Subgroup.centralizer ({t * z} : Set G) = ⊤ := by
    rw [eq_top_iff, ← h.std.stand.gen]
    exact iSup₂_le fun M hM => hall M hM
  have hcomm : ∀ g : G, g * (t * z) = (t * z) * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hcent ▸ Subgroup.mem_top g)
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
  obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hVR).exists_not_commute
  have h1 : t * z = 1 := T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm
  have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.std.hz.sq
  exact h.twinFrameData.t_ne_z (h2.trans h3)

variable (p f) in
theorem c21_E_star_of_starCent (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f)
    (hStar : C21_StarCent p f) : C21_E_star p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu M
  constructor
  · intro hM
    exact ⟨(T3.mem_dstarComp_symm h.std.stand.mem hM).1,
      hStar G Ω K K' z u J t W h hα hD hSigC hmu M hM⟩
  · rintro ⟨hMΩ, hMc⟩
    exact tqMembers_subset_dstarComp_gen h hMF h3s h3 hα M
      ⟨hMΩ, ExactLayer.mem_trivialOnQuot_of_le_centralizer hMc⟩

variable (p f) in
theorem c21_2_final_sect'' (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (h12 : C21_12 p f)
    (hMF : DStarConnectedTwinGen p f) (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n)
    (h13N : C21_13_N p f) (h14N : C21_14_N p f) (h14a : C21_14_alt p f) (h15 : C21_15 p f)
    (hStar : C21_StarCent p f) (hY : C21_YSigma p f) : C21_2 p f := by
  have hC3 : C21_3 p f := c21_3_of p f (twinFrameHyp51_of_cases hHz hHt hHu)
  have h4 : TwinNormAlpha p f := twinNormAlpha_of p f hC3
  have h13w : C21_13_wyl p f :=
    C21_13_wyl_of_star h12 (c21_13_star_of_sections_gen p f hMF h3s hC3)
  have h16 : C21_16 p f := c21_16_of_conj hE hC3 h4 h13N h14N
  have ha : C21_17_cent p f :=
    c21_17_cent_of' p f h14a hY (c21_17_tz_of_sections_gen p f hMF h3s hC3)
  have hb : C21_E_cent p f :=
    c21_E_cent_of' p f h14a hY (c21_E_star_of_starCent p f hMF h3s hC3 hStar)
  have h17 : C21_17 p f := c21_17_of_direct p f hE h13w h15 h16 ha hb
  have hEnd : C21_E p f := c21_E_of_direct p f hE h13w h15 h16 ha hb
  exact c21_2_of_steps (c21_setup p f) (c21_false_of_weak p f h13w h15 h16 h17 hEnd)

variable (p f) in
theorem c21_2_final_G (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (h13 : C21_13_N_ne p f) (h14 : C21_14_N_rest p f)
    (h14a : C21_14_alt_rest p f) (h15 : C21_15 p f) (hStar : C21_StarCent p f) :
    C21_2 p f := by
  by_cases hpq : p ≠ 2 ∧ 5 ≤ p ^ f
  · have hMF : DStarConnectedTwinGen p f :=
      dstarConnectedTwinGen_of smallNoThree G2D4Models.ih8G2D4_unconditional ih8D4Star hpq.1 hpq.2
    have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
      G2D4Models.h3s_of_nonToral_free hNT
    have hC3 : C21_3 p f := c21_3_of p f (twinFrameHyp51_of_cases (twinFrameHyp51z p f) hHt hHu)
    exact c21_2_final_sect'' p f (thmEWithSylow_of_nonToral f hNT) (twinFrameHyp51z p f) hHt hHu
      (c21_12_proved p f) hMF h3s (c21_13_N_of_ne hMF h3s hC3 h13) (c21_14_N_of_rest hC3 h14)
      (c21_14_alt_of_rest h14a) h15 hStar (c21_YSigma_of_sections p f h3s)
  · intro G _ _ _ Ω K K' z hs
    exact absurd ⟨hs.stand.odd, hs.stand.five⟩ hpq

end CFSG.ClassicalInvolution.Asc77
