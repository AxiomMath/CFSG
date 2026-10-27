module

public import CFSG.ClassicalInvolution.Asc77.AscT7ASectC

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_WylTrans' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G),
    Hyp21 p f Ω K K' z u J t W → MuIsoWylD4 Ω W → ∀ H : Subgroup G, rLayer Ω (t * z) ≤ H →
      sigmaGen Ω K ≤ H → ∀ M ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = M

variable {p f}

theorem C21_WylTrans.toWeak (h : C21_WylTrans p f) : C21_WylTrans' p f :=
  fun G _ _ _ Ω K K' z u J t W hh hmu H hD _ => h G Ω K K' z u J t W hh hmu H hD

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem dComp_eq_dstarComp_of_le_weak (h12 : C21_12 p f) (hWyl : C21_WylTrans' p f)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W)
    (hD : rLayer Ω (t * z) ≤ sigmaGen Ω K) : dComp Ω K = dstarComp Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  rcases h12 G Ω K K' z u J t W h with heq | hmu
  · exact heq
  · have hS := T7A.sigmaGen_le_sigmaNorm hΩ.conjInvariant hK
    have htr := hWyl G Ω K K' z u J t W h hmu (sigmaNorm Ω K) (hD.trans hS) hS
    ext M
    constructor
    · exact fun hM => T7A.mem_dstarComp_of_mem_dComp hp hΩ hM
    · intro hM
      obtain ⟨y, hy, rfl⟩ := htr M hM
      exact (hy K).mp Relation.ReflTransGen.refl

theorem sigmaGen_le_normalizer_alpha (hs : AlphaSteps p f) {K K' J W : Subgroup G}
    {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
    sigmaGen Ω K ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hK : K ∈ Ω := h.std.stand.mem
  have hKn : K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    hs.h4 G Ω K K' z u J t W h K (mem_twinSet_self hK h.std.hz)
  refine iSup₂_le fun M hM => ?_
  obtain ⟨x, hx, rfl⟩ := hs.exists_mem_normalizer h hM
  intro g hg
  rw [mem_conjSub_iff] at hg
  have h1 : x⁻¹ * g * x ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := hKn hg
  have h2 : x * (x⁻¹ * g * x) * x⁻¹ ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hx h1) (Subgroup.inv_mem _ hx)
  have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
  rwa [e] at h2

end Steps

variable (p f) in
theorem c21_16_of_weak (hE : ThmEWithSylow p f) (h3 : C21_3 p f) (h4 : TwinNormAlpha p f)
    (h12 : C21_12 p f) (h13 : C21_13_N p f) (h14 : C21_14_N p f) (hWyl : C21_WylTrans' p f) :
    C21_16 p f := by
  intro G _ _ _ Ω K K' z u J t W h
  by_contra hα
  have hs : AlphaSteps p f := ⟨h3, h4⟩
  have hstd := stdCent_normalizer_alpha' hs h13 h14 h
  have hD : rLayer Ω (t * z) ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    (rLayer_le_centralizer Ω (t * z)).trans (h13 G Ω K K' z u J t W h)
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G), conjSub x K = M := by
    rcases h12 G Ω K K' z u J t W h with heq | hWylD4
    · intro M hM
      rw [← heq] at hM
      exact hs.exists_mem_normalizer h hM
    · exact hWyl G Ω K K' z u J t W h hWylD4 _ hD (sigmaGen_le_normalizer_alpha hs h)
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

section Steps2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem frame_cent_sigmaStarNorm_weak (h12 : C21_12 p f) (h13 : C21_13_wyl p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans' p f) (ha : C21_17_cent p f)
    (hb : C21_E_cent p f) {K K' J W : Subgroup G} {z u t : G}
    (h : Hyp21 p f Ω K K' z u J t W) :
    Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K ∧
      Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  have hα := h16 G Ω K K' z u J t W h
  by_cases hD : rLayer Ω (t * z) ≤ sigmaGen Ω K
  · exact ha G Ω K K' z u J t W h hα hD (dComp_eq_dstarComp_of_le_weak h12 hWyl h hD)
  · have hSigC := h15 G Ω K K' z u J t W h hα hD
    have hmu : MuIsoWylD4 Ω W := h13 G Ω K K' z u J t W h hα hD
    obtain ⟨hstar, hu⟩ := hb G Ω K K' z u J t W h hα hD hSigC hmu
    exact ⟨T7A.centralizer_le_sigmaStarNorm_of_eq h.std.stand.hyp.conjInvariant hstar, hu⟩

theorem sigmaStarNorm_eq_top_weak (hE : ThmEWithSylow p f) (h12 : C21_12 p f)
    (h13 : C21_13_wyl p f) (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans' p f)
    (ha : C21_17_cent p f) (hb : C21_E_cent p f) {K K' J W : Subgroup G} {z u t : G}
    (h : Hyp21 p f Ω K K' z u J t W) : sigmaStarNorm Ω K = ⊤ := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have htail : StdCentTail Ω K (sigmaStarNorm Ω K) z :=
    stdCentTail_of_frames hp hq hΩ h fun {_ _ _ _ _ _} _ h₁ =>
      frame_cent_sigmaStarNorm_weak h12 h13 h15 h16 hWyl ha hb h₁
  have hstd := stdCent_sigmaStarNorm hp hq hΩ hK h.std.hz h.std.stand.trans htail
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ sigmaStarNorm Ω K, conjSub x K = M := by
    intro M hM
    obtain ⟨x, hx⟩ := h.std.stand.trans M (T3.mem_dstarComp_symm hK hM).1
    exact ⟨x, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hx ▸ hM), hx⟩
  exact thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd htrans

end Steps2

variable (p f) in
theorem c21_17_of_weak (hE : ThmEWithSylow p f) (h12 : C21_12 p f) (h13 : C21_13_wyl p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans' p f) (ha : C21_17_cent p f)
    (hb : C21_E_cent p f) : C21_17 p f := by
  intro G _ _ _ Ω K K' z u J t W h hD
  have htop := sigmaStarNorm_eq_top_weak hE h12 h13 h15 h16 hWyl ha hb h
  have hSig := dComp_eq_dstarComp_of_le_weak h12 hWyl h hD
  have hsn : sigmaNorm Ω K = ⊤ := by
    rw [← htop]
    ext g
    exact forall_congr' fun M => by rw [hSig]
  exact h.std.disconnected (dConnected_of_sigmaNorm_eq_top h.std.stand.mem h.std.stand.trans hsn)

variable (p f) in
theorem c21_E_of_weak (hE : ThmEWithSylow p f) (h12 : C21_12 p f) (h13 : C21_13_wyl p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans' p f) (ha : C21_17_cent p f)
    (hb : C21_E_cent p f) : C21_E p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have htop := sigmaStarNorm_eq_top_weak hE h12 h13 h15 h16 hWyl ha hb h
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
theorem c21_E_star_of_wylTrans_weak (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f)
    (hWyl : C21_WylTrans' p f) : C21_E_star p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu M
  constructor
  · intro hM
    refine ⟨(T3.mem_dstarComp_symm h.std.stand.mem hM).1, ?_⟩
    have hSig : sigmaGen Ω K ≤ Subgroup.centralizer ({t * z} : Set G) :=
      iSup₂_le fun N hN => hSigC N hN
    obtain ⟨c, hc, rfl⟩ :=
      hWyl G Ω K K' z u J t W h hmu _ (rLayer_le_centralizer Ω (t * z)) hSig M hM
    have hK : K ≤ Subgroup.centralizer ({t * z} : Set G) := hSigC K Relation.ReflTransGen.refl
    have hcc : c * (t * z) = (t * z) * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : (c⁻¹ * x * c) * (t * z) = (t * z) * (c⁻¹ * x * c) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hK hx)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hcinv : c⁻¹ * (t * z) = (t * z) * c⁻¹ := by
      calc c⁻¹ * (t * z) = c⁻¹ * ((t * z) * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * (t * z)) * c⁻¹ := by rw [hcc]
        _ = (t * z) * c⁻¹ := by group
    calc x * (t * z) = (c * (c⁻¹ * x * c) * c⁻¹) * (t * z) := by group
      _ = c * ((c⁻¹ * x * c) * (c⁻¹ * (t * z))) := by group
      _ = c * (((c⁻¹ * x * c) * (t * z)) * c⁻¹) := by rw [hcinv]; group
      _ = c * (((t * z) * (c⁻¹ * x * c)) * c⁻¹) := by rw [h1]
      _ = (c * (t * z)) * (c⁻¹ * x * c * c⁻¹) := by group
      _ = ((t * z) * c) * (c⁻¹ * x * c * c⁻¹) := by rw [hcc]
      _ = (t * z) * x := by group
  · rintro ⟨hMΩ, hMc⟩
    exact tqMembers_subset_dstarComp h hMF h3s h3 hα M
      ⟨hMΩ, ExactLayer.mem_trivialOnQuot_of_le_centralizer hMc⟩

variable (p f) in
theorem c21_2_final_sect' (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (h12 : C21_12 p f)
    (hMF : DStarConnectedTwin p f) (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n)
    (h13N : C21_13_N p f) (h14N : C21_14_N p f) (h14a : C21_14_alt p f) (h15 : C21_15 p f)
    (hWyl : C21_WylTrans' p f) (hY : C21_YSigma p f) : C21_2 p f := by
  have hC3 : C21_3 p f := c21_3_of p f (twinFrameHyp51_of_cases hHz hHt hHu)
  have h4 : TwinNormAlpha p f := twinNormAlpha_of p f hC3
  have h13w : C21_13_wyl p f :=
    C21_13_wyl_of_star h12 (c21_13_star_of_sections p f hMF h3s hC3)
  have h16 : C21_16 p f := c21_16_of_weak p f hE hC3 h4 h12 h13N h14N hWyl
  have ha : C21_17_cent p f :=
    c21_17_cent_of' p f h14a hY (c21_17_tz_of_sections p f hMF h3s hC3)
  have hb : C21_E_cent p f :=
    c21_E_cent_of' p f h14a hY (c21_E_star_of_wylTrans_weak p f hMF h3s hC3 hWyl)
  have h17 : C21_17 p f := c21_17_of_weak p f hE h12 h13w h15 h16 hWyl ha hb
  have hEnd : C21_E p f := c21_E_of_weak p f hE h12 h13w h15 h16 hWyl ha hb
  exact c21_2_of_steps (c21_setup p f) (c21_false_of_weak p f h13w h15 h16 h17 hEnd)

end CFSG.ClassicalInvolution.Asc77
