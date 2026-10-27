module

public import CFSG.ClassicalInvolution.Asc77.AscT7FE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.oddCore_centralizer_tz_le_normalizer_alpha (h : Hyp21 p f Ω K K' z u J t W)
    (hs : AlphaSteps p f) :
    oddCoreOf (Subgroup.centralizer ({t * z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  intro n hn
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hp hΩ
  have hcz : (t * z) * z = z * (t * z) := by
    calc (t * z) * z = (z * t) * z := by rw [hzt]
      _ = z * (t * z) := by group
  have h2 := oddCoreOf_centralizer_le_normalizer_alphaOf (c := t * z) (z := z) h.std.hz.sq
    h.tz_ne_one hcz hn
  rwa [closure_tz_pair, hs.alpha_zt h] at h2

theorem Hyp21.normalizer_le_normalizer_alpha (h : Hyp21 p f Ω K K' z u J t W)
    (hs : AlphaSteps p f) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := fun _ hn =>
  mem_normalizer_iff_conjSub_eq.mpr (hs.conj_alpha_of_mem_centralizer h
    (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn))))

theorem Hyp21.centralizer_tz_le_normalizer_alpha_of_M (h : Hyp21 p f Ω K K' z u J t W)
    (hMF : DStarConnectedTwinGen p f) (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n)
    (hs : AlphaSteps p f) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hM : MGrp Ω W ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G)) :
    Subgroup.centralizer ({t * z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  intro c' hc'
  have h1 : conjSub c' K ∈ tqMembers Ω (t * z) :=
    conjSub_mem_tqMembers hΩ.conjInvariant hc' h.mem_tqMembers_tz_K
  obtain ⟨n, hn, J', -, hJ'd, hMeq⟩ := exists_conj_tqMembers_of_connected hp hq hΩ h.tz_sq
    h.mem_tqMembers_tz_K (h.sectionConnected_tz hMF h3s) _ h1
  have hnα := h.oddCore_centralizer_tz_le_normalizer_alpha hs hn
  obtain ⟨x, hxN, hx⟩ :=
    h.exists_mem_conj_of_dstarComp hne hM (h.normalizer_le_normalizer_alpha hs) J' hJ'd
  have hc'eq : conjSub c' K = conjSub (n * x) K := by rw [hMeq, ← hx, conjSub_mul]
  have hm : conjSub ((n * x)⁻¹ * c') K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmα : (n * x)⁻¹ * c' ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr
      (hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq hm)))
  have e : c' = (n * x) * ((n * x)⁻¹ * c') := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnα hxN) hmα

theorem Hyp21.centralizer_u_le_normalizer_alpha_of_M (h : Hyp21 p f Ω K K' z u J t W)
    (hs : AlphaSteps p f) (hne : dComp Ω K ≠ dstarComp Ω K) (hconn : SectionConnected Ω u)
    (hM : MGrp Ω W ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G)) :
    Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := exists_mem_tqMembers_u hp hq hΩ hK hz h.std.hK' h.std.hne h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := T7A.mem_dstarComp_of_mem_dComp hp hΩ hJ₀d
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ tqMembers Ω u :=
    conjSub_mem_tqMembers hΩ.conjInvariant hc' hJ₀t
  obtain ⟨n, hn, J', -, hJ'd, hMeq⟩ :=
    exists_conj_tqMembers_of_connected hp hq hΩ h.hu2 hJ₀t hconn _ h1
  have hnα : n ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    oddCoreOf_centralizer_le_normalizer_alphaOf h.std.hz.sq h.hu1 h.u_comm_z hn
  have hJ'ds : J' ∈ dstarComp Ω K := by
    rw [T7A.dstarComp_eq_of_mem hK hJ₀ds] at hJ'd
    exact hJ'd
  obtain ⟨x, hxN, hx⟩ :=
    h.exists_mem_conj_of_dstarComp hne hM (h.normalizer_le_normalizer_alpha hs) J' hJ'ds
  obtain ⟨x₀, hx₀N, hx₀⟩ := hs.exists_mem_normalizer h hJ₀d
  have hc'eq : conjSub (c' * x₀) K = conjSub (n * x) K := by
    rw [conjSub_mul, hx₀, hMeq, ← hx, conjSub_mul]
  have hm : conjSub ((n * x)⁻¹ * (c' * x₀)) K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmα : (n * x)⁻¹ * (c' * x₀) ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr
      (hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (hz.conj_eq hm)))
  have e : c' = ((n * x) * ((n * x)⁻¹ * (c' * x₀))) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnα hxN) hmα)
    (Subgroup.inv_mem _ hx₀N)

end Frame

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_13_M_ne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      dComp Ω K ≠ dstarComp Ω K →
        MGrp Ω W ≤ Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_N_disc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      ¬ SectionConnected Ω u →
        Subgroup.centralizer ({u} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

variable {p f}

theorem c21_13_N_ne_of_M (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (hC3 : C21_3 p f)
    (h : C21_13_M_ne p f) : C21_13_N_ne p f := by
  intro G _ _ _ Ω K K' z u J t W hh hne
  exact hh.centralizer_tz_le_normalizer_alpha_of_M hMF h3s ⟨hC3, twinNormAlpha_of p f hC3⟩ hne
    (h G Ω K K' z u J t W hh hne)

theorem c21_14_N_rest_of (hC3 : C21_3 p f) (hM : C21_13_M_ne p f) (hd : C21_14_N_disc p f) :
    C21_14_N_rest p f := by
  intro G _ _ _ Ω K K' z u J t W hh hgood
  by_cases hconn : SectionConnected Ω u
  · have hne : dComp Ω K ≠ dstarComp Ω K := fun heq => hgood ⟨heq, hconn⟩
    exact hh.centralizer_u_le_normalizer_alpha_of_M ⟨hC3, twinNormAlpha_of p f hC3⟩ hne hconn
      (hM G Ω K K' z u J t W hh hne)
  · exact hd G Ω K K' z u J t W hh hconn

variable (p f) in
theorem c21_2_final_residual (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (h13 : C21_13_M_ne p f) (h14 : C21_14_N_disc p f)
    (h14a : C21_14_alt_rest p f) (h15 : C21_15 p f) (hStar : C21_StarCent p f) :
    C21_2 p f := by
  by_cases hpq : p ≠ 2 ∧ 5 ≤ p ^ f
  · have hMF : DStarConnectedTwinGen p f :=
      dstarConnectedTwinGen_of smallNoThree G2D4Models.ih8G2D4_unconditional ih8D4Star hpq.1 hpq.2
    have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
      G2D4Models.h3s_of_nonToral_free hNT
    have hC3 : C21_3 p f := c21_3_of p f (twinFrameHyp51_of_cases (twinFrameHyp51z p f) hHt hHu)
    exact c21_2_final_G p f hNT hHt hHu (c21_13_N_ne_of_M hMF h3s hC3 h13)
      (c21_14_N_rest_of hC3 h13 h14) h14a h15 hStar
  · intro G _ _ _ Ω K K' z hs
    exact absurd ⟨hs.stand.odd, hs.stand.five⟩ hpq

end CFSG.ClassicalInvolution.Asc77
