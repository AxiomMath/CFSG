module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2202
public import CFSG.ClassicalInvolution.Q3.Q3T7W21A02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C21_13_N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      Subgroup.centralizer ({t * z} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_13_wyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        MuIsoWylD4 Ω W

@[expose] def C21_14_alt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ →
        ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K ∨
          Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)
section Weak
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem stdCent_normalizer_alpha'
    (hs
    : Q3T8.Asc77.AlphaSteps) (h13 : Q3T8.Asc77.C21_13_N)
    (h14 : Q3T8.Asc77.C21_14_N) {K K' J W : Subgroup G} {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z
        u J t W) :
    StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G)) z := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hzK' := isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK'
  have hQα := hs.sup_le_normalizer h
  have hzQ : ∀ g ∈ K ⊔ K', g * z * g⁻¹ = z := fun g hg => by
    have := T7A.z_comm_of_mem_sup h.std.hz hzK' hg
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [← this]
      _ = z := by group
  have hz_le : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := fun c hc =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.conj_alpha_of_mem_centralizer h hc)
  refine ⟨hz_le, ?_, ?_⟩
  · intro L hL J'' hJ'' z'' hz'' hzz
    have hKL := (CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK L hL).1
    have hJperp : J'' ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ''
    have hnot : J'' ∉ twinSet Ω K := by
      rintro ⟨-, z₀, hz₀K, hz₀J⟩
      exact hzz ((hz₀J.eq hz'').symm.trans (h.std.hz.eq hz₀K).symm)
    have hJmem : J'' ∈ omegaOfSet Ω (twinSet Ω K) :=
      Q3T8.Asc77.T7A.mem_omegaOfSet_of_mem_kPerp hΩ hK hJperp hnot
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hyN, hy⟩ := hs.exists_mem_normalizer h (T7A.mem_dComp_of_mem_kPerp hJperp)
      have hzy : IsUniqueInvolution J'' (y * z * y⁻¹) := hy ▸ h.std.hz.conj y
      have hz''eq : z'' = y * z * y⁻¹ := hz''.eq hzy
      intro c hc
      have hc' : y⁻¹ * c * y ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        rw [hz''eq] at hc
        calc (y⁻¹ * c * y) * z = y⁻¹ * (c * (y * z * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * z * y⁻¹) * c) * y := by rw [hc]
          _ = z * (y⁻¹ * c * y) := by group
      have h1 := hz_le hc'
      have h2 : y * (y⁻¹ * c * y) * y⁻¹ ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN h1) (Subgroup.inv_mem _ hyN)
      have e : y * (y⁻¹ * c * y) * y⁻¹ = c := by group
      rwa [e] at h2
    · obtain ⟨g, hgQ, W₁, hfr, hW₁, hzW₁, htW₁⟩ :=
        Q3T8.Asc77.exists_twinFrameData_at hΩ hK h.std.hz h.std.hK' h.std.hne h.hu h.hu2 h.hu1 h.huz
          hJmem hz''
      have h' : Q3T8.Asc77.Hyp21 Ω K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ :=
        Q3T8.Asc77.Hyp21.of_twinFrameData h.std hfr hW₁ hzW₁ htW₁
      have h13' := h13 G Ω K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ h'
      have hcomm : z * (g * z'' * g⁻¹) = (g * z'' * g⁻¹) * z :=
        hfr.comm_zt hΩ
      have hgN : g ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
        mem_normalizer_iff_conjSub_eq.mpr (hQα g hgQ)
      intro c hc
      have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer ({(g * z'' * g⁻¹) * z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        have e1 : (g * z'' * g⁻¹) * z = g * (z * z'') * g⁻¹ := by
          calc (g * z'' * g⁻¹) * z = z * (g * z'' * g⁻¹) := hcomm.symm
            _ = (g * z * g⁻¹) * (g * z'' * g⁻¹) := by rw [hzQ g hgQ]
            _ = g * (z * z'') * g⁻¹ := by group
        rw [e1]
        calc (g * c * g⁻¹) * (g * (z * z'') * g⁻¹) = g * (c * (z * z'')) * g⁻¹ := by group
          _ = g * ((z * z'') * c) * g⁻¹ := by rw [hc]
          _ = (g * (z * z'') * g⁻¹) * (g * c * g⁻¹) := by group
      have h2 := h13' hc'
      have h3 : g⁻¹ * (g * c * g⁻¹) * g ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) h2) hgN
      have e : g⁻¹ * (g * c * g⁻¹) * g = c := by group
      rwa [e] at h3
  · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
    have hLΩ : L ∈ Ω := hL.1
    have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz hL
    have hzL' := isUniqueInvolution_of_mem_twinSet h.std.hz hL'
    have htwL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet h.std.hz hL
    have hL'L : L' ∈ twinSet Ω L := by rw [htwL]; exact hL'
    have hJL : J ∈ omegaOfSet Ω (twinSet Ω L) := by rw [htwL]; exact h.hJ
    obtain ⟨g, hgQ, W₂, hJg, htg, hW₂, hzW₂, htW₂, hfr⟩ :=
      Q3T8.Asc77.exists_twinFrameData_of_sylows hΩ hLΩ hzL hL'L hne hJL h.ht hR₁ hR₂ hc
    have hfr' := hfr x hx y hy hx4 hy4
    have h' : Q3T8.Asc77.Hyp21 Ω L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ :=
      Q3T8.Asc77.Hyp21.of_twinFrameData (Q3T8.Asc77.Std7.of_twin h.std hL hL' hne) hfr' hW₂ hzW₂
          htW₂
    have h14' := h14 G Ω L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ h'
    have hα1 := hs.alpha_zt h'
    have hgz : g * z * g⁻¹ = z := by
      have := T7A.z_comm_of_mem_sup hzL hzL' hgQ
      calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
        _ = (z * g) * g⁻¹ := by rw [← this]
        _ = z := by group
    have h2 : conjSub g (Subgroup.closure ({z, t} : Set G)) =
        Subgroup.closure ({z, g * t * g⁻¹} : Set G) := by
      rw [T7A.conjSub_closure_pair, hgz]
    have hαz := hs.alpha_zt h
    have hαeq : alphaOf (Subgroup.closure ({x * y, z} : Set G)) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := by
      rw [← hα1, ← h2, alphaOf_conjSub, hαz]
      exact hs.twin_sup_le h hL hL' g hgQ
    rw [hαeq] at h14'
    exact h14'
end Weak
section Weak2
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem centralizer_u_le_sigmaStarNorm'
    (h14 : Q3T8.Asc77.C21_14_alt) (hY : Q3T8.Asc77.C21_YSigma)
    {K K' J W : Subgroup G} {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (htz : Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K) :
    Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  rcases h14 G Ω K K' z u J t W h hα with h1 | h3
  · exact hY G Ω K K' z u J t W h hα h1 htz
  · exact h3.trans htz

theorem c21_17_cent_of'
    (h14 : Q3T8.Asc77.C21_14_alt) (hY : Q3T8.Asc77.C21_YSigma) (ha : Q3T8.Asc77.C21_17_tz) :
    Q3T8.Asc77.C21_17_cent := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSig
  have htz := ha G Ω K K' z u J t W h hα hD hSig
  exact ⟨htz, Q3T8.Asc77.centralizer_u_le_sigmaStarNorm' h14 hY h hα htz⟩

theorem c21_E_cent_of'
    (h14 : Q3T8.Asc77.C21_14_alt) (hY : Q3T8.Asc77.C21_YSigma) (hb : Q3T8.Asc77.C21_E_star) :
    Q3T8.Asc77.C21_E_cent := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu
  have hstar := hb G Ω K K' z u J t W h hα hD hSigC hmu
  have htz := T7A.centralizer_le_sigmaStarNorm_of_eq h.std.stand.hyp.conjInvariant hstar
  exact ⟨hstar, Q3T8.Asc77.centralizer_u_le_sigmaStarNorm' h14 hY h hα htz⟩
end Weak2

theorem c21_false_of_weak
    (h13 : Q3T8.Asc77.C21_13_wyl) (h15 : Q3T8.Asc77.C21_15) (h16 : Q3T8.Asc77.C21_16)
    (h17 : Q3T8.Asc77.C21_17) (hE : Q3T8.Asc77.C21_E) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
      (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G),
      Q3T8.Asc77.Hyp21 Ω K K' z u J t W → False := by
  intro G _ _ _ Ω K K' z u J t W h
  have hα := h16 G Ω K K' z u J t W h
  have hD := h17 G Ω K K' z u J t W h
  exact hE G Ω K K' z u J t W h hα hD (h15 G Ω K K' z u J t W h hα hD)
    (h13 G Ω K K' z u J t W h hα hD)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C21_13_star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        dComp Ω K ≠ dstarComp Ω K

theorem C21_13_wyl_of_star
    (h12 : Q3T8.Asc77.C21_12) (h : Q3T8.Asc77.C21_13_star) : Q3T8.Asc77.C21_13_wyl := by
  intro G _ _ _ Ω K K' z u J t W hh hα hD
  rcases h12 G Ω K K' z u J t W hh with heq | hmu
  · exact absurd heq (h G Ω K K' z u J t W hh hα hD)
  · exact hmu
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C21_StarCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        (∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) → MuIsoWylD4 Ω W →
          ∀ M ∈ dstarComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)

theorem c21_16_of_conj
    (hE
    : Q3T7E.ThmEWithSylow3) (h3 : Q3T8.Asc77.C21_3) (h4 : Q3T8.Asc77.TwinNormAlpha)
    (h13 : Q3T8.Asc77.C21_13_N) (h14 : Q3T8.Asc77.C21_14_N) : Q3T8.Asc77.C21_16 := by
  intro G _ _ _ Ω K K' z u J t W h
  by_contra hα
  have hs : Q3T8.Asc77.AlphaSteps := ⟨h3, h4⟩
  have hstd := Q3T8.Asc77.stdCent_normalizer_alpha' hs h13 h14 h
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
  have htop := Q3T8.Asc77.thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd htrans
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

theorem frame_cent_sigmaStarNorm_direct
    (h13 : Q3T8.Asc77.C21_13_wyl) (h15 : Q3T8.Asc77.C21_15)
    (h16 : Q3T8.Asc77.C21_16) (ha : Q3T8.Asc77.C21_17_cent) (hb : Q3T8.Asc77.C21_E_cent) {K K' J W
        : Subgroup G}
    {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K ∧
      Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  have hα := h16 G Ω K K' z u J t W h
  by_cases hD : rLayer Ω (t * z) ≤ sigmaGen Ω K
  · exact ha G Ω K K' z u J t W h hα hD (Q3T8.Asc77.dComp_eq_dstarComp_of_rLayer_le h hD)
  · have hSigC := h15 G Ω K K' z u J t W h hα hD
    have hmu : MuIsoWylD4 Ω W := h13 G Ω K K' z u J t W h hα hD
    obtain ⟨hstar, hu⟩ := hb G Ω K K' z u J t W h hα hD hSigC hmu
    exact ⟨T7A.centralizer_le_sigmaStarNorm_of_eq h.std.stand.hyp.conjInvariant hstar, hu⟩

theorem sigmaStarNorm_eq_top_direct
    (hE
    : Q3T7E.ThmEWithSylow3) (h13 : Q3T8.Asc77.C21_13_wyl)
    (h15 : Q3T8.Asc77.C21_15) (h16 : Q3T8.Asc77.C21_16) (ha : Q3T8.Asc77.C21_17_cent) (hb :
        Q3T8.Asc77.C21_E_cent)
    {K K' J W : Subgroup G} {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    sigmaStarNorm Ω K = ⊤ := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have htail : StdCentTail Ω K (sigmaStarNorm Ω K) z :=
    Q3T8.Asc77.stdCentTail_of_frames hΩ h fun {_ _ _ _ _ _} _ h₁ =>
      Q3T8.Asc77.frame_cent_sigmaStarNorm_direct h13 h15 h16 ha hb h₁
  have hstd := Q3T8.Asc77.stdCent_sigmaStarNorm hΩ hK h.std.hz h.std.stand.trans htail
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ sigmaStarNorm Ω K, conjSub x K = M := by
    intro M hM
    obtain ⟨x, hx⟩ := h.std.stand.trans M (T3.mem_dstarComp_symm hK hM).1
    exact ⟨x, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hx ▸ hM), hx⟩
  exact Q3T8.Asc77.thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd htrans
end Steps

theorem c21_17_of_direct
    (hE
    : Q3T7E.ThmEWithSylow3) (h13 : Q3T8.Asc77.C21_13_wyl) (h15 : Q3T8.Asc77.C21_15)
    (h16 : Q3T8.Asc77.C21_16) (ha : Q3T8.Asc77.C21_17_cent) (hb : Q3T8.Asc77.C21_E_cent) :
        Q3T8.Asc77.C21_17 := by
  intro G _ _ _ Ω K K' z u J t W h hD
  have htop := Q3T8.Asc77.sigmaStarNorm_eq_top_direct hE h13 h15 h16 ha hb h
  have hSig := Q3T8.Asc77.dComp_eq_dstarComp_of_rLayer_le h hD
  have hsn : sigmaNorm Ω K = ⊤ := by
    rw [← htop]
    ext g
    exact forall_congr' fun M => by rw [hSig]
  exact h.std.disconnected (dConnected_of_sigmaNorm_eq_top h.std.stand.mem h.std.stand.trans hsn)

theorem c21_E_of_direct
    (hE
    : Q3T7E.ThmEWithSylow3) (h13 : Q3T8.Asc77.C21_13_wyl) (h15 : Q3T8.Asc77.C21_15)
    (h16 : Q3T8.Asc77.C21_16) (ha : Q3T8.Asc77.C21_17_cent) (hb : Q3T8.Asc77.C21_E_cent) :
        Q3T8.Asc77.C21_E := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have htop := Q3T8.Asc77.sigmaStarNorm_eq_top_direct hE h13 h15 h16 ha hb h
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
  obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hVR).exists_not_commute
  have h1 : t * z = 1 := T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm
  have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.std.hz.sq
  exact h.twinFrameData.t_ne_z (h2.trans h3)

theorem c21_2_final_sect''
    (hE : Q3T7E.ThmEWithSylow3) (hHz : TwinFrameHyp51z)
    (hHt : TwinFrameHyp51t) (hHu : TwinFrameHyp51u) (h12 : C21_12)
    (h13s : C21_13_star) (h17tz : C21_17_tz) (hEstar : C21_E_star)
    (h13N : C21_13_N) (h14N : C21_14_N) (h14a : C21_14_alt) (h15 : C21_15)
    (hY : C21_YSigma) : C21_2 := by
  have hC3 : C21_3 := c21_3_of (twinFrameHyp51_of_cases hHz hHt hHu)
  have h4 : TwinNormAlpha := twinNormAlpha_of hC3
  have h13w : C21_13_wyl := C21_13_wyl_of_star h12 h13s
  have h16 : C21_16 := c21_16_of_conj hE hC3 h4 h13N h14N
  have ha : C21_17_cent := c21_17_cent_of' h14a hY h17tz
  have hb : C21_E_cent := c21_E_cent_of' h14a hY hEstar
  have h17 : C21_17 := c21_17_of_direct hE h13w h15 h16 ha hb
  have hEnd : C21_E := c21_E_of_direct hE h13w h15 h16 ha hb
  exact c21_2_of_steps c21_setup (c21_false_of_weak h13w h15 h16 h17 hEnd)

end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
