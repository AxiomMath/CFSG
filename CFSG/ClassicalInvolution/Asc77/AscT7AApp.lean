module

public import CFSG.ClassicalInvolution.Asc77.AscT7AAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)}

theorem AlphaSteps.twin_sup_le (hs : AlphaSteps p f) {K K' J W L L' : Subgroup G} {z u t : G}
    (h : Hyp21 p f Ω K K' z u J t W) (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) :
    ∀ g ∈ L ⊔ L', conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hmem := hs.h4 G Ω K K' z u J t W h
  intro g hg
  exact mem_normalizer_iff_conjSub_eq.mp ((sup_le (hmem L hL) (hmem L' hL')) hg)

theorem stdCent_normalizer_alpha (hs : AlphaSteps p f) (h13 : C21_13 p f) (h14 : C21_14 p f)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
    StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G)) z := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
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
  ·
    intro L hL J'' hJ'' z'' hz'' hzz
    have hLΩ : L ∈ Ω := hL.1
    have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz hL
    have hKL := (l6_3 p f hp hq G Ω hΩ K hK L hL).1
    have hJperp : J'' ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ''
    have hnot : J'' ∉ twinSet Ω K := by
      rintro ⟨-, z₀, hz₀K, hz₀J⟩
      exact hzz ((hz₀J.eq hz'').symm.trans (h.std.hz.eq hz₀K).symm)
    have hJmem : J'' ∈ omegaOfSet Ω (twinSet Ω K) :=
      T7A.mem_omegaOfSet_of_mem_kPerp hp hq hΩ hK hJperp hnot
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
        exists_twinFrameData_at hp hq hΩ hK h.std.hz h.std.hK' h.std.hne h.hu h.hu2 h.hu1 h.huz
          hJmem hz''
      have h' : Hyp21 p f Ω K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ :=
        Hyp21.of_twinFrameData h.std hfr hW₁ hzW₁ htW₁
      have h13' := (h13 G Ω K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ h').1
      have hcomm : z * (g * z'' * g⁻¹) = (g * z'' * g⁻¹) * z :=
        hfr.comm_zt hp hΩ
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
      exists_twinFrameData_of_sylows hp hq hΩ hLΩ hzL hL'L hne hJL h.ht hR₁ hR₂ hc
    have hfr' := hfr x hx y hy hx4 hy4
    have h' : Hyp21 p f Ω L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ :=
      Hyp21.of_twinFrameData (Std7.of_twin h.std hL hL' hne) hfr' hW₂ hzW₂ htW₂
    have h14' := (h14 G Ω L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ h').1
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

omit [Finite G] [IsSimpleGroup G] in
theorem rLayer_le_centralizer (Ω : Set (Subgroup G)) (x : G) :
    rLayer Ω x ≤ Subgroup.centralizer ({x} : Set G) := by
  unfold rLayer
  exact iSup₂_le fun R _ => iSup_le fun hR => hR

variable (p f) in
@[expose] def C21_WylTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G),
    Hyp21 p f Ω K K' z u J t W → MuIsoWylD4 Ω W → ∀ H : Subgroup G, rLayer Ω (t * z) ≤ H →
      ∀ M ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = M

variable (p f) in
theorem c21_16_of (hE : ThmEWithSylow p f) (h3 : C21_3 p f) (h4 : TwinNormAlpha p f)
    (h12 : C21_12 p f)
    (h13 : C21_13 p f) (h14 : C21_14 p f) (hWyl : C21_WylTrans p f) : C21_16 p f := by
  intro G _ _ _ Ω K K' z u J t W h
  by_contra hα
  have hs : AlphaSteps p f := ⟨h3, h4⟩
  have hstd := stdCent_normalizer_alpha hs h13 h14 h
  have hD : rLayer Ω (t * z) ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    (rLayer_le_centralizer Ω (t * z)).trans ((h13 G Ω K K' z u J t W h).1)
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G), conjSub x K = M := by
    rcases h12 G Ω K K' z u J t W h with heq | hWylD4
    · intro M hM
      rw [← heq] at hM
      exact hs.exists_mem_normalizer h hM
    · exact hWyl G Ω K K' z u J t W h hWylD4 _ hD
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

end CFSG.ClassicalInvolution.Asc77
