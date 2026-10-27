module

public import CFSG.ClassicalInvolution.Asc77.AscT7AExclude
public import CFSG.ClassicalInvolution.Asc77.AscT7AAlphaTwin
public import CFSG.ClassicalInvolution.Asc77.AscT7AStep14

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_13_N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      Subgroup.centralizer ({t * z} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_13_wyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        MuIsoWylD4 Ω W

@[expose] def C21_14_alt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ →
        rLayer Ω u ≤ sigmaGen Ω K ∨
          Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)

variable {p f}

theorem C21_13.toN (h : C21_13 p f) : C21_13_N p f := fun G _ _ _ Ω K K' z u J t W hh =>
  (h G Ω K K' z u J t W hh).1

theorem C21_14.toN (h : C21_14 p f) : C21_14_N p f := fun G _ _ _ Ω K K' z u J t W hh =>
  (h G Ω K K' z u J t W hh).1

theorem C21_13.toWyl (h : C21_13 p f) : C21_13_wyl p f := by
  intro G _ _ _ Ω K K' z u J t W hh hα hD
  obtain ⟨-, h13'⟩ := h G Ω K K' z u J t W hh
  rw [hα, bot_sup_eq] at h13'
  rcases h13' with hle | ⟨hmu, -⟩
  · exact absurd hle hD
  · exact hmu

theorem C21_14.toAlt (h : C21_14 p f) : C21_14_alt p f := by
  intro G _ _ _ Ω K K' z u J t W hh hα
  obtain ⟨-, h14'⟩ := h G Ω K K' z u J t W hh
  simp only [hα, bot_sup_eq] at h14'
  rcases h14' with h1 | ⟨-, -, h3⟩
  · exact Or.inl h1
  · exact Or.inr h3

section Weak

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem stdCent_normalizer_alpha' (hs : AlphaSteps p f) (h13 : C21_13_N p f)
    (h14 : C21_14_N p f) {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
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
  · intro L hL J'' hJ'' z'' hz'' hzz
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
      have h13' := h13 G Ω K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ h'
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

variable (p f) in
theorem c21_16_of' (hE : ThmEWithSylow p f) (h3 : C21_3 p f) (h4 : TwinNormAlpha p f)
    (h12 : C21_12 p f) (h13 : C21_13_N p f) (h14 : C21_14_N p f) (hWyl : C21_WylTrans p f) :
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

section Weak2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem centralizer_u_le_sigmaStarNorm' (h14 : C21_14_alt p f) (hY : C21_YSigma p f)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (htz : Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K) :
    Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  rcases h14 G Ω K K' z u J t W h hα with h1 | h3
  · exact hY G Ω K K' z u J t W h hα h1 htz
  · exact h3.trans htz

variable (p f) in
theorem c21_17_cent_of' (h14 : C21_14_alt p f) (hY : C21_YSigma p f) (ha : C21_17_tz p f) :
    C21_17_cent p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSig
  have htz := ha G Ω K K' z u J t W h hα hD hSig
  exact ⟨htz, centralizer_u_le_sigmaStarNorm' h14 hY h hα htz⟩

variable (p f) in
theorem c21_E_cent_of' (h14 : C21_14_alt p f) (hY : C21_YSigma p f) (hb : C21_E_star p f) :
    C21_E_cent p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu
  have hstar := hb G Ω K K' z u J t W h hα hD hSigC hmu
  have htz := T7A.centralizer_le_sigmaStarNorm_of_eq h.std.stand.hyp.conjInvariant hstar
  exact ⟨hstar, centralizer_u_le_sigmaStarNorm' h14 hY h hα htz⟩

theorem frame_cent_sigmaStarNorm' (h12 : C21_12 p f) (h13 : C21_13_wyl p f) (h15 : C21_15 p f)
    (h16 : C21_16 p f) (hWyl : C21_WylTrans p f) (ha : C21_17_cent p f) (hb : C21_E_cent p f)
    {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
    Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K ∧
      Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  have hα := h16 G Ω K K' z u J t W h
  by_cases hD : rLayer Ω (t * z) ≤ sigmaGen Ω K
  · exact ha G Ω K K' z u J t W h hα hD (dComp_eq_dstarComp_of_le h12 hWyl h hD)
  · have hSigC := h15 G Ω K K' z u J t W h hα hD
    have hmu : MuIsoWylD4 Ω W := h13 G Ω K K' z u J t W h hα hD
    obtain ⟨hstar, hu⟩ := hb G Ω K K' z u J t W h hα hD hSigC hmu
    exact ⟨T7A.centralizer_le_sigmaStarNorm_of_eq h.std.stand.hyp.conjInvariant hstar, hu⟩

theorem sigmaStarNorm_eq_top' (hE : ThmEWithSylow p f) (h12 : C21_12 p f)
    (h13 : C21_13_wyl p f) (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans p f)
    (ha : C21_17_cent p f) (hb : C21_E_cent p f) {K K' J W : Subgroup G} {z u t : G}
    (h : Hyp21 p f Ω K K' z u J t W) : sigmaStarNorm Ω K = ⊤ := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have htail : StdCentTail Ω K (sigmaStarNorm Ω K) z :=
    stdCentTail_of_frames hp hq hΩ h fun {_ _ _ _ _ _} _ h₁ =>
      frame_cent_sigmaStarNorm' h12 h13 h15 h16 hWyl ha hb h₁
  have hstd := stdCent_sigmaStarNorm hp hq hΩ hK h.std.hz h.std.stand.trans htail
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ sigmaStarNorm Ω K, conjSub x K = M := by
    intro M hM
    obtain ⟨x, hx⟩ := h.std.stand.trans M (T3.mem_dstarComp_symm hK hM).1
    exact ⟨x, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hx ▸ hM), hx⟩
  exact thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd htrans

end Weak2

variable (p f) in
theorem c21_17_of' (hE : ThmEWithSylow p f) (h12 : C21_12 p f) (h13 : C21_13_wyl p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans p f) (ha : C21_17_cent p f)
    (hb : C21_E_cent p f) : C21_17 p f := by
  intro G _ _ _ Ω K K' z u J t W h hD
  have htop := sigmaStarNorm_eq_top' hE h12 h13 h15 h16 hWyl ha hb h
  have hSig := dComp_eq_dstarComp_of_le h12 hWyl h hD
  have hsn : sigmaNorm Ω K = ⊤ := by
    rw [← htop]
    ext g
    exact forall_congr' fun M => by rw [hSig]
  exact h.std.disconnected (dConnected_of_sigmaNorm_eq_top h.std.stand.mem h.std.stand.trans hsn)

variable (p f) in
theorem c21_E_of' (hE : ThmEWithSylow p f) (h12 : C21_12 p f) (h13 : C21_13_wyl p f)
    (h15 : C21_15 p f) (h16 : C21_16 p f) (hWyl : C21_WylTrans p f) (ha : C21_17_cent p f)
    (hb : C21_E_cent p f) : C21_E p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have htop := sigmaStarNorm_eq_top' hE h12 h13 h15 h16 hWyl ha hb h
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
theorem c21_false_of_weak (h13 : C21_13_wyl p f) (h15 : C21_15 p f) (h16 : C21_16 p f)
    (h17 : C21_17 p f) (hE : C21_E p f) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
      (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G),
      Hyp21 p f Ω K K' z u J t W → False := by
  intro G _ _ _ Ω K K' z u J t W h
  have hα := h16 G Ω K K' z u J t W h
  have hD := h17 G Ω K K' z u J t W h
  exact hE G Ω K K' z u J t W h hα hD (h15 G Ω K K' z u J t W h hα hD)
    (h13 G Ω K K' z u J t W h hα hD)

variable (p f) in
theorem c21_2_final' (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (h12 : C21_12 p f)
    (h13N : C21_13_N p f) (h13w : C21_13_wyl p f) (h14N : C21_14_N p f) (h14a : C21_14_alt p f)
    (h15 : C21_15 p f) (hWyl : C21_WylTrans p f) (hY : C21_YSigma p f) (h17t : C21_17_tz p f)
    (hEs : C21_E_star p f) : C21_2 p f := by
  have h3 : C21_3 p f := c21_3_of p f (twinFrameHyp51_of_cases hHz hHt hHu)
  have h4 : TwinNormAlpha p f := twinNormAlpha_of p f h3
  have h16 : C21_16 p f := c21_16_of' p f hE h3 h4 h12 h13N h14N hWyl
  have ha : C21_17_cent p f := c21_17_cent_of' p f h14a hY h17t
  have hb : C21_E_cent p f := c21_E_cent_of' p f h14a hY hEs
  have h17 : C21_17 p f := c21_17_of' p f hE h12 h13w h15 h16 hWyl ha hb
  have hEnd : C21_E p f := c21_E_of' p f hE h12 h13w h15 h16 hWyl ha hb
  exact c21_2_of_steps (c21_setup p f)
    (c21_false_of_weak p f h13w h15 h16 h17 hEnd)

variable (p f) in
theorem c21_2_final_primitive (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (h1 : ThompsonCube p f)
    (h2 : ThompsonStar p f) (h3 : ThompsonClique p f) (h752 : L7_5_2 p f)
    (h5 : ThompsonGraph p f) (h13N : C21_13_N p f) (h13w : C21_13_wyl p f)
    (h14N : C21_14_N p f) (h14a : C21_14_alt p f) (h15 : C21_15 p f) (hWyl : C21_WylTrans p f)
    (hY : C21_YSigma p f) (h17t : C21_17_tz p f) (hEs : C21_E_star p f) : C21_2 p f :=
  c21_2_final' p f hE hHz hHt hHu (c21_12_of_inputs p f h1 h2 h3 h752 h5) h13N h13w h14N h14a
    h15 hWyl hY h17t hEs

end CFSG.ClassicalInvolution.Asc77
