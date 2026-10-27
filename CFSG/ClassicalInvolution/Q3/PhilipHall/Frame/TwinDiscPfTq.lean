module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscClaims

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

namespace TwinDisc

section SylCent

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def SylCent (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) :=
  {M | M ∈ Ω ∧ ∃ T : Subgroup G, IsSylow2In T M ∧ T ≤ Subgroup.centralizer ({c} : Set G)}

theorem conjSub_mem_sylCent (hΩ : ConjInvariant Ω) {c g : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) {M : Subgroup G} (hM : M ∈ SylCent Ω c) :
    conjSub g M ∈ SylCent Ω c := by
  obtain ⟨hMΩ, T, hT, hTc⟩ := hM
  exact ⟨hΩ g M hMΩ, conjSub g T, hT.conj g, T7A.conjSub_le_of_mem hg hTc⟩

theorem mem_sylCent_tz_J (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) : J ∈ SylCent Ω (t * z) := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ.2 K (mem_twinSet_self h.mem h.hz)
  have hRs : IsSylow2In R J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ h.hJ.1 hR hRJ
  have hRz : R ≤ Subgroup.centralizer ({z} : Set G) := T3.le_centralizer_of_le_normalizer' h.hz hRN
  have hRt : R ≤ Subgroup.centralizer ({t} : Set G) := hRJ.trans (le_centralizer_of_unique h.ht)
  refine ⟨h.hJ.1, R, hRs, fun x hx => ?_⟩
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hRz hx)
  have h3 := Subgroup.mem_centralizer_singleton_iff.mp (hRt hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (t * z) = (x * t) * z := by group
    _ = (t * x) * z := by rw [← h3]
    _ = t * (x * z) := by group
    _ = t * (z * x) := by rw [← h2]
    _ = (t * z) * x := by group

theorem exists_sylCent_u (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) :
    ∃ g ∈ K ⊔ K', conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) ∧ conjSub g J ∈ SylCent Ω u := by
  have hK := h.mem
  have hK'Ω : K' ∈ Ω := h.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hK'
  have hJΩ : J ∈ Ω := h.hJ.1
  obtain ⟨R₁, R₂, hR₁, hR₂, hc, huR⟩ :=
    Hat2A7S.T7X.exists_sylow_pair_of_mem hΩ hK hK'Ω h.hne h.hz hzK' h.hu h.hu2 h.hu1
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, hR₀S, hR₀'S, hT₀S, hc₀, hRT₀, hR'T₀⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hK h.hz h.hK' h.hne h.hJ
  obtain ⟨g, hgQ, hgR, hgR'⟩ :=
    Hat2A7S.T7X.exists_conj_sylow_pair hΩ hK hK'Ω h.hne h.hz hzK' hR₁ hR₂ hc hR₀ hR₀' hc₀
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hK h.hne hzK' h.hz
  have hgiK : conjSub g⁻¹ K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ ((sup_le Subgroup.le_normalizer hKN) hgQ))
  have hJ' : conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := by
    refine ⟨hΩ.conjInvariant g J hJΩ, fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩ.conjInvariant hL g⁻¹
      rwa [hgiK] at this
    have := omegaNbr_conj hΩ.conjInvariant (h.hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  refine ⟨g, hgQ, hJ', hΩ.conjInvariant g J hJΩ, conjSub g T₀, hT₀.conj g, ?_⟩
  have hcRT : Commutes R₁ (conjSub g T₀) := by
    have := hRT₀.conjSub g
    rwa [hgR] at this
  have hcR'T : Commutes R₂ (conjSub g T₀) := by
    have := hR'T₀.conjSub g
    rwa [hgR'] at this
  obtain ⟨x, hx, y, hy, hxy⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huR
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff, ← hxy]
  have h1 : x * s = s * x := hcRT x hx s hs
  have h2 : y * s = s * y := hcR'T y hy s hs
  calc s * (x * y) = (s * x) * y := by group
    _ = (x * s) * y := by rw [h1]
    _ = x * (s * y) := by group
    _ = x * (y * s) := by rw [h2]
    _ = (x * y) * s := by group

end SylCent

@[expose] def DiscTqTz (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) (t * z),
          M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K

@[expose] def DiscTqU (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
            M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K

section Derived

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem frame_J_mem_dstarComp (s : Setting n R S t₀ K K' z u J t W) :
    J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K := by
  have hΩ := s.core.hyp
  have hf := s.data.frame
  exact Relation.ReflTransGen.single ⟨hf.hJ.1, Or.inl
    (omegaNbr_subset_omegaStarNbr_gen hΩ K (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)))⟩

theorem centralizer_le_sigmaStarNorm_of_sylCent (s : Setting n R S t₀ K K' z u J t W) {c : Y}
    {J₀ : Subgroup Y} (hJ₀ : J₀ ∈ SylCent (CoreAssembly.conjClass (tightCore R)) c)
    (hJ₀d : J₀ ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K)
    (hall : ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) c,
      M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K) :
    Subgroup.centralizer ({c} : Set Y) ≤ sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
  have hΩ := s.core.hyp
  have hK : K ∈ CoreAssembly.conjClass (tightCore R) := s.data.frame.mem
  have hJ₀Ω := hJ₀.1
  intro g hg
  have h1 : conjSub g J₀ ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    hall _ (conjSub_mem_sylCent hΩ.conjInvariant hg hJ₀)
  have hJJ : conjSub g J₀ ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) J₀ :=
    (T3.mem_dstarComp_symm hK hJ₀d).2.trans h1
  have hgJn : g ∈ sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) J₀ :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hJ₀Ω hJJ
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hJ₀d)] at hgJn

theorem disc17tz_of_tq (hT : DiscTqTz n) : Disc17tz n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα _ _
  exact centralizer_le_sigmaStarNorm_of_sylCent s (mem_sylCent_tz_J s.core.hyp s.data.frame)
    (frame_J_mem_dstarComp s) (hT Y R S t₀ K K' z u J t W s hα)

theorem discCentInStar_of_tq (hT : DiscTqTz n) : DiscCentInStar n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα _ _ _ M hMΩ hMc
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := Y)) (bot_le : ⊥ ≤ M)
  exact hT Y R S t₀ K K' z u J t W s hα M ⟨hMΩ, V, hV, hV.1.trans hMc⟩

theorem discYSigma_of_tq (hT : DiscTqU n) : DiscYSigma n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hY _
  have hΩ := s.core.hyp
  have hf := s.data.frame
  obtain ⟨g, -, hJ₀nbr, hJ₀⟩ := exists_sylCent_u hΩ hf
  have hJ₀d : conjSub g J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    Relation.ReflTransGen.single ⟨hJ₀.1, Or.inl
      (omegaNbr_subset_omegaStarNbr_gen hΩ K (hJ₀nbr.2 K (mem_twinSet_self hf.mem hf.hz)))⟩
  exact centralizer_le_sigmaStarNorm_of_sylCent s hJ₀ hJ₀d (hT Y R S t₀ K K' z u J t W s hα hY)

theorem disc13Wyl_of_tq (h12 : Disc12 n) (hT : DiscTqTz n) : Disc13Wyl n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hD
  rcases h12 Y R S t₀ K K' z u J t W s with heq | hmu
  · exfalso
    apply hD
    refine iSup₂_le fun R' hR' => iSup_le fun hRc => ?_
    obtain ⟨J', hJ'Ω, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR'
    have hdst := hT Y R S t₀ K K' z u J t W s hα J' ⟨hJ'Ω, R', hRJ', hRc⟩
    rw [← heq] at hdst
    exact hRJ'.1.trans (le_iSup₂_of_le J' hdst le_rfl)
  · exact hmu

end Derived

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
