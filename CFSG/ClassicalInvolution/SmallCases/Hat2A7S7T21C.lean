module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7T21B
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7E1
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8.T21

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_of_mem_dComp {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ dComp Ω K) : M ∈ Ω := by
  induction hM with
  | refl => exact hK
  | tail _ hbc _ => exact hbc.1

theorem mem_dComp_of_twin (hΩ : HypOmegaGen Ω) {M L : Subgroup G} {y : G} (hM : M ∈ Ω)
    (hy : IsUniqueInvolution M y) (hL : L ∈ twinSet Ω M) : L ∈ dComp Ω M := by
  by_cases h : L = M
  · rw [h]
    exact Relation.ReflTransGen.refl
  · have hLy : IsUniqueInvolution L y := isUniqueInvolution_of_mem_twinSet hy hL
    rcases Set.mem_insert_iff.mp (Hat2A7M.Asc77.mem_kPerp_of_twin hΩ hL.1 hM hLy hy) with h' | h'
    · exact absurd h' h
    · exact T8.mem_dComp_of_mem_omegaNbr h'

theorem centralizer_le_sigmaNorm_of_mem_dComp (hΩ : HypOmegaGen Ω) {K M : Subgroup G}
    (hK : K ∈ Ω) (hM : M ∈ dComp Ω K) {y : G} (hy : IsUniqueInvolution M y) :
    Subgroup.centralizer ({y} : Set G) ≤ sigmaNorm Ω K := by
  intro c hc
  have hMΩ : M ∈ Ω := mem_of_mem_dComp hK hM
  have hcy : c * y * c⁻¹ = y := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [mul_inv_eq_iff_eq_mul]
    exact hc
  have hcM : conjSub c M ∈ twinSet Ω M := by
    refine ⟨hΩ.conjInvariant c M hMΩ, y, hy, ?_⟩
    have := hy.conj c
    rwa [hcy] at this
  have hcK : conjSub c M ∈ dComp Ω K := by
    have h1 := mem_dComp_of_twin hΩ hMΩ hy hcM
    rw [T8.dComp_eq_of_mem hK hM] at h1
    exact h1
  exact T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hM hcK

theorem mul_ne_one_of_ne {z z' : G} (hz : z * z = 1) (hne : z' ≠ z) : z * z' ≠ 1 := by
  intro h
  apply hne
  have h1 : z' = z⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h1]
  exact inv_eq_of_mul_eq_one_right hz

end Basic

section Layer


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem dstarComp_subset_dComp (hs : Hat2A7S.Pre2A7 Ω K₀) {K : Subgroup G} (hK : K ∈ Ω) :
    dstarComp Ω K ⊆ dComp Ω K := by
  intro J hJ
  induction hJ with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hbk hbc ih =>
    have hbmem : b ∈ dstarComp Ω K := hbk
    have hb : b ∈ Ω := by
      rcases dstarComp_subset_insert K hbmem with h | h
      · rw [h]
        exact hK
      · exact h
    obtain ⟨hcΩ, hcor⟩ := hbc
    refine Relation.ReflTransGen.tail ih ⟨hcΩ, ?_⟩
    rcases hcor with h | h
    · exact Or.inl (Hat2A7S.omegaStarNbr_subset_omegaNbr_a7 hs hb hcΩ h)
    · exact Or.inr (Hat2A7S.omegaStarNbr_subset_omegaNbr_a7 hs hcΩ hb h)

theorem trans_of_sigmaNorm_le (hs : Hat2A7S.Pre2A7 Ω K₀) {K : Subgroup G} (hK : K ∈ Ω)
    {H : Subgroup G} (hH : sigmaNorm Ω K ≤ H) :
    ∀ M ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = M := by
  intro M hM
  have hMSg := dstarComp_subset_dComp hs hK hM
  obtain ⟨g, hg⟩ := hs.trans M (mem_of_mem_dComp hK hMSg)
  obtain ⟨g₁, hg₁⟩ := hs.trans K hK
  have e : conjSub (g * g₁⁻¹) K = M := by
    rw [conjSub_mul, ← hg₁, conjSub_inv_conjSub, hg]
  exact ⟨g * g₁⁻¹, hH ((T8.mem_sigmaNorm_iff hs.hyp.conjInvariant hK).2 (by rw [e]; exact hMSg)),
    e⟩

theorem centralizer_le_of_oddCore (hs : Hat2A7S.Pre2A7 Ω K₀) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1) (hMa : T8.XMem Ω a M)
    {H : Subgroup G} (hSg : sigmaNorm Ω K ≤ H)
    (hO : oddCoreOf (Subgroup.centralizer ({a} : Set G)) ≤ H) :
    Subgroup.centralizer ({a} : Set G) ≤ H := by
  intro c hc
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hL : Asc77.T8.LayerHyp Ω a := layerHyp_of_pre hs ha2 ha1
  obtain ⟨ν, hν, hνc⟩ := exists_mul_mem_sigmaNorm_of_centralizer hL hMa hc
  have hνc' : ν * c ∈ sigmaNorm Ω K := by
    have h1 := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hMa.1).1 hνc
    rw [T8.dComp_eq_of_mem hK hM] at h1
    exact T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hM h1
  have hνH : ν ∈ H := hO (oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ a hν)
  have := H.mul_mem (H.inv_mem hνH) (hSg hνc')
  simpa using this

theorem oddCore_le_centralizer_of_alpha_bot {A : Subgroup G} {a w : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hw : w ∈ A) (hα : alphaOf A = ⊥) :
    oddCoreOf (Subgroup.centralizer ({a} : Set G)) ≤ Subgroup.centralizer ({w} : Set G) := by
  intro n hn
  have h1 : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ ≤ alphaOf A := by
    unfold alphaOf
    refine le_trans ?_ le_sup_left
    exact le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)
  have h2 : ⁅n, w⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ :=
    Subgroup.commutator_mem_commutator hn hw
  have h3 : ⁅n, w⁆ ∈ alphaOf A := h1 h2
  rw [hα, Subgroup.mem_bot] at h3
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem stdCent_of_data (hs : Hat2A7S.Pre2A7 Ω K₀) {K : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) {H : Subgroup G} (hSg : sigmaNorm Ω K ≤ H)
    (hA : ∀ L ∈ twinSet Ω K, ∀ P ∈ omegaNbr Ω L, ∀ z' : G, IsUniqueInvolution P z' → z' ≠ z →
      oddCoreOf (Subgroup.centralizer ({z * z'} : Set G)) ≤ H)
    (hB : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 → ∃ J ∈ dComp Ω K, T8.XMem Ω (x * y) J ∧
          (x * y) * (x * y) = 1 ∧ x * y ≠ 1 ∧
          oddCoreOf (Subgroup.centralizer ({x * y} : Set G)) ≤ H) :
    StdCent Ω K H z := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := witness_of_pre hs
  have hKSg : K ∈ dComp Ω K := Relation.ReflTransGen.refl
  refine ⟨(centralizer_le_sigmaNorm_of_mem_dComp hΩ hK hKSg hz).trans hSg, ?_, ?_⟩
  · intro L hL P hP z' hz' hne
    have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hz hL
    have hLSg : L ∈ dComp Ω K := mem_dComp_of_twin hΩ hK hz hL
    have hPSg : P ∈ dComp Ω K := by
      rw [← T8.dComp_eq_of_mem hK hLSg]
      exact T8.mem_dComp_of_mem_omegaNbr hP
    refine ⟨(centralizer_le_sigmaNorm_of_mem_dComp hΩ hK hPSg hz').trans hSg, ?_⟩
    have hxm : T8.XMem Ω (z * z') L := xMem_zt hΩ hw hL.1 hzL hP hz'
    have hsq : z * z' * (z * z') = 1 := Q3.Q3CL.T8.mul_self_zt hΩ hzL hP hz'
    have hne1 : z * z' ≠ 1 := mul_ne_one_of_ne hz.sq hne
    exact centralizer_le_of_oddCore hs hK hLSg hsq hne1 hxm hSg (hA L hL P hP z' hz' hne)
  · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
    obtain ⟨J, hJSg, hxm, hsq, hne1, hO⟩ :=
      hB L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
    exact centralizer_le_of_oddCore hs hK hJSg hsq hne1 hxm hSg hO

theorem oddCore_mul_le_normalizer (hs : Hat2A7S.Pre2A7 Ω K₀) {K K' L P : Subgroup G} {z z' : G}
    (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hL : L ∈ twinSet Ω K) (hP : P ∈ omegaNbr Ω L) (hz' : IsUniqueInvolution P z')
    (hne' : z' ≠ z) :
    oddCoreOf (Subgroup.centralizer ({z * z'} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({z', z} : Set G)) : Set G) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hz hL
  obtain ⟨L', hL', hLne⟩ := exists_twin_of_mem hs hK hK' hne hL.1
  have hP' : P ∈ omegaOfSet Ω (twinSet Ω L) := mem_omegaOfSet_of_nbr hs hL.1 hzL hP hz' hne'
  obtain ⟨u, hfr⟩ := exists_sframe hΩ hL.1 hzL hL' hLne hP' hz'
  exact (sframe_alpha hs hfr).2.2 (z * z') (Subgroup.mul_mem _
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))

theorem oddCore_twin_le (hs : Hat2A7S.Pre2A7 Ω K₀) {K J₀ L L' R₁ R₂ : Subgroup G} {z t₀ x y : G}
    (hz : IsUniqueInvolution K z) (hJ₀ : J₀ ∈ omegaOfSet Ω (twinSet Ω K))
    (ht₀ : IsUniqueInvolution J₀ t₀) (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K)
    (hne : L' ≠ L) (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂)
    (hx : x ∈ R₁) (hy : y ∈ R₂) (hx4 : orderOf x = 4) (hy4 : orderOf y = 4) :
    ∃ (J : Subgroup G) (t : G), J ∈ omegaNbr Ω L ∧ IsUniqueInvolution J t ∧ t ≠ z ∧
      T8.XMem Ω (x * y) J ∧ (x * y) * (x * y) = 1 ∧ x * y ≠ 1 ∧
      oddCoreOf (Subgroup.centralizer ({x * y} : Set G)) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) ∧
      alphaOf (Subgroup.closure ({x * y, z} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hz hL
  have hL'L : L' ∈ twinSet Ω L := by
    rw [twinSet_eq_of_mem_twinSet hz hL]
    exact hL'
  have hJ₀L : J₀ ∈ omegaOfSet Ω (twinSet Ω L) := by
    rw [twinSet_eq_of_mem_twinSet hz hL]
    exact hJ₀
  obtain ⟨g, -, hJg, hfr⟩ :=
    exists_sframe_of_sylows hΩ hL.1 hzL hL'L hne hJ₀L ht₀ hR₁ hR₂ hc hx hy hx4 hy4
  have hd := hfr.data
  have hJL : conjSub g J₀ ∈ omegaNbr Ω L := hJg.2 L (mem_twinSet_self hL.1 hzL)
  refine ⟨conjSub g J₀, g * t₀ * g⁻¹, hJL, hd.ht, hd.t_ne_z, ?_, hd.hu2, hd.hu1, ?_, ?_⟩
  · obtain ⟨T, hT, hTc⟩ := sframe_centralizes hfr
    exact xMem_of_centralizes_sylow hΩ hd.hJ.1 hT
      (hTc (x * y) (Subgroup.subset_closure (by simp)))
  · exact (sframe_alpha hs hfr).2.2 (x * y) (Subgroup.subset_closure (by simp))
  · exact sframe_alpha_uz hs hfr

end Layer

section Apply


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K : Subgroup G}

theorem ne_of_mem_omegaOfSet {J : Subgroup G} {z t : G} (hz : IsUniqueInvolution K z)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (ht : IsUniqueInvolution J t) : t ≠ z := by
  intro htz
  have hJt : J ∈ twinSet Ω K := by
    refine ⟨hJ.1, z, hz, ?_⟩
    rw [← htz]
    exact ht
  exact (hJ.2 J hJt).2.1 rfl

theorem eq_bot_of_normalizer_eq_top {α : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hodd : Odd (Nat.card α)) (htop : Subgroup.normalizer (α : Set G) = ⊤) : α = ⊥ := by
  have hnorm : α.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases Subgroup.Normal.eq_bot_or_eq_top α with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hodd
    have h2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    have h3 : 2 ∣ Nat.card G := by
      have := orderOf_dvd_natCard z
      rwa [h2] at this
    have h4 := Nat.odd_iff.mp hodd
    omega

theorem alphaOf_eq_bot_of_thmE (hE : Hat2A7S.A7ThmE) (hs : Hat2A7S.Std2A7 Ω K) {K' J : Subgroup G}
    {z t : G} (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (ht : IsUniqueInvolution J t) :
    alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
  have hpre : Hat2A7S.Pre2A7 Ω K := hs.toPre2A7
  have hΩ : HypOmegaGen Ω := hpre.hyp
  have hK : K ∈ Ω := hpre.mem
  have htz : t ≠ z := ne_of_mem_omegaOfSet hz hJ ht
  have hJK : J ∈ omegaNbr Ω K := hJ.2 K (mem_twinSet_self hK hz)
  obtain ⟨u, hfr⟩ := exists_sframe hΩ hK hz hK' hne hJ ht
  have hodd := (sframe_alpha hpre hfr).1
  have hAC : AlphaConstT Ω := alphaConstT hpre hK hK' hne
  have hSgN := sigmaNorm_le_normalizer_alpha_T hpre hAC hK hz hJK ht htz
  have hconst : ∀ L ∈ dComp Ω K, ∀ P ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y →
      IsUniqueInvolution P y' → y' ≠ y →
        alphaOf (Subgroup.closure ({y', y} : Set G)) =
          alphaOf (Subgroup.closure ({t, z} : Set G)) :=
    fun L hL => (alphaOf_eq_of_mem_dComp_T hpre hAC hK hz hJK ht htz hL).2
  have hstd : StdCent Ω K
      (Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G)) z := by
    refine stdCent_of_data hpre hK hz hSgN ?_ ?_
    · intro L hL P hP z' hz' hne'
      have hLSg : L ∈ dComp Ω K := mem_dComp_of_twin hΩ hK hz hL
      have h1 := oddCore_mul_le_normalizer hpre hK hK' hne hz hL hP hz' hne'
      rw [hconst L hLSg P hP z z' (isUniqueInvolution_of_mem_twinSet hz hL) hz' hne'] at h1
      exact h1
    · intro L hL L' hL' hLne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
      obtain ⟨J₁, t₁, hJ₁L, ht₁, ht₁z, hxm, hsq, hne1, hO, -⟩ :=
        oddCore_twin_le hpre hz hJ ht hL hL' hLne hR₁ hR₂ hc hx hy hx4 hy4
      have hLSg : L ∈ dComp Ω K := mem_dComp_of_twin hΩ hK hz hL
      have hJ₁Sg : J₁ ∈ dComp Ω K := by
        rw [← T8.dComp_eq_of_mem hK hLSg]
        exact T8.mem_dComp_of_mem_omegaNbr hJ₁L
      refine ⟨J₁, hJ₁Sg, hxm, hsq, hne1, ?_⟩
      rw [hconst L hLSg J₁ hJ₁L z t₁ (isUniqueInvolution_of_mem_twinSet hz hL) ht₁ ht₁z] at hO
      exact hO
  have htop := Hat2A7S.a7ThmE_apply hE hs hz hK' hne hstd (trans_of_sigmaNorm_le hpre hK hSgN)
  exact eq_bot_of_normalizer_eq_top hz hodd htop

theorem dConnected_of_alpha_bot (hE : Hat2A7S.A7ThmE) (hs : Hat2A7S.Std2A7 Ω K)
    {K' J : Subgroup G} {z t : G} (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (ht : IsUniqueInvolution J t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) : DConnected Ω := by
  have hpre : Hat2A7S.Pre2A7 Ω K := hs.toPre2A7
  have hΩ : HypOmegaGen Ω := hpre.hyp
  have hK : K ∈ Ω := hpre.mem
  have htz : t ≠ z := ne_of_mem_omegaOfSet hz hJ ht
  have hJK : J ∈ omegaNbr Ω K := hJ.2 K (mem_twinSet_self hK hz)
  have hAC : AlphaConstT Ω := alphaConstT hpre hK hK' hne
  have hconst : ∀ L ∈ dComp Ω K, ∀ P ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y →
      IsUniqueInvolution P y' → y' ≠ y →
        alphaOf (Subgroup.closure ({y', y} : Set G)) =
          alphaOf (Subgroup.closure ({t, z} : Set G)) :=
    fun L hL => (alphaOf_eq_of_mem_dComp_T hpre hAC hK hz hJK ht htz hL).2
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ sigmaNorm Ω K :=
    centralizer_le_sigmaNorm_of_mem_dComp hΩ hK Relation.ReflTransGen.refl hz
  have hstd : StdCent Ω K (sigmaNorm Ω K) z := by
    refine stdCent_of_data hpre hK hz le_rfl ?_ ?_
    · intro L hL P hP z' hz' hne'
      have hLSg : L ∈ dComp Ω K := mem_dComp_of_twin hΩ hK hz hL
      have hbot : alphaOf (Subgroup.closure ({z', z} : Set G)) = ⊥ :=
        (hconst L hLSg P hP z z' (isUniqueInvolution_of_mem_twinSet hz hL) hz' hne').trans hα
      have hmem : z * z' ∈ Subgroup.closure ({z', z} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      exact (oddCore_le_centralizer_of_alpha_bot hmem (mul_ne_one_of_ne hz.sq hne')
        (Subgroup.subset_closure (by simp)) hbot).trans hCz
    · intro L hL L' hL' hLne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
      obtain ⟨J₁, t₁, hJ₁L, ht₁, ht₁z, hxm, hsq, hne1, -, hα₁⟩ :=
        oddCore_twin_le hpre hz hJ ht hL hL' hLne hR₁ hR₂ hc hx hy hx4 hy4
      have hLSg : L ∈ dComp Ω K := mem_dComp_of_twin hΩ hK hz hL
      have hJ₁Sg : J₁ ∈ dComp Ω K := by
        rw [← T8.dComp_eq_of_mem hK hLSg]
        exact T8.mem_dComp_of_mem_omegaNbr hJ₁L
      refine ⟨J₁, hJ₁Sg, hxm, hsq, hne1, ?_⟩
      have hbot : alphaOf (Subgroup.closure ({x * y, z} : Set G)) = ⊥ := by
        rw [hα₁, hconst L hLSg J₁ hJ₁L z t₁ (isUniqueInvolution_of_mem_twinSet hz hL) ht₁ ht₁z, hα]
      exact (oddCore_le_centralizer_of_alpha_bot (Subgroup.subset_closure (by simp)) hne1
        (Subgroup.subset_closure (by simp)) hbot).trans hCz
  have htop := Hat2A7S.a7ThmE_apply hE hs hz hK' hne hstd (trans_of_sigmaNorm_le hpre hK le_rfl)
  exact dConnected_of_sigmaNorm_eq_top hK hpre.trans htop

end Apply

end CFSG.ClassicalInvolution.Hat2A7S8.T21
