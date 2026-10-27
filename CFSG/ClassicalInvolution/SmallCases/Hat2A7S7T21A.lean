module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Alpha
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7F0

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8.T21

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Members


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem hyp51_of_members (hs : Hat2A7S.Pre2A7 Ω K₀) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8)
    (h : ∀ c ∈ B, c ≠ 1 → ∃ (M : Subgroup G) (b : G), IsUniqueInvolution M b ∧ b ∈ B ∧
      b ∉ Subgroup.zpowers c ∧ T8.XMem Ω c M) : Hyp51 B := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  refine hyp51_of_zStar hB hB8 fun c hcB hc1 => ?_
  obtain ⟨M, b, hb, hbB, hbc, hK⟩ := h c hcB hc1
  have hc2 : c * c = 1 := by
    have := hB.2 c hcB
    rwa [pow_two] at this
  have hL : Asc77.T8.LayerHyp Ω c := layerHyp_of_pre hs hc2 hc1
  have hF := Asc77.T8.LayerFam.layerSet hΩ hK
  have hLΛ : T8.layerRes c M ∈ T8.layerSet Ω c := ⟨M, hK, rfl⟩
  have hbL : b ∈ T8.layerRes c M :=
    (Asc77.T8.XMem.isUniqueInvolution_layerRes hΩ hs.classical hc2 hK hb).mem
  have hu : ∀ a ∈ T8.layerRes c M, a * b = b * a := fun a ha =>
    comm_of_mem_isUniqueInvolution hb (T8.layerRes_le c M ha)
  refine ⟨b, hbB, hbc, T8.layerJoin Ω c, T8.le_layerJoin hLΛ hbL, ?_, ?_,
    fun y hy => hF.commutator_mem_oddCoreOf hL hLΛ hbL hu hy⟩
  · rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ c
  · intro n hn
    have hn' : n ∈ T8.cenZ c := by
      rw [T8.cenZ_eq_centralizer]
      exact hn
    exact hF.conjSub_famJoin hn'

theorem xMem_of_le_centralizerModOdd {M B : Subgroup G} (hM : M ∈ Ω) (hB2 : IsPGroup 2 B)
    (hle : B ≤ centralizerModOdd ⊤ M) {c : G} (hc : c ∈ B) : T8.XMem Ω c M := by
  obtain ⟨R, hR, hRc⟩ := exists_sylow_centralized_of_acts_trivially hB2
    (fun c hc => (hle hc).2.1) (fun e he k hk => (hle he).2.2.2 k hk)
  exact ⟨hM, (hle hc).2.1, R, hR, fun r hr => (hRc c hc r hr).symm⟩

theorem xMem_of_centralizes_sylow (hΩ : HypOmegaGen Ω) {J T : Subgroup G} {c : G} (hJ : J ∈ Ω)
    (hT : IsSylow2In T J) (hc : ∀ r ∈ T, r * c = c * r) : T8.XMem Ω c J := by
  have hT8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ hT)
  have hN : c ∈ Subgroup.normalizer (J : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq]
    refine Sec6Gen.eq_of_le_of_le hΩ (hΩ.conjInvariant c J hJ) hJ hT.2.1 (by omega) ?_ hT.1
    intro r hr
    have h1 : c * r * c⁻¹ = r := by
      rw [(hc r hr).symm, mul_inv_cancel_right]
    have h2 := conj_mem_conjSub (n := c) (hT.1 hr)
    rwa [h1] at h2
  exact ⟨hJ, hN, T, hT, hc⟩

theorem inv_mem_centralizerModOdd (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L)
    {M N : Subgroup G} {n : G} (hM : M ∈ Ω) (hn : IsUniqueInvolution N n)
    (h : N = M ∨ N ∈ omegaNbr Ω M) : n ∈ centralizerModOdd ⊤ M := by
  rcases h with rfl | hN
  · refine mem_centralizerModOdd (Subgroup.le_normalizer hn.mem) fun k hk => ?_
    have h1 : n * k = k * n := (comm_of_mem_isUniqueInvolution hn hk).symm
    have h2 : n * k * n⁻¹ * k⁻¹ = 1 := by
      rw [h1]
      group
    rw [h2]
    exact (oddCoreOf N).one_mem
  · obtain ⟨hgt, htriv⟩ := comm_mem_oddCore_of_mem_omegaNbr hΩ (hw M hM) hN hn
    exact mem_centralizerModOdd hgt htriv

end Members

section Frame


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure SFrame (Ω : Set (Subgroup G)) (K K' J : Subgroup G) (z u t : G) : Prop where
  data : TwinFrameData Ω K K' z u J t
  syl : ∃ T : Subgroup G, IsSylow2In T J ∧ (∀ r ∈ T, r * z = z * r) ∧ ∀ r ∈ T, r * u = u * r

theorem sframe_of_sylows (hΩ : HypOmegaGen Ω) {K K' J R R' T : Subgroup G} {z t x y : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (ht : IsUniqueInvolution J t)
    (hR : IsSylow2In R K) (hR' : IsSylow2In R' K') (hT : IsSylow2In T J)
    (hRR' : Commutes R R') (hRT : Commutes R T) (hR'T : Commutes R' T)
    (hx : x ∈ R) (hy : y ∈ R') (hx4 : orderOf x = 4) (hy4 : orderOf y = 4) :
    SFrame Ω K K' J z (x * y) t := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hxK : x ∈ K := hR.1 hx
  have hyK' : y ∈ K' := hR'.1 hy
  have hsqx : x * x = z := T7A.sq_eq_of_orderOf_four hz hxK hx4
  have hsqy : y * y = z := T7A.sq_eq_of_orderOf_four hzK' hyK' hy4
  have hcxy : x * y = y * x := hRR' x hx y hy
  have hxK' : x ∉ K' := fun h =>
    Hat2A7S.T7X.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hx4 hxK h
  have hu2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hsqx, hsqy, hz.sq]
  have hu1 : x * y ≠ 1 := by
    intro h
    apply hxK'
    have : x = y⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h
    rw [this]
    exact K'.inv_mem hyK'
  have huz : x * y ≠ z := by
    intro h
    apply hxK'
    have : x = z * y⁻¹ := by rw [← h]; group
    rw [this]
    exact K'.mul_mem hzK'.mem (K'.inv_mem hyK')
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hR8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hR.1 hR.2.1 (by omega)
  have hT8 : 8 ≤ Nat.card T :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ.1 hT)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup ht hT.1 hT.2.1 (by omega)
  have htu : t * (x * y) = (x * y) * t := by
    have h1 : x * t = t * x := hRT x hx t htT
    have h2 : y * t = t * y := hR'T y hy t htT
    calc t * (x * y) = (t * x) * y := by group
      _ = (x * t) * y := by rw [h1]
      _ = x * (t * y) := by group
      _ = x * (y * t) := by rw [h2]
      _ = (x * y) * t := by group
  refine ⟨⟨hK, hz, hK', hne, Subgroup.mul_mem _ (Subgroup.mem_sup_left hxK)
    (Subgroup.mem_sup_right hyK'), hu2, hu1, huz, hJ, ht, htu⟩, T, hT, fun r hr => ?_,
    fun r hr => ?_⟩
  · exact (hRT z hzR r hr).symm
  · have h1 : x * r = r * x := hRT x hx r hr
    have h2 : y * r = r * y := hR'T y hy r hr
    calc r * (x * y) = (r * x) * y := by group
      _ = (x * r) * y := by rw [h1]
      _ = x * (r * y) := by group
      _ = x * (y * r) := by rw [h2]
      _ = (x * y) * r := by group

theorem exists_sframe (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z t : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (ht : IsUniqueInvolution J t) :
    ∃ u : G, SFrame Ω K K' J z u t := by
  obtain ⟨S, R, R', T, hR, hR', hT, -, -, -, hRR', hRT, hR'T⟩ :=
    Hat2A7S.exists_twinSylow hΩ hK hz hK' hne hJ
  obtain ⟨x, hx, hx4⟩ := Hat2A7M.P25.exists_orderOf_eq_four_of_mem_RSet hΩ
    (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨y, hy, hy4⟩ := Hat2A7M.P25.exists_orderOf_eq_four_of_mem_RSet hΩ
    (mem_RSet_of_isSylow2In hK'.1 hR')
  exact ⟨x * y, sframe_of_sylows hΩ hK hz hK' hne hJ ht hR hR' hT hRR' hRT hR'T hx hy hx4 hy4⟩

theorem exists_sframe_of_sylows (hΩ : HypOmegaGen Ω) {K K' J R₁ R₂ : Subgroup G} {z t x y : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (ht : IsUniqueInvolution J t)
    (hR₁ : IsSylow2In R₁ K) (hR₂ : IsSylow2In R₂ K') (hc : Commutes R₁ R₂) (hx : x ∈ R₁)
    (hy : y ∈ R₂) (hx4 : orderOf x = 4) (hy4 : orderOf y = 4) :
    ∃ g : G, g ∈ K ⊔ K' ∧ conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) ∧
      SFrame Ω K K' (conjSub g J) z (x * y) (g * t * g⁻¹) := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, hR₀S, hR₀'S, hT₀S, hc₀, hRT₀, hR'T₀⟩ :=
    Hat2A7S.exists_twinSylow hΩ hK hz hK' hne hJ
  obtain ⟨g, hgQ, hgR, hgR'⟩ := Hat2A7S.T7X.exists_conj_sylow_pair hΩ hK hK'Ω hne hz hzK' hR₁ hR₂
    hc hR₀ hR₀' hc₀
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hK hne hzK' hz
  have hgiK : conjSub g⁻¹ K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ ((sup_le Subgroup.le_normalizer hKN) hgQ))
  have hJΩ' : conjSub g J ∈ Ω := hΩ.conjInvariant g J hJΩ
  have ht' : IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) := ht.conj g
  have hJ' : conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := by
    refine ⟨hJΩ', fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩ.conjInvariant hL g⁻¹
      rwa [hgiK] at this
    have := omegaNbr_conj hΩ.conjInvariant (hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  have hTsyl : IsSylow2In (conjSub g T₀) (conjSub g J) := hT₀.conj g
  have hcRT : Commutes R₁ (conjSub g T₀) := by
    have := hRT₀.conjSub g
    rwa [hgR] at this
  have hcR'T : Commutes R₂ (conjSub g T₀) := by
    have := hR'T₀.conjSub g
    rwa [hgR'] at this
  exact ⟨g, hgQ, hJ', sframe_of_sylows hΩ hK hz hK' hne hJ' ht' hR₁ hR₂ hTsyl hc hcRT hcR'T hx hy
    hx4 hy4⟩

end Frame

section Alpha


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G} {K K' J : Subgroup G} {z u t : G}

theorem sframe_centralizes (h : SFrame Ω K K' J z u t) :
    ∃ T : Subgroup G, IsSylow2In T J ∧
      ∀ c ∈ Subgroup.closure ({z, u, t} : Set G), ∀ r ∈ T, r * c = c * r := by
  obtain ⟨T, hT, hTz, hTu⟩ := h.syl
  refine ⟨T, hT, fun c hc => ?_⟩
  have hle : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mpr fun r hr => hTz r hr
    · exact Subgroup.mem_centralizer_iff.mpr fun r hr => hTu r hr
    · exact Subgroup.mem_centralizer_iff.mpr fun r hr =>
        comm_of_mem_isUniqueInvolution h.data.ht (hT.1 hr)
  exact fun r hr => Subgroup.mem_centralizer_iff.mp (hle hc) r hr

theorem sframe_hyp51 (hs : Hat2A7S.Pre2A7 Ω K₀) (h : SFrame Ω K K' J z u t) :
    Hyp51 (Subgroup.closure ({z, u, t} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := witness_of_pre hs
  have hd := h.data
  have hJΩ : J ∈ Ω := hd.hJ.1
  have hJK : J ∈ omegaNbr Ω K := hd.hJ.2 K (mem_twinSet_self hd.mem hd.hz)
  have hKJ : K ∈ omegaNbr Ω J := nbr_symm hΩ hd.mem hJΩ hJK
  have hxt : T8.XMem Ω t K := xMem_of_mem_omegaNbr hΩ hw hJΩ hd.ht hKJ
  have hxzt : T8.XMem Ω (z * t) K := xMem_zt hΩ hw hd.mem hd.hz hJK hd.ht
  obtain ⟨T, hT, hTc⟩ := sframe_centralizes h
  refine hyp51_of_members hs (Hat2A7S.twinFrame_isElemAbelian hΩ hd)
    (Hat2A7S.twinFrame_natCard_eight hΩ hd) fun c hcB hc1 => ?_
  have hc2 : c * c = 1 := by
    have := (Hat2A7S.twinFrame_isElemAbelian hΩ hd).2 c hcB
    rwa [pow_two] at this
  have hcord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  by_cases hct : c = t ∨ c = z * t
  · refine ⟨K, z, hd.hz, Subgroup.subset_closure (by simp), ?_, ?_⟩
    · intro hzc
      rcases T7A.eq_one_or_eq_of_mem_zpowers hcord hzc with h1 | h1
      · exact hd.hz.ne_one h1
      · rcases hct with hct | hct
        · exact hd.t_ne_z (by rw [← hct, ← h1])
        · apply hd.ht.ne_one
          have h2 : z * t = z * 1 := by rw [mul_one, ← hct, ← h1]
          exact mul_left_cancel h2
    · rcases hct with hct | hct
      · rw [hct]
        exact hxt
      · rw [hct]
        exact hxzt
  · push Not at hct
    refine ⟨J, t, hd.ht, Subgroup.subset_closure (by simp), ?_,
      xMem_of_centralizes_sylow hΩ hJΩ hT (hTc c hcB)⟩
    intro htc
    rcases T7A.eq_one_or_eq_of_mem_zpowers hcord htc with h1 | h1
    · exact hd.ht.ne_one h1
    · exact hct.1 h1.symm

theorem sframe_alpha (hs : Hat2A7S.Pre2A7 Ω K₀) (h : SFrame Ω K K' J z u t) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G)))) ∧
    (∀ A : Subgroup G, A ≤ Subgroup.closure ({z, u, t} : Set G) → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({t, z} : Set G))) ∧
    ∀ c ∈ Subgroup.closure ({z, u, t} : Set G),
      oddCoreOf (Subgroup.centralizer ({c} : Set G)) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hd := h.data
  have hH51 := sframe_hyp51 hs h
  have hDB : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hd.ht.sq hd.hz.sq hd.ht.ne_one hd.hz.ne_one hd.t_ne_z
      (Hat2A7S.twinFrame_comm_zt hΩ hd).symm
  obtain ⟨hodd, heq⟩ := lemma54_odd_and_eq hH51 hDB hD
  exact ⟨hodd, heq, fun c hc => T8T.oddCoreOf_centralizer_le_normalizer
    (Hat2A7S.twinFrame_isElemAbelian hΩ hd) (Hat2A7S.twinFrame_natCard_eight hΩ hd) hc heq⟩

theorem sframe_alpha_uz (hs : Hat2A7S.Pre2A7 Ω K₀) (h : SFrame Ω K K' J z u t) :
    alphaOf (Subgroup.closure ({u, z} : Set G)) = alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hd := h.data
  have hDB : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  exact (sframe_alpha hs h).2.1 _ hDB
    (T7A.isElemAbelian2_closure_pair hd.hu2 hd.hz.sq hd.hu1 hd.hz.ne_one hd.huz
      hd.comm_zu.symm)

end Alpha

end CFSG.ClassicalInvolution.Hat2A7S8.T21
