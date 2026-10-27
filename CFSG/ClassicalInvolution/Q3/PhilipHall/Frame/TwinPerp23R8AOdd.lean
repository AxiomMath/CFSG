module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift
public import CFSG.ClassicalInvolution.Q3.TL4OddSecEdge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

section Gen

variable {G : Type} [Group G] [Finite G]

theorem p23E8A_isPGroup_modOdd {z : G} {J : Subgroup G}
    (hJs : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (h2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) : IsPGroup 2 ↥(modOdd z J) := by
  have hOJ : oddCoreIn J ≤ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    oddCoreIn_le_of_isSubnormal hJs
  rintro ⟨x₀, hx₀⟩
  obtain ⟨k, hkJ, rfl⟩ := mem_modOdd_iff.mp hx₀
  obtain ⟨m, hm⟩ := h2 (QuotientGroup.mk (⟨(k : G), hkJ⟩ : ↥J))
  refine ⟨m, Subtype.ext ?_⟩
  show (oddQuotMk z k) ^ 2 ^ m = 1
  rw [← map_pow, oddQuotMk_eq_one_iff]
  have h1 : (⟨(k : G), hkJ⟩ : ↥J) ^ 2 ^ m ∈ classicalInvolutionOddCore ↥J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hm
  have h3 : (k : G) ^ 2 ^ m ∈ oddCoreIn J := ⟨_, h1, by simp⟩
  obtain ⟨c, hc, hce⟩ := hOJ h3
  have hck : c = k ^ 2 ^ m := Subtype.ext (by simpa using hce)
  rw [← hck]
  exact hc

theorem p23E8A_modOdd_le_normalizer {z : G} {J J' : Subgroup G}
    (hJ' : J' ≤ Subgroup.normalizer (J : Set G)) :
    modOdd z J' ≤ Subgroup.normalizer (modOdd z J : Set (OddQuot z)) := by
  have key : ∀ c : ↥(Subgroup.centralizer ({z} : Set G)),
      (c : G) ∈ Subgroup.normalizer (J : Set G) →
        ∀ y ∈ modOdd z J, oddQuotMk z c * y * (oddQuotMk z c)⁻¹ ∈ modOdd z J := by
    rintro c hc _ ⟨j, hj, rfl⟩
    refine ⟨c * j * c⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp hc (j : G)).mp (Subgroup.mem_subgroupOf.mp hj)
    simpa using this
  rintro _ ⟨k, hk, rfl⟩
  have hkN : (k : G) ∈ Subgroup.normalizer (J : Set G) := hJ' (Subgroup.mem_subgroupOf.mp hk)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key k hkN y hy, fun hy => ?_⟩
  have := key k⁻¹ (Subgroup.inv_mem _ hkN) _ hy
  simpa [mul_assoc] using this

end Gen

section Cert

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23E8A_u_quiet (hc : P23Cfg n Y R S t K' W u e g)
    (hut : u ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∀ L : Subgroup (OddQuot t), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk t ⟨u, hut⟩ * y = y * oddQuotMk t ⟨u, hut⟩ := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hmem : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz' : IsUniqueInvolution K' t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hA : IsPGroup 2 ↥(modOdd t (tightCore R)) :=
    p23E8A_isPGroup_modOdd (isSubnormal_of_hypOmegaGen hΩ hmem hz) (h2 _ hmem)
  have hB : IsPGroup 2 ↥(modOdd t K') :=
    p23E8A_isPGroup_modOdd (isSubnormal_of_hypOmegaGen hΩ hc.std.hK'.1 hz') (h2 _ hc.std.hK'.1)
  have hBA : modOdd t K' ≤ Subgroup.normalizer (modOdd t (tightCore R) : Set (OddQuot t)) :=
    p23E8A_modOdd_le_normalizer
      (Sec6Gen.le_normalizer_of_twin hΩ hc.std.hK'.1 hmem hc.std.hne hz' hz)
  have hAB : IsPGroup 2 ↥(modOdd t (tightCore R) ⊔ modOdd t K') :=
    hA.to_sup_of_normal_left' hB hBA
  have hK : tightCore R ∈ twinSet (Om R) (tightCore R) :=
    mem_twinSet_self (CoreAssembly.mem_conjClass_self _) hz
  have hKM : tightCore R ≤ TwinSecXg.twinJoin (Om R) (tightCore R) :=
    fun x hx => TwinSecXg.le_twinJoin hK hx
  have hK'M : K' ≤ TwinSecXg.twinJoin (Om R) (tightCore R) :=
    fun x hx => TwinSecXg.le_twinJoin hc.std.hK' hx
  have hMC : TwinSecXg.twinJoin (Om R) (tightCore R) ≤ Subgroup.centralizer ({t} : Set Y) :=
    TwinSecXg.twinJoin_le_centralizer hz
  have hMle : TwinSecXg.twinJoin (Om R) (tightCore R) ≤ tightCore R ⊔ K' := by
    show (⨆ J ∈ twinSet (Om R) (tightCore R), J) ≤ tightCore R ⊔ K'
    refine iSup₂_le fun J hJ => ?_
    rw [twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne] at hJ
    rcases hJ with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hQle : modOdd t (TwinSecXg.twinJoin (Om R) (tightCore R)) ≤
      modOdd t (tightCore R) ⊔ modOdd t K' := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : m ∈ (tightCore R).subgroupOf (Subgroup.centralizer ({t} : Set Y)) ⊔
        K'.subgroupOf (Subgroup.centralizer ({t} : Set Y)) := by
      rw [← Subgroup.subgroupOf_sup (hKM.trans hMC) (hK'M.trans hMC)]
      exact Subgroup.mem_subgroupOf.mpr (hMle (Subgroup.mem_subgroupOf.mp hm))
    have h := Subgroup.mem_map_of_mem (oddQuotMk t) hm'
    rwa [Subgroup.map_sup] at h
  have hMn : ((TwinSecXg.twinJoin (Om R) (tightCore R)).subgroupOf
      (Subgroup.centralizer ({t} : Set Y))).Normal := by
    refine ⟨fun x hx g' => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact TwinSecXg.twinJoin_normalized hΩ hz (g' : Y) g'.2 (x : Y) hx
  have hQn : (modOdd t (TwinSecXg.twinJoin (Om R) (tightCore R))).Normal :=
    hMn.map (oddQuotMk t) (QuotientGroup.mk'_surjective _)
  have huM : u ∈ TwinSecXg.twinJoin (Om R) (tightCore R) := sup_le hKM hK'M hd.hu
  intro L hL y hy
  exact TL4.commute_of_mem_normal_isPGroup hL hQn (hAB.to_le hQle)
    (oddQuotMk_mem_modOdd huM hut) y hy

theorem p23E8A_t_quiet (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) :
    ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y = y * oddQuotMk u ⟨t, htu⟩ := by
  obtain ⟨_, vH, v', ψ, _, ι, _, _, hvH, hzv, _, hψinj, _, _, _, hψvH⟩ := AY.frame_psi hc hA5
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hHn : (coreHull (Om R) u).Normal := ⟨fun a ha g' => by
    have h := conj_mem_conjSub (n := g') ha
    rwa [conjSub_coreHull hΩ hc2 g'] at h⟩
  have hHs : IsSubnormal (coreHull (Om R) u) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hHn.isSubnormal
  have hVn : ((vecSub 5).map (mkQ 5)).Normal :=
    (vecSub_normal (n := 5)).map (mkQ 5) (QuotientGroup.mk'_surjective _)
  have hV2 : IsPGroup 2 ↥((vecSub 5).map (mkQ 5)) := by
    rintro ⟨_, a, ha, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (mkQ 5 a) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two, ← map_mul, vecSub_mul_self ha, map_one]
  have hw : embed ι w0 ∈ vecSub 5 := by
    show (embed ι w0).perm = 1
    rw [embed_perm]
    exact embedPerm_one ι
  have hO2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u))
      (⟨(vH : ↥(Subgroup.centralizer ({u} : Set Y))), vH.2⟩ : ↥(coreHull (Om R) u))) := by
    refine ⟨((vecSub 5).map (mkQ 5)).comap ψ, hVn.comap ψ, hV2.comap_of_injective ψ hψinj, ?_⟩
    show ψ (QuotientGroup.mk vH) ∈ (vecSub 5).map (mkQ 5)
    rw [hψvH]
    exact Subgroup.mem_map_of_mem _ hw
  have hv'C : v' ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [← hvH]
    exact YGam.hcoeHom_mem_centralizer (Om R) u vH
  have hvC : (vH : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨v', hv'C⟩ := Subtype.ext hvH
  have hq : ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk u ⟨v', hv'C⟩ * y = y * oddQuotMk u ⟨v', hv'C⟩ := by
    intro L hL
    have h := TL4.quiet_of_inO2_sub hHs vH.2 hO2 L hL
    rw [hvC] at h
    exact h
  have huC : u ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hucen : ∀ y : OddQuot u, oddQuotMk u ⟨u, huC⟩ * y = y * oddQuotMk u ⟨u, huC⟩ := by
    intro y
    obtain ⟨c, rfl⟩ : ∃ c, oddQuotMk u c = y := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
  rcases hzv with h | h
  · have e : (⟨t, htu⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨v', hv'C⟩ := Subtype.ext h
    rw [e]
    exact hq
  · have e : (⟨t, htu⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨u, huC⟩ * ⟨v', hv'C⟩ :=
      Subtype.ext h
    intro L hL y hy
    rw [e, map_mul, mul_assoc, hq L hL y hy, ← mul_assoc, hucen y, mul_assoc]

theorem p23E8A_oddCoreIn_eq (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) =
      Balance.oddCoreIn (Subgroup.centralizer ({u} : Set Y)) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hK : tightCore R ∈ twinSet (Om R) (tightCore R) :=
    mem_twinSet_self (CoreAssembly.mem_conjClass_self _) hz
  have hKM : tightCore R ≤ TwinSecXg.twinJoin (Om R) (tightCore R) :=
    fun x hx => TwinSecXg.le_twinJoin hK hx
  have hK'M : K' ≤ TwinSecXg.twinJoin (Om R) (tightCore R) :=
    fun x hx => TwinSecXg.le_twinJoin hc.std.hK' hx
  have hut : u ∈ Subgroup.centralizer ({t} : Set Y) :=
    TwinSecXg.twinJoin_le_centralizer hz (sup_le hKM hK'M hd.hu)
  have htu : t ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hut).symm
  have hα' : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
    rw [Set.pair_comm]; exact hα
  have hqu := p23E8A_u_quiet hc hut
  have hqt := p23E8A_t_quiet hc hA5 htu
  have h1 : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set Y)) ≤
      Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
    TwinOdd.oddCent_le_of_alpha hut hd.hu2 hd.hu1 hα
      fun L hL _ ⟨y, hy, hne⟩ => (hne (hqu L hL y hy)).elim
  have h2 : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) ≤
      Balance.oddCoreIn (Subgroup.centralizer ({u} : Set Y)) :=
    TwinOdd.oddCent_le_of_alpha htu hz.sq hz.ne_one hα'
      fun L hL _ ⟨y, hy, hne⟩ => (hne (hqt L hL y hy)).elim
  exact le_antisymm h2 h1

theorem p23E8A_oddCent_eq_bot (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  have hC := CoreData.of_S hc.std.perp.core
  have hTwo := p23Two_of_thmEQ8 hE hcit hP Y R S t K' W u e g hc
  have heq := p23E8A_oddCoreIn_eq hc hA5 hα
  set N : Subgroup Y := oddCoreIn (Subgroup.centralizer ({t} : Set Y)) with hN
  have hnorm_of : ∀ x : Y, (∀ y ∈ N, x * y * x⁻¹ ∈ N) → (∀ y ∈ N, x⁻¹ * y * x ∈ N) →
      x ∈ Subgroup.normalizer (N : Set Y) := by
    intro x h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
    have := h2 _ hh
    simpa [mul_assoc] using this
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := fun x hx =>
    hnorm_of x (fun y hy => conj_mem_oddCoreIn hx hy)
      (fun y hy => by
        have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
        simpa using this)
  have hCu : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := fun x hx =>
    hnorm_of x (fun y hy => by rw [heq] at hy ⊢; exact conj_mem_oddCoreIn hx hy)
      (fun y hy => by
        rw [heq] at hy ⊢
        have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
        simpa using this)
  have htop : Subgroup.normalizer (N : Set Y) = ⊤ := by
    rw [eq_top_iff, ← hTwo]
    exact sup_le hCu hCt
  have hNn : N.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hle : N ≤ classicalInvolutionOddCore Y := le_sSup ⟨hNn, odd_card_oddCoreIn _⟩
  rw [hC.oddFree] at hle
  exact TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn (le_bot_iff.mp hle)

theorem p23E8A_oddCoreIn_eq_bot (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  have h := p23E8A_oddCent_eq_bot hE hcit hP hc hA5 hα
  show (classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))).map _ = ⊥
  rw [h, Subgroup.map_bot]

theorem p23E8A_members_isPGroup (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ J ∈ Om R, IsPGroup 2 ↥J := by
  have hC := CoreData.of_S hc.std.perp.core
  exact isPGroup_conjClass_of_oddCent hC.hyp (Inner.isUniqueInvolution_core hC.datum)
    (p23E8A_oddCoreIn_eq_bot hE hcit hP hc hA5 hα)
    (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
