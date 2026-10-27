module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelTorus
public import CFSG.LieType.Ree.LargeReeInvolutionIntermediateOddCore
public import CFSG.LocalAnalysis.EvenBN.TwoF4.FusionModel

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] [CharP K F4.prime]
  in
theorem map_largeReeSigma (σ : K ≃+* K) (u : K) :
    σ (largeReeSigma a u) = largeReeSigma a (σ u) := by
  simp only [largeReeSigma, map_pow]

omit [Finite K] [CharP K F4.prime]
  in
theorem entrywise_rootElt (σ : K ≃+* K) (i : Idx) (u : K) :
    Units.map (entrywiseHom σ.toRingHom) (rootElt K a i u) = rootElt K a i (σ u) := by
  have hX : ∀ (r : ℕ) (c : K), Units.map (entrywiseHom (σ : K →+* K)) (sylowX K r c) =
      sylowX K r (σ c) := fun r c => units_map_entrywiseHom_pinnedX (σ : K →+* K) _ c
  cases i <;>
    simp only [rootElt, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, map_mul,
      RingEquiv.toRingHom_eq_coe, hX, map_largeReeSigma, map_add, map_mul, map_pow, map_zero]

theorem reeGamma_inf_centralizer_invE_le (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    F4.reeGamma K a ⊓ centralizer {invE K a} ≤ centralizer {rootElt K a .i12 c} := by
  rw [(reeGamma_inf_centralizer_invE_invF ha hK).1]
  have hz : rootElt K a .i12 c = centralZ K a c := sylowH_zero_eq_centralZ c
  rw [hz]
  refine sup_le (fun g hg => ?_) (rankOneGroupTwo_le_centralizer ha hK c)
  exact mem_centralizer_singleton_iff.2 (commute_centralZ ha hK (rootJoin_le_sylowP hK _ hg) c)

theorem exists_conj_rootElt12_eq (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {y : ModGL F4.tag K} (hy : y ∈ F4.reeGamma K a)
    (hye : y * invE K a * y⁻¹ ∈ rootV K a .i12) :
    ∃ c : K, c ≠ 0 ∧ ∀ u, y * rootElt K a .i12 u * y⁻¹ = rootElt K a .i12 (c * u) := by
  have he1 : y * invE K a * y⁻¹ ≠ 1 := by
    intro h1
    have : invE K a = 1 := by
      calc invE K a = y⁻¹ * (y * invE K a * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
    have h2 := (invE_invF_mem (a := a) hK).2.2.2.2.1
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨x, hx, hxe⟩ := exists_torusH_conj_invE ha hK hye he1
  obtain ⟨t', rfl⟩ := hx
  refine ⟨(rootChar K a .i12 t' : K), Units.ne_zero _, fun u => ?_⟩
  have hxΓ : torusPair a t' ∈ F4.reeGamma K a := torusH_le_reeGamma hK ⟨t', rfl⟩
  have hc : (torusPair a t')⁻¹ * y ∈ F4.reeGamma K a ⊓ centralizer {invE K a} := by
    refine mem_inf.2 ⟨mul_mem (inv_mem hxΓ) hy, mem_centralizer_singleton_iff.2 ?_⟩
    calc (torusPair a t')⁻¹ * y * invE K a = (torusPair a t')⁻¹ * (y * invE K a * y⁻¹) * y := by
          group
      _ = (torusPair a t')⁻¹ * (torusPair a t' * invE K a * (torusPair a t')⁻¹) * y := by
          rw [hxe]
      _ = invE K a * ((torusPair a t')⁻¹ * y) := by group
  have hcu := mem_centralizer_singleton_iff.1 (reeGamma_inf_centralizer_invE_le ha hK u hc)
  rw [← torusPair_conj_rootElt hK]
  calc y * rootElt K a .i12 u * y⁻¹ =
      torusPair a t' * (((torusPair a t')⁻¹ * y) * rootElt K a .i12 u) * y⁻¹ := by group
    _ = torusPair a t' * (rootElt K a .i12 u * ((torusPair a t')⁻¹ * y)) * y⁻¹ := by rw [hcu]
    _ = torusPair a t' * rootElt K a .i12 u * (torusPair a t')⁻¹ := by group

theorem rootV2_inf_radR (hK : Nat.card K = 2 ^ (2 * a + 1)) : rootV K a .i2 ⊓ radR K a = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg2, hgR⟩ := mem_inf.1 hg
  have h2 : g ∈ (rootV K a .i2 : Set (ModGL F4.tag K)) := hg2
  have hR : g ∈ (radR K a : Set (ModGL F4.tag K)) := hgR
  rw [coe_rootV hK] at h2
  rw [(radR_spec hK).2.1] at hR
  obtain ⟨x, hx, rfl⟩ := h2
  obtain ⟨z, hz, hzx⟩ := hR
  have hxz := (bijOn_sylowVec (m := a) (K := K) hK).injOn (Set.mem_univ _) (Set.mem_univ _) hzx
  have hx0 : x = 0 := by
    funext n
    by_cases hn : n ∈ Idx.i2.coords
    · have : n = 2 := by simpa [Idx.coords, Idx.isSz, Idx.coord] using hn
      subst this
      rw [← hxz]
      exact hz 2 (by decide)
    · exact hx n hn
  rw [mem_bot, hx0]
  have := (rootElt_eq_sylowVec (a := a) (K := K) .i2 0).symm
  rw [rootElt_zero] at this
  rw [← this]
  simp

theorem conj_rootElt2_mem_radR (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ModGL F4.tag K}
    (hp : p ∈ F4.reeFixedPosUnipotent K a) (w : K) :
    p * rootElt K a .i2 w * p⁻¹ * (rootElt K a .i2 w)⁻¹ ∈ radR K a := by
  have hRn := (radR_spec (a := a) hK).2.2.2
  set z := rootElt K a .i2 w with hz
  have hzP : z ∈ F4.reeFixedPosUnipotent K a := rootV_le_sylowP hK .i2 (rootElt_mem_rootV _ _)
  have hzc : ∀ v ∈ rootV K a .i1, v * z = z * v := by
    have hzZ : z ∈ rootV K a .i1 ⊓ centralizer (rootV K a .i1 : Set (ModGL F4.tag K)) := by
      rw [rootV_inf_centralizer ha hK (i := .i1) rfl]
      exact rootElt_mem_rootV _ _
    exact fun v hv => mem_centralizer_iff.1 (mem_inf.1 hzZ).2 v hv
  have hR : ∀ {i : Idx}, i ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) →
      ∀ u, rootElt K a i u ∈ radR K a := fun hi u => rootV_le_rootJoin hi (rootElt_mem_rootV _ _)
  have hR1 : ∀ {i : Idx}, i ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx) →
      ∀ u, rootElt K a i u ∈ radR K a := fun hi u =>
    (S1_le_S2_le_S3_le_S4_le_radS (a := a) hK).2.2.2.2.1
      (rootV_le_rootJoin hi (rootElt_mem_rootV _ _))
  have hp' : p ∈ (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := hp
  rw [← (bijOn_sylowVec (m := a) (K := K) hK).image_eq] at hp'
  obtain ⟨x, -, rfl⟩ := hp'
  rw [sylowVec_eq_prod_rootElt hK]
  set r₀ := rootElt K a .i3 (x 0) with hr₀
  set v := rootElt K a .i1 (x 1) * rootElt K a .i2 (x 2) with hv
  set r₁ := rootElt K a .i4 (x 3) * rootElt K a .i8 (x 4) * rootElt K a .i6 (x 5) *
    rootElt K a .i11 (x 6) * rootElt K a .i5 (x 7) * rootElt K a .i12 (x 8) *
    rootElt K a .i7 (x 9) * rootElt K a .i9 (x 10) * rootElt K a .i10 (x 11) with hr₁
  have hr₀R : r₀ ∈ radR K a := hR (by decide) _
  have hvV : v ∈ rootV K a .i1 := mul_mem (rootElt_mem_rootV _ _)
    (rootV_le_rootV hK (i := .i2) (j := .i1) (by decide) (rootElt_mem_rootV _ _))
  have hr₁R : r₁ ∈ radR K a := by
    refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_)
      ?_) ?_) ?_) ?_) ?_) ?_
    · exact hR (by decide) _
    · exact hR1 (by decide) _
    · exact hR (by decide) _
    · exact hR1 (by decide) _
    · exact hR (by decide) _
    · exact hR1 (by decide) _
    · exact hR (by decide) _
    · exact hR (by decide) _
    · exact hR (by decide) _
  have hprod : rootElt K a .i3 (x 0) * rootElt K a .i1 (x 1) * rootElt K a .i2 (x 2) *
      rootElt K a .i4 (x 3) * rootElt K a .i8 (x 4) * rootElt K a .i6 (x 5) *
      rootElt K a .i11 (x 6) * rootElt K a .i5 (x 7) * rootElt K a .i12 (x 8) *
      rootElt K a .i7 (x 9) * rootElt K a .i9 (x 10) * rootElt K a .i10 (x 11) = r₀ * v * r₁ := by
    rw [hr₀, hv, hr₁]
    group
  rw [hprod]
  have hρ : r₁ * z * r₁⁻¹ * z⁻¹ ∈ radR K a := by
    have e : r₁ * z * r₁⁻¹ * z⁻¹ = r₁ * (z * r₁⁻¹ * z⁻¹) := by group
    rw [e]
    exact mul_mem hr₁R ((mem_normalizer_iff.1 (hRn hzP) _).1 (inv_mem hr₁R))
  have hvP : v ∈ F4.reeFixedPosUnipotent K a := rootV_le_sylowP hK .i1 hvV
  have hρ' : v * (r₁ * z * r₁⁻¹ * z⁻¹) * v⁻¹ ∈ radR K a := (mem_normalizer_iff.1 (hRn hvP) _).1 hρ
  have hr₀' : z * r₀⁻¹ * z⁻¹ ∈ radR K a := (mem_normalizer_iff.1 (hRn hzP) _).1 (inv_mem hr₀R)
  have hvz := hzc v hvV
  have e : r₀ * v * r₁ * z * (r₀ * v * r₁)⁻¹ * z⁻¹ =
      r₀ * (v * (r₁ * z * r₁⁻¹ * z⁻¹) * v⁻¹) * (v * z * v⁻¹) * r₀⁻¹ * z⁻¹ := by group
  rw [e, show v * z * v⁻¹ = z by rw [hvz]; group,
    show r₀ * (v * (r₁ * z * r₁⁻¹ * z⁻¹) * v⁻¹) * z * r₀⁻¹ * z⁻¹ =
      r₀ * (v * (r₁ * z * r₁⁻¹ * z⁻¹) * v⁻¹) * (z * r₀⁻¹ * z⁻¹) by group]
  exact mul_mem (mul_mem hr₀R hρ') hr₀'

end Model

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

theorem conj_elt_eq (x : h.C) {g : ModGL F4.tag h.K} (hg : g ∈ F4.reeGamma h.K h.a) :
    (x : G) * h.elt g * (x : G)⁻¹ = h.elt (((h.actSemi x).left : ModGL F4.tag h.K) *
      Units.map (entrywiseHom (h.fieldFactor x).toRingHom) g *
        ((h.actSemi x).left : ModGL F4.tag h.K)⁻¹) := by
  have hy := ((h.actSemi x).left).2
  have hσ : Units.map (entrywiseHom (h.fieldFactor x).toRingHom) g ∈ F4.reeGamma h.K h.a := by
    have := (F4.reeGammaFieldAut h.K h.a (h.fieldFactor x) ⟨g, hg⟩).2
    rwa [ReeTag.coe_reeGammaFieldAut] at this
  rw [h.elt_of_mem hg, ← h.emb_act_apply, h.elt_of_mem (mul_mem (mul_mem hy hσ) (inv_mem hy))]
  congr 1
  apply Subtype.ext
  rw [h.act_eq_conj_mul]
  simp only [MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_inv]
  rw [ReeTag.coe_reeGammaFieldAut]

theorem fieldFactor_eq_one_of_commute_V12 (x : h.C)
    (hx : ∀ v ∈ h.V .i12, (x : G) * v = v * x) : h.fieldFactor x = 1 := by
  set y := ((h.actSemi x).left : ModGL F4.tag h.K) with hy
  have hyΓ : y ∈ F4.reeGamma h.K h.a := ((h.actSemi x).left).2
  set σ := h.fieldFactor x with hσ
  have hΓ : ∀ u, rootElt h.K h.a .i12 u ∈ F4.reeGamma h.K h.a := fun u =>
    rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)
  have key : ∀ u, y * rootElt h.K h.a .i12 (σ u) * y⁻¹ = rootElt h.K h.a .i12 u := by
    intro u
    have hv : h.elt (rootElt h.K h.a .i12 u) ∈ h.V .i12 :=
      (h.elt_mem_pull (hΓ u)).2 (rootElt_mem_rootV _ _)
    have h1 := h.conj_elt_eq x (hΓ u)
    rw [hx _ hv, mul_inv_cancel_right, entrywise_rootElt] at h1
    refine h.elt_injOn ?_ (hΓ u) h1.symm
    exact mul_mem (mul_mem hyΓ (hΓ _)) (inv_mem hyΓ)
  have hye : y ∈ F4.reeGamma h.K h.a ⊓ centralizer {invE h.K h.a} := by
    refine mem_inf.2 ⟨hyΓ, mem_centralizer_singleton_iff.2 ?_⟩
    have := key 1
    rw [map_one] at this
    change y * invE h.K h.a * y⁻¹ = invE h.K h.a at this
    calc y * invE h.K h.a = y * invE h.K h.a * y⁻¹ * y := by group
      _ = invE h.K h.a * y := by rw [this]
  refine RingEquiv.ext fun u => ?_
  have hc := mem_centralizer_singleton_iff.1
    (reeGamma_inf_centralizer_invE_le h.one_le_a h.card_K (σ u) hye)
  have h2 := key u
  rw [hc, mul_inv_cancel_right] at h2
  exact rootElt_injective h.card_K .i12 h2

theorem commute_V12_of_conj_eq {l : G} (hl : l ∈ h.L)
    (hlV : ∀ v ∈ h.V .i12, l * v * l⁻¹ ∈ h.V .i12) {v : G} (hv : v ∈ h.V .i12) (hv1 : v ≠ 1)
    (hlv : l * v * l⁻¹ = v) : ∀ w ∈ h.V .i12, l * w = w * l := by
  obtain ⟨y, hyΓ, rfl⟩ := h.exists_elt_eq hl
  have hΓ : ∀ u, rootElt h.K h.a .i12 u ∈ F4.reeGamma h.K h.a := fun u =>
    rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)
  have hE : invE h.K h.a ∈ F4.reeGamma h.K h.a := hΓ 1
  have hye : y * invE h.K h.a * y⁻¹ ∈ rootV h.K h.a .i12 := by
    have := hlV h.e h.e_f_mem_orderOf.1
    rw [Setup.e, ← h.elt_conj' hyΓ hE] at this
    exact (h.elt_mem_pull (mul_mem (mul_mem hyΓ hE) (inv_mem hyΓ))).1 this
  obtain ⟨c₀, hc₀, hc₀u⟩ := exists_conj_rootElt12_eq h.one_le_a h.card_K hyΓ hye
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hv
  have hg' : g ∈ (rootV h.K h.a .i12 : Set (ModGL F4.tag h.K)) := hg
  rw [coe_rootV h.card_K] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  rw [(sylowVec_eq_of_supp .i12 hx).2 rfl] at hgΓ hlv hv1
  set v₀ := x Idx.i12.coord with hv₀
  have hv₀0 : v₀ ≠ 0 := fun h0 => hv1 (by rw [h0, rootElt_zero, h.elt_one'])
  have hc₀1 : c₀ = 1 := by
    rw [← h.elt_conj' hyΓ (hΓ _), hc₀u] at hlv
    have := rootElt_injective h.card_K .i12 (h.elt_injOn (hΓ _) (hΓ _) hlv)
    have h2 : (c₀ - 1) * v₀ = 0 := by rw [sub_mul, this, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hv₀0)
  intro w hw
  obtain ⟨g', hg'V, hg'Γ, rfl⟩ := (h.mem_pull_iff_elt).1 hw
  have hg'' : g' ∈ (rootV h.K h.a .i12 : Set (ModGL F4.tag h.K)) := hg'V
  rw [coe_rootV h.card_K] at hg''
  obtain ⟨z, hz, rfl⟩ := hg''
  rw [(sylowVec_eq_of_supp .i12 hz).2 rfl] at hg'Γ ⊢
  refine (h.commute_elt_iff hyΓ (hΓ _)).2 ?_
  have := hc₀u (z Idx.i12.coord)
  rw [hc₀1, one_mul] at this
  calc y * rootElt h.K h.a .i12 (z Idx.i12.coord) =
      y * rootElt h.K h.a .i12 (z Idx.i12.coord) * y⁻¹ * y := by group
    _ = rootElt h.K h.a .i12 (z Idx.i12.coord) * y := by rw [this]

theorem fieldFactor_eq_one_of_V2 (x : h.C) (hxP : ∀ p ∈ h.P, (x : G) * p * (x : G)⁻¹ ∈ h.P)
    (hx2 : ∀ u : h.K, (x : G) * h.elt (rootElt h.K h.a .i2 u) * (x : G)⁻¹ *
      (h.elt (rootElt h.K h.a .i2 u))⁻¹ ∈ h.R) : h.fieldFactor x = 1 := by
  have hK := h.card_K
  set y := ((h.actSemi x).left : ModGL F4.tag h.K) with hy
  have hyΓ : y ∈ F4.reeGamma h.K h.a := ((h.actSemi x).left).2
  set σ := h.fieldFactor x with hσ
  have hΓ : ∀ u, rootElt h.K h.a .i2 u ∈ F4.reeGamma h.K h.a := fun u =>
    rootV_le_reeGamma hK .i2 (rootElt_mem_rootV _ _)
  set P₀ := F4.reeFixedPosUnipotent h.K h.a with hP₀
  have hP₀Γ : P₀ ≤ F4.reeGamma h.K h.a := inf_le_right
  have hyP : ∀ g' ∈ P₀, y * g' * y⁻¹ ∈ P₀ := by
    intro g' hg'
    have hmap := map_reeFixedPosUnipotent_exactEntrywiseAut (t := F4) (K := h.K) (a := h.a) σ
    have hg'm : g' ∈ P₀.map (exactEntrywiseAut F4.tag σ).toMonoidHom := by rw [hmap]; exact hg'
    obtain ⟨g, hg, hgg'⟩ := hg'm
    have h1 := hxP (h.elt g) ((h.elt_mem_pull (hP₀Γ hg)).2 hg)
    rw [h.conj_elt_eq x (hP₀Γ hg)] at h1
    have hσg : Units.map (entrywiseHom σ.toRingHom) g = g' := by
      rw [← hgg']
      rfl
    rw [hσg] at h1
    exact (h.elt_mem_pull (mul_mem (mul_mem hyΓ (hP₀Γ hg')) (inv_mem hyΓ))).1 h1
  have hyN : y ∈ normalizer (P₀ : Set (ModGL F4.tag h.K)) := by
    have : Finite P₀ := by
      have := h.finite_reeGamma
      exact Finite.of_injective (fun z : P₀ => (⟨z, hP₀Γ z.2⟩ : F4.reeGamma h.K h.a))
        fun z z' e => Subtype.ext (by simpa using congrArg Subtype.val e)
    have hle : P₀.map (MulAut.conj y).toMonoidHom ≤ P₀ := by
      rintro _ ⟨z, hz, rfl⟩
      exact hyP z hz
    refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [card_map_of_injective (MulAut.conj y).injective]
  have hyB : y ∈ (F4.reeFixedBorel h.K h.a : Set (ModGL F4.tag h.K)) := by
    rw [← reeGamma_inf_normalizer_reeFixedPosUnipotent]
    exact mem_inf.2 ⟨hyΓ, hyN⟩
  rw [reeFixedBorel_eq_mul, Set.mem_mul] at hyB
  obtain ⟨tp, htp, p, hp, hyeq⟩ := hyB
  rw [← torusH_eq_reeFixedTorus hK] at htp
  obtain ⟨t', rfl⟩ := htp
  have hRn : torusPair h.a t' ∈ normalizer (radR h.K h.a : Set (ModGL F4.tag h.K)) := by
    rw [(radR_spec hK).1]
    exact torusH_le_normalizer_rootSpan_inf hK (fun α hα => hα.1) ⟨t', rfl⟩
  have hPR := (radR_spec (a := h.a) hK).2.2.2
  have key : ∀ u, rootElt h.K h.a .i2 ((rootChar h.K h.a .i2 t' : h.K) * σ u) *
      (rootElt h.K h.a .i2 u)⁻¹ ∈ radR h.K h.a := by
    intro u
    have h1 := hx2 u
    rw [h.conj_elt_eq x (hΓ u), entrywise_rootElt, ← h.elt_inv' (hΓ u)] at h1
    have hm : y * rootElt h.K h.a .i2 (σ u) * y⁻¹ * (rootElt h.K h.a .i2 u)⁻¹ ∈
        F4.reeGamma h.K h.a :=
      mul_mem (mul_mem (mul_mem hyΓ (hΓ _)) (inv_mem hyΓ)) (inv_mem (hΓ u))
    rw [← h.elt_mul' (mul_mem (mul_mem hyΓ (hΓ _)) (inv_mem hyΓ)) (inv_mem (hΓ u)),
      Setup.R, h.elt_mem_pull hm] at h1
    set r₁ := p * rootElt h.K h.a .i2 (σ u) * p⁻¹ * (rootElt h.K h.a .i2 (σ u))⁻¹ with hr₁
    have hr₁R : r₁ ∈ radR h.K h.a := conj_rootElt2_mem_radR h.one_le_a hK hp (σ u)
    have hconj : y * rootElt h.K h.a .i2 (σ u) * y⁻¹ =
        (torusPair h.a t' * r₁ * (torusPair h.a t')⁻¹) *
          rootElt h.K h.a .i2 ((rootChar h.K h.a .i2 t' : h.K) * σ u) := by
      rw [← torusPair_conj_rootElt hK, ← hyeq, hr₁]
      group
    rw [hconj] at h1
    have hr₂ : torusPair h.a t' * r₁ * (torusPair h.a t')⁻¹ ∈ radR h.K h.a :=
      (mem_normalizer_iff.1 hRn r₁).1 hr₁R
    have := mul_mem (inv_mem hr₂) h1
    rwa [show (torusPair h.a t' * r₁ * (torusPair h.a t')⁻¹)⁻¹ *
      ((torusPair h.a t' * r₁ * (torusPair h.a t')⁻¹) *
        rootElt h.K h.a .i2 ((rootChar h.K h.a .i2 t' : h.K) * σ u) *
          (rootElt h.K h.a .i2 u)⁻¹) =
      rootElt h.K h.a .i2 ((rootChar h.K h.a .i2 t' : h.K) * σ u) *
        (rootElt h.K h.a .i2 u)⁻¹ by group] at this
  have hfix : ∀ u, (rootChar h.K h.a .i2 t' : h.K) * σ u = u := by
    intro u
    have h1 := key u
    have hV : rootElt h.K h.a .i2 ((rootChar h.K h.a .i2 t' : h.K) * σ u) *
        (rootElt h.K h.a .i2 u)⁻¹ ∈ rootV h.K h.a .i2 :=
      mul_mem (rootElt_mem_rootV _ _) (inv_mem (rootElt_mem_rootV _ _))
    have h2 : rootElt h.K h.a .i2 ((rootChar h.K h.a .i2 t' : h.K) * σ u) *
        (rootElt h.K h.a .i2 u)⁻¹ = 1 := by
      have := mem_inf.2 ⟨hV, h1⟩
      rwa [rootV2_inf_radR hK, mem_bot] at this
    exact rootElt_injective hK .i2 (mul_inv_eq_one.1 h2)
  have hχ : (rootChar h.K h.a .i2 t' : h.K) = 1 := by
    have := hfix 1
    rwa [map_one, mul_one] at this
  refine RingEquiv.ext fun u => ?_
  have := hfix u
  rwa [hχ, one_mul] at this

end Setup

end CFSG.LocalAnalysis.EvenBN.TwoF4
