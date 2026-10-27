module

public import CFSG.GH74.GLS.C3.Layer1.St1Conj
public import CFSG.GH74.E2.ComponentsBridge
public import CFSG.GH74.GLS.C3.Layer1.St1Thm6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.IG1516
public import CFSG.GH74.Uniqueness.SU.SU4Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainDFinal
public import CFSG.Walter.Bender1970.S3.TransitivityTools
public import CFSG.GH74.GLS.C3.Layer1.St1Prop51

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

section Prop81

variable {G : Type} [Group G] [Finite G]

@[expose] def IsNormalFourOf (S U : Subgroup G) : Prop :=
  IVK.IsFourSubgroup U ∧ U ≤ S ∧ ∀ s ∈ S, ∀ w ∈ U, s * w * s⁻¹ ∈ U

omit [Finite G] in
theorem isElementaryAbelian_of_le {A B : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hBA : B ≤ A) : CFSG.IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.of_le hA hBA

theorem exists_normalFour {S : Subgroup G} (hS : IsPGroup 2 ↥S) (h3 : 3 ≤ pRank 2 ↥S) :
    ∃ U, IsNormalFourOf S U := by
  have h3' : 3 ≤ CFSG.Open.pRank 2 S := by
    rwa [← Bg.pRank_subgroup_eq_open]
  obtain ⟨U, hUS, hUn, hUe, hUc⟩ := CFSG.GH74.Uniqueness.SU.SU4.exists_isNormalEp2 hS h3'
  refine ⟨U, ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 U).mpr hUe, by simpa using hUc⟩,
    hUS, fun s hs w hw => ?_⟩
  exact CFSG.GH74.Uniqueness.SU.SU1.conj_mem_of_le_normalizer hUn s hs w hw

theorem exists_four_le {H : Subgroup G} (h2 : 2 ≤ pRank 2 ↥H) :
    ∃ U : Subgroup G, U ≤ H ∧ IVK.IsFourSubgroup U := by
  obtain ⟨A, hAH, hAe, hAcard⟩ := exists_elemAbelian_card_pRank H
  have hAp : IsPGroup 2 ↥A := by
    have := hAe
    exact CFSG.IsElementaryAbelian.isPGroup 2 ↥A
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 2 (n := 2)
    (by rw [hAcard]; exact pow_dvd_pow 2 h2)
  have hBA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
  refine ⟨B.map A.subtype, hBA.trans hAH, isElementaryAbelian_of_le hAe hBA, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hB]
  norm_num

theorem exists_U {S : Subgroup G} (hSp : IsPGroup 2 ↥S) (h3 : 3 ≤ pRank 2 ↥S) :
    ∃ U, IsNormalFourOf S U ∧ (¬ IsCyclic ↥(centerIn S) → U ≤ centerIn S) ∧
      (IsCyclic ↥(centerIn S) →
        (∃ U', IsNormalFourOf S U' ∧ ∃ u' ∈ U', u' ∉ centerIn S ∧ NoL29Component u') →
          ∃ u' ∈ U, u' ∉ centerIn S ∧ NoL29Component u') := by
  by_cases hcyc : IsCyclic ↥(centerIn S)
  · by_cases hex : ∃ U', IsNormalFourOf S U' ∧ ∃ u' ∈ U', u' ∉ centerIn S ∧ NoL29Component u'
    · obtain ⟨U', hU', hu'⟩ := hex
      exact ⟨U', hU', fun h => absurd hcyc h, fun _ _ => hu'⟩
    · obtain ⟨U, hU⟩ := exists_normalFour hSp h3
      exact ⟨U, hU, fun h => absurd hcyc h, fun _ h => absurd h hex⟩
  ·
    have hZp : IsPGroup 2 ↥(centerIn S) := hSp.to_le inf_le_left
    have hZcomm : ∀ a ∈ centerIn S, ∀ b ∈ centerIn S, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
    have hrank : 2 ≤ pRank 2 ↥(centerIn S) := by
      by_contra hlt
      apply hcyc
      refine CFSG.ComponentClassification.AschbacherTheorem5.SevenFour.isCyclic_of_commute_of_pRank_le_one
        hZp ?_ hZcomm
      rw [← Bg.pRank_subgroup_eq_open]
      omega
    obtain ⟨U, hUZ, hUfour⟩ := exists_four_le hrank
    refine ⟨U, ⟨hUfour, hUZ.trans inf_le_left, fun s hs w hw => ?_⟩, fun _ => hUZ,
      fun h => absurd h hcyc⟩
    have h1 : s * w = w * s := Subgroup.mem_centralizer_iff.mp (hUZ hw).2 s hs
    rw [h1]
    simpa using hw

omit [Finite G] in
theorem le_normalizer_of_conj {S U : Subgroup G} (h : ∀ s ∈ S, ∀ w ∈ U, s * w * s⁻¹ ∈ U) :
    S ≤ normalizer (U : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => h g hg w hw, fun hw => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ hw
  rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this

omit [Finite G] in
theorem IsNormalFourOf.isNormalEp2 {S U : Subgroup G} (h : IsNormalFourOf S U) :
    CFSG.GH74.Uniqueness.SU.SU1.IsNormalEp2 2 S U :=
  ⟨h.2.1, le_normalizer_of_conj h.2.2,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 U).mp h.1.1, by simpa using h.1.2⟩

omit [Finite G] in
theorem commutator_top_of_simple (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hmem : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_def] at hmem
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  · exact h

theorem exists_extremal {S U : Subgroup G} (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hS : IsSylowOf 2 S ⊤) (hU : IsNormalFourOf S U) {x₀ : G} (hx₀ : orderOf x₀ = 2) :
    ∃ c : G, orderOf (c * x₀ * c⁻¹) = 2 ∧ c * x₀ * c⁻¹ ∈ S ∧
      (∀ w ∈ U, (c * x₀ * c⁻¹) * w = w * (c * x₀ * c⁻¹)) ∧
      IsSylowOf 2 (S ⊓ centralizer ({c * x₀ * c⁻¹} : Set G)) (centralizer ({c * x₀ * c⁻¹} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSle, hSp, hSdvd⟩ := isSylowOf_iff.mp hS
  have hSdvd' : ¬ 2 ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hSdvd
  have hx₀p : IsPGroup 2 (zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀, pow_one])
  obtain ⟨g₀, hg₀⟩ := exists_conj_mem_sylow_two hx₀p (hSp.toSylow hSdvd')
  have hSsub : ((hSp.toSylow hSdvd' : Sylow 2 G) : Subgroup G) = S := IsPGroup.toSylow_coe hSp hSdvd'
  rw [hSsub] at hg₀
  have hu₀S : g₀⁻¹ * x₀ * g₀ ∈ S := hg₀ x₀ (mem_zpowers x₀)
  have hu₀ord : orderOf (g₀⁻¹ * x₀ * g₀) = 2 := by
    have := orderOf_conj' g₀⁻¹ x₀
    rwa [inv_inv, hx₀] at this
  have hrel : (S ⊓ centralizer (U : Set G)).relIndex S ≤ 2 := by
    have := (CFSG.GH74.Uniqueness.SU.SU1.ig10_20_ii Nat.prime_two hSp hU.isNormalEp2).2.1
    rwa [inf_comm, Subgroup.inf_relIndex_right]
  have hperf : (u : G) → u ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ⊔ (⊥ : Subgroup G) := by
    intro u
    rw [commutator_top_of_simple hG hnab, top_sup_eq]
    exact Subgroup.mem_top u
  obtain ⟨y, -, hyQ, hySyl⟩ := Stage1.Thm3.Sec5.ig_15_16_ext_thm G (⊤ : Subgroup G) S (S ⊓ centralizer (U : Set G)) ⊥
    (g₀⁻¹ * x₀ * g₀) hS inf_le_left hrel bot_le (fun _ _ n hn => by simp at hn; simp [hn])
    (by simp) hu₀S hu₀ord (hperf _)
  have hc : (y⁻¹ * g₀⁻¹) * x₀ * (y⁻¹ * g₀⁻¹)⁻¹ = y⁻¹ * (g₀⁻¹ * x₀ * g₀) * y := by group
  refine ⟨y⁻¹ * g₀⁻¹, by rw [orderOf_conj']; exact hx₀, ?_, ?_, ?_⟩
  · rw [hc]; exact hyQ.1
  · intro w hw
    rw [hc]
    exact (Subgroup.mem_centralizer_iff.mp hyQ.2 w hw).symm
  · rw [hc]
    rwa [top_inf_eq] at hySyl

theorem prop81_cmap_inf (c : G) (H K : Subgroup G) :
    cmap c (H ⊓ K) = cmap c H ⊓ cmap c K :=
  Subgroup.map_inf H K (MulAut.conj c).toMonoidHom (MulAut.conj c).injective

theorem prop81_cmap_centralizer (c : G) (S : Subgroup G) :
    cmap c (centralizer (S : Set G)) = centralizer (cmap c S : Set G) := by
  change (Subgroup.centralizer (S : Set G)).map (MulAut.conj c).toMonoidHom =
    Subgroup.centralizer ((S.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G)
  rw [CFSG.Walter.map_centralizer_mulEquiv, Subgroup.coe_map]
  rfl

theorem prop81_cmap_centerIn (c : G) (S : Subgroup G) :
    cmap c (centerIn S) = centerIn (cmap c S) := by
  unfold centerIn
  rw [prop81_cmap_inf, prop81_cmap_centralizer]

theorem prop81_isFourSubgroup_cmap (c : G) {U : Subgroup G} (hU : IVK.IsFourSubgroup U) :
    IVK.IsFourSubgroup (cmap c U) := by
  let e : ↥U ≃* ↥(cmap c U) :=
    Subgroup.equivMapOfInjective U (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  refine ⟨CFSG.IsElementaryAbelian.of_mulEquiv e hU.1, ?_⟩
  rw [← Nat.card_congr e.toEquiv]
  exact hU.2

theorem prop81_isNormalFourOf_cmap (c : G) {S U : Subgroup G} (h : IsNormalFourOf S U) :
    IsNormalFourOf (cmap c S) (cmap c U) := by
  refine ⟨prop81_isFourSubgroup_cmap c h.1, Subgroup.map_mono h.2.1, ?_⟩
  intro s hs w hw
  refine mem_cmap.mpr ?_
  have hs' : c⁻¹ * s * c ∈ S := mem_cmap.mp hs
  have hw' : c⁻¹ * w * c ∈ U := mem_cmap.mp hw
  have hnorm := h.2.2 (c⁻¹ * s * c) hs' (c⁻¹ * w * c) hw'
  convert hnorm using 1
  group

theorem prop81_isCyclic_centerIn_cmap_iff (c : G) (S : Subgroup G) :
    IsCyclic ↥(centerIn (cmap c S)) ↔ IsCyclic ↥(centerIn S) := by
  rw [← prop81_cmap_centerIn c S]
  let e : ↥(centerIn S) ≃* ↥(cmap c (centerIn S)) :=
    Subgroup.equivMapOfInjective (centerIn S) (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective
  exact (MulEquiv.isCyclic e).symm

theorem prop81_noL29Component_cmap_iff
    (c u : G)
    (hu : pPrimeCore 2 ↥(centralizer ({u} : Set G)) = ⊥)
    (hu' : pPrimeCore 2 ↥(centralizer ({c * u * c⁻¹} : Set G)) = ⊥) :
    NoL29Component (c * u * c⁻¹) ↔ NoL29Component u := by
  let Cu := centralizer ({u} : Set G)
  let Cv := centralizer ({c * u * c⁻¹} : Set G)
  let eC : ↥Cu ≃* ↥Cv :=
    (Subgroup.equivMapOfInjective Cu (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr (centralizer_conj_eq c u).symm)
  let eBar : CentralizerBar u ≃* CentralizerBar (c * u * c⁻¹) :=
    (CFSG.GH74.E2.cenBarEquiv hu).symm.trans (eC.trans (CFSG.GH74.E2.cenBarEquiv hu'))
  constructor
  · intro h L hL
    let Lv : Subgroup (CentralizerBar (c * u * c⁻¹)) := L.map eBar.toMonoidHom
    have hLv : IsComponent Lv := CFSG.LocalCores.isComponent_map_mulEquiv eBar hL
    have hno := h Lv hLv
    intro hL2
    apply hno
    let eL : ↥L ≃* ↥Lv := by
      dsimp [Lv]
      exact Subgroup.equivMapOfInjective L eBar.toMonoidHom eBar.injective
    exact TwoThin.hasL2Model_of_mulEquiv eL hL2
  · intro h Lv hLv
    let L : Subgroup (CentralizerBar u) := Lv.map eBar.symm.toMonoidHom
    have hL : IsComponent L := CFSG.LocalCores.isComponent_map_mulEquiv eBar.symm hLv
    have hno := h L hL
    intro hL2
    apply hno
    let eL : ↥Lv ≃* ↥L := by
      dsimp [L]
      exact Subgroup.equivMapOfInjective Lv eBar.symm.toMonoidHom eBar.symm.injective
    exact TwoThin.hasL2Model_of_mulEquiv eL hL2

theorem isStar2_of_mem_normalFour {S U : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hU : IsNormalFourOf S U)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) : IsStar2 u := by
  obtain ⟨hhalf, -, hrank⟩ := CFSG.GH74.Uniqueness.SU.SU1.ig10_20_ii Nat.prime_two hS.isPGroup
    hU.isNormalEp2
  refine ⟨(hhalf u hu hu1).2.1, le_antisymm (Bg.pRank_subgroup_le one_lt_two _) ?_⟩
  have h1 : centralizer (U : Set G) ⊓ S ≤ centralizer ({u} : Set G) :=
    inf_le_left.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hu))
  have h2 : pRank 2 ↥(centralizer (U : Set G) ⊓ S) = pRank 2 ↥S := by
    rw [Bg.pRank_subgroup_eq_open, hrank, ← Bg.pRank_subgroup_eq_open]
  have h3 : pRank 2 ↥S = pRank 2 G := by
    exact (pRank_eq_of_isSylowOf hS).trans
      (Bg.pRank_mulEquiv one_lt_two (Subgroup.topEquiv (G := G)))
  rw [← h3, ← h2]
  exact Bg.pRank_subgroup_mono one_lt_two h1

omit [Finite G] in
theorem pPrimeCoreOf_eq_bot_of_eq_bot {C : Subgroup G} (h : pPrimeCore 2 ↥C = ⊥) :
    pPrimeCoreOf 2 C = ⊥ := by
  unfold pPrimeCoreOf
  rw [h]
  exact Subgroup.map_bot _

theorem exists_unbalancing_of_thm5 (T5 : St1Thm5 G) {x : G} {U : Subgroup G} (hx : orderOf x = 2)
    (hodd : pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥) (hU : IVK.IsFourSubgroup U)
    (hUx : ∀ w ∈ U, x * w = w * x) (hstar : ∀ u ∈ U, u ≠ 1 → IsStar2 u) :
    ∃ (u : G) (K : Subgroup G), u ∈ U ∧ u ≠ 1 ∧ IsUnbalancingTriple u x K := by
  set V := pPrimeCoreOf 2 (centralizer ({x} : Set G)) with hV
  have hV1 : V ≠ ⊥ := pPrimeCoreOf_ne_bot_of_ne_bot hodd
  have hUC : U ≤ centralizer ({x} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (hUx w hw).symm
  have hUN : U ≤ normalizer (V : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore (hUC hc) hg,
      fun hg => ?_⟩
    have h1 := CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore
      (Subgroup.inv_mem _ (hUC hc)) hg
    rwa [show c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g by group] at h1
  have hUe := hU.1
  have hcop : ¬ 2 ∣ Nat.card ↥V :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_pPrimeCoreOf _)
  have hgen := CFSG.Walter.le_iSup_inf_centralizer (E := U) (N := V) Nat.prime_two
    hUe.toIsMulCommutative (fun w hw => CFSG.elemPow_eq_one_of_isElementaryAbelian w hw)
    (by rw [hU.2]; norm_num) hUN hcop
  by_contra hno
  push Not at hno
  apply hV1
  rw [eq_bot_iff]
  refine hgen.trans (iSup₂_le fun e he => iSup_le fun he1 => ?_)
  by_contra hne
  have hsub : ¬ V ⊓ centralizer ({e} : Set G) ≤ pPrimeCoreOf 2 (centralizer ({e} : Set G)) := by
    rw [pPrimeCoreOf_eq_bot_of_eq_bot (T5 e (hstar e he he1))]
    intro h
    exact hne h
  obtain ⟨K, hK⟩ := exists_isUnbalancingTriple_of_not_le (hstar e he he1).1 hx
    (hUx e he).symm hsub
  exact hno e K he he1 hK

end Prop81

theorem b_st1_prop81_general
    {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hrank3 : 3 ≤ pRank 2 G) (T5 : St1Thm5 G)
    {y : G} (hy : orderOf y = 2)
    (hodd : pPrimeCore 2 ↥(centralizer ({y} : Set G)) ≠ ⊥) :
    ∃ (S U : Subgroup G) (u : G) (J W : Subgroup G), Config8 y S U u J W := by
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (⊤ : Subgroup G)
  have hSp : IsPGroup 2 ↥S := hS.isPGroup
  have hSrank : pRank 2 ↥S = pRank 2 G :=
    (pRank_eq_of_isSylowOf hS).trans
      (Bg.pRank_mulEquiv one_lt_two (Subgroup.topEquiv (G := G)))
  have h3S : 3 ≤ pRank 2 ↥S := by rw [hSrank]; exact hrank3
  obtain ⟨U, hU, hUb, hUc⟩ := exists_U hSp h3S
  obtain ⟨c, hy1o, hy1S, hy1U, hy1T⟩ := exists_extremal hG hnab hS hU hy
  let S0 : Subgroup G := cmap c⁻¹ S
  let U0 : Subgroup G := cmap c⁻¹ U
  have hyS0 : y ∈ S0 := by
    refine mem_cmap.mpr ?_
    simpa using hy1S
  have hS0 : IsSylowOf 2 S0 ⊤ := by
    have h := isSylowOf_cmap hS c⁻¹
    have htop : cmap c⁻¹ (⊤ : Subgroup G) = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective
    simpa [S0, htop] using h
  have hT0 : IsSylowOf 2 (S0 ⊓ centralizer ({y} : Set G)) (centralizer ({y} : Set G)) := by
    have h := isSylowOf_cmap hy1T c⁻¹
    have hC : cmap c⁻¹ (centralizer ({c * y * c⁻¹} : Set G)) =
        centralizer ({y} : Set G) := by
      have h' := (centralizer_conj_eq (c⁻¹) (c * y * c⁻¹)).symm
      have hy_eq : c⁻¹ * (c * y * c⁻¹) * c = y := by group
      simpa [hy_eq] using h'
    have hI : cmap c⁻¹ (S ⊓ centralizer ({c * y * c⁻¹} : Set G)) =
        S0 ⊓ centralizer ({y} : Set G) := by
      rw [prop81_cmap_inf, hC]
    rwa [hI, hC] at h
  have hU0four : IVK.IsFourSubgroup U0 := prop81_isFourSubgroup_cmap c⁻¹ hU.1
  have hU0le : U0 ≤ S0 := Subgroup.map_mono hU.2.1
  have hU0normal : ∀ s ∈ S0, ∀ w ∈ U0, s * w * s⁻¹ ∈ U0 := by
    intro s hs w hw
    refine mem_cmap.mpr ?_
    have hs' : c * s * c⁻¹ ∈ S := by simpa using (mem_cmap.mp hs)
    have hw' : c * w * c⁻¹ ∈ U := by simpa using (mem_cmap.mp hw)
    have hnorm := hU.2.2 (c * s * c⁻¹) hs' (c * w * c⁻¹) hw'
    convert hnorm using 1
    group
  have hU0 : IsNormalFourOf S0 U0 := ⟨hU0four, hU0le, hU0normal⟩
  have hU0central : ¬ IsCyclic ↥(centerIn S0) → U0 ≤ centerIn S0 := by
    intro hcyc0
    have hcycS : ¬ IsCyclic ↥(centerIn S) := fun hc =>
      hcyc0 ((prop81_isCyclic_centerIn_cmap_iff c⁻¹ S).mpr hc)
    intro w hw
    have hw' : c * w * c⁻¹ ∈ U := by simpa using (mem_cmap.mp hw)
    have hwS : c * w * c⁻¹ ∈ centerIn S := hUb hcycS hw'
    have hcenter : centerIn S0 = cmap c⁻¹ (centerIn S) :=
      (prop81_cmap_centerIn c⁻¹ S).symm
    rw [hcenter]
    refine mem_cmap.mpr ?_
    convert hwS using 1
    group
  have hU0noL29 : IsCyclic ↥(centerIn S0) →
      (∃ U0' : Subgroup G, IVK.IsFourSubgroup U0' ∧ U0' ≤ S0 ∧
        (∀ s ∈ S0, ∀ w ∈ U0', s * w * s⁻¹ ∈ U0') ∧
        ∃ u0' ∈ U0', u0' ∉ centerIn S0 ∧ NoL29Component u0') →
      ∃ u' ∈ U0, u' ∉ centerIn S0 ∧ NoL29Component u' := by
    intro hcyc0 hcomp0
    have hcycS : IsCyclic ↥(centerIn S) :=
      (prop81_isCyclic_centerIn_cmap_iff c⁻¹ S).mp hcyc0
    obtain ⟨U0', hU0'four, hU0'le, hU0'normal, hrest⟩ := hcomp0
    obtain ⟨u0', hu0', hu0'Z, hno0⟩ := hrest
    let U' : Subgroup G := cmap c U0'
    have hU' : IsNormalFourOf S U' := by
      have h := prop81_isNormalFourOf_cmap c ⟨hU0'four, hU0'le, hU0'normal⟩
      have hS_eq : cmap c S0 = S := by
        rw [show S0 = cmap c⁻¹ S from rfl, cmap_cmap, mul_inv_cancel]
        ext x
        simp [mem_cmap]
      simpa [U', hS_eq] using h
    let u' : G := c * u0' * c⁻¹
    have hu' : u' ∈ U' := by
      refine mem_cmap.mpr ?_
      have h_eq : c⁻¹ * u' * c = u0' := by
        dsimp [u']
        group
      rwa [h_eq]
    have hu'Z : u' ∉ centerIn S := by
      intro h
      apply hu0'Z
      have hcenter : centerIn S0 = cmap c⁻¹ (centerIn S) :=
        (prop81_cmap_centerIn c⁻¹ S).symm
      rw [hcenter]
      refine mem_cmap.mpr ?_
      simpa [u'] using h
    have hu0'1 : u0' ≠ 1 := by
      intro h
      apply hu0'Z
      rw [h]
      exact one_mem _
    have hu'1 : u' ≠ 1 := by
      intro h
      apply hu'Z
      rw [h]
      exact one_mem _
    have hcore0 : pPrimeCore 2 ↥(centralizer ({u0'} : Set G)) = ⊥ :=
      T5 u0' (isStar2_of_mem_normalFour hS0 ⟨hU0'four, hU0'le, hU0'normal⟩ hu0' hu0'1)
    have hcore' : pPrimeCore 2 ↥(centralizer ({u'} : Set G)) = ⊥ :=
      T5 u' (isStar2_of_mem_normalFour hS hU' hu' hu'1)
    have hno' : NoL29Component u' :=
      (prop81_noL29Component_cmap_iff c u0' hcore0 hcore').mpr hno0
    obtain ⟨uold, huoldU, huoldZ, hnoold⟩ := hUc hcycS ⟨U', hU', u', hu', hu'Z, hno'⟩
    refine ⟨c⁻¹ * uold * c, ?_, ?_, ?_⟩
    · refine mem_cmap.mpr ?_
      convert huoldU using 1
      group
    · intro h
      apply huoldZ
      have hcenter : centerIn S0 = cmap c⁻¹ (centerIn S) :=
        (prop81_cmap_centerIn c⁻¹ S).symm
      rw [hcenter] at h
      have h' : c * (c⁻¹ * uold * c) * c⁻¹ ∈ centerIn S := by
        simpa using (mem_cmap.mp h)
      have h_eq : c * (c⁻¹ * uold * c) * c⁻¹ = uold := by group
      rwa [h_eq] at h'
    · have huold1 : uold ≠ 1 := by
        intro h
        apply huoldZ
        rw [h]
        exact one_mem _
      have hw1 : c⁻¹ * uold * c ≠ 1 := by
        intro h
        apply huoldZ
        have h_eq : c * (c⁻¹ * uold * c) * c⁻¹ = uold := by group
        have h1 : c * (c⁻¹ * uold * c) * c⁻¹ = 1 := by rw [h]; group
        rw [← h_eq]
        exact h1.symm ▸ one_mem _
      have hcoreold : pPrimeCore 2 ↥(centralizer ({uold} : Set G)) = ⊥ :=
        T5 uold (isStar2_of_mem_normalFour hS hU huoldU huold1)
      have hwU0 : c⁻¹ * uold * c ∈ U0 := by
        refine mem_cmap.mpr ?_
        convert huoldU using 1
        group
      have hcorew : pPrimeCore 2 ↥(centralizer ({c⁻¹ * uold * c} : Set G)) = ⊥ :=
        T5 (c⁻¹ * uold * c) (isStar2_of_mem_normalFour hS0 hU0 hwU0 hw1)
      have hcorew' : pPrimeCore 2 ↥(centralizer ({c⁻¹ * uold * c⁻¹⁻¹} : Set G)) = ⊥ := by
        rw [show c⁻¹ * uold * c⁻¹⁻¹ = c⁻¹ * uold * c by group]
        exact hcorew
      have hno_w : NoL29Component (c⁻¹ * uold * c) := by
        simpa using (prop81_noL29Component_cmap_iff c⁻¹ uold hcoreold hcorew').mpr hnoold
      exact hno_w
  have hyU0 : ∀ w ∈ U0, y * w = w * y := by
    intro w hw
    have hw' : c * w * c⁻¹ ∈ U := by simpa using (mem_cmap.mp hw)
    have h := hy1U (c * w * c⁻¹) hw'
    have h' := congrArg (fun t => c⁻¹ * t * c) h
    have hL : c⁻¹ * ((c * y * c⁻¹) * (c * w * c⁻¹)) * c = y * w := by group
    have hR : c⁻¹ * ((c * w * c⁻¹) * (c * y * c⁻¹)) * c = w * y := by group
    rw [hL, hR] at h'
    exact h'
  obtain ⟨u₁, J₁, hu₁, hu₁1, hJ₁⟩ :=
    exists_unbalancing_of_thm5 T5 hy hodd hU0four hyU0
      (fun u hu hu1 => isStar2_of_mem_normalFour hS0 hU0 hu hu1)
  have hex : ∃ (u : G) (J : Subgroup G), u ∈ U0 ∧ u ≠ 1 ∧ IsUnbalancingTriple u y J ∧
      ((∃ (u' : G) (K' : Subgroup G), u' ∈ U0 ∧ u' ≠ 1 ∧ u' ∈ centerIn S0 ∧
        IsUnbalancingTriple u' y K') → u ∈ centerIn S0) := by
    by_cases hz : ∃ (u' : G) (K' : Subgroup G), u' ∈ U0 ∧ u' ≠ 1 ∧ u' ∈ centerIn S0 ∧
        IsUnbalancingTriple u' y K'
    · obtain ⟨u', K', hu', hu'1, hzu', hK'⟩ := hz
      exact ⟨u', K', hu', hu'1, hK', fun _ => hzu'⟩
    · exact ⟨u₁, J₁, hu₁, hu₁1, hJ₁, fun h => absurd h hz⟩
  obtain ⟨u, J, hu, hu1, hJ, hcen⟩ := hex
  have hyN : y ∈ NxK u J := ⟨hJ.2.2.1, hJ.2.2.2.1⟩
  have hyp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨W, hW, hyW⟩ := exists_isSylowOf_ge (N := NxK u J) (K := zpowers y)
    (zpowers_le.mpr hyN) hyp
  exact ⟨S0, U0, u, J, W,
    { ord_x := hy
      oddCore := hodd
      sylow_S := hS0
      sylow_T := hT0
      four := hU0four
      U_le := hU0le
      U_normal := hU0normal
      U_central := hU0central
      U_noL29 := hU0noL29
      x_mem := ⟨hyS0, hyU0⟩
      u_mem := ⟨hu, hu1⟩
      unbal := hJ
      u_central := hcen
      sylow_W := hW
      x_mem_W := hyW (mem_zpowers y) }⟩

theorem b_st1_prop81
    : B_st1_prop81 := by
  intro G _ _ hG _ T5 ⟨x₀, hx₀, hodd₀⟩
  have hrank3 : 3 ≤ pRank 2 G := by
    rw [hG.pRank_eq_four]
    omega
  obtain ⟨S, U, u, K, W, hcfg⟩ :=
    b_st1_prop81_general hG.kproper.1 hG.kproper.2.1 hrank3 T5 hx₀ hodd₀
  exact ⟨x₀, S, U, u, K, W, hcfg⟩

end CFSG.GH74.GLS
