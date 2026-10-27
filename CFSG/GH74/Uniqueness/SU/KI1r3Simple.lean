module

public import CFSG.GH74.Uniqueness.SU.KI1r3Fitting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreFreeTwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GH74.KGH
public import CFSG.Walter.TwoRank
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GH74.Uniqueness.SU
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]


open CFSG.LocalCores in
theorem Cfg.fitting_eq_bot (hpow : R3PowStmt) (hr3 : Open.twoRank H = 3) {T : Sylow 2 H} {x : H}
    (h : Cfg H T x) : fittingSubgroup H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Fitting_eq_pcore H 2 h.odd]
  exact h.normal_two_subgroup_eq_bot hpow hr3 pCore_normal pCore_isPGroup

open CFSG.LocalCores in
theorem Cfg.exists_component (hF : fittingSubgroup H = ⊥) {T : Sylow 2 H} {x : H} (h : Cfg H T x) :
    ∃ L : Subgroup H, IsComponent L := by
  by_contra hno
  push Not at hno
  have hl : layer H = ⊥ := by
    have : {K : Subgroup H | IsComponent K} = ∅ := by
      ext K; simp [hno K]
    rw [layer, this, sSup_empty]
  have hFb : generalizedFitting H = ⊥ := by
    rw [generalizedFitting, hF, hl]; simp
  have hc := centralizer_generalizedFitting_le H
  rw [hFb] at hc
  have hx1 : x = 1 := by
    have hxc : x ∈ centralizer ((⊥ : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hg' : g ∈ (⊥ : Subgroup H) := hg
      rw [Subgroup.mem_bot.mp hg']
      simp
    have := hc hxc
    exact Subgroup.mem_bot.mp this
  have := h.x2
  rw [hx1, orderOf_one] at this
  omega

open CFSG.LocalCores in
theorem Cfg.component_center_bot (hF : fittingSubgroup H = ⊥) {T : Sylow 2 H} {x : H}
    (_h : Cfg H T x) {L : Subgroup H} (hL : IsComponent L) :
    ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1 := by
  intro z hzL hzc
  have hzE : z ∈ layer H := le_sSup (show L ∈ {K : Subgroup H | IsComponent K} from hL) hzL
  have hcentral : ∀ g ∈ layer H, z * g = g * z := by
    have hle : layer H ≤ centralizer ({z} : Set H) := by
      refine sSup_le fun K hK => ?_
      rcases distinct_components_commute hL hK with hLK | hLK
      · rw [← hLK]
        intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hzc l hl).symm
      · intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLK hzL
        have h2 := Subgroup.mem_centralizer_iff.mp this k hk
        exact h2
    intro g hg
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm
  have hzF : z ∈ fittingSubgroup H := by
    apply CFSG.ComponentClassification.UnbalancedLayer.center_layer_le_fittingSubgroup
    refine ⟨⟨z, hzE⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hcentral g g.2).symm)
  rw [hF] at hzF
  exact Subgroup.mem_bot.mp hzF


omit [Finite H] in
theorem component_simple_data {L : Subgroup H}
    (hL : IsComponent L) (hZ : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1) :
    IsSimpleGroup ↥L ∧ ∃ a b : ↥L, a * b ≠ b * a := by
  have hcen : Subgroup.center ↥L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply Subtype.ext
    exact hZ z z.2 (fun l hl => congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩).symm)
  obtain ⟨-, hsimple, a, b, hab⟩ := hL.1
  have := hsimple
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem exists_E4_in_component {L : Subgroup H}
    (hL : IsComponent L) (hZ : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1) :
    ∃ E : Subgroup H, E ≤ L ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨hsimple, hnab⟩ := component_simple_data hL hZ
  have := hsimple
  have heven : Even (Nat.card ↥L) := CFSG.GH74.even_card_of_nonabelian_simple hnab
  have h2 : 2 ≤ Open.twoRank ↥L := CFSG.Walter.two_le_twoRank ↥L hnab heven
  obtain ⟨E', -, hE'el, hE'card⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two
    (H := (⊤ : Subgroup ↥L)) (k := 2) h2
  refine ⟨E'.map L.subtype, Subgroup.map_subtype_le E', ?_, ?_⟩
  · rw [SU1.isElemAbelian_iff] at hE'el ⊢
    obtain ⟨hc, hp⟩ := hE'el
    constructor
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hc a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (hp a ha)
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hE'card]
    norm_num


open CFSG.LocalCores in
theorem Cfg.component_normalized_of_centerless {T : Sylow 2 H} {x : H}
    (h : Cfg H T x) {L : Subgroup H} (hL : IsComponent L)
    (hZL : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1) : ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
  by_contra hnot
  push Not at hnot
  have hxx := h.mul_self_x
  set L' : Subgroup H := L.map (MulAut.conj x).toMonoidHom with hL'def
  have hL' : IsComponent L' := isComponent_map_mulEquiv (MulAut.conj x) hL
  have hmemL' : ∀ l ∈ L, x * l * x⁻¹ ∈ L' := fun l hl => ⟨l, hl, by simp [MulAut.conj_apply]⟩
  have hLne : L ≠ L' := by
    intro heq
    obtain ⟨l, hl, hxl⟩ := hnot
    exact hxl (heq ▸ hmemL' l hl)
  have hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := by
    rcases distinct_components_commute hL hL' with h1 | h1
    · exact absurd h1 hLne
    · intro a ha b hb
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 ha
      exact (Subgroup.mem_centralizer_iff.mp this b hb).symm
  have hZL' : ∀ z ∈ L', (∀ l ∈ L', z * l = l * z) → z = 1 := by
    rintro _ ⟨l, hl, rfl⟩ hzc
    have hc1 : (MulAut.conj x).toMonoidHom l = x * l * x⁻¹ := by simp [MulAut.conj_apply]
    have h1 : l = 1 := hZL l hl (fun l' hl' => by
      have h2 := hzc (x * l' * x⁻¹) (hmemL' l' hl')
      rw [hc1] at h2
      have e : x * (l * l') * x⁻¹ = x * (l' * l) * x⁻¹ := by
        calc x * (l * l') * x⁻¹ = (x * l * x⁻¹) * (x * l' * x⁻¹) := by group
          _ = (x * l' * x⁻¹) * (x * l * x⁻¹) := h2
          _ = x * (l' * l) * x⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e))
    rw [h1]
    exact map_one _
  obtain ⟨E, hEL, hEel, hEcard⟩ := exists_E4_in_component hL hZL
  let dE : ↥E →* H :=
    MonoidHom.mk' (fun e => (e : H) * (x * (e : H) * x⁻¹)) (by
      intro e₁ e₂
      have h1 : (e₂ : H) * (x * (e₁ : H) * x⁻¹) = (x * (e₁ : H) * x⁻¹) * (e₂ : H) :=
        hcomm _ (hEL e₂.2) _ (hmemL' _ (hEL e₁.2))
      calc ((e₁ * e₂ : ↥E) : H) * (x * ((e₁ * e₂ : ↥E) : H) * x⁻¹)
          = (e₁ : H) * ((e₂ : H) * (x * (e₁ : H) * x⁻¹)) * (x * (e₂ : H) * x⁻¹) := by
            simp only [Subgroup.coe_mul]; group
        _ = (e₁ : H) * ((x * (e₁ : H) * x⁻¹) * (e₂ : H)) * (x * (e₂ : H) * x⁻¹) := by rw [h1]
        _ = ((e₁ : H) * (x * (e₁ : H) * x⁻¹)) * ((e₂ : H) * (x * (e₂ : H) * x⁻¹)) := by group)
  have hdE : ∀ e : ↥E, dE e = (e : H) * (x * (e : H) * x⁻¹) := fun e => rfl
  have hinj : Function.Injective dE := by
    rw [injective_iff_map_eq_one]
    intro e he
    rw [hdE] at he
    have heL : (e : H) ∈ L := hEL e.2
    have hxe : x * (e : H) * x⁻¹ ∈ L' := hmemL' _ heL
    have h1 : (e : H) = (x * (e : H) * x⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left he
    have heL' : (e : H) ∈ L' := by
      rw [h1]; exact L'.inv_mem hxe
    have : (e : H) = 1 := hZL' (e : H) heL' (fun l' hl' => hcomm _ heL _ hl')
    exact Subtype.ext this
  set V : Subgroup H := dE.range with hV
  have hVcard : Nat.card V = 4 := by
    rw [← hEcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hVel : Open.IsElemAbelian 2 V := by
    rw [SU1.isElemAbelian_iff]
    constructor
    · rintro _ ⟨e₁, rfl⟩ _ ⟨e₂, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (SU1.isElemAbelian_iff.mp hEel).1 _ e₁.2 _ e₂.2
    · rintro _ ⟨e, rfl⟩
      rw [← map_pow]
      have : e ^ 2 = 1 := by
        apply Subtype.ext
        simpa using (SU1.isElemAbelian_iff.mp hEel).2 _ e.2
      rw [this, map_one]
  have hVx : ∀ v ∈ V, v * x = x * v := by
    rintro _ ⟨e, rfl⟩
    rw [hdE]
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have h1 : (e : H) * (x * (e : H) * x) = (x * (e : H) * x) * (e : H) := by
      have := hcomm _ (hEL e.2) _ (hmemL' _ (hEL e.2))
      rwa [hxi] at this
    rw [hxi]
    calc (e : H) * (x * (e : H) * x) * x = (e : H) * x * (e : H) * (x * x) := by group
      _ = (e : H) * x * (e : H) := by rw [hxx]; group
      _ = (x * x) * (e : H) * x * (e : H) := by rw [hxx]; group
      _ = x * ((x * (e : H) * x) * (e : H)) := by group
      _ = x * ((e : H) * (x * (e : H) * x)) := by rw [h1]
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hL'perf : ⁅L', L'⁆ = L' := Subgroup.isPerfect_iff.mp hL'.1.1
  have hperf : ⁅L ⊔ L', L ⊔ L'⁆ = L ⊔ L' := by
    apply le_antisymm
    · refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
      rw [commutatorElement_def]
      exact (L ⊔ L').mul_mem ((L ⊔ L').mul_mem ((L ⊔ L').mul_mem ha hb) ((L ⊔ L').inv_mem ha))
        ((L ⊔ L').inv_mem hb)
    · refine sup_le ?_ ?_
      · calc L = ⁅L, L⁆ := hLperf.symm
          _ ≤ ⁅L ⊔ L', L ⊔ L'⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
      · calc L' = ⁅L', L'⁆ := hL'perf.symm
          _ ≤ ⁅L ⊔ L', L ⊔ L'⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  have hxP : x ∉ L ⊔ L' := h.x_notMem_of_perfect hperf
  have hxV : x ∉ V := by
    rintro ⟨e, he⟩
    rw [hdE] at he
    apply hxP
    rw [← he]
    exact (L ⊔ L').mul_mem (Subgroup.mem_sup_left (hEL e.2))
      (Subgroup.mem_sup_right (hmemL' _ (hEL e.2)))
  obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hVel (by omega) hxx hVx hxV
  exact h.no_E8 hel hc8 1 (by simpa using Subgroup.mem_sup_right (mem_zpowers x))


open CFSG.LocalCores in
theorem Cfg.component_normalized (hF : fittingSubgroup H = ⊥) {T : Sylow 2 H} {x : H}
    (h : Cfg H T x) {L : Subgroup H} (hL : IsComponent L) : ∀ l ∈ L, x * l * x⁻¹ ∈ L :=
  h.component_normalized_of_centerless hL (h.component_center_bot hF hL)

theorem exists_fixed_involution_of_even {X : Subgroup H} (hX : 2 ∣ Nat.card X) {x : H}
    (hx : x * x = 1) (hxX : ∀ s ∈ X, x * s * x⁻¹ ∈ X) :
    ∃ u ∈ X, u ≠ 1 ∧ u * u = 1 ∧ x * u * x⁻¹ = u := by
  classical
  let f : Function.End X := fun s => ⟨x * s * x⁻¹, hxX s s.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    change (f ∘ f) = id
    funext s
    apply Subtype.ext
    change x * (x * (s : H) * x⁻¹) * x⁻¹ = s
    calc x * (x * (s : H) * x⁻¹) * x⁻¹ = (x * x) * (s : H) * (x * x)⁻¹ := by group
      _ = s := by rw [hx]; group
  let : Fintype X := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) hf
  have hY : Nat.card ↥(X ⊓ centralizer ({x} : Set H)) = Fintype.card (Function.fixedPoints f) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.mp s.2).1⟩, ?_⟩
        invFun := fun s => ⟨s.1.1, Subgroup.mem_inf.mpr ⟨s.1.2, ?_⟩⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    ·
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp s.2).2
      apply Subtype.ext
      change x * (s : H) * x⁻¹ = s
      calc x * (s : H) * x⁻¹ = (s : H) * x * x⁻¹ := by rw [← h1]
        _ = s := by group
    · have h1 : x * (s.1 : H) * x⁻¹ = s.1 := congrArg Subtype.val s.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (s.1 : H) * x = x * (s.1 : H) * x⁻¹ * x := by rw [h1]
        _ = x * (s.1 : H) := by group
  have hdvd : 2 ∣ Nat.card ↥(X ⊓ centralizer ({x} : Set H)) := by
    have hX' : 2 ∣ Fintype.card X := by rw [← Nat.card_eq_fintype_card]; exact hX
    have h2 : 2 ∣ Fintype.card (Function.fixedPoints f) := (hmod.dvd_iff (dvd_refl 2)).mp hX'
    rw [hY]; exact h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ centralizer ({x} : Set H))) 2 hdvd
  have hg' : orderOf (g : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  refine ⟨(g : H), (Subgroup.mem_inf.mp g.2).1, ?_, mul_self_eq_one_of_orderOf_two hg', ?_⟩
  · intro h1; rw [h1, orderOf_one] at hg'; omega
  · have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).2
    calc x * (g : H) * x⁻¹ = (g : H) * x * x⁻¹ := by rw [← h1]
      _ = g := by group


theorem Cfg.x_notMem_component {T : Sylow 2 H} {x : H} (h : Cfg H T x) {L : Subgroup H}
    (hL : IsComponent L) : x ∉ L :=
  h.x_notMem_of_perfect (Subgroup.isPerfect_iff.mp hL.1.1)

omit [Finite H] in
theorem isElemAbelian_of_class {K : Type} [Group K] (V : Subgroup K) [IsElementaryAbelian 2 V] :
    Open.IsElemAbelian 2 V := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr inferInstance

theorem four_group_fixed_of_inner {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (G : K) (hG2 : (MulAut.conj G) ^ 2 = 1) :
    ∃ V : Subgroup K, (∀ v ∈ V, MulAut.conj G v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨V, hV, hVel, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup.exists_four_group_le_fixedSubgroup_conj
      hnab G hG2
  exact ⟨V, fun v hv => hV hv, isElemAbelian_of_class V, hVcard⟩

open CFSG.LocalCores in
theorem Cfg.component_not_inner_of_centerless {T : Sylow 2 H} {x : H} (h : Cfg H T x)
    {L : Subgroup H} (hL : IsComponent L) (hZL : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1)
    (hxL : ∀ l ∈ L, x * l * x⁻¹ ∈ L) : ¬ ∃ g ∈ L, ∀ l ∈ L, x * l * x⁻¹ = g * l * g⁻¹ := by
  rintro ⟨g, hgL, hg⟩
  have hxx := h.mul_self_x
  obtain ⟨hsimple, hnab⟩ := component_simple_data hL hZL
  have := hsimple
  set G : ↥L := ⟨g, hgL⟩ with hGdef
  have hG2 : (MulAut.conj G) ^ 2 = 1 := by
    ext l
    rw [pow_two, MulAut.mul_apply]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.one_apply]
    have h1 : (g : H) * (l : H) * g⁻¹ = x * (l : H) * x⁻¹ := (hg l l.2).symm
    have h2 : g * (x * (l : H) * x⁻¹) * g⁻¹ = x * (x * (l : H) * x⁻¹) * x⁻¹ :=
      (hg _ (hxL l l.2)).symm
    show g * (g * (l : H) * g⁻¹) * g⁻¹ = l
    rw [h1, h2]
    calc x * (x * (l : H) * x⁻¹) * x⁻¹ = (x * x) * (l : H) * (x * x)⁻¹ := by group
      _ = l := by rw [hxx]; group
  obtain ⟨V, hVfix, hVel', hVcard⟩ := four_group_fixed_of_inner hnab G hG2
  set W : Subgroup H := V.map L.subtype with hW
  have hWel : Open.IsElemAbelian 2 W := by
    rw [SU1.isElemAbelian_iff] at hVel' ⊢
    obtain ⟨hc, hp⟩ := hVel'
    constructor
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hc a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (hp a ha)
  have hWcard : Nat.card W = 4 := by
    rw [hW, Subgroup.card_map_of_injective L.subtype_injective]; exact hVcard
  have hWx : ∀ w ∈ W, w * x = x * w := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 : MulAut.conj G v = v := hVfix v hv
    have h2 : g * (v : H) * g⁻¹ = v := congrArg Subtype.val h1
    have h3 : x * (v : H) * x⁻¹ = v := by rw [hg v v.2]; exact h2
    show (v : H) * x = x * v
    calc (v : H) * x = x * (v : H) * x⁻¹ * x := by rw [h3]
      _ = x * v := by group
  have hxW : x ∉ W := fun hx => h.x_notMem_component hL (by
    obtain ⟨v, -, hv⟩ := hx
    rw [← hv]; exact v.2)
  obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hWel (by omega) hxx hWx hxW
  exact h.no_E8 hel hc8 1 (by simpa using Subgroup.mem_sup_right (mem_zpowers x))


open CFSG.LocalCores in
theorem Cfg.component_not_inner (hF : fittingSubgroup H = ⊥) {T : Sylow 2 H} {x : H} (h : Cfg H T x)
    {L : Subgroup H} (hL : IsComponent L) (hxL : ∀ l ∈ L, x * l * x⁻¹ ∈ L) :
    ¬ ∃ g ∈ L, ∀ l ∈ L, x * l * x⁻¹ = g * l * g⁻¹ :=
  h.component_not_inner_of_centerless hL (h.component_center_bot hF hL) hxL

open CFSG.LocalCores in
theorem Cfg.component_unique (hF : fittingSubgroup H = ⊥) {T : Sylow 2 H} {x : H} (h : Cfg H T x)
    {L K : Subgroup H} (hL : IsComponent L) (hK : IsComponent K) : K = L := by
  by_contra hne
  have hxx := h.mul_self_x
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxL := h.component_normalized hF hL
  have hZL := h.component_center_bot hF hL
  have hZK := h.component_center_bot hF hK
  have hKC : K ≤ centralizer (L : Set H) := by
    rcases distinct_components_commute hK hL with h1 | h1
    · exact absurd h1 hne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hxL' : ∀ l ∈ L, x * l * x ∈ L := fun l hl => by
    have := hxL l hl; rwa [hxi] at this
  have hxC : ∀ c ∈ centralizer (L : Set H), x * c * x⁻¹ ∈ centralizer (L : Set H) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := Subgroup.mem_centralizer_iff.mp hc (x * l * x) (hxL' l hl)
    rw [hxi]
    have e1 : x * ((x * l * x) * c) * x = l * (x * c * x) := by
      calc x * ((x * l * x) * c) * x = (x * x) * l * (x * c * x) := by group
        _ = l * (x * c * x) := by rw [hxx]; group
    have e2 : x * (c * (x * l * x)) * x = (x * c * x) * l := by
      calc x * (c * (x * l * x)) * x = (x * c * x) * l * (x * x) := by group
        _ = (x * c * x) * l := by rw [hxx]; group
    rw [← e1, ← e2, h1]
  obtain ⟨hKsimple, hKnab⟩ := component_simple_data hK hZK
  obtain ⟨hLsimple, hLnab⟩ := component_simple_data hL hZL
  have := hKsimple
  have := hLsimple
  have hKeven : Even (Nat.card ↥K) := CFSG.GH74.even_card_of_nonabelian_simple hKnab
  have hLeven : Even (Nat.card ↥L) := CFSG.GH74.even_card_of_nonabelian_simple hLnab
  have hC2 : 2 ∣ Nat.card (centralizer (L : Set H)) :=
    (even_iff_two_dvd.mp hKeven).trans (Subgroup.card_dvd_of_le hKC)
  obtain ⟨u, huC, hu1, hu2, hxu⟩ := exists_fixed_involution_of_even hC2 hxx hxC
  obtain ⟨v, hvL, hv1, hv2, hxv⟩ := exists_fixed_involution_of_even (X := L)
    (even_iff_two_dvd.mp hLeven) hxx hxL
  have huv : u * v = v * u := (Subgroup.mem_centralizer_iff.mp huC v hvL).symm
  have hnot : v ∉ zpowers u := by
    intro hmem
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hu2 hmem with h1 | h1
    · exact hv1 h1
    · apply hu1
      refine hZL u (by rw [← h1]; exact hvL) (fun l hl => ?_)
      exact (Subgroup.mem_centralizer_iff.mp huC l hl).symm
  obtain ⟨hEel, hEcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := u) (y := v)
    (by rw [pow_two]; exact hu2) (by rw [pow_two]; exact hv2) hu1 hnot huv
  have hEx : ∀ e ∈ zpowers u ⊔ zpowers v, e * x = x * e := by
    have : zpowers u ⊔ zpowers v ≤ centralizer ({x} : Set H) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        symm
        calc x * u = x * u * x⁻¹ * x := by group
          _ = u * x := by rw [hxu]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        symm
        calc x * v = x * v * x⁻¹ * x := by group
          _ = v * x := by rw [hxv]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (this he)
  have hxE : x ∉ zpowers u ⊔ zpowers v := by
    intro hx
    have hcomm' : ∀ a ∈ zpowers u, ∀ b ∈ zpowers v, a * b = b * a := by
      rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
      exact ((Commute.zpow_zpow (show Commute u v from huv) m n)).eq
    obtain ⟨a, ha, b, hb, hab⟩ := SU1.mem_sup_of_commute hcomm' hx
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hu2 ha with ha1 | ha1
    · rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hv2 hb with hb1 | hb1
      ·
        have := h.x2
        rw [ha1, hb1, one_mul] at hab
        rw [← hab, orderOf_one] at this
        omega
      ·
        rw [ha1, hb1, one_mul] at hab
        exact h.x_notMem_component hL (hab ▸ hvL)
    · rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hv2 hb with hb1 | hb1
      ·
        rw [ha1, hb1, mul_one] at hab
        apply h.component_not_inner hF hL hxL
        refine ⟨1, one_mem _, fun l hl => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp (hab ▸ huC) l hl
        calc x * l * x⁻¹ = l * x * x⁻¹ := by rw [← this]
          _ = 1 * l * 1⁻¹ := by group
      ·
        rw [ha1, hb1] at hab
        apply h.component_not_inner hF hL hxL
        refine ⟨v, hvL, fun l hl => ?_⟩
        rw [← hab]
        calc u * v * l * (u * v)⁻¹ = u * (v * l * v⁻¹) * u⁻¹ := by group
          _ = v * l * v⁻¹ := by
            have hvl : v * l * v⁻¹ ∈ L := L.mul_mem (L.mul_mem hvL hl) (L.inv_mem hvL)
            have := (Subgroup.mem_centralizer_iff.mp huC _ hvl)
            calc u * (v * l * v⁻¹) * u⁻¹ = (v * l * v⁻¹) * u * u⁻¹ := by rw [this]
              _ = v * l * v⁻¹ := by group
  obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hEel (by rw [hEcard]; norm_num) hxx hEx hxE
  exact h.no_E8 hel hc8 1 (by simpa using Subgroup.mem_sup_right (mem_zpowers x))


open CFSG.LocalCores in
theorem Cfg.fstar_simple (hF : fittingSubgroup H = ⊥) {T : Sylow 2 H} {x : H} (h : Cfg H T x) :
    IsSimpleGroup ↥(generalizedFitting H) ∧
      (∃ a b : ↥(generalizedFitting H), a * b ≠ b * a) ∧
      centralizer ((generalizedFitting H : Subgroup H) : Set H) = ⊥ ∧
      x ∉ generalizedFitting H ∧
      Open.pRank 2 (centralizer ({x} : Set H) ⊓ generalizedFitting H) = 1 := by
  obtain ⟨L, hL⟩ := h.exists_component hF
  have hxx := h.mul_self_x
  have hZL := h.component_center_bot hF hL
  have hlayer : layer H = L :=
    le_antisymm (sSup_le fun K hK => (h.component_unique hF hL hK).le) (le_sSup hL)
  have hFL : generalizedFitting H = L := by
    rw [generalizedFitting, hF, hlayer]; simp
  obtain ⟨hsimple, hnab⟩ := component_simple_data hL hZL
  have hxnL : x ∉ L := h.x_notMem_component hL
  rw [hFL]
  refine ⟨hsimple, hnab, ?_, hxnL, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hcL : c ∈ L := by
      have := centralizer_generalizedFitting_le H
      rw [hFL] at this
      exact this hc
    exact hZL c hcL (fun l hl => (Subgroup.mem_centralizer_iff.mp hc l hl).symm)
  · apply le_antisymm (h.pRank_centralizer_inf_le_one hxnL)
    have := hsimple
    have hLeven : Even (Nat.card ↥L) := CFSG.GH74.even_card_of_nonabelian_simple hnab
    obtain ⟨v, hvL, hv1, hv2, hxv⟩ := exists_fixed_involution_of_even (X := L)
      (even_iff_two_dvd.mp hLeven) hxx (h.component_normalized hF hL)
    have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
    have hle : zpowers v ≤ centralizer ({x} : Set H) ⊓ L := by
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, hvL⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      symm
      calc x * v = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [hxv]
    exact SU1.le_pRank (p := 2) (by norm_num) hle
      (SU1.isElemAbelian_zpowers (by rw [pow_two]; exact hv2))
      (k := 1) (by rw [Nat.card_zpowers, hvo]; norm_num)

end CFSG.GH74.Uniqueness.SU.K.R3
