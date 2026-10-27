module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lambda2
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Bal
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Restrict
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.Sporadic.SmallOddCore.McLAut
import CFSG.LocalAnalysis.OddStandard.Solomon75T11bLy
import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

private theorem ec_isPGroup_zpowers {G : Type} [Group G] {a : G} {k : ℕ}
    (ha : a ^ (2 ^ k) = 1) : IsPGroup 2 (zpowers a) := fun g => by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    ha, one_zpow, OneMemClass.coe_one]

private theorem ec_centralizer_zpowers {G : Type} [Group G] (a : G) :
    centralizer (zpowers a : Set G) = centralizer ({a} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

private theorem ec_mk_eq_one_iff {X : Type} [Group X] {C : Subgroup X} (x : ↥C) :
    QuotientGroup.mk' (pPrimeCore 2 ↥C) x = 1 ↔ (x : X) ∈ oddCoreOf C := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨x', hx', hxx'⟩
    rw [show x = x' from (Subtype.ext hxx').symm]
    exact hx'

private def ecComm {X : Type} [Group X] (N : Subgroup X) (g : X) : Subgroup X where
  carrier := {k | k ∈ normalizer (N : Set X) ∧ ⁅k, g⁆ ∈ N}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have h : ⁅a * b, g⁆ = a * ⁅b, g⁆ * a⁻¹ * ⁅a, g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact N.mul_mem ((mem_normalizer_iff.mp ha _).mp hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have h : ⁅a⁻¹, g⁆ = a⁻¹ * ⁅a, g⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact (mem_normalizer_iff.mp (inv_mem ha) _).mp (N.inv_mem ha')

private structure EcRigid (Q : Type) [Group Q] : Prop where
  center_eq_bot : center Q = ⊥
  card_outer_le : Nat.card (ComponentClassification.OuterAutomorphisms.Outer Q) ≤ 2
  core_eq_bot : ∀ s : Q, orderOf s = 2 → pPrimeCore 2 ↥(centralizer ({s} : Set Q)) = ⊥

private theorem ec_center_eq_bot_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact hp IsSimpleGroup.prime_card

private theorem ec_center_eq_bot_of_type
    {Q : Type} [Group Q]
    (h : Nonempty (Q ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (Q ≃* Blueprint.NativeSporadic.Ly)) : center Q = ⊥ := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.McL.isSimpleGroup_McL e
    refine ec_center_eq_bot_of_simple ?_
    rw [Nat.card_congr e.toEquiv, Sporadic.McL.card_McL]
    norm_num
  · have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.isSimpleGroup_Ly e
    refine ec_center_eq_bot_of_simple ?_
    rw [Nat.card_congr e.toEquiv, Sporadic.Ly.card_Ly']
    norm_num

private theorem ec_rigid_of_mcl
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.McL) : EcRigid Q := by
  have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.McL.isSimpleGroup_McL e
  have hZ : center Q = ⊥ := ec_center_eq_bot_of_simple (by
    rw [Nat.card_congr e.toEquiv, Sporadic.McL.card_McL]
    norm_num)
  refine ⟨hZ, ?_, fun s hs => ?_⟩
  · rw [Nat.card_congr (ComponentClassification.OuterAutomorphisms.equivalence
      (e.trans Sporadic.Schreier.mclPermEquiv)).toEquiv]
    exact Sporadic.SmallOddCore.mcl_outer_card_le
  · have hC : centralizer ((⊤ : Subgroup Q) : Set Q) = ⊥ := by
      rw [coe_top, centralizer_univ, hZ]
    have h := Sporadic.SmallOddCore.mcl_almost_simple_odd_core (⊤ : Subgroup Q)
      ⟨topEquiv.trans e⟩ hC s hs
    rwa [ComponentClassification.SymmetricLocal.oddCore_eq_pPrimeCore_two] at h

private theorem ec_rigid_of_ly
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.Ly) : EcRigid Q := by
  have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.isSimpleGroup_Ly e
  have hZ : center Q = ⊥ := ec_center_eq_bot_of_simple (by
    rw [Nat.card_congr e.toEquiv, Sporadic.Ly.card_Ly']
    norm_num)
  refine ⟨hZ, ?_, fun s hs => ?_⟩
  · have h := ComponentClassification.OuterAutomorphisms.inner_map_congr
      (G := Blueprint.NativeSporadic.Ly) (H := Q) (by exact e.symm)
    rw [show ComponentClassification.OuterAutomorphisms.inner Blueprint.NativeSporadic.Ly = ⊤ from
      ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput,
      map_top_of_surjective _ (MulEquiv.surjective _)] at h
    have h1 : (ComponentClassification.OuterAutomorphisms.inner Q).index = 1 := by
      rw [← h, index_top]
    exact h1.le.trans (by norm_num)
  · have hnonab : ∃ a b : Q, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      obtain ⟨g, hg⟩ := exists_ne (1 : Q)
      have hgZ : g ∈ center Q := mem_center_iff.mpr fun h => hc h g
      rw [hZ, mem_bot] at hgZ
      exact hg hgZ
    exact pPrimeCore_cen_eq_bot_of_Ly hnonab ⟨e⟩ hs

private theorem ec_le_centralizer_of_rigid {G : Type} [Group G] [Finite G] {F P : Subgroup G}
    (hF : EcRigid ↥F) {β c : G} (hcF : c ∈ F) (hc2 : orderOf c = 2)
    (hβc : ∀ f ∈ F, β * f * β⁻¹ = c * f * c⁻¹) (hPodd : Odd (Nat.card P))
    (hPβ : P ≤ centralizer ({β} : Set G))
    (hPn : centralizer ({β} : Set G) ≤ normalizer (P : Set G))
    (hPF : P ≤ normalizer (F : Set G)) : P ≤ centralizer (F : Set G) := by
  set φ : P →* MulAut F := F.normalizerMonoidHom.comp (inclusion hPF)
  have hφa : ∀ (p : P) (f : F), ((φ p f : F) : G) = (p : G) * f * (p : G)⁻¹ := fun _ _ => rfl
  set ψ : F →* MulAut F := MulAut.conj with hψ
  have hψa : ∀ (g f : F), ((ψ g f : F) : G) = (g : G) * f * (g : G)⁻¹ := fun _ _ => rfl
  have hψinj : Function.Injective ψ := by
    intro g h hgh
    have hz : g⁻¹ * h ∈ center F := by
      rw [mem_center_iff]
      intro f
      have h1 : g * f * g⁻¹ = h * f * h⁻¹ := by
        have := congrArg (fun σ : MulAut F => σ f) hgh
        simpa [hψ, MulAut.conj_apply] using this
      calc f * (g⁻¹ * h) = g⁻¹ * (g * f * g⁻¹) * h := by group
        _ = g⁻¹ * (h * f * h⁻¹) * h := by rw [h1]
        _ = g⁻¹ * h * f := by group
    rw [hF.center_eq_bot, mem_bot] at hz
    calc g = g * (g⁻¹ * h) := by rw [hz, mul_one]
      _ = h := by group
  have hinner : ∀ p : P, ∃ g : F, ψ g = φ p := by
    intro p
    have h1 : orderOf (QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner F)
        (φ p)) ∣ Nat.card P :=
      (orderOf_map_dvd _ _).trans ((orderOf_map_dvd φ p).trans (orderOf_dvd_natCard p))
    have h2 : orderOf (QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner F)
        (φ p)) ≤ 2 :=
      (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard _)).trans hF.card_outer_le
    have h3 : orderOf (QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner F)
        (φ p)) = 1 := by
      obtain ⟨k, hk⟩ := hPodd.of_dvd_nat h1
      have := orderOf_pos (QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner F)
        (φ p))
      omega
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact MonoidHom.mem_range.mp h3
  set Pstar : Subgroup F := φ.range.comap ψ
  have hPstar_odd : Odd (Nat.card Pstar) := by
    refine hPodd.of_dvd_nat ?_
    rw [← card_map_of_injective hψinj]
    refine (card_dvd_of_le (map_comap_le _ _)).trans ?_
    rw [MonoidHom.range_eq_map]
    exact (card_map_dvd _ _).trans (by rw [card_top])
  set c' : F := ⟨c, hcF⟩
  have hcomm : ∀ p : P, φ p * ψ c' = ψ c' * φ p := by
    intro p
    have hpβ : (p : G) * β = β * p := mem_centralizer_singleton_iff.mp (hPβ p.2)
    refine MulEquiv.ext fun f => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hφa, hψa, hψa, hφa]
    have e1 := hβc f f.2
    have e2 := hβc _ (φ p f).2
    rw [hφa] at e2
    rw [← e1, ← e2]
    calc (p : G) * (β * f * β⁻¹) * (p : G)⁻¹ = ((p : G) * β) * f * ((p : G) * β)⁻¹ := by group
      _ = (β * p) * f * (β * p)⁻¹ := by rw [hpβ]
      _ = β * ((p : G) * f * (p : G)⁻¹) * β⁻¹ := by group
  have hPstarC : Pstar ≤ centralizer ({c'} : Set F) := by
    intro g hg
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp (mem_comap.mp hg)
    rw [mem_centralizer_singleton_iff]
    apply hψinj
    rw [map_mul, map_mul, ← hp, hcomm p]
  have hPstarN1 : ∀ m ∈ centralizer ({c'} : Set F), ∀ g ∈ Pstar, m * g * m⁻¹ ∈ Pstar := by
    intro m hm g hg
    have hmβ : (m : G) ∈ centralizer ({β} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h2 : (m : G) * c = c * m := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hm)
      have h3 : β * m * β⁻¹ = m := by rw [hβc m m.2, ← h2, mul_inv_cancel_right]
      calc (m : G) * β = β * m * β⁻¹ * β := by rw [h3]
        _ = β * m := by group
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp (mem_comap.mp hg)
    have hmp : (m : G) * p * (m : G)⁻¹ ∈ P := (mem_normalizer_iff.mp (hPn hmβ) p).mp p.2
    refine mem_comap.mpr (MonoidHom.mem_range.mpr ⟨⟨_, hmp⟩, ?_⟩)
    rw [map_mul, map_mul, ← hp]
    refine MulEquiv.ext fun f => Subtype.ext ?_
    simp only [MulAut.mul_apply, hφa, hψa, coe_inv]
    group
  have hPstarN : centralizer ({c'} : Set F) ≤ normalizer (Pstar : Set F) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hPstarN1 m hm g, fun h => ?_⟩
    have := hPstarN1 m⁻¹ (inv_mem hm) _ h
    rwa [inv_inv, show m⁻¹ * (m * g * m⁻¹) * m = g by group] at this
  have hc'2 : orderOf c' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hc2
  have hPstar1 : Pstar = ⊥ := by
    have h := le_oddCoreOf_of_normalized hPstarC hPstarN hPstar_odd
    rw [oddCoreOf, hF.core_eq_bot c' hc'2, Subgroup.map_bot] at h
    exact le_bot_iff.mp h
  intro p hp
  obtain ⟨g, hg⟩ := hinner ⟨p, hp⟩
  have hg1 : g ∈ Pstar := mem_comap.mpr (MonoidHom.mem_range.mpr ⟨⟨p, hp⟩, hg.symm⟩)
  rw [hPstar1, mem_bot] at hg1
  rw [hg1, map_one] at hg
  rw [mem_centralizer_iff]
  intro f hf
  have h := congrArg (fun σ : MulAut F => ((σ ⟨f, hf⟩ : F) : G)) hg
  simp only [MulAut.one_apply, hφa] at h
  calc f * p = p * f * p⁻¹ * p := by rw [← h]
    _ = p * f := by group

private theorem ec_dec {G : Type} [Group G] [Finite G] {𝓕 : Set (Subgroup G)}
    (h𝓕 : ∀ F ∈ 𝓕, IsComponent F) {β : G} (hβ : β ∈ sSup 𝓕) {F : Subgroup G}
    (hF : IsComponent F) :
    β ∈ centralizer (F : Set G) ∨ (F ∈ 𝓕 ∧ ∃ c ∈ F, ∃ w ∈ centralizer (F : Set G), β = c * w) := by
  have hother : ∀ K ∈ 𝓕, K ≠ F → K ≤ centralizer (F : Set G) := fun K hK hKF =>
    commutator_eq_bot_iff_le_centralizer.mp
      ((LocalCores.distinct_components_commute (h𝓕 K hK) hF).resolve_left hKF)
  by_cases hF𝓕 : F ∈ 𝓕
  · right
    have hEF : sSup {K | K ∈ 𝓕 ∧ K ≠ F} ≤ centralizer (F : Set G) :=
      sSup_le fun K hK => hother K hK.1 hK.2
    have hle : sSup 𝓕 ≤ F ⊔ sSup {K | K ∈ 𝓕 ∧ K ≠ F} := sSup_le fun K hK => by
      by_cases h : K = F
      · exact h ▸ le_sup_left
      · exact le_sup_of_le_right (le_sSup ⟨hK, h⟩)
    have hβFE : β ∈ ((F ⊔ sSup {K | K ∈ 𝓕 ∧ K ≠ F} : Subgroup G) : Set G) := hle hβ
    rw [coe_mul_of_left_le_normalizer_right _ _
      ((le_centralizer_iff.mp hEF).trans (centralizer_le_normalizer _))] at hβFE
    obtain ⟨c, hc, w, hw, rfl⟩ := hβFE
    exact ⟨hF𝓕, c, hc, w, hEF hw, rfl⟩
  · left
    exact (sSup_le fun K hK => hother K hK fun h => hF𝓕 (h ▸ hK)) hβ

private theorem ec_le_centralizer_component {G : Type} [Group G] [Finite G]
    (hO : pPrimeCore 2 G = ⊥) {β : G} (hβ2 : β ^ 2 = 1) {P : Subgroup G}
    (hPodd : Odd (Nat.card P)) (hPβ : P ≤ centralizer ({β} : Set G))
    (hPn : centralizer ({β} : Set G) ≤ normalizer (P : Set G)) {F : Subgroup G}
    (hF : IsComponent F) (hβF : β ∉ centralizer (F : Set G)) {c w : G} (hcF : c ∈ F)
    (hw : w ∈ centralizer (F : Set G)) (hβcw : β = c * w)
    (hbr : EcRigid ↥F ∨ (P ≤ normalizer (F : Set G) → P ≤ centralizer (F : Set G))) :
    P ≤ centralizer (F : Set G) := by
  have hcw : c * w = w * c := ((mem_centralizer_iff.mp hw) c hcF)
  have hcβ : c ∈ centralizer ({β} : Set G) := by
    rw [mem_centralizer_singleton_iff, hβcw]
    calc c * (c * w) = c * (w * c) := by rw [hcw]
      _ = c * w * c := by group
  have hcZ : c ∉ centralizer (F : Set G) := fun h => hβF (hβcw ▸ mul_mem h hw)
  have hc1 : c ≠ 1 := fun h => hcZ (h ▸ one_mem _)
  have hc2F : c ^ 2 ∈ centralizer (F : Set G) := by
    have h1 : c ^ 2 * w ^ 2 = 1 := by
      rw [← (show Commute c w from hcw).mul_pow, ← hβcw]
      exact hβ2
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem hw 2)
  have hc2Z : (⟨c ^ 2, pow_mem hcF 2⟩ : ↥F) ∈ center ↥F := by
    rw [mem_center_iff]
    intro f
    exact Subtype.ext ((mem_centralizer_iff.mp hc2F) f f.2)
  have hZ2 : IsPGroup 2 ↥(center ↥F) := isPGroup_two_center_of_subnormal hO hF.2
  obtain ⟨k, hk⟩ := hZ2 ⟨_, hc2Z⟩
  have hck : c ^ (2 ^ (k + 1)) = 1 := by
    have := congrArg (fun z : ↥(center ↥F) => ((z : ↥F) : G)) hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [pow_succ', pow_mul]
    exact this
  have hPF : P ≤ normalizer (F : Set G) :=
    le_normalizer_component_of_odd hPodd hPβ hPn hF hcF hcβ hck hcZ
  rcases hbr with hR | hT
  · have hc2 : c ^ 2 = 1 := by
      rw [hR.center_eq_bot, mem_bot] at hc2Z
      exact congrArg Subtype.val hc2Z
    have hco : orderOf c = 2 := orderOf_eq_prime hc2 hc1
    have hβc : ∀ f ∈ F, β * f * β⁻¹ = c * f * c⁻¹ := by
      intro f hf
      have hwf : f * w = w * f := (mem_centralizer_iff.mp hw) f hf
      rw [hβcw]
      calc c * w * f * (c * w)⁻¹ = c * (w * f) * w⁻¹ * c⁻¹ := by group
        _ = c * (f * w) * w⁻¹ * c⁻¹ := by rw [hwf]
        _ = c * f * c⁻¹ := by group
    exact ec_le_centralizer_of_rigid hR hcF hco hβc hPodd hPβ hPn hPF
  · exact hT hPF

private theorem ec_eq_bot {G : Type} [Group G] [Finite G] (hO : pPrimeCore 2 G = ⊥) {β : G}
    (hβ2 : β ^ 2 = 1) {P : Subgroup G} (hPodd : Odd (Nat.card P))
    (hPβ : P ≤ centralizer ({β} : Set G))
    (hPn : centralizer ({β} : Set G) ≤ normalizer (P : Set G))
    (hloc : ∀ F : Subgroup G, IsComponent F → β ∉ centralizer (F : Set G) →
      ∃ c ∈ F, ∃ w ∈ centralizer (F : Set G), β = c * w ∧
        (EcRigid ↥F ∨ (P ≤ normalizer (F : Set G) → P ≤ centralizer (F : Set G)))) :
    P = ⊥ := by
  refine eq_bot_of_odd_of_le_centralizer_layer hO (k := 1) (by rwa [pow_one]) hPodd hPβ hPn ?_
  rw [le_centralizer_iff, layer.eq_sSup]
  refine sSup_le fun F (hF : IsComponent F) => le_centralizer_iff.mp ?_
  by_cases hβF : β ∈ centralizer (F : Set G)
  ·
    have hFβ : F ≤ centralizer ({β} : Set G) := fun f hf =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hβF f hf)
    have hFc : IsComponent (F.subgroupOf (centralizer ({β} : Set G))) :=
      LocalCores.component_overgroup hF hFβ
    have hPnH : (P.subgroupOf (centralizer ({β} : Set G))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hPβ).mpr hPn
    have hsolv : Group.IsSolvable ↥(P.subgroupOf (centralizer ({β} : Set G))) := by
      refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe hPβ).toEquiv]
      exact hPodd
    have hcomm := (LocalCores.component_solvable_centralizer hsolv hPnH.isSubnormal).1 _ hFc
    intro p hp
    rw [mem_centralizer_iff]
    intro f hf
    have h1 := commutator_eq_bot_iff_le_centralizer.mp hcomm
      (show (⟨f, hFβ hf⟩ : centralizer ({β} : Set G)) ∈ F.subgroupOf _ from hf)
    have h2 := mem_centralizer_iff.mp h1 ⟨p, hPβ hp⟩ hp
    exact (congrArg Subtype.val h2).symm
  · obtain ⟨c, hcF, w, hw, hβcw, hbr⟩ := hloc F hF hβF
    exact ec_le_centralizer_component hO hβ2 hPodd hPβ hPn hF hβF hcF hw hβcw hbr

private theorem ec_tTrick {X : Type} [Group X] [Finite X] {H D P V : Subgroup X} {t : X}
    (htH : t ∈ H) (ht2 : t * t = 1) (hVH : V ≤ H) (hDt : ∀ d ∈ D, d * t = t * d)
    (hPt : t ∈ normalizer (P : Set X)) (hPodd : Odd (Nat.card P)) (hVodd : Odd (Nat.card V))
    (hDV : D ≤ normalizer (V : Set X)) (hPV : ∀ c ∈ P, c * t = t * c → c ∈ V)
    (hF : IsComponent ((D.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))))
    (hPF : (P.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ≤
      normalizer (((D.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :
        Subgroup (↥H ⧸ pPrimeCore 2 ↥H)) : Set (↥H ⧸ pPrimeCore 2 ↥H))) :
    (P.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ≤
      centralizer (((D.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :
        Subgroup (↥H ⧸ pPrimeCore 2 ↥H)) : Set (↥H ⧸ pPrimeCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  set F := (D.subgroupOf H).map π with hFdef
  set Vb := (V.subgroupOf H).map π with hVb
  obtain ⟨t', ht'⟩ : ∃ t' : ↥H, (t' : X) = t := ⟨⟨t, htH⟩, rfl⟩
  have htF : ∀ f ∈ F, π t' * f = f * π t' := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [coe_mul, coe_mul, ht']
    exact (hDt _ hd).symm
  have hFV : F ≤ normalizer (Vb : Set _) := by
    rintro _ ⟨d, hd, rfl⟩
    have hdV : (d : X) ∈ normalizer (V : Set X) := hDV hd
    have hdN : d ∈ normalizer ((V.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [mem_normalizer_iff]
      intro h
      rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp hdV h
    exact le_normalizer_map π (mem_map_of_mem π hdN)
  have hVbodd : Odd (Nat.card Vb) := by
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ π)
    rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv]
    exact hVodd
  have hFVb : ∀ z ∈ F, z ∈ Vb → z = 1 := by
    have hO : pPrimeCore 2 (↥H ⧸ pPrimeCore 2 ↥H) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
    have hRn : F ≤ normalizer ((F ⊓ Vb : Subgroup _) : Set _) := fun f hf =>
      mem_normalizer_inf (le_normalizer hf) (hFV hf)
    have hsub : (F ⊓ Vb).IsSubnormal :=
      Subgroup.IsSubnormal.step _ F inf_le_left hF.2
        ((normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hRn)
    have hodd : Odd (Nat.card ↥(F ⊓ Vb)) := hVbodd.of_dvd_nat (card_dvd_of_le inf_le_right)
    have h1 := ComponentClassification.UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsub
    have htop : (⊤ : Subgroup ↥(F ⊓ Vb)) ≤ pPrimeCore 2 ↥(F ⊓ Vb) := by
      refine le_sSup ⟨inferInstance, ?_⟩
      simpa using Nat.coprime_two_left.mpr hodd
    intro z hzF hzV
    have hz : z ∈ (pPrimeCore 2 ↥(F ⊓ Vb)).map (F ⊓ Vb).subtype :=
      ⟨⟨z, hzF, hzV⟩, htop (mem_top _), rfl⟩
    rw [h1, hO] at hz
    exact mem_bot.mp hz.2
  have hVC : ∀ v ∈ Vb, v ∈ normalizer (F : Set _) → v ∈ centralizer (F : Set _) := by
    intro v hv hvN
    rw [mem_centralizer_iff]
    intro f hf
    have h1 : v * f * v⁻¹ ∈ F := (mem_normalizer_iff.mp hvN f).mp hf
    have h2 : f * v⁻¹ * f⁻¹ ∈ Vb := (mem_normalizer_iff.mp (hFV hf) v⁻¹).mp (inv_mem hv)
    have hz : v * f * v⁻¹ * f⁻¹ = 1 := by
      refine hFVb _ (mul_mem h1 (inv_mem hf)) ?_
      rw [show v * f * v⁻¹ * f⁻¹ = v * (f * v⁻¹ * f⁻¹) by group]
      exact mul_mem hv h2
    calc f * v = (v * f * v⁻¹ * f⁻¹)⁻¹ * (v * f) := by group
      _ = v * f := by rw [hz, inv_one, one_mul]
  rintro _ ⟨p, hp, rfl⟩
  have hpP : (p : X) ∈ P := hp
  have hpN : π p ∈ normalizer (F : Set _) := hPF (mem_map_of_mem π hp)
  have htt : t' * t' = 1 := Subtype.ext (by rw [coe_mul, ht', coe_one]; exact ht2)
  have htP : ∀ x : ↥H, (x : X) ∈ P → ((t' * x * t'⁻¹ : ↥H) : X) ∈ P := fun x hx => by
    rw [coe_mul, coe_mul, coe_inv, ht']
    exact (mem_normalizer_iff.mp hPt x).mp hx
  obtain ⟨k, hk⟩ : ∃ k : ↥H, k = p⁻¹ * (t' * p * t'⁻¹) := ⟨_, rfl⟩
  have hkP : (k : X) ∈ P := by
    rw [hk, coe_mul, coe_inv]
    exact mul_mem (inv_mem hpP) (htP p hpP)
  have hkF : π k ∈ centralizer (F : Set _) := by
    rw [mem_centralizer_iff]
    intro f hf
    have h1 : π t' * f = f * π t' := htF f hf
    have hf2 : π p * f * (π p)⁻¹ ∈ F := (mem_normalizer_iff.mp hpN f).mp hf
    have h2 : π t' * (π p * f * (π p)⁻¹) = π p * f * (π p)⁻¹ * π t' := htF _ hf2
    have h1' : f * (π t')⁻¹ = (π t')⁻¹ * f := by
      calc f * (π t')⁻¹ = (π t')⁻¹ * (π t' * f) * (π t')⁻¹ := by group
        _ = (π t')⁻¹ * (f * π t') * (π t')⁻¹ := by rw [h1]
        _ = (π t')⁻¹ * f := by group
    rw [hk, map_mul, map_inv, map_mul, map_mul, map_inv]
    calc f * ((π p)⁻¹ * (π t' * π p * (π t')⁻¹))
        = (π p)⁻¹ * (π p * f * (π p)⁻¹ * π t') * π p * (π t')⁻¹ := by group
      _ = (π p)⁻¹ * (π t' * (π p * f * (π p)⁻¹)) * π p * (π t')⁻¹ := by rw [h2]
      _ = (π p)⁻¹ * π t' * π p * (f * (π t')⁻¹) := by group
      _ = (π p)⁻¹ * π t' * π p * ((π t')⁻¹ * f) := by rw [h1']
      _ = (π p)⁻¹ * (π t' * π p * (π t')⁻¹) * f := by group
  have hkodd : Odd (orderOf k) := by
    rw [← Subgroup.orderOf_coe]
    exact hPodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hkP)
  obtain ⟨s, hs⟩ := hkodd
  obtain ⟨r, hr⟩ : ∃ r : ↥H, r = k ^ (s + 1) := ⟨_, rfl⟩
  have hrr : r * r = k := by
    rw [hr, ← pow_add, show s + 1 + (s + 1) = orderOf k + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hσ : t' * (t' * p * t'⁻¹) * t'⁻¹ = p := by
    calc t' * (t' * p * t'⁻¹) * t'⁻¹ = (t' * t') * p * (t' * t')⁻¹ := by group
      _ = p := by rw [htt, one_mul, inv_one, mul_one]
  have htk : t' * k * t'⁻¹ = k⁻¹ := by
    rw [hk]
    calc t' * (p⁻¹ * (t' * p * t'⁻¹)) * t'⁻¹
        = (t' * p * t'⁻¹)⁻¹ * (t' * (t' * p * t'⁻¹) * t'⁻¹) := by group
      _ = (t' * p * t'⁻¹)⁻¹ * p := by rw [hσ]
      _ = (p⁻¹ * (t' * p * t'⁻¹))⁻¹ := by group
  have htr : t' * r * t'⁻¹ = r⁻¹ := by
    rw [hr, ← conj_pow, htk, inv_pow]
  have hpk : t' * p * t'⁻¹ = p * k := by
    rw [hk]
    group
  obtain ⟨c, hc⟩ : ∃ c : ↥H, c = p * r := ⟨_, rfl⟩
  have htc : c * t' = t' * c := by
    have h1 : t' * c * t'⁻¹ = c := by
      rw [hc]
      calc t' * (p * r) * t'⁻¹ = (t' * p * t'⁻¹) * (t' * r * t'⁻¹) := by group
        _ = p * (r * r) * r⁻¹ := by rw [hpk, htr, hrr]
        _ = p * r := by group
    calc c * t' = (t' * c * t'⁻¹) * t' := by rw [h1]
      _ = t' * c := by group
  have hcP : (c : X) ∈ P := by
    rw [hc, coe_mul, hr, coe_pow]
    exact mul_mem hpP (pow_mem hkP _)
  have hcV : (c : X) ∈ V := by
    refine hPV _ hcP ?_
    have h1 := congrArg Subtype.val htc
    rw [coe_mul, coe_mul, ht'] at h1
    exact h1
  have hcC : π c ∈ centralizer (F : Set _) :=
    hVC _ (mem_map_of_mem π (show c ∈ V.subgroupOf H from hcV))
      (hPF (mem_map_of_mem π (show c ∈ P.subgroupOf H from hcP)))
  have hrC : π r ∈ centralizer (F : Set _) := by
    rw [hr, map_pow]
    exact pow_mem hkF _
  have hpc : p = c * r⁻¹ := by
    rw [hc]
    group
  rw [hpc, map_mul, map_inv]
  exact mul_mem hcC (inv_mem hrC)

private theorem ec_decomp {G : Type} [Group G] (W : Subgroup G) (s : Set (Subgroup G))
    (hs : s.Finite) :
    (∀ M ∈ s, ∀ z ∈ M, (∀ y ∈ M, z * y = y * z) → z = 1) →
    (∀ M ∈ s, ∀ M' ∈ s, M ≠ M' → M' ≤ centralizer (M : Set G)) →
    ∀ β ∈ sSup s, (∀ M ∈ s, ∀ z ∈ M, z * β = β * z → (∃ k : ℕ, z ^ (2 ^ k) = 1) → z ∈ W) →
    ∀ x ∈ sSup s, x * β = β * x → ∀ j : ℕ, x ^ (2 ^ j) = 1 → x ∈ W := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    intro _ _ β _ _ x hx _ _ _
    rw [sSup_empty, mem_bot] at hx
    rw [hx]
    exact W.one_mem
  | @insert M s hMs hs ih =>
    intro hZ hc β hβ hW x hx hxβ j hxj
    have hMmem : M ∈ insert M s := Set.mem_insert M s
    have hEC : sSup s ≤ centralizer (M : Set G) := sSup_le fun M' hM' =>
      hc M hMmem M' (Set.mem_insert_of_mem M hM') (fun h => hMs (h ▸ hM'))
    have hME : M ≤ normalizer ((sSup s : Subgroup G) : Set G) :=
      (le_centralizer_iff.mp hEC).trans (centralizer_le_normalizer _)
    have hdec : ∀ y ∈ sSup (insert M s), ∃ m ∈ M, ∃ e ∈ sSup s, m * e = y := by
      intro y hy
      rw [sSup_insert] at hy
      have hy' : y ∈ ((M ⊔ sSup s : Subgroup G) : Set G) := hy
      rw [coe_mul_of_left_le_normalizer_right _ _ hME] at hy'
      exact hy'
    have hme : ∀ m ∈ M, ∀ e ∈ sSup s, m * e = e * m := fun m hm e he =>
      mem_centralizer_iff.mp (hEC he) m hm
    have hME1 : ∀ z ∈ M, z ∈ sSup s → z = 1 := fun z hzM hzE =>
      hZ M hMmem z hzM fun y hy => (mem_centralizer_iff.mp (hEC hzE) y hy).symm
    obtain ⟨m', hm', e', he', rfl⟩ := hdec β hβ
    obtain ⟨m, hm, e, he, rfl⟩ := hdec x hx
    have h1 : m * m' * (e * e') = m' * m * (e' * e) := by
      have e1 : m * e * (m' * e') = m * m' * (e * e') := by
        calc m * e * (m' * e') = m * (e * m') * e' := by group
          _ = m * (m' * e) * e' := by rw [← hme m' hm' e he]
          _ = m * m' * (e * e') := by group
      have e2 : m' * e' * (m * e) = m' * m * (e' * e) := by
        calc m' * e' * (m * e) = m' * (e' * m) * e := by group
          _ = m' * (m * e') * e := by rw [← hme m hm e' he']
          _ = m' * m * (e' * e) := by group
      rw [← e1, ← e2]
      exact hxβ
    have hw : (m' * m)⁻¹ * (m * m') = 1 := by
      apply hME1
      · exact mul_mem (inv_mem (mul_mem hm' hm)) (mul_mem hm hm')
      · have h2 : (m' * m)⁻¹ * (m * m') = (e' * e) * (e * e')⁻¹ := by
          calc (m' * m)⁻¹ * (m * m') = (m' * m)⁻¹ * (m * m' * (e * e')) * (e * e')⁻¹ := by
                group
            _ = (m' * m)⁻¹ * (m' * m * (e' * e)) * (e * e')⁻¹ := by rw [h1]
            _ = (e' * e) * (e * e')⁻¹ := by group
        rw [h2]
        exact mul_mem (mul_mem he' he) (inv_mem (mul_mem he he'))
    have hmm' : m * m' = m' * m := (inv_mul_eq_one.mp hw).symm
    have hee' : e * e' = e' * e := by
      have h2 : m * m' * (e * e') = m * m' * (e' * e) := by rw [h1, hmm']
      exact mul_left_cancel h2
    have h3 : m ^ (2 ^ j) * e ^ (2 ^ j) = 1 := by
      rw [← (show Commute m e from hme m hm e he).mul_pow]
      exact hxj
    have hmj : m ^ (2 ^ j) = 1 := by
      apply hME1 _ (pow_mem hm _)
      rw [eq_inv_of_mul_eq_one_left h3]
      exact inv_mem (pow_mem he _)
    have hej : e ^ (2 ^ j) = 1 := by
      rw [hmj, one_mul] at h3
      exact h3
    have hmW : m ∈ W := by
      refine hW M hMmem m hm ?_ ⟨j, hmj⟩
      calc m * (m' * e') = m * m' * e' := by group
        _ = m' * m * e' := by rw [hmm']
        _ = m' * (m * e') := by group
        _ = m' * (e' * m) := by rw [hme m hm e' he']
        _ = m' * e' * m := by group
    have heW : e ∈ W := by
      refine ih (fun M'' hM'' => hZ M'' (Set.mem_insert_of_mem M hM''))
        (fun M₁ h₁ M₂ h₂ hne =>
          hc M₁ (Set.mem_insert_of_mem M h₁) M₂ (Set.mem_insert_of_mem M h₂) hne)
        e' he' ?_ e he hee' j hej
      intro M'' hM'' z hz hze' hz2
      refine hW M'' (Set.mem_insert_of_mem M hM'') z hz ?_ hz2
      have hzm' : z * m' = m' * z :=
        (mem_centralizer_iff.mp (hEC (le_sSup hM'' hz)) m' hm').symm
      calc z * (m' * e') = z * m' * e' := by group
        _ = m' * z * e' := by rw [hzm']
        _ = m' * (z * e') := by group
        _ = m' * (e' * z) := by rw [hze']
        _ = m' * e' * z := by group
    exact mul_mem hmW heW

private theorem ec_kcomp_pc {X : Type} [Group X] {n : ℕ} {H L : Subgroup X}
    (h : Sec6KComp X n H L) : IsPCompIn 2 H L := by
  rcases h with ⟨⟨u, hu⟩, -⟩ | hM
  · exact hu.2.2.1
  · exact hM.1.1

private theorem ec_core_le_of_pc {X : Type} [Group X] [Finite X] {H J : Subgroup X}
    (hJ : IsPCompIn 2 H J) : pPrimeCoreOf 2 J ≤ oddCoreOf H := by
  obtain ⟨-, -, hsub, -⟩ := hJ.2
  exact pPrimeCoreOf_le_oddCoreOf hJ.1 hsub

private theorem ec_mem_normalizer_of_subgroupOf {X : Type} [Group X] {H J : Subgroup X}
    (hJH : J ≤ H) {c : ↥H}
    (hc : c ∈ normalizer ((J.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    (c : X) ∈ normalizer (J : Set X) := by
  rw [mem_normalizer_iff] at hc ⊢
  intro x
  constructor
  · intro hx
    exact (hc ⟨x, hJH hx⟩).1 hx
  · intro hx
    have hxH : x ∈ H := by
      have h1 : (c : X) * x * (c : X)⁻¹ ∈ H := hJH hx
      have h2 : x = (c : X)⁻¹ * ((c : X) * x * (c : X)⁻¹) * (c : X) := by group
      rw [h2]
      exact H.mul_mem (H.mul_mem (H.inv_mem c.2) h1) c.2
    exact (hc ⟨x, hxH⟩).2 hx

private theorem ec_distinct {X : Type} [Group X] [Finite X] {H L L' : Subgroup X}
    (hL : IsPCompIn 2 H L) (hL' : IsPCompIn 2 H L') (hne : L ≠ L') :
    L' ≤ centralizerSection L (pPrimeCoreOf 2 L) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : L.subgroupOf H ≠ L'.subgroupOf H := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hL.1, inf_of_le_left hL'.1] at h
    exact h
  obtain ⟨hn1, -, hcore, -⟩ :=
    (ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
      Nat.prime_two _ _ hL.2 hL'.2).2 hne'
  intro y hy
  have hyH : y ∈ H := hL'.1 hy
  have hyN : y ∈ normalizer (L : Set X) :=
    ec_mem_normalizer_of_subgroupOf hL.1 (c := ⟨y, hyH⟩)
      (hn1 (show (⟨y, hyH⟩ : ↥H) ∈ L'.subgroupOf H from hy))
  refine ⟨hyN, mem_normalizer_oddCoreOf_of_mem_normalizer hyN, fun k hk => ?_⟩
  have hc : ⁅(⟨k, hL.1 hk⟩ : ↥H), (⟨y, hyH⟩ : ↥H)⁆ ∈
      (pPrimeCore 2 ↥(L.subgroupOf H)).map (L.subgroupOf H).subtype :=
    (hcore.trans inf_le_left) (Subgroup.commutator_mem_commutator
      (show (⟨k, hL.1 hk⟩ : ↥H) ∈ L.subgroupOf H from hk)
      (show (⟨y, hyH⟩ : ↥H) ∈ L'.subgroupOf H from hy))
  obtain ⟨w, hw, hweq⟩ := hc
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  have hew : e w ∈ pPrimeCore 2 ↥L := by
    rw [← pPrimeCore_map_iso 2 e]
    exact ⟨w, hw, rfl⟩
  refine ⟨e w, hew, ?_⟩
  change ((w : ↥H) : X) = ⁅k, y⁆
  exact congrArg Subtype.val hweq

private theorem ec_K_le_normalizer {X : Type} [Group X] [Finite X] {n : ℕ} {H L : Subgroup X}
    (hL : Sec6KComp X n H L) : Sec6K X n H ≤ normalizer (L : Set X) :=
  sSup_le fun L' (hL' : Sec6KComp X n H L') => by
    by_cases h : L' = L
    · rw [h]
      exact le_normalizer
    · exact fun c hc => (ec_distinct (ec_kcomp_pc hL) (ec_kcomp_pc hL') (Ne.symm h) hc).1

private theorem ec_not_A_M
    {X : Type} [Group X] {n : ℕ} {H H' A : Subgroup X} (hA : Sec5Comp X n H A)
    (hM : Sec6MComp X n H' A) : False := by
  have h2 := hA.2.2.1
  rw [ec_center_eq_bot_of_type hM.1.2.1, Subgroup.card_bot] at h2
  exact absurd h2 (by norm_num)

private theorem ec_K0_le {X : Type} [Group X] {n : ℕ} {t : X} : K0 X n (cen t) ≤ cen t :=
  sSup_le fun _ hA => by
    obtain ⟨⟨u, hu⟩, -⟩ := hA
    exact hu.2.2.1.1

private theorem ec_M_le {X : Type} [Group X] {n : ℕ} {t : X} : Sec6M X n (cen t) ≤ cen t :=
  sSup_le fun _ hM => hM.1.1.1

private theorem ec_K_le {X : Type} [Group X] {n : ℕ} {t : X} : Sec6K X n (cen t) ≤ cen t :=
  sSup_le fun _ hL => (ec_kcomp_pc hL).1

private theorem ec_base_le_cen {X : Type} [Group X] {n : ℕ} {t : X} :
    Sec6Base X n t ≤ cen t :=
  sup_le ec_M_le (inf_le_left.trans ec_K0_le)

private theorem ec_base_le_K {X : Type} [Group X] {n : ℕ} {t : X} :
    Sec6Base X n t ≤ Sec6K X n (cen t) := by
  rw [sec6K_eq]
  exact sup_le le_sup_right (inf_le_left.trans le_sup_left)

private theorem ec_core_K0_le {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} :
    pPrimeCoreOf 2 (K0 X n (cen t)) ≤ oddCoreOf (cen t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.GH74.GLS.pPrimeCoreOf_le_of_normal 2 ec_K0_le
    ((normal_subgroupOf_iff_le_normalizer ec_K0_le).mpr (K0_cen_normal n t))

private theorem ec_core_le_coreK {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    {L : Subgroup X} (hL : Sec6KComp X n (cen t) L) :
    pPrimeCoreOf 2 L ≤ oddCoreOf (Sec6K X n (cen t)) := by
  have hLK : L ≤ Sec6K X n (cen t) := le_sSup (s := {L | Sec6KComp X n (cen t) L}) hL
  have h1 : pPrimeCoreOf 2 L ≤ oddCoreOf (cen t) ⊓ Sec6K X n (cen t) :=
    le_inf (ec_core_le_of_pc (ec_kcomp_pc hL)) ((oddCoreOf_le L).trans hLK)
  refine h1.trans (le_oddCoreOf_of_normalized inf_le_right ?_ ?_)
  · intro k hk
    exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen t) (ec_K_le hk)) (le_normalizer hk)
  · exact (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)

private theorem ec_coreA_le_coreK {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} :
    pPrimeCoreOf 2 (K0 X n (cen t)) ≤ oddCoreOf (Sec6K X n (cen t)) := by
  have hAK : K0 X n (cen t) ≤ Sec6K X n (cen t) := by
    rw [sec6K_eq]
    exact le_sup_left
  refine le_oddCoreOf_of_normalized ((oddCoreOf_le _).trans hAK) ?_ (odd_card_oddCoreOf _)
  intro k hk
  exact mem_normalizer_oddCoreOf_of_mem_normalizer (K0_cen_normal n t (ec_K_le hk))

private theorem ec_zStar_le_Q
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} :
    zStar (K0 X n (cen t)) ≤ Sec6Q X n (cen t) := by
  intro z hz
  have hzA : z ∈ K0 X n (cen t) := hz.1
  have hzt : z ∈ cen t := ec_K0_le hzA
  refine mem_inf.2 ⟨hzt, mem_QOf_iff.2 ⟨Sec6K_cen_normal n t hzt, ?_⟩⟩
  have hle : Sec6K X n (cen t) ≤ ecComm (oddCoreOf (Sec6K X n (cen t))) z :=
    sSup_le fun L (hL : Sec6KComp X n (cen t) L) l hl => by
      have hlK : l ∈ Sec6K X n (cen t) := le_sSup (s := {L | Sec6KComp X n (cen t) L}) hL hl
      refine ⟨le_normalizer_oddCoreOf _ hlK, ?_⟩
      rcases hL with hA | hM
      ·
        have hlA : l ∈ K0 X n (cen t) := (le_sSup hA : L ≤ K0 X n (cen t)) hl
        exact ec_coreA_le_coreK (hz.2.2.2 l hlA)
      ·
        have hAL : K0 X n (cen t) ≤ centralizerSection L (pPrimeCoreOf 2 L) :=
          sSup_le fun A (hA : Sec5Comp X n (cen t) A) =>
            ec_distinct hM.1.1 (ec_kcomp_pc (Or.inl hA)) fun h =>
              ec_not_A_M (H' := cen t) hA (by rw [← h]; exact hM)
        exact ec_core_le_coreK (Or.inr hM) ((hAL hzA).2.2 l hl)
  exact fun k hk => (hle hk).2

private theorem ec_base_le_MQ
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} :
    Sec6Base X n t ≤ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) :=
  sup_le le_sup_left (le_sup_of_le_right ec_zStar_le_Q)

private theorem ec_base_le_cS
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} {A : Subgroup X}
    (hA : Sec5Comp X n (cen t) A) :
    Sec6Base X n t ≤ centralizerSection A (pPrimeCoreOf 2 A) := by
  have hApc : IsPCompIn 2 (cen t) A := ec_kcomp_pc (Or.inl hA)
  have hAK0 : A ≤ K0 X n (cen t) := le_sSup hA
  refine sup_le ?_ ?_
  · exact sSup_le fun M (hM : Sec6MComp X n (cen t) M) => ec_distinct hApc hM.1.1 fun h =>
      ec_not_A_M (H' := cen t) hA (by rw [h]; exact hM)
  · intro z hz
    have hzA : z ∈ K0 X n (cen t) := hz.1
    have hK0N : K0 X n (cen t) ≤ normalizer (A : Set X) :=
      sSup_le fun A' (hA' : Sec5Comp X n (cen t) A') => by
        by_cases h : A' = A
        · rw [h]
          exact le_normalizer
        · exact fun c hc => (ec_distinct hApc (ec_kcomp_pc (Or.inl hA')) (Ne.symm h) hc).1
    have hzN : z ∈ normalizer (A : Set X) := hK0N hzA
    refine ⟨hzN, mem_normalizer_oddCoreOf_of_mem_normalizer hzN, fun k hk => ?_⟩
    have h1 : ⁅k, z⁆ ∈ A := by
      rw [commutatorElement_def, show k * z * k⁻¹ * z⁻¹ = k * (z * k⁻¹ * z⁻¹) by group]
      exact mul_mem hk ((mem_normalizer_iff.mp hzN _).mp (inv_mem hk))
    have h2 : ⁅k, z⁆ ∈ pPrimeCoreOf 2 (K0 X n (cen t)) := hz.2.2.2 k (hAK0 hk)
    have hle : A ⊓ pPrimeCoreOf 2 (K0 X n (cen t)) ≤ oddCoreOf A :=
      le_oddCoreOf_of_normalized inf_le_left
        (fun a ha => mem_normalizer_inf (le_normalizer ha)
          (le_normalizer_oddCoreOf _ (hAK0 ha)))
        ((odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_right))
    exact hle ⟨h1, h2⟩

private theorem ec_zStar_central {X : Type} [Group X] [Finite X] {n : ℕ} {t z : X}
    (hz : z ∈ zStar (K0 X n (cen t))) (hzC : z ∈ cen t) :
    ∀ F : Subgroup (↥(cen t) ⧸ pPrimeCore 2 ↥(cen t)), IsComponent F →
      QuotientGroup.mk' (pPrimeCore 2 ↥(cen t)) ⟨z, hzC⟩ ∈ centralizer (F : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := cen t with hCdef
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  intro F hF
  by_cases hFA : ∃ A, Sec5Comp X n C A ∧ (A.subgroupOf C).map π = F
  · obtain ⟨A, hA, rfl⟩ := hFA
    have hAK : A ≤ K0 X n C := le_sSup hA
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hcomm : ⁅(a : X), z⁆ ∈ oddCoreOf C :=
      ec_core_K0_le (hz.2.2.2 _ (hAK (show (a : X) ∈ A from ha)))
    have h1 : π ⁅a, ⟨z, hzC⟩⁆ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨y, hy, hyc⟩ := hcomm
      have : y = ⁅a, ⟨z, hzC⟩⁆ := Subtype.ext (by simpa [commutatorElement_def] using hyc)
      rw [← this]
      exact hy
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · have hle : K0 X n C ≤ ((centralizer (F : Set _)).comap π).map C.subtype :=
      sSup_le fun A hA y hy => by
        obtain ⟨u, hu⟩ := hA.1
        have hyC : y ∈ C := hu.2.2.1.1 hy
        refine ⟨⟨y, hyC⟩, ?_, rfl⟩
        have hpc := hu.2.2.1
        obtain ⟨-, K', hK', -, hmap, -⟩ := hpc
        rw [← hmap] at hK'
        have hne : (A.subgroupOf C).map π ≠ F := fun h => hFA ⟨A, hA, h⟩
        have hc := (LocalCores.distinct_components_commute hK' hF).resolve_left hne
        exact (commutator_eq_bot_iff_le_centralizer.mp hc)
          (mem_map_of_mem π (show (⟨y, hyC⟩ : ↥C) ∈ A.subgroupOf C from hy))
    obtain ⟨y, hy, hyz⟩ := hle ((show zStar (K0 X n C) ≤ K0 X n C from inf_le_left) hz)
    have : y = ⟨z, hzC⟩ := Subtype.ext hyz
    rw [← this]
    exact hy

private theorem ec_lemmaT
    {X : Type} [Group X] [Finite X] {n : ℕ} {t x : X}
    (hx : x ∈ Sec6Base X n t) (hx2 : x ^ 2 = 1) :
    oddCoreOf (cen t ⊓ cen x) ≤ oddCoreOf (cen t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxC : x ∈ cen t := ec_base_le_cen hx
  have hZC : zStar (K0 X n (cen t)) ≤ cen t := inf_le_left.trans ec_K0_le
  have hx' : x ∈ ((zStar (K0 X n (cen t)) ⊔ Sec6M X n (cen t) : Subgroup X) : Set X) := by
    rw [sup_comm]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right _ _ (hZC.trans (Sec6M_cen_normal n t))] at hx'
  obtain ⟨z, hz, m, hm, hxzm⟩ := hx'
  set C : Subgroup X := cen t with hCdef
  have hMC : Sec6M X n C ≤ C := ec_M_le
  have hzC : z ∈ C := hZC hz
  have hmC : m ∈ C := hMC hm
  have hQC : oddCoreOf (C ⊓ cen x) ≤ C := (oddCoreOf_le _).trans inf_le_left
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set x' : ↥C := ⟨x, hxC⟩
  set P := ((oddCoreOf (C ⊓ cen x)).subgroupOf C).map π
  have hPodd : Odd (Nat.card P) := by
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ π)
    rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv]
    exact odd_card_oddCoreOf _
  have hPβ : P ≤ centralizer ({π x'} : Set _) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      ((inf_le_right : C ⊓ cen x ≤ cen x) (oddCoreOf_le _ hq)))
  have hPn : centralizer ({π x'} : Set _) ≤ normalizer (P : Set _) := by
    have hN2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥C) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    have hx'2 : x' ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using hx2)
    have hcent := Semidihedral.Local.map_centralizer_eq_of_coprime 2 (pPrimeCore 2 ↥C) hN2
      (zpowers x') (ec_isPGroup_zpowers hx'2)
    rw [← hπ, MonoidHom.map_zpowers, ec_centralizer_zpowers, ec_centralizer_zpowers] at hcent
    rw [← hcent]
    refine (map_mono ?_).trans (le_normalizer_map π)
    intro y hy
    have hyb : (y : X) ∈ C ⊓ cen x :=
      ⟨y.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mem_centralizer_singleton_iff.mp hy))⟩
    have hyQ := le_normalizer_oddCoreOf (C ⊓ cen x) hyb
    rw [mem_normalizer_iff]
    intro h
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp hyQ h
  set 𝓜 : Set (Subgroup (↥C ⧸ pPrimeCore 2 ↥C)) :=
    {K | ∃ M, Sec6MComp X n C M ∧ (M.subgroupOf C).map π = K}
  have h𝓜 : ∀ K ∈ 𝓜, IsComponent K ∧ EcRigid ↥K := by
    rintro K ⟨M, hM, rfl⟩
    obtain ⟨⟨⟨hMC, K', hK', hsub, hmap, -⟩, hty, -⟩, -⟩ := hM
    obtain ⟨e, -⟩ :=
      ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hMC hsub
    rw [← hmap] at hK'
    refine ⟨hK', ?_⟩
    rcases hty with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
    · exact ec_rigid_of_mcl (e.symm.trans eM)
    · exact ec_rigid_of_ly (e.symm.trans eL)
  have hπm : π ⟨m, hmC⟩ ∈ sSup 𝓜 := by
    have hle : Sec6M X n C ≤ ((sSup 𝓜).comap π).map C.subtype := sSup_le fun M hM y hy => by
      have hyC : y ∈ C := hM.1.1.1 hy
      refine ⟨⟨y, hyC⟩, ?_, rfl⟩
      have hK : (M.subgroupOf C).map π ≤ sSup 𝓜 := le_sSup ⟨M, hM, rfl⟩
      exact hK (mem_map_of_mem π (show (⟨y, hyC⟩ : ↥C) ∈ M.subgroupOf C from hy))
    obtain ⟨y, hy, hym⟩ := hle hm
    have : y = ⟨m, hmC⟩ := Subtype.ext hym
    rw [← this]
    exact hy
  have hπz : ∀ F : Subgroup (↥C ⧸ pPrimeCore 2 ↥C), IsComponent F →
      π ⟨z, hzC⟩ ∈ centralizer (F : Set _) := fun F hF => ec_zStar_central hz hzC F hF
  have hπx : π x' = π ⟨z, hzC⟩ * π ⟨m, hmC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hxzm.symm
  have hβ2 : (π x') ^ 2 = 1 := by
    rw [← map_pow, show x' ^ 2 = 1 from Subtype.ext (by simpa using hx2), map_one]
  have hP1 : P = ⊥ := by
    refine ec_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hβ2 hPodd hPβ hPn ?_
    intro F hF hβF
    rcases ec_dec (fun K hK => (h𝓜 K hK).1) hπm hF with hmF | ⟨hF𝓜, c, hcF, w, hw, hmcw⟩
    · exact absurd (hπx ▸ mul_mem (hπz F hF) hmF) hβF
    · refine ⟨c, hcF, π ⟨z, hzC⟩ * w, mul_mem (hπz F hF) hw, ?_, Or.inl (h𝓜 F hF𝓜).2⟩
      have hzc : π ⟨z, hzC⟩ * c = c * π ⟨z, hzC⟩ :=
        ((mem_centralizer_iff.mp (hπz F hF)) c hcF).symm
      rw [hπx, hmcw, ← mul_assoc, hzc, mul_assoc]
  intro y hy
  have hyC : y ∈ C := hQC hy
  have hyP : π ⟨y, hyC⟩ ∈ P := mem_map_of_mem π (show (⟨y, hyC⟩ : ↥C) ∈ _ from hy)
  rw [hP1, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hyP
  exact ⟨⟨y, hyC⟩, hyP, rfl⟩

private abbrev ecY (X : Type) [Group X] (n : ℕ) (t b : X) : Subgroup X :=
  ⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L b

private theorem ecY_le_cen_t {X : Type} [Group X] {n : ℕ} {t b : X} : ecY X n t b ≤ cen t :=
  iSup₂_le fun L hL => (oTwoPrimeOf_le _).trans (inf_le_left.trans (ec_kcomp_pc hL).1)

private theorem ecY_le_cen_b {X : Type} [Group X] {n : ℕ} {t b : X} : ecY X n t b ≤ cen b :=
  iSup₂_le fun L _ => (oTwoPrimeOf_le _).trans inf_le_right

private theorem piece_le_ecY {X : Type} [Group X] {n : ℕ} {t b : X} {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) : sec6Piece L b ≤ ecY X n t b :=
  le_iSup₂_of_le (f := fun L (_ : Sec6KComp X n (cen t) L) => sec6Piece L b) L hL le_rfl

private theorem ec_loc
    {X : Type} [Group X] [Finite X] {n : ℕ} {t a b : X}
    (ha : a ∈ Sec6Base X n t) (ha2 : a ^ 2 = 1) (hb : b ∈ Sec6Base X n t) (hb2 : b ^ 2 = 1)
    (hab : a * b = b * a) :
    a ∈ ecY X n t b ⊔ (oddCoreOf (cen t) ⊓ cen b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYC : ecY X n t b ≤ cen t := ecY_le_cen_t
  have hYb : ecY X n t b ≤ cen b := ecY_le_cen_b
  have haC : a ∈ cen t := ec_base_le_cen ha
  have hbC : b ∈ cen t := ec_base_le_cen hb
  have hZC : zStar (K0 X n (cen t)) ≤ cen t := inf_le_left.trans ec_K0_le
  have hdec : ∀ x ∈ Sec6Base X n t,
      ∃ z ∈ zStar (K0 X n (cen t)), ∃ m ∈ Sec6M X n (cen t), z * m = x := by
    intro x hx
    have hx' : x ∈ ((zStar (K0 X n (cen t)) ⊔ Sec6M X n (cen t) : Subgroup X) : Set X) := by
      rw [sup_comm]
      exact hx
    rw [coe_mul_of_left_le_normalizer_right _ _ (hZC.trans (Sec6M_cen_normal n t))] at hx'
    exact hx'
  obtain ⟨z, hz, m, hm, hzm⟩ := hdec a ha
  obtain ⟨z', hz', m', hm', hzm'⟩ := hdec b hb
  have hzC : z ∈ cen t := hZC hz
  have hz'C : z' ∈ cen t := hZC hz'
  have hmC : m ∈ cen t := ec_M_le hm
  have hm'C : m' ∈ cen t := ec_M_le hm'
  set C : Subgroup X := cen t with hCdef
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set 𝓜 : Set (Subgroup (↥C ⧸ pPrimeCore 2 ↥C)) :=
    {K | ∃ L, Sec6MComp X n C L ∧ (L.subgroupOf C).map π = K} with h𝓜def
  have h𝓜c : ∀ K ∈ 𝓜, IsComponent K := by
    rintro K ⟨L, hL, rfl⟩
    obtain ⟨-, K', hK', -, hmap, -⟩ := hL.1.1
    rw [hmap]
    exact hK'
  have h𝓜Z : ∀ K ∈ 𝓜, ∀ w ∈ K, (∀ y ∈ K, w * y = y * w) → w = 1 := by
    rintro K ⟨L, hL, rfl⟩ w hw hwc
    obtain ⟨hLC, -, -, hsub, -, -⟩ := hL.1.1
    obtain ⟨e, -⟩ :=
      ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hLC
        hsub
    have hZ : center ↥((L.subgroupOf C).map π) = ⊥ := by
      rcases hL.1.2.1 with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
      · exact ec_center_eq_bot_of_type (Or.inl ⟨e.symm.trans eM⟩)
      · exact ec_center_eq_bot_of_type (Or.inr ⟨e.symm.trans eL⟩)
    have hwZ : (⟨w, hw⟩ : ↥((L.subgroupOf C).map π)) ∈ center _ := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hwc g g.2).symm
    rw [hZ, mem_bot] at hwZ
    exact congrArg Subtype.val hwZ
  have h𝓜comm : ∀ K ∈ 𝓜, ∀ K' ∈ 𝓜, K ≠ K' → K' ≤ centralizer (K : Set _) :=
    fun K hK K' hK' hne => commutator_eq_bot_iff_le_centralizer.mp
      ((LocalCores.distinct_components_commute (h𝓜c K' hK') (h𝓜c K hK)).resolve_left
        (Ne.symm hne))
  have hmem : ∀ x ∈ Sec6M X n C, ∀ hx : x ∈ C, π ⟨x, hx⟩ ∈ sSup 𝓜 := by
    intro x hxM hxC
    have hle : Sec6M X n C ≤ ((sSup 𝓜).comap π).map C.subtype :=
      sSup_le fun L (hL : Sec6MComp X n C L) y hy => by
        refine ⟨⟨y, hL.1.1.1 hy⟩, ?_, rfl⟩
        have hK : (L.subgroupOf C).map π ≤ sSup 𝓜 := le_sSup ⟨L, hL, rfl⟩
        exact hK (mem_map_of_mem π (show (⟨y, hL.1.1.1 hy⟩ : ↥C) ∈ L.subgroupOf C from hy))
    obtain ⟨y, hy, hyx⟩ := hle hxM
    have : y = ⟨x, hxC⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have hcz : ∀ F : Subgroup (↥C ⧸ pPrimeCore 2 ↥C), IsComponent F →
      π ⟨z, hzC⟩ ∈ centralizer (F : Set _) := fun F hF => ec_zStar_central hz hzC F hF
  have hcz' : ∀ F : Subgroup (↥C ⧸ pPrimeCore 2 ↥C), IsComponent F →
      π ⟨z', hz'C⟩ ∈ centralizer (F : Set _) := fun F hF => ec_zStar_central hz' hz'C F hF
  have hcM : ∀ g : ↥C ⧸ pPrimeCore 2 ↥C, (∀ F : Subgroup (↥C ⧸ pPrimeCore 2 ↥C), IsComponent F →
        g ∈ centralizer (F : Set _)) →
      ∀ y ∈ sSup 𝓜, g * y = y * g := by
    intro g hg y hy
    have hle : sSup 𝓜 ≤ centralizer ({g} : Set _) := sSup_le fun K hK k hk =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hg K (h𝓜c K hK))) k hk)
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hcA : ∀ g : ↥C ⧸ pPrimeCore 2 ↥C, (∀ F : Subgroup (↥C ⧸ pPrimeCore 2 ↥C), IsComponent F →
        g ∈ centralizer (F : Set _)) →
      ∀ y (hyC : y ∈ C), y ∈ K0 X n C → π ⟨y, hyC⟩ * g = g * π ⟨y, hyC⟩ := by
    intro g hg y hyC hy
    have hle : K0 X n C ≤ ((centralizer ({g} : Set _)).comap π).map C.subtype :=
      sSup_le fun A hA w hw => by
        obtain ⟨u, hu⟩ := hA.1
        have hwC : w ∈ C := hu.2.2.1.1 hw
        refine ⟨⟨w, hwC⟩, ?_, rfl⟩
        obtain ⟨-, K', hK', -, hmap, -⟩ := hu.2.2.1
        rw [← hmap] at hK'
        show π ⟨w, hwC⟩ ∈ centralizer ({g} : Set _)
        exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hg _ hK')) _
          (mem_map_of_mem π (show (⟨w, hwC⟩ : ↥C) ∈ A.subgroupOf C from hw)))
    obtain ⟨y', hy', hyy'⟩ := hle hy
    have : y' = ⟨y, hyC⟩ := Subtype.ext hyy'
    rw [← this]
    exact mem_centralizer_singleton_iff.mp hy'
  have hπa : π ⟨a, haC⟩ = π ⟨z, hzC⟩ * π ⟨m, hmC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hzm.symm
  have hπb : π ⟨b, hbC⟩ = π ⟨z', hz'C⟩ * π ⟨m', hm'C⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hzm'.symm
  have hzm_c : π ⟨z, hzC⟩ * π ⟨m, hmC⟩ = π ⟨m, hmC⟩ * π ⟨z, hzC⟩ :=
    hcM _ hcz _ (hmem m hm hmC)
  have hzm'_c : π ⟨z, hzC⟩ * π ⟨m', hm'C⟩ = π ⟨m', hm'C⟩ * π ⟨z, hzC⟩ :=
    hcM _ hcz _ (hmem m' hm' hm'C)
  have hz'm_c : π ⟨z', hz'C⟩ * π ⟨m, hmC⟩ = π ⟨m, hmC⟩ * π ⟨z', hz'C⟩ :=
    hcM _ hcz' _ (hmem m hm hmC)
  have hzz' : π ⟨z', hz'C⟩ * π ⟨z, hzC⟩ = π ⟨z, hzC⟩ * π ⟨z', hz'C⟩ :=
    hcA _ hcz z' hz'C hz'.1
  have hab' : π ⟨a, haC⟩ * π ⟨b, hbC⟩ = π ⟨b, hbC⟩ * π ⟨a, haC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hab
  have hmm' : π ⟨m, hmC⟩ * π ⟨m', hm'C⟩ = π ⟨m', hm'C⟩ * π ⟨m, hmC⟩ := by
    have e : π ⟨z, hzC⟩ * π ⟨z', hz'C⟩ * (π ⟨m, hmC⟩ * π ⟨m', hm'C⟩) =
        π ⟨z, hzC⟩ * π ⟨z', hz'C⟩ * (π ⟨m', hm'C⟩ * π ⟨m, hmC⟩) := by
      calc π ⟨z, hzC⟩ * π ⟨z', hz'C⟩ * (π ⟨m, hmC⟩ * π ⟨m', hm'C⟩)
          = π ⟨z, hzC⟩ * (π ⟨z', hz'C⟩ * π ⟨m, hmC⟩) * π ⟨m', hm'C⟩ := by group
        _ = π ⟨z, hzC⟩ * (π ⟨m, hmC⟩ * π ⟨z', hz'C⟩) * π ⟨m', hm'C⟩ := by rw [hz'm_c]
        _ = π ⟨a, haC⟩ * π ⟨b, hbC⟩ := by rw [hπa, hπb]; group
        _ = π ⟨b, hbC⟩ * π ⟨a, haC⟩ := hab'
        _ = π ⟨z', hz'C⟩ * (π ⟨m', hm'C⟩ * π ⟨z, hzC⟩) * π ⟨m, hmC⟩ := by rw [hπa, hπb]; group
        _ = π ⟨z', hz'C⟩ * (π ⟨z, hzC⟩ * π ⟨m', hm'C⟩) * π ⟨m, hmC⟩ := by rw [hzm'_c]
        _ = (π ⟨z', hz'C⟩ * π ⟨z, hzC⟩) * (π ⟨m', hm'C⟩ * π ⟨m, hmC⟩) := by group
        _ = π ⟨z, hzC⟩ * π ⟨z', hz'C⟩ * (π ⟨m', hm'C⟩ * π ⟨m, hmC⟩) := by rw [hzz']
    exact mul_left_cancel e
  obtain ⟨N, hNodd, j, hj⟩ := exists_odd_pow_twoElt (π ⟨m, hmC⟩)
  have haN : π ⟨a, haC⟩ ^ N = π ⟨a, haC⟩ := by
    obtain ⟨r, rfl⟩ := hNodd
    have h2 : π ⟨a, haC⟩ ^ 2 = 1 := by
      rw [← map_pow, show (⟨a, haC⟩ : ↥C) ^ 2 = 1 from Subtype.ext (by simpa using ha2), map_one]
    rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  have haN' : π ⟨a, haC⟩ = π ⟨z, hzC⟩ ^ N * π ⟨m, hmC⟩ ^ N := by
    calc π ⟨a, haC⟩ = π ⟨a, haC⟩ ^ N := haN.symm
      _ = (π ⟨z, hzC⟩ * π ⟨m, hmC⟩) ^ N := by rw [hπa]
      _ = π ⟨z, hzC⟩ ^ N * π ⟨m, hmC⟩ ^ N :=
        (show Commute (π ⟨z, hzC⟩) (π ⟨m, hmC⟩) from hzm_c).mul_pow N
  set W := ((ecY X n t b).subgroupOf C).map π with hW
  have hWcond : ∀ K ∈ 𝓜, ∀ y ∈ K, y * π ⟨m', hm'C⟩ = π ⟨m', hm'C⟩ * y →
      (∃ k : ℕ, y ^ (2 ^ k) = 1) → y ∈ W := by
    rintro K ⟨L, hL, rfl⟩ _ ⟨y, hy, rfl⟩ hym' ⟨k, hk⟩
    have hyL : (y : X) ∈ L := hy
    obtain ⟨hLC, -, -, hsub, -, -⟩ := hL.1.1
    have hOL : oddCoreOf L ≤ oddCoreOf C := pPrimeCoreOf_le_oddCoreOf hLC hsub
    have hLO : L ⊓ oddCoreOf C ≤ oddCoreOf L :=
      le_oddCoreOf_of_normalized inf_le_left
        (fun l hl => mem_normalizer_inf (le_normalizer hl) (le_normalizer_oddCoreOf C (hLC hl)))
        ((odd_card_oddCoreOf C).of_dvd_nat (card_dvd_of_le inf_le_right))
    have hyk : (y : X) ^ (2 ^ k) ∈ oddCoreOf L := by
      refine hLO ⟨pow_mem hyL _, ?_⟩
      have h1 := (ec_mk_eq_one_iff (y ^ (2 ^ k))).mp (by rw [← hπ, map_pow]; exact hk)
      rwa [coe_pow] at h1
    obtain ⟨μ, hμ1, hμ2⟩ :=
      exists_zpow_twoElt_of_pow_mem (Nat.coprime_two_left.mpr (odd_card_oddCoreOf L)) hyk
    have hy'L : (y : X) ^ μ ∈ L := zpow_mem hyL μ
    have hy'C : (y : X) ^ μ ∈ C := hLC hy'L
    have hπy' : π ⟨(y : X) ^ μ, hy'C⟩ = π y := by
      have h1 : π (y⁻¹ * ⟨(y : X) ^ μ, hy'C⟩) = 1 := (ec_mk_eq_one_iff _).mpr (hOL hμ2)
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1.symm
    have hyz' : π y * π ⟨z', hz'C⟩ = π ⟨z', hz'C⟩ * π y :=
      (mem_centralizer_iff.mp (hcz' _ (h𝓜c _ ⟨L, hL, rfl⟩))) _ (mem_map_of_mem π hy)
    have hyb : π y * π ⟨b, hbC⟩ = π ⟨b, hbC⟩ * π y := by
      rw [hπb]
      exact (show Commute (π y) (π ⟨z', hz'C⟩ * π ⟨m', hm'C⟩) from
        Commute.mul_right hyz' hym').eq
    have hbN : b ∈ normalizer (L : Set X) := ec_K_le_normalizer (Or.inr hL) (ec_base_le_K hb)
    have hbO : b ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
      mem_normalizer_oddCoreOf_of_mem_normalizer hbN
    have hcomm : ⁅(y : X) ^ μ, b⁆ ∈ pPrimeCoreOf 2 L := by
      refine hLO ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have h1 : b * ((y : X) ^ μ)⁻¹ * b⁻¹ ∈ L :=
          (mem_normalizer_iff.mp hbN _).mp (inv_mem hy'L)
        rw [show (y : X) ^ μ * b * ((y : X) ^ μ)⁻¹ * b⁻¹ =
          (y : X) ^ μ * (b * ((y : X) ^ μ)⁻¹ * b⁻¹) by group]
        exact mul_mem hy'L h1
      · have h1 : π (⟨(y : X) ^ μ, hy'C⟩ * ⟨b, hbC⟩ * ⟨(y : X) ^ μ, hy'C⟩⁻¹ * ⟨b, hbC⟩⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπy', hyb, mul_inv_cancel_right,
            mul_inv_cancel]
        have h2 := (ec_mk_eq_one_iff _).mp h1
        rw [commutatorElement_def]
        exact h2
    obtain ⟨c, hc, hck, hcy⟩ := exists_twoElt_centralizer_of_comm_mem hb2 hbO hy'L hcomm hμ1
    have hcY : c ∈ ecY X n t b := piece_le_ecY (Or.inr hL) (mem_oTwoPrimeOf hc k hck)
    have hcC : c ∈ C := hYC hcY
    refine ⟨⟨c, hcC⟩, hcY, ?_⟩
    rw [← hπy']
    have h1 : π ((⟨c, hcC⟩ : ↥C)⁻¹ * ⟨(y : X) ^ μ, hy'C⟩) = 1 :=
      (ec_mk_eq_one_iff _).mpr (hOL hcy)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hmN : π ⟨m, hmC⟩ ^ N ∈ W := by
    refine ec_decomp W 𝓜 (Set.toFinite 𝓜) h𝓜Z h𝓜comm _ (hmem m' hm' hm'C) hWcond _
      (pow_mem (hmem m hm hmC) N) ?_ j hj
    exact ((show Commute (π ⟨m, hmC⟩) (π ⟨m', hm'C⟩) from hmm').pow_left N).eq
  have hK0Y : K0 X n C ≤ ecY X n t b ⊔ oddCoreOf C := sSup_le fun A hA => by
    have hA' : Sec5Comp X n C A := hA
    have hApc : IsPCompIn 2 C A := ec_kcomp_pc (Or.inl hA')
    obtain ⟨-, hcov⟩ := isPCompIn_restrict hApc hb2 (ec_base_le_cS hA' hb)
    have hcov' := (covers_subgroupOf_iff ((oTwoPrimeOf_le _).trans inf_le_left)).mp hcov
    rw [← hcov']
    exact sup_le_sup (piece_le_ecY (Or.inl hA')) (ec_core_le_of_pc hApc)
  have hzN : π ⟨z, hzC⟩ ^ N ∈ W := by
    have hzN' : z ^ N ∈ ((ecY X n t b ⊔ oddCoreOf C : Subgroup X) : Set X) :=
      hK0Y (pow_mem hz.1 N)
    rw [coe_mul_of_left_le_normalizer_right _ _ (hYC.trans (le_normalizer_oddCoreOf C))] at hzN'
    obtain ⟨w, hw, o, ho, hwo⟩ := hzN'
    have hwC : w ∈ C := hYC hw
    refine ⟨⟨w, hwC⟩, hw, ?_⟩
    rw [← map_pow]
    have h1 : π ((⟨w, hwC⟩ : ↥C)⁻¹ * ⟨z, hzC⟩ ^ N) = 1 := by
      apply (ec_mk_eq_one_iff _).mpr
      have e : (((⟨w, hwC⟩ : ↥C)⁻¹ * ⟨z, hzC⟩ ^ N : ↥C) : X) = o := by
        show w⁻¹ * z ^ N = o
        rw [← hwo]
        group
      rw [e]
      exact ho
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have haW : π ⟨a, haC⟩ ∈ W := by
    rw [haN']
    exact mul_mem hzN hmN
  obtain ⟨w, hw, hwa⟩ := haW
  have hwY : (w : X) ∈ ecY X n t b := hw
  have h1 : π (w⁻¹ * ⟨a, haC⟩) = 1 := by rw [map_mul, map_inv, hwa, inv_mul_cancel]
  have h2 : (w : X)⁻¹ * a ∈ oddCoreOf C := (ec_mk_eq_one_iff _).mp h1
  have h3 : (w : X)⁻¹ * a ∈ cen b :=
    mul_mem (inv_mem (hYb hwY)) (mem_centralizer_singleton_iff.mpr hab)
  rw [show a = (w : X) * ((w : X)⁻¹ * a) by group]
  exact mul_mem_sup hwY ⟨h2, h3⟩

private theorem ec_claimA
    {X : Type} [Group X] [Finite X] {n : ℕ} {t a b : X} (ht2 : t * t = 1)
    (hC : Sec6CtrlAt X n t) (hb : b ∈ Sec6Base X n t) (hb2 : orderOf b = 2)
    (haY : a ∈ ecY X n t b) (haB : a ∈ Sec6Base X n t) (ha22 : a ^ 2 = 1) :
    oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbMQ : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := ec_base_le_MQ hb
  have hab : a ∈ cen b := ecY_le_cen_b haY
  have hta : t ∈ cen a :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (ec_base_le_cen haB)).symm
  have htb : t ∈ cen b :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (ec_base_le_cen hb)).symm
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(cen b)) with hπ
  set P := oddCoreOf (cen a) ⊓ cen b with hP
  have hPb : P ≤ cen b := inf_le_right
  have hPodd' : Odd (Nat.card P) :=
    (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
  set Pb := (P.subgroupOf (cen b)).map π with hPbdef
  have hPodd : Odd (Nat.card Pb) := by
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ π)
    rw [Nat.card_congr (subgroupOfEquivOfLe hPb).toEquiv]
    exact hPodd'
  have hPβ : Pb ≤ centralizer ({π ⟨a, hab⟩} : Set _) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (oddCoreOf_le _ hq.1))
  have hPn : centralizer ({π ⟨a, hab⟩} : Set _) ≤ normalizer (Pb : Set _) := by
    have hN2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(cen b)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    have ha'2 : (⟨a, hab⟩ : ↥(cen b)) ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using ha22)
    have hcent := Semidihedral.Local.map_centralizer_eq_of_coprime 2 (pPrimeCore 2 ↥(cen b))
      hN2 (zpowers ⟨a, hab⟩) (ec_isPGroup_zpowers ha'2)
    rw [← hπ, MonoidHom.map_zpowers, ec_centralizer_zpowers, ec_centralizer_zpowers] at hcent
    rw [← hcent]
    refine (map_mono ?_).trans (le_normalizer_map π)
    intro z hz
    have hza : (z : X) ∈ cen a := mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_centralizer_singleton_iff.mp hz))
    have hzP : (z : X) ∈ normalizer (P : Set X) :=
      mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hza) (le_normalizer z.2)
    rw [mem_normalizer_iff]
    intro h
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp hzP h
  set 𝓕 : Set (Subgroup (↥(cen b) ⧸ pPrimeCore 2 ↥(cen b))) :=
    {K | ∃ F, Sec6KComp X n (cen b) F ∧ (∃ L, Sec6KComp X n (cen t) L ∧ sec6Piece L b ≤ F) ∧
      (F.subgroupOf (cen b)).map π = K} with h𝓕def
  have h𝓕 : ∀ K ∈ 𝓕, IsComponent K := by
    rintro K ⟨F, hF, -, rfl⟩
    obtain ⟨-, K', hK', -, hmap, -⟩ := ec_kcomp_pc hF
    rw [hmap]
    exact hK'
  have haBar : π ⟨a, hab⟩ ∈ sSup 𝓕 := by
    have hle : ecY X n t b ≤ ((sSup 𝓕).comap π).map (cen b).subtype :=
      iSup₂_le fun L hL y hy => by
        obtain ⟨F, hF, hLF⟩ := hC.land b hbMQ hb2 L hL
        have hyb : y ∈ cen b := ((oTwoPrimeOf_le _).trans inf_le_right) hy
        refine ⟨⟨y, hyb⟩, ?_, rfl⟩
        have hK : (F.subgroupOf (cen b)).map π ≤ sSup 𝓕 := le_sSup ⟨F, hF, ⟨L, hL, hLF⟩, rfl⟩
        exact hK (mem_map_of_mem π
          (show (⟨y, hyb⟩ : ↥(cen b)) ∈ F.subgroupOf (cen b) from hLF hy))
    obtain ⟨y, hy, hya⟩ := hle haY
    have : y = ⟨a, hab⟩ := Subtype.ext hya
    rw [← this]
    exact hy
  have hβ2 : (π ⟨a, hab⟩) ^ 2 = 1 := by
    rw [← map_pow, show (⟨a, hab⟩ : ↥(cen b)) ^ 2 = 1 from Subtype.ext (by simpa using ha22),
      map_one]
  have hP1 : Pb = ⊥ := by
    refine ec_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hβ2 hPodd hPβ hPn ?_
    intro F hF hβF
    rcases ec_dec h𝓕 haBar hF with h | ⟨hF𝓕, c, hcF, w, hw, hβcw⟩
    · exact absurd h hβF
    refine ⟨c, hcF, w, hw, hβcw, ?_⟩
    obtain ⟨F₀, hF₀, ⟨L, hL, hLF⟩, rfl⟩ := hF𝓕
    have hF₀pc : IsPCompIn 2 (cen b) F₀ := ec_kcomp_pc hF₀
    obtain ⟨-, hdich⟩ := hC.dich b hbMQ hb2 L F₀ hL hF₀ hLF
    rcases hdich with hF₀eq | ⟨hM, -, -⟩
    ·
      right
      intro hPF
      have heq : ((sec6Piece L b).subgroupOf (cen b)).map π = (F₀.subgroupOf (cen b)).map π := by
        have hOF : oddCoreOf F₀ ≤ oddCoreOf (cen b) := ec_core_le_of_pc hF₀pc
        apply le_antisymm
        · exact map_mono fun x hx => hLF hx
        · rintro _ ⟨f, hf, rfl⟩
          have hfF : (f : X) ∈ ((sec6Piece L b ⊔ oddCoreOf F₀ : Subgroup X) : Set X) := by
            rw [sup_comm, ← hF₀eq]
            exact hf
          rw [coe_mul_of_left_le_normalizer_right _ _
            (fun y hy => le_normalizer_oddCoreOf F₀ (hLF hy))] at hfF
          obtain ⟨p, hp, o, ho, hpo⟩ := hfF
          have hpb : p ∈ cen b := ((oTwoPrimeOf_le _).trans inf_le_right) hp
          have hob : o ∈ cen b := by
            have : o = p⁻¹ * f := by
              rw [← hpo]
              group
            rw [this]
            exact mul_mem (inv_mem hpb) f.2
          refine ⟨⟨p, hpb⟩, hp, ?_⟩
          have h1 : π ⟨o, hob⟩ = 1 := (ec_mk_eq_one_iff _).mpr (hOF ho)
          have h2 : f = ⟨p, hpb⟩ * ⟨o, hob⟩ := Subtype.ext hpo.symm
          rw [h2, map_mul, h1, mul_one]
      rw [← heq] at hPF hF ⊢
      refine ec_tTrick (V := oddCoreOf (cen t) ⊓ cen b) htb ht2 inf_le_right ?_ ?_ hPodd' ?_ ?_ ?_
        hF hPF
      · intro d hd
        exact mem_centralizer_singleton_iff.mp
          ((ec_kcomp_pc hL).1 (((oTwoPrimeOf_le _).trans inf_le_left) hd))
      · exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hta) (le_normalizer htb)
      · exact (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
      · intro d hd
        have hd' : d ∈ L ⊓ cen b := oTwoPrimeOf_le _ hd
        exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen t) ((ec_kcomp_pc hL).1 hd'.1))
          (le_normalizer hd'.2)
      · intro c' hc' hc't
        refine ⟨?_, hc'.2⟩
        have h1 : c' ∈ oddCoreOf (cen t ⊓ cen a) := by
          refine le_oddCoreOf_of_normalized (N := oddCoreOf (cen a) ⊓ cen t) ?_ ?_ ?_
            ⟨hc'.1, mem_centralizer_singleton_iff.mpr hc't⟩
          · exact le_inf inf_le_right (inf_le_left.trans (oddCoreOf_le _))
          · intro y hy
            exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hy.2) (le_normalizer hy.1)
          · exact (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
        exact ec_lemmaT haB ha22 h1
    ·
      left
      obtain ⟨hFb, -, -, hsub, -, -⟩ := hF₀pc
      obtain ⟨e, -⟩ :=
        ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hFb
          hsub
      rcases hM.1.2.1 with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
      · exact ec_rigid_of_mcl (e.symm.trans eM)
      · exact ec_rigid_of_ly (e.symm.trans eL)
  intro x hx
  have hxb : x ∈ cen b := hx.2
  have hxP : π ⟨x, hxb⟩ ∈ Pb :=
    mem_map_of_mem π (show (⟨x, hxb⟩ : ↥(cen b)) ∈ P.subgroupOf (cen b) from hx)
  rw [hP1, mem_bot] at hxP
  exact (ec_mk_eq_one_iff _).mp hxP

theorem sec6_base_balance
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t) {a b : X}
    (ha : a ∈ Sec6Base X n t) (hb : b ∈ Sec6Base X n t) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (hab : a * b = b * a) :
    oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b) := by
  have hsq : ∀ {x : X}, orderOf x = 2 → x ^ 2 = 1 := fun hx => by
    rw [← hx]
    exact pow_orderOf_eq_one _
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have hmem := ec_loc ha (hsq ha2) hb (hsq hb2) hab
  have hYN : ecY X n t b ≤ normalizer ((oddCoreOf (cen t) ⊓ cen b : Subgroup X) : Set X) := by
    refine iSup₂_le fun L hL y hy => ?_
    have hy' : y ∈ L ⊓ cen b := oTwoPrimeOf_le _ hy
    exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen t) ((ec_kcomp_pc hL).1 hy'.1))
      (le_normalizer hy'.2)
  have hNodd : Odd (Nat.card ↥(oddCoreOf (cen t) ⊓ cen b)) :=
    (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨o, ho, a', ha', ha'2, rfl⟩ :=
    exists_conj_twoElt_of_mem_sup_odd_X hYN hNodd hmem (j := 1) (by rw [pow_one]; exact hsq ha2)
  have ha'22 : a' ^ 2 = 1 := by rwa [pow_one] at ha'2
  have hot : o ∈ cen t := (oddCoreOf_le _) ho.1
  have hob : o ∈ cen b := ho.2
  have ha'B : a' ∈ Sec6Base X n t := by
    have h1 : a' = o⁻¹ * (o * a' * o⁻¹) * o⁻¹⁻¹ := by group
    rw [h1]
    exact (mem_normalizer_iff.mp (cen_le_normalizer_sec6Base n t (inv_mem hot)) _).mp ha
  have hA := ec_claimA ht2 hC hb hb2 ha' ha'B ha'22
  intro x hx
  have h1 : oddCoreOf (cen (o * a' * o⁻¹)) =
      (oddCoreOf (cen a')).map (MulAut.conj o).toMonoidHom := by
    rw [oddCoreOf_map_mulEquiv', cen_map, MulAut.conj_apply]
  have hx1 : x ∈ (oddCoreOf (cen a')).map (MulAut.conj o).toMonoidHom := by
    rw [← h1]
    exact hx.1
  obtain ⟨x', hx', rfl⟩ := hx1
  have hx'b : x' ∈ cen b := by
    have h2 : o * x' * o⁻¹ ∈ cen b := hx.2
    have h3 : x' = o⁻¹ * (o * x' * o⁻¹) * o := by group
    rw [h3]
    exact mul_mem (mul_mem (inv_mem hob) h2) hob
  have h4 := hA ⟨hx', hx'b⟩
  exact (mem_normalizer_iff.mp (le_normalizer_oddCoreOf (cen b) hob) x').mp h4

theorem sec6_extCanon
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (hC : Sec6CtrlAt X n t)
    (hcan : ∀ B : Subgroup X, B ≤ Sec6M X n (cen t) → CFSG.Open.IsElemAbelian 2 B →
      Nat.card B = 4 → (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t)
    {E : Subgroup X} (hEB : E ≤ Sec6Base X n t) (hE : CFSG.Open.IsElemAbelian 2 E)
    (hE8 : 8 ≤ Nat.card E)
    (hEM : ∃ B : Subgroup X, B ≤ E ⊓ Sec6M X n (cen t) ∧ CFSG.Open.IsElemAbelian 2 B ∧
      Nat.card B = 4) :
    ∀ B : Subgroup X, B ≤ E → CFSG.Open.IsElemAbelian 2 B → Nat.card B = 4 →
      (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hinv : ∀ x ∈ E, x ≠ 1 → orderOf x = 2 := fun x hx hx1 => orderOf_eq_prime (hE.2 x hx) hx1
  have hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b) :=
    fun a ha ha1 b hb hb1 => sec6_base_balance hS hC (hEB ha) (hEB hb) (hinv a ha ha1)
      (hinv b hb hb1) (hEcomm a ha b hb)
  obtain ⟨-, -, hV⟩ := sec6_lambda2 hE hE8 hbal
  obtain ⟨B₀, hB₀, hB₀ab, hB₀4⟩ := hEM
  intro B hBE _ hB4
  rw [hV B hBE hB4, ← hV B₀ (hB₀.trans inf_le_left) hB₀4]
  exact hcan B₀ (hB₀.trans inf_le_right) hB₀ab hB₀4

end CFSG.OddStandard.Solomon75
