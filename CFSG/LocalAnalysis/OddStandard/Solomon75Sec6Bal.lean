module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs
import CFSG.Adapters.WholeGroupLayer
import CFSG.Sporadic.SmallOddCore.McLAut
import CFSG.LocalAnalysis.OddStandard.Solomon75T11bLy
import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.Ly.Primitive
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Schreier.PairMcLFaithful

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

private theorem isPGroup_zpowers_of_pow {G : Type} [Group G] {a : G} {k : ℕ}
    (ha : a ^ (2 ^ k) = 1) : IsPGroup 2 (zpowers a) := fun g => by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    ha, one_zpow, OneMemClass.coe_one]

private theorem centralizer_zpowers_eq_singleton {G : Type} [Group G] (a : G) :
    centralizer (zpowers a : Set G) = centralizer ({a} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem eq_bot_of_odd_of_le_centralizer_layer {G : Type} [Group G] [Finite G]
    (hO : pPrimeCore 2 G = ⊥) {a : G} {k : ℕ} (ha : a ^ (2 ^ k) = 1) {P : Subgroup G}
    (hPodd : Odd (Nat.card P)) (hPa : P ≤ centralizer ({a} : Set G))
    (hPn : centralizer ({a} : Set G) ≤ normalizer (P : Set G))
    (hPE : P ≤ centralizer (layer G : Set G)) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen := centralizer_zpowers_eq_singleton a
  have hPn' : (P.subgroupOf (centralizer (zpowers a : Set G))).Normal := by
    rw [hcen]
    exact (normal_subgroupOf_iff_le_normalizer hPa).mpr hPn
  have hPQ : ⁅P, pCore 2 G⁆ = ⊥ :=
    ComponentClassification.SmallLocal.normal_coprime_centralizer_centralizes_prime_core
      Nat.prime_two (isPGroup_zpowers_of_pow ha) (hcen ▸ hPa) hPn'
      (Nat.coprime_two_left.mpr hPodd)
  have hPF : P ≤ centralizer (generalizedFitting G : Set G) := by
    rw [le_centralizer_iff, generalizedFitting.eq_sup, Fitting_eq_pcore G 2 hO]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hPQ))
      (le_centralizer_iff.mp hPE)
  have hP2 : IsPGroup 2 P := (pCore_isPGroup (p := 2) (G := G)).to_le
    (hPF.trans ((Adapters.centralizer_generalizedFitting_le_fittingSubgroup G).trans
      (Fitting_eq_pcore G 2 hO).le))
  obtain ⟨m, hm⟩ := hP2.exists_card_eq
  rcases m with _ | m
  · exact card_eq_one.mp (by rw [hm, pow_zero])
  · exfalso
    rw [hm] at hPodd
    exact (Nat.not_even_iff_odd.mpr hPodd) (Nat.even_pow.mpr ⟨even_two, m.succ_ne_zero⟩)

theorem le_normalizer_component_of_odd {G : Type} [Group G] [Finite G] {a : G}
    {P F : Subgroup G} (hPodd : Odd (Nat.card P)) (hPa : P ≤ centralizer ({a} : Set G))
    (hPn : centralizer ({a} : Set G) ≤ normalizer (P : Set G)) (hF : IsComponent F)
    {c : G} (hcF : c ∈ F) (hca : c ∈ centralizer ({a} : Set G)) {m : ℕ} (hc2 : c ^ (2 ^ m) = 1)
    (hcZ : c ∉ centralizer (F : Set G)) : P ≤ normalizer (F : Set G) := by
  intro p hp
  set F' := F.map (MulAut.conj p).toMonoidHom
  have hmem : ∀ h, p * h * p⁻¹ ∈ F' ↔ h ∈ F := fun h => by
    constructor
    · rintro ⟨h', hh', he⟩
      have : h' = h := by
        simpa [MulAut.conj_apply] using he
      exact this ▸ hh'
    · intro hh
      exact ⟨h, hh, rfl⟩
  by_cases hFF : F' = F
  · rw [mem_normalizer_iff]
    intro h
    rw [← hmem h, hFF]
  · exfalso
    have hF'c : IsComponent F' := LocalCores.isComponent_map_mulEquiv (MulAut.conj p) hF
    have hcomm : F' ≤ centralizer (F : Set G) := le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        ((LocalCores.distinct_components_commute hF hF'c).resolve_left (Ne.symm hFF)))
    have hdF' : p * c⁻¹ * p⁻¹ ∈ F' := (hmem c⁻¹).mpr (inv_mem hcF)
    have hcd : Commute c (p * c⁻¹ * p⁻¹) := mem_centralizer_iff.mp (hcomm hdF') c hcF
    have hx : c * (p * c⁻¹ * p⁻¹) ∈ P := by
      have h1 : c * p * c⁻¹ ∈ P := (mem_normalizer_iff.mp (hPn hca) p).mp hp
      have : c * (p * c⁻¹ * p⁻¹) = c * p * c⁻¹ * p⁻¹ := by group
      rw [this]
      exact mul_mem h1 (inv_mem hp)
    set r := orderOf (c * (p * c⁻¹ * p⁻¹)) with hr
    have hrodd : Odd r := hPodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hx)
    have h1 : c ^ r * (p * c⁻¹ * p⁻¹) ^ r = 1 := by
      rw [← hcd.mul_pow, hr, pow_orderOf_eq_one]
    have hcr : c ^ r ∈ centralizer (F : Set G) := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact hcomm (inv_mem (pow_mem hdF' r))
    have hcop : r.Coprime (orderOf c) :=
      ((Nat.coprime_two_right.mpr hrodd).pow_right m).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one hc2)
    obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
    exact hcZ (hs ▸ pow_mem hcr s)

private structure Rigid (Q : Type) [Group Q] : Prop where
  center_eq_bot : center Q = ⊥
  card_outer_le : Nat.card (ComponentClassification.OuterAutomorphisms.Outer Q) ≤ 2
  core_eq_bot : ∀ s : Q, orderOf s = 2 → pPrimeCore 2 ↥(centralizer ({s} : Set Q)) = ⊥

private theorem center_eq_bot_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact hp IsSimpleGroup.prime_card

private theorem rigid_of_mcl
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.McL) : Rigid Q := by
  have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.McL.isSimpleGroup_McL e
  have hZ : center Q = ⊥ := center_eq_bot_of_simple (by
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

private theorem rigid_of_ly
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.Ly) : Rigid Q := by
  have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.isSimpleGroup_Ly e
  have hZ : center Q = ⊥ := center_eq_bot_of_simple (by
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

private theorem le_centralizer_of_rigid {G : Type} [Group G] [Finite G] {F P : Subgroup G}
    (hF : Rigid ↥F) {β c : G} (hcF : c ∈ F) (hc2 : orderOf c = 2)
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

private theorem eq_bot_of_rigid {G : Type} [Group G] [Finite G] (hO : pPrimeCore 2 G = ⊥)
    {𝓜 : Set (Subgroup G)} (h𝓜 : ∀ F ∈ 𝓜, IsComponent F ∧ Rigid ↥F) {β : G}
    (hβ : β ∈ sSup 𝓜) (hβ2 : β ^ 2 = 1) {P : Subgroup G} (hPodd : Odd (Nat.card P))
    (hPβ : P ≤ centralizer ({β} : Set G))
    (hPn : centralizer ({β} : Set G) ≤ normalizer (P : Set G)) : P = ⊥ := by
  refine eq_bot_of_odd_of_le_centralizer_layer hO (k := 1) (by rwa [pow_one]) hPodd hPβ hPn ?_
  rw [le_centralizer_iff, layer.eq_sSup]
  refine sSup_le fun F (hF : IsComponent F) => le_centralizer_iff.mp ?_
  have hother : ∀ K ∈ 𝓜, K ≠ F → K ≤ centralizer (F : Set G) := fun K hK hKF =>
    commutator_eq_bot_iff_le_centralizer.mp
      ((LocalCores.distinct_components_commute (h𝓜 K hK).1 hF).resolve_left hKF)
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
  ·
    have hF𝓜 : F ∈ 𝓜 := by
      by_contra hn
      exact hβF ((sSup_le fun K hK => hother K hK fun h => hn (h ▸ hK)) hβ)
    have hEF : sSup {K | K ∈ 𝓜 ∧ K ≠ F} ≤ centralizer (F : Set G) :=
      sSup_le fun K hK => hother K hK.1 hK.2
    have hle : sSup 𝓜 ≤ F ⊔ sSup {K | K ∈ 𝓜 ∧ K ≠ F} := sSup_le fun K hK => by
      by_cases h : K = F
      · exact h ▸ le_sup_left
      · exact le_sup_of_le_right (le_sSup ⟨hK, h⟩)
    have hβFE : β ∈ ((F ⊔ sSup {K | K ∈ 𝓜 ∧ K ≠ F} : Subgroup G) : Set G) := hle hβ
    rw [coe_mul_of_left_le_normalizer_right _ _
      ((le_centralizer_iff.mp hEF).trans (centralizer_le_normalizer _))] at hβFE
    obtain ⟨c, hc, e, he, rfl⟩ := hβFE
    have heF : e ∈ centralizer (F : Set G) := hEF he
    have hce : c * e = e * c := mem_centralizer_iff.mp heF c hc
    have hcβ : c ∈ centralizer ({c * e} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * (c * e) = c * (e * c) := by rw [hce]
        _ = c * e * c := by group
    have hc2 : c ^ 2 = 1 := by
      have h1 : c ^ 2 * e ^ 2 = 1 := by
        rw [← (show Commute c e from hce).mul_pow]
        exact hβ2
      have h2 : c ^ 2 ∈ centralizer (F : Set G) := by
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem (pow_mem heF 2)
      have h3 : (⟨c ^ 2, pow_mem hc 2⟩ : F) ∈ center F := by
        rw [mem_center_iff]
        intro f
        exact Subtype.ext (mem_centralizer_iff.mp h2 f f.2)
      rw [(h𝓜 F hF𝓜).2.center_eq_bot, mem_bot] at h3
      exact congrArg Subtype.val h3
    have hcZ : c ∉ centralizer (F : Set G) := fun h => hβF (mul_mem h heF)
    have hc1 : c ≠ 1 := fun h => hcZ (h ▸ one_mem _)
    have hco : orderOf c = 2 := orderOf_eq_prime hc2 hc1
    have hPF : P ≤ normalizer (F : Set G) :=
      le_normalizer_component_of_odd hPodd hPβ hPn hF hc hcβ (m := 1) (by rwa [pow_one]) hcZ
    have hβc : ∀ f ∈ F, c * e * f * (c * e)⁻¹ = c * f * c⁻¹ := by
      intro f hf
      have hef : f * e = e * f := mem_centralizer_iff.mp heF f hf
      calc c * e * f * (c * e)⁻¹ = c * (e * f) * e⁻¹ * c⁻¹ := by group
        _ = c * (f * e) * e⁻¹ * c⁻¹ := by rw [hef]
        _ = c * f * c⁻¹ := by group
    exact le_centralizer_of_rigid (h𝓜 F hF𝓜).2 hc hco hβc hPodd hPβ hPn hPF

private theorem oddCoreOf_inf_cen_le
    {X : Type} [Group X] [Finite X] {C : Subgroup X} {𝓐 : Set (Subgroup X)}
    (h𝓐 : ∀ M ∈ 𝓐, IsPCompIn 2 C M ∧
      (Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.McL) ∨
        Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.Ly)))
    {b : X} (hb : b ∈ sSup 𝓐) (hb2 : b ^ 2 = 1) :
    oddCoreOf (C ⊓ cen b) ≤ oddCoreOf C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbC : b ∈ C := (sSup_le fun M hM => (h𝓐 M hM).1.1) hb
  have hQC : oddCoreOf (C ⊓ cen b) ≤ C := (oddCoreOf_le _).trans inf_le_left
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set b' : ↥C := ⟨b, hbC⟩
  set P := ((oddCoreOf (C ⊓ cen b)).subgroupOf C).map π
  have hPodd : Odd (Nat.card P) := by
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ π)
    rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv]
    exact odd_card_oddCoreOf _
  have hPβ : P ≤ centralizer ({π b'} : Set _) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      ((inf_le_right : C ⊓ cen b ≤ cen b) (oddCoreOf_le _ hq)))
  have hPn : centralizer ({π b'} : Set _) ≤ normalizer (P : Set _) := by
    have hN2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥C) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    have hb'2 : b' ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using hb2)
    have hcent := Semidihedral.Local.map_centralizer_eq_of_coprime 2 (pPrimeCore 2 ↥C) hN2
      (zpowers b') (isPGroup_zpowers_of_pow hb'2)
    rw [← hπ, MonoidHom.map_zpowers, centralizer_zpowers_eq_singleton,
      centralizer_zpowers_eq_singleton] at hcent
    rw [← hcent]
    refine (map_mono ?_).trans (le_normalizer_map π)
    intro z hz
    have hzb : (z : X) ∈ C ⊓ cen b :=
      ⟨z.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mem_centralizer_singleton_iff.mp hz))⟩
    have hzQ := le_normalizer_oddCoreOf (C ⊓ cen b) hzb
    rw [mem_normalizer_iff]
    intro h
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp hzQ h
  set 𝓜 : Set (Subgroup (↥C ⧸ pPrimeCore 2 ↥C)) := {K | ∃ M ∈ 𝓐, (M.subgroupOf C).map π = K}
  have h𝓜 : ∀ K ∈ 𝓜, IsComponent K ∧ Rigid ↥K := by
    rintro K ⟨M, hM, rfl⟩
    obtain ⟨⟨hMC, K', hK', hsub, hmap, -⟩, hty⟩ := h𝓐 M hM
    obtain ⟨e, -⟩ :=
      ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hMC hsub
    rw [← hmap] at hK'
    refine ⟨hK', ?_⟩
    rcases hty with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
    · exact rigid_of_mcl (e.symm.trans eM)
    · exact rigid_of_ly (e.symm.trans eL)
  have hβ : π b' ∈ sSup 𝓜 := by
    have hle : sSup 𝓐 ≤ ((sSup 𝓜).comap π).map C.subtype := sSup_le fun M hM x hx => by
      have hxC : x ∈ C := (h𝓐 M hM).1.1 hx
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      have hK : (M.subgroupOf C).map π ≤ sSup 𝓜 := le_sSup ⟨M, hM, rfl⟩
      exact hK (mem_map_of_mem π (show (⟨x, hxC⟩ : ↥C) ∈ M.subgroupOf C from hx))
    obtain ⟨y, hy, hyb⟩ := hle hb
    have : y = b' := Subtype.ext hyb
    rw [← this]
    exact hy
  have hβ2 : (π b') ^ 2 = 1 := by
    rw [← map_pow, show b' ^ 2 = 1 from Subtype.ext (by simpa using hb2), map_one]
  have hP1 := eq_bot_of_rigid (pPrimeCore_quotient_pPrimeCore_eq_bot 2) h𝓜 hβ hβ2 hPodd hPβ hPn
  intro x hx
  have hxC : x ∈ C := hQC hx
  have hxP : π ⟨x, hxC⟩ ∈ P := mem_map_of_mem π (show (⟨x, hxC⟩ : ↥C) ∈ _ from hx)
  rw [hP1, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxP
  exact ⟨⟨x, hxC⟩, hxP, rfl⟩

theorem sec6_lemmaT
    {X : Type} [Group X] [Finite X] {n : ℕ} {t b : X}
    (hS : Sec6Setting X n t) (hb : b ∈ Sec6M X n (cen t)) (hb2 : orderOf b = 2) :
    oddCoreOf (cen t ⊓ cen b) ≤ oddCoreOf (cen t) :=
  oddCoreOf_inf_cen_le (𝓐 := {M | Sec6MComp X n (cen t) M}) (fun _ hM => ⟨hM.1.1, hM.1.2.1⟩) hb
    (by rw [← hb2, pow_orderOf_eq_one])

end CFSG.OddStandard.Solomon75
