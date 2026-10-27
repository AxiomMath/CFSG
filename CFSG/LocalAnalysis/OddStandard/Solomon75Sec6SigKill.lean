module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Bal
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Restrict
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lemma51B
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Setup
import CFSG.GH74.GLS.SP.Local.SPLCoprime
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.LocalAnalysis.OddStandard.Solomon75T11bLy
import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

private theorem sk_isPGroup_zpowers {G : Type} [Group G] {a : G} {k : ℕ}
    (ha : a ^ (2 ^ k) = 1) : IsPGroup 2 (zpowers a) := fun g => by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    ha, one_zpow, OneMemClass.coe_one]

private theorem sk_centralizer_zpowers {G : Type} [Group G] (a : G) :
    centralizer (zpowers a : Set G) = centralizer ({a} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

private structure SkRigid (Q : Type) [Group Q] : Prop where
  center_eq_bot : center Q = ⊥
  card_outer_le : Nat.card (ComponentClassification.OuterAutomorphisms.Outer Q) ≤ 2
  core_eq_bot : ∀ s : Q, orderOf s = 2 → pPrimeCore 2 ↥(centralizer ({s} : Set Q)) = ⊥

private theorem sk_center_eq_bot_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact hp IsSimpleGroup.prime_card

private theorem sk_rigid_of_mcl
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.McL) : SkRigid Q := by
  have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.McL.isSimpleGroup_McL e
  have hZ : center Q = ⊥ := sk_center_eq_bot_of_simple (by
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

private theorem sk_rigid_of_ly
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.Ly) : SkRigid Q := by
  have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.isSimpleGroup_Ly e
  have hZ : center Q = ⊥ := sk_center_eq_bot_of_simple (by
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

private theorem sk_le_centralizer_of_rigid {G : Type} [Group G] [Finite G] {F P : Subgroup G}
    (hF : SkRigid ↥F) {β c : G} (hcF : c ∈ F) (hc2 : orderOf c = 2)
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

private theorem sk_le_centralizer_of_tstep {G : Type} [Group G] [Finite G] {P F : Subgroup G}
    (hPodd : Odd (Nat.card P)) (hF : IsComponent F) (hPF : P ≤ normalizer (F : Set G))
    {t : G} {O' : Subgroup G} (ht2 : t ^ 2 = 1) (htP : t ∈ normalizer (P : Set G))
    (hPt : P ⊓ centralizer ({t} : Set G) ≤ O') (hO'odd : Odd (Nat.card O'))
    (htF : t ∈ centralizer (F : Set G)) (hFO' : F ≤ normalizer (O' : Set G))
    {c : G} (hcF : c ∈ F) (hc1 : c ≠ 1) {m : ℕ} (hcm : c ^ (2 ^ m) = 1) :
    P ≤ centralizer (F : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : ¬ 2 ∣ Nat.card P := fun h => (Nat.not_even_iff_odd.mpr hPodd) (even_iff_two_dvd.mpr h)
  have hcop := CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.le_commutator_sup_inf_centralizer
    Nat.prime_two (P := zpowers t) (R := P) (sk_isPGroup_zpowers (k := 1) (by rwa [pow_one]))
    (zpowers_le.mpr htP) hP2
  rw [sk_centralizer_zpowers] at hcop
  refine hcop.trans (sup_le ?_ ?_)
  ·
    rw [commutator_le]
    intro p hp a ha
    have haF : a ∈ centralizer (F : Set G) := (zpowers_le.mpr htF) ha
    rw [mem_centralizer_iff]
    intro f hf
    have hf' : p⁻¹ * f * p ∈ F := by
      have := (mem_normalizer_iff.mp (inv_mem (hPF hp)) f).mp hf
      rwa [inv_inv] at this
    have h1 : (p⁻¹ * f * p) * a = a * (p⁻¹ * f * p) := (mem_centralizer_iff.mp haF) _ hf'
    have h2 : f * a⁻¹ = a⁻¹ * f := (mem_centralizer_iff.mp (inv_mem haF)) f hf
    calc f * ⁅p, a⁆ = p * ((p⁻¹ * f * p) * a) * p⁻¹ * a⁻¹ := by
          rw [commutatorElement_def]; group
      _ = p * (a * (p⁻¹ * f * p)) * p⁻¹ * a⁻¹ := by rw [h1]
      _ = p * a * p⁻¹ * (f * a⁻¹) := by group
      _ = p * a * p⁻¹ * (a⁻¹ * f) := by rw [h2]
      _ = ⁅p, a⁆ * f := by rw [commutatorElement_def]; group
  ·
    intro q hq
    have hqO : q ∈ O' := hPt hq
    have hqF : q ∈ normalizer (F : Set G) := hPF hq.1
    have hN : (O'.subgroupOf F).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simpa using (mem_normalizer_iff.mp (hFO' g.2) n).mp hn⟩
    have hcen : O'.subgroupOf F ≤ center ↥F := by
      rcases LocalCores.quasisimple_normal_subgroups hF.1 hN with htop | hle
      · exfalso
        have hcO : c ∈ O' := by
          have : (⟨c, hcF⟩ : ↥F) ∈ O'.subgroupOf F := by rw [htop]; exact mem_top _
          exact mem_subgroupOf.mp this
        have h1 : orderOf c ∣ Nat.card O' := Subgroup.orderOf_dvd_natCard O' hcO
        have h2 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hcm
        have h3 : orderOf c = 1 := by
          obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
          rcases j with _ | j
          · simpa using hj
          · exfalso
            rw [hj] at h1
            exact (Nat.not_even_iff_odd.mpr hO'odd)
              (even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h1))
        exact hc1 (orderOf_eq_one_iff.mp h3)
      · exact hle
    have hqf : ∀ f ∈ F, q * f * q⁻¹ * f⁻¹ ∈ F ∧ ∀ g ∈ F, g * (q * f * q⁻¹ * f⁻¹) =
        (q * f * q⁻¹ * f⁻¹) * g := by
      intro f hf
      have hmF : q * f * q⁻¹ * f⁻¹ ∈ F :=
        F.mul_mem ((mem_normalizer_iff.mp hqF f).mp hf) (F.inv_mem hf)
      have hmO : q * f * q⁻¹ * f⁻¹ ∈ O' := by
        have h1 : f * q⁻¹ * f⁻¹ ∈ O' := (mem_normalizer_iff.mp (hFO' hf) _).mp (O'.inv_mem hqO)
        have : q * f * q⁻¹ * f⁻¹ = q * (f * q⁻¹ * f⁻¹) := by group
        rw [this]
        exact O'.mul_mem hqO h1
      refine ⟨hmF, fun g hg => ?_⟩
      have hz : (⟨_, hmF⟩ : ↥F) ∈ center ↥F :=
        hcen (show (⟨_, hmF⟩ : ↥F) ∈ O'.subgroupOf F from hmO)
      exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨g, hg⟩)
    have hperf : ⁅F, F⁆ = F := Subgroup.isPerfect_iff.mp hF.1.1
    have hfix : ⁅F, F⁆ ≤ centralizer ({q} : Set G) := by
      rw [commutator_le]
      intro f hf g hg
      obtain ⟨hfF, hfz⟩ := hqf f hf
      obtain ⟨hgF, hgz⟩ := hqf g hg
      have e1 : q * f * q⁻¹ = (q * f * q⁻¹ * f⁻¹) * f := by group
      have e2 : q * g * q⁻¹ = (q * g * q⁻¹ * g⁻¹) * g := by group
      generalize q * f * q⁻¹ * f⁻¹ = z₁ at hfF hfz e1
      generalize q * g * q⁻¹ * g⁻¹ = z₂ at hgF hgz e2
      have k1 : Commute z₁ f := (hfz f hf).symm
      have k2 : Commute z₁ g := (hfz g hg).symm
      have k3 : Commute z₁ z₂ := (hfz z₂ hgF).symm
      have k4 : Commute z₂ f := (hgz f hf).symm
      have k5 : Commute z₂ g := (hgz g hg).symm
      have hconj : q * ⁅f, g⁆ * q⁻¹ = ⁅f, g⁆ := by
        have h0 : q * ⁅f, g⁆ * q⁻¹ = (q * f * q⁻¹) * (q * g * q⁻¹) * (q * f * q⁻¹)⁻¹ *
            (q * g * q⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        rw [h0, e1, e2, commutatorElement_def]
        calc z₁ * f * (z₂ * g) * (z₁ * f)⁻¹ * (z₂ * g)⁻¹
            = z₁ * (f * z₂ * g * f⁻¹) * z₁⁻¹ * g⁻¹ * z₂⁻¹ := by group
          _ = (f * z₂ * g * f⁻¹) * z₁ * z₁⁻¹ * g⁻¹ * z₂⁻¹ := by
            rw [(((k1.mul_right k3).mul_right k2).mul_right k1.inv_right).eq]
          _ = f * (z₂ * (g * f⁻¹ * g⁻¹)) * z₂⁻¹ := by group
          _ = f * ((g * f⁻¹ * g⁻¹) * z₂) * z₂⁻¹ := by
            rw [((k5.mul_right k4.inv_right).mul_right k5.inv_right).eq]
          _ = f * g * f⁻¹ * g⁻¹ := by group
      rw [mem_centralizer_singleton_iff]
      calc ⁅f, g⁆ * q = q * ⁅f, g⁆ * q⁻¹ * q := by rw [hconj]
        _ = q * ⁅f, g⁆ := by group
    rw [mem_centralizer_iff]
    intro f hf
    have hf' : f ∈ ⁅F, F⁆ := by rw [hperf]; exact hf
    exact mem_centralizer_singleton_iff.mp (hfix hf')

private theorem sk_dec {G : Type} [Group G] [Finite G] {𝓕 : Set (Subgroup G)}
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

private theorem sk_le_centralizer_component {G : Type} [Group G] [Finite G]
    (hO : pPrimeCore 2 G = ⊥) {β : G} (hβ2 : β ^ 2 = 1) {P : Subgroup G}
    (hPodd : Odd (Nat.card P)) (hPβ : P ≤ centralizer ({β} : Set G))
    (hPn : centralizer ({β} : Set G) ≤ normalizer (P : Set G)) {F : Subgroup G}
    (hF : IsComponent F) (hβF : β ∉ centralizer (F : Set G)) {c w : G} (hcF : c ∈ F)
    (hw : w ∈ centralizer (F : Set G)) (hβcw : β = c * w)
    (hbr : SkRigid ↥F ∨ ∃ (t : G) (O' : Subgroup G), t ^ 2 = 1 ∧
      t ∈ normalizer (P : Set G) ∧ P ⊓ centralizer ({t} : Set G) ≤ O' ∧ Odd (Nat.card O') ∧
      t ∈ centralizer (F : Set G) ∧ F ≤ normalizer (O' : Set G)) :
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
  rcases hbr with hR | ⟨t, O', ht2, htP, hPt, hO'odd, htF, hFO'⟩
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
    exact sk_le_centralizer_of_rigid hR hcF hco hβc hPodd hPβ hPn hPF
  · exact sk_le_centralizer_of_tstep hPodd hF hPF ht2 htP hPt hO'odd htF hFO' hcF hc1 hck

private theorem sk_eq_bot {G : Type} [Group G] [Finite G] (hO : pPrimeCore 2 G = ⊥) {β : G}
    (hβ2 : β ^ 2 = 1) {P : Subgroup G} (hPodd : Odd (Nat.card P))
    (hPβ : P ≤ centralizer ({β} : Set G))
    (hPn : centralizer ({β} : Set G) ≤ normalizer (P : Set G))
    (hloc : ∀ F : Subgroup G, IsComponent F → β ∉ centralizer (F : Set G) →
      ∃ c ∈ F, ∃ w ∈ centralizer (F : Set G), β = c * w ∧
        (SkRigid ↥F ∨ ∃ (t : G) (O' : Subgroup G), t ^ 2 = 1 ∧
          t ∈ normalizer (P : Set G) ∧ P ⊓ centralizer ({t} : Set G) ≤ O' ∧
          Odd (Nat.card O') ∧ t ∈ centralizer (F : Set G) ∧ F ≤ normalizer (O' : Set G))) :
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
    exact sk_le_centralizer_component hO hβ2 hPodd hPβ hPn hF hβF hcF hw hβcw hbr

private theorem sk_sec6Base_le {X : Type} [Group X] {n : ℕ} {t : X} :
    Sec6Base X n t ≤ cen t :=
  sup_le (sSup_le fun _ hM => hM.1.1.1) (inf_le_left.trans (sSup_le fun _ hA => by
    obtain ⟨⟨u, hu⟩, -⟩ := hA
    exact hu.2.2.1.1))

private theorem sk_core_K0_le {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} :
    pPrimeCoreOf 2 (K0 X n (cen t)) ≤ oddCoreOf (cen t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : K0 X n (cen t) ≤ cen t := sSup_le fun _ hA => by
    obtain ⟨⟨u, hu⟩, -⟩ := hA
    exact hu.2.2.1.1
  exact CFSG.GH74.GLS.pPrimeCoreOf_le_of_normal 2 hle
    ((normal_subgroupOf_iff_le_normalizer hle).mpr (K0_cen_normal n t))

private theorem sk_lemmaT
    {X : Type} [Group X] [Finite X] {n : ℕ} {t x : X}
    (hx : x ∈ Sec6Base X n t) (hx2 : x ^ 2 = 1) :
    oddCoreOf (cen t ⊓ cen x) ≤ oddCoreOf (cen t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxC : x ∈ cen t := sk_sec6Base_le hx
  have hAC : K0 X n (cen t) ≤ cen t := sSup_le fun _ hA => by
    obtain ⟨⟨u, hu⟩, -⟩ := hA
    exact hu.2.2.1.1
  have hZC : zStar (K0 X n (cen t)) ≤ cen t := inf_le_left.trans hAC
  have hx' : x ∈ ((zStar (K0 X n (cen t)) ⊔ Sec6M X n (cen t) : Subgroup X) : Set X) := by
    rw [sup_comm]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right _ _ (hZC.trans (Sec6M_cen_normal n t))] at hx'
  obtain ⟨z, hz, m, hm, hxzm⟩ := hx'
  set C : Subgroup X := cen t with hCdef
  have hMC : Sec6M X n C ≤ C := sSup_le fun _ hM => hM.1.1.1
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
      (zpowers x') (sk_isPGroup_zpowers hx'2)
    rw [← hπ, MonoidHom.map_zpowers, sk_centralizer_zpowers, sk_centralizer_zpowers] at hcent
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
  have h𝓜 : ∀ K ∈ 𝓜, IsComponent K ∧ SkRigid ↥K := by
    rintro K ⟨M, hM, rfl⟩
    obtain ⟨⟨⟨hMC, K', hK', hsub, hmap, -⟩, hty, -⟩, -⟩ := hM
    obtain ⟨e, -⟩ :=
      ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hMC hsub
    rw [← hmap] at hK'
    refine ⟨hK', ?_⟩
    rcases hty with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
    · exact sk_rigid_of_mcl (e.symm.trans eM)
    · exact sk_rigid_of_ly (e.symm.trans eL)
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
      π ⟨z, hzC⟩ ∈ centralizer (F : Set _) := by
    intro F hF
    by_cases hFA : ∃ A, Sec5Comp X n C A ∧ (A.subgroupOf C).map π = F
    · obtain ⟨A, hA, rfl⟩ := hFA
      have hAK : A ≤ K0 X n C := le_sSup hA
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      have hcomm : ⁅(a : X), z⁆ ∈ oddCoreOf C :=
        sk_core_K0_le (hz.2.2.2 _ (hAK (show (a : X) ∈ A from ha)))
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
  have hπx : π x' = π ⟨z, hzC⟩ * π ⟨m, hmC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hxzm.symm
  have hβ2 : (π x') ^ 2 = 1 := by
    rw [← map_pow, show x' ^ 2 = 1 from Subtype.ext (by simpa using hx2), map_one]
  have hP1 : P = ⊥ := by
    refine sk_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hβ2 hPodd hPβ hPn ?_
    intro F hF hβF
    rcases sk_dec (fun K hK => (h𝓜 K hK).1) hπm hF with hmF | ⟨hF𝓜, c, hcF, w, hw, hmcw⟩
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

private theorem sk_kcomp_pc {X : Type} [Group X] {n : ℕ} {H L : Subgroup X}
    (h : Sec6KComp X n H L) : IsPCompIn 2 H L := by
  rcases h with ⟨⟨u, hu⟩, -⟩ | hM
  · exact hu.2.2.1
  · exact hM.1.1

private theorem sk_core_le_of_pc {X : Type} [Group X] [Finite X] {H J : Subgroup X}
    (hJ : IsPCompIn 2 H J) : pPrimeCoreOf 2 J ≤ oddCoreOf H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hsub, -⟩ := hJ.2
  have h1 := CFSG.GH74.GLS.pPrimeCoreOf_le_of_subnormal 2 hsub
  have hid : pPrimeCoreOf 2 J = (pPrimeCoreOf 2 (J.subgroupOf H)).map H.subtype := by
    let e : ↥(J.subgroupOf H) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJ.1
    unfold pPrimeCoreOf
    rw [Subgroup.map_map, ← pPrimeCore_map_iso 2 e, Subgroup.map_map]
    rfl
  rw [hid]
  exact Subgroup.map_mono h1

private theorem sk_distinct {X : Type} [Group X] [Finite X] {H L L' : Subgroup X}
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
    Sec6L51B.mem_normalizer_of_mem_normalizer_subgroupOf hL.1 (c := ⟨y, hyH⟩)
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

private theorem sk_mem_normalizer_sSup {X : Type} [Group X] {S : Set (Subgroup X)} {c : X}
    (h : ∀ L ∈ S, c ∈ normalizer (L : Set X)) : c ∈ normalizer ((sSup S : Subgroup X) : Set X) := by
  have key : ∀ d : X, (∀ L ∈ S, d ∈ normalizer (L : Set X)) → ∀ g ∈ sSup S,
      d * g * d⁻¹ ∈ sSup S := by
    intro d hd g hg
    have hle : sSup S ≤ (sSup S).comap (MulAut.conj d).toMonoidHom := sSup_le fun L hL l hl => by
      rw [mem_comap]
      exact le_sSup hL ((mem_normalizer_iff.mp (hd L hL) l).mp hl)
    exact hle hg
  rw [mem_normalizer_iff]
  intro g
  refine ⟨key c h g, fun hg => ?_⟩
  have := key c⁻¹ (fun L hL => inv_mem (h L hL)) _ hg
  rwa [show c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g by group] at this

private theorem sk_mem_core_of_central
    {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hty : Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.Ly))
    {y : X} (hyL : y ∈ L) (hy : ∀ k ∈ L, ⁅k, y⁆ ∈ pPrimeCoreOf 2 L) : y ∈ pPrimeCoreOf 2 L := by
  have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := by
    rcases hty with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact (sk_rigid_of_mcl e).center_eq_bot
    · exact (sk_rigid_of_ly e).center_eq_bot
  have hmem : (QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨y, hyL⟩ : ↥L ⧸ pPrimeCore 2 ↥L) ∈
      center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
    obtain ⟨w, hw, hweq⟩ := hy k k.2
    have hw' : w = ⁅k, ⟨y, hyL⟩⁆ := Subtype.ext (by simpa [commutatorElement_def] using hweq)
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⁅k, ⟨y, hyL⟩⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hw']
      exact hw
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

private theorem sk_lift {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) {a : G} {j : ℕ} (ha : a ^ (2 ^ j) = 1) {g : G} (hg2 : g ^ 2 ∈ N)
    (hga : ⁅g, a⁆ ∈ N) : ∃ d : G, d ^ 2 = 1 ∧ d * a = a * d ∧ g⁻¹ * d ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : ¬ 2 ∣ Nat.card N := fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  have hcent := Semidihedral.Local.map_centralizer_eq_of_coprime 2 N hN2 (zpowers a)
    (sk_isPGroup_zpowers ha)
  rw [MonoidHom.map_zpowers, sk_centralizer_zpowers, sk_centralizer_zpowers] at hcent
  have hgc : QuotientGroup.mk' N g ∈ centralizer ({QuotientGroup.mk' N a} : Set (G ⧸ N)) := by
    have h1 : QuotientGroup.mk' N ⁅g, a⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hga
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact mem_centralizer_singleton_iff.mpr h1
  rw [← hcent] at hgc
  obtain ⟨c, hc, hcg⟩ := hgc
  have hca : c * a = a * c := mem_centralizer_singleton_iff.mp hc
  have hc2 : c ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have h1 : (QuotientGroup.mk c : G ⧸ N) = QuotientGroup.mk g := hcg
    rw [h1, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hg2
  refine ⟨c ^ Nat.card N, ?_, ?_, ?_⟩
  · have h1 : (⟨c ^ 2, hc2⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [← pow_mul, mul_comm, pow_mul]
    exact h2
  · exact ((Commute.pow_left hca (Nat.card N)))
  · rw [← QuotientGroup.eq]
    have h1 : (QuotientGroup.mk c : G ⧸ N) = QuotientGroup.mk g := hcg
    have hg2' : (QuotientGroup.mk g : G ⧸ N) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hg2
    obtain ⟨k, hk⟩ := hN
    rw [QuotientGroup.mk_pow, h1, hk, pow_succ, pow_mul, hg2', one_pow, one_mul]

private theorem sk_split
    {X : Type} [Group X] [Finite X] {n : ℕ} {t x : X} {L0 : Subgroup X}
    (hL0 : Sec6MComp X n (cen t) L0) (hx : x ∈ Sec6Base X n t) (hx2 : x ^ 2 = 1) :
    ∃ k ℓ : X, x = k * ℓ ∧ ℓ ∈ L0 ∧ ℓ ^ 2 ∈ pPrimeCoreOf 2 L0 ∧
      k ∈ sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} ∧
      sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} ≤ centralizerSection L0 (pPrimeCoreOf 2 L0) ∧
      ∀ c ∈ L0, c ∈ normalizer ((sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} : Subgroup X) :
        Set X) := by
  have hL0pc : IsPCompIn 2 (cen t) L0 := hL0.1.1
  have hK'CS : sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} ≤
      centralizerSection L0 (pPrimeCoreOf 2 L0) :=
    sSup_le fun L hL => sk_distinct hL0pc (sk_kcomp_pc hL.1) (Ne.symm hL.2)
  have hL0N : ∀ c ∈ L0, c ∈ normalizer ((sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} :
      Subgroup X) : Set X) := fun c hc =>
    sk_mem_normalizer_sSup fun L hL => (sk_distinct (sk_kcomp_pc hL.1) hL0pc hL.2 hc).1
  have hxK : x ∈ Sec6K X n (cen t) := by
    rw [sec6K_eq]
    have hle : Sec6Base X n t ≤ K0 X n (cen t) ⊔ Sec6M X n (cen t) :=
      sup_le le_sup_right (inf_le_left.trans le_sup_left)
    exact hle hx
  have hKle : Sec6K X n (cen t) ≤ sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} ⊔ L0 :=
    sSup_le fun L hL => by
      by_cases h : L = L0
      · exact h ▸ le_sup_right
      · exact le_sup_of_le_left (le_sSup ⟨hL, h⟩)
  have hx' : x ∈ ((sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} ⊔ L0 : Subgroup X) : Set X) :=
    hKle hxK
  rw [coe_mul_of_left_le_normalizer_right _ _ (hK'CS.trans fun c hc => hc.1)] at hx'
  obtain ⟨k, hk, ℓ, hℓ, hxkl⟩ := hx'
  have hxkl' : x = k * ℓ := hxkl.symm
  refine ⟨k, ℓ, hxkl', hℓ, ?_, hk, hK'CS, hL0N⟩
  have hℓK : ℓ ^ 2 ∈ sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} := by
    have h1 : k * (ℓ * k * ℓ⁻¹) * ℓ ^ 2 = 1 := by
      rw [← hx2, hxkl', pow_two, pow_two]
      group
    have h2 : ℓ ^ 2 = (k * (ℓ * k * ℓ⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_mem (mul_mem hk ((mem_normalizer_iff.mp (hL0N ℓ hℓ) k).mp hk))
  exact sk_mem_core_of_central hL0.1.2.1 (pow_mem hℓ 2) (hK'CS hℓK).2.2

private theorem sk_loc
    {X : Type} [Group X] [Finite X] {n : ℕ} {t e x : X} {L0 : Subgroup X}
    (hL0 : Sec6MComp X n (cen t) L0) (he : e ∈ L0) (he2 : e ^ 2 = 1)
    (hx : x ∈ Sec6Base X n t) (hx2 : x ^ 2 = 1) (hxe : x * e = e * x) :
    x ∈ (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ⊔
      (oddCoreOf (cen t) ⊓ cen e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, ℓ, hxkl, hℓ, hℓ2, hk, hK'CS, -⟩ := sk_split hL0 hx hx2
  have hL0pc : IsPCompIn 2 (cen t) L0 := hL0.1.1
  have hpiece_le : ∀ L, Sec6KComp X n (cen t) L →
      sec6Piece L e ≤ ⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e :=
    fun L hL => le_iSup₂_of_le L hL le_rfl
  have hYC : (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ≤ cen t :=
    iSup₂_le fun L hL => (oTwoPrimeOf_le _).trans (inf_le_left.trans (sk_kcomp_pc hL).1)
  have hYe : (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ≤ cen e :=
    iSup₂_le fun L _ => (oTwoPrimeOf_le _).trans inf_le_right
  have hK'W : sSup {L | Sec6KComp X n (cen t) L ∧ L ≠ L0} ≤
      (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ⊔ oddCoreOf (cen t) :=
    sSup_le fun L hL => by
      have hLpc := sk_kcomp_pc hL.1
      have heL : e ∈ centralizerSection L (pPrimeCoreOf 2 L) := sk_distinct hLpc hL0pc hL.2 he
      obtain ⟨-, hcov⟩ := isPCompIn_restrict hLpc he2 heL
      have hcov' := (covers_subgroupOf_iff ((oTwoPrimeOf_le _).trans inf_le_left)).mp hcov
      rw [← hcov']
      exact sup_le_sup (hpiece_le L hL.1) (sk_core_le_of_pc hLpc)
  have hℓW : ℓ ∈ (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ⊔
      oddCoreOf (cen t) := by
    have hcomm : ⁅ℓ, e⁆ ∈ pPrimeCoreOf 2 L0 := by
      have h1 : ℓ * e * ℓ⁻¹ = k⁻¹ * e * k := by
        have h0 : k * ℓ * e = e * (k * ℓ) := by rw [← hxkl]; exact hxe
        calc ℓ * e * ℓ⁻¹ = k⁻¹ * (k * ℓ * e) * ℓ⁻¹ := by group
          _ = k⁻¹ * (e * (k * ℓ)) * ℓ⁻¹ := by rw [h0]
          _ = k⁻¹ * e * k := by group
      have h2 : ⁅e, k⁻¹⁆ ∈ pPrimeCoreOf 2 L0 := (hK'CS (inv_mem hk)).2.2 e he
      have h3 : ⁅ℓ, e⁆ = ⁅e, k⁻¹⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def, h1]
        group
      rw [h3]
      exact inv_mem h2
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥L0)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have he'2 : (⟨e, he⟩ : ↥L0) ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using he2)
    have hℓ2' : (⟨ℓ, hℓ⟩ : ↥L0) ^ 2 ∈ pPrimeCore 2 ↥L0 := by
      obtain ⟨w, hw, hweq⟩ := hℓ2
      have : w = (⟨ℓ, hℓ⟩ : ↥L0) ^ 2 := Subtype.ext (by simpa using hweq)
      rw [← this]
      exact hw
    have hcomm' : ⁅(⟨ℓ, hℓ⟩ : ↥L0), ⟨e, he⟩⁆ ∈ pPrimeCore 2 ↥L0 := by
      obtain ⟨w, hw, hweq⟩ := hcomm
      have : w = ⁅(⟨ℓ, hℓ⟩ : ↥L0), ⟨e, he⟩⁆ :=
        Subtype.ext (by simpa [commutatorElement_def] using hweq)
      rw [← this]
      exact hw
    obtain ⟨d, hd2, hde, hdℓ⟩ := sk_lift hodd he'2 hℓ2' hcomm'
    have hdP : (d : X) ∈ sec6Piece L0 e := by
      refine mem_oTwoPrimeOf ⟨d.2, ?_⟩ 1 (by simpa using congrArg Subtype.val hd2)
      exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hde)
    have hdO : (d : X)⁻¹ * ℓ ∈ oddCoreOf (cen t) := by
      have h1 : ((⟨ℓ, hℓ⟩ : ↥L0)⁻¹ * d)⁻¹ ∈ pPrimeCore 2 ↥L0 := inv_mem hdℓ
      have h2 : (d : X)⁻¹ * ℓ ∈ pPrimeCoreOf 2 L0 :=
        ⟨_, h1, by simp⟩
      exact sk_core_le_of_pc hL0pc h2
    have : ℓ = (d : X) * ((d : X)⁻¹ * ℓ) := by group
    rw [this]
    exact mul_mem (mem_sup_left (hpiece_le L0 (Or.inr hL0) hdP)) (mem_sup_right hdO)
  have hxW : x ∈ (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ⊔
      oddCoreOf (cen t) := hxkl ▸ mul_mem (hK'W hk) hℓW
  have hYN : (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ≤
      normalizer (oddCoreOf (cen t) : Set X) := hYC.trans (le_normalizer_oddCoreOf (cen t))
  have hxW' : x ∈ (((⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ⊔
      oddCoreOf (cen t) : Subgroup X) : Set X) := hxW
  rw [coe_mul_of_left_le_normalizer_right _ _ hYN] at hxW'
  obtain ⟨y, hy, o, ho, hyo⟩ := hxW'
  have hyo' : x = y * o := hyo.symm
  have hoe : o ∈ cen e := by
    have h1 : o = y⁻¹ * x := by rw [hyo']; group
    rw [h1]
    exact mul_mem (inv_mem (hYe hy)) (mem_centralizer_singleton_iff.mpr hxe)
  rw [hyo']
  exact mul_mem (mem_sup_left hy) (mem_sup_right ⟨ho, hoe⟩)

private theorem sk_isComponent_of_pc {G : Type} [Group G] [Finite G] (hO : pPrimeCore 2 G = ⊥)
    {L : Subgroup G} (hL : IsPComponent 2 L) : IsComponent L := by
  obtain ⟨K, hK, -, hmap, -⟩ := hL
  let e : G ⧸ pPrimeCore 2 G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 G)) = MonoidHom.id G := by
    ext g
    rfl
  have he : K.map e.toMonoidHom = L := by
    rw [← hmap, Subgroup.map_map, hcomp, Subgroup.map_id]
  rw [← he]
  exact LocalCores.isComponent_map_mulEquiv e hK

private theorem sk_core
    {X : Type} [Group X] [Finite X] {n : ℕ} {t e a : X} (ht2 : t ^ 2 = 1)
    (hC : Sec6CtrlAt X n t) (he : e ∈ Sec6M X n (cen t)) (he2 : orderOf e = 2)
    (h0e : oddCoreOf (cen e) = ⊥) (haB : a ∈ Sec6Base X n t) (ha2 : a ^ 2 = 1)
    (haY : a ∈ ⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) :
    oddCoreOf (cen a) ⊓ cen e = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 ↥(cen e) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (cen e).subtype_injective).mp h0e
  have hYe : (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ≤ cen e :=
    iSup₂_le fun L _ => (oTwoPrimeOf_le _).trans inf_le_right
  have haC : a ∈ cen e := hYe haY
  have heM : e ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := mem_sup_left he
  have heC : e ∈ cen t := (sSup_le fun _ hM => hM.1.1.1 : Sec6M X n (cen t) ≤ cen t) he
  have htC : t ∈ cen e :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp heC).symm
  have hta : t ∈ cen a :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (sk_sec6Base_le haB)).symm
  set β : ↥(cen e) := ⟨a, haC⟩ with hβdef
  have hβ2 : β ^ 2 = 1 := Subtype.ext (by simpa using ha2)
  set P : Subgroup ↥(cen e) := (oddCoreOf (cen a) ⊓ cen e).subgroupOf (cen e) with hPdef
  have hPodd : Odd (Nat.card P) := by
    rw [hPdef, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : oddCoreOf (cen a) ⊓ cen e ≤
      cen e)).toEquiv]
    exact (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hPβ : P ≤ centralizer ({β} : Set ↥(cen e)) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (oddCoreOf_le _ (mem_subgroupOf.mp hp).1))
  have hconj : ∀ g : ↥(cen e), (g : X) ∈ normalizer ((oddCoreOf (cen a) ⊓ cen e : Subgroup X) :
      Set X) → g ∈ normalizer (P : Set ↥(cen e)) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro p
    rw [hPdef, mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp hg p
  have hPn : centralizer ({β} : Set ↥(cen e)) ≤ normalizer (P : Set ↥(cen e)) := by
    intro g hg
    apply hconj
    have hga : (g : X) ∈ cen a :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg))
    exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hga) (le_normalizer g.2)
  set 𝓕 : Set (Subgroup ↥(cen e)) := {F' | ∃ F, Sec6KComp X n (cen e) F ∧
    (∃ L, Sec6KComp X n (cen t) L ∧ sec6Piece L e ≤ F) ∧ F.subgroupOf (cen e) = F'}
  have h𝓕 : ∀ F' ∈ 𝓕, IsComponent F' := by
    rintro _ ⟨F, hF, -, rfl⟩
    exact sk_isComponent_of_pc hO (sk_kcomp_pc hF).2
  have hβ𝓕 : β ∈ sSup 𝓕 := by
    have hle : (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ≤
        (sSup 𝓕).map (cen e).subtype := iSup₂_le fun L hL y hy => by
      obtain ⟨F, hF, hLF⟩ := hC.land e heM he2 L hL
      have hye : y ∈ cen e := ((oTwoPrimeOf_le _).trans inf_le_right) hy
      refine ⟨⟨y, hye⟩, ?_, rfl⟩
      have hF𝓕 : F.subgroupOf (cen e) ∈ 𝓕 := ⟨F, hF, ⟨L, hL, hLF⟩, rfl⟩
      exact (le_sSup hF𝓕 : F.subgroupOf (cen e) ≤ sSup 𝓕)
        (show (⟨y, hye⟩ : ↥(cen e)) ∈ F.subgroupOf (cen e) from hLF hy)
    obtain ⟨y, hy, hya⟩ := hle haY
    have : y = β := Subtype.ext hya
    rw [← this]
    exact hy
  have hP1 : P = ⊥ := by
    refine sk_eq_bot hO hβ2 hPodd hPβ hPn ?_
    intro F hF hβF
    rcases sk_dec h𝓕 hβ𝓕 hF with h | ⟨hF𝓕, c, hcF, w, hw, hβcw⟩
    · exact absurd h hβF
    refine ⟨c, hcF, w, hw, hβcw, ?_⟩
    obtain ⟨F₀, hF₀, ⟨L, hL, hLF⟩, rfl⟩ := hF𝓕
    have hO₀ : pPrimeCoreOf 2 F₀ = ⊥ := le_bot_iff.mp (h0e ▸ sk_core_le_of_pc (sk_kcomp_pc hF₀))
    obtain ⟨-, hdich⟩ := hC.dich e heM he2 L F₀ hL hF₀ hLF
    rcases hdich with hF₀eq | ⟨hM, -, -⟩
    ·
      right
      have hF₀t : F₀ ≤ cen t := by
        have h1 : F₀ = sec6Piece L e := by
          rw [hF₀eq]
          exact (show oddCoreOf F₀ = ⊥ from hO₀) ▸ bot_sup_eq _
        rw [h1]
        exact (oTwoPrimeOf_le _).trans (inf_le_left.trans (sk_kcomp_pc hL).1)
      refine ⟨⟨t, htC⟩, (oddCoreOf (cen t) ⊓ cen e).subgroupOf (cen e),
        Subtype.ext (by simpa using ht2), ?_, ?_, ?_, ?_, ?_⟩
      · exact hconj _ (mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hta)
          (le_normalizer htC))
      · rintro p ⟨hp, hpt⟩
        have hpt' : (p : X) ∈ cen t :=
          mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            (mem_centralizer_singleton_iff.mp hpt))
        have hp' := mem_subgroupOf.mp hp
        have h1 : (p : X) ∈ oddCoreOf (cen t ⊓ cen a) := by
          refine le_oddCoreOf_of_normalized (H := cen t ⊓ cen a) (N := oddCoreOf (cen a) ⊓ cen t)
            (fun y hy => mem_inf.mpr ⟨hy.2, oddCoreOf_le _ hy.1⟩) ?_ ?_ ⟨hp'.1, hpt'⟩
          · intro y hy
            exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hy.2) (le_normalizer hy.1)
          · exact (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
        exact mem_subgroupOf.mpr ⟨sk_lemmaT haB ha2 h1, p.2⟩
      · rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : oddCoreOf (cen t) ⊓ cen e ≤
          cen e)).toEquiv]
        exact (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
      · rw [mem_centralizer_iff]
        intro f hf
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (hF₀t (mem_subgroupOf.mp hf)))
      · intro f hf
        have hf' : (f : X) ∈ F₀ := mem_subgroupOf.mp hf
        rw [mem_normalizer_iff]
        intro p
        rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
        exact mem_normalizer_iff.mp (mem_normalizer_inf (le_normalizer_oddCoreOf (cen t)
          (hF₀t hf')) (le_normalizer f.2)) p
    ·
      left
      have hO₀' : pPrimeCore 2 ↥F₀ = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ F₀.subtype_injective).mp hO₀
      let e₁ : ↥(F₀.subgroupOf (cen e)) ≃* ↥F₀ ⧸ pPrimeCore 2 ↥F₀ :=
        (Subgroup.subgroupOfEquivOfLe (sk_kcomp_pc hF₀).1).trans
          (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO₀'.symm))
      rcases hM.1.2.1 with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
      · exact sk_rigid_of_mcl (e₁.trans eM)
      · exact sk_rigid_of_ly (e₁.trans eL)
  rw [eq_bot_iff]
  intro y hy
  have hyP : (⟨y, hy.2⟩ : ↥(cen e)) ∈ P := mem_subgroupOf.mpr hy
  rw [hP1, mem_bot] at hyP
  rw [mem_bot]
  exact congrArg Subtype.val hyP

private theorem sk_lift_X {X : Type} [Group X] [Finite X] {H N : Subgroup X} (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set X)) (hN : Odd (Nat.card N)) {a g : X} (haH : a ∈ H)
    {j : ℕ} (ha : a ^ (2 ^ j) = 1) (hgH : g ∈ H) (hg2 : g ^ 2 ∈ N) (hga : ⁅g, a⁆ ∈ N) :
    ∃ d ∈ H, d ^ 2 = 1 ∧ d * a = a * d ∧ g⁻¹ * d ∈ N := by
  have hNn : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hN' : Odd (Nat.card (N.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]
    exact hN
  obtain ⟨d, hd2, hda, hdg⟩ := sk_lift (N := N.subgroupOf H) hN' (a := ⟨a, haH⟩) (j := j)
    (Subtype.ext (by simpa using ha)) (g := ⟨g, hgH⟩) (mem_subgroupOf.mpr (by simpa using hg2))
    (mem_subgroupOf.mpr (by simpa [commutatorElement_def] using hga))
  refine ⟨d, d.2, by simpa using congrArg Subtype.val hd2, by simpa using congrArg Subtype.val hda,
    by simpa using mem_subgroupOf.mp hdg⟩

private theorem sk_four
    {X : Type} [Group X] [Finite X] {n : ℕ} {t x : X} {L0 : Subgroup X}
    (hL0 : Sec6MComp X n (cen t) L0) (hx : x ∈ Sec6Base X n t) (hx2 : x ^ 2 = 1) :
    ∃ e₁ e₂ : X, e₁ ∈ L0 ∧ e₂ ∈ L0 ∧ orderOf e₁ = 2 ∧ orderOf e₂ = 2 ∧ e₁ ≠ e₂ ∧
      e₁ * e₂ = e₂ * e₁ ∧ e₁ * x = x * e₁ ∧ e₂ * x = x * e₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, ℓ, hxkl, hℓ, hℓ2, hk, hK'CS, -⟩ := sk_split hL0 hx hx2
  set ψ : ↥L0 →* ↥L0 ⧸ pPrimeCore 2 ↥L0 := QuotientGroup.mk' (pPrimeCore 2 ↥L0) with hψ
  have hψ1 : ∀ g : ↥L0, ψ g = 1 ↔ (g : X) ∈ pPrimeCoreOf 2 L0 := by
    intro g
    rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨g, h, rfl⟩
    · rintro ⟨w, hw, hwg⟩
      have : w = g := Subtype.ext hwg
      rwa [← this]
  have hψcomm : ∀ g h : ↥L0, ψ g * ψ h = ψ h * ψ g → ⁅(g : X), (h : X)⁆ ∈ pPrimeCoreOf 2 L0 := by
    intro g h hgh
    have h1 : ψ ⁅g, h⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hgh
    have := (hψ1 _).mp h1
    simpa [commutatorElement_def] using this
  have hψsq : ∀ g : ↥L0, (ψ g) ^ 2 = 1 → (g : X) ^ 2 ∈ pPrimeCoreOf 2 L0 := by
    intro g hg
    have := (hψ1 (g ^ 2)).mp (by rw [map_pow]; exact hg)
    simpa using this
  have hxN : x ∈ normalizer (L0 : Set X) := by
    rw [hxkl]
    exact mul_mem (hK'CS hk).1 (le_normalizer hℓ)
  set q₀ : ↥L0 ⧸ pPrimeCore 2 ↥L0 := ψ ⟨ℓ, hℓ⟩ with hq₀
  have hq₀2 : q₀ ^ 2 = 1 := by
    rw [hq₀, ← map_pow, hψ1]
    simpa using hℓ2
  have hL0N : L0 ≤ normalizer (L0 : Set X) := le_normalizer
  have hON : normalizer (L0 : Set X) ≤ normalizer (pPrimeCoreOf 2 L0 : Set X) := fun c hc =>
    mem_normalizer_oddCoreOf_of_mem_normalizer hc
  have hOodd : Odd (Nat.card (pPrimeCoreOf 2 L0)) := odd_card_oddCoreOf L0
  have hlift1 : ∀ q : ↥L0 ⧸ pPrimeCore 2 ↥L0, q ^ 2 = 1 → q * q₀ = q₀ * q →
      ∃ d ∈ L0, d ^ 2 = 1 ∧ d * x = x * d ∧ ∀ hd : d ∈ L0, ψ ⟨d, hd⟩ = q := by
    intro q hq2 hqq₀
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L0) q
    have hg2 : (g : X) ^ 2 ∈ pPrimeCoreOf 2 L0 := hψsq g hq2
    have hgℓ : ⁅(g : X), ℓ⁆ ∈ pPrimeCoreOf 2 L0 := hψcomm g ⟨ℓ, hℓ⟩ hqq₀
    have hgx : ⁅(g : X), x⁆ ∈ pPrimeCoreOf 2 L0 := by
      have h1 : ⁅(g : X), k⁆ ∈ pPrimeCoreOf 2 L0 := (hK'CS hk).2.2 g g.2
      have h2 : k * ⁅(g : X), ℓ⁆ * k⁻¹ ∈ pPrimeCoreOf 2 L0 :=
        (mem_normalizer_iff.mp (hK'CS hk).2.1 _).mp hgℓ
      have h3 : ⁅(g : X), x⁆ = ⁅(g : X), k⁆ * (k * ⁅(g : X), ℓ⁆ * k⁻¹) := by
        rw [hxkl, commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      rw [h3]
      exact mul_mem h1 h2
    obtain ⟨d, hdN, hd2, hdx, hdg⟩ := sk_lift_X (oddCoreOf_le L0 |>.trans hL0N) hON hOodd hxN
      (j := 1) (by rwa [pow_one]) (hL0N g.2) hg2 hgx
    have hdL : d ∈ L0 := by
      have h1 : (g : X) * ((g : X)⁻¹ * d) ∈ L0 := mul_mem g.2 (oddCoreOf_le L0 hdg)
      rwa [mul_inv_cancel_left] at h1
    refine ⟨d, hdL, hd2, hdx, fun hd => ?_⟩
    rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := (show (g : X)⁻¹ * d ∈ pPrimeCoreOf 2 L0 from hdg)
    have hw1 : w = g⁻¹ * ⟨d, hd⟩ := Subtype.ext (by simpa using hwe)
    have hw2 : g⁻¹ * ⟨d, hd⟩ ∈ pPrimeCore 2 ↥L0 := by
      rw [← hw1]
      exact hw
    have hw3 : (⟨d, hd⟩ : ↥L0)⁻¹ * g = (g⁻¹ * ⟨d, hd⟩)⁻¹ := by group
    rw [hw3]
    exact inv_mem hw2
  have hQinv : ∃ q₁ : ↥L0 ⧸ pPrimeCore 2 ↥L0, orderOf q₁ = 2 ∧ (q₀ = 1 ∨ q₀ = q₁) := by
    by_cases h0 : q₀ = 1
    · have hdvd : 2 ∣ Nat.card (↥L0 ⧸ pPrimeCore 2 ↥L0) := by
        rcases hL0.1.2.1 with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
        · rw [Nat.card_congr eM.toEquiv, Sporadic.McL.card_McL]
          norm_num
        · rw [Nat.card_congr eL.toEquiv, Sporadic.Ly.card_Ly']
          norm_num
      obtain ⟨q₁, hq₁⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
      exact ⟨q₁, hq₁, Or.inl h0⟩
    · exact ⟨q₀, orderOf_eq_prime hq₀2 h0, Or.inr rfl⟩
  obtain ⟨q₁, hq₁, hq₀₁⟩ := hQinv
  have hq₁2 : q₁ ^ 2 = 1 := by
    have := pow_orderOf_eq_one q₁
    rwa [hq₁] at this
  obtain ⟨u, hu2, huZ⟩ : ∃ u : ↥(centralizer ({q₁} : Set (↥L0 ⧸ pPrimeCore 2 ↥L0))),
      u ^ 2 = 1 ∧ u ∉ center ↥(centralizer ({q₁} : Set (↥L0 ⧸ pPrimeCore 2 ↥L0))) := by
    rcases hL0.1.2.1 with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
    · exact GH74.GLS.Stage12.McLRec.exists_noncentral_involution_of_doubleCover
        (Sec6L51B.isDoubleCoverOfAlt_centralizer_McL eM q₁ hq₁)
    · exact Sporadic.Recognition.LyonsSims.exists_noncentral_involution_of_doubleCover_eleven
        (Sec6L51B.isDoubleCoverOfAlt_centralizer_Ly eL q₁ hq₁)
  set q₂ : ↥L0 ⧸ pPrimeCore 2 ↥L0 := (u : ↥L0 ⧸ pPrimeCore 2 ↥L0)
  have hq₂2 : q₂ ^ 2 = 1 := by simpa using congrArg Subtype.val hu2
  have hq₁Z : (⟨q₁, mem_centralizer_singleton_iff.mpr rfl⟩ :
      ↥(centralizer ({q₁} : Set (↥L0 ⧸ pPrimeCore 2 ↥L0)))) ∈
      center ↥(centralizer ({q₁} : Set (↥L0 ⧸ pPrimeCore 2 ↥L0))) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (mem_centralizer_singleton_iff.mp v.2)
  have hq₂ne1 : q₂ ≠ 1 := by
    intro h
    apply huZ
    have : u = 1 := Subtype.ext h
    rw [this]
    exact one_mem _
  have hq₂ne : q₂ ≠ q₁ := by
    intro h
    apply huZ
    have : u = ⟨q₁, mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext h
    rw [this]
    exact hq₁Z
  have hq₁₂ : q₂ * q₁ = q₁ * q₂ := mem_centralizer_singleton_iff.mp u.2
  have hcomm₀ : ∀ q, (q₀ = 1 ∨ q₀ = q₁) → q * q₁ = q₁ * q → q * q₀ = q₀ * q := by
    rintro q (h | h) hq
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact hq
  obtain ⟨e₁, he₁L, he₁2, he₁x, hψe₁⟩ := hlift1 q₁ hq₁2 (hcomm₀ q₁ hq₀₁ rfl)
  obtain ⟨ℓ₂, hℓ₂L, hℓ₂2, hℓ₂x, hψℓ₂⟩ := hlift1 q₂ hq₂2 (hcomm₀ q₂ hq₀₁ hq₁₂)
  have hNH : pPrimeCoreOf 2 L0 ⊓ cen x ≤ normalizer (L0 : Set X) ⊓ cen x :=
    inf_le_inf ((oddCoreOf_le L0).trans hL0N) le_rfl
  have hHN : normalizer (L0 : Set X) ⊓ cen x ≤ normalizer ((pPrimeCoreOf 2 L0 ⊓ cen x :
      Subgroup X) : Set X) := fun c hc => mem_normalizer_inf (hON hc.1) (le_normalizer hc.2)
  have hNodd : Odd (Nat.card ↥(pPrimeCoreOf 2 L0 ⊓ cen x)) :=
    hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have he₁xC : e₁ ∈ cen x := mem_centralizer_singleton_iff.mpr he₁x
  have hℓ₂xC : ℓ₂ ∈ cen x := mem_centralizer_singleton_iff.mpr hℓ₂x
  have hcomm₁₂ : ⁅ℓ₂, e₁⁆ ∈ pPrimeCoreOf 2 L0 ⊓ cen x := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have := hψcomm ⟨ℓ₂, hℓ₂L⟩ ⟨e₁, he₁L⟩ (by rw [hψℓ₂, hψe₁]; exact hq₁₂)
      exact this
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hℓ₂xC he₁xC) (inv_mem hℓ₂xC)) (inv_mem he₁xC)
  obtain ⟨e₂, he₂H, he₂2, he₂e₁, he₂ℓ⟩ := sk_lift_X hNH hHN hNodd
    (mem_inf.mpr ⟨hL0N he₁L, he₁xC⟩) (j := 1) (by rwa [pow_one])
    (mem_inf.mpr ⟨hL0N hℓ₂L, hℓ₂xC⟩) (by rw [hℓ₂2]; exact one_mem _) hcomm₁₂
  have he₂L : e₂ ∈ L0 := by
    have h1 : ℓ₂ * (ℓ₂⁻¹ * e₂) ∈ L0 := mul_mem hℓ₂L (oddCoreOf_le L0 he₂ℓ.1)
    rwa [mul_inv_cancel_left] at h1
  have hψe₂ : ψ ⟨e₂, he₂L⟩ = q₂ := by
    rw [← hψℓ₂ hℓ₂L, hψ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := he₂ℓ.1
    have hw1 : w = (⟨ℓ₂, hℓ₂L⟩ : ↥L0)⁻¹ * ⟨e₂, he₂L⟩ := Subtype.ext (by simpa using hwe)
    have hw2 : (⟨ℓ₂, hℓ₂L⟩ : ↥L0)⁻¹ * ⟨e₂, he₂L⟩ ∈ pPrimeCore 2 ↥L0 := by
      rw [← hw1]
      exact hw
    have hw3 : (⟨e₂, he₂L⟩ : ↥L0)⁻¹ * ⟨ℓ₂, hℓ₂L⟩ = ((⟨ℓ₂, hℓ₂L⟩ : ↥L0)⁻¹ * ⟨e₂, he₂L⟩)⁻¹ := by
      group
    rw [hw3]
    exact inv_mem hw2
  have hq₁ne1 : q₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hq₁
    exact absurd hq₁ (by norm_num)
  have he₁ne : e₁ ≠ 1 := by
    rintro rfl
    apply hq₁ne1
    rw [← hψe₁ he₁L]
    exact map_one ψ ▸ congrArg ψ (Subtype.ext rfl)
  have he₂ne : e₂ ≠ 1 := by
    rintro rfl
    apply hq₂ne1
    rw [← hψe₂]
    exact map_one ψ ▸ congrArg ψ (Subtype.ext rfl)
  refine ⟨e₁, e₂, he₁L, he₂L, orderOf_eq_prime he₁2 he₁ne, orderOf_eq_prime he₂2 he₂ne, ?_,
    he₂e₁.symm, he₁x, mem_centralizer_singleton_iff.mp he₂H.2⟩
  intro h
  apply hq₂ne
  rw [← hψe₂, ← hψe₁ he₁L]
  congr 1
  exact Subtype.ext h.symm

theorem sec6L65_of_ctrl
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (h0 : ∀ b ∈ Sec6M X n (cen t), orderOf b = 2 → oddCoreOf (cen b) = ⊥) :
    Sec6L65 X n t := by
  intro x hx hxo
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.choice.inv] at this
  obtain ⟨L0, hL0⟩ := hS.choice.hasM
  have hL0M : L0 ≤ Sec6M X n (cen t) := le_sSup hL0
  obtain ⟨e₁, e₂, he₁, he₂, ho₁, ho₂, hne, hcomm, hx₁, hx₂⟩ := sk_four hL0 hx hx2
  have he₁2 : e₁ ^ 2 = 1 := by
    have := pow_orderOf_eq_one e₁
    rwa [ho₁] at this
  have he₂2 : e₂ ^ 2 = 1 := by
    have := pow_orderOf_eq_one e₂
    rwa [ho₂] at this
  have he₁m : e₁ * e₁ = 1 := by rw [← sq]; exact he₁2
  have he₂m : e₂ * e₂ = 1 := by rw [← sq]; exact he₂2
  set E := GH74.GLS.SP.Local.kleinFourSubgroup e₁ e₂ he₁m he₂m hcomm
  have hE2 : ∀ g ∈ E, g ^ 2 = 1 := fun g hg => by
    rw [sq]
    exact GH74.GLS.SP.Local.kleinFourSubgroup_mul_self hg
  have hEab : Open.IsElemAbelian 2 E :=
    ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb => comm_of_sq_eq_one hE2 ha hb, hE2⟩
  have he₁1 : e₁ ≠ 1 := fun h => by rw [h, orderOf_one] at ho₁; exact absurd ho₁ (by norm_num)
  have he₂1 : e₂ ≠ 1 := fun h => by rw [h, orderOf_one] at ho₂; exact absurd ho₂ (by norm_num)
  have hEcard : Nat.card E = 4 := GH74.GLS.SP.Local.card_kleinFourSubgroup he₁1 he₂1 hne
  have hEmem : ∀ e ∈ E, e ∈ L0 ∧ e * x = x * e := by
    intro e he
    rcases GH74.GLS.SP.Local.mem_kleinFourSubgroup.mp he with rfl | rfl | rfl | rfl
    · exact ⟨one_mem _, by rw [one_mul, mul_one]⟩
    · exact ⟨he₁, hx₁⟩
    · exact ⟨he₂, hx₂⟩
    · refine ⟨mul_mem he₁ he₂, ?_⟩
      calc e₁ * e₂ * x = e₁ * (x * e₂) := by rw [mul_assoc, hx₂]
        _ = x * (e₁ * e₂) := by rw [← mul_assoc, hx₁, mul_assoc]
  have hEN : E ≤ normalizer (oddCoreOf (cen x) : Set X) := fun e he =>
    le_normalizer_oddCoreOf (cen x) (mem_centralizer_singleton_iff.mpr (hEmem e he).2)
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreOf (cen x))) :=
    Nat.coprime_two_left.mpr (odd_card_oddCoreOf _)
  have hgen := SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two hEab
    (by rw [hEcard]; norm_num) hEN hcop
  rw [← hgen, eq_bot_iff]
  refine iSup_le fun e => iSup_le fun heE => iSup_le fun he1 => ?_
  obtain ⟨heL0, hex⟩ := hEmem e heE
  have he2 : e ^ 2 = 1 := hE2 e heE
  have heo : orderOf e = 2 := orderOf_eq_prime he2 he1
  have heM : e ∈ Sec6M X n (cen t) := hL0M heL0
  have hloc := sk_loc hL0 heL0 he2 hx hx2 hex.symm
  have hYN : (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), sec6Piece L e) ≤
      normalizer ((oddCoreOf (cen t) ⊓ cen e : Subgroup X) : Set X) := by
    refine iSup₂_le fun L hL y hy => ?_
    have hyt : y ∈ cen t := ((oTwoPrimeOf_le _).trans (inf_le_left.trans (sk_kcomp_pc hL).1)) hy
    have hye : y ∈ cen e := ((oTwoPrimeOf_le _).trans inf_le_right) hy
    exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen t) hyt) (le_normalizer hye)
  have hRodd : Odd (Nat.card ↥(oddCoreOf (cen t) ⊓ cen e)) :=
    (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨o, ho, a, haY, ha2, hxoa⟩ :=
    exists_conj_twoElt_of_mem_sup_odd_X hYN hRodd hloc (j := 1) (by rwa [pow_one])
  have ha2' : a ^ 2 = 1 := by rwa [pow_one] at ha2
  have hot : o ∈ cen t := (oddCoreOf_le _) (mem_inf.mp ho).1
  have hoe : o ∈ cen e := (mem_inf.mp ho).2
  have haB : a ∈ Sec6Base X n t := by
    have h1 : a = o⁻¹ * x * o⁻¹⁻¹ := by rw [hxoa]; group
    rw [h1]
    exact (mem_normalizer_iff.mp (cen_le_normalizer_sec6Base n t (inv_mem hot)) x).mp hx
  have hcore := sk_core ht2 hC heM heo (h0 e heM heo) haB ha2' haY
  set φ : X ≃* X := MulAut.conj o with hφ
  have hφa : φ a = x := by rw [hφ, MulAut.conj_apply, hxoa]
  have hφe : φ e = e := by
    rw [hφ, MulAut.conj_apply, mem_centralizer_singleton_iff.mp hoe, mul_inv_cancel_right]
  have hmap : (oddCoreOf (cen a) ⊓ cen e).map φ.toMonoidHom = oddCoreOf (cen x) ⊓ cen e := by
    rw [Subgroup.map_inf_eq _ _ φ.toMonoidHom (by exact φ.injective), oddCoreOf_map_mulEquiv',
      cen_map, cen_map, hφa, hφe]
  rw [← hmap, hcore, Subgroup.map_bot]

end CFSG.OddStandard.Solomon75
