module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TypeIExteriorTi
import CFSG.FeitThompson.Local.SigmaCoreFusion
import CFSG.FeitThompson.Local.TypeIExteriorFixedElementPowers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson Subgroup Pointwise
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem orderOf_conj_eq (a g : G) : orderOf (g⁻¹ * a * g) = orderOf a :=
  (SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * a = g⁻¹ * a * g * g⁻¹ by group)).symm

theorem natCard_prep09_hallCoreIn_eq (M : Subgroup G) :
    Nat.card (hallCoreIn M) = Nat.card (hallCore M) := by
  rw [hallCoreIn_def, Subgroup.card_subtype]

theorem mem_hallCoreIn_of_conj [Finite G] {M : Subgroup G} {a g : G}
    (ha : a ∈ hallCoreIn M) (hb : g⁻¹ * a * g ∈ M) : g⁻¹ * a * g ∈ hallCoreIn M := by
  refine mem_hallCoreIn_of_orderOf_dvd hb ?_
  rw [orderOf_conj_eq, ← natCard_prep09_hallCoreIn_eq]
  exact Subgroup.orderOf_dvd_natCard _ ha

theorem conj_mem_coreFixedSet {M : Subgroup G} {a m : G} (hm : m ∈ M)
    (ha : a ∈ coreFixedSet (hallCoreIn M) M) :
    m⁻¹ * a * m ∈ coreFixedSet (hallCoreIn M) M := by
  obtain ⟨haM, ha1, hac⟩ := ha
  refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hm) haM) hm, ?_, ?_⟩
  · intro h
    apply ha1
    have hconj : a = m * (m⁻¹ * a * m) * m⁻¹ := by group
    rw [hconj, h]; group
  · obtain ⟨x, hx, hx1⟩ :=
      (centIn (hallCoreIn M) {a}).nontrivial_iff_exists_ne_one.1
        ((centIn (hallCoreIn M) {a}).nontrivial_iff_ne_bot.2 hac)
    have hxH : x ∈ hallCoreIn M := (mem_centIn.1 hx).1
    have hxc : a * x = x * a := (mem_centIn.1 hx).2 a rfl
    refine (centIn (hallCoreIn M) {m⁻¹ * a * m}).nontrivial_iff_ne_bot.1
      ((centIn (hallCoreIn M) {m⁻¹ * a * m}).nontrivial_iff_exists_ne_one.2
        ⟨m⁻¹ * x * m, mem_centIn.2 ⟨conj_mem_hallCoreIn hm hxH, ?_⟩, ?_⟩)
    · intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      calc m⁻¹ * a * m * (m⁻¹ * x * m) = m⁻¹ * (a * x) * m := by group
        _ = m⁻¹ * (x * a) * m := by rw [hxc]
        _ = m⁻¹ * x * m * (m⁻¹ * a * m) := by group
    · intro h
      apply hx1
      have hxconj : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
      rw [hxconj, h]; group

theorem mem_exteriorFixedSet_of_mem_coreFixedSet {M : Subgroup G} {a : G}
    (ha : a ∈ coreFixedSet (hallCoreIn M) M) (haH : a ∉ hallCoreIn M) :
    a ∈ exteriorFixedSet (hallCoreIn M) M := ⟨ha.1, haH, ha.2.2⟩

theorem centralizer_le_of_forall_fusion {M : Subgroup G}
    (hfus : ∀ y ∈ exteriorFixedSet (hallCoreIn M) M, ∀ z ∈ exteriorFixedSet (hallCoreIn M) M,
      ∀ g : G, g⁻¹ * y * g = z → g ∈ M)
    {a : G} (ha : a ∈ exteriorFixedSet (hallCoreIn M) M) :
    centralizer ({a} : Set G) ≤ M := by
  intro g hg
  refine hfus a ha a ha g ?_
  have hc : a * g = g * a := (Subgroup.mem_centralizer_iff.1 hg) a rfl
  calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
    _ = g⁻¹ * (g * a) := by rw [hc]
    _ = a := by group

theorem isTIWithNormalizer_exteriorFixedSet {M : Subgroup G}
    (hD : (exteriorFixedSet (hallCoreIn M) M).Nonempty)
    (hnorm : normalizer (exteriorFixedSet (hallCoreIn M) M) = M)
    (hdisj : ∀ g : G, g ∉ M →
      exteriorFixedSet (hallCoreIn M) M ∩ conjSet g (exteriorFixedSet (hallCoreIn M) M) = ∅) :
    IsTIWithNormalizer (exteriorFixedSet (hallCoreIn M) M) M where
  nonempty := hD
  one_notMem := fun h => h.2.1 (one_mem _)
  normalizer_eq := hnorm
  disjoint_conj_image := by
    intro g hg
    have hg' : g⁻¹ ∉ M := fun hc => hg (by simpa using inv_mem hc)
    have himg : (MulAut.conj g) '' (exteriorFixedSet (hallCoreIn M) M) =
        conjSet g⁻¹ (exteriorFixedSet (hallCoreIn M) M) :=
      Set.image_congr' fun x => by simp [MulAut.conj]
    rw [himg]
    exact Set.disjoint_iff_inter_eq_empty.2 (hdisj g⁻¹ hg')

section Signalizer

variable [Finite G]

open scoped Classical in
theorem sigmaSignalizerOn_eq_sigmaSignalizer {M : Subgroup G} {a : G} (ha : a ∈ sigmaCore M)
    (ha1 : a ≠ 1) : sigmaSignalizerOn M a = sigmaSignalizer a := by
  rw [sigmaSignalizerOn, if_pos ⟨ha, ha1⟩]

open scoped Classical in
theorem sigmaSignalizerOn_eq_bot {M : Subgroup G} {a : G} (ha : a ∉ sigmaCore M) :
    sigmaSignalizerOn M a = ⊥ := by
  rw [sigmaSignalizerOn, if_neg fun h => ha h.1]

theorem signalizer_splitting_of_notMem {M : Subgroup G} {a : G}
    (haS : a ∉ sigmaCore M) (hle : centralizer ({a} : Set G) ≤ M) :
    sigmaSignalizerOn M a ≤ centralizer ({a} : Set G) ∧
      ((sigmaSignalizerOn M a).subgroupOf (centralizer ({a} : Set G))).Normal ∧
      ((sigmaSignalizerOn M a : Set G) * ((centIn M {a} : Subgroup G) : Set G) =
        (centralizer ({a} : Set G) : Set G)) ∧
      sigmaSignalizerOn M a ⊓ centIn M {a} = ⊥ := by
  rw [sigmaSignalizerOn_eq_bot haS]
  refine ⟨bot_le, ?_, ?_, by simp⟩
  · rw [Subgroup.bot_subgroupOf]; infer_instance
  · rw [centIn_def, inf_eq_right.2 hle]; simp

end Signalizer

theorem signalizer_splitting (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsFTAmbient G) {M : Subgroup G} (hM : IsCoatom M)
    {a : G} (ha : a ∈ sigmaCore M) (ha1 : a ≠ 1) :
    sigmaSignalizerOn M a ≤ centralizer ({a} : Set G) ∧
      ((sigmaSignalizerOn M a).subgroupOf (centralizer ({a} : Set G))).Normal ∧
      ((sigmaSignalizerOn M a : Set G) * ((centIn M {a} : Subgroup G) : Set G) =
        (centralizer ({a} : Set G) : Set G)) ∧
      sigmaSignalizerOn M a ⊓ centIn M {a} = ⊥ ∧
      Nat.card (sigmaSignalizerOn M a) = sigmaMultiplicity a ∧
      sigmaSignalizerOn M a ⊓ M = ⊥ := by
  have haU : a ∈ sigmaSupport G := mem_sigmaSupport.2 ⟨M, hM, ha, ha1⟩
  have hR := h₁ G hG a haU
  obtain ⟨hsemi, hinfM⟩ := hR.2.2.2.2.1 M (mem_sigmaSupportingMaximals.2 ⟨hM, ha⟩)
  rw [sigmaSignalizerOn_eq_sigmaSignalizer ha ha1]
  exact ⟨sigmaSignalizer_le_centralizer a, hR.1, hsemi.coe_eq_mul.symm,
    le_bot_iff.1 fun x hx => hinfM ▸ ⟨hx.1, hx.2.1⟩, hR.2.2.1, hinfM⟩

theorem typeI_dade_clause_iv
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_kappa_free_auxiliary_cross_point_coprimality.{u})
    (h₆ : Statements.FTS_signalizer_supporting_type_exterior.{u})
    (h₇ : Statements.FTS_signalizer_unique_supporting_maximum.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimpleOddOrder G) (hamb : IsFTAmbient G)
    {M : Subgroup G} (hM : IsCoatom M) (hkap : kappaPrimes M = ∅)
    (hHS : hallCoreIn M = sigmaCore M)
    (hDcent : ∀ a ∈ exteriorFixedSet (hallCoreIn M) M, centralizer ({a} : Set G) ≤ M)
    {a : G} (ha : a ∈ coreFixedSet (hallCoreIn M) M) (hnle : ¬ centralizer ({a} : Set G) ≤ M) :
    (a ∈ hallCoreIn M ∧ a ≠ 1) ∧
      ∃ T : Subgroup G, IsUniqueMaximalOvergroup (centralizer ({a} : Set G)) T ∧
        (IsTypeI T ∨ IsTypeII T) ∧ hallCoreIn T = sigmaCore T ∧
        FreeCore.IsInternalSemidirectProduct T (hallCoreIn T) (M ⊓ T) ∧
        (IsTypeI T → a ∈ coreFixedSet (hallCoreIn T) T \ ((hallCoreIn T : Set G) \ {1})) ∧
        (IsTypeII T → a ∈ coreFixedSet (hallCoreIn T) (⁅T, T⁆ : Subgroup G) \
          ((hallCoreIn T : Set G) \ {1})) ∧
        sigmaSignalizerOn M a = centIn (hallCoreIn T) {a} ∧
        ∀ b ∈ coreFixedSet (hallCoreIn M) M,
          (Nat.card (hallCoreIn T)).Coprime (Nat.card (centIn M {b})) := by
  have haH : a ∈ hallCoreIn M := by
    by_contra haH
    exact hnle (hDcent a (mem_exteriorFixedSet_of_mem_coreFixedSet ha haH))
  have ha1 : a ≠ 1 := ha.2.1
  have haS : a ∈ sigmaCore M := hHS ▸ haH
  have haU : a ∈ sigmaSupport G := mem_sigmaSupport.2 ⟨M, hM, haS, ha1⟩
  obtain ⟨hRle, hRnorm, hRmul, hRinf, hRcard, hRinfM⟩ :=
    signalizer_splitting h₁ hamb hM haS ha1
  have hRne : sigmaSignalizerOn M a ≠ ⊥ := by
    intro hR
    refine hnle fun x hx => ?_
    rw [← SetLike.mem_coe, ← hRmul, hR] at hx
    obtain ⟨r, hr, c, hc, rfl⟩ := hx
    simp only [Subgroup.coe_bot, Set.mem_singleton_iff] at hr
    subst hr
    simpa using (centIn_le M ({a} : Set G)) hc
  have hk : 1 < sigmaMultiplicity a := by
    rw [← hRcard]; exact (Subgroup.one_lt_card_iff_ne_bot _).2 hRne
  obtain ⟨⟨T, ⟨hTco, hTle⟩, hTuniq⟩, hTstruct⟩ := h₇ G hG a haU hk
  have hTU : IsUniqueMaximalOvergroup (centralizer ({a} : Set G)) T :=
    ⟨hTco, hTle, fun N hN hNle => hTuniq N ⟨hN, hNle⟩⟩
  obtain ⟨hTtype, hTHS, hRT, hRTne, hBI, hBII⟩ := h₆ G hG a haU hk T hTU
  obtain ⟨-, -, -, hMT⟩ := hTstruct T hTco hTle
  obtain ⟨hTM, haMT, hsemi, hsigdisj, htau2, hbeta⟩ :=
    hMT M (mem_sigmaSupportingMaximals.2 ⟨hM, haS⟩)
  refine ⟨⟨haH, ha1⟩, T, hTU, hTtype, hTHS, by rw [hTHS]; exact hsemi, hBI, hBII,
    by rw [sigmaSignalizerOn_eq_sigmaSignalizer haS ha1]; exact hRT, fun b hb => ?_⟩
  have hbc : sigmaCore M ⊓ centralizer ({b} : Set G) ≠ ⊥ := by
    have hb2 := hb.2.2; rwa [centIn_def, hHS] at hb2
  rw [hTHS]
  exact h₂ G hamb M hM T hTco htau2 (fun r hr hrT => hbeta r hrT hr) hkap
    (Set.inter_comm _ _ ▸ hsigdisj) ⟨a, haS, ha1, hTle⟩ b hb.1 hb.2.1 hbc

theorem FTS_type_I_dade_support
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_kappa_free_auxiliary_cross_point_coprimality.{u})
    (_h₃ : Statements.FTS_outside_sigma_plane_structure.{u})
    (_h₄ : Statements.FTS_plane_maximal_overgroups.{u})
    (_h₅ : Statements.FTS_sigma_prime_separation.{u})
    (h₆ : Statements.FTS_signalizer_supporting_type_exterior.{u})
    (h₇ : Statements.FTS_signalizer_unique_supporting_maximum.{u})
    (h₈ : Statements.FTS_type_I_complement_structure.{u})
    (h₉ : Statements.FTS_type_I_core_kappa_identity.{u}) :
    Statements.FTS_type_I_dade_support.{u} := by
  intro G _ _ hG M hM hMI
  have hamb : IsFTAmbient G :=
    { isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      odd_natCard := hG.odd_natCard
      isSolvable := hG.isSolvable_of_ne_top }
  have hG8 : Prep08.IsMinimalSimpleOddOrder G :=
    { isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      odd_natCard := hG.odd_natCard
      isSolvable_of_ne_top := hG.isSolvable_of_ne_top }
  obtain ⟨hkap, hHS, -⟩ := h₉ G hG M hM hMI
  have hcorefus := FTS_sigma_core_fusion h₁ G hG8 M hM
  have hinv : ∀ a ∈ coreFixedSet (hallCoreIn M) M, ∀ m ∈ M,
      m⁻¹ * a * m ∈ coreFixedSet (hallCoreIn M) M := fun _ ha _ hm => conj_mem_coreFixedSet hm ha
  have hTI : (exteriorFixedSet (hallCoreIn M) M).Nonempty →
      IsTIWithNormalizer (exteriorFixedSet (hallCoreIn M) M) M := by
    intro hD
    obtain ⟨hnorm, hdisj, -⟩ := FTS_type_I_exterior_ti h₈ h₉ G hG M hM hMI hD
    exact isTIWithNormalizer_exteriorFixedSet hD hnorm hdisj
  have hDfus : (exteriorFixedSet (hallCoreIn M) M).Nonempty →
      ∀ y ∈ exteriorFixedSet (hallCoreIn M) M, ∀ z ∈ exteriorFixedSet (hallCoreIn M) M,
        ∀ g : G, g⁻¹ * y * g = z → g ∈ M := fun hD =>
    (FTS_type_I_exterior_ti h₈ h₉ G hG M hM hMI hD).2.2
  have hDcent : ∀ a ∈ exteriorFixedSet (hallCoreIn M) M, centralizer ({a} : Set G) ≤ M :=
    fun a ha => centralizer_le_of_forall_fusion (hDfus ⟨a, ha⟩) ha
  have hfus : ∀ a ∈ coreFixedSet (hallCoreIn M) M, ∀ b ∈ coreFixedSet (hallCoreIn M) M,
      (∃ g : G, g⁻¹ * a * g = b) → ∃ m ∈ M, m⁻¹ * a * m = b := by
    intro a ha b hb hab
    obtain ⟨g, hg⟩ := hab
    by_cases haH : a ∈ hallCoreIn M
    ·
      have hbH : b ∈ hallCoreIn M := hg ▸ mem_hallCoreIn_of_conj haH (hg ▸ hb.1)
      rw [hHS] at haH hbH
      exact hcorefus a haH g (hg ▸ hbH) |>.imp fun m hm => ⟨hm.1, hg ▸ hm.2.symm⟩
    ·
      have hbH : b ∉ hallCoreIn M := by
        intro hbH
        refine haH ?_
        have hconj : a = (g⁻¹)⁻¹ * b * g⁻¹ := by rw [← hg]; group
        rw [hconj]
        exact mem_hallCoreIn_of_conj hbH (hconj ▸ ha.1)
      exact ⟨g, hDfus ⟨a, mem_exteriorFixedSet_of_mem_coreFixedSet ha haH⟩
        a (mem_exteriorFixedSet_of_mem_coreFixedSet ha haH)
        b (mem_exteriorFixedSet_of_mem_coreFixedSet hb hbH) g hg, hg⟩
  have hsplit : ∀ a ∈ coreFixedSet (hallCoreIn M) M,
      sigmaSignalizerOn M a ≤ centralizer ({a} : Set G) ∧
        ((sigmaSignalizerOn M a).subgroupOf (centralizer ({a} : Set G))).Normal ∧
        ((sigmaSignalizerOn M a : Set G) * ((centIn M {a} : Subgroup G) : Set G) =
          (centralizer ({a} : Set G) : Set G)) ∧
        sigmaSignalizerOn M a ⊓ centIn M {a} = ⊥ := by
    intro a ha
    by_cases haS : a ∈ sigmaCore M
    · obtain ⟨hR1, hR2, hR3, hR4, -, -⟩ := signalizer_splitting h₁ hamb hM haS ha.2.1
      exact ⟨hR1, hR2, hR3, hR4⟩
    · exact signalizer_splitting_of_notMem haS
        (hDcent a (mem_exteriorFixedSet_of_mem_coreFixedSet ha fun h => haS (hHS ▸ h)))
  have hcop : ∀ a ∈ coreFixedSet (hallCoreIn M) M, ∀ b ∈ coreFixedSet (hallCoreIn M) M,
      (Nat.card (sigmaSignalizerOn M a)).Coprime (Nat.card (centIn M {b})) := by
    intro a ha b hb
    have hbot : sigmaSignalizerOn M a = ⊥ →
        (Nat.card (sigmaSignalizerOn M a)).Coprime (Nat.card (centIn M {b})) := fun h => by
      rw [h, Subgroup.card_bot]; exact Nat.gcd_one_left _
    by_cases haS : a ∈ sigmaCore M
    · by_cases hnle : centralizer ({a} : Set G) ≤ M
      ·
        obtain ⟨hRle, -, -, -, -, hRinfM⟩ := signalizer_splitting h₁ hamb hM haS ha.2.1
        exact hbot (le_bot_iff.1 (hRinfM ▸ fun x hx => ⟨hx, hnle (hRle hx)⟩))
      ·
        obtain ⟨-, T, -, -, -, -, -, -, hRT, hcopT⟩ :=
          typeI_dade_clause_iv h₁ h₂ h₆ h₇ hG hamb hM hkap hHS hDcent ha hnle
        refine Nat.Coprime.coprime_dvd_left ?_ (hcopT b hb)
        rw [hRT]; exact Subgroup.card_dvd_of_le (centIn_le _ _)
    · exact hbot (sigmaSignalizerOn_eq_bot haS)
  have hdade : IsDadeData M (coreFixedSet (hallCoreIn M) M) (sigmaSignalizerOn M) :=
    { subset_sdiff := fun a ha => ⟨ha.1, by simpa using ha.2.1⟩
      conj_mem := fun {a} ha {x} hx => by simpa using hinv a ha x⁻¹ (M.inv_mem hx)
      fusion := fun {a} ha {b} hb hconj => by
        obtain ⟨c, hc⟩ := isConj_iff.1 hconj
        obtain ⟨m, hm, hmeq⟩ := hfus a ha b hb ⟨c⁻¹, by rw [← hc]; group⟩
        exact ⟨m⁻¹, M.inv_mem hm, by simpa using hmeq⟩
      le_centralizer := fun {a} ha => (hsplit a ha).1
      normal_subgroupOf := fun {a} ha => (hsplit a ha).2.1
      inf_eq_bot := fun {a} ha => (hsplit a ha).2.2.2
      mul_eq := fun {a} ha => (hsplit a ha).2.2.1
      coprime_card := fun {a} ha {b} hb => hcop a ha b hb }
  refine ⟨hHS.symm, hinv, hfus, hsplit, hcop, hdade, ?_, hTI, ?_⟩
  ·
    intro f _ hfconj z
    refine ⟨fun a ha hy => ?_, fun hnone => ?_⟩
    · refine dadeSupportExtension_apply_of_mem_dadeSupport hdade ?_ ha
        (mem_dadeSupport_iff.2 hy)
      intro b _ l hl
      simpa using hfconj l⁻¹ (M.inv_mem hl) b
    · refine dadeSupportExtension_eq_zero_of_notMem fun hz => ?_
      obtain ⟨a, ha, y, hy, hc⟩ := mem_totalDadeSupport_iff_exists_isConj.1 hz
      exact hnone a ha y hy hc
  · exact fun a ha hnle => typeI_dade_clause_iv h₁ h₂ h₆ h₇ hG hamb hM hkap hHS hDcent ha hnle

end CFSG.FeitThompson.Proofs

end
