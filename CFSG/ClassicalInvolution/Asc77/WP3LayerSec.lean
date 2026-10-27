module

public import CFSG.ClassicalInvolution.Asc77.AscE184SecB
public import CFSG.ClassicalInvolution.Asc77.AscL62Lem33
public import CFSG.ClassicalInvolution.Asc77.WP3LayerPair

public section

namespace CFSG.ClassicalInvolution.Asc77.ExactLayer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Bridge

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {c : G} {K : Subgroup G}

omit [Finite G] in
theorem oddCoreOf_eq_oddCoreIn (X : Subgroup G) : oddCoreOf X = oddCoreIn X := rfl

theorem commutator_zpowers_le_iff :
    ⁅Subgroup.zpowers c, K⁆ ≤ oddCoreOf K ↔ c ∈ trivialOnQuot K := by
  constructor
  · intro h
    exact ⟨le_normalizer_of_commutator_le_oddCoreOf h (Subgroup.mem_zpowers c), fun x hx =>
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers c) hx)⟩
  · intro h
    refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
    have ha' : a ∈ trivialOnQuot K := (Subgroup.zpowers_le.mpr h) ha
    exact ha'.2 x hx

theorem sectionMembers_zpowers (Ω : Set (Subgroup G)) (c : G) :
    AscE184Sect.sectionMembers Ω (Subgroup.zpowers c) = tqMembers Ω c := by
  ext J
  exact and_congr_right fun _ => commutator_zpowers_le_iff

omit [Finite G] in
theorem mem_fixedSylows_zpowers_iff {T : Subgroup G} :
    T ∈ AscE184Sect.fixedSylows (Subgroup.zpowers c) K ↔
      IsSylow2In T K ∧ T ≤ Subgroup.centralizer ({c} : Set G) := by
  show (IsSylow2In T K ∧ T ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G)) ↔ _
  rw [centralizer_zpowers_eq_singleton']

theorem secMember_zpowers_eq_exactCore (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hK : K ∈ Ω) (hcK : c ∈ trivialOnQuot K) :
    AscE184Sect.secMember (Subgroup.zpowers c) K = exactCore c K := by
  have hAK : ⁅Subgroup.zpowers c, K⁆ ≤ oddCoreOf K := commutator_zpowers_le_iff.mpr hcK
  have hcent : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := centralizer_zpowers_eq_singleton' c
  set S := AscE184Sect.secMember (Subgroup.zpowers c) K with hS
  set M : Subgroup G := K ⊓ Subgroup.centralizer ({c} : Set G) with hM
  have hSM : S ≤ M := by
    have := AscE184Sect.secMember_le (Subgroup.zpowers c) K
    rwa [hcent] at this
  have hSperf : Group.IsPerfect ↥S := AscE184Sect.secMember_perfect hΩ hc2 hK hAK
  refine le_antisymm (le_perfectResidualOf_of_perfect hSM hSperf) ?_
  have hPM : exactCore c K ≤ M := exactCore_le c K
  have hPperf : Group.IsPerfect ↥(exactCore c K) := perfect_exactCore c K
  have hSnorm : (S.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hSM]
    intro s m hs hm
    have h1 : m * s * m⁻¹ ∈ conjSub m S := conj_mem_conjSub hs
    rwa [AscE184Sect.conjSub_secMember_of_mem hm.1 (by rw [hcent]; exact hm.2)] at h1
  set ρ : ↥M →* ↥M ⧸ S.subgroupOf M := QuotientGroup.mk' (S.subgroupOf M) with hρ
  set ι : ↥(oddCoreOf K ⊓ M) →* ↥M := Subgroup.inclusion inf_le_right with hι
  have hdec : ∀ m : ↥M, ∃ n : ↥(oddCoreOf K ⊓ M), ρ (ι n) = ρ m := by
    intro m
    obtain ⟨s, hs, n, hn, hsn⟩ := AscE184Sect.exists_mul_secMember hΩ hc2 hK hAK m.2.1
    have hsM : s ∈ M := hSM hs
    have hnM : n ∈ M := by
      have : n = s⁻¹ * (m : G) := by rw [hsn]; group
      rw [this]
      exact M.mul_mem (M.inv_mem hsM) m.2
    refine ⟨⟨n, hn, hnM⟩, ?_⟩
    show QuotientGroup.mk' _ (⟨n, hnM⟩ : ↥M) = QuotientGroup.mk' _ m
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h2 : ((⟨n, hnM⟩ : ↥M)⁻¹ * m : ↥M) =
        (⟨n, hnM⟩ : ↥M)⁻¹ * (⟨s, hsM⟩ : ↥M) * ((⟨n, hnM⟩ : ↥M)⁻¹)⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv, hsn]; group)
    rw [h2]
    exact hSnorm.conj_mem (⟨s, hsM⟩ : ↥M) (Subgroup.mem_subgroupOf.mpr hs) _
  have hQodd : Odd (Nat.card (↥M ⧸ S.subgroupOf M)) := by
    have hsurj : Function.Surjective (ρ.comp ι) := by
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (S.subgroupOf M) q
      obtain ⟨n, hn⟩ := hdec m
      exact ⟨n, hn⟩
    have h1 := Subgroup.card_range_dvd (ρ.comp ι)
    rw [MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top] at h1
    exact ((oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)).of_dvd_nat h1
  set P' : Subgroup ↥M := (exactCore c K).subgroupOf M with hP'
  have hP'perf : Group.IsPerfect ↥P' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPM).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPM).symm.surjective
  set Pbar : Subgroup (↥M ⧸ S.subgroupOf M) := P'.map ρ with hPbar
  have hPbarperf : Group.IsPerfect ↥Pbar := by
    refine Group.IsPerfect.ofSurjective
      (f := (ρ.comp P'.subtype).codRestrict Pbar (fun x => ⟨x, x.2, rfl⟩)) ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hPbot : Pbar = ⊥ :=
    eq_bot_of_perfect_of_odd hPbarperf.commutator_eq_top
      (hQodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Pbar))
  intro x hx
  have h1 : ρ ⟨x, hPM hx⟩ ∈ Pbar := ⟨⟨x, hPM hx⟩, hx, rfl⟩
  rw [hPbot, Subgroup.mem_bot, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem exactCore_eq_iSup_fixedSylows (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hK : K ∈ Ω) (hcK : c ∈ trivialOnQuot K) :
    exactCore c K = ⨆ T ∈ AscE184Sect.fixedSylows (Subgroup.zpowers c) K, T :=
  (secMember_zpowers_eq_exactCore hΩ hc2 hK hcK).symm

theorem isSylow2In_exactCore_iff (hΩ : HypOmegaMod p f Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hK : K ∈ Ω) (hcK : c ∈ trivialOnQuot K) {V : Subgroup G} :
    IsSylow2In V (exactCore c K) ↔ IsSylow2In V K ∧ V ≤ Subgroup.centralizer ({c} : Set G) := by
  rw [← secMember_zpowers_eq_exactCore hΩ hc2 hK hcK,
    AscE184Sect.isSylow2In_secMember_iff hc2 (commutator_zpowers_le_iff.mpr hcK),
    mem_fixedSylows_zpowers_iff]


theorem mem_trivialOnQuot_iff_exists_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hK : K ∈ Ω) :
    c ∈ trivialOnQuot K ↔ ∃ R, IsSylow2In R K ∧ R ≤ Subgroup.centralizer ({c} : Set G) := by
  constructor
  · intro h
    obtain ⟨R, hR, hRc⟩ :=
      AscE184Sect.exists_isSylow2In_centralizer hc2 (commutator_zpowers_le_iff.mpr h)
    exact ⟨R, hR, by rwa [centralizer_zpowers_eq_singleton'] at hRc⟩
  · rintro ⟨R, hR, hRc⟩
    have hR8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
    have hRcomm : ∀ r ∈ R, r * c = c * r := fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)
    have hRK : R ≤ conjSub c K := by
      intro r hr
      rw [mem_conjSub_iff]
      have : c⁻¹ * r * c = r := by
        calc c⁻¹ * r * c = c⁻¹ * (r * c) := by group
          _ = c⁻¹ * (c * r) := by rw [hRcomm r hr]
          _ = r := by group
      rw [this]
      exact hR.1 hr
    have hKc : conjSub c K = K :=
      hΩ.eq_of_le_of_le (hΩ.conjInvariant c K hK) hK hR.2.1 (by omega) hRK hR.1
    have hcN : c ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hKc
    have h3 := lemma_3_3_member_element hp hq hΩ hK hR
      (AscE184Sect.exists_orderOf_eq_pow_two hc2 (Subgroup.mem_zpowers c)) hcN hRcomm
    exact ⟨hcN, fun x hx => h3 x hx⟩

theorem mem_tqMembers_iff_exists_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    K ∈ tqMembers Ω c ↔
      K ∈ Ω ∧ ∃ R, IsSylow2In R K ∧ R ≤ Subgroup.centralizer ({c} : Set G) :=
  and_congr_right fun hK => mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hK

theorem sectionFamily_zpowers (hΩ : HypOmegaMod p f Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    AscE184Sect.sectionFamily Ω (Subgroup.zpowers c) = exactFamily Ω c := by
  ext K'
  constructor
  · rintro ⟨K, hK, rfl⟩
    rw [sectionMembers_zpowers] at hK
    exact ⟨K, hK, secMember_zpowers_eq_exactCore hΩ hc2 hK.1 hK.2⟩
  · rintro ⟨K, hK, rfl⟩
    refine ⟨K, ?_, secMember_zpowers_eq_exactCore hΩ hc2 hK.1 hK.2⟩
    rw [sectionMembers_zpowers]
    exact hK

theorem sectionHull_zpowers (hΩ : HypOmegaMod p f Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    AscE184Sect.sectionHull Ω (Subgroup.zpowers c) = exactLayer Ω c := by
  rw [exactLayer_eq_iSup]
  unfold AscE184Sect.sectionHull
  rw [sectionFamily_zpowers hΩ hc2]

omit [Finite G] in
theorem hypOmegaMod_restrictFamily_congr {Φ Φ' : Set (Subgroup G)} {Y Y' : Subgroup G}
    (hΦ : Φ = Φ') (hY : Y = Y') (h : HypOmegaMod p f (restrictFamily Φ Y)) :
    HypOmegaMod p f (restrictFamily Φ' Y') := by
  subst hΦ hY
  exact h

theorem hypOmegaMod_exactPair (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) : HypOmegaMod p f (exactPair Ω c) :=
  hypOmegaMod_restrictFamily_congr (sectionFamily_zpowers hΩ hc2) (sectionHull_zpowers hΩ hc2)
    (AscE184Sect.hypOmegaMod_sectionFamily hp hq hΩ hc2)

end Bridge

end CFSG.ClassicalInvolution.Asc77.ExactLayer
