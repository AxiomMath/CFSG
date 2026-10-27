module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open Matrix CFSG.Open

abbrev CoverSL2 : Type := SpecialLinearGroup (Fin 2) (ZMod 2)

private theorem sl2_sq_cube (g : CoverSL2) : (g ^ 2) ^ 3 = 1 := by
  revert g; decide +revert

private theorem sl2_conj_sq (u g : CoverSL2) :
    g * u ^ 2 * g⁻¹ = u ^ 2 ∨ g * u ^ 2 * g⁻¹ = (u ^ 2)⁻¹ := by
  revert u g; decide +revert

private theorem sl2_exists_inv (u : CoverSL2) (h : u ^ 3 = 1) : ∃ s : CoverSL2, s * u * s⁻¹ = u⁻¹ := by
  revert u; decide +revert

private theorem sl2_pow_six (g : CoverSL2) : g ^ 6 = 1 := by
  revert g; decide +revert

section S3Facts

variable {Γ : Type*} [Group Γ] {L : Subgroup Γ}

theorem sl2_sq_pow_three (e : ↥L ≃* CoverSL2) {u : Γ} (hu : u ∈ L) : (u ^ 2) ^ 3 = 1 := by
  have h : ((⟨u, hu⟩ : ↥L) ^ 2) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_pow, map_one]
    exact sl2_sq_cube _
  simpa using congrArg Subtype.val h

theorem sl2_conj_sq_cases (e : ↥L ≃* CoverSL2) {u g : Γ} (hu : u ∈ L) (hg : g ∈ L) :
    g * u ^ 2 * g⁻¹ = u ^ 2 ∨ g * u ^ 2 * g⁻¹ = (u ^ 2)⁻¹ := by
  rcases sl2_conj_sq (e ⟨u, hu⟩) (e ⟨g, hg⟩) with h | h
  · left
    have : (⟨g, hg⟩ : ↥L) * ⟨u, hu⟩ ^ 2 * (⟨g, hg⟩ : ↥L)⁻¹ = ⟨u, hu⟩ ^ 2 := by
      apply e.injective
      simp only [map_mul, map_inv, map_pow]
      exact h
    simpa using congrArg Subtype.val this
  · right
    have : (⟨g, hg⟩ : ↥L) * ⟨u, hu⟩ ^ 2 * (⟨g, hg⟩ : ↥L)⁻¹ = (⟨u, hu⟩ ^ 2)⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv, map_pow]
      exact h
    simpa using congrArg Subtype.val this

theorem sl2_exists_inv' (e : ↥L ≃* CoverSL2) {u : Γ} (hu : u ∈ L) (h3 : u ^ 3 = 1) :
    ∃ s ∈ L, s * u * s⁻¹ = u⁻¹ := by
  have h3' : (⟨u, hu⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  have h : (e ⟨u, hu⟩) ^ 3 = 1 := by rw [← map_pow, h3', map_one]
  obtain ⟨s, hs⟩ := sl2_exists_inv _ h
  refine ⟨((e.symm s : ↥L) : Γ), (e.symm s).2, ?_⟩
  have : (e.symm s : ↥L) * ⟨u, hu⟩ * (e.symm s : ↥L)⁻¹ = (⟨u, hu⟩ : ↥L)⁻¹ := by
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hs
  simpa using congrArg Subtype.val this

theorem sl2_pow_six' (e : ↥L ≃* CoverSL2) {u : Γ} (hu : u ∈ L) : u ^ 6 = 1 := by
  have h : (⟨u, hu⟩ : ↥L) ^ 6 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact sl2_pow_six _
  simpa using congrArg Subtype.val h

end S3Facts

section Fam

variable {Γ : Type*} [Group Γ]

structure S3Fam (I : Finset (Subgroup Γ)) : Prop where
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  indep : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥
  sl2 : ∀ L ∈ I, Nonempty (↥L ≃* CoverSL2)

namespace S3Fam

variable [DecidableEq (Subgroup Γ)] {I : Finset (Subgroup Γ)} (hI : S3Fam I)
include hI

omit [DecidableEq (Subgroup Γ)] in
theorem commute_iSup {L₀ : Subgroup Γ} (hL₀ : L₀ ∈ I) {F : Finset (Subgroup Γ)} (hF : F ⊆ I)
    (hL₀F : L₀ ∉ F) {u y : Γ} (hu : u ∈ L₀) (hy : y ∈ (⨆ L ∈ F, L : Subgroup Γ)) :
    u * y = y * u := by
  have hle : (⨆ L ∈ F, L : Subgroup Γ) ≤ Subgroup.centralizer ({u} : Set Γ) := by
    refine iSup₂_le fun L hL v hv => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hI.comm L (hF hL) L₀ hL₀ (fun h => hL₀F (h ▸ hL)) v hv u hu
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

omit [DecidableEq (Subgroup Γ)] in
theorem inf_iSup_eq_bot {L₀ : Subgroup Γ} (hL₀ : L₀ ∈ I) {F : Finset (Subgroup Γ)} (hF : F ⊆ I)
    (hL₀F : L₀ ∉ F) : L₀ ⊓ (⨆ L ∈ F, L : Subgroup Γ) = ⊥ := by
  refine eq_bot_iff.2 ?_
  refine le_trans (inf_le_inf_left _ ?_) (hI.indep L₀ hL₀).le
  refine iSup₂_le fun L hL => ?_
  exact le_iSup₂_of_le L (hF hL) (le_iSup (fun _ : L ≠ L₀ => L) (fun h => hL₀F (h ▸ hL)))

theorem exists_mul_of_mem_insert {L₀ : Subgroup Γ} (hL₀ : L₀ ∈ I) {F : Finset (Subgroup Γ)}
    (hF : F ⊆ I) (hL₀F : L₀ ∉ F) {z : Γ}
    (hz : z ∈ (⨆ L ∈ insert L₀ F, L : Subgroup Γ)) :
    ∃ u ∈ L₀, ∃ y ∈ (⨆ L ∈ F, L : Subgroup Γ), z = u * y := by
  classical
  rw [Finset.iSup_insert] at hz
  have hc : L₀ ≤ Subgroup.centralizer ((⨆ L ∈ F, L : Subgroup Γ) : Set Γ) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hI.commute_iSup hL₀ hF hL₀F hu hy).symm
  have h := Subgroup.coe_mul_of_left_le_normalizer_right L₀ (⨆ L ∈ F, L : Subgroup Γ)
    (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hz' : z ∈ ((L₀ ⊔ ⨆ L ∈ F, L : Subgroup Γ) : Set Γ) := hz
  rw [h] at hz'
  obtain ⟨u, hu, y, hy, rfl⟩ := hz'
  exact ⟨u, hu, y, hy, rfl⟩

theorem sq_mem_pCore_of_mem {L : Subgroup Γ} (hL : L ∈ I) {u : Γ} (hu : u ∈ L) :
    u ^ 2 ∈ CFSG.Open.pCoreOf 3 (⨆ L ∈ I, L : Subgroup Γ) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hI.sl2 L hL
  set H : Subgroup Γ := ⨆ L ∈ I, L with hH
  have hu2L : u ^ 2 ∈ L := L.pow_mem hu 2
  have hu2 : u ^ 2 ∈ H := Subgroup.mem_iSup_of_mem L (Subgroup.mem_iSup_of_mem hL hu2L)
  have hconj : ∀ g : Γ, g * u ^ 2 * g⁻¹ ∈ Subgroup.zpowers (u ^ 2) →
      ∀ y ∈ Subgroup.zpowers (u ^ 2), g * y * g⁻¹ ∈ Subgroup.zpowers (u ^ 2) := by
    intro g hg y hy
    obtain ⟨n, rfl⟩ := hy
    have : g * (u ^ 2) ^ n * g⁻¹ = (g * u ^ 2 * g⁻¹) ^ n := (conj_zpow).symm
    rw [this]
    exact Subgroup.zpow_mem _ hg n
  have hLmem : ∀ g ∈ L, g * u ^ 2 * g⁻¹ ∈ Subgroup.zpowers (u ^ 2) := by
    intro g hg
    rcases sl2_conj_sq_cases e hu hg with h | h
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hnorm : ∀ g : Γ, g * u ^ 2 * g⁻¹ ∈ Subgroup.zpowers (u ^ 2) →
      g⁻¹ * u ^ 2 * g⁻¹⁻¹ ∈ Subgroup.zpowers (u ^ 2) →
      g ∈ Subgroup.normalizer (Subgroup.zpowers (u ^ 2) : Set Γ) := fun g h1 h2 =>
    CFSG.Quasithin.B6.mem_normalizer_of_forall_mem (hconj g h1)
      (fun y hy => by simpa using hconj g⁻¹ h2 y hy)
  have hN : H ≤ Subgroup.normalizer (Subgroup.zpowers (u ^ 2) : Set Γ) := by
    refine iSup₂_le fun L' hL' g hg => ?_
    by_cases hLL' : L' = L
    · rw [hLL'] at hg
      exact hnorm g (hLmem g hg) (hLmem g⁻¹ (L.inv_mem hg))
    · have hc : g * u ^ 2 = u ^ 2 * g := hI.comm L' hL' L hL hLL' g hg (u ^ 2) hu2L
      have h1 : g * u ^ 2 * g⁻¹ = u ^ 2 := by rw [hc]; group
      have h2 : g⁻¹ * u ^ 2 * g⁻¹⁻¹ = u ^ 2 := by
        have : g⁻¹ * u ^ 2 = u ^ 2 * g⁻¹ := by
          calc g⁻¹ * u ^ 2 = g⁻¹ * (u ^ 2 * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * u ^ 2) * g⁻¹ := by rw [hc]
            _ = u ^ 2 * g⁻¹ := by group
        rw [this]; group
      exact hnorm g (by rw [h1]; exact Subgroup.mem_zpowers _)
        (by rw [h2]; exact Subgroup.mem_zpowers _)
  have hp : IsPGroup 3 (Subgroup.zpowers (u ^ 2)) := by
    have h3 : orderOf (u ^ 2) ∣ 3 := orderOf_dvd_of_pow_eq_one (sl2_sq_pow_three e hu)
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 (Subgroup.zpowers_le.2 hu2) hN hp
    (Subgroup.mem_zpowers _)

theorem sq_mem_pCore :
    ∀ F : Finset (Subgroup Γ), F ⊆ I → ∀ z ∈ (⨆ L ∈ F, L : Subgroup Γ),
      z ^ 2 ∈ CFSG.Open.pCoreOf 3 (⨆ L ∈ I, L : Subgroup Γ) := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _ z hz
    have hbot : (⨆ L ∈ (∅ : Finset (Subgroup Γ)), L : Subgroup Γ) = ⊥ := by simp
    rw [hbot, Subgroup.mem_bot] at hz
    subst hz
    simp
  | insert L₀ F hL₀F ih =>
    intro hFI z hz
    have hL₀ : L₀ ∈ I := hFI (Finset.mem_insert_self _ _)
    have hF : F ⊆ I := fun L hL => hFI (Finset.mem_insert_of_mem hL)
    obtain ⟨u, hu, y, hy, rfl⟩ := hI.exists_mul_of_mem_insert hL₀ hF hL₀F hz
    have hcomm : Commute u y := hI.commute_iSup hL₀ hF hL₀F hu hy
    rw [hcomm.mul_pow]
    exact mul_mem (hI.sq_mem_pCore_of_mem hL₀ hu) (ih hF y hy)

theorem pow_six :
    ∀ F : Finset (Subgroup Γ), F ⊆ I → ∀ z ∈ (⨆ L ∈ F, L : Subgroup Γ), z ^ 6 = 1 := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _ z hz
    have hbot : (⨆ L ∈ (∅ : Finset (Subgroup Γ)), L : Subgroup Γ) = ⊥ := by simp
    rw [hbot, Subgroup.mem_bot] at hz
    subst hz
    simp
  | insert L₀ F hL₀F ih =>
    intro hFI z hz
    have hL₀ : L₀ ∈ I := hFI (Finset.mem_insert_self _ _)
    have hF : F ⊆ I := fun L hL => hFI (Finset.mem_insert_of_mem hL)
    obtain ⟨u, hu, y, hy, rfl⟩ := hI.exists_mul_of_mem_insert hL₀ hF hL₀F hz
    have hcomm : Commute u y := hI.commute_iSup hL₀ hF hL₀F hu hy
    obtain ⟨e⟩ := hI.sl2 L₀ hL₀
    rw [hcomm.mul_pow, sl2_pow_six' e hu, ih hF y hy, one_mul]

theorem pow_three_of_mem_pCore [Finite Γ] {y : Γ}
    (hy : y ∈ CFSG.Open.pCoreOf 3 (⨆ L ∈ I, L : Subgroup Γ)) : y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSig : y ∈ (⨆ L ∈ I, L : Subgroup Γ) := CFSG.LieType.BorelTits.pCoreOf_le 3 _ hy
  have h6 : y ^ 6 = 1 := hI.pow_six I subset_rfl y hSig
  have hp := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 (⨆ L ∈ I, L : Subgroup Γ)
  obtain ⟨k, hk⟩ := hp ⟨y, hy⟩
  have h3k : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd1 : orderOf y ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hd2 : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h3k
  obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd2
  have hj : j ≤ 1 := by
    by_contra h
    push Not at h
    have h9 : 9 ∣ 3 ^ j := by
      have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 h
      simpa using this
    rw [← hjo] at h9
    have := h9.trans hd1
    omega
  have hj' : orderOf y ∣ 3 := by
    rw [hjo]
    interval_cases j <;> simp
  exact orderOf_dvd_iff_pow_eq_one.1 hj'

theorem exists_dec {KA KB : Subgroup Γ} (hcov : ∀ L ∈ I, L ≤ KA ∨ L ≤ KB) :
    ∀ F : Finset (Subgroup Γ), F ⊆ I → ∀ y ∈ (⨆ L ∈ F, L : Subgroup Γ), y ^ 3 = 1 →
      ∃ a ∈ KA, ∃ b ∈ KB, ∃ s ∈ (⨆ L ∈ F, L : Subgroup Γ),
        a ∈ (⨆ L ∈ F, L : Subgroup Γ) ∧ b ∈ (⨆ L ∈ F, L : Subgroup Γ) ∧
        y = a * b ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ s * a * s⁻¹ = a⁻¹ ∧ s * b * s⁻¹ = b := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _ y hy hy3
    have hbot : (⨆ L ∈ (∅ : Finset (Subgroup Γ)), L : Subgroup Γ) = ⊥ := by simp
    rw [hbot, Subgroup.mem_bot] at hy
    subst hy
    refine ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, one_mem _, one_mem _, by simp, by simp,
      by simp, by simp⟩
  | insert L₀ F hL₀F ih =>
    intro hFI z hz hz3
    have hL₀ : L₀ ∈ I := hFI (Finset.mem_insert_self _ _)
    have hF : F ⊆ I := fun L hL => hFI (Finset.mem_insert_of_mem hL)
    obtain ⟨u, hu, y, hy, rfl⟩ := hI.exists_mul_of_mem_insert hL₀ hF hL₀F hz
    have hcomm : u * y = y * u := hI.commute_iSup hL₀ hF hL₀F hu hy
    have hcomm' : Commute u y := hcomm
    rw [hcomm'.mul_pow] at hz3
    have hu3 : u ^ 3 = 1 := by
      have h1 : u ^ 3 = (y ^ 3)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; exact hz3
      have h2 : u ^ 3 ∈ L₀ ⊓ (⨆ L ∈ F, L : Subgroup Γ) :=
        ⟨L₀.pow_mem hu 3, by rw [h1]; exact Subgroup.inv_mem _ ((⨆ L ∈ F, L : Subgroup Γ).pow_mem hy 3)⟩
      rw [hI.inf_iSup_eq_bot hL₀ hF hL₀F] at h2
      exact Subgroup.mem_bot.1 h2
    have hy3 : y ^ 3 = 1 := by rw [hu3, one_mul] at hz3; exact hz3
    obtain ⟨a', ha'A, b', hb'B, s', hs', ha'S, hb'S, hya, ha3, hb3, hsa, hsb⟩ := ih hF y hy hy3
    obtain ⟨e⟩ := hI.sl2 L₀ hL₀
    obtain ⟨su, hsuL, hsu⟩ := sl2_exists_inv' e hu hu3
    have hSle : (⨆ L ∈ F, L : Subgroup Γ) ≤ (⨆ L ∈ insert L₀ F, L : Subgroup Γ) := by
      rw [Finset.iSup_insert]; exact le_sup_right
    have hL₀le : L₀ ≤ (⨆ L ∈ insert L₀ F, L : Subgroup Γ) := by
      rw [Finset.iSup_insert]; exact le_sup_left
    have hu_a : u * a' = a' * u := hI.commute_iSup hL₀ hF hL₀F hu ha'S
    have hu_b : u * b' = b' * u := hI.commute_iSup hL₀ hF hL₀F hu hb'S
    have hu_s : u * s' = s' * u := hI.commute_iSup hL₀ hF hL₀F hu hs'
    have hsu_a : su * a' = a' * su := hI.commute_iSup hL₀ hF hL₀F hsuL ha'S
    have hsu_b : su * b' = b' * su := hI.commute_iSup hL₀ hF hL₀F hsuL hb'S
    have hsu_s : su * s' = s' * su := hI.commute_iSup hL₀ hF hL₀F hsuL hs'
    rcases hcov L₀ hL₀ with hLA | hLB
    · refine ⟨u * a', KA.mul_mem (hLA hu) ha'A, b', hb'B, su * s',
        (⨆ L ∈ insert L₀ F, L : Subgroup Γ).mul_mem (hL₀le hsuL) (hSle hs'),
        (⨆ L ∈ insert L₀ F, L : Subgroup Γ).mul_mem (hL₀le hu) (hSle ha'S), hSle hb'S, ?_, ?_, hb3,
        ?_, ?_⟩
      · rw [hya]; group
      · rw [Commute.mul_pow (show Commute u a' from hu_a), hu3, ha3, one_mul]
      · have h1 : s' * (u * a') * s'⁻¹ = u * a'⁻¹ := by
          calc s' * (u * a') * s'⁻¹ = (s' * u) * a' * s'⁻¹ := by group
            _ = (u * s') * a' * s'⁻¹ := by rw [← hu_s]
            _ = u * (s' * a' * s'⁻¹) := by group
            _ = u * a'⁻¹ := by rw [hsa]
        have h2 : su * a'⁻¹ * su⁻¹ = a'⁻¹ := by
          have : su * a' * su⁻¹ = a' := by
            calc su * a' * su⁻¹ = (a' * su) * su⁻¹ := by rw [hsu_a]
              _ = a' := by group
          calc su * a'⁻¹ * su⁻¹ = (su * a' * su⁻¹)⁻¹ := by group
            _ = a'⁻¹ := by rw [this]
        have h3 : (u * a')⁻¹ = u⁻¹ * a'⁻¹ := by
          have : u⁻¹ * a'⁻¹ = a'⁻¹ * u⁻¹ := by
            have h := Commute.inv_inv (show Commute u a' from hu_a)
            exact h.eq
          rw [_root_.mul_inv_rev, this]
        calc su * s' * (u * a') * (su * s')⁻¹ = su * (s' * (u * a') * s'⁻¹) * su⁻¹ := by group
          _ = su * (u * a'⁻¹) * su⁻¹ := by rw [h1]
          _ = (su * u * su⁻¹) * (su * a'⁻¹ * su⁻¹) := by group
          _ = (u * a')⁻¹ := by rw [hsu, h2, h3]
      · calc su * s' * b' * (su * s')⁻¹ = su * (s' * b' * s'⁻¹) * su⁻¹ := by group
          _ = su * b' * su⁻¹ := by rw [hsb]
          _ = b' := by
            calc su * b' * su⁻¹ = (b' * su) * su⁻¹ := by rw [hsu_b]
              _ = b' := by group
    · refine ⟨a', ha'A, u * b', KB.mul_mem (hLB hu) hb'B, s', hSle hs', hSle ha'S,
        (⨆ L ∈ insert L₀ F, L : Subgroup Γ).mul_mem (hL₀le hu) (hSle hb'S), ?_, ha3, ?_, hsa, ?_⟩
      · rw [hya]
        calc u * (a' * b') = (u * a') * b' := by group
          _ = (a' * u) * b' := by rw [hu_a]
          _ = a' * (u * b') := by group
      · rw [Commute.mul_pow (show Commute u b' from hu_b), hu3, hb3, one_mul]
      · calc s' * (u * b') * s'⁻¹ = (s' * u) * b' * s'⁻¹ := by group
          _ = (u * s') * b' * s'⁻¹ := by rw [← hu_s]
          _ = u * (s' * b' * s'⁻¹) := by group
          _ = u * b' := by rw [hsb]

end S3Fam

end Fam



end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
