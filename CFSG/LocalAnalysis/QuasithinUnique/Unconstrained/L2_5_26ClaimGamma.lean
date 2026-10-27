module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraConfining
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingComponents

public section

namespace CFSG.QuasithinUnique.Claim2526

open CFSG.Open CFSG.Quasithin

section Gamma

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem gamma_contradiction (h : UniqueSetting G T M)
    (hnc : ∀ H : Subgroup G, IsGamma0 M H → ¬ CharTwo H) {H' U : Subgroup G} (hchar : CharTwo H')
    (hO2 : pCoreOf 2 H' ≠ ⊥) (hsyl : IsSylowTwoOf U H') (hUT : U ≤ T)
    (hT : Nat.card T = 2 * Nat.card U) (hnot : ¬ H' ≤ M) : False := by
  have hrel : U.relIndex T = 2 := by
    have h1 := Subgroup.card_mul_index (U.subgroupOf T)
    have h2 : Nat.card (U.subgroupOf T) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUT).toEquiv
    rw [h2, hT] at h1
    have hpos : 0 < Nat.card U := Nat.card_pos
    unfold Subgroup.relIndex
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1]; ring)
  have hconf := isConfining_of_relIndex_two_of_exists_local h hUT hrel ⟨H', hO2, hsyl.le, hnot⟩
  have hwit : IsWitnessPair M U H' := ⟨hconf, hsyl.le, hO2, hchar, hnot⟩
  have hG : IsGamma M H' := ⟨hO2, U, H', hwit, le_refl _⟩
  have hG2 : IsGamma2 M H' := by
    refine ⟨hG, fun K hK => ?_⟩
    have hlt := IsGamma.twoPart_lt h hK
    obtain ⟨a, ha⟩ : ∃ a, Nat.card U = 2 ^ a := hsyl.isPGroup.exists_card_eq
    rw [← hsyl.card_eq]
    unfold twoPart at hlt ⊢
    rw [hT, ha, ← pow_succ'] at hlt
    have hab := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    rw [ha]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hnc H' (Or.inr hG2) hchar

end Gamma

section Component

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_of_le {L C A : Subgroup G} (hCA : C ≤ A)
    (h : (L.subgroupOf A).IsSubnormal) : (L.subgroupOf C).IsSubnormal := by
  have h1 : ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).IsSubnormal := h.subgroupOf
  have hcomap : L.subgroupOf C = ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).comap
      (Subgroup.subgroupOfEquivOfLe hCA).symm.toMonoidHom := by
    ext x
    rfl
  rw [hcomap]
  exact h1.comap _

variable [Finite G]

theorem no_component_in_charTwo {M' : Subgroup G} (hM : CharTwo M') {i : G} (hiM : i ∈ M')
    (hi2 : i ^ 2 = 1) {Ki : Subgroup G}
    (hKi : IsComponentIn Ki (Subgroup.centralizer ({i} : Set G))) (hKiM : Ki ≤ M')
    (hsimple : IsSimpleGroup ↥Ki) (hcard : 3 ∣ Nat.card Ki) : False := by
  have hX2 : IsPGroup 2 (Subgroup.zpowers i) := by
    have hord : orderOf i ∣ 2 := orderOf_dvd_of_pow_eq_one hi2
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h2
    · exact (IsPGroup.iff_card (p := 2)).mpr ⟨0, by rw [Nat.card_zpowers, h1]; rfl⟩
    · exact (IsPGroup.iff_card (p := 2)).mpr ⟨1, by rw [Nat.card_zpowers, h2]; rfl⟩
  have hXM : Subgroup.zpowers i ≤ M' := Subgroup.zpowers_le.mpr hiM
  have hY := CharTwo.inf_centralizer hM hXM hX2
  have hcent : Subgroup.centralizer ((Subgroup.zpowers i : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({i} : Set G) :=
    Subgroup.centralizer_le (by simp)
  have hcent' : Subgroup.centralizer ({i} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers i : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact (Commute.zpow_left (show Commute i g from this.symm) n).eq
  have hKiY : Ki ≤ M' ⊓ Subgroup.centralizer ((Subgroup.zpowers i : Subgroup G) : Set G) :=
    le_inf hKiM (hKi.1.trans hcent')
  have hYC : M' ⊓ Subgroup.centralizer ((Subgroup.zpowers i : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({i} : Set G) := inf_le_right.trans hcent
  have hsub := isSubnormal_subgroupOf_of_le hYC hKi.2.2
  have hKchar := EscapingComponents.charTwo_of_isSubnormal hY hKiY hsub
  have hP2 : IsPGroup 2 (pCoreOf 2 Ki) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Ki
  have hPle : pCoreOf 2 Ki ≤ Ki := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 Ki
  have hPnorm : ((pCoreOf 2 Ki).subgroupOf Ki).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Ki)
  have hPbot : pCoreOf 2 Ki = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ((pCoreOf 2 Ki).subgroupOf Ki) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxK := hPle hx
      have : (⟨x, hxK⟩ : ↥Ki) ∈ (pCoreOf 2 Ki).subgroupOf Ki := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hKP : Ki ≤ pCoreOf 2 Ki := by
        intro x hx
        have : (⟨x, hx⟩ : ↥Ki) ∈ (pCoreOf 2 Ki).subgroupOf Ki := by rw [h]; trivial
        exact this
      have hK2 : IsPGroup 2 ↥Ki := hP2.to_le hKP
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hK2
      rw [hn] at hcard
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hcard
      omega
  have hKbot : Ki = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer ((pCoreOf 2 Ki : Subgroup G) : Set G) := by
      rw [hPbot, Subgroup.mem_centralizer_iff]
      intro y hy
      have : y = 1 := hy
      rw [this]
      simp
    have := hKchar ⟨hx, hxc⟩
    rwa [hPbot] at this
  rw [hKbot, Subgroup.card_bot] at hcard
  omega

end Component

end CFSG.QuasithinUnique.Claim2526
