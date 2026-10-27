module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExNear
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarCent

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two.Exact

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z u : G}

theorem card_centralizer_le_of_double_of_l0 (hR2 : RankTwoAlternatingStandard) {m : ℕ}
    (T : Shape G L Q (m + 1) z u) (θ : L ≃* alternatingGroup (Fin (m + 1)))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hbal : FourPointBalance L θ) (hm : 10 ≤ m)
    (hL0 : ∀ (O : OverData G z m) {R : Subgroup (Perm (Fin (m + 3)))}, SecR m R →
      CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G)) → L0Normal O R)
    {S₀ : Finset (Fin (m + 1))} (hS₀ : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ m + 1)
    (hII : CaseIIAt θ z S₀) {w : G} (hw : w ∈ L)
    (hct : ((θ ⟨w, hw⟩ : alternatingGroup (Fin (m + 1))) : Perm (Fin (m + 1))).cycleType =
      {2, 2}) :
    Nat.card (centralizer ({w} : Set G)) ≤ 8 * (m - 1).factorial := by
  classical
  obtain ⟨u₀, T₀, htw⟩ := exists_untwisted T θ hS₀ hkn hII
  set D := nearData_of_untwisted T₀ θ hC hS₀ hkn hII htw with hD
  obtain ⟨M, eM, hCM, hz, hcompat, hconj⟩ := exists_symmetric_overgroup_near hm D
  set O : OverData G z m := ⟨D, M, eM, hCM, hz, hcompat, hconj⟩ with hO
  have h4 : 4 ≤ m + 3 := by omega
  set σ : Perm (Fin (m + 1)) :=
    ((θ ⟨w, hw⟩ : alternatingGroup (Fin (m + 1))) : Perm (Fin (m + 1))) with hσ
  have hσA : σ ∈ alternatingGroup (Fin (m + 1)) := (θ ⟨w, hw⟩).2
  obtain ⟨hw', hew⟩ := swapIota_mem_of_even T₀ θ hσA
  have hwι : (swapIota T₀ θ σ : G) = w := by
    have h1 : θ ⟨swapIota T₀ θ σ, hw'⟩ = θ ⟨w, hw⟩ := Subtype.ext hew
    exact congrArg Subtype.val (θ.injective h1)
  have hwφ : O.φ (inclPerm m σ) = w := by
    rw [OverData.φ_apply]
    change (eM (inclPerm m σ) : G) = w
    rw [hcompat]
    exact hwι
  have hct1 : (inclPerm m σ).cycleType = {2, 2} := by
    rw [inclPerm, Perm.extendDomainHom_apply, Perm.cycleType_extendDomain]
    exact hct
  have hct2 : (emb4 h4 kA4).cycleType = {2, 2} := by
    rw [emb4, Perm.extendDomainHom_apply, Perm.cycleType_extendDomain]
    exact cycleType_mul_swap ⟨0, 1, by decide, rfl⟩ ⟨2, 3, by decide, rfl⟩ (by decide) (by decide)
  obtain ⟨γ, hγ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hct2.trans hct1.symm))
  have hw0 : w = O.φ γ * wA O h4 * (O.φ γ)⁻¹ := by
    rw [← hwφ, ← hγ, map_mul, map_mul, map_inv]
    rfl
  have hOA : CFSG.oddCore (centralizer ({wA O h4} : Set G)) = ⊥ := by
    have hwA : wA O h4 = (O.φ γ)⁻¹ * w * (O.φ γ)⁻¹⁻¹ := by
      rw [hw0]
      group
    rw [hwA]
    exact oddCore_centralizer_conj_eq_bot hbal hw hct _
  rw [hw0, nat_card_centralizer_conj]
  have hw1 : wA O h4 ≠ 1 := wA_ne_one O h4
  have hw2 : orderOf (wA O h4) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact wA_mul_self O h4) hw1
  obtain ⟨hKE, hKy⟩ := isKGroupCat_secP O h4 (isKGroupCat_of_kProper T.std.kProper)
    (fun x hx => centralizer_singleton_ne_top_of_simple T.std.simple T.std.nonab hx)
  exact card_centralizer_wA_le O h4 hR2 (hL0 O (secR_klein (by omega)) hKE)
    (hL0 O (secR_cyc (by omega)) hKy) (isKGroupCat_twoSec_of_std T.std hw1)
    (oddCore_twoSec_eq_bot_of (wA O h4) hw2 hOA) hm

theorem isSwap_permOf_of_partner_of_l0 (hR2 : RankTwoAlternatingStandard) {m : ℕ}
    (T : Shape G L Q (m + 1) z u) (θ : L ≃* alternatingGroup (Fin (m + 1)))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hbal : FourPointBalance L θ) (hm : 10 ≤ m)
    (hL0 : ∀ (O : OverData G z m) {R : Subgroup (Perm (Fin (m + 3)))}, SecR m R →
      CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G)) → L0Normal O R)
    {S₀ : Finset (Fin (m + 1))} (hS₀ : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ m + 1)
    (hII : CaseIIAt θ z S₀) {a : G} (ha : a ∈ centralizer ({z} : Set G)) (hP : a ∈ Partners z) :
    (permOf T.toBase θ ha).IsSwap := by
  classical
  obtain ⟨u₀, T₀, htw⟩ := exists_untwisted T θ hS₀ hkn hII
  set D := nearData_of_untwisted T₀ θ hC hS₀ hkn hII htw with hD
  obtain ⟨M, eM, hCM, hz, hcompat, hconj⟩ := exists_symmetric_overgroup_near hm D
  have h47' : ∀ e₁ e₂ : Perm (Fin (m + 3)), e₁.IsSwap → e₂.IsSwap → e₁ ≠ e₂ →
      e₁ * e₂ = e₂ * e₁ → centralizer ({(eM (e₁ * e₂) : G)} : Set G) ≤ M := by
    intro e₁ e₂ h₁ h₂ hne hc
    set σ₀ : Perm (Fin (m + 1)) :=
      swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩ with hσ₀
    have hs1 : (swap (⟨0, by omega⟩ : Fin (m + 1)) ⟨1, by omega⟩).IsSwap :=
      ⟨_, _, by simp [Fin.ext_iff], rfl⟩
    have hs2 : (swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩).IsSwap :=
      ⟨_, _, by simp [Fin.ext_iff], rfl⟩
    have hne0 : swap (⟨0, by omega⟩ : Fin (m + 1)) ⟨1, by omega⟩ ≠
        swap ⟨2, by omega⟩ ⟨3, by omega⟩ := by
      intro h'
      have := DFunLike.congr_fun h' ⟨0, by omega⟩
      rw [swap_apply_left, swap_apply_of_ne_of_ne (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff])] at this
      simp [Fin.ext_iff] at this
    have hc0 : swap (⟨0, by omega⟩ : Fin (m + 1)) ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩
        = swap ⟨2, by omega⟩ ⟨3, by omega⟩ * swap ⟨0, by omega⟩ ⟨1, by omega⟩ :=
      swap_mul_swap_comm_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    have hct0 : σ₀.cycleType = {2, 2} := cycleType_mul_swap hs1 hs2 hne0 hc0
    have heven : σ₀ ∈ alternatingGroup (Fin (m + 1)) := by
      rw [mem_alternatingGroup, hσ₀, map_mul, hs1.sign_eq, hs2.sign_eq]
      rfl
    obtain ⟨hwL, hew⟩ := swapIota_mem_of_even T₀ θ heven
    have hcard0 := card_centralizer_le_of_double_of_l0 hR2 T₀ θ hC hbal hm hL0 hS₀ hkn hII hwL
      (by rw [hew]; exact hct0)
    have hct : (e₁ * e₂).cycleType = {2, 2} := cycleType_mul_swap h₁ h₂ hne hc
    have hct' : (inclPerm m σ₀).cycleType = {2, 2} := by
      have hi1 := inclPerm_isSwap (m := m) hs1
      have hi2 := inclPerm_isSwap (m := m) hs2
      rw [hσ₀, map_mul]
      refine cycleType_mul_swap hi1 hi2 (fun h' => hne0 (Perm.extendDomainHom_injective _ h'))
        (by rw [← map_mul, ← map_mul, hc0])
    obtain ⟨γ, hγ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hct'.trans hct.symm))
    have hw : (eM (e₁ * e₂) : G) =
        (eM γ : G) * (swapIota T₀ θ σ₀ : G) * (eM γ : G)⁻¹ := by
      rw [← hγ, coe_eM_mul, coe_eM_mul, map_inv, hcompat]
      rfl
    have hcard : Nat.card (centralizer ({(eM (e₁ * e₂) : G)} : Set G)) ≤
        8 * (m - 1).factorial := by
      rw [hw, nat_card_centralizer_conj]
      exact hcard0
    set K : Subgroup G := (centralizer ({e₁ * e₂} : Set (Perm (Fin (m + 3))))).map
      (M.subtype.comp eM.toMonoidHom) with hK
    have hKle : K ≤ centralizer ({(eM (e₁ * e₂) : G)} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ centralizer ({e₁ * e₂} : Set (Perm (Fin (m + 3)))) := hx
      show (eM x : G) ∈ _
      rw [mem_centralizer_singleton_iff] at hx' ⊢
      exact eM_comm eM hx'
    have hKcard : Nat.card K = 8 * (m - 1).factorial := by
      rw [hK, Subgroup.card_map_of_injective (Subtype.coe_injective.comp eM.injective),
        nat_card_centralizer_of_cycleType_two_two hct, Fintype.card_fin]
      congr 2
    have hKeq : K = centralizer ({(eM (e₁ * e₂) : G)} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hKle (by rw [hKcard]; exact hcard)
    rw [← hKeq]
    rintro _ ⟨x, -, rfl⟩
    exact (eM x).2
  exact isSwap_π_of_partner hm D eM hCM hz hcompat hconj h47' hP

theorem caseII_of_double_of_l0 (hR2 : RankTwoAlternatingStandard) {m : ℕ}
    (T : Shape G L Q (m + 1) z u) (θ : L ≃* alternatingGroup (Fin (m + 1)))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hbal : FourPointBalance L θ) (hm : 10 ≤ m)
    (hL0 : ∀ (O : OverData G z m) {R : Subgroup (Perm (Fin (m + 3)))}, SecR m R →
      CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G)) → L0Normal O R)
    {S₀ : Finset (Fin (m + 1))} (hS₀ : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ m + 1)
    (hII : CaseIIAt θ z S₀) :
    CaseII θ T.hn (L ⊔ zpowers u) z ∨ CaseII θ T.hn (L ⊔ zpowers (u * z)) z := by
  have hz2 : z * z = 1 := T.cyc.mul_self
  have hsw : ∀ (a : G) (ha : a ∈ centralizer ({z} : Set G)), a ∈ Partners z →
      (permOf T.toBase θ ha).IsSwap := fun a ha hP =>
    isSwap_permOf_of_partner_of_l0 hR2 T θ hC hbal hm hL0 hS₀ hkn hII ha hP
  obtain ⟨c, hc, htw⟩ := caseII_twist T θ hS₀ hkn hII
  rcases hc with hc | hc
  · left
    rw [hc] at htw
    exact caseII_of_caseIIW T.cyc hC
      (caseIIW_of_untwisted T θ hsw (fun τ hτ => by simpa using htw τ hτ))
  · right
    rw [hc] at htw
    refine caseII_of_caseIIW T.cyc hC (caseIIW_of_untwisted T.mul_z θ hsw ?_)
    intro τ hτ
    obtain ⟨h1, h2⟩ := htw τ hτ
    rw [hz2, one_mul] at h2
    rw [swapIota_mul_z_eq T θ hτ.sign_eq, ← mul_assoc, hz2, one_mul]
    exact ⟨h1, h2⟩

end CFSG.OddStandard.AltStdCycTwo.Two.Exact
