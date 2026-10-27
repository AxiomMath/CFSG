module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511F
public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsD
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem exists_two_ne_one_of_card_four {X : Type*} [Group X] (V : Subgroup X)
    (hV4 : Nat.card V = 4) : ∃ x ∈ V, ∃ y ∈ V, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype V := Fintype.ofFinite V
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx1⟩ := exists_ne (1 : V)
  obtain ⟨y, hy1, hyx⟩ : ∃ y : V, y ≠ 1 ∧ y ≠ x := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset V) ⊆ {1, x} := by
      intro v _
      by_cases hv : v = 1
      · simp [hv]
      · simp [hno v hv]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hV4] at this
    have h2 : ({1, x} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  exact ⟨x, x.2, y, y.2, fun h => hx1 (Subtype.ext h), fun h => hy1 (Subtype.ext h),
    fun h => hyx (Subtype.ext h).symm⟩

theorem eq_one_or_eq_of_card_le_two {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : Nat.card H ≤ 2) {n x : X} (hn : n ∈ H) (hn1 : n ≠ 1) (hx : x ∈ H) :
    x = 1 ∨ x = n := by
  classical
  by_contra hne
  push Not at hne
  have : Fintype H := Fintype.ofFinite H
  have h3 : ({⟨1, one_mem H⟩, ⟨n, hn⟩, ⟨x, hx⟩} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h1 => hne.2 (congrArg Subtype.val h1).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h1 => hn1 (congrArg Subtype.val h1).symm,
        fun h1 => hne.1 (congrArg Subtype.val h1).symm⟩
  have h4 := Finset.card_le_univ ({⟨1, one_mem H⟩, ⟨n, hn⟩, ⟨x, hx⟩} : Finset H)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
include h

omit [Finite 𝕊] in
include ε in
theorem conj_injective : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊) := by
  intro a b hab
  have h1 : b⁻¹ * a ∈ center 𝕊 := by
    rw [mem_center_iff]
    intro g
    have h2 := congrArg (fun φ : MulAut 𝕊 => φ g) hab
    simp only [MulAut.conj_apply] at h2
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h2]
      _ = b⁻¹ * a * g := by group
  rw [h.center_eq_bot ε, mem_bot, inv_mul_eq_one] at h1
  exact h1.symm

omit [Finite 𝕊] in
theorem exists_lift_of_fixed_W {W : Subgroup G} (hWS : W ≤ S) {r : G}
    (hW : ∀ w ∈ W, actG L ε w = 1 ∨ actG L ε w = actG L ε r) {x : 𝕊}
    (hx : actG L ε r x = x) :
    ∃ k : G, ∃ hk : k ∈ L, k ∈ centralizer (W : Set G) ∧ psi L ε ⟨k, hk⟩ = x :=
  exists_lift_of_fixed_pgroup ε (h.isPGroup_S.to_le hWS) (hWS.trans h.S_le) fun p hp => by
    rcases hW p hp with h1 | h1
    · rw [h1, MulAut.one_apply]
    · rw [h1]
      exact hx

theorem mem_oddCoreIn_of_mem_coreActionKernel_footeF (hKF : Foote5FieldCentralizerC)
    (h𝕊 : FooteSimpleType 𝕊) {r : G} (hrS : r ∈ S) (hr2 : r * r = 1)
    (hrinn : actG L ε r ∉ innAut5 𝕊) (hrR : ∀ ρ ∈ S ⊓ L, r * ρ = ρ * r)
    {W : Subgroup G} (hWS : W ≤ S) (hrW : r ∈ W)
    (hW : ∀ w ∈ W, actG L ε w = 1 ∨ actG L ε w = actG L ε r)
    {w : G} (hwW : w ∈ W) (hwL : w ∉ L) (hwF : IsTwoComponentAt w (footeF L₀ w))
    (hwF' : footeF L₀ w ∈ footeFamilyOf L₀) {y : G} (hyL : y ∈ L)
    (hyW : y ∈ centralizer (W : Set G)) (hyC : y ∈ coreActionKernel (footeF L₀ w)) :
    y ∈ oddCoreIn L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrN := h.S_le hrS
  set β := actG L ε r with hβ
  have hβ2 : β * β = 1 := by rw [hβ, ← actG_mul ε hrN hrN, hr2, actG_one]
  have hβfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), β ρ = ρ := (h.actG_fix_iff ε hrS).mpr hrR
  obtain ⟨M, hMfix, hMcard, hMnorm, hMaut⟩ := hKF 𝕊 h𝕊 β hβ2 hrinn ⟨h.Rbar ε, hβfix⟩
  set B := footeF L₀ w with hB
  set N : Subgroup G := L ⊓ centralizer (W : Set G) ⊓ coreActionKernel B with hN
  set Nb : Subgroup 𝕊 := (N.subgroupOf L).map (psi L ε) with hNb
  set Cb : Subgroup 𝕊 := MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id 𝕊) with hCb
  have hNL : N ≤ L := inf_le_left.trans inf_le_left
  have hCwB : ∀ k ∈ centralizer (W : Set G), k ∈ normalizer (coreActionKernel B : Set G) :=
    fun k hk => normalizer_le_normalizer_coreActionKernel B
      (le_normalizer_of_mem_footeFamilyOf h.sec4.huniq hwF hwF'
        (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hk w hwW).symm))
  have hNbC : Nb ≤ Cb := by
    rintro _ ⟨⟨k, hkL⟩, hkN, rfl⟩
    have hk := mem_subgroupOf.mp hkN
    have hkW : k ∈ centralizer (W : Set G) := (mem_inf.mp (mem_inf.mp hk).1).2
    change β (psi L ε ⟨k, hkL⟩) = psi L ε ⟨k, hkL⟩
    rw [hβ, actG_psi ε hrN]
    congr 1
    apply Subtype.ext
    change r * k * r⁻¹ = k
    rw [mem_centralizer_iff.mp hkW r hrW, mul_inv_cancel_right]
  have hlift : ∀ m ∈ Cb, ∃ k : G, ∃ hk : k ∈ L, k ∈ centralizer (W : Set G) ∧
      psi L ε ⟨k, hk⟩ = m := fun m hm => h.exists_lift_of_fixed_W ε hWS hW hm
  have hNbn : ∀ m ∈ Cb, ∀ x ∈ Nb, m * x * m⁻¹ ∈ Nb := by
    intro m hm x hx
    obtain ⟨k, hkL, hkW, rfl⟩ := hlift m hm
    obtain ⟨⟨y', hy'L⟩, hy'N, rfl⟩ := hx
    have hy' := mem_subgroupOf.mp hy'N
    have hy'W : y' ∈ centralizer (W : Set G) := (mem_inf.mp (mem_inf.mp hy').1).2
    have hy'C : y' ∈ coreActionKernel B := (mem_inf.mp hy').2
    have hkyL : k * y' * k⁻¹ ∈ L := mul_mem (mul_mem hkL hy'L) (inv_mem hkL)
    refine ⟨⟨k * y' * k⁻¹, hkyL⟩, mem_subgroupOf.mpr (mem_inf.mpr ⟨mem_inf.mpr ⟨hkyL,
      mul_mem (mul_mem hkW hy'W) (inv_mem hkW)⟩, ?_⟩), ?_⟩
    · exact (mem_normalizer_iff.mp (hCwB k hkW) y').mp hy'C
    · rw [show (⟨k * y' * k⁻¹, hkyL⟩ : L) = ⟨k, hkL⟩ * ⟨y', hy'L⟩ * ⟨k, hkL⟩⁻¹ from rfl,
        map_mul, map_mul, map_inv]
  have hMC : M ≤ Cb := fun m hm => hMfix m hm
  have hNb1 : Nb = ⊥ := by
    by_contra hne
    obtain ⟨V, hV, hVN⟩ : ∃ V : Subgroup 𝕊, IsKleinFour V ∧ V ≤ Nb := by
      by_cases hNM : Nb ⊓ M = ⊥
      · exfalso
        have hdisj : Disjoint Nb M := disjoint_iff.mpr hNM
        have hcard := card_sup_eq_mul_of_disjoint_of_le_normalizer Nb M
          (fun m hm => mem_normalizer_iff.mpr fun x => ⟨fun hx => hNbn m (hMC hm) x hx,
            fun hx => by
              have h1 := hNbn m⁻¹ (inv_mem (hMC hm)) _ hx
              rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at h1⟩) hdisj
        have hle := Subgroup.card_le_of_le (sup_le hNbC hMC)
        have hM0 : 0 < Nat.card M := Nat.card_pos
        have hNb2 : Nat.card Nb ≤ 2 := by
          rw [hcard] at hle
          by_contra hlt
          push Not at hlt
          have h3 : 3 * Nat.card M ≤ Nat.card Nb * Nat.card M := Nat.mul_le_mul_right _ hlt
          have h4 : 3 * Nat.card M ≤ 2 * Nat.card M := h3.trans (hle.trans hMcard)
          omega
        obtain ⟨⟨n, hnN⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
        have hn1' : n ≠ 1 := fun h1 => hn1 (Subtype.ext h1)
        have hNbeq : ∀ x ∈ Nb, x = 1 ∨ x = n := fun x hx =>
          eq_one_or_eq_of_card_le_two hNb2 hnN hn1' hx
        have hnM : ∀ m ∈ M, MulAut.conj n m = m := by
          intro m hm
          have h1 := hNbn m⁻¹ (inv_mem (hMC hm)) n hnN
          rcases hNbeq _ h1 with h2 | h2
          · exfalso
            apply hn1'
            calc n = m * (m⁻¹ * n * m⁻¹⁻¹) * m⁻¹ := by group
              _ = 1 := by rw [h2]; group
          · rw [MulAut.conj_apply]
            calc n * m * n⁻¹ = m * (m⁻¹ * n * m⁻¹⁻¹) * n⁻¹ := by group
              _ = m := by rw [h2]; group
        rcases hMaut (MulAut.conj n) hnM with h1 | h1
        · exact hn1' (h.conj_injective ε (h1.trans (map_one _).symm))
        · exact hrinn (h1 ▸ ⟨n, rfl⟩)
      · obtain ⟨V, hV, hVle⟩ := hMnorm (Nb ⊓ M) inf_le_right (fun m hm x hx =>
          mem_inf.mpr ⟨hNbn m (hMC hm) x (mem_inf.mp hx).1,
            mul_mem (mul_mem hm (mem_inf.mp hx).2) (inv_mem hm)⟩) hNM
        exact ⟨V, hV, hVle.trans inf_le_left⟩
    obtain ⟨a, haV, b, hbV, ha1, hb1, hab⟩ := exists_two_ne_one_of_card_four V hV.card_four
    have ha2 : a * a = 1 := by rw [← sq]; exact sq_eq_one_of_isKleinFour hV haV
    have hb2 : b * b = 1 := by rw [← sq]; exact sq_eq_one_of_isKleinFour hV hbV
    have habc : a * b = b * a :=
      commute_of_sq_eq_one (fun x hx => by rw [← sq]; exact sq_eq_one_of_isKleinFour hV hx) haV
        hbV
    obtain ⟨u, huN, v, hvN, huL, hvL, hψu, hψv, hu2, hv2, huv⟩ :=
      exists_commuting_involution_lifts ε (hVN haV) (hVN hbV) ha2 hb2 ha1 hb1 habc
    have hu1 : u ≠ 1 := fun h1 => ha1 (by
      rw [← hψu, show (⟨u, huL⟩ : L) = 1 from Subtype.ext h1, map_one])
    have hv1 : v ≠ 1 := fun h1 => hb1 (by
      rw [← hψv, show (⟨v, hvL⟩ : L) = 1 from Subtype.ext h1, map_one])
    have huv' : u ≠ v := fun h1 => hab (by
      rw [← hψu, ← hψv]
      congr 1
      exact Subtype.ext h1)
    set U := kleinFourOfCommutingInvolutions u v hu2 hv2 huv with hU
    have hU4 : Nat.card U = 4 :=
      (isKleinFour_kleinFourOfCommutingInvolutions u v hu2 hv2 hu1 hv1 huv' huv).card_four
    have hUmem : ∀ x ∈ U, x ∈ N := fun x hx => by
      rcases (mem_kleinFour_iff hu2 hv2 huv).mp hx with rfl | rfl | rfl | rfl
      · exact mul_mem huN hvN
      · exact huN
      · exact hvN
      · exact one_mem _
    have hUsq : ∀ x ∈ U, x * x = 1 := fun x hx => by
      rcases (mem_kleinFour_iff hu2 hv2 huv).mp hx with rfl | rfl | rfl | rfl
      · rw [show u * v * (u * v) = u * (v * u) * v by group, ← huv,
          show u * (u * v) * v = (u * u) * (v * v) by group, hu2, hv2, one_mul]
      · exact hu2
      · exact hv2
      · exact one_mul 1
    have hw2 : w * w = 1 := by rw [← sq, ← hwF.1, pow_orderOf_eq_one]
    have hwc : ∀ x ∈ U, ∀ y' ∈ zpowers w, x * y' = y' * x := by
      intro x hx y' hy'
      rcases eq_one_or_eq_of_mem_zpowers_sq hw2 hy' with rfl | rfl
      · rw [mul_one, one_mul]
      · exact (mem_centralizer_iff.mp (mem_inf.mp (mem_inf.mp (hUmem x hx)).1).2 y' hwW).symm
    have hdisj : U ⊓ zpowers w = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases eq_one_or_eq_of_mem_zpowers_sq hw2 (mem_inf.mp hx).2 with rfl | rfl
      · exact one_mem _
      · exact absurd (hNL (hUmem x (mem_inf.mp hx).1)) hwL
    have hwo : orderOf w = 2 := hwF.1
    have h8 : Nat.card ↥(U ⊔ zpowers w) = 8 := by
      rw [card_sup_eq_mul_of_disjoint_of_le_normalizer U (zpowers w)
        (le_normalizer_of_commute hwc) (disjoint_iff.mpr hdisj), hU4, Nat.card_zpowers, hwo]
    have hwB : w ∈ coreActionKernel B := mem_coreActionKernel_of_le_centralizer hwF.2.1
    have hEC : U ⊔ zpowers w ≤ coreActionKernel B :=
      sup_le (fun x hx => (mem_inf.mp (hUmem x hx)).2) (zpowers_le.mpr hwB)
    have hEsq : ∀ x ∈ U ⊔ zpowers w, x ^ 2 = 1 := fun x hx => by
      rw [sq]
      exact sq_eq_one_of_mem_sup hUsq (fun y' hy' => by
        rcases eq_one_or_eq_of_mem_zpowers_sq hw2 hy' with rfl | rfl
        · exact one_mul 1
        · exact hw2) hwc hx
    have h3 := Foote47.three_le_pRank_of_card_eight hEC hEsq h8
    have h2 := h.rankC B hwF'
    omega
  have hyN : y ∈ N := mem_inf.mpr ⟨mem_inf.mpr ⟨hyL, hyW⟩, hyC⟩
  have h1 : psi L ε ⟨y, hyL⟩ ∈ Nb := ⟨⟨y, hyL⟩, mem_subgroupOf.mpr hyN, rfl⟩
  rw [hNb1, mem_bot] at h1
  exact (psi_eq_one_iff ε ⟨y, hyL⟩).mp h1

end Sec5

end CFSG.ComponentClassification.Foote5
