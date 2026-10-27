module

public import CFSG.LargeExtraspecial.S5OneB
public import CFSG.LargeExtraspecial.S4SevenCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem dtEqConj_of_ne (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g) : DtEqConj S g t := by
  rcases timmesfeld_4_5 H hNo C ht ht1 with hR' | hL | ⟨hVQ, hSp | hA | hΩ | hP⟩
  · exact absurd hR' hR
  · exact dtEqConj_of_linCase H hL
  · exact dtEqConj_of_transitive H ht hSp.transitive
  · exact dtEqConj_of_transitive H ht hA.transitive
  · exact dtEqConj_of_omegaCase H hNo C hΩ
  · exact dtEqConj_of_pgl25Case H C hP

theorem card_LmodN_of_a6Pair (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hA : A6Pair (RmodN S g t) (LmodN S g t) (aV ht)) : Nat.card (LmodN S g t) = 4 := by
  obtain ⟨h4, β, hβ, hnd, -, -, hcard, -, -⟩ := hA
  rw [card_spPointRadical hβ hnd (aV_ne_zero H ht), h4] at hcard
  norm_num at hcard
  omega

theorem card_le_two_mul_of_relIndex_le_two {X : Type*} [Group X] {B H : Subgroup X}
    (hB : B ≤ H) (h : B.relIndex H ≤ 2) : Nat.card H ≤ 2 * Nat.card B := by
  have h1 := card_mul_index (B.subgroupOf H)
  rw [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv] at h1
  change Nat.card B * B.relIndex H = Nat.card H at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_right _ h

namespace CompAt

variable (A : CompAt S g)

theorem commute_of_mem_inf_Nbar (hIrr : Irr S) (H : Hyp4 S g) (C : Cons311 S g) {x : S.O}
    (hxX : x ∈ A.X) (hxN : x ∈ Nbar S g A.t) {y : S.O} (hy : y ∈ A.X) : x * y = y * x := by
  have hnorm : ∀ a ∈ A.X, ∀ n ∈ A.X ⊓ Nbar S g A.t, a * n * a⁻¹ ∈ A.X ⊓ Nbar S g A.t := by
    intro a ha n hn
    obtain ⟨k, rfl, hkt⟩ := A.rho_comm ha
    exact ⟨A.X.mul_mem (A.X.mul_mem ha hn.1) (A.X.inv_mem ha),
      conj_mem_Nbar H.conj_mem hkt hn.2⟩
  rcases commute_or_eq_of_normalized A.isQuasisimple inf_le_left hnorm with hcen | heq
  · exact hcen x ⟨hxX, hxN⟩ y hy
  · exact absurd (by rw [← heq]; exact inf_le_right) (A.not_le_Nbar hIrr H C)

theorem commute_of_mem_Nbar_of_isPGroup (hIrr : Irr S) (H : Hyp4 S g) (C : Cons311 S g)
    (h2 : IsPGroup 2 (Nbar S g A.t)) {n : S.O} (hn : n ∈ Nbar S g A.t) {y : S.O}
    (hy : y ∈ A.X) : n * y = y * n := by
  have hnX : n * y * n⁻¹ ∈ A.X :=
    (mem_normalizer_iff.mp (A.Rbar_le_normalizer (Nbar_le_Rbar hn)) y).mp hy
  obtain ⟨k, rfl, hkt⟩ := A.rho_comm hy
  have hyN : S.ρ k * n⁻¹ * (S.ρ k)⁻¹ ∈ Nbar S g A.t := conj_mem_Nbar H.conj_mem hkt (inv_mem hn)
  obtain ⟨c, hc⟩ : ∃ c, c = n * S.ρ k * n⁻¹ * (S.ρ k)⁻¹ := ⟨_, rfl⟩
  have hcX : c ∈ A.X := hc ▸ A.X.mul_mem hnX (A.X.inv_mem hy)
  have hcN : c ∈ Nbar S g A.t := by
    have := mul_mem hn hyN
    rw [hc]
    simpa [mul_assoc] using this
  obtain ⟨j, hj⟩ := h2 ⟨c, hcN⟩
  have hj' : c ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hc1 : c = 1 := eq_one_of_mem_center_of_pow S A.isComponentOf.2.1 hcX
    (fun z hz => A.commute_of_mem_inf_Nbar hIrr H C hcX hcN hz) hj'
  calc n * S.ρ k = c * (S.ρ k * n) := by rw [hc]; group
    _ = S.ρ k * n := by rw [hc1, one_mul]

theorem eight_le_card_LmodN (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (Q : Hyp45Q H C) (hn : 4 < S.width) (hVQ : ¬ V S g A.t ≤ S.Qa g) :
    8 ≤ Nat.card (LmodN S g A.t) := by
  have h2 := A.card_Lbar_inf_Nbar_le_two hIrr H hNo C Q hVQ
  have h16 := sixteen_le_card_Lbar C hn
  rw [card_Lbar_eq H.conj_mem A.mem_Lbar] at h16
  by_contra h
  have : Nat.card (S.Lbar g ⊓ Nbar S g A.t : Subgroup S.O) * Nat.card (LmodN S g A.t) ≤
      2 * 7 := Nat.mul_le_mul h2 (by omega)
  omega

theorem linCase (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hVQ : V S g A.t ≤ S.Qa g) : LinCase S g A.mem_Lbar := by
  rcases timmesfeld_4_5 H hNo C A.mem_Lbar A.ne_one with hR' | hL | ⟨hVQ', -⟩
  · exact absurd hR' (A.Rbar_ne hIrr H)
  · exact hL
  · exact absurd hVQ hVQ'

theorem four_le_card_LmodN (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (Q : Hyp45Q H C) (hVQ : V S g A.t ≤ S.Qa g) : 4 ≤ Nat.card (LmodN S g A.t) := by
  have h3 := ((A.hyp45q hIrr H hNo C Q).2 hVQ).2
  rw [(A.linCase hIrr H hNo C hVQ).LmodN_eq, card_centreGroup (aV_ne_zero H A.mem_Lbar)]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (finrank (ZMod 2) (Vt S g A.t) - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem Nbar_le_Lbar (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width) :
    IsPGroup 2 (Nbar S g A.t) ∧ Nbar S g A.t ≤ S.Lbar g := by
  have haQ := H.conj_mem
  have hR := A.Rbar_ne hIrr H
  have hfac := (A.hyp45q hIrr H hNo C Q).1.1
  have hP : ∀ hVQ : ¬ V S g A.t ≤ S.Qa g, ¬ PGL25Case H C A.mem_Lbar A.ne_one hVQ := by
    intro hVQ hPG
    have h4 := card_LmodN_le_four_of_tau_not_mem H C A.mem_Lbar A.ne_one hVQ hPG.finrank_eq
      hPG.tau_not_mem
    have h8 := A.eight_le_card_LmodN hIrr H hNo C Q hn hVQ
    omega
  rcases timmesfeld_4_7_a hCE H hNo C A.mem_Lbar A.ne_one hR hP with ⟨h2, -, hsup⟩ | ⟨hA6, -⟩
  · refine ⟨h2, hsup.le.trans (iSup₂_le fun X hX => ?_)⟩
    obtain ⟨h, rfl, hth⟩ := hX
    intro y hy
    obtain ⟨k, hkR, hk⟩ := dtEqConj_of_ne H hNo C A.mem_Lbar A.ne_one hR h hth
    have hyL : y ∈ S.Lbar ((k : G) * g) := hk ▸ hy.1
    rw [mem_Lbar_mul_iff] at hyL
    obtain ⟨x, hxX, -, s, hs, n, hnN, hkr⟩ := exists_mul_mul_of_factor H A.mem_Lbar hfac hkR
    rw [hkr] at hyL
    have hxy : x * y = y * x := (A.commute_of_mem_Nbar_of_isPGroup hIrr H C h2 hy.2 hxX).symm
    have hnL := Nbar_le_normalizer haQ H.conj_ne (Lbar_mem_Dset A.mem_Lbar) hnN
    have e : (x * s * n)⁻¹ * y * (x * s * n) = n⁻¹ * (s⁻¹ * y * s) * n⁻¹⁻¹ := by
      calc (x * s * n)⁻¹ * y * (x * s * n) = n⁻¹ * s⁻¹ * (x⁻¹ * (y * x)) * s * n := by group
        _ = n⁻¹ * s⁻¹ * (x⁻¹ * (x * y)) * s * n := by rw [hxy]
        _ = n⁻¹ * (s⁻¹ * y * s) * n⁻¹⁻¹ := by group
    rw [e] at hyL
    have h1 : s⁻¹ * y * s ∈ S.Lbar g :=
      (mem_normalizer_iff.mp (inv_mem hnL) (s⁻¹ * y * s)).mpr hyL
    have e2 : y = s * (s⁻¹ * y * s) * s⁻¹ := by group
    rw [e2]
    exact mul_mem (mul_mem hs h1) (inv_mem hs)
  · exfalso
    have h4 := card_LmodN_of_a6Pair H A.mem_Lbar hA6
    by_cases hVQ : V S g A.t ≤ S.Qa g
    · have := A.four_le_card_LmodN hIrr H hNo C Q hVQ
      rw [(A.linCase hIrr H hNo C hVQ).LmodN_eq, card_centreGroup (aV_ne_zero H A.mem_Lbar),
        hA6.1] at h4
      norm_num at h4
    · have := A.eight_le_card_LmodN hIrr H hNo C Q hn hVQ
      omega

theorem card_LmodN_inf_le (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width) :
    Nat.card (LmodN S g A.t ⊓ imgR H.conj_mem A.t A.X : Subgroup _) ≤
      Nat.card (S.Lbar g ⊓ A.X : Subgroup S.O) := by
  have hNL := (A.Nbar_le_Lbar hCE hIrr H hNo C Q hn).2
  let f : (S.Lbar g ⊓ A.X : Subgroup S.O) →
      (LmodN S g A.t ⊓ imgR H.conj_mem A.t A.X : Subgroup _) := fun y =>
    ⟨resV H.conj_mem A.t ⟨y, Lbar_le_Rbar A.mem_Lbar y.2.1⟩,
      resV_mem_LmodN H.conj_mem y.2.1 _, mem_imgR.mpr ⟨_, y.2.2, rfl⟩⟩
  refine Nat.card_le_card_of_surjective f fun e => ?_
  obtain ⟨⟨s, hs, hse⟩, hK⟩ := e.2
  obtain ⟨y, hyX, hye⟩ := mem_imgR.mp hK
  have hsR : s ∈ Rbar S g A.t := Lbar_le_Rbar A.mem_Lbar hs
  have hres : resV H.conj_mem A.t ⟨s, hsR⟩ = e :=
    LinearEquiv.ext fun v => Subtype.ext (hse v).symm
  have hN : ((y⁻¹ * ⟨s, hsR⟩ : Rbar S g A.t) : S.O) ∈ Nbar S g A.t := by
    rw [← resV_eq_one_iff H.conj_mem, map_mul, map_inv, hres, hye, inv_mul_cancel]
  have hyL : (y : S.O) ∈ S.Lbar g := by
    have := mul_mem hs (inv_mem (hNL hN))
    simpa using this
  refine ⟨⟨y, hyL, hyX⟩, Subtype.ext ?_⟩
  change resV H.conj_mem A.t ⟨y, _⟩ = (e : Vt S g A.t ≃ₗ[ZMod 2] Vt S g A.t)
  rw [← hye]

end CompAt

end CFSG.LargeExtraspecial.S5
