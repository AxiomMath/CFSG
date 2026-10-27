module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyOutThreeGrp
public import CFSG.Sporadic.Recognition.McLNoThree
public import CFSG.Sporadic.Recognition.LyonsLocalPerfect

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup Equiv Equiv.Perm CFSG CFSG.Blueprint CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.McLAS

theorem lyThreeA_core_of_mcl
    (hMcL : McLNoThreeNormalized) {Y : Type} [Group Y] [Finite Y] {t : Y}
    {ρ : ↥(centralizer ({t} : Set Y)) →* Perm (Fin 11)}
    {x₁ x₂ x₃ : ↥(centralizer ({t} : Set Y))} (D : LyData Y t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {A : Subgroup Y} (hA : Nat.card ↥A = 2 ^ 8)
    (hAn : A ≤ normalizer (zpowers (x₁ : Y) : Set Y))
    {W : Subgroup Y} (hW : IsPGroup 3 ↥W)
    (hWn : W ≤ normalizer (zpowers (x₁ : Y) : Set Y))
    (hAW : A ≤ normalizer (W : Set Y)) : W ≤ zpowers (x₁ : Y) := by
  classical
  have hx3 : orderOf (x₁ : Y) = 3 := LyData.orderOf_x₁ S
  have hcen := D.center_centralizer S
  have hc3 := D.card_center_centralizer S
  obtain ⟨eM⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  set M : Subgroup Y := centralizer ({(x₁ : Y)} : Set Y) with hMdef
  have e : ↥M ⧸ center ↥M ≃* NativeSporadic.McL :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans eM
  have hWM : W ≤ M := le_centralizer_of_isPGroup_three hx3 hW hWn
  have hcardM : Nat.card ↥M = 2694384000 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥M)
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL, hc3] at h1
    omega
  have hA0 : Nat.card ↥(A ⊓ M) = 2 ^ 7 := by
    have hlow := card_le_two_mul_card_inf_centralizer hx3 hAn
    rw [hA] at hlow
    have hd1 : Nat.card ↥(A ⊓ M) ∣ 2 ^ 8 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(A ⊓ M) ∣ 2694384000 := hcardM ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    rw [hjc] at hd2 hlow ⊢
    interval_cases j <;> omega
  set A0 : Subgroup ↥M := (A ⊓ M).subgroupOf M with hA0def
  have hA0card : Nat.card ↥A0 = 2 ^ 7 := by
    rw [hA0def, ← hA0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  let mk : ↥M →* ↥M ⧸ center ↥M := QuotientGroup.mk' (center ↥M)
  have hinj : Function.Injective (mk.domRestrict A0) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : ↥M) ∈ center ↥M := (QuotientGroup.eq_one_iff _).1 ha
    have h2 : (a : ↥M) ^ (2 ^ 7) = 1 := by
      have := pow_card_eq_one' (G := ↥A0) (x := a)
      rw [hA0card] at this
      simpa using congrArg Subtype.val this
    have h3 : (a : ↥M) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(center ↥M)) (x := ⟨a, h1⟩)
      rw [hc3] at this
      simpa using congrArg Subtype.val this
    have h4 : (a : ↥M) ^ Nat.gcd (2 ^ 7) 3 = 1 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    have : Nat.gcd (2 ^ 7) 3 = 1 := by norm_num
    rw [this, pow_one] at h4
    exact Subtype.ext h4
  have hS : Nat.card ↥(A0.map mk) = 2 ^ 7 := by
    rw [← MonoidHom.domRestrict_range, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      hA0card]
  have hWsub : IsPGroup 3 ↥(W.subgroupOf M) := hW.comap_subtype (K := M)
  have hWbar : IsPGroup 3 ↥((W.subgroupOf M).map mk) := hWsub.map mk
  have hnorm0 : A0 ≤ normalizer ((W.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro w
    have hs' : (s : Y) ∈ normalizer (W : Set Y) :=
      hAW (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).1
    have := mem_normalizer_iff.1 hs' (w : Y)
    simpa [Subgroup.mem_subgroupOf] using this
  have hnorm : A0.map mk ≤ normalizer (((W.subgroupOf M).map mk : Subgroup _) : Set _) :=
    (Subgroup.map_mono hnorm0).trans (Subgroup.le_normalizer_map _)
  have hbot := hMcL _ ⟨e⟩ (A0.map mk) hS _ hWbar hnorm
  intro w hw
  have hwM : (⟨w, hWM hw⟩ : ↥M) ∈ W.subgroupOf M := Subgroup.mem_subgroupOf.2 hw
  have h1 : mk ⟨w, hWM hw⟩ ∈ (W.subgroupOf M).map mk := Subgroup.mem_map_of_mem _ hwM
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : (⟨w, hWM hw⟩ : ↥M) ∈ center ↥M := (QuotientGroup.eq_one_iff _).1 h1
  rw [hcen, Subgroup.mem_zpowers_iff] at h2
  obtain ⟨k, hk⟩ := h2
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
