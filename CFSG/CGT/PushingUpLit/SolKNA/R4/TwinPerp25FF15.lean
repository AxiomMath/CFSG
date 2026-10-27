module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF10

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open scoped commutatorElement

section TwoGroup


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ b : Y}

theorem isPGroup_quot_of_center (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ H)
    (hcent : ∀ g : ↥H ⧸ classicalInvolutionOddCore ↥H, g * QuotientGroup.mk'
      (classicalInvolutionOddCore ↥H)
      (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H) * g⁻¹ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H)) :
    IsPGroup 2 (↥H ⧸ classicalInvolutionOddCore ↥H) := by
  classical
  set tH : ↥H := ⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ with htHdef
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥H) with hπ
  set ι : ↥H →* Y := (Subgroup.centralizer ({b} : Set Y)).subtype.comp H.subtype with hι
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.ext hab)
  have hιt : ι tH = t := rfl
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hOq : TightOddFree (↥H ⧸ classicalInvolutionOddCore ↥H) :=
    CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot
  have htH2 : tH * tH = 1 := Subtype.ext (Subtype.ext F.base.inv.sq)
  have hlift : ∀ h : ↥H, ∃ y : ↥H, y * tH = tH * y ∧ π y = π h := by
    intro h
    have h1 : π (h * tH * h⁻¹) = π tH := by
      have := hcent (π h)
      simpa [map_mul, map_inv] using this
    have hs2 : (h * tH * h⁻¹) * (h * tH * h⁻¹) = 1 := by
      calc (h * tH * h⁻¹) * (h * tH * h⁻¹) = h * (tH * tH) * h⁻¹ := by group
        _ = 1 := by rw [htH2]; group
    have hmem : (h * tH * h⁻¹)⁻¹ * tH ∈ classicalInvolutionOddCore ↥H := by
      have h1' := h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1'
      exact h1'
    obtain ⟨m, hm, hmz⟩ := OddQuot.exists_conj_of_involutions hodd htH2 hs2 hmem
    refine ⟨m⁻¹ * h, ?_, ?_⟩
    · have e1 : m⁻¹ * h * tH * (m⁻¹ * h)⁻¹ = tH := by
        calc m⁻¹ * h * tH * (m⁻¹ * h)⁻¹ = m⁻¹ * (h * tH * h⁻¹) * m := by group
          _ = m⁻¹ * (m * tH * m⁻¹) * m := by rw [hmz]
          _ = tH := by group
      calc m⁻¹ * h * tH = (m⁻¹ * h * tH * (m⁻¹ * h)⁻¹) * (m⁻¹ * h) := by group
        _ = tH * (m⁻¹ * h) := by rw [e1]
    · have hπm : π m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
      simp [map_mul, map_inv, hπm]
  set Mo : Subgroup Y := Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) with hMo
  set MH : Subgroup ↥H := Mo.comap ι with hMH
  have hMHodd : Odd (Nat.card ↥MH) := by
    have hinj' : Function.Injective (ι.subgroupComap Mo) := by
      intro a b hab
      have h1 : ι (a : ↥H) = ι (b : ↥H) := congrArg (fun z : ↥Mo => (z : Y)) hab
      exact Subtype.ext (hιinj h1)
    have hdvd : Nat.card ↥MH ∣ Nat.card ↥Mo := Subgroup.card_dvd_of_injective _ hinj'
    exact (Balance.odd_card_oddCoreIn _).of_dvd_nat hdvd
  set N' : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H) := MH.map π with hN'
  have hN'odd : Odd (Nat.card ↥N') :=
    hMHodd.of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hN'n : N'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ g
    obtain ⟨y, hyt, hπy⟩ := hlift h
    rw [← hπy]
    refine ⟨y * m * y⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hyC : ι y ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hιt, ← map_mul, ← map_mul, hyt]
    show ι (y * m * y⁻¹) ∈ Mo
    rw [map_mul, map_mul, map_inv]
    exact Balance.conj_mem_oddCoreIn hyC hm
  have hN'bot : N' = ⊥ := by
    have hle : N' ≤ classicalInvolutionOddCore (↥H ⧸ classicalInvolutionOddCore ↥H) :=
      le_sSup ⟨hN'n, hN'odd⟩
    rw [hOq] at hle
    exact le_bot_iff.mp hle
  have hec := ec_twin_odd F.hr F.hP F.hyp F.h11
  have hoddtriv : ∀ g : ↥H ⧸ classicalInvolutionOddCore ↥H, Odd (orderOf g) → g = 1 := by
    intro g hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ g
    obtain ⟨y, hyt, hπy⟩ := hlift h
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    have hpos : 0 < 2 ^ a := by positivity
    have hy₂ord : orderOf (y ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd hpos.ne' ⟨m, hord⟩, hord, Nat.mul_div_cancel_left m hpos]
    have hy₂C : ι (y ^ 2 ^ a) ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff, map_pow, ← hιt]
      have : ι y * ι tH = ι tH * ι y := by rw [← map_mul, ← map_mul, hyt]
      exact ((Commute.pow_left (show Commute (ι y) (ι tH) from this) _).eq)
    have hy₂odd : Odd (orderOf (ι (y ^ 2 ^ a))) := by
      rw [orderOf_injective ι hιinj, hy₂ord]
      exact hm
    have hy₂Mo : ι (y ^ 2 ^ a) ∈ Mo := hec _ hy₂C hy₂odd
    have h1 : π (y ^ 2 ^ a) ∈ N' := ⟨y ^ 2 ^ a, hy₂Mo, rfl⟩
    rw [hN'bot, Subgroup.mem_bot, map_pow, hπy] at h1
    have h2 : orderOf (π h) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h1
    have h3 : Odd (orderOf (π h)) := hg
    have h4 : Nat.Coprime (orderOf (π h)) (2 ^ a) :=
      Nat.Coprime.pow_right a (Odd.coprime_two_right h3)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h4 h2)
  intro g
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hpos : 0 < 2 ^ a := by positivity
  have hg₂ord : orderOf (g ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd hpos.ne' ⟨m, hord⟩, hord, Nat.mul_div_cancel_left m hpos]
  exact ⟨a, hoddtriv _ (by rw [hg₂ord]; exact hm)⟩

end TwoGroup

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
