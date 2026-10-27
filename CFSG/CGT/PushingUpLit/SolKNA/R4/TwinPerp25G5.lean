module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF10

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Pow

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_two_pow_mem {N : Subgroup G} {g : G} (hg : Odd (orderOf g)) {a : ℕ}
    (h : g ^ 2 ^ a ∈ N) : g ∈ N := by
  have hcop : Nat.Coprime (2 ^ a) (orderOf g) :=
    (Nat.Coprime.pow_right a (Odd.coprime_two_right hg)).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact N.pow_mem h m

end Pow

section EC


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ b : Y}

theorem oddEC_quot (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ H) :
    OddEC (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H)) := by
  classical
  set tH : ↥H := ⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ with htHdef
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥H) with hπ
  set ι : ↥H →* Y := (Subgroup.centralizer ({b} : Set Y)).subtype.comp H.subtype with hι
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.ext hab)
  have hιt : ι tH = t := rfl
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have htH2 : tH * tH = 1 := Subtype.ext (Subtype.ext F.base.inv.sq)
  have hec := ec_twin_odd F.hr F.hP F.hyp F.h11
  have hlift : ∀ h : ↥H, π (h * tH * h⁻¹) = π tH → ∃ y : ↥H, y * tH = tH * y ∧ π y = π h := by
    intro h h1
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
  have hcent : ∀ g : ↥H ⧸ classicalInvolutionOddCore ↥H, g * π tH = π tH * g →
      ∃ y : ↥H, y * tH = tH * y ∧ π y = g := by
    intro g hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ g
    have hg' : π h * π tH = π tH * π h := hg
    have h1 : π (h * tH * h⁻¹) = π tH := by
      rw [map_mul, map_mul, map_inv, hg']
      group
    exact hlift h h1
  have hyC : ∀ y : ↥H, y * tH = tH * y → ι y ∈ Subgroup.centralizer ({t} : Set Y) := by
    intro y hyt
    rw [Subgroup.mem_centralizer_singleton_iff, ← hιt, ← map_mul, ← map_mul, hyt]
  refine ⟨MH.map π, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmC : ι m ∈ Subgroup.centralizer ({t} : Set Y) := Balance.oddCoreIn_le _ hm
    have hcm : m * tH = tH * m := by
      apply hιinj
      rw [map_mul, map_mul, hιt]
      exact Subgroup.mem_centralizer_singleton_iff.mp hmC
    rw [← map_mul, ← map_mul, hcm]
  · exact hMHodd.of_dvd_nat (Subgroup.card_map_dvd _ _)
  ·
    intro g hg m hm
    obtain ⟨y, hyt, hπy⟩ := hcent g (Subgroup.mem_centralizer_singleton_iff.mp hg)
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    rw [← hπy]
    refine ⟨y * m₀ * y⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show ι (y * m₀ * y⁻¹) ∈ Mo
    rw [map_mul, map_mul, map_inv]
    exact Balance.conj_mem_oddCoreIn (hyC y hyt) hm₀
  ·
    intro g hg hgodd
    obtain ⟨y, hyt, hπy⟩ := hcent g (Subgroup.mem_centralizer_singleton_iff.mp hg)
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    have hpos : 0 < 2 ^ a := by positivity
    have hy₂ord : orderOf (y ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd hpos.ne' ⟨m, hord⟩, hord, Nat.mul_div_cancel_left m hpos]
    have hy₂C : ι (y ^ 2 ^ a) ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [map_pow]
      exact (Subgroup.centralizer ({t} : Set Y)).pow_mem (hyC y hyt) _
    have hy₂odd : Odd (orderOf (ι (y ^ 2 ^ a))) := by
      rw [orderOf_injective ι hιinj, hy₂ord]
      exact hm
    have hy₂Mo : ι (y ^ 2 ^ a) ∈ Mo := hec _ hy₂C hy₂odd
    have h1 : π (y ^ 2 ^ a) ∈ MH.map π := ⟨y ^ 2 ^ a, hy₂Mo, rfl⟩
    rw [map_pow, hπy] at h1
    exact mem_of_pow_two_pow_mem hgodd h1

end EC

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four
