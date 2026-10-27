module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E2
public import CFSG.ClassicalInvolution.Asc77.AscC5O9H

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C5O (Om5Data Om5Centerless Om5InvFixFour Om5Interchange Om5ZSwap
  Om5USwapNotZ Om5ExcClass ModelFacts TwinShare M8GFacts Om5TwinComm Om5TwinCommSwap HasBigFix)
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.ExactLayer (isPGroup_zpowers_of_sq_eq_one)
open scoped commutatorElement


section Main

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

@[expose] def kerLayer [Finite G] (Ω : Set (Subgroup G)) (c : G) : Subgroup G :=
  Subgroup.centralizer ({c} : Set G) ⊓ trivialOnQuot (layerX Ω c)
namespace Ctx

theorem two_orbits (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {τ : G} (hτa : τ * a = a * τ)
    (hτG : ∃ c : G, c * z * c⁻¹ = τ) (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ)
    (haτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ) {b : G} (hba : b * a = a * b)
    (hbG : ∃ c : G, c * z * c⁻¹ = b) :
    (∃ h : G, h * a = a * h ∧ h * z * h⁻¹ = b) ∨
      ∃ x ∈ layerX Ω a, ∃ n ∈ kerLayer Ω a, Odd (orderOf n) ∧ (x * n) * τ * (x *
          n)⁻¹ = b := by
  classical
  by_cases hbz : ∃ h : G, h * a = a * h ∧ h * z * h⁻¹ = b
  · exact Or.inl hbz
  right
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaGen Ω := C.hΩ
  have hz2 := C.hz2
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', A, A', hD⟩ := C.om5'
  obtain ⟨cb, hcb⟩ := hbG
  obtain ⟨cτ, hcτ⟩ := hτG
  have hconj2 : ∀ c : G, (c * z * c⁻¹) * (c * z * c⁻¹) = 1 := by
    intro c
    calc (c * z * c⁻¹) * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hb2 : b * b = 1 := by rw [← hcb]; exact hconj2 cb
  have hτ2 : τ * τ = 1 := by rw [← hcτ]; exact hconj2 cτ
  have hbCa : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hba
  have hτCa : τ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hτa
  have hbX : conjSub b (layerX Ω a) = layerX Ω a :=
    conjSub_layerX_of_mem hΩ hbCa
  have hτX : conjSub τ (layerX Ω a) = layerX Ω a :=
    conjSub_layerX_of_mem hΩ hτCa
  have hnofix : ∀ (w cw : G) (hw : w ∈ Subgroup.centralizer ({a} : Set G)),
      cw * z * cw⁻¹ = w → (∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ w) →
      ∀ J ∈ C.fam, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 →
        C25Y.layerAut (layerX Ω a) (conjSub_layerX_of_mem hΩ
            hw) x ≠ x := by
    intro w cw hw hcw hn J hJ x hxJ hx4 hx2 hfix
    subst hcw
    obtain ⟨h, hhC, hh⟩ := C.c25_8_one hw hJ hxJ hx4 hx2 hfix
    exact hn h (Subgroup.mem_centralizer_singleton_iff.mp hhC) hh
  have hnb := hnofix b cb hbCa hcb (fun h hh hhz => hbz ⟨h, hh, hhz⟩)
  have hnτ := hnofix τ cτ hτCa hcτ hτn
  obtain ⟨gb, hg⟩ := hM.excClass _ _ _ _ _ _ _ hD (C25Y.layerAut _ hbX) (C25Y.layerAut _ hτX)
    (C25Y.layerAut_involutive _ hbX hb2) (C25Y.layerAut_involutive _ hτX hτ2) hnb hnτ
    (C.not_hasBigFix hb2 hbX hcb) (C.not_hasBigFix hτ2 hτX hcτ)
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective gb
  have hg₀X : (g₀ : G) ∈ layerX Ω a := g₀.2
  have hg₀a : (g₀ : G) * a = a * g₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω a hg₀X)
  set v : G := (g₀ : G) * b * (g₀ : G)⁻¹ with hv
  have hva : v * a = a * v := by
    have hg₀a' : (g₀ : G)⁻¹ * a = a * (g₀ : G)⁻¹ := by
      calc (g₀ : G)⁻¹ * a = (g₀ : G)⁻¹ * (a * g₀) * (g₀ : G)⁻¹ := by group
        _ = (g₀ : G)⁻¹ * (g₀ * a) * (g₀ : G)⁻¹ := by rw [hg₀a]
        _ = a * (g₀ : G)⁻¹ := by group
    calc v * a = (g₀ : G) * b * ((g₀ : G)⁻¹ * a) := by rw [hv]; group
      _ = (g₀ : G) * (b * a) * (g₀ : G)⁻¹ := by rw [hg₀a']; group
      _ = ((g₀ : G) * a) * b * (g₀ : G)⁻¹ := by rw [hba]; group
      _ = a * v := by rw [hg₀a, hv]; group
  have hv2 : v * v = 1 := by
    calc v * v = (g₀ : G) * (b * b) * (g₀ : G)⁻¹ := by rw [hv]; group
      _ = 1 := by rw [hb2]; group
  have hvCa : v ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hva
  have hvX : conjSub v (layerX Ω a) = layerX Ω a :=
    conjSub_layerX_of_mem hΩ hvCa
  have hvact : ∀ e, C25Y.layerAut (layerX Ω a) hvX e =
      QuotientGroup.mk g₀ * C25Y.layerAut (layerX Ω a) hbX
        ((QuotientGroup.mk g₀)⁻¹ * e * QuotientGroup.mk g₀) * (QuotientGroup.mk g₀)⁻¹ := by
    intro e
    induction e using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        C25Y.layerAut_mk, C25Y.layerAut_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [C25Y.coe_conjOnSub, Subgroup.coe_mul, Subgroup.coe_inv, hv]
      group
  set d : G := τ * v with hd
  have hdCa : d ∈ Subgroup.centralizer ({a} : Set G) := mul_mem hτCa hvCa
  have hdT : d ∈ trivialOnQuot (layerX Ω a) := by
    rw [← layerAut_eq_id_iff (layerX Ω a) (conjSub_layerX_of_mem hΩ hdCa)]
    intro e
    rw [layerAut_mul_apply _ hτX hvX _ e, hg, hvact]
    have e1 : (QuotientGroup.mk g₀ : ↥(layerX Ω a) ⧸ classicalInvolutionOddCore
        ↥(layerX Ω a))⁻¹ * (QuotientGroup.mk g₀ * C25Y.layerAut
            (layerX Ω a) hbX
          ((QuotientGroup.mk g₀)⁻¹ * e * QuotientGroup.mk g₀) * (QuotientGroup.mk g₀)⁻¹) *
          QuotientGroup.mk g₀ =
        C25Y.layerAut (layerX Ω a) hbX ((QuotientGroup.mk g₀)⁻¹ * e *
            QuotientGroup.mk g₀) := by
      group
    rw [e1, C25Y.layerAut_involutive _ hbX hb2]
    group
  have hda : d * a = a * d := Subgroup.mem_centralizer_singleton_iff.mp hdCa
  have hpowa : ∀ n : ℕ, d ^ n * a = a * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc d ^ (n + 1) * a = d ^ n * (d * a) := by rw [pow_succ, mul_assoc]
        _ = d ^ n * (a * d) := by rw [hda]
        _ = (d ^ n * a) * d := by group
        _ = (a * d ^ n) * d := by rw [ih]
        _ = a * d ^ (n + 1) := by rw [pow_succ, mul_assoc]
  have hzpa : ∀ x ∈ Subgroup.zpowers d, x * a = a * x := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    have h := Subgroup.zpow_mem (Subgroup.centralizer ({a} : Set G)) hdCa n
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  by_cases hk : k = 0
  ·
    have hdodd : Odd (Nat.card (Subgroup.zpowers d)) := by
      rw [Nat.card_zpowers, hn, hk, pow_zero, one_mul]
      exact hm
    obtain ⟨n, hn', hnv⟩ := C25Y.exists_conj_of_involutions_odd hdodd hτ2 hv2
      (Subgroup.mem_zpowers d)
    have hdK : d ∈ kerLayer Ω a := ⟨hdCa, hdT⟩
    have hnK : n ∈ kerLayer Ω a := by
      obtain ⟨i, rfl⟩ := hn'
      exact zpow_mem hdK i
    have hnodd : Odd (orderOf n) := by
      have h1 : orderOf n ∣ orderOf d := orderOf_dvd_of_mem_zpowers hn'
      have h2 : Odd (orderOf d) := by rw [hn, hk, pow_zero, one_mul]; exact hm
      exact Odd.of_dvd_nat h2 h1
    refine ⟨(g₀ : G)⁻¹, (layerX Ω a).inv_mem hg₀X, n, hnK, hnodd, ?_⟩
    calc (g₀ : G)⁻¹ * n * τ * ((g₀ : G)⁻¹ * n)⁻¹ = (g₀ : G)⁻¹ * (n * τ * n⁻¹) * g₀ := by group
      _ = (g₀ : G)⁻¹ * v * g₀ := by rw [← hnv]
      _ = b := by rw [hv]; group
  ·
    exfalso
    have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
    have hord : orderOf (d ^ m) = 2 ^ k := by
      rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hn.symm), hn, Nat.mul_div_cancel _ (by omega)]
    have h2 : IsPGroup 2 (Subgroup.zpowers (d ^ m)) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord])
    have hdT' : d ^ m ∈ trivialOnQuot (layerX Ω a) := pow_mem hdT m
    rcases C.twoElt_triv hM.centerless (hpowa m) hdT' h2 with h1 | h1
    · have h3 : orderOf (d ^ m) = 1 := by rw [h1, orderOf_one]
      rw [hord] at h3
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    ·
      obtain ⟨j, rfl⟩ := hm
      have hapow : a ^ (2 * j + 1) = a := by
        rw [pow_succ, pow_mul, sq, C.ha2, one_pow, one_mul]
      have had : (a * d) ^ (2 * j + 1) = 1 := by
        rw [(Commute.mul_pow (hda.symm) _), hapow, h1, C.ha2]
      have hodd : Odd (Nat.card (Subgroup.zpowers (a * d))) := by
        rw [Nat.card_zpowers]
        exact Odd.of_dvd_nat (odd_two_mul_add_one j) (orderOf_dvd_of_pow_eq_one had)
      have haτ2 : (a * τ) * (a * τ) = 1 := by
        calc (a * τ) * (a * τ) = a * (τ * a) * τ := by group
          _ = a * (a * τ) * τ := by rw [hτa]
          _ = (a * a) * (τ * τ) := by group
          _ = 1 := by rw [C.ha2, hτ2, one_mul]
      have hmem : (a * τ) * v ∈ Subgroup.zpowers (a * d) := by
        rw [show (a * τ) * v = a * d by rw [hd]; group]
        exact Subgroup.mem_zpowers _
      obtain ⟨n, -, hnv⟩ := C25Y.exists_conj_of_involutions_odd hodd haτ2 hv2 hmem
      apply haτ
      refine ⟨n⁻¹ * (g₀ : G) * cb, ?_⟩
      calc n⁻¹ * (g₀ : G) * cb * z * (n⁻¹ * (g₀ : G) * cb)⁻¹
          = n⁻¹ * ((g₀ : G) * (cb * z * cb⁻¹) * (g₀ : G)⁻¹) * n := by group
        _ = n⁻¹ * v * n := by rw [hcb, hv]
        _ = a * τ := by rw [hnv]; group

theorem pair_count (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {τ m : G} (hτa : τ * a = a * τ)
    (hτG : ∃ c : G, c * z * c⁻¹ = τ) (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ)
    (haτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ) (hm : m * (a * z) = (a * z) * m)
    (hmz : m * z * m⁻¹ = τ) (hmτ : m * τ * m⁻¹ = z) {g : G}
    (hg : (g * a * g⁻¹) * z = z * (g * a * g⁻¹)) :
    (∃ c : G, c * z * c⁻¹ = z ∧ c * a * c⁻¹ = g * a * g⁻¹) ∨
      ∃ c : G, c * z * c⁻¹ = z ∧ c * (a * z * τ) * c⁻¹ = g * a * g⁻¹ := by
  have hba : (g⁻¹ * z * g) * a = a * (g⁻¹ * z * g) := by
    calc (g⁻¹ * z * g) * a = g⁻¹ * (z * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * z) * g := by rw [hg]
      _ = a * (g⁻¹ * z * g) := by group
  have hor := C.two_orbits hM hτa hτG hτn haτ hba ⟨g⁻¹, by group⟩
  replace hor : (∃ h : G, h * a = a * h ∧ h * z * h⁻¹ = g⁻¹ * z * g) ∨
      ∃ h : G, h * a = a * h ∧ h * τ * h⁻¹ = g⁻¹ * z * g := by
    rcases hor with h | ⟨x, hx, n, hn, -, hxn⟩
    · exact Or.inl h
    · refine Or.inr ⟨x * n, ?_, hxn⟩
      have hxa : x * a = a * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω a hx)
      have hna : n * a = a * n := Subgroup.mem_centralizer_singleton_iff.mp hn.1
      calc x * n * a = x * (n * a) := by group
        _ = x * (a * n) := by rw [hna]
        _ = (x * a) * n := by group
        _ = a * (x * n) := by rw [hxa]; group
  rcases hor with ⟨h, hha, hh⟩ | ⟨h, hha, hh⟩
  · left
    refine ⟨g * h, ?_, ?_⟩
    · calc g * h * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
        _ = z := by rw [hh]; group
    · calc g * h * a * (g * h)⁻¹ = g * (h * a) * h⁻¹ * g⁻¹ := by group
        _ = g * a * g⁻¹ := by rw [hha]; group
  · right
    refine ⟨g * h * m⁻¹, ?_, ?_⟩
    · have hm' : m⁻¹ * z * m = τ := by
        calc m⁻¹ * z * m = m⁻¹ * (m * τ * m⁻¹) * m := by rw [hmτ]
          _ = τ := by group
      calc g * h * m⁻¹ * z * (g * h * m⁻¹)⁻¹ = g * (h * (m⁻¹ * z * m) * h⁻¹) * g⁻¹ := by group
        _ = z := by rw [hm', hh]; group
    · have hm1 : m⁻¹ * (a * z) * m = a * z := by
        calc m⁻¹ * (a * z) * m = m⁻¹ * ((a * z) * m) := by group
          _ = m⁻¹ * (m * (a * z)) := by rw [hm]
          _ = a * z := by group
      have hm2 : m⁻¹ * τ * m = z := by
        calc m⁻¹ * τ * m = m⁻¹ * (m * z * m⁻¹) * m := by rw [hmz]
          _ = z := by group
      have hm3 : m⁻¹ * (a * z * τ) * m = a := by
        calc m⁻¹ * (a * z * τ) * m = (m⁻¹ * (a * z) * m) * (m⁻¹ * τ * m) := by group
          _ = a := by rw [hm1, hm2, C.mul_z_mul_z]
      calc g * h * m⁻¹ * (a * z * τ) * (g * h * m⁻¹)⁻¹
          = g * (h * (m⁻¹ * (a * z * τ) * m) * h⁻¹) * g⁻¹ := by group
        _ = g * (h * a) * h⁻¹ * g⁻¹ := by rw [hm3]; group
        _ = g * a * g⁻¹ := by rw [hha]; group
end Ctx





theorem conj_mem_kerLayer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c g n : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) (hn : n ∈ kerLayer Ω c) :
    g * n * g⁻¹ ∈ kerLayer Ω c := by
  refine ⟨(Subgroup.centralizer ({c} : Set G)).mul_mem
    ((Subgroup.centralizer ({c} : Set G)).mul_mem hg hn.1)
    ((Subgroup.centralizer ({c} : Set G)).inv_mem hg), ?_⟩
  have h := trivialOnQuot_conjSub hn.2 g
  rwa [conjSub_layerX_of_mem hΩ hg] at h


theorem mem_normalizer_kerLayer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c g : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) :
    g ∈ Subgroup.normalizer ((kerLayer Ω c : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => conj_mem_kerLayer hΩ hg hn,
    fun hn => ?_⟩
  have := conj_mem_kerLayer hΩ (inv_mem hg) hn
  simpa [mul_assoc] using this

theorem conj_mem_oddCore_kerLayer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c g o : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) (ho : o ∈ oddCoreIn (kerLayer Ω c)) :
    g * o * g⁻¹ ∈ oddCoreIn (kerLayer Ω c) :=
  conj_mem_oddCoreIn_of_mem_normalizer (mem_normalizer_kerLayer hΩ hg) ho


@[expose] def hSub {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (c τ : G)
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) : Subgroup G :=
  mulSub (Subgroup.zpowers τ)
    (mulSub (layerX Ω c) (oddCoreIn (kerLayer Ω c))
      (fun x hx o ho => conj_mem_oddCore_kerLayer hΩ (layerX_le_centralizer Ω c hx)
          ho))
    (fun y hy w hw => by
      obtain ⟨k, rfl⟩ := hy
      have hk : τ ^ k ∈ Subgroup.centralizer ({c} : Set G) := zpow_mem hτ k
      obtain ⟨x, hx, o, ho, rfl⟩ := hw
      refine ⟨τ ^ k * x * (τ ^ k)⁻¹, ?_, τ ^ k * o * (τ ^ k)⁻¹,
        conj_mem_oddCore_kerLayer hΩ hk ho, by group⟩
      have := conjSub_layerX_of_mem hΩ hk (c := c)
      rw [← this]
      exact ⟨x, hx, rfl⟩)

theorem le_hSub_layer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c τ : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) : layerX Ω c ≤ hSub hΩ c τ hτ :=
  (le_mulSub_left _).trans (le_mulSub_right _)

theorem le_hSub_odd {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c τ : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) :
    oddCoreIn (kerLayer Ω c) ≤ hSub hΩ c τ hτ :=
  (le_mulSub_right _).trans (le_mulSub_right _)

theorem mem_hSub_self {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c τ : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) : τ ∈ hSub hΩ c τ hτ :=
  le_mulSub_left _ (Subgroup.mem_zpowers τ)
namespace Ctx

theorem a_mem_kerLayer (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : a ∈ kerLayer Ω a :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, C.a_triv⟩

theorem mem_oddCore_of_odd (hM5 : Om5Centerless)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {n : G} (hn : n ∈ kerLayer Ω a)
    (hodd : Odd (orderOf n)) : n ∈ oddCoreIn (kerLayer Ω a) := by
  have ha := C.a_mem_kerLayer
  have hsyl : IsSylow2In (Subgroup.zpowers a) (kerLayer Ω a) := by
    refine ⟨Subgroup.zpowers_le.mpr ha, isPGroup_zpowers_of_sq_eq_one C.ha2, ?_⟩
    intro V hV hV2 hle
    apply le_antisymm _ hle
    intro v hv
    have hv2 : IsPGroup 2 (Subgroup.zpowers v) := hV2.to_le (Subgroup.zpowers_le.mpr hv)
    have hvN := hV hv
    rcases C.twoElt_triv hM5 (Subgroup.mem_centralizer_singleton_iff.mp hvN.1) hvN.2 hv2 with
      h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers a
  have hNC : ∀ g ∈ kerLayer Ω a, (∀ x : G, x ∈ Subgroup.zpowers a ↔
      g * x * g⁻¹ ∈ Subgroup.zpowers a) → ∀ x ∈ Subgroup.zpowers a, g * x = x * g := by
    intro g hg _ x hx
    obtain ⟨k, rfl⟩ := hx
    have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hg.1
    exact ((Commute.zpow_right hga k)).eq
  obtain ⟨o, ho, b, hb, rfl⟩ := exists_oddCore_mul_of_normalizer_le hsyl hNC n hn
  obtain ⟨k, rfl⟩ := hb
  dsimp only at hodd ⊢
  rcases zpow_of_sq C.ha2 k with h | h
  · rw [h, mul_one]; exact ho
  · exfalso
    rw [h] at hodd
    have hoN : o ∈ kerLayer Ω a := oddCoreIn_le _ ho
    have hoa : o * a = a * o := (Subgroup.mem_centralizer_singleton_iff.mp hoN.1)
    obtain ⟨j, hj⟩ := hodd
    have h1 : (o * a) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have hapow : a ^ (2 * j + 1) = a := by
      rw [pow_succ, pow_mul, sq, C.ha2, one_pow, one_mul]
    rw [(Commute.mul_pow hoa.symm.symm _), hapow] at h1
    have h2 : a = (o ^ (2 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : (o ^ (2 * j + 1))⁻¹ ∈ oddCoreIn (kerLayer Ω a) := inv_mem (pow_mem ho _)
    rw [← h2] at h3
    have h4 := eq_one_of_isPGroup_of_odd (isPGroup_zpowers_of_sq_eq_one C.ha2)
      (odd_card_oddCoreIn _) (Subgroup.mem_zpowers a) h3
    exact C.ha1 h4

theorem not_inner (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {τ cτ : G}
    (hτC : τ ∈ Subgroup.centralizer ({a} : Set G)) (hcτ : cτ * z * cτ⁻¹ = τ)
    (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ)
    (hτX : conjSub τ (layerX Ω a) = layerX Ω a) :
    ¬ ∃ yb, ∀ e, C25Y.layerAut (layerX Ω a) hτX e = yb * e * yb⁻¹ := by
  rintro ⟨yb, hyb⟩
  subst hcτ
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaGen Ω := C.hΩ
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', A, A', hD⟩ := C.om5'
  have hτ2 : (cτ * z * cτ⁻¹) * (cτ * z * cτ⁻¹) = 1 := by
    calc (cτ * z * cτ⁻¹) * (cτ * z * cτ⁻¹) = cτ * (z * z) * cτ⁻¹ := by group
      _ = 1 := by rw [C.hz2]; group
  have hyb2 : yb * yb = 1 := by
    apply hM.centerless _ _ _ _ _ _ _ hD
    intro x
    have h1 := C25Y.layerAut_involutive _ hτX hτ2 x
    rw [hyb, hyb] at h1
    calc yb * yb * x = (yb * (yb * x * yb⁻¹) * yb⁻¹) * (yb * yb) := by group
      _ = x * (yb * yb) := by rw [h1]
  by_cases hy1 : yb = 1
  · have hτT : cτ * z * cτ⁻¹ ∈ trivialOnQuot (layerX Ω a) := by
      rw [← layerAut_eq_id_iff _ hτX]
      intro e
      rw [hyb, hy1]
      group
    rcases C.twoElt_triv hM.centerless (Subgroup.mem_centralizer_singleton_iff.mp hτC) hτT
      (isPGroup_zpowers_of_sq_eq_one hτ2) with h | h
    · apply C.hz1
      calc z = cτ⁻¹ * (cτ * z * cτ⁻¹) * cτ := by group
        _ = 1 := by rw [h]; group
    · exact C.not_conj_z cτ h
  · obtain ⟨J, hJ, x, hxJ, hx4, hx2, hxc⟩ := hM.invFixFour _ _ _ _ _ _ _ hD yb hyb2 hy1
    have hfix : C25Y.layerAut (layerX Ω a) hτX x = x := by
      rw [hyb, hxc]
      group
    obtain ⟨h, hhC, hh⟩ := C.c25_8_one hτC hJ hxJ hx4 hx2 hfix
    exact hτn h (Subgroup.mem_centralizer_singleton_iff.mp hhC) hh

theorem oddCore_layer_le (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    oddCoreIn (layerX Ω a) ≤ oddCoreIn (kerLayer Ω a) := by
  have hΩ : HypOmegaGen Ω := C.hΩ
  refine le_oddCoreIn_of_normalizes (fun o ho => ?_) (fun n hn => ?_) (odd_card_oddCoreIn _)
  · have hoX : o ∈ layerX Ω a := oddCoreIn_le _ ho
    refine ⟨layerX_le_centralizer Ω a hoX,
      Generic.mem_normalizer_of_conjSub_eq (conjSub_eq_self_of_mem hoX), fun y hy => ?_⟩
    rw [commutatorElement_def]
    have h1 : y * o⁻¹ * y⁻¹ ∈ oddCoreIn (layerX Ω a) :=
      conj_mem_oddCoreIn hy ((oddCoreIn _).inv_mem ho)
    have := (oddCoreIn (layerX Ω a)).mul_mem ho h1
    simpa [mul_assoc] using this
  · have hX : n ∈ Subgroup.normalizer ((layerX Ω a : Subgroup G) : Set G) :=
      Generic.mem_normalizer_of_conjSub_eq (conjSub_layerX_of_mem hΩ hn.1)
    refine Subgroup.mem_normalizer_iff.mpr fun o => ⟨fun ho =>
      conj_mem_oddCoreIn_of_mem_normalizer hX ho, fun ho => ?_⟩
    have := conj_mem_oddCoreIn_of_mem_normalizer (inv_mem hX) ho
    simpa [mul_assoc] using this

theorem a_not_mem_hSub (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {τ cτ : G}
    (hτC : τ ∈ Subgroup.centralizer ({a} : Set G)) (hcτ : cτ * z * cτ⁻¹ = τ)
    (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ) :
    a ∉ hSub C.hΩ a τ hτC := by
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaGen Ω := C.hΩ
  have hτ2 : τ * τ = 1 := by
    rw [← hcτ]
    calc (cτ * z * cτ⁻¹) * (cτ * z * cτ⁻¹) = cτ * (z * z) * cτ⁻¹ := by group
      _ = 1 := by rw [C.hz2]; group
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', A, A', hD⟩ := C.om5'
  have haK := C.a_mem_kerLayer
  rintro ⟨y, ⟨k, rfl⟩, w, ⟨x, hx, o, ho, rfl⟩, ha⟩
  have hoN : o ∈ kerLayer Ω a := oddCoreIn_le _ ho
  rcases zpow_of_sq hτ2 k with h | h <;> dsimp only at h ha <;> rw [h] at ha
  ·
    rw [one_mul] at ha
    have hxN : x ∈ kerLayer Ω a := by
      have e : x = a * o⁻¹ := by rw [ha]; group
      rw [e]
      exact mul_mem haK (inv_mem hoN)
    have hxO : x ∈ oddCoreIn (layerX Ω a) := by
      have hxX : conjSub x (layerX Ω a) = layerX Ω a :=
          conjSub_eq_self_of_mem hx
      have hfix := (layerAut_eq_id_iff (layerX Ω a) hxX).mpr hxN.2
      refine (mk_eq_one_iff (layerX Ω a) ⟨x, hx⟩).mp ?_
      apply hM.centerless _ _ _ _ _ _ _ hD
      intro e
      have h1 := hfix e
      rw [layerAut_of_mem _ hx] at h1
      calc QuotientGroup.mk ⟨x, hx⟩ * e = (QuotientGroup.mk ⟨x, hx⟩ * e *
            (QuotientGroup.mk ⟨x, hx⟩)⁻¹) * QuotientGroup.mk ⟨x, hx⟩ := by group
        _ = e * QuotientGroup.mk ⟨x, hx⟩ := by rw [h1]
    have hxO' := C.oddCore_layer_le hxO
    have haO : x * o ∈ oddCoreIn (kerLayer Ω a) := mul_mem hxO' ho
    rw [← ha] at haO
    exact C.ha1 (eq_one_of_isPGroup_of_odd (isPGroup_zpowers_of_sq_eq_one C.ha2)
      (odd_card_oddCoreIn _) (Subgroup.mem_zpowers a) haO)
  ·
    have hτX : conjSub τ (layerX Ω a) = layerX Ω a :=
      conjSub_layerX_of_mem hΩ hτC
    apply C.not_inner hM hτC hcτ hτn hτX
    refine ⟨QuotientGroup.mk ⟨x⁻¹, inv_mem hx⟩, fun e => ?_⟩
    have e1 : τ = (a * o⁻¹) * x⁻¹ := by rw [ha]; group
    have hao : a * o⁻¹ ∈ kerLayer Ω a := mul_mem haK (inv_mem hoN)
    have hx1 : conjSub x⁻¹ (layerX Ω a) = layerX Ω a :=
      conjSub_eq_self_of_mem (inv_mem hx)
    have hao1 : conjSub (a * o⁻¹) (layerX Ω a) = layerX Ω a :=
      conjSub_layerX_of_mem hΩ hao.1
    have hfixa := (layerAut_eq_id_iff (layerX Ω a) hao1).mpr hao.2
    have h2 : conjSub ((a * o⁻¹) * x⁻¹) (layerX Ω a) = layerX Ω a :=
        by
      rw [← e1]; exact hτX
    have h3 := layerAut_mul_apply (layerX Ω a) hao1 hx1 h2 e
    rw [hfixa, layerAut_of_mem _ (inv_mem hx)] at h3
    have h4 : C25Y.layerAut (layerX Ω a) hτX e =
        C25Y.layerAut (layerX Ω a) h2 e := by
      subst e1
      rfl
    rw [h4, h3]
end Ctx





theorem conj_mem_kerLayer' {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c g n : G}
    (hn : n ∈ kerLayer Ω c) : g * n * g⁻¹ ∈ kerLayer Ω (g * c * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · have h := Subgroup.mem_centralizer_singleton_iff.mp hn.1
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g * n * g⁻¹ * (g * c * g⁻¹) = g * (n * c) * g⁻¹ := by group
      _ = g * (c * n) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * (g * n * g⁻¹) := by group
  · have h := trivialOnQuot_conjSub hn.2 g
    rwa [← layerX_conj hΩ] at h

theorem conjSub_kerLayer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (c g : G) :
    conjSub g (kerLayer Ω c) = kerLayer Ω (g * c * g⁻¹) := by
  ext n
  rw [mem_conjSub_iff]
  constructor
  · intro hn
    have := conj_mem_kerLayer' hΩ (g := g) hn
    simpa [mul_assoc] using this
  · intro hn
    have := conj_mem_kerLayer' hΩ (g := g⁻¹) hn
    simpa [mul_assoc] using this

theorem conj_mem_oddCore_kerLayer' {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c g o : G}
    (ho : o ∈ oddCoreIn (kerLayer Ω c)) :
    g * o * g⁻¹ ∈ oddCoreIn (kerLayer Ω (g * c * g⁻¹)) := by
  rw [← conjSub_kerLayer hΩ, oddCoreIn_conjSub_eq]
  exact ⟨o, ho, rfl⟩


theorem conj_mem_hSub {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c τ c' τ' g y : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G))
    (hτ' : τ' ∈ Subgroup.centralizer ({c'} : Set G)) (hc : g * c * g⁻¹ = c')
    (hgτ : g * τ * g⁻¹ ∈ hSub hΩ c' τ' hτ') (hy : y ∈ hSub hΩ c τ hτ) :
    g * y * g⁻¹ ∈ hSub hΩ c' τ' hτ' := by
  obtain ⟨w, ⟨k, rfl⟩, v, ⟨x, hx, o, ho, rfl⟩, rfl⟩ := hy
  have hx' : g * x * g⁻¹ ∈ layerX Ω c' := by
    rw [← hc, layerX_conj hΩ]
    exact ⟨x, hx, rfl⟩
  have ho' : g * o * g⁻¹ ∈ oddCoreIn (kerLayer Ω c') := by
    rw [← hc]; exact conj_mem_oddCore_kerLayer' hΩ ho
  have e : g * ((fun i : ℤ => τ ^ i) k * (x * o)) * g⁻¹ =
      (g * τ * g⁻¹) ^ k * ((g * x * g⁻¹) * (g * o * g⁻¹)) := by
    simp only [conj_zpow]
    group
  rw [e]
  exact mul_mem (zpow_mem hgτ k) (mul_mem (le_hSub_layer hΩ hτ' hx') (le_hSub_odd hΩ hτ' ho'))

theorem hSub_le_centralizer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {c τ : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) :
    hSub hΩ c τ hτ ≤ Subgroup.centralizer ({c} : Set G) := by
  rintro _ ⟨w, ⟨k, rfl⟩, v, ⟨x, hx, o, ho, rfl⟩, rfl⟩
  exact mul_mem (zpow_mem hτ k) (mul_mem (layerX_le_centralizer Ω c hx)
    (oddCoreIn_le _ ho).1)

theorem hSub_inf_le {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {z a τ σ : G}
    (hτ : τ ∈ Subgroup.centralizer ({a} : Set G))
    (hσ : σ ∈ Subgroup.centralizer ({a * z} : Set G)) :
    hSub hΩ a τ hτ ⊓ hSub hΩ (a * z) σ hσ ≤ Subgroup.centralizer ({z} : Set G) :=
  fun _ hx => mem_centralizer_z_of (hSub_le_centralizer hΩ hτ hx.1)
    (hSub_le_centralizer hΩ hσ hx.2)

structure Swaps (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ a τ σ : G) : Prop where
  ctx : Ctx Ω K K' W S R R' z t u₁ u₂ a
  τG : ∃ c : G, c * z * c⁻¹ = τ
  τa : τ * a = a * τ
  τz : τ * z = z * τ
  τn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ
  aτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ
  τX : τ ∈ layerX Ω (a * z)
  τK : conjSub τ K = K'
  σG : ∃ c : G, c * z * c⁻¹ = σ
  σa : σ * a = a * σ
  σz : σ * z = z * σ
  σn : ∀ h : G, h * (a * z) = (a * z) * h → h * z * h⁻¹ ≠ σ
  aσ : ¬ ∃ g : G, g * z * g⁻¹ = (a * z) * σ
  σX : σ ∈ layerX Ω a
  m : ∃ m ∈ layerX Ω (a * z), m * z * m⁻¹ = τ ∧ m * τ * m⁻¹ = z
namespace Swaps
variable {τ σ : G}
theorem τC (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) :
    τ ∈ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr D.τa
theorem σC (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) :
    σ ∈ Subgroup.centralizer ({a * z} : Set G) := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc σ * (a * z) = (σ * a) * z := by group
    _ = a * (σ * z) := by rw [D.σa]; group
    _ = a * z * σ := by rw [D.σz]; group
end Swaps


@[expose] def hBig {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (z a τ σ : G)
    (hτ : τ ∈ Subgroup.centralizer ({a} : Set G))
    (hσ : σ ∈ Subgroup.centralizer ({a * z} : Set G)) : Subgroup G :=
  mulSub (hSub hΩ a τ hτ ⊓ hSub hΩ (a * z) σ hσ)
    (oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    (fun _ hx _ ho => conj_mem_oddCoreIn (hSub_inf_le hΩ hτ hσ hx) ho)
namespace Ctx

theorem mem_hSub_of_conj (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {τ : G}
    (hτC : τ ∈ Subgroup.centralizer ({a} : Set G)) (hτG : ∃ c : G, c * z * c⁻¹ = τ)
    (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ) (haτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ)
    {b : G} (hba : b * a = a * b) (hbG : ∃ c : G, c * z * c⁻¹ = b)
    (hbn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ b) :
    b ∈ hSub C.hΩ a τ hτC := by
  have hτa : τ * a = a * τ := Subgroup.mem_centralizer_singleton_iff.mp hτC
  rcases C.two_orbits hM hτa hτG hτn haτ hba hbG with ⟨h, hh, hhz⟩ | ⟨x, hx, n, hn, hodd, hxn⟩
  · exact absurd hhz (hbn h hh)
  · have hnO := C.mem_oddCore_of_odd hM.centerless hn hodd
    rw [← hxn]
    have hΩ := C.hΩ
    have hxH := le_hSub_layer hΩ hτC hx
    have hnH := le_hSub_odd hΩ hτC hnO
    exact mul_mem (mul_mem (mul_mem hxH hnH) (mem_hSub_self hΩ hτC)) (inv_mem (mul_mem hxH hnH))

theorem norm_fix_z (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {g : G}
    (hg : g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G)) : g * z * g⁻¹ = z := by
  have hm := (Subgroup.mem_normalizer_iff.mp hg z).mp ((z_facts C.hyp).1)
  rcases C.hA0 _ hm with h | h | h | h
  · exfalso; apply C.hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact absurd h (C.not_conj_z g)
  · exact h
  · exact absurd h (C.swap.not_conj_z g)

theorem norm_a_cases (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {g : G}
    (hg : g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G)) : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a * z := by
  have hm := (Subgroup.mem_normalizer_iff.mp hg a).mp C.haA
  have hgz := C.norm_fix_z hg
  rcases C.hA0 _ hm with h | h | h | h
  · exfalso; apply C.ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exfalso
    apply C.not_conj_z g⁻¹
    calc g⁻¹ * z * g⁻¹⁻¹ = g⁻¹ * (g * a * g⁻¹) * g := by rw [h]; group
      _ = a := by group
  · exact Or.inr h
end Ctx
namespace Swaps
variable {τ σ : G}

theorem a_not_mem_hBig (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) :
    a ∉ hBig D.ctx.hΩ z a τ σ D.τC D.σC := by
  have C := D.ctx
  rintro ⟨h, hh, o, ho, hao⟩
  have hΩ := D.ctx.hΩ
  have hha : h * a = a * h :=
    Subgroup.mem_centralizer_singleton_iff.mp (hSub_le_centralizer hΩ D.τC hh.1)
  have he : h = a * o⁻¹ := by rw [hao]; group
  have hhia : h⁻¹ * a = a * h⁻¹ := by
    calc h⁻¹ * a = h⁻¹ * (a * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * a) * h⁻¹ := by rw [hha]
      _ = a * h⁻¹ := by group
  have hoa : o * a = a * o := by
    have e : o = h⁻¹ * a := by rw [hao]; group
    rw [e]
    calc h⁻¹ * a * a = (a * h⁻¹) * a := by rw [hhia]
      _ = a * (h⁻¹ * a) := by group
  have hodd : Odd (orderOf o) := by
    have h1 : orderOf o ∣ Nat.card (oddCoreIn (Subgroup.centralizer ({z} : Set G))) := by
      have := orderOf_dvd_natCard (⟨o, ho⟩ : oddCoreIn (Subgroup.centralizer ({z} : Set G)))
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (odd_card_oddCoreIn _) h1
  obtain ⟨j, hj⟩ := hodd
  have hcomm : Commute a o⁻¹ := by
    show a * o⁻¹ = o⁻¹ * a
    calc a * o⁻¹ = o⁻¹ * (o * a) * o⁻¹ := by group
      _ = o⁻¹ * (a * o) * o⁻¹ := by rw [hoa]
      _ = o⁻¹ * a := by group
  have hapow : a ^ (2 * j + 1) = a := by
    rw [pow_succ, pow_mul, sq, C.ha2, one_pow, one_mul]
  have hopow : o ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one o
  have hpow : h ^ (2 * j + 1) = a := by
    rw [he, hcomm.mul_pow, hapow, inv_pow, hopow, inv_one, mul_one]
  have haH : a ∈ hSub hΩ a τ D.τC := by
    have := pow_mem hh.1 (2 * j + 1)
    rwa [hpow] at this
  obtain ⟨cτ, hcτ⟩ := D.τG
  exact C.a_not_mem_hSub hM D.τC hcτ D.τn haH

theorem conj_mem_hInf (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) {g y : G}
    (hg : g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G))
    (hy : y ∈ hSub D.ctx.hΩ a τ D.τC ⊓
      hSub D.ctx.hΩ (a * z) σ D.σC) :
    g * y * g⁻¹ ∈ hSub D.ctx.hΩ a τ D.τC ⊓
      hSub D.ctx.hΩ (a * z) σ D.σC := by
  have C := D.ctx
  have hΩ := D.ctx.hΩ
  have hgz := C.norm_fix_z hg
  obtain ⟨cτ, hcτ⟩ := D.τG
  obtain ⟨cσ, hcσ⟩ := D.σG
  have hconjG : ∀ (w c : G), c * z * c⁻¹ = w → (g * c) * z * (g * c)⁻¹ = g * w * g⁻¹ := by
    intro w c hc
    calc (g * c) * z * (g * c)⁻¹ = g * (c * z * c⁻¹) * g⁻¹ := by group
      _ = g * w * g⁻¹ := by rw [hc]
  have hpull : ∀ (b b' w : G), g * b * g⁻¹ = b' →
      (∀ h : G, h * b = b * h → h * z * h⁻¹ ≠ w) →
      ∀ h : G, h * b' = b' * h → h * z * h⁻¹ ≠ g * w * g⁻¹ := by
    intro b b' w hb hn h hh hhz
    apply hn (g⁻¹ * h * g)
    · calc g⁻¹ * h * g * b = g⁻¹ * (h * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * (h * b') * g := by rw [hb]
        _ = g⁻¹ * (b' * h) * g := by rw [hh]
        _ = g⁻¹ * ((g * b * g⁻¹) * h) * g := by rw [hb]
        _ = b * (g⁻¹ * h * g) := by group
    · calc g⁻¹ * h * g * z * (g⁻¹ * h * g)⁻¹ = g⁻¹ * (h * (g * z * g⁻¹) * h⁻¹) * g := by group
        _ = g⁻¹ * (g * w * g⁻¹) * g := by rw [hgz, hhz]
        _ = w := by group
  have hcomm : ∀ (b b' w : G), g * b * g⁻¹ = b' → w * b = b * w →
      (g * w * g⁻¹) * b' = b' * (g * w * g⁻¹) := by
    intro b b' w hb hw
    rw [← hb]
    calc g * w * g⁻¹ * (g * b * g⁻¹) = g * (w * b) * g⁻¹ := by group
      _ = g * (b * w) * g⁻¹ := by rw [hw]
      _ = g * b * g⁻¹ * (g * w * g⁻¹) := by group
  have hσaz : σ * (a * z) = (a * z) * σ := Subgroup.mem_centralizer_singleton_iff.mp D.σC
  have hτaz : τ * (a * z) = (a * z) * τ := by
    calc τ * (a * z) = (τ * a) * z := by group
      _ = a * (τ * z) := by rw [D.τa]; group
      _ = (a * z) * τ := by rw [D.τz]; group
  rcases C.norm_a_cases hg with ha | ha
  · have haz : g * (a * z) * g⁻¹ = a * z := by
      calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
        _ = a * z := by rw [ha, hgz]
    have hgτ : g * τ * g⁻¹ ∈ hSub hΩ a τ D.τC :=
      C.mem_hSub_of_conj hM D.τC D.τG D.τn D.aτ (hcomm a a τ ha D.τa) ⟨g * cτ, hconjG τ cτ hcτ⟩
        (hpull a a τ ha D.τn)
    have hgσ : g * σ * g⁻¹ ∈ hSub hΩ (a * z) σ D.σC :=
      C.swap.mem_hSub_of_conj hM D.σC D.σG D.σn D.aσ (hcomm (a * z) (a * z) σ haz hσaz)
        ⟨g * cσ, hconjG σ cσ hcσ⟩ (hpull (a * z) (a * z) σ haz D.σn)
    exact ⟨conj_mem_hSub hΩ D.τC D.τC ha hgτ hy.1,
      conj_mem_hSub hΩ D.σC D.σC haz hgσ hy.2⟩
  · have haz : g * (a * z) * g⁻¹ = a := by
      calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
        _ = a := by rw [ha, hgz, C.mul_z_mul_z]
    have hgτ : g * τ * g⁻¹ ∈ hSub hΩ (a * z) σ D.σC :=
      C.swap.mem_hSub_of_conj hM D.σC D.σG D.σn D.aσ (hcomm a (a * z) τ ha D.τa)
        ⟨g * cτ, hconjG τ cτ hcτ⟩ (hpull a (a * z) τ ha D.τn)
    have hgσ : g * σ * g⁻¹ ∈ hSub hΩ a τ D.τC :=
      C.mem_hSub_of_conj hM D.τC D.τG D.τn D.aτ (hcomm (a * z) a σ haz hσaz)
        ⟨g * cσ, hconjG σ cσ hcσ⟩ (hpull (a * z) a σ haz D.σn)
    exact ⟨conj_mem_hSub hΩ D.σC D.τC haz hgσ hy.2,
      conj_mem_hSub hΩ D.τC D.σC ha hgτ hy.1⟩

theorem conj_mem_hBig (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) {c y : G} (hc : c * z * c⁻¹ = z)
    (hy : y ∈ hBig D.ctx.hΩ z a τ σ D.τC D.σC) :
    c * y * c⁻¹ ∈ hBig D.ctx.hΩ z a τ σ D.τC D.σC := by
  have C := D.ctx
  have hΩ := D.ctx.hΩ
  obtain ⟨o₁, ho₁, hg⟩ := C.frattini hc
  obtain ⟨h, hh, o, ho, rfl⟩ := hy
  set g := o₁⁻¹ * c with hgdef
  have hcz : c ∈ Subgroup.centralizer ({z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc c * z = (c * z * c⁻¹) * c := by group
      _ = z * c := by rw [hc]
  have ho₁z : o₁ ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho₁
  have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := mul_mem (inv_mem ho₁z) hcz
  have hh' := conj_mem_hInf hM D hg hh
  have hh'z := hSub_inf_le hΩ D.τC D.σC hh'
  have ho' : g * o * g⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    conj_mem_oddCoreIn hgz ho
  have ho₁' : (g * h * g⁻¹)⁻¹ * o₁ * (g * h * g⁻¹)⁻¹⁻¹ ∈
      oddCoreIn (Subgroup.centralizer ({z} : Set G)) := conj_mem_oddCoreIn (inv_mem hh'z) ho₁
  refine ⟨g * h * g⁻¹, hh', ((g * h * g⁻¹)⁻¹ * o₁ * (g * h * g⁻¹)⁻¹⁻¹) * (g * o * g⁻¹) * o₁⁻¹,
    mul_mem (mul_mem ho₁' ho') (inv_mem ho₁), ?_⟩
  rw [hgdef]
  group

theorem extremal_mem_hBig (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) {g : G}
    (hg : (g⁻¹ * a * g) * z = z * (g⁻¹ * a * g)) :
    a⁻¹ * (g⁻¹ * a * g) ∈
      hBig D.ctx.hΩ z a τ σ D.τC D.σC := by
  have C := D.ctx
  have hΩ := D.ctx.hΩ
  obtain ⟨hzY, -, -, -, -, A, A', -⟩ := C.om5'
  obtain ⟨hzY', -, -, -, -, A, A', -⟩ := C.swap.om5'
  set H := hBig hΩ z a τ σ D.τC D.σC with hH
  have hzH₀ : z ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC :=
    ⟨le_hSub_layer hΩ D.τC hzY, le_hSub_layer hΩ D.σC hzY'⟩
  have hτH₀ : τ ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC :=
    ⟨mem_hSub_self hΩ D.τC, le_hSub_layer hΩ D.σC D.τX⟩
  have hzH : z ∈ H := le_mulSub_left _ hzH₀
  have hτH : τ ∈ H := le_mulSub_left _ hτH₀
  have hOH : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ H := le_mulSub_right _
  have hconj : ∀ c : G, c * z * c⁻¹ = z → a⁻¹ * (c * a * c⁻¹) ∈ H := by
    intro c hc
    obtain ⟨o, ho, h | h⟩ := C.conj_a_mem hc
    · rw [h]
      have e : a⁻¹ * (a * o) = o := by group
      rw [e]; exact hOH ho
    · rw [h]
      have e : a⁻¹ * (a * z * o) = z * o := by group
      rw [e]; exact mul_mem hzH (hOH ho)
  obtain ⟨m, hmX, hmz, hmτ⟩ := D.m
  have hm : m * (a * z) = (a * z) * m :=
    Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω (a * z) hmX)
  have hg' : (g⁻¹ * a * g⁻¹⁻¹) * z = z * (g⁻¹ * a * g⁻¹⁻¹) := by rw [inv_inv]; exact hg
  rcases C.pair_count hM D.τa D.τG D.τn D.aτ hm hmz hmτ hg' with ⟨c, hc, hca⟩ | ⟨c, hc, hca⟩
  · rw [inv_inv] at hca
    rw [← hca]
    exact hconj c hc
  · rw [inv_inv] at hca
    rw [← hca]
    have e : a⁻¹ * (c * (a * z * τ) * c⁻¹) = (a⁻¹ * (c * a * c⁻¹)) * (c * (z * τ) * c⁻¹) := by
      group
    rw [e]
    exact mul_mem (hconj c hc) (conj_mem_hBig hM D hc (mul_mem hzH hτH))
end Swaps



namespace Swaps
variable {τ σ : G}

theorem mem_hInf_of_triv (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) {c w : G}
    (hca : c ∈ Subgroup.centralizer ({a} : Set G))
    (hcaz : c ∈ Subgroup.centralizer ({a * z} : Set G))
    (hwa : w ∈ layerX Ω a) (hwaz : w ∈ layerX Ω (a * z))
    (h1 : c * w⁻¹ ∈ trivialOnQuot (layerX Ω a))
    (h2 : c * w⁻¹ ∈ trivialOnQuot (layerX Ω (a * z))) :
    c ∈ hSub D.ctx.hΩ a τ D.τC ⊓
      hSub D.ctx.hΩ (a * z) σ D.σC := by
  have C := D.ctx
  have hΩ := D.ctx.hΩ
  set c' := c * w⁻¹ with hc'
  have hc'a : c' ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem hca (inv_mem (layerX_le_centralizer Ω a hwa))
  have hc'az : c' ∈ Subgroup.centralizer ({a * z} : Set G) :=
    mul_mem hcaz (inv_mem (layerX_le_centralizer Ω (a * z) hwaz))
  have hK1 : c' ∈ kerLayer Ω a := ⟨hc'a, h1⟩
  have hK2 : c' ∈ kerLayer Ω (a * z) := ⟨hc'az, h2⟩
  have hodd : Odd (orderOf c') := by
    obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c').ne'
    have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
    have hord : orderOf (c' ^ m) = 2 ^ k := by
      rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hn.symm), hn, Nat.mul_div_cancel _ (by omega)]
    have h2p : IsPGroup 2 (Subgroup.zpowers (c' ^ m)) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord])
    have hpa : c' ^ m * a = a * c' ^ m :=
      Subgroup.mem_centralizer_singleton_iff.mp (pow_mem hc'a m)
    have hpaz : c' ^ m * (a * z) = (a * z) * c' ^ m :=
      Subgroup.mem_centralizer_singleton_iff.mp (pow_mem hc'az m)
    have hone : c' ^ m = 1 := by
      rcases C.twoElt_triv hM.centerless hpa (pow_mem h1 m) h2p with e | e
      · exact e
      · exfalso
        rcases C.swap.twoElt_triv hM.centerless hpaz (pow_mem h2 m) h2p with e' | e'
        · exact C.ha1 (e.symm.trans e')
        · apply C.hz1
          have : a = a * z := e.symm.trans e'
          calc z = a⁻¹ * (a * z) := by group
            _ = a⁻¹ * a := by rw [← this]
            _ = 1 := by group
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hone)
  have hO1 := C.mem_oddCore_of_odd hM.centerless hK1 hodd
  have hO2 := C.swap.mem_oddCore_of_odd hM.centerless hK2 hodd
  have e : c = c' * w := by rw [hc']; group
  rw [e]
  exact ⟨mul_mem (le_hSub_odd hΩ D.τC hO1) (le_hSub_layer hΩ D.τC hwa),
    mul_mem (le_hSub_odd hΩ D.σC hO2) (le_hSub_layer hΩ D.σC hwaz)⟩
end Swaps


end Main

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL
