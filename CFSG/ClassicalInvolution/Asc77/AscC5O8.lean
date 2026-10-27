module

public import CFSG.ClassicalInvolution.Asc77.AscC5O8B
public import CFSG.ClassicalInvolution.Asc77.AscC25Y4
public import CFSG.ClassicalInvolution.Asc77.AscC25Y5

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G]

theorem layerAut_mul_apply (Y : Subgroup G) {x y : G} (hx : conjSub x Y = Y)
    (hy : conjSub y Y = Y) (hxy : conjSub (x * y) Y = Y) (e : ↥Y ⧸ classicalInvolutionOddCore ↥Y) :
    C25Y.layerAut Y hxy e = C25Y.layerAut Y hx (C25Y.layerAut Y hy e) := by
  induction e using QuotientGroup.induction_on with
  | H w =>
    rw [C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    simp only [C25Y.coe_conjOnSub]
    group

@[expose] def kerLayer [Finite G] (Ω : Set (Subgroup G)) (c : G) : Subgroup G :=
  Subgroup.centralizer ({c} : Set G) ⊓ trivialOnQuot (exactLayer Ω c)

variable [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem two_orbits [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {τ : G} (hτa : τ * a = a * τ)
    (hτG : ∃ c : G, c * z * c⁻¹ = τ) (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ)
    (haτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ) {b : G} (hba : b * a = a * b)
    (hbG : ∃ c : G, c * z * c⁻¹ = b) :
    (∃ h : G, h * a = a * h ∧ h * z * h⁻¹ = b) ∨
      ∃ x ∈ exactLayer Ω a, ∃ n ∈ kerLayer Ω a, Odd (orderOf n) ∧ (x * n) * τ * (x * n)⁻¹ = b := by
  classical
  by_cases hbz : ∃ h : G, h * a = a * h ∧ h * z * h⁻¹ = b
  · exact Or.inl hbz
  right
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz2 := C.hz2
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hD⟩ := C.om5
  obtain ⟨D, hD1, i₀, hDi⟩ := hD.lie
  have hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
    subst hi
    simp only [IsOrthTag] at hDi
    rcases hDi with ⟨-, ht, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · rw [ht]; exact ⟨by decide, by decide⟩
    all_goals omega
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
  have hbX : conjSub b (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hΩ.conjInvariant hbCa
  have hτX : conjSub τ (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hΩ.conjInvariant hτCa
  have hnofix : ∀ (w cw : G) (hw : w ∈ Subgroup.centralizer ({a} : Set G)),
      cw * z * cw⁻¹ = w → (∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ w) →
      ∀ J ∈ oddQuotientFamily (exactPair Ω a), ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 →
        C25Y.layerAut (exactLayer Ω a) (conjSub_exactLayer hΩ.conjInvariant hw) x ≠ x := by
    intro w cw hw hcw hn J hJ x hxJ hx4 hx2 hfix
    subst hcw
    obtain ⟨h, hhC, hh⟩ := C25Y.c25_8_one C.hyp C.ha2 hzY hK₂ D hD1 hD4 hw hJ hxJ hx4 hx2 hfix
    exact hn h (Subgroup.mem_centralizer_singleton_iff.mp hhC) hh
  have hnb := hnofix b cb hbCa hcb (fun h hh hhz => hbz ⟨h, hh, hhz⟩)
  have hnτ := hnofix τ cτ hτCa hcτ hτn
  obtain ⟨gb, hg⟩ := hM.excClass _ _ _ _ _ _ _ hD (C25Y.layerAut _ hbX) (C25Y.layerAut _ hτX)
    (C25Y.layerAut_involutive _ hbX hb2) (C25Y.layerAut_involutive _ hτX hτ2) hnb hnτ
    (C.not_hasBigFix hM hb2 hbX hcb) (C.not_hasBigFix hM hτ2 hτX hcτ)
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective gb
  have hg₀X : (g₀ : G) ∈ exactLayer Ω a := g₀.2
  have hg₀a : (g₀ : G) * a = a * g₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω a hg₀X)
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
  have hvX : conjSub v (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hΩ.conjInvariant hvCa
  have hvact : ∀ e, C25Y.layerAut (exactLayer Ω a) hvX e =
      QuotientGroup.mk g₀ * C25Y.layerAut (exactLayer Ω a) hbX
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
  have hdT : d ∈ trivialOnQuot (exactLayer Ω a) := by
    rw [← layerAut_eq_id_iff (exactLayer Ω a) (conjSub_exactLayer hΩ.conjInvariant hdCa)]
    intro e
    rw [layerAut_mul_apply _ hτX hvX _ e, hg, hvact]
    have e1 : (QuotientGroup.mk g₀ : ↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore
        ↥(exactLayer Ω a))⁻¹ * (QuotientGroup.mk g₀ * C25Y.layerAut (exactLayer Ω a) hbX
          ((QuotientGroup.mk g₀)⁻¹ * e * QuotientGroup.mk g₀) * (QuotientGroup.mk g₀)⁻¹) *
          QuotientGroup.mk g₀ =
        C25Y.layerAut (exactLayer Ω a) hbX ((QuotientGroup.mk g₀)⁻¹ * e * QuotientGroup.mk g₀) := by
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
    refine ⟨(g₀ : G)⁻¹, (exactLayer Ω a).inv_mem hg₀X, n, hnK, hnodd, ?_⟩
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
    have hdT' : d ^ m ∈ trivialOnQuot (exactLayer Ω a) := pow_mem hdT m
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

theorem pair_count [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {τ m : G} (hτa : τ * a = a * τ)
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
        Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω a hx)
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

end CFSG.ClassicalInvolution.Asc77.C5O
