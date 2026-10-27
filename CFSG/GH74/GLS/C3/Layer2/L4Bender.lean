module

public import CFSG.GH74.Uniqueness.Statements
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer2.L4Lift

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.Uniqueness CFSG.GH74.Uniqueness.Bender

section Transport

variable {Y : Type} [Group Y] [Finite Y]

noncomputable def derivedBarEquiv (h : commutator Y = ⊤) :
    derivedBar Y ≃* Y ⧸ pPrimeCore 2 Y := by
  let e₁ : ↥(commutator Y) ≃* Y := (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
  refine QuotientGroup.congr ((pPrimeCore 2 Y).subgroupOf (commutator Y)) (pPrimeCore 2 Y) e₁ ?_
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hy
    have hyc : y ∈ commutator Y := by rw [h]; trivial
    exact ⟨⟨y, hyc⟩, hy, rfl⟩

omit [Finite Y] in
theorem isBenderGroup_quot (h : commutator Y = ⊤)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (derivedBar Y)) :
    CFSG.BenderSuzuki.IsBenderGroup (Y ⧸ pPrimeCore 2 Y) := by
  obtain ⟨n, i, e, hBT⟩ := isBenderGroup_iff_exists_benderType.1 hB
  exact isBenderGroup_iff_exists_benderType.2 ⟨n, i, e, hBT.of_mulEquiv (derivedBarEquiv h)⟩

end Transport

section Lifting

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_conj_of_mk_eq {O : Subgroup Y} [O.Normal] (hO : ¬ 2 ∣ Nat.card O) {r w : Y}
    (hr : r * r = 1) (hw : w * w = 1) (hrw : (QuotientGroup.mk r : Y ⧸ O) = QuotientGroup.mk w) :
    ∃ o ∈ O, o * r * o⁻¹ = w := by
  have hodd1 : ∀ y : Y, y * y = 1 → y ∈ O → y = 1 := by
    intro y hy hyO
    have h2 : orderOf (⟨y, hyO⟩ : O) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa [sq] using hy
    have h3 : orderOf (⟨y, hyO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    have h4 : orderOf (⟨y, hyO⟩ : O) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h5 | h5
      · exact h5
      · exfalso; apply hO; rw [← h5]; exact h3
    have : (⟨y, hyO⟩ : O) = 1 := orderOf_eq_one_iff.1 h4
    exact congrArg Subtype.val this
  have hrw' : r⁻¹ * w ∈ O := QuotientGroup.eq.1 hrw
  by_cases hr1 : r = 1
  · subst hr1
    have : w ∈ O := by simpa using hrw'
    exact ⟨1, one_mem _, by simp [hodd1 w hw this]⟩
  have hw1 : w ≠ 1 := by
    intro h1
    apply hr1
    rw [h1] at hrw'
    apply hodd1 r hr
    simpa using O.inv_mem hrw'
  set H₀ : Subgroup Y := O ⊔ zpowers r with hH₀
  have hwH : w ∈ H₀ := by
    have : w = r * (r⁻¹ * w) := by group
    rw [this]
    exact H₀.mul_mem ((le_sup_right : zpowers r ≤ H₀) (mem_zpowers r))
      ((le_sup_left : O ≤ H₀) hrw')
  have hpr : IsPGroup 2 (zpowers r) := by
    intro g
    obtain ⟨g, hg⟩ := g
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    show (r ^ m) ^ (2 ^ 1) = 1
    have h2 : r ^ (2 : ℕ) = 1 := by rw [sq]; exact hr
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  have hpw : IsPGroup 2 (zpowers w) := by
    intro g
    obtain ⟨g, hg⟩ := g
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    show (w ^ m) ^ (2 ^ 1) = 1
    have h2 : w ^ (2 : ℕ) = 1 := by rw [sq]; exact hw
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  have hSyl : IsSylowOf 2 (zpowers r) H₀ := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hpr, ?_⟩
    rw [hH₀, relIndex_sup_eq_relIndex_of_normal O (zpowers r)]
    intro hdvd
    apply hO
    refine hdvd.trans ?_
    exact Subgroup.index_dvd_card _
  obtain ⟨k, hkH, hk⟩ := exists_mem_conj_le_of_isSylowOf hSyl
    (zpowers_le.2 hwH) hpw
  have hkw : k⁻¹ * w * k ∈ zpowers r := hk w (mem_zpowers w)
  have hkw' : k⁻¹ * w * k = r := by
    rcases (mem_zpowers_iff_of_mul_self' hr).1 hkw with h1 | h1
    · exfalso; apply hw1
      have : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
      rw [this, h1]; group
    · exact h1
  have hwk : w = k * r * k⁻¹ := by
    have : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
    rw [this, hkw']
  rw [Subgroup.mem_sup_of_normal_left] at hkH
  obtain ⟨o, ho, s, hs, hos⟩ := hkH
  refine ⟨o, ho, ?_⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
  rw [hwk, ← hos]
  have hcomm : r ^ m * r = r * r ^ m := (Commute.zpow_left (Commute.refl r) m).eq
  calc o * r * o⁻¹ = o * (r ^ m * r * (r ^ m)⁻¹) * o⁻¹ := by rw [hcomm]; group
    _ = o * r ^ m * r * (o * r ^ m)⁻¹ := by group

end Lifting

theorem bender_sylow_card {Y : Type} [Group Y] [Finite Y] {Zs : Set Y}
    (hZinv : ∀ z ∈ Zs, ∀ g : Y, g * z * g⁻¹ ∈ Zs) (hZ2 : ∀ z ∈ Zs, z * z = 1)
    (hperf : commutator Y = ⊤)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (derivedBar Y))
    (hZO : ∀ z ∈ Zs, z ∉ pPrimeCore 2 Y)
    {R K4 : Subgroup Y} (hR : IsSylowOf 2 R ⊤) (hK4R : K4 ≤ R) (hK4card : Nat.card K4 = 4)
    (hK4Z : ∀ y ∈ K4, y ≠ 1 → y ∈ Zs) (hRZ : ∀ y ∈ R, y ∈ Zs → y ∈ K4) :
    (∀ r ∈ R, r * r = 1 → r ∈ K4) ∧ (Nat.card R = 4 ∨ 64 ≤ Nat.card R) := by
  set O := pPrimeCore 2 Y with hO
  have : O.Normal := pPrimeCore_normal
  have hOodd : ¬ 2 ∣ Nat.card O := by
    have := pPrimeCore_coprime_card (p := 2) (G := Y)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 this
  have hBq := isBenderGroup_quot hperf hB
  obtain ⟨n, i, e, hBT⟩ := isBenderGroup_iff_exists_benderType.1 hBq
  obtain ⟨-, hRp, hRidx⟩ := isSylowOf_iff.1 hR
  have hRidx' : ¬ 2 ∣ R.index := by rwa [Subgroup.relIndex_top_right] at hRidx
  have hRO : ∀ g ∈ R, g ∈ O → g = 1 := by
    intro g hgR hgO
    obtain ⟨k, hk⟩ := hRp ⟨g, hgR⟩
    have h1 : orderOf g ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      exact congrArg Subtype.val hk
    have h2 : orderOf g ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨g, hgO⟩ : O)
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card O) := by
      apply Nat.Coprime.pow_left
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hOodd
    have : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.1 this
  let Q : Sylow 2 Y := hRp.toSylow hRidx'
  let P : Sylow 2 (Y ⧸ O) := Sylow.mapSurjective (QuotientGroup.mk'_surjective O) Q
  have hPcoe : (P : Subgroup (Y ⧸ O)) = R.map (QuotientGroup.mk' O) := by
    show Q.map (QuotientGroup.mk' O) = _
    rfl
  obtain ⟨t, hc⟩ := hBT.exists_benderCore P
  have hrc : (rootCenter (P : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) ⊆
      (QuotientGroup.mk' O) '' (K4 : Set Y) := by
    intro z hz
    by_cases hz1 : z = 1
    · exact ⟨1, one_mem _, by simp [hz1]⟩
    have hzP : z ∈ (P : Subgroup (Y ⧸ O)) := rootCenter_le _ hz
    rw [hPcoe] at hzP
    obtain ⟨r, hrR, hrz⟩ := hzP
    have hz2 : z * z = 1 := hc.center_sq z hz
    have hrr : r * r = 1 := by
      have h1 : r * r ∈ O := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
        have : (QuotientGroup.mk r : Y ⧸ O) = z := hrz
        rw [this, hz2]
      exact hRO _ (R.mul_mem hrR hrR) h1
    obtain ⟨k, hkK, hk1⟩ : ∃ k ∈ K4, k ≠ 1 := by
      by_contra hno
      push Not at hno
      have : (K4 : Set Y) ⊆ {1} := fun k hk => hno k hk
      have h1 : (K4 : Set Y).ncard ≤ ({1} : Set Y).ncard := Set.ncard_le_ncard this (Set.toFinite _)
      have h2 : (K4 : Set Y).ncard = Nat.card K4 := (Nat.card_coe_set_eq _).symm
      rw [Set.ncard_singleton] at h1
      omega
    have hkZ : k ∈ Zs := hK4Z k hkK hk1
    have hkO : k ∉ O := hZO k hkZ
    have hkk := hZ2 k hkZ
    have hmk2 : (QuotientGroup.mk k : Y ⧸ O) * QuotientGroup.mk k = 1 := by
      rw [← QuotientGroup.mk_mul, hkk]; rfl
    have hmk1 : (QuotientGroup.mk k : Y ⧸ O) ≠ 1 := by
      intro h1
      exact hkO ((QuotientGroup.eq_one_iff _).1 h1)
    have hconj := hc.isConj_of_involutions hmk2 hmk1 hz2 hz1
    obtain ⟨cbar, hcbar⟩ := isConj_iff.1 hconj
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cbar
    have hw : (QuotientGroup.mk (c * k * c⁻¹) : Y ⧸ O) = z := by
      rw [← hcbar]; rfl
    have hwZ : c * k * c⁻¹ ∈ Zs := hZinv k hkZ c
    have hww := hZ2 _ hwZ
    have hmk : (QuotientGroup.mk r : Y ⧸ O) = QuotientGroup.mk (c * k * c⁻¹) := by
      have : (QuotientGroup.mk r : Y ⧸ O) = z := hrz
      rw [this, hw]
    obtain ⟨o, hoO, hor⟩ := exists_conj_of_mk_eq hOodd hrr hww hmk
    have hrZ : r ∈ Zs := by
      have : r = o⁻¹ * (c * k * c⁻¹) * (o⁻¹)⁻¹ := by rw [← hor]; group
      rw [this]
      exact hZinv _ hwZ o⁻¹
    exact ⟨r, hRZ r hrR hrZ, hrz⟩
  have hinvK : ∀ r ∈ R, r * r = 1 → r ∈ K4 := by
    intro r hrR hrr
    by_cases hr1 : r = 1
    · rw [hr1]; exact one_mem _
    have hmk1 : (QuotientGroup.mk r : Y ⧸ O) ≠ 1 := by
      intro h1
      exact hr1 (hRO r hrR ((QuotientGroup.eq_one_iff _).1 h1))
    have hmk2 : (QuotientGroup.mk r : Y ⧸ O) * QuotientGroup.mk r = 1 := by
      rw [← QuotientGroup.mk_mul, hrr]; rfl
    have hmkP : (QuotientGroup.mk r : Y ⧸ O) ∈ (P : Subgroup (Y ⧸ O)) := by
      rw [hPcoe]; exact ⟨r, hrR, rfl⟩
    have hord : orderOf (QuotientGroup.mk r : Y ⧸ O) = 2 := by
      apply orderOf_eq_prime _ hmk1
      rw [sq]; exact hmk2
    have hzr : (QuotientGroup.mk r : Y ⧸ O) ∈ rootCenter (P : Subgroup (Y ⧸ O)) :=
      (hc.involution_iff.1 ⟨le_borel _ hmkP, hord⟩).1
    obtain ⟨r', hr'K, hr'⟩ := hrc hzr
    have hr'' : (QuotientGroup.mk r' : Y ⧸ O) = QuotientGroup.mk r := hr'
    have h1 : r'⁻¹ * r ∈ O := QuotientGroup.eq.1 hr''
    have h2 : r'⁻¹ * r ∈ R := R.mul_mem (R.inv_mem (hK4R hr'K)) hrR
    have h3 : r'⁻¹ * r = 1 := hRO _ h2 h1
    have : r = r' := (inv_mul_eq_one.1 h3).symm
    rw [this]; exact hr'K
  refine ⟨hinvK, ?_⟩
  have hcard1 : 2 ^ n = Nat.card (rootCenter (P : Subgroup (Y ⧸ O))) := hc.card_center.symm
  have hcard2 : (rootCenter (P : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)).ncard ≤ 4 := by
    have h1 := Set.ncard_le_ncard hrc (Set.toFinite _)
    have h2 : ((QuotientGroup.mk' O) '' (K4 : Set Y)).ncard ≤ (K4 : Set Y).ncard :=
      Set.ncard_image_le (Set.toFinite _)
    have h3 : (K4 : Set Y).ncard = Nat.card K4 := (Nat.card_coe_set_eq _).symm
    omega
  have hcard3 : (rootCenter (P : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)).ncard =
      Nat.card (rootCenter (P : Subgroup (Y ⧸ O))) := Nat.card_coe_set_eq _
  have hn4 : 2 ^ n ≤ 4 := by omega
  obtain ⟨hi1, hn2⟩ := hBT.two_le
  have hn : n = 2 := by
    by_contra hne
    have : 3 ≤ n := by omega
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
    omega
  subst hn
  have hRP : Nat.card R = Nat.card (P : Subgroup (Y ⧸ O)) := by
    have hinj : Function.Injective ((QuotientGroup.mk' O).comp R.subtype) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have : (g : Y) ∈ O := (QuotientGroup.eq_one_iff _).1 hg
      exact Subtype.ext (hRO _ g.2 this)
    rw [hPcoe]
    have : ((QuotientGroup.mk' O).comp R.subtype).range = R.map (QuotientGroup.mk' O) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← this]
    exact Nat.card_congr (Equiv.ofInjective _ hinj)
  have hPcard : Nat.card (P : Subgroup (Y ⧸ O)) = (2 ^ 2) ^ i := hc.card_eq
  rcases hBT.cases' with ⟨hi, -, -⟩ | ⟨hi, -, a, ha, hna⟩ | ⟨hi, -, -⟩
  · left; rw [hRP, hPcard, hi]; norm_num
  · omega
  · right; rw [hRP, hPcard, hi]; norm_num

end CFSG.GH74.GLS.C3.Layer2.L4
