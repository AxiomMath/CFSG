module

public import CFSG.LocalAnalysis.AGLEmbedding.AltSix
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixH

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB

namespace Six

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 6)} {ψB : B ≃* alternatingGroup (Fin 6)}

variable (ψB) in
@[expose] noncomputable def R : Subgroup G := ((rootV 6).map ψB.symm.toMonoidHom).map B.subtype

theorem R_le_B : R ψB ≤ B := map_subtype_le _

theorem card_R : Nat.card (R ψB) = 4 := by
  rw [R, card_map_of_injective B.subtype_injective, card_map_of_injective ψB.symm.injective,
    card_rootV (by norm_num)]

theorem exists_kOf_of_mem_R {r : G} (hr : r ∈ R ψB) :
    ∃ (hrB : r ∈ B) (i : Fin 4), ((ψB ⟨r, hrB⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) (kOf i) ∧ (r = 1 ↔ i = 0) := by
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := hr
  obtain ⟨k', hk', hkk⟩ := (mem_rootV_iff (by norm_num) k).mp hk
  obtain ⟨i, rfl⟩ := exists_kOf_of_mem_kleinFour hk'
  refine ⟨(ψB.symm k).2, i, ?_, ?_⟩
  · have : (⟨B.subtype (ψB.symm.toMonoidHom k), (ψB.symm k).2⟩ : B) = ψB.symm k := rfl
    rw [this, MulEquiv.apply_symm_apply, ← hkk]
  · constructor
    · intro h
      have h1 : ψB.symm k = 1 := Subtype.ext h
      have h2 : k = 1 := ψB.symm.injective (h1.trans (map_one _).symm)
      have h3 : viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) (kOf i) = 1 := by
        rw [hkk, h2]; rfl
      have h4 : kOf i = 1 := viaEmbeddingHom_injective _ (h3.trans (map_one _).symm)
      have key : ∀ j : Fin 4, kOf j = 1 → j = 0 := by decide
      exact key i h4
    · rintro rfl
      have hk1 : k = 1 := Subtype.ext (by rw [← hkk]; exact map_one _)
      show ((ψB.symm k : B) : G) = 1
      rw [hk1, map_one, Subgroup.coe_one]

theorem mul_self_of_mem_R {r : G} (hr : r ∈ R ψB) : r * r = 1 := by
  obtain ⟨hrB, i, hi, -⟩ := exists_kOf_of_mem_R hr
  have h : (⟨r, hrB⟩ : B) * ⟨r, hrB⟩ = 1 := by
    apply ψB.injective
    apply Subtype.ext
    have key : ∀ j : Fin 4, kOf j * kOf j = 1 := by decide
    rw [map_mul, Subgroup.coe_mul, hi, ← map_mul, map_one, Subgroup.coe_one, key i, map_one]
  exact congrArg Subtype.val h

theorem R_le_centralizer_A (hco : AltCoords 6 A B ψA ψB) : R ψB ≤ centralizer (A : Set G) :=
  hco.2.1.le

theorem w_pow_three : w ψA ^ 3 = 1 := by
  show ((ψA.symm e123 : A) : G) ^ 3 = 1
  rw [← Subgroup.coe_pow, ← map_pow, show e123 ^ 3 = 1 from Subtype.ext (by decide), map_one,
    Subgroup.coe_one]

theorem c1_pow_three : c1 ψA ^ 3 = 1 := by
  show ((ψA.symm e450 : A) : G) ^ 3 = 1
  rw [← Subgroup.coe_pow, ← map_pow, show e450 ^ 3 = 1 from Subtype.ext (by decide), map_one,
    Subgroup.coe_one]

theorem inOmega6_of_mem [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    {r : G} (hr : r ∈ R ψB) (hr1 : r ≠ 1) {h : G} (hH : h ∈ H ψA)
    (hhr : h ∈ centralizer ({r} : Set G)) (hodd : Odd (orderOf h)) : InOmega6 ψA B h := by
  have hC5A := hco.2.2.2.2.2.2.2.1
  have hrA := R_le_centralizer_A hco hr
  have hhN : h ∈ normalizer (A : Set G) := ht1A r hrA (mul_self_of_mem_R hr) hr1 hhr
  set α := actAut ψA ⟨h, hhN⟩ with hα
  have hαodd : Odd (orderOf α) := by
    refine Odd.of_dvd_nat hodd ?_
    have := orderOf_map_dvd (actAut ψA) (⟨h, hhN⟩ : normalizer (A : Set G))
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨a, ha⟩ := CFSG.AGLEmbedding.mem_range_conj_of_odd_orderOf α hαodd
  have hpw : h * w ψA * h⁻¹ = w ψA := by
    rw [(mem_centralizer_singleton_iff.mp hH), mul_inv_cancel_right]
  have hfix : α e123 = e123 := by
    have h1 := actAut_apply ψA ⟨h, hhN⟩ (ψA.symm e123)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [hα, h1]
    have h2 : (⟨h * (ψA.symm e123 : G) * h⁻¹,
        (mem_normalizer_iff.mp hhN _).mp (ψA.symm e123).2⟩ : A) = ψA.symm e123 :=
      Subtype.ext hpw
    rw [h2, MulEquiv.apply_symm_apply]
  have hac : (a : Perm (Fin 6)) * s123 = s123 * a := by
    have h1 : MulAut.conj a e123 = e123 := by rw [ha]; exact hfix
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conj_apply] at h2
    have h3 : (a : Perm (Fin 6)) * s123 * (a : Perm (Fin 6))⁻¹ = s123 := h2
    calc (a : Perm (Fin 6)) * s123 = (a : Perm (Fin 6)) * s123 * (a : Perm (Fin 6))⁻¹ * a := by
          group
      _ = s123 * a := by rw [h3]
  obtain ⟨i, j, -, -, hij⟩ := eq_of_commute_s123 (mem_alternatingGroup.mp a.2) hac
  have haij : a = e123 ^ i * e450 ^ j := Subtype.ext (by
    rw [hij, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    rfl)
  set g := w ψA ^ i * c1 ψA ^ j with hg
  have hgA : g ∈ A := mul_mem (pow_mem w_mem i) (pow_mem c1_mem j)
  have hgψ : ψA ⟨g, hgA⟩ = a := by
    have : (⟨g, hgA⟩ : A) = ψA.symm (e123 ^ i * e450 ^ j) := Subtype.ext (by
      rw [map_mul, map_pow, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
      rfl)
    rw [this, MulEquiv.apply_symm_apply, haij]
  have hαg : actAut ψA ⟨g, le_normalizer hgA⟩ = α := by
    rw [actAut_of_mem ψA hgA, hgψ, ha]
  have hh'A : h * g⁻¹ ∈ centralizer (A : Set G) := by
    have h1 : actAut ψA (⟨h, hhN⟩ * (⟨g, le_normalizer hgA⟩ : normalizer (A : Set G))⁻¹) = 1 := by
      rw [map_mul, map_inv, hαg, mul_inv_cancel]
    exact (actAut_eq_one_iff ψA _).mp h1
  have hhg : h * g = g * h := by
    have h1 := actAut_apply ψA ⟨h, hhN⟩ ⟨g, hgA⟩
    rw [← hα, hgψ, ← ha, MulAut.conj_apply, mul_inv_cancel_right, ← hgψ] at h1
    have h2 := congrArg Subtype.val (ψA.injective h1)
    have h3 : g = h * g * h⁻¹ := h2
    calc h * g = h * g * h⁻¹ * h := by group
      _ = g * h := by rw [← h3]
  set h' := h * g⁻¹ with hh'
  have hgr : g * r = r * g := (mem_centralizer_iff.mp hrA) g hgA
  have hhr' : h * r = r * h := mem_centralizer_singleton_iff.mp hhr
  have hh'r : h' * r = r * h' := by
    have hg'r : g⁻¹ * r = r * g⁻¹ := (show Commute g r from hgr).inv_left.eq
    calc h' * r = h * (g⁻¹ * r) := by rw [hh']; group
      _ = h * r * g⁻¹ := by rw [hg'r]; group
      _ = r * h' := by rw [hhr', hh']; group
  have hg3 : g ^ 3 = 1 := by
    rw [hg, ((w_comm_c1 (ψA := ψA)).pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i,
      mul_comm j, pow_mul, pow_mul, w_pow_three, c1_pow_three, one_pow, one_pow, one_mul]
  set m := orderOf h * 3 with hm
  have hmodd : Odd m := Nat.odd_mul.mpr ⟨hodd, by decide⟩
  have hh'm : h' ^ m = 1 := by
    rw [hh', (show Commute h g⁻¹ from (show Commute h g from hhg).inv_right).mul_pow, hm,
      pow_mul, pow_orderOf_eq_one, one_pow, one_mul, mul_comm, pow_mul, inv_pow, hg3, inv_one,
      one_pow]
  obtain ⟨hh'B, π, hπfix, hπb⟩ := hC5A h' hh'A
  have hact : actAut ψB ⟨h', hh'B⟩ = conjPerm 6 π := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    obtain ⟨b, rfl⟩ := ψB.surjective x
    rw [actAut_apply, conjPerm_apply]
    exact (hπb b).2
  have hπm : π ^ m = 1 := by
    apply conjPerm_injective (n := 6) (by norm_num)
    rw [map_pow, ← hact, ← map_pow, map_one]
    have : (⟨h', hh'B⟩ : normalizer (B : Set G)) ^ m = 1 := Subtype.ext (by simp [hh'm])
    rw [this, map_one]
  obtain ⟨hrB, k, hk, hk0⟩ := exists_kOf_of_mem_R hr
  have hk0' : k ≠ 0 := fun h0 => hr1 (hk0.mpr h0)
  obtain ⟨ha, hae⟩ := hπb ⟨r, hrB⟩
  have h2 : (⟨h' * r * h'⁻¹, ha⟩ : B) = ⟨r, hrB⟩ :=
    Subtype.ext (by show h' * r * h'⁻¹ = r; rw [hh'r, mul_inv_cancel_right])
  rw [h2, hk] at hae
  obtain ⟨π', rfl⟩ := exists_perm_four_of_fix (by norm_num : 4 ≤ 6) hπfix
  have hcomm' : π' * kOf k = kOf k * π' := by
    apply viaEmbeddingHom_injective (fourEmb (by norm_num : 4 ≤ 6))
    rw [map_mul (viaEmbeddingHom _) π', map_mul (viaEmbeddingHom _) _ π']
    calc _ = viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) π' *
          viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) (kOf k) *
            (viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) π')⁻¹ *
              viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) π' := by group
      _ = _ := by rw [← hae]
  have h3 : π' ^ 3 = 1 := by
    refine pow_three_of_odd hmodd (viaEmbeddingHom_injective (fourEmb (by norm_num : 4 ≤ 6)) ?_)
    rw [map_pow, hπm, map_one]
  have hπ'1 := eq_one_of_commute_kOf π' k hk0' hcomm' h3
  have hh'B' : h' ∈ centralizer (B : Set G) := by
    rw [mem_centralizer_iff]
    intro b hb
    obtain ⟨hb', hbe⟩ := hπb ⟨b, hb⟩
    rw [hπ'1, map_one, one_mul, inv_one, mul_one] at hbe
    have h4 := congrArg Subtype.val (ψB.injective (Subtype.ext hbe))
    have h5 : h' * b * h'⁻¹ = b := h4
    calc b * h' = h' * b * h'⁻¹ * h' := by rw [h5]
      _ = h' * b := by group
  refine ⟨h', mem_inf.mpr ⟨hh'A, hh'B'⟩, i, j, ?_⟩
  rw [zpow_natCast, zpow_natCast, mul_assoc, ← hg, hh', inv_mul_cancel_right]

theorem core_le [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    {g : G} (hg : g ∈ (pPrimeCore 2 (H ψA)).map (H ψA).subtype) : InOmega6 ψA B g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := (pPrimeCore 2 (H ψA)).map (H ψA).subtype with hK
  have hKcard : Nat.card K = Nat.card (pPrimeCore 2 (H ψA)) :=
    card_map_of_injective (H ψA).subtype_injective
  have hKodd : ¬ 2 ∣ Nat.card K := by
    rw [hKcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have hKH : K ≤ H ψA := map_subtype_le _
  have hHN : H ψA ≤ normalizer (K : Set G) := by
    intro x hx
    have := pPrimeCore_normal (p := 2) (G := H ψA)
    apply le_normalizer_map (H ψA).subtype
    exact ⟨⟨x, hx⟩, le_normalizer_of_normal (K := ⊤) (mem_top _), rfl⟩
  have hRH : R ψB ≤ H ψA := R_le_B.trans (B_le_H hco)
  have hgen := RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two (R ψB) K (fun r => Subtype.ext (by simpa [sq] using mul_self_of_mem_R r.2))
    (by rw [card_R]; norm_num) hKodd (hRH.trans hHN)
  rw [hgen] at hg
  refine Subgroup.iSup_induction (C := InOmega6 ψA B) _ hg (fun r y hy => ?_) inOmega6_one
    (fun y z hy hz => inOmega6_mul hN hy hz)
  refine Subgroup.iSup_induction (C := InOmega6 ψA B) _ hy (fun hr1 z hz => ?_) inOmega6_one
    (fun y z hy hz => inOmega6_mul hN hy hz)
  obtain ⟨hzK, hzr⟩ := mem_inf.mp hz
  have hodd : Odd (orderOf z) :=
    Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hKodd))
      (Subgroup.orderOf_dvd_natCard _ hzK)
  exact inOmega6_of_mem hco ht1A r.2 (fun h => hr1 (Subtype.ext h)) (hKH hzK) hzr hodd

theorem mul_formula
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    {k₁ k₂ : G} (hk₁ : k₁ ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G))
    (hk₂ : k₂ ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G)) (i j a b : ℤ) :
    ∃ k ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G),
      k₁ * w ψA ^ i * c1 ψA ^ j * (k₂ * w ψA ^ a * c1 ψA ^ b) =
        k * w ψA ^ (i + a) * c1 ψA ^ (j + b) := by
  have hwN := hN (mem_sup_left (le_normalizer (w_mem (ψA := ψA))))
  have hcN := hN (mem_sup_left (le_normalizer (c1_mem (ψA := ψA))))
  set c := w ψA ^ i * c1 ψA ^ j with hc
  have hcN' : c ∈ normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) :
      Subgroup G) : Set G) := mul_mem (zpow_mem hwN i) (zpow_mem hcN j)
  refine ⟨k₁ * (c * k₂ * c⁻¹), mul_mem hk₁ ((mem_normalizer_iff.mp hcN' k₂).mp hk₂), ?_⟩
  have hvw : c1 ψA ^ j * w ψA ^ a = w ψA ^ a * c1 ψA ^ j :=
    ((w_comm_c1 (ψA := ψA)).zpow_zpow a j).eq.symm
  rw [zpow_add, zpow_add]
  calc k₁ * w ψA ^ i * c1 ψA ^ j * (k₂ * w ψA ^ a * c1 ψA ^ b)
      = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * (c1 ψA ^ j * w ψA ^ a) * c1 ψA ^ b) := by
        rw [hc]; group
    _ = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * (w ψA ^ a * c1 ψA ^ j) * c1 ψA ^ b) := by rw [hvw]
    _ = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * w ψA ^ a) * (c1 ψA ^ j * c1 ψA ^ b) := by group

theorem pow_formula
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    {k : G} (hk : k ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G)) (a b : ℤ) (n : ℕ) :
    ∃ k' ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G),
      (k * w ψA ^ a * c1 ψA ^ b) ^ n = k' * w ψA ^ (n * a) * c1 ψA ^ (n * b) := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', hk'e⟩ := ih
    obtain ⟨k'', hk'', e⟩ := mul_formula hN hk' hk (n * a) (n * b) a b
    refine ⟨k'', hk'', ?_⟩
    rw [pow_succ, hk'e, e]
    congr 3 <;> push_cast <;> ring

theorem three_dvd_of_c1_zpow {k : G} (hk : k ∈ centralizer (A : Set G)) {p q : ℤ}
    (h : c1 ψA ^ p = k * w ψA ^ q) : (3 : ℤ) ∣ p := by
  have hkA : k ∈ A := by
    have : k = c1 ψA ^ p * (w ψA ^ q)⁻¹ := by rw [h]; group
    rw [this]
    exact mul_mem (zpow_mem c1_mem p) (inv_mem (zpow_mem w_mem q))
  have hk1 := eq_one_of_mem_centralizer_six ψA hkA hk
  rw [hk1, one_mul] at h
  have h2 : ψA.symm (e450 ^ p) = ψA.symm (e123 ^ q) := by
    apply Subtype.ext
    rw [map_zpow, map_zpow, Subgroup.coe_zpow, Subgroup.coe_zpow]
    exact h
  have h3 := ψA.symm.injective h2
  have he450 : e450 ^ 3 = 1 := Subtype.ext (by decide)
  have he123 : e123 ^ 3 = 1 := Subtype.ext (by decide)
  rw [zpow_eq_zpow_emod' p he450, zpow_eq_zpow_emod' q he123] at h3
  have hp : p % (3 : ℕ) = 0 ∨ p % (3 : ℕ) = 1 ∨ p % (3 : ℕ) = 2 := by omega
  have hq : q % (3 : ℕ) = 0 ∨ q % (3 : ℕ) = 1 ∨ q % (3 : ℕ) = 2 := by omega
  rcases hp with hp | hp | hp
  · omega
  all_goals
    exfalso
    rcases hq with hq | hq | hq <;> rw [hp, hq] at h3 <;> revert h3 <;> decide

theorem c1_not_mem_core [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G)) :
    (⟨c1 ψA, c1_mem_H⟩ : H ψA) ∉ pPrimeCore 2 (H ψA) := by
  intro hc
  have hsH : s ψB ∈ H ψA := B_le_H hco s_mem
  have hsc : (⟨s ψB, hsH⟩ : H ψA) * ⟨c1 ψA, c1_mem_H⟩ * (⟨s ψB, hsH⟩ : H ψA)⁻¹ ∈
      pPrimeCore 2 (H ψA) := (pPrimeCore_normal (p := 2) (G := H ψA)).conj_mem _ hc _
  obtain ⟨k, hk, a, e, hke⟩ := core_le hco hN ht1A ⟨_, hsc, rfl⟩
  have hke' : s ψB * c1 ψA * (s ψB)⁻¹ = k * w ψA ^ a * c1 ψA ^ e := hke
  set e' : ℕ := (e % 3).toNat with he'
  have he'3 : e' < 3 := by omega
  have hce : c1 ψA ^ e = c1 ψA ^ (e' : ℤ) := by
    rw [zpow_eq_zpow_emod' e c1_pow_three, he', Int.toNat_of_nonneg (by omega)]
    rfl
  rw [hce] at hke'
  set φ := MulAut.conj (s ψB) with hφ
  have hφapp : ∀ x, φ x = s ψB * x * (s ψB)⁻¹ := fun x => rfl
  have hsw : φ (w ψA) = w ψA := by
    rw [hφapp, (mem_centralizer_iff.mp (w_mem_centralizer_B hco)) _ s_mem, mul_inv_cancel_right]
  have hsN := hN (mem_sup_right (le_normalizer (s_mem (ψB := ψB))))
  have hsk : φ k ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G) :=
    (mem_normalizer_iff.mp hsN k).mp hk
  have hy : y0 ψB * c1 ψA * (y0 ψB)⁻¹ = φ (φ (c1 ψA)) := by
    rw [hφapp, hφapp, ← s_sq]
    group
  rw [hφapp (c1 ψA), hke', map_mul, map_mul, map_zpow, map_zpow, hsw, hφapp (c1 ψA), hke'] at hy
  obtain ⟨k', hk', hk'e⟩ := pow_formula hN hk a (e' : ℤ) e'
  rw [zpow_natCast, hk'e] at hy
  obtain ⟨k'', hk'', hk''e⟩ := mul_formula hN hsk hk' a 0 (e' * a) (e' * (e' : ℤ))
  rw [show φ k * w ψA ^ a * (k' * w ψA ^ (e' * a) * c1 ψA ^ (e' * (e' : ℤ))) =
      φ k * w ψA ^ a * c1 ψA ^ (0 : ℤ) * (k' * w ψA ^ (e' * a) * c1 ψA ^ (e' * (e' : ℤ))) by
        rw [zpow_zero, mul_one], hk''e, y0_conj_c1 hco] at hy
  have h2 : c1 ψA ^ (-1 - e' * (e' : ℤ)) = k'' * w ψA ^ (a + e' * a) := by
    have h3 : c1 ψA ^ (-1 - e' * (e' : ℤ)) =
        (c1 ψA)⁻¹ * (c1 ψA ^ (0 + e' * (e' : ℤ)))⁻¹ := by
      rw [← zpow_neg_one, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [h3, hy]
    group
  have h3 := three_dvd_of_c1_zpow (mem_inf.mp hk'').1 h2
  interval_cases e' <;> omega

end Six

end CFSG.ComponentClassification.RankTwoAlt
