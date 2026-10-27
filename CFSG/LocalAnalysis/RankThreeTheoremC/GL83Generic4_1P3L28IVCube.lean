module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.ABGLocalTools Subgroup

theorem l28iv_three_pow_dvd {k r : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r) (h : 3 ^ k ∣ r ^ 3 - 1) :
    3 ^ k ∣ 3 * (r - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [show s + 1 - 1 = s by omega]
  have he : (s + 1) ^ 3 - 1 = s * (s ^ 2 + 3 * s + 3) := by
    have : (s + 1) ^ 3 = s * (s ^ 2 + 3 * s + 3) + 1 := by ring
    omega
  rw [he] at h
  have h3 : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  by_cases hs : 3 ∣ s
  · obtain ⟨t, rfl⟩ := hs
    have he2 : 3 * t * ((3 * t) ^ 2 + 3 * (3 * t) + 3) = 9 * t * (3 * (t ^ 2 + t) + 1) := by ring
    rw [he2] at h
    have hcop : Nat.Coprime (3 ^ k) (3 * (t ^ 2 + t) + 1) := by
      refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
      intro hd
      have : (3 : ℕ) ∣ 1 := (Nat.dvd_add_right (dvd_mul_right 3 _)).mp hd
      norm_num at this
    have h9 := hcop.dvd_of_dvd_mul_right h
    rw [show 3 * (3 * t) = 9 * t by ring]
    exact h9
  · exfalso
    have hdvd : (3 : ℕ) ∣ s * (s ^ 2 + 3 * s + 3) := h3.trans h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
    · exact hs h1
    · have h2 : (3 : ℕ) ∣ s ^ 2 := by
        have h4 : (3 : ℕ) ∣ 3 * s + 3 := ⟨s + 1, by ring⟩
        have h5 : s ^ 2 + 3 * s + 3 = s ^ 2 + (3 * s + 3) := by ring
        rw [h5] at h1
        exact (Nat.dvd_add_left h4).mp h1
      exact hs (Nat.prime_three.dvd_of_dvd_pow h2)

theorem l28iv_fix_cube {G : Type*} [Group G] {z₀ y : G} {k : ℕ} (hk : 1 ≤ k)
    (hz₀ : orderOf z₀ = 3 ^ k) (hy3 : y ^ 3 = 1) (hyz : y * z₀ * y⁻¹ ∈ zpowers z₀) :
    y * z₀ ^ 3 * y⁻¹ = z₀ ^ 3 := by
  have hfin : IsOfFinOrder z₀ := orderOf_pos_iff.mp (by rw [hz₀]; positivity)
  obtain ⟨r, -, hr⟩ : ∃ r : ℕ, r < orderOf z₀ ∧ z₀ ^ r = y * z₀ * y⁻¹ := by
    classical
    have h := hfin.mem_zpowers_iff_mem_range_orderOf.mp hyz
    rw [Finset.mem_image] at h
    obtain ⟨r, hr, hrz⟩ := h
    exact ⟨r, Finset.mem_range.mp hr, hrz⟩
  have hpow : ∀ n : ℕ, y * z₀ ^ n * y⁻¹ = z₀ ^ (r * n) := fun n => by
    rw [← conj_pow, ← hr, ← pow_mul]
  have hy2 : y ^ 2 * z₀ * (y ^ 2)⁻¹ = z₀ ^ (r * r) := by
    calc y ^ 2 * z₀ * (y ^ 2)⁻¹ = y * (y * z₀ * y⁻¹) * y⁻¹ := by rw [pow_two]; group
      _ = y * z₀ ^ r * y⁻¹ := by rw [← hr]
      _ = z₀ ^ (r * r) := hpow r
  have hr3 : z₀ ^ (r ^ 3) = z₀ ^ 1 := by
    have h : y ^ 3 * z₀ * (y ^ 3)⁻¹ = z₀ ^ (r * (r * r)) := by
      calc y ^ 3 * z₀ * (y ^ 3)⁻¹ = y * (y ^ 2 * z₀ * (y ^ 2)⁻¹) * y⁻¹ := by
            rw [pow_succ, pow_two]; group
        _ = y * z₀ ^ (r * r) * y⁻¹ := by rw [hy2]
        _ = z₀ ^ (r * (r * r)) := hpow (r * r)
    rw [hy3, one_mul, inv_one, mul_one] at h
    rw [pow_one, show r ^ 3 = r * (r * r) by ring]
    exact h.symm
  have hmod : r ^ 3 ≡ 1 [MOD 3 ^ k] := by
    rw [← hz₀]
    exact pow_eq_pow_iff_modEq.mp hr3
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      rw [h0] at hmod
      have : 3 ^ k ∣ 1 := (Nat.modEq_zero_iff_dvd.mp hmod.symm)
      have h3 : 3 ≤ 3 ^ k := by
        calc 3 = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · exact h0
  have hdvd : 3 ^ k ∣ r ^ 3 - 1 := by
    have h1 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ hr1
    exact (Nat.modEq_iff_dvd' h1).mp hmod.symm
  have hd := l28iv_three_pow_dvd hk hr1 hdvd
  rw [hpow 3]
  have h3r : r * 3 = 3 + 3 * (r - 1) := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [show s + 1 - 1 = s by omega]
    ring
  rw [h3r, pow_add]
  obtain ⟨c, hc⟩ := hd
  rw [hc, pow_mul, ← hz₀, pow_orderOf_eq_one, one_pow, mul_one]

variable {G : Type} [Group G]

theorem l28iv_cube_mem {P T Z : Subgroup G} {y : G} (hcomm : ∀ a ∈ T, ∀ c ∈ Z, a * c = c * a)
    (hy3 : y ^ 3 = 1) (hyN : y ∈ normalizer (T : Set G))
    (hcen : ∀ w ∈ P, ∀ c ∈ Z, w * c = c * w) (hZ3 : ∀ c ∈ Z, c ^ 3 = 1)
    (hP : P ≤ zpowers y ⊔ (T ⊔ Z)) (hyP : y ∈ P) (hTZP : T ⊔ Z ≤ P) :
    ∀ w ∈ P, w ^ 3 ∈ T := by
  intro w hw
  have hyZ : y ∈ normalizer (Z : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun c hc => ?_)
    exact (hcen y hyP c hc).symm
  have hyN' : zpowers y ≤ normalizer ((T ⊔ Z : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact Subgroup.inf_normalizer_le_normalizer_sup T Z ⟨hyN, hyZ⟩
  have hw' : w ∈ ((zpowers y ⊔ (T ⊔ Z) : Subgroup G) : Set G) := hP hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hyN'] at hw'
  obtain ⟨v, hv, s, hs, rfl⟩ := hw'
  obtain ⟨a, ha, c, hc, rfl⟩ := u3l42_decomp hcomm hs
  have hvN : v ∈ normalizer (T : Set G) := (zpowers_le.mpr hyN) hv
  have hv3 : v ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hvP : v ∈ P := (zpowers_le.mpr hyP) hv
  have haP : a ∈ P := hTZP (mem_sup_left ha)
  have hc3 := hZ3 c hc
  have hcva : (v * a) * c = c * (v * a) := hcen _ (P.mul_mem hvP haP) c hc
  have h1 : (v * (a * c)) ^ 3 = (v * a) ^ 3 * c ^ 3 := by
    rw [← mul_assoc, (Commute.mul_pow (show Commute (v * a) c from hcva) 3)]
  rw [h1, hc3, mul_one]
  have hva : v * a * v⁻¹ ∈ T := (mem_normalizer_iff.mp hvN a).mp ha
  have hvva : v * (v * a * v⁻¹) * v⁻¹ ∈ T := (mem_normalizer_iff.mp hvN _).mp hva
  have e : (v * a) ^ 3 = (v * a * v⁻¹) * (v * (v * a * v⁻¹) * v⁻¹) * (v ^ 3 * a * (v ^ 3)⁻¹) *
      v ^ 3 := by
    rw [pow_succ, pow_succ, pow_one, pow_succ, pow_succ, pow_one]
    group
  rw [e, hv3, one_mul, inv_one, mul_one, mul_one]
  exact T.mul_mem (T.mul_mem hva hvva) ha

theorem l28iv_exists_normalizer_conj [Finite G] {Q : Subgroup G} {x g : G}
    (hQsyl : IsSylowOf 3 Q (centralizer ({x} : Set G)))
    (hcen : ∀ a ∈ Q, a * (g * x * g⁻¹) = (g * x * g⁻¹) * a) :
    ∃ n ∈ normalizer (Q : Set G), n * x * n⁻¹ = g * x * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q' : Subgroup G := Q.map (MulAut.conj g⁻¹).toMonoidHom with hQ'
  have hQ'mem : ∀ w : G, w ∈ Q' ↔ g * w * g⁻¹ ∈ Q := by
    intro w
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have e : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
      rw [e]
      exact hq
    · intro hw
      refine ⟨g * w * g⁻¹, hw, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  have hQ'le : Q' ≤ centralizer ({x} : Set G) := by
    intro w hw
    rw [hQ'mem] at hw
    rw [mem_centralizer_singleton_iff]
    have h := hcen _ hw
    calc w * x = g⁻¹ * ((g * w * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * w * g⁻¹)) * g := by rw [h]
      _ = x * w := by group
  have hQ'syl : IsSylowOf 3 Q' (centralizer ({x} : Set G)) := by
    refine isSylowOf_of_card hQ'le ?_
    rw [hQ', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hQsyl.card_eq
  obtain ⟨k, hkC, hk⟩ := hQsyl.exists_mem_conj hQ'syl
  refine ⟨g * k, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro z
    have h1 := hk (k * z * k⁻¹)
    have e1 : k⁻¹ * (k * z * k⁻¹) * k = z := by group
    have e2 : g * (k * z * k⁻¹) * g⁻¹ = g * k * z * (g * k)⁻¹ := by group
    rw [e1, hQ'mem, e2] at h1
    exact h1.symm
  · have hkx : k * x * k⁻¹ = x := by rw [mem_centralizer_singleton_iff.mp hkC]; group
    calc g * k * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [hkx]

end CFSG.LocalAnalysis.RankThreeTheoremC
