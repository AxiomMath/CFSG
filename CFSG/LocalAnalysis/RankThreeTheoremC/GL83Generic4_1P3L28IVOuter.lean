module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ThreeProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Quasithin
open CFSG.Quasithin.F6.L28Res (G8 frob frobF)

@[expose] def l28ivC : G8 :=
  ⟨(GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 6), by decide⟩

theorem l28ivC_pow_nine : l28ivC ^ 9 = 1 := by decide +kernel

theorem l28ivC_pow_three_ne : l28ivC ^ 3 ≠ 1 := by decide +kernel

theorem l28ivC_frob : frobF l28ivC = l28ivC ^ 7 := by decide +kernel

private theorem l28iv_factorization_1512 : (1512 : ℕ).factorization 3 = 3 := by
  have h3 : 3 ≤ (1512 : ℕ).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).1 (by norm_num)
  have h4 : ¬ 4 ≤ (1512 : ℕ).factorization 3 := fun h =>
    absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).2 h) (by norm_num)
  omega

theorem l28iv_mem_normalizer_zpowers {A : Type*} [Group A] [Finite A] {a f : A} {k : ℤ}
    (h : f * a * f⁻¹ = a ^ k) : f ∈ normalizer ((zpowers a : Subgroup A) : Set A) := by
  have hmap : ∀ z ∈ zpowers a, f * z * f⁻¹ ∈ zpowers a := by
    intro z hz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    rw [← conj_zpow, h, ← zpow_mul]
    exact zpow_mem (mem_zpowers a) _
  set m : zpowers a → zpowers a := fun z => ⟨f * z * f⁻¹, hmap z z.2⟩ with hm
  have hinj : Function.Injective m := by
    intro z₁ z₂ hz
    have h1 : f * (z₁ : A) * f⁻¹ = f * z₂ * f⁻¹ := congrArg Subtype.val hz
    exact Subtype.ext (by simpa using h1)
  have hsurj : Function.Surjective m := Finite.injective_iff_surjective.mp hinj
  rw [mem_normalizer_iff]
  intro z
  refine ⟨fun hz => hmap z hz, fun hz => ?_⟩
  obtain ⟨w, hw⟩ := hsurj ⟨f * z * f⁻¹, hz⟩
  have h1 : f * (w : A) * f⁻¹ = f * z * f⁻¹ := congrArg Subtype.val hw
  have h2 : (w : A) = z := by simpa using h1
  rw [← h2]
  exact w.2

theorem l28iv_mulAut_conj_conj {K : Type*} [Group K] (φ : MulAut K) (c : K) :
    φ * MulAut.conj c * φ⁻¹ = MulAut.conj (φ c) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem l28m_outer_moves_sylow' {K : Type} [Group K] [Finite K] (hK : IsRankThreeL28 K)
    (T : Sylow 3 K) {α : MulAut K} {m : ℕ} (hα3 : α ^ (3 ^ m) = 1)
    (hout : ∀ k : K, MulAut.conj k ≠ α) : ∃ t ∈ (T : Subgroup K), α t ≠ t := by
  by_contra hfix
  push Not at hfix
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcard : Nat.card (MulAut K) = 1512 := l28m_card_mulAut hK
  have : Finite (MulAut K) := Nat.finite_of_card_ne_zero (by rw [hAcard]; norm_num)
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    refine Subgroup.mem_bot.mpr (l28m_eq_one_of_central hK fun y => ?_)
    have h := congrArg (fun β : MulAut K => β y) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h]
  set IT : Subgroup (MulAut K) := (T : Subgroup K).map MulAut.conj with hIT
  have hTcard : Nat.card (T : Subgroup K) = 3 ^ 2 := l28m_card_sylow hK T
  have hITcard : Nat.card IT = 3 ^ 2 := by
    rw [hIT, Subgroup.card_map_of_injective hinj, hTcard]
  have hTab : ∀ a ∈ (T : Subgroup K), ∀ b ∈ (T : Subgroup K), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val
      ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hTcard).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hITab : ∀ e₁ ∈ IT, ∀ e₂ ∈ IT, e₁ * e₂ = e₂ * e₁ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hTab a ha b hb]
  have hαc : ∀ e ∈ IT, e * α = α * e := by
    rintro _ ⟨t, ht, rfl⟩
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix t ht]
  have hαIT : α ∉ IT := by
    rintro ⟨k, -, hk⟩
    exact hout k hk
  have h27 : Nat.card ↥(IT ⊔ zpowers α) = 27 := by
    have hITp : IsPGroup 3 IT := IsPGroup.of_card hITcard
    have hαp : IsPGroup 3 (zpowers α) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hα3)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hN : zpowers α ≤ normalizer (IT : Set (MulAut K)) := by
      rw [zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun e he => hαc e he)
    have hSp := IsPGroup.to_sup_of_normal_left' hITp hαp hN
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    have hle : IT < IT ⊔ zpowers α := lt_of_le_of_ne le_sup_left fun h =>
      hαIT (h ▸ mem_sup_right (mem_zpowers α))
    have h9 : 3 ^ 2 < 3 ^ k := by
      rw [← hITcard, ← hk]
      exact Subgroup.card_lt_of_lt hle
    have hk3 : 3 ≤ k := by
      by_contra h
      push Not at h
      have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hdvd : 3 ^ k ∣ 1512 := by
      rw [← hk, ← hAcard]
      exact Subgroup.card_subgroup_dvd_card _
    have hk3' : k ≤ 3 := by
      by_contra h
      push Not at h
      have : 3 ^ 4 ∣ 1512 := (Nat.pow_dvd_pow 3 h).trans hdvd
      norm_num at this
    rw [hk, show k = 3 by omega]
    norm_num
  have hS₁card : Nat.card ↥(IT ⊔ zpowers α) = 3 ^ (Nat.card (MulAut K)).factorization 3 := by
    rw [h27, hAcard, l28iv_factorization_1512]
    norm_num
  have hcz : ∀ e ∈ IT, ∀ c ∈ zpowers α, e * c = c * e := by
    intro e he c hc
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute e α from hαc e he) n).eq
  have hS₁ab : ∀ a ∈ IT ⊔ zpowers α, ∀ b ∈ IT ⊔ zpowers α, a * b = b * a := by
    intro a ha b hb
    obtain ⟨e₁, he₁, c₁, hc₁, rfl⟩ := u3l42_decomp hcz ha
    obtain ⟨e₂, he₂, c₂, hc₂, rfl⟩ := u3l42_decomp hcz hb
    have h1 := hcz e₂ he₂ c₁ hc₁
    have h2 := hcz e₁ he₁ c₂ hc₂
    have h3 := hITab e₁ he₁ e₂ he₂
    have h4 : c₁ * c₂ = c₂ * c₁ := by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hc₁
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc₂
      exact (Commute.zpow_zpow_self α m n).eq
    calc e₁ * c₁ * (e₂ * c₂) = e₁ * (c₁ * e₂) * c₂ := by group
      _ = e₁ * (e₂ * c₁) * c₂ := by rw [h1]
      _ = (e₁ * e₂) * (c₁ * c₂) := by group
      _ = (e₂ * e₁) * (c₂ * c₁) := by rw [h3, h4]
      _ = e₂ * (e₁ * c₂) * c₁ := by group
      _ = e₂ * (c₂ * e₁) * c₁ := by rw [h2]
      _ = e₂ * c₂ * (e₁ * c₁) := by group
  obtain ⟨e⟩ := l28m_equiv hK
  set c : K := e.symm l28ivC with hc
  set φ : MulAut K := (e.trans frob).trans e.symm with hφ
  have hφapp : ∀ y : K, φ y = e.symm (frobF (e y)) := fun y => rfl
  have hφc : φ c = c ^ 7 := by
    rw [hφapp, hc, MulEquiv.apply_symm_apply, l28ivC_frob, map_pow]
  have hc9 : c ^ 9 = 1 := by rw [hc, ← map_pow, l28ivC_pow_nine, map_one]
  have hc3 : c ^ 3 ≠ 1 := by
    intro h
    apply l28ivC_pow_three_ne
    have := congrArg e h
    rwa [map_pow, hc, MulEquiv.apply_symm_apply, map_one] at this
  have hφ3 : φ ^ 3 = 1 := by
    ext y
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hφapp,
      MulEquiv.apply_symm_apply, CFSG.Quasithin.F6.L28Res.frobF_frobF_frobF,
      MulEquiv.symm_apply_apply]
  have hconjc : φ * MulAut.conj c * φ⁻¹ = MulAut.conj c ^ (7 : ℤ) := by
    rw [l28iv_mulAut_conj_conj, hφc, map_pow]
    exact (zpow_natCast _ 7).symm
  have hN := l28iv_mem_normalizer_zpowers hconjc
  have hc9' : MulAut.conj c ^ 9 = 1 := by rw [← map_pow, hc9, map_one]
  have hP1 : IsPGroup 3 (zpowers (MulAut.conj c)) :=
    IsPGroup.of_card (n := 2) (by
      rw [Nat.card_zpowers]
      have hd : orderOf (MulAut.conj c) ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hc9')
      rcases (Nat.dvd_prime_pow Nat.prime_three).mp hd with ⟨i, hi, hci⟩
      interval_cases i
      · exfalso
        rw [pow_zero, orderOf_eq_one_iff] at hci
        apply hc3
        have : c = 1 := hinj (by rw [hci, map_one])
        rw [this, one_pow]
      · exfalso
        rw [pow_one] at hci
        apply hc3
        apply hinj
        rw [map_pow, map_one, ← hci, pow_orderOf_eq_one]
      · exact hci)
  have hc7 : c ^ 7 ≠ c := by
    intro h2
    have h6 : c ^ 6 = 1 := by
      have : c ^ 7 = c ^ 6 * c := pow_succ c 6
      rw [this] at h2
      simpa using h2
    apply hc3
    have h3 := pow_gcd_eq_one.mpr ⟨h6, hc9⟩
    have hg : Nat.gcd 6 9 = 3 := by norm_num
    rwa [hg] at h3
  have hP2 : IsPGroup 3 (zpowers φ) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      refine orderOf_eq_prime hφ3 fun h1 => hc7 ?_
      rw [← hφc, h1, MulAut.one_apply])
  have hP := IsPGroup.to_sup_of_normal_left' hP1 hP2 (zpowers_le.mpr hN)
  obtain ⟨S₃, hS₃⟩ := hP.exists_le_sylow
  set S₁ : Sylow 3 (MulAut K) := Sylow.ofCard (IT ⊔ zpowers α) hS₁card with hS₁
  have hS₃ab : ∀ a ∈ (S₃ : Subgroup (MulAut K)), ∀ b ∈ (S₃ : Subgroup (MulAut K)),
      a * b = b * a := by
    intro a ha b hb
    set f := Sylow.equiv S₃ S₁ with hf
    have h1 : f ⟨a, ha⟩ * f ⟨b, hb⟩ = f ⟨b, hb⟩ * f ⟨a, ha⟩ :=
      Subtype.ext (hS₁ab _ (f ⟨a, ha⟩).2 _ (f ⟨b, hb⟩).2)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (f.injective h1)
  have hcomm := hS₃ab _ (hS₃ (mem_sup_left (mem_zpowers _))) _
    (hS₃ (mem_sup_right (mem_zpowers φ)))
  have h1 : MulAut.conj (φ c) = MulAut.conj c := by
    rw [← l28iv_mulAut_conj_conj, ← hcomm, mul_inv_cancel_right]
  exact hc7 (by rw [← hφc]; exact hinj h1)

private theorem l28iv_factorization_504 : (504 : ℕ).factorization 3 = 2 := by
  have h2 : 2 ≤ (504 : ℕ).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).1 (by norm_num)
  have h3 : ¬ 3 ≤ (504 : ℕ).factorization 3 := fun h =>
    absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).2 h) (by norm_num)
  omega

theorem l28m_sylow_isCyclic {K : Type} [Group K] [Finite K] (hK : IsRankThreeL28 K)
    (S : Sylow 3 K) : IsCyclic (S : Subgroup K) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := l28m_exists_order_nine hK
  have hcard : Nat.card (zpowers c) = 3 ^ (Nat.card K).factorization 3 := by
    rw [Nat.card_zpowers, hc, l28m_card hK, l28iv_factorization_504]
    norm_num
  set S₀ : Sylow 3 K := Sylow.ofCard (zpowers c) hcard with hS₀
  have hcyc : IsCyclic (S₀ : Subgroup K) := by
    rw [hS₀, Sylow.coe_ofCard]
    infer_instance
  exact isCyclic_of_surjective (Sylow.equiv S₀ S).toMonoidHom (Sylow.equiv S₀ S).surjective

end CFSG.LocalAnalysis.RankThreeTheoremC
