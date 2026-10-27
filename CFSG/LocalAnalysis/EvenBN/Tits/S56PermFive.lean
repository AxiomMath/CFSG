module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

set_option maxRecDepth 10000 in
theorem perm_five_pow_four_eq_one_of_commute :
    ∀ c g : Equiv.Perm (Fin 5), c ^ 5 = 1 → c ≠ 1 → g * c = c * g → g ^ 4 = 1 → g = 1 := by
  decide

theorem exists_orderOf_five_normal {P : Type*} [Group P] [Finite P]
    (hP : Nat.card P = 20 ∨ Nat.card P = 40) :
    ∃ x₀ : P, orderOf x₀ = 5 ∧ ∀ g : P, g * x₀ * g⁻¹ ∈ Subgroup.zpowers x₀ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite (Sylow 5 P) :=
    Finite.of_injective (fun Q : Sylow 5 P => (Q : Set P)) SetLike.coe_injective
  have h5 : 5 ∣ Nat.card P := by
    rcases hP with h | h <;> rw [h] <;> norm_num
  have hcard : ∀ Q : Sylow 5 P, Nat.card (Q : Subgroup P) = 5 := by
    intro Q
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 Q.isPGroup'
    have h1 : 5 ∣ Nat.card (Q : Subgroup P) := Q.dvd_card_of_dvd_card h5
    have h2 : Nat.card (Q : Subgroup P) ∣ Nat.card P := Subgroup.card_subgroup_dvd_card _
    rw [ha] at h1 h2 ⊢
    have ha0 : a ≠ 0 := by
      rintro rfl
      norm_num at h1
    have ha1 : a < 2 := by
      by_contra hcon
      have h25 : 5 ^ 2 ∣ Nat.card P := (pow_dvd_pow 5 (not_lt.1 hcon)).trans h2
      rcases hP with h | h <;> rw [h] at h25 <;> norm_num at h25
    obtain rfl : a = 1 := by omega
    norm_num
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow 5 P))
  have hS5 : Nat.card (S : Subgroup P) = 5 := hcard S
  have hidx : (S : Subgroup P).index * 5 = Nat.card P := by
    have h := Subgroup.card_mul_index (H := (S : Subgroup P))
    rw [hS5] at h
    omega
  have hdvdidx : Nat.card (Sylow 5 P) ∣ (S : Subgroup P).index := Sylow.card_dvd_index S
  have hmod : Nat.card (Sylow 5 P) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 P
  have hn5 : Nat.card (Sylow 5 P) = 1 := by
    have hm8 : Nat.card (Sylow 5 P) ∣ 8 := by
      rcases hP with h | h
      · have hi : (S : Subgroup P).index = 4 := by omega
        rw [hi] at hdvdidx
        exact hdvdidx.trans (by norm_num)
      · have hi : (S : Subgroup P).index = 8 := by omega
        rw [hi] at hdvdidx
        exact hdvdidx
    have hpos : 0 < Nat.card (Sylow 5 P) := Nat.card_pos
    have hle8 : Nat.card (Sylow 5 P) ≤ 8 := Nat.le_of_dvd (by norm_num) hm8
    unfold Nat.ModEq at hmod
    generalize Nat.card (Sylow 5 P) = m at hm8 hpos hle8 hmod ⊢
    interval_cases m <;> omega
  haveI : Subsingleton (Sylow 5 P) := (Nat.card_eq_one_iff_unique.1 hn5).1
  have hSn : (S : Subgroup P).Normal := Sylow.normal_of_subsingleton S
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S : Subgroup P)) 5 (by simp [hS5])
  have hx5 : orderOf (x : P) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hzeq : Subgroup.zpowers (x : P) = (S : Subgroup P) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact x.2
    · simp [Nat.card_zpowers, hx5, hS5]
  refine ⟨(x : P), hx5, fun g => ?_⟩
  rw [hzeq]
  exact hSn.conj_mem _ x.2 g

theorem card_le_twenty_of_embeds_perm_five {P : Type*} [Group P] [Finite P]
    (ι : P →* Equiv.Perm (Fin 5)) (hι : Function.Injective ι) (h3 : ¬ 3 ∣ Nat.card P) :
    Nat.card P ≤ 20 ∧ (Nat.card P = 20 → CFSG.pCore 2 P = ⊥) := by
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hdvd120 : Nat.card P ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card ((⊤ : Subgroup P).map ι)
    rwa [Subgroup.card_map_of_injective hι, Subgroup.card_top, h120] at h
  have hcop : Nat.Coprime (Nat.card P) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  have hdvd40 : Nat.card P ∣ 40 :=
    hcop.dvd_of_dvd_mul_right (show Nat.card P ∣ 40 * 3 from hdvd120)
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hle40 : Nat.card P ≤ 40 := Nat.le_of_dvd (by norm_num) hdvd40
  have hne40 : Nat.card P ≠ 40 := by
    intro hn
    obtain ⟨x₀, hx₀, hconj⟩ := exists_orderOf_five_normal (Or.inr hn)
    have hx₀1 : x₀ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx₀
      norm_num at hx₀
    have h1notin : (1 : P) ∉ conjugatesOf x₀ := by
      intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact hx₀1 (by simpa using hc)
    have hsub : insert (1 : P) (conjugatesOf x₀) ⊆ (Subgroup.zpowers x₀ : Set P) := by
      rintro y (rfl | hy)
      · exact Subgroup.one_mem _
      · obtain ⟨c, rfl⟩ := isConj_iff.1 hy
        exact hconj c
    have e1 := Set.ncard_insert_of_notMem h1notin
    have e2 := Set.ncard_le_ncard hsub
    have e3 : (Subgroup.zpowers x₀ : Set P).ncard = 5 := by
      rw [← Nat.card_coe_set_eq]
      exact (Nat.card_zpowers x₀).trans hx₀
    have hcount : (conjugatesOf x₀).ncard ≤ 4 := by omega
    have hindex : (Subgroup.centralizer {x₀}).index ≤ 4 := by
      rw [Subgroup.index_centralizer_eq_ncard]
      exact hcount
    have hcm := Subgroup.card_mul_index (H := Subgroup.centralizer {x₀})
    rw [hn] at hcm
    have h2dvd : 2 ∣ Nat.card (Subgroup.centralizer {x₀}) := by
      generalize (Subgroup.centralizer {x₀}).index = i at hcm hindex
      generalize Nat.card (Subgroup.centralizer {x₀}) = c at hcm ⊢
      interval_cases i <;> omega
    obtain ⟨y, hy⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer {x₀})) 2 h2dvd
    have hyo : orderOf (y : P) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hy
    have hyx : (y : P) * x₀ = x₀ * (y : P) := Subgroup.mem_centralizer_singleton_iff.1 y.2
    have hy2 : (y : P) ^ 2 = 1 := by
      rw [← hyo]
      exact pow_orderOf_eq_one _
    have hy1 : (y : P) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hyo
      norm_num at hyo
    have hy4 : (y : P) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hy2, one_pow]
    have hx₀5 : x₀ ^ 5 = 1 := by
      rw [← hx₀]
      exact pow_orderOf_eq_one x₀
    have hc5 : ι x₀ ^ 5 = 1 := by rw [← map_pow, hx₀5, map_one]
    have hc1 : ι x₀ ≠ 1 := fun h => hx₀1 (hι (by rw [h, map_one]))
    have hcomm : ι (y : P) * ι x₀ = ι x₀ * ι (y : P) := by
      rw [← map_mul, ← map_mul, hyx]
    have hy4' : ι (y : P) ^ 4 = 1 := by rw [← map_pow, hy4, map_one]
    have hyι : ι (y : P) = 1 :=
      perm_five_pow_four_eq_one_of_commute (ι x₀) (ι (y : P)) hc5 hc1 hcomm hy4'
    exact hy1 (hι (by rw [hyι, map_one]))
  have hle20 : Nat.card P ≤ 20 := by
    generalize Nat.card P = m at hpos hle40 hdvd40 hne40 ⊢
    interval_cases m <;> omega
  refine ⟨hle20, fun h20 => ?_⟩
  obtain ⟨x₀, hx₀, hconj⟩ := exists_orderOf_five_normal (Or.inl h20)
  have hx₀1 : x₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx₀
    norm_num at hx₀
  have hx₀5 : x₀ ^ 5 = 1 := by
    rw [← hx₀]
    exact pow_orderOf_eq_one x₀
  have hc5 : ι x₀ ^ 5 = 1 := by rw [← map_pow, hx₀5, map_one]
  have hc1 : ι x₀ ≠ 1 := fun h => hx₀1 (hι (by rw [h, map_one]))
  have hcent : ∀ g ∈ CFSG.pCore 2 P, g * x₀ = x₀ * g := by
    intro g hg
    have hk_zp : g * x₀ * g⁻¹ * x₀⁻¹ ∈ Subgroup.zpowers x₀ :=
      mul_mem (hconj g) (inv_mem (Subgroup.mem_zpowers x₀))
    have hk_R : g * x₀ * g⁻¹ * x₀⁻¹ ∈ CFSG.pCore 2 P := by
      have h1 : x₀ * g⁻¹ * x₀⁻¹ ∈ CFSG.pCore 2 P :=
        (CFSG.pCore_normal (p := 2) (G := P)).conj_mem _ (inv_mem hg) x₀
      have e : g * x₀ * g⁻¹ * x₀⁻¹ = g * (x₀ * g⁻¹ * x₀⁻¹) := by group
      rw [e]
      exact mul_mem hg h1
    have hk5 : (g * x₀ * g⁻¹ * x₀⁻¹) ^ 5 = 1 := by
      have h := orderOf_dvd_of_mem_zpowers hk_zp
      rw [hx₀] at h
      exact orderOf_dvd_iff_pow_eq_one.1 h
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := P)) ⟨_, hk_R⟩
    have ha' : (g * x₀ * g⁻¹ * x₀⁻¹) ^ 2 ^ a = 1 := by
      simpa using congrArg Subtype.val ha
    have hgcd : Nat.gcd 5 (2 ^ a) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right a (by norm_num))
    have hk1 : g * x₀ * g⁻¹ * x₀⁻¹ = 1 := by
      have h := (pow_gcd_eq_one).2 ⟨hk5, ha'⟩
      rw [hgcd, pow_one] at h
      exact h
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hk1)
  have hR4 : ∀ g ∈ CFSG.pCore 2 P, g ^ 4 = 1 := by
    intro g hg
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := P)) ⟨g, hg⟩
    have hb' : g ^ 2 ^ b = 1 := by
      simpa using congrArg Subtype.val hb
    have hn : g ^ Nat.card P = 1 := pow_card_eq_one'
    rw [h20] at hn
    have hd1 : orderOf g ∣ 2 ^ b := orderOf_dvd_iff_pow_eq_one.2 hb'
    have hd2 : orderOf g ∣ 20 := orderOf_dvd_iff_pow_eq_one.2 hn
    obtain ⟨j, _, hjg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    rw [hjg] at hd2
    have hj2 : j ≤ 2 := by
      by_contra hcon
      have h8 : 2 ^ 3 ∣ 20 := (pow_dvd_pow 2 (by omega : 3 ≤ j)).trans hd2
      norm_num at h8
    have hd4 : orderOf g ∣ 4 := by
      rw [hjg]
      interval_cases j <;> norm_num
    exact orderOf_dvd_iff_pow_eq_one.1 hd4
  have hbot : CFSG.pCore 2 P = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hcomm : ι g * ι x₀ = ι x₀ * ι g := by
      rw [← map_mul, ← map_mul, hcent g hg]
    have h4 : ι g ^ 4 = 1 := by rw [← map_pow, hR4 g hg, map_one]
    have hι1 : ι g = 1 := perm_five_pow_four_eq_one_of_commute (ι x₀) (ι g) hc5 hc1 hcomm h4
    exact hι (by rw [hι1, map_one])
  exact hbot

end CFSG.LocalAnalysis.EvenBN.Tits.S56
