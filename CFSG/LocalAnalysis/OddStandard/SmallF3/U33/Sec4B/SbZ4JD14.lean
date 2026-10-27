module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD14A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem mem_E_fin {e : H} :
    e ∈ closure ({t, τ, l} : Set H) ↔
      ∃ a b c : Fin 2, e = t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) :=
  mem_closure_t_tau_l_iff h.t_sq h.tau_sq h.l_sq h.t_tau h.t_l h.tau_l

theorem mem_E_iff {e : H} :
    e ∈ closure ({t, τ, l} : Set H) ↔
      e = 1 ∨ e = t ∨ e = τ ∨ e = t * τ ∨ e = l ∨ e = t * l ∨ e = τ * l ∨
        e = t * τ * l :=
  mem_closure_t_tau_l_iff' h.t_sq h.tau_sq h.l_sq h.t_tau h.t_l h.tau_l

private lemma gen_mem_normalizer_Mc {g : H} (hg : g ∈ ({t, τ, l} : Set H)) :
    g ∈ normalizer (Mc : Set H) := by
  have hg' : g = t ∨ g = τ ∨ g = l := by simpa using hg
  have hg2 : g * g = 1 := by
    rcases hg' with rfl | rfl | rfl
    · exact h.t_sq
    · exact h.tau_sq
    · exact h.l_sq
  have hnf : ∀ k : H, k ∈ Mc → g * k * g⁻¹ ∈ Mc := by
    intro k hk
    rcases hg' with rfl | rfl | rfl
    · exact Mc_conj_t h hMh hMc hk
    · exact Mc_conj_tau h hMh hMc hk
    · exact Mc_conj_l h hMh hMc hk
  rw [Subgroup.mem_set_normalizer_iff]
  intro k
  constructor
  · exact hnf k
  · intro hk
    have hconj : g * (g * k * g⁻¹) * g⁻¹ = k := by
      calc g * (g * k * g⁻¹) * g⁻¹ = (g * g) * k * (g * g)⁻¹ := by group
        _ = k := by rw [hg2]; simp
    have hk' : g * (g * k * g⁻¹) * g⁻¹ ∈ Mc := hnf (g * k * g⁻¹) hk
    rwa [hconj] at hk'

theorem E_le_normalizer_Mc :
    closure ({t, τ, l} : Set H) ≤ normalizer (Mc : Set H) :=
  (Subgroup.closure_le (k := ({t, τ, l} : Set H))
    (Subgroup.normalizer (Mc : Set H))).mpr fun _ hg => gen_mem_normalizer_Mc h hMh hMc hg

theorem Mc_normal_Vh {g x : H} (hg : g ∈ zjVh Mc t τ l) (hx : x ∈ Mc) : g * x * g⁻¹ ∈ Mc := by
  have hle : zjVh Mc t τ l ≤ normalizer (Mc : Set H) :=
    sup_le Mc.le_normalizer (E_le_normalizer_Mc h hMh hMc)
  exact ((Subgroup.mem_set_normalizer_iff).mp (hle hg) x).mp hx

theorem mem_zjVh_iff_exists {g : H} :
    g ∈ zjVh Mc t τ l ↔ ∃ m ∈ Mc, ∃ e ∈ closure ({t, τ, l} : Set H), m * e = g := by
  change g ∈ (↑(Mc ⊔ closure ({t, τ, l} : Set H)) : Set H) ↔ _
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mc (closure ({t, τ, l} : Set H))
    (E_le_normalizer_Mc h hMh hMc)]
  exact Set.mem_mul

theorem mem_Vh_iff {g : H} : g ∈ zjVh Mc t τ l ↔
    ∃ m ∈ Mc, g = m ∨ g = m * t ∨ g = m * τ ∨ g = m * (t * τ) ∨ g = m * l ∨ g = m * (t * l) ∨
      g = m * (τ * l) ∨ g = m * (t * τ * l) := by
  rw [mem_zjVh_iff_exists h hMh hMc]
  constructor
  · rintro ⟨m, hm, e, he, rfl⟩
    refine ⟨m, hm, ?_⟩
    rcases (mem_E_iff h hMh hMc).mp he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rintro ⟨m, hm, h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8⟩
    · exact ⟨m, hm, 1, (mem_E_fin h hMh hMc).mpr ⟨0, 0, 0, by simp⟩, by rw [h1]; simp⟩
    · exact ⟨m, hm, t, (mem_E_fin h hMh hMc).mpr ⟨1, 0, 0, by simp⟩, h2.symm⟩
    · exact ⟨m, hm, τ, (mem_E_fin h hMh hMc).mpr ⟨0, 1, 0, by simp⟩, h3.symm⟩
    · exact ⟨m, hm, t * τ, (mem_E_fin h hMh hMc).mpr ⟨1, 1, 0, by simp⟩, h4.symm⟩
    · exact ⟨m, hm, l, (mem_E_fin h hMh hMc).mpr ⟨0, 0, 1, by simp⟩, h5.symm⟩
    · exact ⟨m, hm, t * l, (mem_E_fin h hMh hMc).mpr ⟨1, 0, 1, by simp⟩, h6.symm⟩
    · exact ⟨m, hm, τ * l, (mem_E_fin h hMh hMc).mpr ⟨0, 1, 1, by simp⟩, h7.symm⟩
    · exact ⟨m, hm, t * τ * l, (mem_E_fin h hMh hMc).mpr ⟨1, 1, 1, by simp⟩, h8.symm⟩

private lemma tau_ne_one' : τ ≠ 1 := fun h1 =>
  tau_not_mem_Mc h hMh hMc (by rw [h1]; exact Mc.one_mem)

private lemma l_ne_one' : l ≠ 1 := fun h1 =>
  l_not_mem_Mh h hMh (by rw [h1]; exact Mh.one_mem)

private lemma t_l_ne_one' : t * l ≠ 1 := fun h1 =>
  tl_not_mem_Mh h hMh (by rw [h1]; exact Mh.one_mem)

private lemma t_tau_ne_one' : t * τ ≠ 1 := by
  intro h1
  have hmem : t * τ ∈ Mh := by rw [h1]; exact Mh.one_mem
  have ht : t ∈ Mh := by
    have := Mh.mul_mem hmem (tau_mem_Mh h hMh)
    rwa [show (t * τ) * τ = t by rw [mul_assoc, h.tau_sq, mul_one]] at this
  exact t_not_mem_Mh h hMh ht

private lemma tau_l_ne_one' : τ * l ≠ 1 := by
  intro h1
  have hmem : τ * l ∈ Mh := by rw [h1]; exact Mh.one_mem
  have hl : l ∈ Mh := by
    have := Mh.mul_mem hmem (tau_mem_Mh h hMh)
    rwa [show (τ * l) * τ = l by rw [h.tau_l, mul_assoc, h.tau_sq, mul_one]] at this
  exact l_not_mem_Mh h hMh hl

private lemma t_tau_l_ne_one' : t * τ * l ≠ 1 := by
  intro h1
  have hmem : t * τ * l ∈ Mh := by rw [h1]; exact Mh.one_mem
  have htl : t * l ∈ Mh := by
    have := Mh.mul_mem hmem (tau_mem_Mh h hMh)
    rwa [show (t * τ * l) * τ = t * l by
      calc (t * τ * l) * τ = t * τ * (l * τ) := by group
        _ = t * τ * (τ * l) := by rw [← h.tau_l]
        _ = t * (τ * τ) * l := by group
        _ = t * l := by rw [h.tau_sq, mul_one]] at this
  exact tl_not_mem_Mh h hMh htl

private lemma word_ne_one_of_ne_zero {a b c : Fin 2} (hd : (a, b, c) ≠ (0, 0, 0)) :
    t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) ≠ 1 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
  all_goals
    first
      | exact h.t_ne_one
      | exact tau_ne_one' h hMh hMc
      | exact t_tau_ne_one' h hMh hMc
      | exact l_ne_one' h hMh hMc
      | exact t_l_ne_one' h hMh hMc
      | exact tau_l_ne_one' h hMh hMc
      | exact t_tau_l_ne_one' h hMh hMc

theorem card_closure_t_tau_l : Nat.card ↥(closure ({t, τ, l} : Set H)) = 8 := by
  classical
  let f : Fin 2 × Fin 2 × Fin 2 → ↥(closure ({t, τ, l} : Set H)) := fun p =>
    ⟨t ^ (p.1 : ℕ) * τ ^ (p.2.1 : ℕ) * l ^ (p.2.2 : ℕ),
      (mem_E_fin h hMh hMc).mpr ⟨p.1, p.2.1, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ heq
      have hwords : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) =
          t ^ (a' : ℕ) * τ ^ (b' : ℕ) * l ^ (c' : ℕ) := congrArg Subtype.val heq
      have hunit : (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)) *
          (t ^ (a' : ℕ) * τ ^ (b' : ℕ) * l ^ (c' : ℕ)) = 1 := by
        rw [hwords, zj_word_sq h.t_sq h.tau_sq h.l_sq h.t_tau h.t_l h.tau_l a' b' c']
      have hword : t ^ ((a + a' : Fin 2) : ℕ) * τ ^ ((b + b' : Fin 2) : ℕ) *
          l ^ ((c + c' : Fin 2) : ℕ) = 1 := by
        rw [← zj_word_mul h.t_sq h.tau_sq h.l_sq h.t_tau h.t_l h.tau_l a b c a' b' c']
        exact hunit
      by_cases hsum : (a + a', b + b', c + c') = (0, 0, 0)
      · have h1 : a + a' = 0 := by
          have := congrArg (fun p : Fin 2 × Fin 2 × Fin 2 => p.1) hsum
          simpa using this
        have h2 : b + b' = 0 := by
          have := congrArg (fun p : Fin 2 × Fin 2 × Fin 2 => p.2.1) hsum
          simpa using this
        have h3 : c + c' = 0 := by
          have := congrArg (fun p : Fin 2 × Fin 2 × Fin 2 => p.2.2) hsum
          simpa using this
        exact Prod.ext (fin2_add_eq_zero h1)
          (Prod.ext (fin2_add_eq_zero h2) (fin2_add_eq_zero h3))
      · exact absurd hword (word_ne_one_of_ne_zero h hMh hMc hsum)
    · rintro ⟨x, hx⟩
      obtain ⟨a, b, c, rfl⟩ := (mem_E_fin h hMh hMc).mp hx
      exact ⟨(a, b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  norm_num [Fintype.card_prod]

theorem Mc_inf_E : Mc ⊓ closure ({t, τ, l} : Set H) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxMc, hxE⟩ := Subgroup.mem_inf.mp hx
  rcases (mem_E_iff h hMh hMc).mp hxE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (Mc_le_Mh h hMh hMc hxMc) (t_not_mem_Mh h hMh)
  · exact absurd hxMc (tau_not_mem_Mc h hMh hMc)
  · have hMh' : t * τ ∈ Mh := Mc_le_Mh h hMh hMc hxMc
    have ht : t ∈ Mh := by
      have := Mh.mul_mem hMh' (tau_mem_Mh h hMh)
      rwa [show (t * τ) * τ = t by rw [mul_assoc, h.tau_sq, mul_one]] at this
    exact absurd ht (t_not_mem_Mh h hMh)
  · exact absurd (Mc_le_Mh h hMh hMc hxMc) (l_not_mem_Mh h hMh)
  · exact absurd (Mc_le_Mh h hMh hMc hxMc) (tl_not_mem_Mh h hMh)
  · have hMh' : τ * l ∈ Mh := Mc_le_Mh h hMh hMc hxMc
    have hl : l ∈ Mh := by
      have := Mh.mul_mem hMh' (tau_mem_Mh h hMh)
      rwa [show (τ * l) * τ = l by rw [h.tau_l, mul_assoc, h.tau_sq, mul_one]] at this
    exact absurd hl (l_not_mem_Mh h hMh)
  · have hMh' : t * τ * l ∈ Mh := Mc_le_Mh h hMh hMc hxMc
    have htl : t * l ∈ Mh := by
      have := Mh.mul_mem hMh' (tau_mem_Mh h hMh)
      rwa [show (t * τ * l) * τ = t * l by
        calc (t * τ * l) * τ = t * τ * (l * τ) := by group
          _ = t * τ * (τ * l) := by rw [← h.tau_l]
          _ = t * (τ * τ) * l := by group
          _ = t * l := by rw [h.tau_sq, mul_one]] at this
    exact absurd htl (tl_not_mem_Mh h hMh)

theorem card_Vh : Nat.card ↥(zjVh Mc t τ l) = 2048 := by
  rw [zjVh, card_sup_of_le_normalizer (E_le_normalizer_Mc h hMh hMc) (Mc_inf_E h hMh hMc),
    card_Mc h hMh hMc, card_closure_t_tau_l h hMh hMc]

theorem Vh_isPGroup : IsPGroup 2 ↥(zjVh Mc t τ l) := by
  refine IsPGroup.of_card (n := 11) ?_
  rw [card_Vh h hMh hMc]
  norm_num

theorem Vh_maximal {P : Subgroup H} (hP : IsPGroup 2 P) (hle : zjVh Mc t τ l ≤ P) :
    P = zjVh Mc t τ l := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdiv1 : 2 ^ 11 ∣ 2 ^ n := by
    have hcv := Subgroup.card_dvd_of_le hle
    rw [card_Vh h hMh hMc, hn] at hcv
    rwa [show (2048 : ℕ) = 2 ^ 11 by norm_num] at hcv
  have hdiv2 : 2 ^ n ∣ 6144 := by
    have hcv := Subgroup.card_subgroup_dvd_card P
    rwa [card_H h, hn] at hcv
  have hn0 : 2 ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hge : 11 ≤ n := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).mp hdiv1
    rwa [Nat.factorization_pow_self Nat.prime_two] at this
  have hle11 : n ≤ 11 := by
    by_contra hcon
    have hge12 : 12 ≤ n := by omega
    have h12 : 2 ^ 12 ∣ 2 ^ n := pow_dvd_pow 2 hge12
    have hnot : ¬ (2 ^ 12 ∣ 6144) := by norm_num
    exact hnot (dvd_trans h12 hdiv2)
  have hn11 : n = 11 := by omega
  have hPcard : Nat.card P = 2048 := by
    rw [hn, hn11]; norm_num
  have hcardle : Nat.card P ≤ Nat.card ↥(zjVh Mc t τ l) := by
    rw [hPcard, card_Vh h hMh hMc]
  exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm

theorem comm_Vh_mem_Mc {a b : H} (ha : a ∈ zjVh Mc t τ l) (hb : b ∈ zjVh Mc t τ l) :
    a * b * a⁻¹ * b⁻¹ ∈ Mc := by
  obtain ⟨m, hm, e, he, rfl⟩ := (mem_zjVh_iff_exists h hMh hMc).mp ha
  obtain ⟨m', hm', e', he', rfl⟩ := (mem_zjVh_iff_exists h hMh hMc).mp hb
  have heV : e ∈ zjVh Mc t τ l := Subgroup.mem_sup_right he
  have he'V : e' ∈ zjVh Mc t τ l := Subgroup.mem_sup_right he'
  have h1 : e * m' * e⁻¹ ∈ Mc := Mc_normal_Vh h hMh hMc heV hm'
  have h2 : e * e' * e⁻¹ = e' := by
    have hcomm := closure_comm h.t_tau h.t_l h.tau_l he he'
    calc e * e' * e⁻¹ = (e * e') * e⁻¹ := by group
      _ = (e' * e) * e⁻¹ := by rw [hcomm.eq]
      _ = e' := by group
  have h3 : e' * m⁻¹ * e'⁻¹ ∈ Mc := Mc_normal_Vh h hMh hMc he'V (Mc.inv_mem hm)
  have hfinal : (m * e) * (m' * e') * (m * e)⁻¹ * (m' * e')⁻¹ =
      m * (e * m' * e⁻¹) * (e' * m⁻¹ * e'⁻¹) * m'⁻¹ := by
    rw [show (m * e) * (m' * e') * (m * e)⁻¹ * (m' * e')⁻¹ =
        m * (e * m' * e⁻¹) * (e * e' * e⁻¹) * m⁻¹ * e'⁻¹ * m'⁻¹ by group, h2]
    group
  rw [hfinal]
  exact Mc.mul_mem (Mc.mul_mem (Mc.mul_mem hm h1) h3) (Mc.inv_mem hm')

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
