module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Cong
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7TFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem four_dvd_index_of_orbit {E : Subgroup X} (hTE : S.data.T ≤ normalizer (E : Set X))
    (h4 : {b | ∃ n ∈ normalizer (E : Set X), n * S.t * n⁻¹ = b}.ncard = 4) :
    4 ∣ (centralizer ({S.t} : Set X)).index := by
  set N := normalizer (E : Set X) with hN
  set C := centralizer ({S.t} : Set X) with hC
  have hidx := relIndex_inf_centralizer_eq_ncard N S.t
  rw [h4] at hidx
  have hcardN : Nat.card N = Nat.card (N ⊓ C : Subgroup X) * 4 := by
    rw [← hidx, mul_comm, ← relIndex_mul_card, inf_of_le_left inf_le_left]
  have hT1 := S.card_T_eq_of_le (le_inf hTE S.data.T_le_centralizer) inf_le_right
  have hT2 := S.card_T_eq_two_pow
  have hv : (Nat.card (N ⊓ C : Subgroup X)).factorization 2 = (Nat.card C).factorization 2 :=
    Nat.pow_right_injective le_rfl (hT1.symm.trans hT2)
  have hpos : ∀ (H : Subgroup X), Nat.card H ≠ 0 := fun H => Nat.card_pos.ne'
  have hvN : (Nat.card N).factorization 2 = (Nat.card C).factorization 2 + 2 := by
    rw [hcardN, Nat.factorization_mul (hpos _) (by norm_num), Finsupp.add_apply, hv,
      show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hvX : (Nat.card C).factorization 2 + 2 ≤ (Nat.card X).factorization 2 := by
    rw [← hvN]
    exact (Nat.factorization_le_iff_dvd (hpos _) Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card N) 2
  have hXC : Nat.card X = Nat.card C * C.index := (C.card_mul_index).symm
  have hidx0 : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [hXC, Nat.factorization_mul (hpos _) hidx0, Finsupp.add_apply] at hvX
  have h2 : 2 ≤ C.index.factorization 2 := by omega
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hidx0).mpr h2
  simpa using this

theorem tk_eq_t_iff {c d : Fin 2} (h : S.t ^ (c : ℕ) * S.k ^ (d : ℕ) = S.t) : c = 1 ∧ d = 0 := by
  fin_cases c <;> fin_cases d
  · exact absurd h.symm (by simpa using S.t_ne_one)
  · exact absurd (by simpa using h) S.k_ne_t
  · exact ⟨rfl, rfl⟩
  · exfalso
    apply S.k_ne_one
    simpa using h

theorem z_mul_ne_t {c d : Fin 2} : S.z * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ)) ≠ S.t := by
  intro h
  have hmem : S.z ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X) := by
    have : S.z = S.t * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ))⁻¹ := by
      calc S.z = S.z * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ)) * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ))⁻¹ := by
            group
        _ = S.t * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ))⁻¹ := by rw [h]
    rw [this]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (inv_mem (mul_mem
      (mem_sup_left (pow_mem (mem_zpowers _) _)) (mem_sup_right (pow_mem (mem_zpowers _) _))))
  have : S.z ∈ (⊥ : Subgroup X) := S.R_inf_tk ▸ mem_inf.mpr ⟨S.z_mem, hmem⟩
  exact S.z_ne_one (mem_bot.mp this)

theorem conjTo_E_xy_of_tz
    (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.t * S.z) {e : X}
    (he : e ∈ S.E (S.x * S.y)) (hce : ConjTo S.t e) :
    e = S.t ∨ e = S.t * S.z ∨ e = S.x * S.y * S.t ∨ e = S.z * (S.x * S.y) * S.t := by
  obtain ⟨a, b, c, d, rfl⟩ := S.eq_of_mem_E S.xy_mem S.xy_sq (S.z_comm_of_mem_T S.xy_mem.1) he
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hkB : S.k ∈ S.B := subset_closure (by simp)
  have hf : S.t ^ (c : ℕ) * S.k ^ (d : ℕ) ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X) :=
    mul_mem (mem_sup_left (pow_mem (mem_zpowers _) _)) (mem_sup_right (pow_mem (mem_zpowers _) _))
  have hfB : S.t ^ (c : ℕ) * S.k ^ (d : ℕ) ∈ S.B := mul_mem (pow_mem htB _) (pow_mem hkB _)
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hzf : ConjTo S.t (S.z * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ))) → c = 1 ∧ d = 0 := by
    intro h
    rcases (hO _ (mul_mem hzB hfB)).mp h with h1 | h1
    · exact absurd h1 S.z_mul_ne_t
    · apply S.tk_eq_t_iff
      rw [← hzt] at h1
      exact mul_left_cancel h1
  fin_cases b
  · simp only [pow_zero, mul_one] at hce ⊢
    have heB : S.z ^ (a : ℕ) * S.t ^ (c : ℕ) * S.k ^ (d : ℕ) ∈ S.B :=
      mul_mem (mul_mem (pow_mem hzB _) (pow_mem htB _)) (pow_mem hkB _)
    rcases (hO _ heB).mp hce with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · fin_cases a
    · simp only [pow_zero, pow_one, one_mul] at hce ⊢
      rw [mul_assoc] at hce
      obtain ⟨rfl, rfl⟩ := hzf ((S.conjTo_xy_iff hf).1.mp hce)
      exact Or.inr (Or.inr (Or.inl (by simp)))
    · simp only [pow_one] at hce ⊢
      rw [mul_assoc] at hce
      obtain ⟨rfl, rfl⟩ := hzf ((S.conjTo_xy_iff hf).2.mp hce)
      exact Or.inr (Or.inr (Or.inr (by simp)))

theorem not_subConj_of_tz (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.t * S.z) :
    ¬ SubConj (S.E S.y) (S.E (S.x * S.y)) := by
  rintro ⟨g, hg⟩
  have hgmem : ∀ e ∈ S.E S.y, g * e * g⁻¹ ∈ S.E (S.x * S.y) := fun e he => hg ▸ ⟨e, he, rfl⟩
  have hgmem' : ∀ e ∈ S.E (S.x * S.y), g⁻¹ * e * g ∈ S.E S.y := by
    intro e he
    rw [← hg] at he
    obtain ⟨e', he', rfl⟩ := he
    simpa [MulAut.conj_apply, mul_assoc] using he'
  have htEy : S.t ∈ S.E S.y := subset_closure (by simp)
  have htExy : S.t ∈ S.E (S.x * S.y) := subset_closure (by simp)
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hxyt : S.x * S.y * S.t = S.t * (S.x * S.y) := (S.data.commute_t S.xy_mem.1)
  have hnotC : ∀ m : X, m * S.t * m⁻¹ = S.t → ¬ ∀ e ∈ S.E S.y, m * e * m⁻¹ ∈ S.E (S.x * S.y) := by
    intro m hm hme
    refine S.not_conj_E_y_E_xy ?_ hme
    rw [mem_centralizer_singleton_iff]
    calc m * S.t = m * S.t * m⁻¹ * m := by group
      _ = S.t * m := by rw [hm]
  set u := g * S.t * g⁻¹ with hu
  have huE : u ∈ S.E (S.x * S.y) := hgmem _ htEy
  have huc : ConjTo S.t u := ⟨g, rfl⟩
  by_cases hA : ∃ n ∈ normalizer (S.E (S.x * S.y) : Set X), n * u * n⁻¹ = S.t
  · obtain ⟨n, hn, hnu⟩ := hA
    refine hnotC (n * g) (by
      calc n * g * S.t * (n * g)⁻¹ = n * u * n⁻¹ := by rw [hu]; group
        _ = S.t := hnu) fun e he => ?_
    have := (mem_normalizer_iff.mp hn _).mp (hgmem e he)
    simpa [mul_assoc] using this
  push Not at hA
  obtain ⟨d, hdC, hdN, hdz, hdxy, -⟩ := S.exists_d_xy
  have hdt : d * S.t * d⁻¹ = S.t := by
    rw [mem_centralizer_singleton_iff.mp hdC]
    group
  have hd1 : d * (S.t * S.z) * d⁻¹ = S.x * S.y * S.t := by
    calc d * (S.t * S.z) * d⁻¹ = (d * S.t * d⁻¹) * (d * S.z * d⁻¹) := by group
      _ = S.x * S.y * S.t := by rw [hdt, hdz, hxyt]
  have hd2 : d * (S.x * S.y * S.t) * d⁻¹ = S.z * (S.x * S.y) * S.t := by
    calc d * (S.x * S.y * S.t) * d⁻¹ = (d * (S.x * S.y) * d⁻¹) * (d * S.t * d⁻¹) := by group
      _ = S.z * (S.x * S.y) * S.t := by rw [hdxy, hdt]
  have hd3 : d * (S.z * (S.x * S.y) * S.t) * d⁻¹ = S.t * S.z := by
    have hxy2 : S.x * S.y * (S.z * (S.x * S.y)) = S.z := by
      calc S.x * S.y * (S.z * (S.x * S.y)) = S.z * ((S.x * S.y) * (S.x * S.y)) := by
            rw [← mul_assoc, ← S.z_comm_of_mem_T S.xy_mem.1]; group
        _ = S.z := by rw [← pow_two, S.xy_sq, mul_one]
    calc d * (S.z * (S.x * S.y) * S.t) * d⁻¹
        = (d * S.z * d⁻¹) * (d * (S.x * S.y) * d⁻¹) * (d * S.t * d⁻¹) := by group
      _ = S.t * S.z := by rw [hdz, hdxy, hdt, hxy2, hzt]
  have hfixt : ∀ n ∈ normalizer (S.E (S.x * S.y) : Set X), n * S.t * n⁻¹ = S.t := by
    intro n hn
    by_contra hvt
    have hvE : n * S.t * n⁻¹ ∈ S.E (S.x * S.y) := (mem_normalizer_iff.mp hn _).mp htExy
    have hut : u ≠ S.t := fun h => hA 1 (one_mem _) (by rw [h]; group)
    have hd : d ∈ normalizer (S.E (S.x * S.y) : Set X) := hdN
    have key : ∀ m ∈ normalizer (S.E (S.x * S.y) : Set X), m * (n * S.t * n⁻¹) * m⁻¹ = u →
        False := by
      intro m hm hmu
      apply hA (m * n)⁻¹ (inv_mem (mul_mem hm hn))
      rw [← hmu]
      group
    have hd2' : ∀ e, (d * d) * e * (d * d)⁻¹ = d * (d * e * d⁻¹) * d⁻¹ := fun e => by group
    have hrot : ∀ a ∈ ({S.t * S.z, S.x * S.y * S.t, S.z * (S.x * S.y) * S.t} : Set X),
        ∀ b ∈ ({S.t * S.z, S.x * S.y * S.t, S.z * (S.x * S.y) * S.t} : Set X),
        ∃ m ∈ normalizer (S.E (S.x * S.y) : Set X), m * a * m⁻¹ = b := by
      intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact ⟨1, one_mem _, by group⟩
      · exact ⟨d, hd, hd1⟩
      · exact ⟨d * d, mul_mem hd hd, by rw [hd2', hd1, hd2]⟩
      · exact ⟨d * d, mul_mem hd hd, by rw [hd2', hd2, hd3]⟩
      · exact ⟨1, one_mem _, by group⟩
      · exact ⟨d, hd, hd2⟩
      · exact ⟨d, hd, hd3⟩
      · exact ⟨d * d, mul_mem hd hd, by rw [hd2', hd3, hd1]⟩
      · exact ⟨1, one_mem _, by group⟩
    have hmem3 : ∀ e ∈ S.E (S.x * S.y), ConjTo S.t e → e ≠ S.t →
        e ∈ ({S.t * S.z, S.x * S.y * S.t, S.z * (S.x * S.y) * S.t} : Set X) := by
      intro e he hce het
      rcases S.conjTo_E_xy_of_tz hO he hce with h | h | h | h
      · exact absurd h het
      all_goals simp [h]
    obtain ⟨m, hm, hmu⟩ := hrot _ (hmem3 _ hvE ⟨n, rfl⟩ hvt) _ (hmem3 _ huE huc hut)
    exact key m hm hmu
  set u' := g⁻¹ * S.t * g with hu'
  have hu'E : u' ∈ S.E S.y := hgmem' _ htExy
  have hfixu' : ∀ m ∈ normalizer (S.E S.y : Set X), m * u' * m⁻¹ = u' := by
    intro m hm
    have hgm : g * m * g⁻¹ ∈ normalizer (S.E (S.x * S.y) : Set X) := by
      refine mem_normalizer_of_conj_mem fun e he => ?_
      have h1 := hgmem' e he
      have h2 := (mem_normalizer_iff.mp hm _).mp h1
      have h3 := hgmem _ h2
      simpa [mul_assoc] using h3
    have := hfixt _ hgm
    calc m * u' * m⁻¹ = g⁻¹ * ((g * m * g⁻¹) * S.t * (g * m * g⁻¹)⁻¹) * g := by rw [hu']; group
      _ = u' := by rw [this]
  have hu'B : u' ∈ S.B := by
    rw [← S.mem_B_iff (S.E_le_T S.y_mem hu'E)]
    intro h hh
    have := hfixu' h (S.T_le_normalizer_E S.y_mem hh)
    calc u' * h = h * (h⁻¹ * u' * h) := by group
      _ = h * u' := by
        congr 1
        calc h⁻¹ * u' * h = h⁻¹ * (h * u' * h⁻¹) * h := by rw [this]
          _ = u' := by group
  rcases (hO u' hu'B).mp ⟨g⁻¹, by rw [hu', inv_inv]⟩ with h1 | h1
  · refine hnotC g ?_ hgmem
    calc g * S.t * g⁻¹ = g * (g⁻¹ * S.t * g) * g⁻¹ := by rw [← hu', h1]
      _ = S.t := by group
  · obtain ⟨d', hd'C, hd'N, hd'z, -, -⟩ := S.exists_d_y
    have hfix := hfixu' d' hd'N
    rw [h1] at hfix
    have hd't : d' * S.t * d'⁻¹ = S.t := by
      rw [mem_centralizer_singleton_iff.mp hd'C]
      group
    have : S.t * (S.z * S.y) = S.t * S.z := by
      calc S.t * (S.z * S.y) = (d' * S.t * d'⁻¹) * (d' * S.z * d'⁻¹) := by rw [hd't, hd'z]
        _ = d' * (S.t * S.z) * d'⁻¹ := by group
        _ = S.t * S.z := hfix
    have hy1 : S.y = 1 := by
      have := mul_left_cancel this
      calc S.y = S.z⁻¹ * (S.z * S.y) := by group
        _ = 1 := by rw [this]; group
    exact S.y_not_mem_B (hy1 ▸ one_mem _)

theorem orbit_xy_of_tz (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.t * S.z)
    (hnot : ¬ SubConj (S.E S.y) (S.E (S.x * S.y))) :
    {b | ∃ n ∈ normalizer (S.E (S.x * S.y) : Set X), n * S.t * n⁻¹ = b}.ncard = 4 := by
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have htkf : S.t ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X) := mem_sup_left (mem_zpowers _)
  have hctz : ConjTo S.t (S.z * S.t) := by
    rw [hzt]
    exact (hO _ (mul_mem htB hzB)).mpr (Or.inr rfl)
  have hc1 : ConjTo S.t (S.x * S.y * S.t) := (S.conjTo_xy_iff htkf).1.mpr hctz
  have hc2 : ConjTo S.t (S.z * (S.x * S.y) * S.t) := (S.conjTo_xy_iff htkf).2.mpr hctz
  have htE : S.t ∈ S.E (S.x * S.y) := subset_closure (by simp)
  have hzE : S.z ∈ S.E (S.x * S.y) := subset_closure (by simp)
  have hxyE : S.x * S.y ∈ S.E (S.x * S.y) := subset_closure (by simp)
  have hmemO : ∀ e ∈ S.E (S.x * S.y), ConjTo S.t e →
      e ∈ {b | ∃ n ∈ normalizer (S.E (S.x * S.y) : Set X), n * S.t * n⁻¹ = b} := by
    intro e he hce
    obtain ⟨n, hn, hne⟩ := S.exists_normalizer_conj_eq_t (Or.inr rfl) hnot he hce
    refine ⟨n⁻¹, inv_mem hn, ?_⟩
    rw [← hne]
    group
  have hO4 : {b | ∃ n ∈ normalizer (S.E (S.x * S.y) : Set X), n * S.t * n⁻¹ = b} =
      ({S.t, S.t * S.z, S.x * S.y * S.t, S.z * (S.x * S.y) * S.t} : Set X) := by
    ext b
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hbE := (mem_normalizer_iff.mp hn _).mp htE
      rcases S.conjTo_E_xy_of_tz hO hbE ⟨n, rfl⟩ with h | h | h | h <;> simp [h]
    · intro hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact ⟨1, one_mem _, by group⟩
      · exact hmemO _ (mul_mem htE hzE) (hzt ▸ hctz)
      · exact hmemO _ (mul_mem hxyE htE) hc1
      · exact hmemO _ (mul_mem (mul_mem hzE hxyE) htE) hc2
  rw [hO4]
  have htT := S.data.t_mem_T
  have hzT := S.z_mem.1
  have hxyT := S.xy_mem.1
  have hψ1 : S.data.ψ ⟨S.t, htT⟩ = 1 := S.ψ_t
  have hψ2 : S.data.ψ ⟨S.t * S.z, mul_mem htT hzT⟩ = a0 ^ 2 := by
    rw [show (⟨S.t * S.z, mul_mem htT hzT⟩ : S.data.T) = ⟨S.t, htT⟩ * ⟨S.z, hzT⟩ from rfl,
      map_mul, S.ψ_t, S.ψ_z, one_mul]
  have hψ3 : S.data.ψ ⟨S.x * S.y * S.t, mul_mem hxyT htT⟩ = rho0 * (c0 * b0) := by
    rw [show (⟨S.x * S.y * S.t, mul_mem hxyT htT⟩ : S.data.T) =
      ⟨S.x, S.x_mem.1⟩ * ⟨S.y, S.y_mem.1⟩ * ⟨S.t, htT⟩ from rfl, map_mul, map_mul, S.ψ_x,
      S.ψ_y, S.ψ_t, mul_one]
  have hψ4 : S.data.ψ ⟨S.z * (S.x * S.y) * S.t, mul_mem (mul_mem hzT hxyT) htT⟩ =
      a0 ^ 2 * (rho0 * (c0 * b0)) := by
    rw [show (⟨S.z * (S.x * S.y) * S.t, mul_mem (mul_mem hzT hxyT) htT⟩ : S.data.T) =
      ⟨S.z, hzT⟩ * (⟨S.x, S.x_mem.1⟩ * ⟨S.y, S.y_mem.1⟩) * ⟨S.t, htT⟩ from rfl, map_mul,
      map_mul, map_mul, S.ψ_z, S.ψ_x, S.ψ_y, S.ψ_t, mul_one]
  have hne : ∀ {a b : X} (ha : a ∈ S.data.T) (hb : b ∈ S.data.T),
      S.data.ψ ⟨a, ha⟩ ≠ S.data.ψ ⟨b, hb⟩ → a ≠ b := fun ha hb h hab => h (by subst hab; rfl)
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
  · exact hne _ _ (by rw [hψ3, hψ4]; decide)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne _ _ (by rw [hψ2, hψ3]; decide), hne _ _ (by rw [hψ2, hψ4]; decide)⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne _ _ (by rw [hψ1, hψ2]; decide), hne _ _ (by rw [hψ1, hψ3]; decide),
      hne _ _ (by rw [hψ1, hψ4]; decide)⟩

theorem false_of_tz (hsign : ∀ φ : X →* ℤˣ, φ = 1)
    (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.t * S.z) : False := by
  have hnot := S.not_subConj_of_tz hO
  have hidx := S.four_dvd_index_of_orbit (S.T_le_normalizer_E S.xy_mem)
    (S.orbit_xy_of_tz hO hnot)
  have hcong := card_conj_modEq_card_conj_centralizer hsign S.t_sq S.t
  set C := centralizer ({S.t} : Set X) with hC
  have hclass : {a | IsConj S.t a}.ncard = C.index := by
    have := relIndex_inf_centralizer_eq_ncard (⊤ : Subgroup X) S.t
    rw [top_inf_eq, relIndex_top_right] at this
    rw [this]
    congr 1
    ext a
    simp only [Set.mem_ofPred_eq, mem_top, true_and, isConj_iff]
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have htzB : S.t * S.z ∈ S.B := mul_mem htB hzB
  have htz : ConjTo S.t (S.t * S.z) := (hO _ htzB).mpr (Or.inr rfl)
  have htC := S.t_mem_centralizer
  have hzC : S.z ∈ C := S.data.T_le_centralizer S.z_mem.1
  set A : Set X := {b | ∃ g ∈ C, g * (S.t * S.z) * g⁻¹ = b} with hA
  set Z : Set X := {b | ∃ g ∈ C, g * S.z * g⁻¹ = b} with hZ
  have hset : {a | IsConj S.t a ∧ S.t * a = a * S.t} = insert S.t A := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hconj, hcomm⟩
      obtain ⟨h, rfl⟩ := isConj_iff.mp hconj
      have haC : h * S.t * h⁻¹ ∈ C := mem_centralizer_singleton_iff.mpr hcomm.symm
      have ha2 : (h * S.t * h⁻¹) ^ 2 = 1 := by rw [conj_pow, S.t_sq]; group
      obtain ⟨g, hg, hgB⟩ := S.exists_conj_mem_B haC ha2
      have hgc : ConjTo S.t (g * (h * S.t * h⁻¹) * g⁻¹) := ⟨g * h, by group⟩
      have hgt : ∀ v, g⁻¹ * (g * v * g⁻¹) * g = v := fun v => by group
      rcases (hO _ hgB).mp hgc with h1 | h1
      · left
        calc h * S.t * h⁻¹ = g⁻¹ * (g * (h * S.t * h⁻¹) * g⁻¹) * g := (hgt _).symm
          _ = g⁻¹ * S.t * g := by rw [h1]
          _ = S.t := by
            rw [mem_centralizer_singleton_iff.mp (inv_mem hg)]
            group
      · right
        refine ⟨g⁻¹, inv_mem hg, ?_⟩
        rw [← h1, inv_inv]
        group
    · rintro (rfl | ⟨g, hg, rfl⟩)
      · exact ⟨IsConj.refl _, rfl⟩
      · obtain ⟨h, hh⟩ := htz
        refine ⟨isConj_iff.mpr ⟨g * h, by rw [← hh]; group⟩, ?_⟩
        exact (mem_centralizer_singleton_iff.mp
          (mul_mem (mul_mem hg (mul_mem htC hzC)) (inv_mem hg))).symm
  have htA : S.t ∉ A := by
    rintro ⟨g, hg, hgt⟩
    have : S.t * S.z = S.t := by
      calc S.t * S.z = g⁻¹ * (g * (S.t * S.z) * g⁻¹) * g := by group
        _ = g⁻¹ * S.t * g := by rw [hgt]
        _ = S.t := by rw [mem_centralizer_singleton_iff.mp (inv_mem hg)]; group
    exact S.z_ne_one (mul_left_cancel (this.trans (mul_one S.t).symm))
  have hAZ : A = (fun b => S.t * b) '' Z := by
    ext b
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g * S.z * g⁻¹, ⟨g, hg, rfl⟩, ?_⟩
      have := mem_centralizer_singleton_iff.mp hg
      calc S.t * (g * S.z * g⁻¹) = (S.t * g) * S.z * g⁻¹ := by group
        _ = g * S.t * S.z * g⁻¹ := by rw [← this]
        _ = g * (S.t * S.z) * g⁻¹ := by group
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨g, hg, ?_⟩
      have := mem_centralizer_singleton_iff.mp hg
      calc g * (S.t * S.z) * g⁻¹ = g * S.t * S.z * g⁻¹ := by group
        _ = S.t * g * S.z * g⁻¹ := by rw [this]
        _ = S.t * (g * S.z * g⁻¹) := by group
  have hAc : A.ncard = Z.ncard := by
    rw [hAZ, Set.ncard_image_of_injective _ (mul_right_injective S.t)]
  have hzt : ∀ g ∈ C, g * S.z * g⁻¹ ≠ S.t * S.z := by
    intro g hg h
    have hzc : ConjTo S.t S.z := by
      obtain ⟨h', hh'⟩ := htz
      exact ⟨g⁻¹ * h', by rw [show g⁻¹ * h' * S.t * (g⁻¹ * h')⁻¹ = g⁻¹ * (h' * S.t * h'⁻¹) * g
        by group, hh', ← h]; group⟩
    rcases (hO _ hzB).mp hzc with h1 | h1
    · exact S.data.t_not_mem_L (h1 ▸ S.z_mem.2)
    · apply S.t_ne_one
      calc S.t = S.t * S.z * S.z⁻¹ := by group
        _ = S.z * S.z⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel _
  have hZ1 := S.card_conj_z_modEq hzt
  rw [hset, Set.ncard_insert_of_notMem htA, hAc, hclass] at hcong
  have h0 : C.index ≡ 0 [MOD 4] := (Nat.modEq_zero_iff_dvd).mpr hidx
  have := (hZ1.add_right 1).symm.trans (hcong.trans h0)
  exact absurd this (by decide)

end A7Base

end CFSG.ComponentClassification.HSFLit
