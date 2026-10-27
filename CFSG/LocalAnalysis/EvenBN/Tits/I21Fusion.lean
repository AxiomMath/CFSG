module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Odd
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Red
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoConstrained

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem card_R_eq (h : SecTwoHyp G t u) : Nat.card (secTwoR t u) = 8 := by
  have hle := h.card_R_le
  have hdvd : 4 ∣ Nat.card (secTwoR t u) := by
    have := Subgroup.card_dvd_of_le (show zpowers u ≤ secTwoR t u from
      (zpowers_le).mpr SecTwoHyp.u_mem_R)
    rwa [Nat.card_zpowers, h.orderOf_u] at this
  have hne : Nat.card (secTwoR t u) ≠ 4 := by
    intro h4
    have hu4 : Nat.card (zpowers u) = 4 := by rw [Nat.card_zpowers, h.orderOf_u]
    have heq : zpowers u = secTwoR t u := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact (zpowers_le).mpr SecTwoHyp.u_mem_R
      · rw [h4, hu4]
    have htu : t ∈ zpowers u := heq ▸ SecTwoHyp.t_mem_R
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u ^ n = t := mem_powers_iff_mem_zpowers.mpr htu
    have h1 : t ^ 1 * (1 : G) ^ 0 * u ^ n = 1 := by
      rw [pow_one, pow_zero, mul_one, hn, ← sq, h.t_sq]
    have := (h.crel_one.nf_eq_one_iff).mp h1
    omega
  have hpos : 0 < Nat.card (secTwoR t u) := Nat.card_pos
  generalize Nat.card (secTwoR t u) = n at hle hdvd hne hpos ⊢
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.I21

namespace CFSG.LocalAnalysis.EvenBN.Tits.Sec622Bar

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits I21

variable {G : Type} [Group G] [Finite G] {t u x : G}

variable (h : Sec622Bar G t u x)

include h

theorem x_pow_conj_z (k : ℕ) : x ^ k * u ^ 2 * (x ^ k)⁻¹ = x ^ (2 * k) * u ^ 2 := by
  have hinv : (x ^ k)⁻¹ = x ^ (4 * k) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 4 * k = 5 * k by ring, pow_mul, h.x_five,
      one_pow]
  have h1 := h.crel.pow_u_mul_x_pow 2 (4 * k)
  calc x ^ k * u ^ 2 * (x ^ k)⁻¹ = x ^ k * (u ^ 2 * x ^ (4 * k)) := by rw [hinv, mul_assoc]
    _ = x ^ k * (x ^ (4 * k * 2 ^ 2) * u ^ 2) := by rw [h1]
    _ = x ^ (k + 4 * k * 2 ^ 2) * u ^ 2 := by rw [pow_add]; exact (mul_assoc _ _ _).symm
    _ = x ^ (2 * k) * u ^ 2 := by
      rw [show k + 4 * k * 2 ^ 2 = 2 * k + 5 * (3 * k) by ring, pow_add x (2 * k),
        pow_mul x 5 (3 * k), h.x_five, one_pow, mul_one]

theorem conj_t_x_pow (y : G) (hy : y * t * y⁻¹ = t * u ^ 2) (i : ℕ) :
    (x ^ (3 * i) * y) * t * (x ^ (3 * i) * y)⁻¹ = t * (x ^ i * u ^ 2) := by
  have hc := h.crel.t_comm_x_pow (3 * i)
  have h6 : x ^ (2 * (3 * i)) = x ^ i := by
    rw [show 2 * (3 * i) = i + 5 * i by ring, pow_add, pow_mul, h.x_five, one_pow, mul_one]
  calc (x ^ (3 * i) * y) * t * (x ^ (3 * i) * y)⁻¹
      = x ^ (3 * i) * (y * t * y⁻¹) * (x ^ (3 * i))⁻¹ := by group
    _ = x ^ (3 * i) * (t * u ^ 2) * (x ^ (3 * i))⁻¹ := by rw [hy]
    _ = t * (x ^ (3 * i) * u ^ 2 * (x ^ (3 * i))⁻¹) := by
      rw [← mul_assoc, ← hc]; group
    _ = t * (x ^ i * u ^ 2) := by rw [h.x_pow_conj_z, h6]

theorem conj_t_inter_C (hy : ∃ y : G, y * t * y⁻¹ = t * u ^ 2) (s : G)
    (hsC : s ∈ centralizer ({t} : Set G)) :
    (∃ g : G, g * t * g⁻¹ = s) ↔ s = t ∨ ∃ i : ℕ, s = t * (x ^ i * u ^ 2) := by
  constructor
  · rintro ⟨g, rfl⟩
    have hsq : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, h.secTwo.t_sq]; group
    have hne : g * t * g⁻¹ ≠ 1 := by
      intro h1
      apply h.secTwo.t_ne_one
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hmem : g * t * g⁻¹ ∈ closure ({t, u, x} : Set G) := h.cent ▸ hsC
    rcases h.crel.eq_of_sq_eq_one hmem hsq hne with h1 | ⟨i, h1⟩ | ⟨i, h1⟩
    · exact Or.inl h1
    · exfalso
      have h6 : x ^ (2 * (3 * i)) = x ^ i := by
        rw [show 2 * (3 * i) = i + 5 * i by ring, pow_add, pow_mul, h.x_five, one_pow, mul_one]
      have hz : x ^ (3 * i) * u ^ 2 * (x ^ (3 * i))⁻¹ = x ^ i * u ^ 2 := by
        rw [h.x_pow_conj_z, h6]
      apply h.secTwo.conj_z_ne_t ((g⁻¹ * x ^ (3 * i)))
      calc g⁻¹ * x ^ (3 * i) * u ^ 2 * (g⁻¹ * x ^ (3 * i))⁻¹
          = g⁻¹ * (x ^ (3 * i) * u ^ 2 * (x ^ (3 * i))⁻¹) * g := by group
        _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hz, ← h1]
        _ = t := by group
    · exact Or.inr ⟨i, h1⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨1, by group⟩
    · obtain ⟨y, hy'⟩ := hy
      exact ⟨x ^ (3 * i) * y, h.conj_t_x_pow y hy' i⟩

theorem card_conj_inter_C (hy : ∃ y : G, y * t * y⁻¹ = t * u ^ 2) :
    Nat.card {s : G // (∃ g : G, g * t * g⁻¹ = s) ∧ t * s * t⁻¹ = s} =
      if orderOf x = 5 then 6 else 2 := by
  classical
  set F : Finset G := insert t ((Finset.range 5).image fun i => t * (x ^ i * u ^ 2)) with hF
  have hsC : ∀ s : G, t * s * t⁻¹ = s ↔ s ∈ centralizer ({t} : Set G) := by
    intro s
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]
  have hxuC : ∀ i : ℕ, t * (x ^ i * u ^ 2) ∈ centralizer ({t} : Set G) := by
    intro i
    have h1 : x ^ i * u ^ 2 ∈ centralizer ({t} : Set G) := by
      rw [h.cent]
      exact mul_mem (pow_mem (subset_closure (by simp)) i) (pow_mem (subset_closure (by simp)) 2)
    exact mul_mem (mem_centralizer_singleton_iff.mpr rfl) h1
  have hmem : ∀ s : G, ((∃ g : G, g * t * g⁻¹ = s) ∧ t * s * t⁻¹ = s) ↔ s ∈ F := by
    intro s
    rw [hsC s, hF, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hconj, hC⟩
      rcases (h.conj_t_inter_C hy s hC).mp hconj with rfl | ⟨i, rfl⟩
      · exact Or.inl rfl
      · right
        refine ⟨i % 5, Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
        rw [pow_mod_of_pow_eq_one h.x_five i]
    · rintro (rfl | ⟨i, -, rfl⟩)
      · exact ⟨⟨1, by group⟩, mem_centralizer_singleton_iff.mpr rfl⟩
      · exact ⟨(h.conj_t_inter_C hy _ (hxuC i)).mpr (Or.inr ⟨i, rfl⟩), hxuC i⟩
  have hcard : Nat.card {s : G // (∃ g : G, g * t * g⁻¹ = s) ∧ t * s * t⁻¹ = s} = F.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  rw [hcard]
  have hznt : ∀ i : ℕ, t * (x ^ i * u ^ 2) ≠ t := by
    intro i hi
    have h1 : t ^ 0 * x ^ i * u ^ 2 = 1 := by
      have : x ^ i * u ^ 2 = 1 := by simpa using hi
      simpa using this
    have := (h.crel.nf_eq_one_iff).mp h1
    omega
  rcases h.x_cases.symm with hx5 | hx1
  · rw [if_pos hx5, hF, Finset.card_insert_of_notMem, Finset.card_image_of_injOn,
      Finset.card_range]
    · intro i hi j hj hij
      have h1 : x ^ i = x ^ j := by
        have := mul_left_cancel hij
        exact mul_right_cancel this
      rw [pow_inj_mod, hx5] at h1
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      omega
    · intro hmem'
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem'
      exact hznt i hi
  · have hne : ¬ orderOf x = 5 := by
      rw [hx1, orderOf_one]; norm_num
    rw [if_neg hne, hF, Finset.card_insert_of_notMem]
    · have : (Finset.range 5).image (fun i => t * (x ^ i * u ^ 2)) = {t * u ^ 2} := by
        ext s
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_singleton, hx1, one_pow,
          one_mul]
        constructor
        · rintro ⟨i, -, rfl⟩; rfl
        · rintro rfl; exact ⟨0, by norm_num, rfl⟩
      rw [this]
      rfl
    · intro hmem'
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem'
      exact hznt i hi

theorem factorization_card_centralizer :
    (Nat.card (centralizer ({t} : Set G))).factorization 2 = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Sylow.card_eq_multiplicity (secTwoSylowOf h.secTwo.sylow)
  have h2 : Nat.card (secTwoSylowOf h.secTwo.sylow) = Nat.card (secTwoR t u) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.secTwo.R_le_centralizer).toEquiv
  rw [h2, card_R_eq h.secTwo] at h1
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

theorem four_dvd_index_of_big (S : Sylow 2 G) (hRS : secTwoR t u ≤ S)
    (hbig : 4 ≤ (secTwoR t u).relIndex S) : 4 ∣ (centralizer ({t} : Set G)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := Sylow.card_eq_multiplicity S
  have hrel := Subgroup.relIndex_mul_card (secTwoR t u) (S : Subgroup G)
  rw [inf_of_le_left hRS, card_R_eq h.secTwo] at hrel
  have hv : 5 ≤ (Nat.card G).factorization 2 := by
    by_contra hlt
    push Not at hlt
    have h16 : 2 ^ (Nat.card G).factorization 2 ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hS] at h16
    omega
  have hGC := Subgroup.index_mul_card (centralizer ({t} : Set G))
  have hidx : (centralizer ({t} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hC0 : Nat.card (centralizer ({t} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hfac := Nat.factorization_mul hidx hC0
  rw [hGC] at hfac
  have hfac2 := congrArg (fun f => f 2) hfac
  simp only [Finsupp.coe_add, Pi.add_apply] at hfac2
  rw [h.factorization_card_centralizer] at hfac2
  have h4 : 2 ^ 2 ∣ (centralizer ({t} : Set G)).index :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hidx).mpr (by omega)
  simpa using h4

theorem exists_normal_index_two_of_big (S : Sylow 2 G) (hRS : secTwoR t u ≤ S)
    (hbig : 4 ≤ (secTwoR t u).relIndex S) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N := by
  have hne : secTwoR t u ≠ S := by
    intro heq
    rw [heq, Subgroup.relIndex_self] at hbig
    omega
  obtain ⟨y, -, -, -, hy⟩ := h.secTwo.exists_conj_t_eq S.isPGroup' hRS hne
  refine exists_normal_index_two_of_conj_class h.secTwo.t_mul_t
    (h.four_dvd_index_of_big S hRS hbig) ?_
  rw [h.card_conj_inter_C ⟨y, hy⟩]
  split_ifs <;> norm_num

end CFSG.LocalAnalysis.EvenBN.Tits.Sec622Bar
