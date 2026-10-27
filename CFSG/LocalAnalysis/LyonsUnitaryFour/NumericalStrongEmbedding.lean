module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralizerIndex

public section

namespace CFSG.LyonsUnitaryFour

variable {G : Type} [Group G] [Finite G]

theorem lyons_numerical_order_identity_forces_strong_embedding [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) {z : G}
    (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) (hz1 : z ≠ 1)
    (a : ℕ)
    (hcubic : Nat.card G * Nat.card (Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) ^ 2 = a * Nat.card (Subgroup.centralizer ({z} : Set G)) ^ 3)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 12 ∣ Nat.card G) :
    (∀ e ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) = Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) ∧
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (Subgroup.normalizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) := by
  classical
  obtain ⟨hcard, -, hsqZ, hZcard, -, -, -, -, -, htrans, -, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  set D := Subgroup.centralizer (Z : Set G) with hD
  obtain ⟨q, hqodd, hq⟩ :=
    unitary_four_involution_centralizer_index_fourth_power hT S U hSU hzZ hz1
  have hDC : D ≤ Subgroup.centralizer ({z} : Set G) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hd) z hzZ).symm
  have hCcard : Nat.card (Subgroup.centralizer ({z} : Set G)) = q ^ 4 * Nat.card D := by
    have h := Subgroup.relIndex_mul_card (H := D) (K := Subgroup.centralizer ({z} : Set G))
    rw [inf_of_le_left hDC, hq] at h
    exact h.symm
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hGeq : Nat.card G = a * q ^ 12 * Nat.card D := by
    rw [hCcard] at hcubic
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hDpos 2)
    rw [hcubic]
    ring
  have hq1 : q = 1 := by
    by_contra hne
    obtain ⟨p, hpp, hpq⟩ := Nat.exists_prime_and_dvd hne
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hqodd) (even_iff_two_dvd.mpr hpq)
    apply hp p hpp hp2
    rw [hGeq]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpq 12) a) _
  have hCD : Subgroup.centralizer ({z} : Set G) = D := by
    have h1 : D.relIndex (Subgroup.centralizer ({z} : Set G)) = 1 := by rw [hq, hq1, one_pow]
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hDC
  have hcent : ∀ e ∈ Z, e ≠ 1 → Subgroup.centralizer ({e} : Set G) = D := by
    intro e he he1
    obtain ⟨n, hn, hne⟩ := htrans z hzZ e he hz1 he1
    have hninv : n⁻¹ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := inv_mem hn
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, ← hne]
    constructor
    · intro hg
      have h1 : n⁻¹ * g * n ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc n⁻¹ * g * n * z = n⁻¹ * (g * (n * z * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * z * n⁻¹) * g) * n := by rw [hg]
          _ = z * (n⁻¹ * g * n) := by group
      rw [hCD] at h1
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : n⁻¹ * w * n⁻¹⁻¹ ∈ Z := conj_mem_map_center hninv hw
      have h2 := (Subgroup.mem_centralizer_iff.mp h1) _ hw'
      calc w * g = n * ((n⁻¹ * w * n⁻¹⁻¹) * (n⁻¹ * g * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * g * n) * (n⁻¹ * w * n⁻¹⁻¹)) * n⁻¹ := by rw [h2]
        _ = g * w := by group
    · intro hg
      exact ((Subgroup.mem_centralizer_iff.mp hg) _ (conj_mem_map_center hn hzZ)).symm
  refine ⟨hcent, ?_⟩
  have hZS : Z ≤ (S : Subgroup G) := Subgroup.map_subtype_le _
  have hZcardG : Nat.card Z = 4 := by
    rw [hZ, Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective, hZcard]
  have hZbot : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcardG
    norm_num at hZcardG
  have hnotnormal : ¬ Z.Normal := by
    intro hnormal
    rcases hnormal.eq_bot_or_eq_top with h | h
    · exact hZbot h
    · have hle := Subgroup.card_le_of_le (le_top.trans h.ge : (S : Subgroup G) ≤ Z)
      rw [hcard, hZcardG] at hle
      norm_num at hle
  exact central_sylow_involution_set_strong_embedding S Z hZS
    (fun e he s hs => (mem_map_center_iff.mp he).2 s hs)
    (fun e he => (hsqZ e (hZS he)).mpr he) hZbot
    (fun t ht ht2 => (hsqZ t ht).mp ht2) hnotnormal hcent

theorem not_pow_twelve_dvd_lyons_order_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 12 ∣ 2 ^ 6 * 3 ^ 8 * 5 ^ 3 * 7 ^ 2 * 11 * 13 := by
  intro h
  have hle : p ^ 12 ≤ 2 ^ 6 * 3 ^ 8 * 5 ^ 3 * 7 ^ 2 * 11 * 13 := Nat.le_of_dvd (by norm_num) h
  have hp10 : p < 10 := by
    by_contra hge
    have h10 : 10 ^ 12 ≤ p ^ 12 := Nat.pow_le_pow_left (not_lt.mp hge) 12
    have := h10.trans hle
    norm_num at this
  interval_cases p <;> revert hp hp2 h <;> decide

theorem lyons_numerical_order_identity_forces_strong_embedding_of_dvd [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) {z : G}
    (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) (hz1 : z ≠ 1)
    (hcubic : Nat.card G * Nat.card (Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) ^ 2 = 195 * Nat.card (Subgroup.centralizer ({z} : Set G)) ^ 3)
    (hdvd : Nat.card G ∣ 2 ^ 6 * 3 ^ 8 * 5 ^ 3 * 7 ^ 2 * 11 * 13) :
    (∀ e ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) = Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) ∧
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (Subgroup.normalizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) :=
  lyons_numerical_order_identity_forces_strong_embedding hnonab hT S U hSU hzZ hz1 195 hcubic
    fun _ hp hp2 h => not_pow_twelve_dvd_lyons_order_bound hp hp2 (h.trans hdvd)

end CFSG.LyonsUnitaryFour
