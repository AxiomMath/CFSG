module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BCentProd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec5B517Quad (K : Fin 4 → Subgroup G) (z : G) : Prop where
  comm : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a
  iso : ∀ i : Fin 4, Nonempty (↥(K i) ≃* SL23)
  z_mem : ∀ i : Fin 4, z ∈ K i
  z_sq : z * z = 1
  z_ne : z ≠ 1

abbrev Sec5B517All (K : Fin 4 → Subgroup G) : Subgroup G := K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3

private lemma sec5b517_zeta_sq {K : Subgroup G} (e : ↥K ≃* SL23) {z : G} (hz : z ∈ K)
    (hz2 : z * z = 1) : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by
  rw [← map_mul, ← map_one e]
  congr 1
  apply Subtype.ext
  simpa using hz2

private lemma sec5b517_zeta_ne_one {K : Subgroup G} (e : ↥K ≃* SL23) {z : G} (hz : z ∈ K)
    (hz1 : z ≠ 1) : e ⟨z, hz⟩ ≠ 1 := by
  intro hc
  have hsub : (⟨z, hz⟩ : ↥K) = 1 := e.injective (by rw [hc, map_one])
  exact hz1 (congrArg Subtype.val hsub)

private lemma sec5b517_map_pow4_eq_one {K : Subgroup G} (e : ↥K ≃* SL23) {u : G} (hu : u ∈ K) :
    (e ⟨u, hu⟩) ^ 4 = 1 ↔ u ^ 4 = 1 := by
  constructor
  · intro h
    have hsub : (⟨u, hu⟩ : ↥K) ^ 4 = 1 := e.injective (by rw [map_pow, h, map_one])
    simpa using congrArg Subtype.val hsub
  · intro h
    rw [← map_pow, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using h

private lemma sec5b517_sl23_q8_central {ζ w : SL23} (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (hw4 : w ^ 4 = 1) (h : ∀ v : SL23, v ^ 4 = 1 → w * v = v * w) :
    w = 1 ∨ w = ζ := by
  have hζneg : ζ = -1 := (sl23_unique_involution ζ hζ).resolve_left hζ1
  rw [hζneg]
  revert w
  decide +kernel

private lemma sec5b517_sl23_exists_sq {ζ : SL23} (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1) :
    ∃ a : SL23, a * a = ζ := by
  have hζneg : ζ = -1 := (sl23_unique_involution ζ hζ).resolve_left hζ1
  rw [hζneg]
  exact (by decide : ∃ a : SL23, a * a = -1)

private lemma sec5b517_sup_comm {A B C : Subgroup G}
    (hA : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hB : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    ∀ x ∈ A ⊔ B, ∀ c ∈ C, x * c = c * x := by
  intro x hx c hc
  have hmem : A ⊔ B ≤ Subgroup.centralizer (C : Set G) := by
    apply sup_le
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro c' hc'
      exact (hA a ha c' hc').symm
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c' hc'
      exact (hB b hb c' hc').symm
  have hx' : x ∈ Subgroup.centralizer (C : Set G) := hmem hx
  rw [Subgroup.mem_centralizer_iff] at hx'
  exact (hx' c hc).symm

theorem sec5b517_central {K : Subgroup G} (e : ↥K ≃* SL23) {z u : G} (hz : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu : u ∈ K) (h : ∀ v ∈ K, u * v = v * u) :
    u = 1 ∨ u = z := by
  have hζ : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := sec5b517_zeta_sq e hz hz2
  have hζ1 : e ⟨z, hz⟩ ≠ 1 := sec5b517_zeta_ne_one e hz hz1
  have hcent : ∀ c : SL23, e ⟨u, hu⟩ * c = c * e ⟨u, hu⟩ := by
    intro c
    obtain ⟨v, rfl⟩ := e.surjective c
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact h v.1 v.2
  rcases sec5b_sl23_eq_of_central hζ hζ1 hcent with h1 | h1
  · left
    have hsub : (⟨u, hu⟩ : ↥K) = 1 := by
      apply e.injective
      rw [h1, map_one]
    exact congrArg Subtype.val hsub
  · right
    exact congrArg Subtype.val (e.injective h1)

theorem sec5b517_sq {K : Subgroup G} (e : ↥K ≃* SL23) {z u : G} (hz : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu : u ∈ K) (h : u * u = 1) : u = 1 ∨ u = z := by
  have hζ : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := sec5b517_zeta_sq e hz hz2
  have hζ1 : e ⟨z, hz⟩ ≠ 1 := sec5b517_zeta_ne_one e hz hz1
  have hsq : e ⟨u, hu⟩ * e ⟨u, hu⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using h
  rcases sec5b_sl23_eq_of_sq_eq_one hζ hζ1 hsq with h1 | h1
  · left
    have hsub : (⟨u, hu⟩ : ↥K) = 1 := by
      apply e.injective
      rw [h1, map_one]
    exact congrArg Subtype.val hsub
  · right
    exact congrArg Subtype.val (e.injective h1)

theorem sec5b517_pow4 {K : Subgroup G} (e : ↥K ≃* SL23) {u : G} (hu : u ∈ K) {m : ℕ}
    (h : u ^ (2 ^ m) = 1) : u ^ 4 = 1 := by
  let y : SL23 := e ⟨u, hu⟩
  have hy : y ^ (2 ^ m) = 1 := by
    dsimp [y]
    rw [← map_pow, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using h
  have hcard : Nat.card SL23 = 24 := by rw [Nat.card_eq_fintype_card]; decide
  have hdvd1 : orderOf y ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr hy
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd1
  have hdvd2 : orderOf y ∣ 24 := by rw [← hcard]; exact orderOf_dvd_natCard y
  have hj3 : j ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have h4 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have : 2 ^ 4 ∣ 24 := h4.trans (hj ▸ hdvd2)
    norm_num at this
  have hy8 : y ^ 8 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hj]
    have h : 2 ^ j ∣ 2 ^ 3 := pow_dvd_pow 2 hj3
    simpa using h
  have hy4 : y ^ 4 = 1 := (by decide : ∀ y : SL23, y ^ 8 = 1 → y ^ 4 = 1) y hy8
  exact (sec5b517_map_pow4_eq_one e hu).1 (by simpa [y] using hy4)

theorem sec5b517_q8_central {K : Subgroup G} (e : ↥K ≃* SL23) {z u : G} (hz : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu : u ∈ K) (h4 : u ^ 4 = 1)
    (h : ∀ v ∈ K, v ^ 4 = 1 → u * v = v * u) : u = 1 ∨ u = z := by
  have hζ : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := sec5b517_zeta_sq e hz hz2
  have hζ1 : e ⟨z, hz⟩ ≠ 1 := sec5b517_zeta_ne_one e hz hz1
  have hu4' : (e ⟨u, hu⟩) ^ 4 = 1 := (sec5b517_map_pow4_eq_one e hu).2 h4
  have hcomm : ∀ v : SL23, v ^ 4 = 1 → e ⟨u, hu⟩ * v = v * e ⟨u, hu⟩ := by
    intro v hv
    obtain ⟨v', rfl⟩ := e.surjective v
    have hv4 : v'.1 ^ 4 = 1 := (sec5b517_map_pow4_eq_one e v'.2).1 hv
    have hh : u * v'.1 = v'.1 * u := h v'.1 v'.2 hv4
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hh
  rcases sec5b517_sl23_q8_central hζ hζ1 hu4' hcomm with h1 | h1
  · left
    have hsub : (⟨u, hu⟩ : ↥K) = 1 := by
      apply e.injective
      rw [h1, map_one]
    exact congrArg Subtype.val hsub
  · right
    exact congrArg Subtype.val (e.injective h1)

theorem sec5b517_pow4_mul {K : Subgroup G} (e : ↥K ≃* SL23) {u v : G} (hu : u ∈ K) (hv : v ∈ K)
    (hu4 : u ^ 4 = 1) (hv4 : v ^ 4 = 1) : (u * v) ^ 4 = 1 := by
  have hu4' : (e ⟨u, hu⟩) ^ 4 = 1 := (sec5b517_map_pow4_eq_one e hu).2 hu4
  have hv4' : (e ⟨v, hv⟩) ^ 4 = 1 := (sec5b517_map_pow4_eq_one e hv).2 hv4
  have hmem : e ⟨u, hu⟩ * e ⟨v, hv⟩ ∈ sl23Q8 :=
    sl23Q8.mul_mem ((mem_sl23Q8 _).2 hu4') ((mem_sl23Q8 _).2 hv4')
  have h4' : (e (⟨u, hu⟩ * ⟨v, hv⟩)) ^ 4 = 1 := by rw [map_mul]; exact hmem
  exact (sec5b517_map_pow4_eq_one e (K.mul_mem hu hv)).1 (by simpa using h4')

theorem sec5b517_exists_sq {K : Subgroup G} (e : ↥K ≃* SL23) {z : G} (hz : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : ∃ a ∈ K, a * a = z := by
  have hζ : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := sec5b517_zeta_sq e hz hz2
  have hζ1 : e ⟨z, hz⟩ ≠ 1 := sec5b517_zeta_ne_one e hz hz1
  obtain ⟨a, ha⟩ := sec5b517_sl23_exists_sq hζ hζ1
  refine ⟨(e.symm a : G), (e.symm a).2, ?_⟩
  have h1 : (e.symm a : ↥K) * (e.symm a : ↥K) = ⟨z, hz⟩ := by
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact ha
  simpa using congrArg Subtype.val h1

variable {K : Fin 4 → Subgroup G} {z : G}

theorem Sec5B517Quad.z_comm (hq : Sec5B517Quad K z) {i : Fin 4} {v : G} (hv : v ∈ K i) :
    z * v = v * z := by
  have hji : i + 1 ≠ i := by fin_cases i <;> decide
  exact hq.comm (i + 1) i hji z (hq.z_mem (i + 1)) v hv

theorem Sec5B517Quad.eq_of_central (hq : Sec5B517Quad K z) {i : Fin 4} {u : G} (hu : u ∈ K i)
    (h : ∀ v ∈ K i, u * v = v * u) : u = 1 ∨ u = z :=
  sec5b517_central (Classical.choice (hq.iso i)) (hq.z_mem i) hq.z_sq hq.z_ne hu h

theorem Sec5B517Quad.eq_of_sq (hq : Sec5B517Quad K z) {i : Fin 4} {u : G} (hu : u ∈ K i)
    (h : u * u = 1) : u = 1 ∨ u = z :=
  sec5b517_sq (Classical.choice (hq.iso i)) (hq.z_mem i) hq.z_sq hq.z_ne hu h

theorem Sec5B517Quad.pow4_of_pow (hq : Sec5B517Quad K z) {i : Fin 4} {u : G} (hu : u ∈ K i)
    {m : ℕ} (h : u ^ (2 ^ m) = 1) : u ^ 4 = 1 :=
  sec5b517_pow4 (Classical.choice (hq.iso i)) hu h

theorem Sec5B517Quad.sq_of_pow4 (hq : Sec5B517Quad K z) {i : Fin 4} {u : G} (hu : u ∈ K i)
    (h : u ^ 4 = 1) : u * u = 1 ∨ u * u = z := by
  have hmem : u * u ∈ K i := (K i).mul_mem hu hu
  have hsq : (u * u) * (u * u) = 1 := by
    have h4 : u ^ 4 = (u * u) * (u * u) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [← h4]; exact h
  exact hq.eq_of_sq hmem hsq

theorem Sec5B517Quad.eq_of_central_q8 (hq : Sec5B517Quad K z) {i : Fin 4} {u : G}
    (hu : u ∈ K i) (h4 : u ^ 4 = 1) (h : ∀ v ∈ K i, v ^ 4 = 1 → u * v = v * u) :
    u = 1 ∨ u = z :=
  sec5b517_q8_central (Classical.choice (hq.iso i)) (hq.z_mem i) hq.z_sq hq.z_ne hu h4 h

theorem Sec5B517Quad.pow4_mul (hq : Sec5B517Quad K z) {i : Fin 4} {u v : G} (hu : u ∈ K i)
    (hv : v ∈ K i) (hu4 : u ^ 4 = 1) (hv4 : v ^ 4 = 1) : (u * v) ^ 4 = 1 :=
  sec5b517_pow4_mul (Classical.choice (hq.iso i)) hu hv hu4 hv4

theorem Sec5B517Quad.exists_sq (hq : Sec5B517Quad K z) (i : Fin 4) : ∃ a ∈ K i, a * a = z :=
  sec5b517_exists_sq (Classical.choice (hq.iso i)) (hq.z_mem i) hq.z_sq hq.z_ne

theorem Sec5B517Quad.ne (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) : K i ≠ K j := by
  intro heq
  obtain ⟨a, ha, ha2⟩ := hq.exists_sq i
  have haj : a ∈ K j := heq ▸ ha
  have hcomm : ∀ v ∈ K i, a * v = v * a := fun v hv => hq.comm j i hij.symm a haj v hv
  rcases hq.eq_of_central ha hcomm with h1 | hz
  · rw [h1, one_mul] at ha2
    exact hq.z_ne ha2.symm
  · rw [hz] at ha2
    exact hq.z_ne (by rw [← ha2, hq.z_sq])

theorem Sec5B517Quad.card_eq (hq : Sec5B517Quad K z) (i j : Fin 4) :
    Nat.card ↥(K i) = Nat.card ↥(K j) :=
  Nat.card_congr
    ((Classical.choice (hq.iso i)).toEquiv.trans (Classical.choice (hq.iso j)).toEquiv.symm)

theorem Sec5B517Quad.decomp (hq : Sec5B517Quad K z) {x : G} (hx : x ∈ Sec5B517All K) :
    ∃ k : Fin 4 → G, (∀ i, k i ∈ K i) ∧ x = k 0 * k 1 * k 2 * k 3 := by
  have h01 : ∀ a ∈ K 0, ∀ b ∈ K 1, a * b = b * a := hq.comm 0 1 (by decide)
  have h02 : ∀ a ∈ K 0, ∀ b ∈ K 2, a * b = b * a := hq.comm 0 2 (by decide)
  have h03 : ∀ a ∈ K 0, ∀ b ∈ K 3, a * b = b * a := hq.comm 0 3 (by decide)
  have h12 : ∀ a ∈ K 1, ∀ b ∈ K 2, a * b = b * a := hq.comm 1 2 (by decide)
  have h13 : ∀ a ∈ K 1, ∀ b ∈ K 3, a * b = b * a := hq.comm 1 3 (by decide)
  have h23 : ∀ a ∈ K 2, ∀ b ∈ K 3, a * b = b * a := hq.comm 2 3 (by decide)
  have hA3 : ∀ a ∈ K 0 ⊔ K 1 ⊔ K 2, ∀ b ∈ K 3, a * b = b * a :=
    sec5b517_sup_comm (A := K 0 ⊔ K 1) (B := K 2) (C := K 3)
      (sec5b517_sup_comm (A := K 0) (B := K 1) (C := K 3) h03 h13) h23
  have hA2 : ∀ a ∈ K 0 ⊔ K 1, ∀ b ∈ K 2, a * b = b * a :=
    sec5b517_sup_comm (A := K 0) (B := K 1) (C := K 2) h02 h12
  obtain ⟨a, ha, k3, hk3, hx3⟩ := sec5b_mem_sup_of_comm hA3 hx
  obtain ⟨a', ha', k2, hk2, ha3⟩ := sec5b_mem_sup_of_comm hA2 ha
  obtain ⟨k0, hk0, k1, hk1, ha'3⟩ := sec5b_mem_sup_of_comm h01 ha'
  refine ⟨![k0, k1, k2, k3], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hk0, hk1, hk2, hk3]
  · rw [hx3, ha3, ha'3]
    simp

end CFSG.OddStandard.SmallF3.Omega
