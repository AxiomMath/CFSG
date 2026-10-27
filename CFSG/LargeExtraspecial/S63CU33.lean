module

public import CFSG.LargeExtraspecial.S63BU33
public import Certificates.Certificate21110

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier

theorem u33CentCheck_eq_true : u33CentCheck = true := Certificates.certificate21110

theorem mem_u33Cent {L : List (Equiv.Perm (Fin 28))} {s x : Equiv.Perm (Fin 28)} :
    x ∈ u33Cent L s ↔ x ∈ L ∧ x * s = s * x := by
  simp [u33Cent]

theorem mem_u33Core_of {C : List (Equiv.Perm (Fin 28))} {x : Equiv.Perm (Fin 28)} (hx : x ∈ C)
    (h2 : x ^ 32 = 1) (hc : ∀ c ∈ C, c ^ 3 = 1 → (x * (c * x * c⁻¹)) ^ 32 = 1) :
    x ∈ u33Core C := by
  simp only [u33Core, List.mem_filter, Bool.and_eq_true, List.all_eq_true, u33Two,
    decide_eq_true_eq, tab_eq]
  exact ⟨hx, h2, fun c hc3 => hc c hc3.1 hc3.2⟩

theorem nodup_u33Core {L : List (Equiv.Perm (Fin 28))} (hL : L.Nodup) (s : Equiv.Perm (Fin 28)) :
    (u33Core (u33Cent L s)).Nodup :=
  (hL.filter _).filter _

theorem u33InvCheck_spec {L : List (Equiv.Perm (Fin 28))} {s : Equiv.Perm (Fin 28)}
    (h : u33InvCheck L s = true) :
    (u33Core (u33Cent L s)).length = 16 ∧
    (∀ t ∈ u33Cent L s, t * t = 1 → t ∈ u33Core (u33Cent L s)) ∧
    ∃ q ∈ u33Core (u33Cent L s), q * q = s ∧ (∀ c ∈ u33Cent L s, q * c = c * q) ∧
      ∀ n ∈ u33Core (u33Cent L s), (∀ m ∈ u33Core (u33Cent L s), n * m = m * n) →
        n = 1 ∨ n = q ∨ n = q * q ∨ n = q * q * q := by
  simp only [u33InvCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h16, hinv⟩, q, hq, ⟨hqq, hqc⟩, hZ⟩ := h
  refine ⟨h16, fun t ht htt => ?_, q, hq, hqq, hqc, fun n hn hc => ?_⟩
  · rcases hinv t ht with h1 | ⟨p, hp, rfl⟩
    · exact absurd htt h1
    · exact hp
  · rcases hZ n hn with h1 | ⟨r, hr, rfl⟩
    · have h2 : ((u33Core (u33Cent L s)).all fun m => decide (n * m = m * n)) = true :=
        List.all_eq_true.2 fun m hm => decide_eq_true (hc m hm)
      rw [h1] at h2
      exact absurd h2 (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))

theorem pow_thirtyTwo_eq_one {Y : Type} [Group Y] (hY : Nat.card Y = 6048) {y : Y} {k : ℕ}
    (hk : y ^ 2 ^ k = 1) : y ^ 32 = 1 := by
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have h2 : orderOf y ∣ 6048 := hY ▸ _root_.orderOf_dvd_natCard y
  rw [hj] at h2
  have hj5 : j ≤ 5 := by
    by_contra hc
    have h6 : 2 ^ 6 ∣ 6048 := (Nat.pow_dvd_pow 2 (by omega)).trans h2
    norm_num at h6
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact Nat.pow_dvd_pow 2 hj5

theorem u33Concl_of_check {Y : Type} [Group Y] (φ : Y →* Equiv.Perm (Fin 28))
    (hφ : Function.Injective φ) {L : List (Equiv.Perm (Fin 28))} (hL : L.Nodup)
    (hmem : ∀ y, φ y ∈ L) (hsurj : ∀ x ∈ L, ∃ y, φ y = x)
    (h32 : ∀ (y : Y) (k : ℕ), y ^ 2 ^ k = 1 → y ^ 32 = 1) {s : Y}
    (hchk : u33InvCheck L (φ s) = true) (N : Subgroup Y)
    (hNC : N ≤ centralizer ({s} : Set Y))
    (hNn : ∀ c ∈ centralizer ({s} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (hN16 : 2 ^ 4 ≤ Nat.card N) :
    (∀ t ∈ centralizer ({s} : Set Y), t * t = 1 → t ∈ N) ∧
    ∃ q ∈ N, q * q = s ∧ (∀ c ∈ centralizer ({s} : Set Y), q * c = c * q) ∧
      ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n ∈ zpowers q := by
  classical
  obtain ⟨h16, hinv, q', hq'P, hq'q', hq'C, hq'Z⟩ := u33InvCheck_spec hchk
  set C := u33Cent L (φ s) with hCdef
  set P := u33Core C with hPdef
  have hCmem : ∀ y : Y, y ∈ centralizer ({s} : Set Y) → φ y ∈ C := by
    intro y hy
    rw [mem_centralizer_singleton_iff] at hy
    rw [hCdef, mem_u33Cent, ← map_mul, ← map_mul, hy]
    exact ⟨hmem y, rfl⟩
  have hCpre : ∀ c ∈ C, ∃ y ∈ centralizer ({s} : Set Y), φ y = c := by
    intro c hc
    rw [hCdef, mem_u33Cent] at hc
    obtain ⟨y, rfl⟩ := hsurj c hc.1
    refine ⟨y, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact hφ (by rw [map_mul, map_mul, hc.2])
  have hN32 : ∀ n ∈ N, n ^ 32 = 1 := by
    intro n hn
    obtain ⟨k, hk⟩ := hN2 ⟨n, hn⟩
    exact h32 n k (by simpa using congrArg Subtype.val hk)
  have hNP : ∀ n ∈ N, φ n ∈ P := by
    intro n hn
    refine mem_u33Core_of (hCmem n (hNC hn)) (by rw [← map_pow, hN32 n hn, map_one]) ?_
    intro c hc _
    obtain ⟨y, hy, rfl⟩ := hCpre c hc
    have hm : n * (y * n * y⁻¹) ∈ N := mul_mem hn (hNn y hy n hn)
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hN32 _ hm, map_one]
  have hPN : ∀ x ∈ P, ∃ n ∈ N, φ n = x := by
    have hsub : φ '' (N : Set Y) ⊆ {x | x ∈ P} := by
      rintro _ ⟨n, hn, rfl⟩
      exact hNP n hn
    have hset : {x | x ∈ P} = ((P.toFinset : Finset (Equiv.Perm (Fin 28))) : Set _) := by
      ext x
      simp
    have heq : φ '' (N : Set Y) = {x | x ∈ P} := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_ ?_
      · rw [Set.ncard_image_of_injective _ hφ, hset, Set.ncard_coe_finset,
          List.toFinset_card_of_nodup (nodup_u33Core hL _), h16, ← Nat.card_coe_set_eq]
        exact hN16
      · rw [hset]
        exact Finset.finite_toSet _
    intro x hx
    have hx' : x ∈ φ '' (N : Set Y) := by rw [heq]; exact hx
    obtain ⟨n, hn, rfl⟩ := hx'
    exact ⟨n, hn, rfl⟩
  obtain ⟨q, hqN, rfl⟩ := hPN q' hq'P
  refine ⟨fun t ht htt => ?_, q, hqN, hφ (by rw [map_mul, hq'q']), fun c hc => ?_,
    fun n hn hnc => ?_⟩
  · obtain ⟨n, hn, hnt⟩ := hPN (φ t) (hinv _ (hCmem t ht) (by rw [← map_mul, htt, map_one]))
    rw [← hφ hnt]
    exact hn
  · exact hφ (by rw [map_mul, map_mul, hq'C _ (hCmem c hc)])
  · have hc : ∀ m ∈ P, φ n * m = m * φ n := by
      intro m hm
      obtain ⟨m', hm', rfl⟩ := hPN m hm
      rw [← map_mul, ← map_mul, hnc m' hm']
    rw [mem_zpowers_iff]
    rcases hq'Z (φ n) (hNP n hn) hc with h | h | h | h
    · exact ⟨0, hφ (by rw [h, zpow_zero, map_one])⟩
    · exact ⟨1, hφ (by rw [h, zpow_one])⟩
    · refine ⟨2, hφ ?_⟩
      rw [h, ← map_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
    · refine ⟨3, hφ ?_⟩
      rw [h, ← map_mul, ← map_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
        pow_succ, pow_two]

theorem u33CentInput : U33CentInput := by
  intro Y _ hY s hs N hNC hNn hN2 _ hN16
  obtain ⟨e⟩ := GH74.KGroups.U33.equiv_of_lieModel hY
  let φ : Y →* Equiv.Perm (Fin 28) := QP.originalSubgroup.subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hmem : ∀ y, φ y ∈ elemsT QP := fun y => (mem_elemsT QP QP_ok _).2 (e y).2
  have hsurj : ∀ x ∈ elemsT QP, ∃ y, φ y = x := by
    intro x hx
    refine ⟨e.symm ⟨x, (mem_elemsT QP QP_ok x).1 hx⟩, ?_⟩
    simp [φ]
  have hcard : Nat.card Y = 6048 := by
    rw [Nat.card_congr e.toEquiv, card_group _ QP_ok, QP_valid.2]
  have hss : s * s = 1 := by
    rw [← pow_two, ← hs]
    exact pow_orderOf_eq_one s
  have hs1 : φ s ≠ 1 := by
    intro h
    have : s = 1 := hφ (by rw [h, map_one])
    rw [this, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hchk : u33InvCheck (elemsT QP) (φ s) = true := by
    have h := List.all_eq_true.1 u33CentCheck_eq_true (φ s) (hmem s)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · exact absurd (by rw [← map_mul, hss, map_one]) h
    · exact absurd h hs1
    · exact h
  exact u33Concl_of_check φ hφ (nodup_elemsT QP QP_ok) hmem hsurj
    (fun y k hk => pow_thirtyTwo_eq_one hcard hk) hchk N hNC hNn hN2 hN16

end CFSG.LargeExtraspecial.S63
