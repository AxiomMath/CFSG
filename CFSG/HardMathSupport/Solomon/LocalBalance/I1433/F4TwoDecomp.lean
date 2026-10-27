module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoRoots

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

set_option maxRecDepth 100000

@[expose] def e4 (j : Nat) : List ℤ := (List.range 4).map (fun i => if i = j then 1 else 0)

abbrev decompP : Prop :=
  ∀ κ ∈ [1, 2], ∀ κ' ∈ [1, 2],
  ∀ s ∈ rts, ipL s s = 2 * κ → ∀ t ∈ rts, ipL t t = 2 * κ → ipL s t = -κ →
  ∀ s' ∈ rts, ipL s' s' = 2 * κ' → ipL s s' = 0 → ipL t s' = 0 →
  ∀ t' ∈ rts, ipL t' t' = 2 * κ' → ipL s' t' = -κ' → ipL s t' = 0 → ipL t t' = 0 →
  ∀ j ∈ [0, 1, 2, 3],
    ipL (e4 j) s % κ = 0 ∧ ipL (e4 j) t % κ = 0 ∧ ipL (e4 j) s' % κ' = 0 ∧
    ipL (e4 j) t' % κ' = 0 ∧
    ∀ i ∈ [0, 1, 2, 3],
      3 * (e4 j).getD i 0 =
        (2 * (ipL (e4 j) s / κ) + ipL (e4 j) t / κ) * s.getD i 0 +
        ((ipL (e4 j) s / κ) + 2 * (ipL (e4 j) t / κ)) * t.getD i 0 +
        (2 * (ipL (e4 j) s' / κ') + ipL (e4 j) t' / κ') * s'.getD i 0 +
        ((ipL (e4 j) s' / κ') + 2 * (ipL (e4 j) t' / κ')) * t'.getD i 0

theorem decompP_holds : decompP := by decide +kernel

theorem e4_vec4 (j : Fin Tag.F4.rank) : vec4 (e4 j.val) = Pi.single j 1 := by
  funext i
  obtain ⟨j, hj⟩ := j
  obtain ⟨i, hi⟩ := i
  rw [rank_F4] at hj hi
  interval_cases j <;> interval_cases i <;> rfl

theorem decomposition_single {κ κ' : ℤ} (hκ : κ = 1 ∨ κ = 2)
    (hκ' : κ' = 1 ∨ κ' = 2) {s t s' t' : V4} (hs : IsRoot Tag.F4 s) (ht : IsRoot Tag.F4 t)
    (hs' : IsRoot Tag.F4 s') (ht' : IsRoot Tag.F4 t') (hss : ipF4 s s = 2 * κ)
    (htt : ipF4 t t = 2 * κ) (hst : ipF4 s t = -κ) (hs's' : ipF4 s' s' = 2 * κ')
    (hss' : ipF4 s s' = 0) (hts' : ipF4 t s' = 0) (ht't' : ipF4 t' t' = 2 * κ')
    (hs't' : ipF4 s' t' = -κ') (hst' : ipF4 s t' = 0) (htt' : ipF4 t t' = 0) (j : Fin Tag.F4.rank) :
    ∃ a b a' b' : ℤ, ipF4 (Pi.single j 1) s = κ * a ∧ ipF4 (Pi.single j 1) t = κ * b ∧
      ipF4 (Pi.single j 1) s' = κ' * a' ∧ ipF4 (Pi.single j 1) t' = κ' * b' ∧
      (3 : ℤ) • (Pi.single j 1 : V4) =
        (2 * a + b) • s + (a + 2 * b) • t + (2 * a' + b') • s' + (a' + 2 * b') • t' := by
  obtain ⟨ls, hls, rfl⟩ := (mem_rts_iff s).1 hs
  obtain ⟨lt, hlt, rfl⟩ := (mem_rts_iff t).1 ht
  obtain ⟨ls', hls', rfl⟩ := (mem_rts_iff s').1 hs'
  obtain ⟨lt', hlt', rfl⟩ := (mem_rts_iff t').1 ht'
  rw [ipF4_vec4] at hss htt hs's' ht't'
  rw [ipF4_vec4] at hst hss' hts' hs't' hst' htt'
  have hm : ∀ n : ℤ, n = 1 ∨ n = 2 → n ∈ [1, 2] := fun n hn => by simp; omega
  have h := decompP_holds κ (hm _ hκ) κ' (hm _ hκ') ls hls hss lt hlt htt hst ls' hls' hs's' hss'
    hts' lt' hlt' ht't' hs't' hst' htt' j.val (by
      have hj : (j : ℕ) < 4 := j.2
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega)
  obtain ⟨d1, d2, d3, d4, hid⟩ := h
  rw [← e4_vec4 j]
  have hκ0 : κ ≠ 0 := by omega
  have hκ0' : κ' ≠ 0 := by omega
  refine ⟨ipL (e4 j.val) ls / κ, ipL (e4 j.val) lt / κ, ipL (e4 j.val) ls' / κ',
    ipL (e4 j.val) lt' / κ', ?_, ?_, ?_, ?_, ?_⟩
  · rw [ipF4_vec4]; exact (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero d1)).symm
  · rw [ipF4_vec4]; exact (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero d2)).symm
  · rw [ipF4_vec4]; exact (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero d3)).symm
  · rw [ipF4_vec4]; exact (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero d4)).symm
  · funext i
    have hi : i.val ∈ [0, 1, 2, 3] := by
      have hi : (i : ℕ) < 4 := i.2
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have := hid i.val hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simpa [vec4] using this

theorem ipF4_add_left (u u' v : V4) : ipF4 (u + u') v = ipF4 u v + ipF4 u' v := by
  simp only [ipF4, Pi.add_apply]
  ring

theorem ipF4_smul_left (c : ℤ) (u v : V4) : ipF4 (c • u) v = c * ipF4 u v := by
  simp only [ipF4, Pi.smul_apply, smul_eq_mul]
  ring

theorem ipF4_comm (u v : V4) : ipF4 u v = ipF4 v u := by
  simp only [ipF4]
  ring

theorem ipF4_zero_left (v : V4) : ipF4 0 v = 0 := by
  simp [ipF4]

theorem ipF4_add_right (u v v' : V4) : ipF4 u (v + v') = ipF4 u v + ipF4 u v' := by
  simp only [ipF4, Pi.add_apply]
  ring

theorem ipF4_neg_neg (u : V4) : ipF4 (-u) (-u) = ipF4 u u := by
  simp only [ipF4, Pi.neg_apply]
  ring

theorem ipF4_sub_left (u u' v : V4) : ipF4 (u - u') v = ipF4 u v - ipF4 u' v := by
  simp only [ipF4, Pi.sub_apply]
  ring

theorem exists_decomposition {κ κ' : ℤ} (hκ : κ = 1 ∨ κ = 2)
    (hκ' : κ' = 1 ∨ κ' = 2) {s t s' t' : V4} (hs : IsRoot Tag.F4 s) (ht : IsRoot Tag.F4 t)
    (hs' : IsRoot Tag.F4 s') (ht' : IsRoot Tag.F4 t') (hss : ipF4 s s = 2 * κ)
    (htt : ipF4 t t = 2 * κ) (hst : ipF4 s t = -κ) (hs's' : ipF4 s' s' = 2 * κ')
    (hss' : ipF4 s s' = 0) (hts' : ipF4 t s' = 0) (ht't' : ipF4 t' t' = 2 * κ')
    (hs't' : ipF4 s' t' = -κ') (hst' : ipF4 s t' = 0) (htt' : ipF4 t t' = 0) (v : V4) :
    ∃ a b a' b' : ℤ, ipF4 v s = κ * a ∧ ipF4 v t = κ * b ∧ ipF4 v s' = κ' * a' ∧
      ipF4 v t' = κ' * b' ∧
      (3 : ℤ) • v = (2 * a + b) • s + (a + 2 * b) • t + (2 * a' + b') • s' + (a' + 2 * b') • t' := by
  set P : V4 → Prop := fun v => ∃ a b a' b' : ℤ, ipF4 v s = κ * a ∧ ipF4 v t = κ * b ∧
    ipF4 v s' = κ' * a' ∧ ipF4 v t' = κ' * b' ∧
    (3 : ℤ) • v = (2 * a + b) • s + (a + 2 * b) • t + (2 * a' + b') • s' + (a' + 2 * b') • t'
    with hP
  have hzero : P 0 := ⟨0, 0, 0, 0, by simp [ipF4_zero_left], by simp [ipF4_zero_left],
    by simp [ipF4_zero_left], by simp [ipF4_zero_left], by simp⟩
  have hadd : ∀ u w, P u → P w → P (u + w) := by
    rintro u w ⟨a, b, a', b', h1, h2, h3, h4, h5⟩ ⟨c, d, c', d', k1, k2, k3, k4, k5⟩
    refine ⟨a + c, b + d, a' + c', b' + d', ?_, ?_, ?_, ?_, ?_⟩
    · rw [ipF4_add_left, h1, k1]; ring
    · rw [ipF4_add_left, h2, k2]; ring
    · rw [ipF4_add_left, h3, k3]; ring
    · rw [ipF4_add_left, h4, k4]; ring
    · rw [smul_add, h5, k5]
      simp only [add_smul, mul_add, smul_add]
      abel
  have hsmul : ∀ (c : ℤ) u, P u → P (c • u) := by
    rintro c u ⟨a, b, a', b', h1, h2, h3, h4, h5⟩
    refine ⟨c * a, c * b, c * a', c * b', ?_, ?_, ?_, ?_, ?_⟩
    · rw [ipF4_smul_left, h1]; ring
    · rw [ipF4_smul_left, h2]; ring
    · rw [ipF4_smul_left, h3]; ring
    · rw [ipF4_smul_left, h4]; ring
    · rw [smul_comm, h5]
      simp only [smul_add, smul_smul]
      congr 1 <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;> ring_nf
  have hsingle : ∀ j : Fin Tag.F4.rank, P (Pi.single j 1) := fun j =>
    decomposition_single hκ hκ' hs ht hs' ht' hss htt hst hs's' hss' hts' ht't' hs't' hst' htt' j
  have hv : v = ∑ j, v j • (Pi.single j 1 : V4) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact Finset.sum_induction _ P hadd hzero fun j _ => hsmul _ _ (hsingle j)

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

