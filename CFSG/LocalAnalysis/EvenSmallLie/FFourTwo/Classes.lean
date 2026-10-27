module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Moves
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Native

public noncomputable section

namespace CFSG.EvenSmallLie.FFourTwo.Cover

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

variable {K : Type} [Field K] {M : Type*} [Group M] (C : Cover K M) [Finite M]
  [Group.IsPerfect M]

theorem nf_inj
    {E F : ℕ} (hE : E < 2 ^ 25) (hF : F < 2 ^ 25)
    (h : Pc.nf C.gU E = Pc.nf C.gU F) : E = F :=
  Pc.nf_injective C.pcData C.card_Uhat hE hF h

omit [Finite M] [Group.IsPerfect M] in
theorem nf_mem
    {E : ℕ} (hE : E < 2 ^ 25) : Pc.nf C.gU E ∈ C.Uhat := Pc.nf_mem_gens E hE

theorem exists_nf
    {x : M} (hx : x ∈ C.Uhat) : ∃ E < 2 ^ 25, Pc.nf C.gU E = x :=
  Pc.exists_nf_eq C.pcData x hx

theorem two_pow_lt {i : ℕ} (hi : i < 25) : 2 ^ i < 2 ^ 25 := Nat.pow_lt_pow_right (by omega) hi

theorem commute_gU_high
    {k : ℕ} (hk : 22 ≤ k) (hk' : k < 25) {x : M} (hx : x ∈ C.Uhat) :
    Commute (C.gU k) x := by
  have hgen : ∀ i < 25, C.gU k * C.gU i = C.gU i * C.gU k := by
    intro i hi
    have key : ∀ k', k' < 25 → mulU (2 ^ k') (2 ^ i) = mulU (2 ^ i) (2 ^ k') →
        C.gU k' * C.gU i = C.gU i * C.gU k' := fun k' hk'' h => by
      have := congrArg (Pc.nf C.gU) h
      rwa [(C.nf_mulU (two_pow_lt hk'') (two_pow_lt hi)).1,
        (C.nf_mulU (two_pow_lt hi) (two_pow_lt hk'')).1, Pc.nf_two_pow,
        Pc.nf_two_pow] at this
    rcases (by omega : k = 22 ∨ k = 23 ∨ k = 24) with rfl | rfl | rfl
    · exact key 22 (by omega) (small_spec.2.1 i hi).1
    · exact key 23 (by omega) (small_spec.2.1 i hi).2
    · rw [C.gU_24]; exact (C.z_comm _).symm
  have hle : C.Uhat ≤ Subgroup.centralizer {C.gU k} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hgen i hi).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

omit [Finite M] [Group.IsPerfect M] in
theorem commute_nf_high
    {H : ℕ} (hH : H < 2 ^ 25) (hlow : Pc.LowZero 22 H) {x : M}
    (hx : ∀ k, 22 ≤ k → k < 25 → Commute (C.gU k) x) : Commute (Pc.nf C.gU H) x := by
  rw [Pc.nf_eq_prod C.gU 25 H hH]
  refine Commute.list_prod_left _ _ fun y hy => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_filter, List.mem_range] at hk
  refine hx k ?_ hk.1
  by_contra hlt
  rw [hlow k (by omega)] at hk
  exact absurd hk.2 (by decide)

theorem high_eq {H : ℕ} (hH : H < 2 ^ 25) (hlow : Pc.LowZero 22 H) :
    H = H / 2 ^ 22 * 2 ^ 22 ∧ H / 2 ^ 22 < 8 := by
  have h := (Pc.lowZero_iff_mod 22 H).1 hlow
  have h2 := Nat.div_add_mod H (2 ^ 22)
  refine ⟨by rw [h] at h2; rw [mul_comm]; omega, ?_⟩
  exact (Nat.div_lt_iff_lt_mul (by positivity)).2 (by simpa using hH)

theorem nf_high_mul_self
    {H : ℕ} (hH : H < 2 ^ 25) (hlow : Pc.LowZero 22 H) :
    Pc.nf C.gU H * Pc.nf C.gU H = 1 := by
  obtain ⟨h1, h2⟩ := high_eq hH hlow
  have h3 := small_spec.2.2.1 _ h2
  rw [← h1] at h3
  rw [← (C.nf_mulU hH hH).1, h3, Pc.nf_zero]

omit [Finite M] [Group.IsPerfect M] in
theorem nf_add_high
    {p j : ℕ} (hp : p < 2 ^ 22) :
    Pc.nf C.gU (p + j * 2 ^ 22) = Pc.nf C.gU p * Pc.nf C.gU (j * 2 ^ 22) := by
  have h1 : (p + j * 2 ^ 22) % 2 ^ 22 = p := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  have h2 : ((p + j * 2 ^ 22) >>> 22) <<< 22 = j * 2 ^ 22 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hp, zero_add]
  rw [Pc.nf_mod_high C.gU _ 22, h1, h2]

theorem lowZero_mul_two_pow (j : ℕ) : Pc.LowZero 22 (j * 2 ^ 22) :=
  (Pc.lowZero_iff_mod 22 _).2 (Nat.mul_mod_left _ _)

theorem nf_add_high_sq
    {p j : ℕ} (hp : p < 2 ^ 22) (hj : j < 8) :
    Pc.nf C.gU (p + j * 2 ^ 22) * Pc.nf C.gU (p + j * 2 ^ 22) =
      Pc.nf C.gU p * Pc.nf C.gU p := by
  have hH : j * 2 ^ 22 < 2 ^ 25 := by omega
  have hc := C.commute_nf_high hH (lowZero_mul_two_pow j) fun k hk hk' =>
    C.commute_gU_high hk hk' (C.nf_mem (by omega : p < 2 ^ 25))
  rw [C.nf_add_high hp]
  calc Pc.nf C.gU p * Pc.nf C.gU (j * 2 ^ 22) * (Pc.nf C.gU p * Pc.nf C.gU (j * 2 ^ 22)) =
      Pc.nf C.gU p * Pc.nf C.gU p * (Pc.nf C.gU (j * 2 ^ 22) * Pc.nf C.gU (j * 2 ^ 22)) := by
        rw [mul_assoc, ← mul_assoc (Pc.nf C.gU (j * 2 ^ 22)), hc.eq]; simp only [mul_assoc]
    _ = _ := by rw [C.nf_high_mul_self hH (lowZero_mul_two_pow j), mul_one]

theorem mem_preSq22
    {p : ℕ} (hp : p < 2 ^ 22) {c : ℕ} (hc : c < 8)
    (h : Pc.nf C.gU p * Pc.nf C.gU p = Pc.nf C.gU (c * 2 ^ 22)) :
    p ∈ Pc.preSq cmF 25 22 ∧ mulU p p = c * 2 ^ 22 := by
  have hp' : p < 2 ^ 25 := by omega
  have hm := Pc.mem_preSq C.pcData C.card_Uhat hp' 22
  rw [Nat.mod_eq_of_lt hp, h] at hm
  refine ⟨hm (Pc.nf_mem_lowSub C.pcData (by omega) (lowZero_mul_two_pow c)), ?_⟩
  obtain ⟨m1, m2⟩ := C.nf_mulU hp' hp'
  exact C.nf_inj m2 (by omega) (m1.trans h)

theorem card_sq_aux
    {c : ℕ} (hc : c < 8) (l : List ℕ) (hnd : l.Nodup)
    (hlt : ∀ p ∈ l, p < 2 ^ 22) (hsq : ∀ p ∈ l, mulU p p = c * 2 ^ 22)
    (hall : ∀ p, p ∈ Pc.preSq cmF 25 22 → mulU p p = c * 2 ^ 22 → p ∈ l) :
    Nat.card {u : C.Uhat // (u : M) * u = Pc.nf C.gU (c * 2 ^ 22)} = 8 * l.length := by
  have hval : ∀ (i : Fin l.length) (j : Fin 8),
      Pc.nf C.gU (l[i] + j * 2 ^ 22) * Pc.nf C.gU (l[i] + j * 2 ^ 22) =
        Pc.nf C.gU (c * 2 ^ 22) := fun i j => by
    have h : l[i] < 2 ^ 22 := hlt _ (List.getElem_mem i.2)
    have hs : mulU l[i] l[i] = c * 2 ^ 22 := hsq _ (List.getElem_mem i.2)
    rw [C.nf_add_high_sq h j.2, ← (C.nf_mulU (by omega) (by omega)).1, hs]
  let f : Fin l.length × Fin 8 → {u : C.Uhat // (u : M) * u = Pc.nf C.gU (c * 2 ^ 22)} :=
    fun ij => ⟨⟨Pc.nf C.gU (l[ij.1] + ij.2 * 2 ^ 22),
      C.nf_mem (by
        have : l[ij.1] < 2 ^ 22 := hlt _ (List.getElem_mem ij.1.2)
        have := ij.2.2
        omega)⟩, hval ij.1 ij.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun ⟨i, j⟩ ⟨i', j'⟩ h => ?_, fun ⟨⟨x, hx⟩, hx2⟩ => ?_⟩
    · have h1 : Pc.nf C.gU (l[i] + j * 2 ^ 22) = Pc.nf C.gU (l[i'] + j' * 2 ^ 22) :=
        congrArg (fun u => ((u : C.Uhat) : M)) (congrArg Subtype.val h)
      have hi : l[i] < 2 ^ 22 := hlt _ (List.getElem_mem i.2)
      have hi' : l[i'] < 2 ^ 22 := hlt _ (List.getElem_mem i'.2)
      have hj := j.2
      have hj' := j'.2
      have e := C.nf_inj (by omega) (by omega) h1
      have e1 : l[i] = l[i'] := by omega
      have e2 : (j : ℕ) = j' := by omega
      exact Prod.ext (Fin.ext ((hnd.getElem_inj_iff (i := i.1) (j := i'.1)).1 e1)) (Fin.ext e2)
    · obtain ⟨E, hE, rfl⟩ := C.exists_nf hx
      have hp : E % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (by positivity)
      have hj : E / 2 ^ 22 < 8 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by simpa using hE)
      have hEq : E = E % 2 ^ 22 + E / 2 ^ 22 * 2 ^ 22 := by
        have := Nat.mod_add_div E (2 ^ 22); rw [mul_comm] at this; omega
      have hsq' : Pc.nf C.gU (E % 2 ^ 22) * Pc.nf C.gU (E % 2 ^ 22) =
          Pc.nf C.gU (c * 2 ^ 22) := by
        rw [← C.nf_add_high_sq hp hj, ← hEq]; exact hx2
      obtain ⟨m1, m2⟩ := C.mem_preSq22 hp hc hsq'
      obtain ⟨i, hi, hli⟩ := List.getElem_of_mem (hall _ m1 m2)
      refine ⟨(⟨i, hi⟩, ⟨E / 2 ^ 22, hj⟩), Subtype.ext (Subtype.ext ?_)⟩
      change Pc.nf C.gU (l[i] + E / 2 ^ 22 * 2 ^ 22) = Pc.nf C.gU E
      rw [hli, ← hEq]
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, mul_comm]

theorem card_sq
    {c : ℕ} (hc : c < 8) :
    Nat.card {u : C.Uhat // (u : M) * u = Pc.nf C.gU (c * 2 ^ 22)} = 8 * sqCounts.getD c 0 := by
  rw [← sqCount_spec hc, List.countP_eq_length_filter]
  refine C.card_sq_aux hc _ ((Pc.preSq_spec cmF 25 22).2.filter _) (fun p hp => ?_)
    (fun p hp => ?_) (fun p hp h => ?_)
  · exact (Pc.preSq_spec cmF 25 22).1 _ (Array.mem_toList_iff.1 (List.mem_filter.1 hp).1)
  · simpa using (List.mem_filter.1 hp).2
  · exact List.mem_filter.2 ⟨Array.mem_toList_iff.2 hp, by simpa using h⟩

theorem mul_self_ne_z
    {u : M} (hu : u ∈ C.Uhat) : u * u ≠ C.z := by
  intro h
  have hz : Pc.nf C.gU (4 * 2 ^ 22) = C.z := by
    rw [show 4 * 2 ^ 22 = 2 ^ 24 by norm_num, Pc.nf_two_pow, C.gU_24]
  have h0 := C.card_sq (c := 4) (by norm_num)
  have hne : Nonempty {u : C.Uhat // (u : M) * u = Pc.nf C.gU (4 * 2 ^ 22)} :=
    ⟨⟨⟨u, hu⟩, by rw [hz]; exact h⟩⟩
  have := Nat.card_pos (α := {u : C.Uhat // (u : M) * u = Pc.nf C.gU (4 * 2 ^ 22)})
  rw [h0] at this
  exact absurd this (by decide)

theorem eq_of_mem_center
    {x : M} (hx : x ∈ C.Uhat) (hc : ∀ y ∈ C.Uhat, x * y = y * x) :
    ∃ c < 8, x = Pc.nf C.gU (c * 2 ^ 22) := by
  obtain ⟨E, hE, rfl⟩ := C.exists_nf hx
  have hm := Pc.mem_preCen C.pcData C.card_Uhat hE (fun i hi =>
    commutatorElement_eq_one_iff_mul_comm.2 (hc _ (Pc.g_mem_gens hi))) 25
  rw [Nat.mod_eq_of_lt hE, cen_spec] at hm
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, by norm_num⟩
  · exact ⟨4, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num⟩
  · exact ⟨6, by norm_num, by norm_num⟩
  · exact ⟨1, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num⟩

theorem nf_mul_two_pow_mem_center
    {c : ℕ} (hc : c < 8) {y : M} (hy : y ∈ C.Uhat) :
    Pc.nf C.gU (c * 2 ^ 22) * y = y * Pc.nf C.gU (c * 2 ^ 22) :=
  C.commute_nf_high (by omega) (lowZero_mul_two_pow c) fun _ hk hk' => C.commute_gU_high hk hk' hy

theorem lt_of_mvOK {d x : ℕ} (h : mvOK d x = true) : d < 8 := by
  simp only [mvOK, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h, -⟩ <;> omega

theorem nf_mv
    {d x : ℕ} (hok : mvOK d x = true) (hx : x < 2 ^ 25) :
    ∃ n : M, Pc.nf C.gU (mv d x) = n * Pc.nf C.gU x * n⁻¹ ∧ mv d x < 2 ^ 25 := by
  have hd := lt_of_mvOK hok
  by_cases h4 : d < 4
  · obtain ⟨h1, h2⟩ := C.nf_conjU (by omega : d < 25) hx
    exact ⟨C.gU d, by simp only [mv, h4, ↓reduceIte]; exact h1,
      by simp only [mv, h4, ↓reduceIte]; exact h2⟩
  · have hb : x.testBit (d - 4) = false := by simpa [mvOK, h4, hd] using hok
    obtain ⟨h1, h2⟩ := C.nf_weylU (by omega : d - 4 < 4) hx hb
    exact ⟨_, by simp only [mv, h4, ↓reduceIte]; exact h1,
      by simp only [mv, h4, ↓reduceIte]; exact h2⟩

theorem chain_sound
    : ∀ (l : List ℕ) (x : ℕ), x < 2 ^ 25 → chainOK x l = true →
    ∃ r ∈ r8, IsConj (Pc.nf C.gU x) (Pc.nf C.gU r)
  | [], x, _, h => ⟨x, by simpa [chainOK] using h, IsConj.refl _⟩
  | d :: l, x, hx, h => by
    simp only [chainOK, Bool.and_eq_true] at h
    obtain ⟨n, h1, h2⟩ := C.nf_mv h.1 hx
    obtain ⟨r, hr, hc⟩ := chain_sound l (mv d x) h2 h.2
    exact ⟨r, hr, (isConj_iff.2 ⟨n, h1.symm⟩).trans hc⟩

theorem nf_rMove
    {m x : ℕ} (hm : m ∈ rMoves) (hok : mvOK m x = true) (hx : x < 2 ^ 25) :
    ∃ n : M, Pc.nf C.gU (mv m x) = n * Pc.nf C.gU x * n⁻¹ ∧ mv m x < 2 ^ 25 ∧
      ∀ k, 22 ≤ k → k < 25 → Commute (C.gU k) n := by
  have hW : ∀ a (ha : a < 4), weylU a (2 ^ 22) = 2 ^ 22 → weylU a (2 ^ 23) = 2 ^ 23 →
      ∀ k, 22 ≤ k → k < 25 → Commute (C.gU k) (C.nU a ha) := fun a ha h22 h23 k hk hk' => by
    have key : ∀ k', 22 ≤ k' → k' < 24 → weylU a (2 ^ k') = 2 ^ k' →
        Commute (C.gU k') (C.nU a ha) := fun k' h1 h2 h => by
      have hb : (2 ^ k' : ℕ).testBit a = false := by
        rw [Nat.testBit_two_pow]; simp; omega
      have := (C.nf_weylU ha (two_pow_lt (by omega : k' < 25)) hb).1
      rw [h, Pc.nf_two_pow] at this
      exact eq_mul_inv_iff_mul_eq.1 this
    rcases (by omega : k = 22 ∨ k = 23 ∨ k = 24) with rfl | rfl | rfl
    · exact key 22 le_rfl (by omega) h22
    · exact key 23 (by omega) (by omega) h23
    · rw [C.gU_24]; exact (C.z_comm _).symm
  have hs := small_spec.1
  simp only [rMoves, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := C.nf_conjU (by omega : 0 < 25) hx
    exact ⟨C.gU 0, h1, h2, fun k hk hk' => C.commute_gU_high hk hk' (Pc.g_mem_gens (by omega))⟩
  · obtain ⟨h1, h2⟩ := C.nf_conjU (by omega : 1 < 25) hx
    exact ⟨C.gU 1, h1, h2, fun k hk hk' => C.commute_gU_high hk hk' (Pc.g_mem_gens (by omega))⟩
  · obtain ⟨h1, h2⟩ := C.nf_conjU (by omega : 2 < 25) hx
    exact ⟨C.gU 2, h1, h2, fun k hk hk' => C.commute_gU_high hk hk' (Pc.g_mem_gens (by omega))⟩
  · obtain ⟨h1, h2⟩ := C.nf_conjU (by omega : 3 < 25) hx
    exact ⟨C.gU 3, h1, h2, fun k hk hk' => C.commute_gU_high hk hk' (Pc.g_mem_gens (by omega))⟩
  · have hb : x.testBit 1 = false := by simpa [mvOK] using hok
    obtain ⟨h1, h2⟩ := C.nf_weylU (by omega : 1 < 4) hx hb
    exact ⟨C.nU 1 (by omega), h1, h2, hW 1 (by omega) hs.1 hs.2.1⟩
  · have hb : x.testBit 2 = false := by simpa [mvOK] using hok
    obtain ⟨h1, h2⟩ := C.nf_weylU (by omega : 2 < 4) hx hb
    exact ⟨C.nU 2 (by omega), h1, h2, hW 2 (by omega) hs.2.2.1 hs.2.2.2⟩

theorem or_mod_two_pow {q W k : ℕ} (hq : q < 2 ^ k) (hW : Pc.LowZero k W) :
    (q ||| W) % 2 ^ k = q := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
  by_cases hj : j < k
  · simp [hj, hW j hj]
  · have : q.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hj, this]

theorem compReps_size : compReps.size = 34 := rfl

theorem exists_isConj_r8_of_coset
    : ∀ (d E : ℕ), bfsD (E % 2 ^ 22) = d → E < 2 ^ 25 →
    Pc.nf C.gU E * Pc.nf C.gU E = 1 → E % 2 ^ 22 ≠ 0 →
    ∃ r ∈ r8, IsConj (Pc.nf C.gU E) (Pc.nf C.gU r) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro E hd hE h2 h0
  have hp : E % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (by positivity)
  have hj : E / 2 ^ 22 < 8 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by simpa using hE)
  have hEq : E = E % 2 ^ 22 + E / 2 ^ 22 * 2 ^ 22 := by
    have := Nat.mod_add_div E (2 ^ 22); rw [mul_comm] at this; omega
  have hsq : Pc.nf C.gU (E % 2 ^ 22) * Pc.nf C.gU (E % 2 ^ 22) = Pc.nf C.gU (0 * 2 ^ 22) := by
    rw [← C.nf_add_high_sq hp hj, ← hEq, h2, zero_mul, Pc.nf_zero]
  obtain ⟨m1, m2⟩ := C.mem_preSq22 hp (by norm_num) hsq
  have hpc : E % 2 ^ 22 ∈ invCosets (Pc.preSq cmF 25 22) := by
    rw [invCosets, Array.mem_filter]
    refine ⟨m1, ?_⟩
    rw [zero_mul] at m2
    rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    exact ⟨h0, m2⟩
  rcases bfs_spec hpc with hrep | ⟨m, hm, hok, hq0, hdq⟩
  · obtain ⟨c, hc, hcp⟩ := Array.mem_iff_getElem.1 hrep
    have hc34 : c < 34 := compReps_size ▸ hc
    have hch := chains_spec hc34 hj
    have hg : compReps.getD c 0 = E % 2 ^ 22 := by simp [Array.getD, hc, hcp]
    rw [hg, ← hEq] at hch
    exact C.chain_sound _ _ hE hch
  · set p := E % 2 ^ 22 with hp_def
    obtain ⟨n, h1, h3, h4⟩ := C.nf_rMove hm hok (by omega : p < 2 ^ 25)
    set A := (mv m p >>> 22) <<< 22 with hA_def
    set B := E / 2 ^ 22 * 2 ^ 22 with hB_def
    have hAlow : Pc.LowZero 22 A := fun j hj => by
      rw [hA_def, Nat.testBit_shiftLeft]; simp; omega
    have hAlt : A < 2 ^ 25 := by
      rw [hA_def, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      have := Nat.div_mul_le_self (mv m p) (2 ^ 22)
      omega
    have hBlt : B < 2 ^ 25 := by omega
    obtain ⟨w1, w2⟩ := C.nf_mulU hAlt hBlt
    have hWlow : Pc.LowZero 22 (mulU A B) :=
      Pc.lowZero_mul C.pcData hAlt hBlt hAlow (lowZero_mul_two_pow _)
    set q := mv m p % 2 ^ 22 with hq_def
    have hq : q < 2 ^ 22 := Nat.mod_lt _ (by positivity)
    have hE'lt : q ||| mulU A B < 2 ^ 25 := Nat.or_lt_two_pow (by omega) w2
    have hconj : n * Pc.nf C.gU E * n⁻¹ = Pc.nf C.gU (q ||| mulU A B) := by
      have hB := (C.commute_nf_high hBlt (lowZero_mul_two_pow _) h4).eq
      rw [Pc.nf_or C.gU hWlow q hq, w1, ← mul_assoc, ← Pc.nf_mod_high, hEq, C.nf_add_high hp]
      rw [h1]
      calc n * (Pc.nf C.gU p * Pc.nf C.gU B) * n⁻¹ =
          n * Pc.nf C.gU p * n⁻¹ * (n * Pc.nf C.gU B * n⁻¹) := by group
        _ = n * Pc.nf C.gU p * n⁻¹ * Pc.nf C.gU B := by
          rw [show n * Pc.nf C.gU B * n⁻¹ = Pc.nf C.gU B by rw [← hB]; group]
    have hmod : (q ||| mulU A B) % 2 ^ 22 = q := or_mod_two_pow hq hWlow
    have hsq' : Pc.nf C.gU (q ||| mulU A B) * Pc.nf C.gU (q ||| mulU A B) = 1 := by
      rw [← hconj, show n * Pc.nf C.gU E * n⁻¹ * (n * Pc.nf C.gU E * n⁻¹) =
        n * (Pc.nf C.gU E * Pc.nf C.gU E) * n⁻¹ by group, h2, mul_one, mul_inv_cancel]
    obtain ⟨r, hr, hc⟩ := ih (bfsD q) (by omega) (q ||| mulU A B) (by rw [hmod]) hE'lt hsq'
      (by rw [hmod]; exact hq0)
    exact ⟨r, hr, (isConj_iff.2 ⟨n, hconj⟩).trans hc⟩

theorem exists_isConj_r8
    {x : M} (hx : x ∈ C.Uhat) (h2 : x * x = 1) (h1 : x ≠ 1)
    (hz : x ≠ C.z) : ∃ r ∈ r8, IsConj x (Pc.nf C.gU r) := by
  obtain ⟨E, hE, rfl⟩ := C.exists_nf hx
  by_cases h0 : E % 2 ^ 22 = 0
  · obtain ⟨hEq, hc⟩ := high_eq hE ((Pc.lowZero_iff_mod 22 E).2 h0)
    refine ⟨E, ?_, IsConj.refl _⟩
    have hc0 : E / 2 ^ 22 ≠ 0 := fun h => h1 (by rw [hEq, h, zero_mul, Pc.nf_zero])
    have hc4 : E / 2 ^ 22 ≠ 4 := fun h => hz (by
      rw [hEq, h, show 4 * 2 ^ 22 = 2 ^ 24 by norm_num, Pc.nf_two_pow, C.gU_24])
    rw [hEq]
    generalize E / 2 ^ 22 = c at hc hc0 hc4
    interval_cases c
    all_goals first | exact absurd rfl hc0 | exact absurd rfl hc4 | decide
  · exact C.exists_isConj_r8_of_coset _ E rfl hE h2 h0
