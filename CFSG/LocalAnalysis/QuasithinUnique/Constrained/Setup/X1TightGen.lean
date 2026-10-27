module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen

public section

namespace CFSG.QuasithinUnique.Setup.X1

variable {S : Type} [Group S] [Finite S] [DecidableEq S] {a m : ℕ} {Rl : List S}

@[expose] def heavyList (Rl El : List S) (n : ℕ) : List S :=
  ((invG Rl).filter fun x => x ∉ El).filter fun x =>
    n ≤ ((invG Rl).filter fun y => y ≠ x ∧ x * y = y * x).length

theorem SylowData.gen2_top (h : SylowData S a m Rl) {k : ℕ} (reps : List (S × S))
    (hcover : ∀ q ∈ pairG (invG Rl), ∃ t ∈ reps, ∃ r ∈ Rl,
      r * q.1 * r⁻¹ = t.1 ∧ r * q.2 * r⁻¹ = t.2)
    (hwit : ∀ t ∈ reps, ∃ cs : List S, cs.length = k ∧
      Subgroup.closure (conjSet cs {t.1, t.2}) = ⊤)
    (B : Subgroup S) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (h3 : 2 < Nat.card B) :
    ∃ cs : List S, cs.length = k ∧ Subgroup.closure (conjSet cs (B : Set S)) = ⊤ := by
  classical
  obtain ⟨g, hg⟩ := h.conj_into B hsq
  obtain ⟨P, hPcard, hP⟩ := card_distinct_nonid_pairs B
  have hPne : P.Nonempty := by
    rw [← Finset.card_pos, hPcard]
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨q, hqP⟩ := hPne
  obtain ⟨h1, h2, h3', h4, h5⟩ := hP q hqP
  have hpair := pair_mem_pairG hg hcomm hsq h1 h2 h3' h4 h5
  obtain ⟨t, ht, r, hr, e1, e2⟩ := hcover _ hpair
  obtain ⟨cs0, hcs0, hcl⟩ := hwit t ht
  refine ⟨cs0.map (· * (r * g)), by simpa using hcs0, ?_⟩
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ Subgroup.closure (conjSet cs0 {t.1, t.2}) := by
    rw [hcl]; exact Subgroup.mem_top z
  have hz' := closure_conjSet_transfer (T := ({q.1, q.2} : Set S)) (r * g)
    (fun t' ht' => by
      have : t' = t.1 ∨ t' = t.2 := by simpa using ht'
      rcases this with rfl | rfl
      · exact ⟨q.1, by simp, by rw [← e1]; group⟩
      · exact ⟨q.2, by simp, by rw [← e2]; group⟩) cs0 hz
  refine Subgroup.closure_mono (conjSet_mono ?_) hz'
  intro u hu
  rcases hu with rfl | rfl
  · exact h1
  · exact h2

omit [Finite S] [DecidableEq S] in
theorem conj_map_mem {B : Subgroup S} {g y : S} :
    y ∈ B.map (MulAut.conj g).toMonoidHom ↔ ∃ x ∈ B, g * x * g⁻¹ = y := by
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem SylowData.unique32 (h : SylowData S a m Rl) (E5 : Subgroup S) (El : List S)
    (hEl : ∀ x, x ∈ E5 ↔ x ∈ El) (hE5 : Nat.card E5 = 32)
    (hheavy : (heavyList Rl El 30).length < 16)
    (B : Subgroup S) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hB : Nat.card B = 32) : ∃ g : S, ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ E5 := by
  classical
  obtain ⟨g, hg⟩ := h.conj_into B hsq
  set B' : Subgroup S := B.map (MulAut.conj g).toMonoidHom with hB'
  have hB'card : Nat.card B' = 32 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj g).injective, hB]
  have hB'R : ∀ y ∈ B', y ∈ Rl := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := conj_map_mem.1 hy
    exact hg x hx
  have hB'sq : ∀ y ∈ B', y * y = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := conj_map_mem.1 hy
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hsq x hx]; group
  have hB'comm : ∀ y ∈ B', ∀ z ∈ B', y * z = z * y := by
    intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := conj_map_mem.1 hy
    obtain ⟨x', hx', rfl⟩ := conj_map_mem.1 hz
    calc g * x * g⁻¹ * (g * x' * g⁻¹) = g * (x * x') * g⁻¹ := by group
      _ = g * (x' * x) * g⁻¹ := by rw [hcomm x hx x' hx']
      _ = _ := by group
  have hEq : B' = E5 := by
    by_contra hne
    have hnle : ¬ B' ≤ E5 := fun hle =>
      hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hB'card, hE5]))
    obtain ⟨y0, hy0B, hy0E⟩ : ∃ y0 ∈ B', y0 ∉ E5 := by
      by_contra hcon
      push Not at hcon
      exact hnle hcon
    have hinf : Nat.card ↥(B' ⊓ E5) ≤ 16 := by
      have hdvd : Nat.card ↥(B' ⊓ E5) ∣ 2 ^ 5 := by
        rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← hB'card]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨j, hj, hjj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hj5 : j ≠ 5 := by
        intro hj5
        have : Nat.card ↥(B' ⊓ E5) = Nat.card B' := by rw [hjj, hj5, hB'card]; norm_num
        have heq : B' ⊓ E5 = B' := Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq this.symm)
        exact hy0E ((inf_eq_left.1 heq : B' ≤ E5) hy0B)
      rw [hjj]
      calc 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 16 := by norm_num
    have hPcard : 16 ≤ ((B' : Set S) \ (E5 : Set S)).ncard := by
      have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (B' : Set S) (E5 : Set S)
        (Set.toFinite _)
      have h2 : ((B' : Set S) ∩ (E5 : Set S)).ncard = Nat.card ↥(B' ⊓ E5) := by
        rw [← Nat.card_coe_set_eq]; rfl
      have h3 : (B' : Set S).ncard = 32 := by rw [← Nat.card_coe_set_eq]; exact hB'card
      omega
    have hsub : (B' : Set S) \ (E5 : Set S) ⊆ ↑(heavyList Rl El 30).toFinset := by
      rintro y ⟨hyB, hyE⟩
      have hyE' : y ∉ El := fun hmem => hyE ((hEl y).2 hmem)
      have hy1 : y ≠ 1 := fun h1 => hyE (h1 ▸ E5.one_mem)
      simp only [heavyList, Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      refine ⟨⟨mem_invG.2 ⟨hB'R y hyB, hy1, hB'sq y hyB⟩, hyE'⟩, ?_⟩
      have hsub2 : ((B' : Set S) \ {1, y}) ⊆
          ↑((invG Rl).filter fun z => z ≠ y ∧ y * z = z * y).toFinset := by
        rintro z ⟨hzB, hz1⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz1
        simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
        exact ⟨mem_invG.2 ⟨hB'R z hzB, hz1.1, hB'sq z hzB⟩, hz1.2, hB'comm y hyB z hzB⟩
      have hc2 : ({1, y} : Set S).ncard = 2 := by
        rw [Set.ncard_pair (Ne.symm hy1)]
      have hsub3 : ({1, y} : Set S) ⊆ (B' : Set S) := by
        intro z hz
        rcases hz with rfl | rfl
        · exact B'.one_mem
        · exact hyB
      have hc30 : ((B' : Set S) \ {1, y}).ncard = 30 := by
        rw [Set.ncard_sdiff hsub3 (Set.toFinite _), hc2]
        have : (B' : Set S).ncard = 32 := by rw [← Nat.card_coe_set_eq]; exact hB'card
        omega
      calc 30 = ((B' : Set S) \ {1, y}).ncard := hc30.symm
        _ ≤ (↑((invG Rl).filter fun z => z ≠ y ∧ y * z = z * y).toFinset : Set S).ncard :=
            Set.ncard_le_ncard hsub2 (Finset.finite_toSet _)
        _ = ((invG Rl).filter fun z => z ≠ y ∧ y * z = z * y).toFinset.card :=
            Set.ncard_coe_finset _
        _ ≤ ((invG Rl).filter fun z => z ≠ y ∧ y * z = z * y).length :=
            List.toFinset_card_le _
    have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at hle
    have hle2 := List.toFinset_card_le (heavyList Rl El 30)
    omega
  refine ⟨g, fun x => ?_⟩
  rw [← hEq, hB']
  constructor
  · intro hx
    exact conj_map_mem.2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨x', hx', hxx'⟩ := conj_map_mem.1 hx
    have : x' = x := by
      have := mul_left_cancel (mul_right_cancel (hxx'.trans rfl : g * x' * g⁻¹ = g * x * g⁻¹))
      exact this
    rw [← this]
    exact hx'

end CFSG.QuasithinUnique.Setup.X1
