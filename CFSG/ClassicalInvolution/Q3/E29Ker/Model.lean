module

public import Certificates.Certificate272901
public import CFSG.ClassicalInvolution.Q3.AE.E64

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E29Data

theorem mkQ8_eq_iff {x y : Wr 8} : mkQ 8 x = mkQ 8 y ↔ x = y ∨ x = y * allOnes 8 := by
  have hπ : (allOnes 8)⁻¹ = allOnes 8 := inv_eq_of_mul_eq_one_right (allOnes_mul_self 8)
  rw [mkQ_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (inv_mul_eq_one.mp h)
    · right
      calc x = y * (x⁻¹ * y)⁻¹ := by group
        _ = y * allOnes 8 := by rw [h, hπ]
  · rintro (h | h)
    · left
      rw [h]
      group
    · right
      rw [h, mul_inv_rev, hπ, mul_assoc, inv_mul_cancel, mul_one]

theorem eqPi_iff {x y : Wr 8} : eqPi x y = true ↔ mkQ 8 x = mkQ 8 y := by
  rw [mkQ8_eq_iff]
  simp only [eqPi, Bool.or_eq_true, decide_eq_true_eq]

theorem nC_zero : nC 0 = 1 := by
  decide +kernel

theorem nG_even (j : ℕ) : nG (2 * j) = nC j * nA * (nC j)⁻¹ := by
  have h1 : 2 * j / 2 = j := by omega
  have h2 : 2 * j % 2 = 0 := by omega
  simp only [nG, h1, h2, if_true]

theorem nG_odd (j : ℕ) : nG (2 * j + 1) = nC j * nB * (nC j)⁻¹ := by
  have h1 : (2 * j + 1) / 2 = j := by omega
  have h2 : (2 * j + 1) % 2 = 1 := by omega
  simp only [nG, h1, h2, one_ne_zero, if_false]

theorem nG_zero : nG 0 = nA := by
  decide +kernel

theorem nG_one : nG 1 = nB := by
  decide +kernel

theorem model_check :
    e29ConjData.all rowOK29 = true ∧ conjOK29 = true ∧ nodupM0 = true ∧ distinctOK29 = true ∧
      partnerOK29 = true ∧ y3OK29 = true ∧ 1344 ≤ (aglFin ()).card ∧
      (evenFin0 ()).card = 64 := by
  obtain ⟨-, hA, hB, hC, hD, hE, hF, hG, hH⟩ := Certificates.certificate272901
  refine ⟨List.all_eq_true.mpr fun d hd => eqPi_iff.mpr (hA d hd),
    List.all_eq_true.mpr fun j hj => decide_eq_true (hB j (List.mem_range.mp hj)), ?_, ?_, ?_, ?_,
    hG, hH⟩
  · refine List.all_eq_true.mpr fun s hs => List.all_eq_true.mpr fun t ht => ?_
    rw [List.mem_range] at hs ht
    by_cases hst : s = t
    · simp [hst]
    · have hn : eqPi ((n8 0).getD s 1) ((n8 0).getD t 1) = false :=
        Bool.eq_false_iff.mpr fun h => hC s hs t ht hst (eqPi_iff.mp h)
      rw [hn]
      simp [hst]
  · refine List.all_eq_true.mpr fun j hj => List.all_eq_true.mpr fun k hk => ?_
    rw [List.mem_range] at hj hk
    by_cases hjk : j = k
    · simp [hjk]
    · have hn : (n8 k).any (eqPi (nG (2 * j))) = false := by
        refine Bool.eq_false_iff.mpr fun h => ?_
        obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp h
        obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hx
        exact hD j hj k hk hjk W hW (eqPi_iff.mp hxe)
      simp [hjk, hn]
  · refine List.all_eq_true.mpr fun p hp => ?_
    obtain ⟨h1, h2, h3⟩ := hE p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨h1, h2⟩, eqPi_iff.mpr h3⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hF
    simp only [y3OK29, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨h1, h2⟩, fun r hr => eqPi_iff.mpr (h3 r hr)⟩, fun k hk => ?_⟩
    have hn : eqPi (nY3 * nG (2 * k)) (nG (2 * k) * nY3) = false :=
      Bool.eq_false_iff.mpr fun h => h4 k hk (eqPi_iff.mp h)
    simp [hn]

theorem nC_mem {j : ℕ} (hj : j < 28) :
    nC j ∈ aeSubOver agl32 := by
  have h := model_check.2.1
  unfold conjOK29 at h
  rw [List.all_eq_true] at h
  have h1 := h j (List.mem_range.mpr hj)
  rw [decide_eq_true_eq] at h1
  exact ofPerm_mem_aeSubOver h1.1 h1.2

theorem localWords29_lt : ∀ W ∈ localWords29, ∀ l ∈ W, l < 2 := by
  decide +kernel

theorem q8_pow_four : mkQ 8 nA * mkQ 8 nA * mkQ 8 nA * mkQ 8 nA = 1 := by
  have h : eqPi (nA * nA * nA * nA) 1 = true := by decide +kernel
  simpa only [map_mul, map_one] using eqPi_iff.mp h

theorem q8_sq_eq : mkQ 8 nA * mkQ 8 nA = mkQ 8 nB * mkQ 8 nB := by
  have h : eqPi (nA * nA) (nB * nB) = true := by decide +kernel
  simpa only [map_mul] using eqPi_iff.mp h

theorem q8_conj : mkQ 8 nB * mkQ 8 nA * (mkQ 8 nB)⁻¹ * mkQ 8 nA = 1 := by
  have h : eqPi (nB * nA * nB⁻¹ * nA) 1 = true := by decide +kernel
  simpa only [map_mul, map_inv, map_one] using eqPi_iff.mp h

theorem nA_sq_ne_one : mkQ 8 nA * mkQ 8 nA ≠ 1 := by
  intro h
  have h' : eqPi (nA * nA) 1 = true := by
    rw [eqPi_iff]
    simpa only [map_mul, map_one] using h
  exact absurd h' (by decide +kernel)

theorem local_pow_four : ∀ W ∈ localWords29,
    mkQ 8 (nWord 0 W) * mkQ 8 (nWord 0 W) * mkQ 8 (nWord 0 W) * mkQ 8 (nWord 0 W) = 1 := by
  have h : ∀ W ∈ localWords29,
      eqPi (nWord 0 W * nWord 0 W * nWord 0 W * nWord 0 W) 1 = true := by decide +kernel
  intro W hW
  simpa only [map_mul, map_one] using eqPi_iff.mp (h W hW)

theorem local_sq_eq_one : ∀ W ∈ localWords29, mkQ 8 (nWord 0 W) * mkQ 8 (nWord 0 W) = 1 →
    mkQ 8 (nWord 0 W) = 1 ∨ mkQ 8 (nWord 0 W) = mkQ 8 nA * mkQ 8 nA := by
  have h : ∀ W ∈ localWords29, eqPi (nWord 0 W * nWord 0 W) 1 = true →
      eqPi (nWord 0 W) 1 = true ∨ eqPi (nWord 0 W) (nA * nA) = true := by decide +kernel
  intro W hW hsq
  have hsq' : eqPi (nWord 0 W * nWord 0 W) 1 = true := by
    rw [eqPi_iff]
    simpa only [map_mul, map_one] using hsq
  rcases h W hW hsq' with h1 | h1
  · left
    simpa only [map_one] using eqPi_iff.mp h1
  · right
    simpa only [map_mul] using eqPi_iff.mp h1

theorem local_central : ∀ W ∈ localWords29,
    mkQ 8 (nWord 0 W) * (mkQ 8 nA * mkQ 8 nA) = (mkQ 8 nA * mkQ 8 nA) * mkQ 8 (nWord 0 W) := by
  have h : ∀ W ∈ localWords29,
      eqPi (nWord 0 W * (nA * nA)) ((nA * nA) * nWord 0 W) = true := by decide +kernel
  intro W hW
  simpa only [map_mul] using eqPi_iff.mp (h W hW)

theorem conjData_bounds : ∀ d ∈ e29ConjData, d.1 < 56 ∧ d.2.1 < 28 ∧ d.2.2.1 < 2 ∧
    d.2.2.2.1 < 28 ∧ ∀ l ∈ d.2.2.2.2, l < 2 := by
  decide +kernel

private def md_siblings : List (Nat × Nat × Nat × Nat × List Nat) → Bool
  | d0 :: d1 :: rest => d0.1 == d1.1 && d0.2.1 == d1.2.1 && d0.2.2.1 == 0 && d1.2.2.1 == 1 &&
      d0.2.2.2.1 == d1.2.2.2.1 && md_siblings rest
  | [] => true
  | [_] => false

private theorem md_siblings_spec : ∀ l : List (Nat × Nat × Nat × Nat × List Nat),
    md_siblings l = true → ∀ d ∈ l, ∀ t < 2, ∃ d' ∈ l, d'.1 = d.1 ∧ d'.2.1 = d.2.1 ∧
      d'.2.2.1 = t ∧ d'.2.2.2.1 = d.2.2.2.1
  | [], _, d, hd => by simp at hd
  | [_], h, _, _ => by simp [md_siblings] at h
  | d0 :: d1 :: rest, h, d, hd => by
    simp only [md_siblings, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hrest⟩ := h
    intro t ht
    have ht' : t = 0 ∨ t = 1 := by omega
    rcases List.mem_cons.mp hd with rfl | hd'
    · rcases ht' with rfl | rfl
      · exact ⟨d, List.mem_cons_self, rfl, rfl, h3, rfl⟩
      · exact ⟨d1, List.mem_cons_of_mem _ List.mem_cons_self, h1.symm, h2.symm, h4, h5.symm⟩
    · rcases List.mem_cons.mp hd' with rfl | hd''
      · rcases ht' with rfl | rfl
        · exact ⟨d0, List.mem_cons_self, h1, h2, h3, h5⟩
        · exact ⟨d, List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl, h4, rfl⟩
      · obtain ⟨d', hd', e1, e2, e3, e4⟩ := md_siblings_spec rest hrest d hd'' t ht
        exact ⟨d', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd'), e1, e2, e3, e4⟩

theorem conjData_sibling : ∀ d ∈ e29ConjData, ∀ l < 2, ∃ d' ∈ e29ConjData, d'.1 = d.1 ∧
    d'.2.1 = d.2.1 ∧ d'.2.2.1 = l ∧ d'.2.2.2.1 = d.2.2.2.1 := fun d hd l hl =>
  md_siblings_spec e29ConjData (by decide +kernel) d hd l hl

theorem row_eq {d : Nat × Nat × Nat × Nat × List Nat}
    (hd : d ∈ e29ConjData) :
    mkQ 8 (nG d.1) * mkQ 8 (nG (2 * d.2.1 + d.2.2.1)) * (mkQ 8 (nG d.1))⁻¹ =
      mkQ 8 (nWord d.2.2.2.1 d.2.2.2.2) := by
  have h := model_check.1
  rw [List.all_eq_true] at h
  have h1 := h d hd
  unfold rowOK29 at h1
  simpa only [map_mul, map_inv] using eqPi_iff.mp h1

theorem distinct_ne {j k : ℕ} (hj : j < 28) (hk : k < 28)
    (hne : j ≠ k) : ∀ W ∈ localWords29, mkQ 8 (nG (2 * j)) ≠ mkQ 8 (nWord k W) := by
  intro W hW heq
  have h := model_check.2.2.2.1
  unfold distinctOK29 at h
  rw [List.all_eq_true] at h
  have h1 := h j (List.mem_range.mpr hj)
  rw [List.all_eq_true] at h1
  have h2 := h1 k (List.mem_range.mpr hk)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exact hne h2
  · have h3 : (n8 k).any (eqPi (nG (2 * j))) = true := by
      rw [List.any_eq_true]
      exact ⟨nWord k W, List.mem_map_of_mem hW, eqPi_iff.mpr heq⟩
    rw [h3] at h2
    exact Bool.noConfusion h2

theorem partner_facts : ∀ p ∈ e29Partners,
    p < 28 ∧ p ≠ 0 ∧ mkQ 8 (nG (2 * p)) * mkQ 8 (nG (2 * p)) = mkQ 8 nA * mkQ 8 nA := by
  have h := model_check.2.2.2.2.1
  unfold partnerOK29 at h
  rw [List.all_eq_true] at h
  intro p hp
  have h1 := h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
  obtain ⟨⟨h2, h3⟩, h4⟩ := h1
  exact ⟨h2, h3, by simpa only [map_mul] using eqPi_iff.mp h4⟩

theorem y3Rows_bounds : ∀ r ∈ e29Y3Rows, r.1 < 28 ∧ r.2.1 < 2 ∧ ∀ l ∈ r.2.2, l < 2 := by
  decide +kernel

theorem y3Rows_complete : ∀ k ∈ 0 :: e29Partners, ∀ t < 2,
    ∃ r ∈ e29Y3Rows, r.1 = k ∧ r.2.1 = t := by
  decide +kernel

theorem y3_facts :
    nY3 * nY3 * nY3 = 1 ∧ nY3 ∈ aeSubOver agl32 ∧
      (∀ r ∈ e29Y3Rows, mkQ 8 nY3 * mkQ 8 (nG (2 * r.1 + r.2.1)) * (mkQ 8 nY3)⁻¹ =
        mkQ 8 (nWord r.1 r.2.2)) ∧
      ∀ k ∈ 0 :: e29Partners,
        mkQ 8 nY3 * mkQ 8 (nG (2 * k)) ≠ mkQ 8 (nG (2 * k)) * mkQ 8 nY3 := by
  have h := model_check.2.2.2.2.2.1
  simp only [y3OK29, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, ofPerm_mem_aeSubOver h2.1 h2.2, ?_, ?_⟩
  · intro r hr
    simpa only [map_mul, map_inv] using eqPi_iff.mp (h3 r hr)
  · intro k hk heq
    have h5 : eqPi (nY3 * nG (2 * k)) (nG (2 * k) * nY3) = true := by
      rw [eqPi_iff]
      simpa only [map_mul] using heq
    have h6 := h4 k hk
    rw [h5] at h6
    exact Bool.noConfusion h6

end CFSG.ClassicalInvolution.Q3.E29Ker
