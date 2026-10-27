module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HCharTableTab

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HChar

open CFSG.GH74.QTGen4.Recog.G23.HCharData

noncomputable def cof (v : Fin 20 → ℂ) (n : Fin 20) : ℂ :=
  (576 : ℂ)⁻¹ * ∑ j, (hcSize j : ℂ) * v j * (hcT n j : ℂ)

theorem row_orth_c (m n : Fin 20) :
    ∑ j, (hcSize j : ℂ) * (hcT m j : ℂ) * (hcT n j : ℂ) = if m = n then 576 else 0 := by
  have := row_orth m n
  have h2 : ((∑ j, (hcSize j : ℤ) * hcT m j * hcT n j : ℤ) : ℂ) =
      ((if m = n then 576 else 0 : ℤ) : ℂ) := congrArg _ this
  push_cast at h2
  exact h2

theorem col_orth_c (j j' : Fin 20) :
    (hcSize j : ℂ) * ∑ m, (hcT m j : ℂ) * (hcT m j' : ℂ) = if j = j' then 576 else 0 := by
  have := col_orth j j'
  have h2 : (((hcSize j : ℤ) * ∑ m, hcT m j * hcT m j' : ℤ) : ℂ) =
      ((if j = j' then 576 else 0 : ℤ) : ℂ) := congrArg _ this
  push_cast at h2
  exact h2

theorem cof_ev (d : Fin 20 → ℂ) (n : Fin 20) : cof (fun j => ∑ m, d m * (hcT m j : ℂ)) n = d n := by
  unfold cof
  have h1 : ∑ j, (hcSize j : ℂ) * (∑ m, d m * (hcT m j : ℂ)) * (hcT n j : ℂ) =
      ∑ m, d m * ∑ j, (hcSize j : ℂ) * (hcT m j : ℂ) * (hcT n j : ℂ) := by
    calc _ = ∑ j, ∑ m, d m * ((hcSize j : ℂ) * (hcT m j : ℂ) * (hcT n j : ℂ)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ m, ∑ j, d m * ((hcSize j : ℂ) * (hcT m j : ℂ) * (hcT n j : ℂ)) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
  rw [h1]
  simp only [row_orth_c]
  simp
  field_simp

theorem ev_cof (v : Fin 20 → ℂ) (j : Fin 20) : v j = ∑ n, cof v n * (hcT n j : ℂ) := by
  unfold cof
  have h1 : ∑ n, (576 : ℂ)⁻¹ * (∑ j', (hcSize j' : ℂ) * v j' * (hcT n j' : ℂ)) * (hcT n j : ℂ) =
      ∑ j', ∑ n, (576 : ℂ)⁻¹ * (v j' * ((hcSize j' : ℂ) * ((hcT n j' : ℂ) * (hcT n j : ℂ)))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by ring
  have h2 : ∑ j', ∑ n, (576 : ℂ)⁻¹ * (v j' * ((hcSize j' : ℂ) * ((hcT n j' : ℂ) * (hcT n j : ℂ)))) =
      (576 : ℂ)⁻¹ * ∑ j', v j' * ((hcSize j' : ℂ) * ∑ n, (hcT n j' : ℂ) * (hcT n j : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [h1, h2]
  simp only [col_orth_c]
  simp
  field_simp

theorem eigen (t : Fin 20 → ℂ) (ht0 : t 0 ≠ 0)
    (hR : ∀ (r : Fin 4) (j : Fin 20),
      (∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * t k) * t 0 =
        (hcSize (hcI r) : ℂ) * t (hcI r) * ((hcSize j : ℂ) * t j)) :
    ∃ (m : Fin 20) (c : ℂ), ∀ j, t j = c * (hcT m j : ℂ) := by
  set c : Fin 20 → ℂ := cof t with hc
  have hfour : ∀ j, t j = ∑ n, c n * (hcT n j : ℂ) := ev_cof t
  have hTne : ∀ m, (hcT m 0 : ℂ) ≠ 0 := fun m => by
    exact_mod_cast (deg_pos m).ne'
  have hsne : ∀ j, (hcSize j : ℂ) ≠ 0 := fun j => by
    have : 0 < hcSize j := by revert j; decide
    exact_mod_cast this.ne'
  have hz : ∀ n r, c n * (t 0 * ((hcT n (hcI r) : ℂ) / (hcT n 0 : ℂ)) - t (hcI r)) = 0 := by
    intro n r
    have hv : ∀ j, ∑ m, (c m * (t 0 * ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) - t (hcI r))) *
        (hcT m j : ℂ) = 0 := by
      intro j
      have h1 := hR r j
      have hexp : ∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * t k =
          ∑ m, c m * (∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * (hcT m k : ℂ)) := by
        calc _ = ∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * ∑ m, c m * (hcT m k : ℂ) :=
              Finset.sum_congr rfl fun k _ => by rw [← hfour k]
          _ = ∑ k, ∑ m, c m * ((hcSize k : ℂ) * (hcA r j k : ℂ) * (hcT m k : ℂ)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun m _ => by ring
          _ = ∑ m, ∑ k, c m * ((hcSize k : ℂ) * (hcA r j k : ℂ) * (hcT m k : ℂ)) := Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
      have hU : ∀ m, ∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * (hcT m k : ℂ) =
          (hcSize (hcI r) : ℂ) * (hcSize j : ℂ) * ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) *
            (hcT m j : ℂ) := by
        intro m
        have := eig m r j
        have h2 : (hcT m 0 : ℂ) * ∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * (hcT m k : ℂ) =
            (hcSize (hcI r) : ℂ) * (hcT m (hcI r) : ℂ) * ((hcSize j : ℂ) * (hcT m j : ℂ)) := by
          exact_mod_cast this
        field_simp [hTne m]
        linear_combination h2
      rw [hexp] at h1
      simp only [hU] at h1
      have h3 : (hcSize (hcI r) : ℂ) * (hcSize j : ℂ) *
          (t 0 * ∑ m, c m * ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) * (hcT m j : ℂ)) =
          (hcSize (hcI r) : ℂ) * (hcSize j : ℂ) * (t (hcI r) * ∑ m, c m * (hcT m j : ℂ)) := by
        have e1 : ∑ m, c m * ((hcSize (hcI r) : ℂ) * (hcSize j : ℂ) *
            ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) * (hcT m j : ℂ)) =
            (hcSize (hcI r) : ℂ) * (hcSize j : ℂ) *
              ∑ m, c m * ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) * (hcT m j : ℂ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
        rw [e1] at h1
        rw [← hfour j]
        linear_combination h1
      have h4 := mul_left_cancel₀ (mul_ne_zero (hsne (hcI r)) (hsne j)) h3
      calc ∑ m, (c m * (t 0 * ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) - t (hcI r))) * (hcT m j : ℂ)
          = t 0 * ∑ m, c m * ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) * (hcT m j : ℂ) -
              t (hcI r) * ∑ m, c m * (hcT m j : ℂ) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun m _ => by ring
        _ = 0 := sub_eq_zero.2 h4
    have := cof_ev (fun m => c m * (t 0 * ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) - t (hcI r))) n
    have h0 : (fun j => ∑ m, (c m * (t 0 * ((hcT m (hcI r) : ℂ) / (hcT m 0 : ℂ)) - t (hcI r))) *
        (hcT m j : ℂ)) = fun _ => 0 := funext hv
    rw [h0] at this
    simpa [cof] using this.symm
  have hex : ∃ n₀, c n₀ ≠ 0 := by
    by_contra hall
    have hall' : ∀ n, c n = 0 := fun n => by
      by_contra h
      exact hall ⟨n, h⟩
    apply ht0
    rw [hfour 0]
    exact Finset.sum_eq_zero fun n _ => by rw [hall' n, zero_mul]
  obtain ⟨n₀, hn₀⟩ := hex
  have hkey : ∀ n, c n ≠ 0 → ∀ r, t 0 * ((hcT n (hcI r) : ℂ) / (hcT n 0 : ℂ)) = t (hcI r) := by
    intro n hn r
    have := hz n r
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hn
    · exact sub_eq_zero.1 h
  have hsame : ∀ n, c n ≠ 0 → n = n₀ := by
    intro n hn
    apply sep n n₀
    intro r
    have h1 := hkey n hn r
    have h2 := hkey n₀ hn₀ r
    have h3 : (hcT n (hcI r) : ℂ) / (hcT n 0 : ℂ) = (hcT n₀ (hcI r) : ℂ) / (hcT n₀ 0 : ℂ) :=
      mul_left_cancel₀ ht0 (h1.trans h2.symm)
    rw [div_eq_div_iff (hTne n) (hTne n₀)] at h3
    exact_mod_cast h3
  refine ⟨n₀, c n₀, fun j => ?_⟩
  rw [hfour j]
  rw [Finset.sum_eq_single n₀]
  · intro n _ hn
    by_contra hcn
    exact hn (hsame n (fun h => hcn (by rw [h, zero_mul])))
  · intro h
    exact absurd (Finset.mem_univ _) h

end CFSG.GH74.QTGen4.Recog.G23.P7.HChar
