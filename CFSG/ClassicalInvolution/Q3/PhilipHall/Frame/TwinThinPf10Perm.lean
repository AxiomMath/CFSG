module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Cent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem supportedOn_one (s : Set (Fin n)) : SupportedOn (1 : Wr n) s := fun _ _ => ⟨rfl, rfl⟩

theorem card_off (ι : Fin 4 ↪ Fin n) :
    (Finset.univ.filter fun t : Fin n => t ∉ Set.range ι).card = n - 4 := by
  classical
  have h1 : (Finset.univ.filter fun t : Fin n => t ∈ Set.range ι) = Finset.univ.image ι := by
    ext t; simp
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun t : Fin n => t ∈ Set.range ι)
  rw [h1, Finset.card_image_of_injective _ ι.injective] at h2
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem perm_sq_eq (ι : Fin 4 ↪ Fin n) (hn : n ≤ 6) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ x ∈ Set.range ι, σ x = x) : ∀ x, σ (σ x) = x := by
  classical
  intro x
  by_cases hx : x ∈ Set.range ι
  · rw [hσ x hx, hσ x hx]
  · have hy : σ x ∉ Set.range ι := by
      intro hy
      apply hx
      have := hσ _ hy
      have := σ.injective this
      rw [← this]; exact hy
    by_cases hyx : σ x = x
    · rw [hyx, hyx]
    · let Tf := Finset.univ.filter fun t : Fin n => t ∉ Set.range ι
      have hcard : Tf.card ≤ 2 := by rw [card_off]; omega
      have hsub : ({x, σ x} : Finset (Fin n)) ⊆ Tf := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
      have hpair : ({x, σ x} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hyx)
      have hTf : Tf = {x, σ x} := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      have hz : σ (σ x) ∉ Set.range ι := by
        intro hz
        have := σ.injective (hσ _ hz)
        apply hy
        rw [← this]; exact hz
      have hz' : σ (σ x) ∈ Tf := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      rw [hTf] at hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
      rcases hz' with h | h
      · exact h
      · exfalso
        have := σ.injective h
        exact hyx this

theorem pow_four_eq_one_of_sq (c : Wr n) (hc : ∀ x, c.perm (c.perm x) = x) : c ^ 4 = 1 := by
  have h2 : c * c = ofVec (c * c).vec := by
    refine Wr.ext rfl ?_
    show c.perm * c.perm = 1
    exact Equiv.ext fun x => hc x
  calc c ^ 4 = (c * c) * (c * c) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    _ = 1 := by rw [h2, ofVec_mul_self]

theorem supportedOn_e {ι : Fin 4 ↪ Fin n} {e : Wr n} (he : e = 1 ∨ e = zOf ι) :
    SupportedOn e (Set.range ι) := by
  rcases he with rfl | rfl
  · exact supportedOn_one _
  · exact embed_supportedOn ι zQ

theorem e_sq {ι : Fin 4 ↪ Fin n} {e : Wr n} (he : e = 1 ∨ e = zOf ι) : e * e = 1 := by
  rcases he with rfl | rfl
  · simp
  · exact zOf_mul_self ι

theorem three_pow_mod_four (a : ℕ) : 3 ^ a % 4 = 1 ∨ 3 ^ a % 4 = 3 := by
  induction a with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.mul_mod]; omega

theorem aePerm_of_le_six (hn : 5 ≤ n) (hn6 : n ≤ 6) : TwinThinPf8.AEPerm n := by
  intro α hα w ⟨a, hA⟩ hB
  right
  have hB' : ∀ c : Bool, ∀ x ∈ memBar α hα c, mkQ n w * x * (mkQ n w)⁻¹ = x :=
    fun c x hx => hB α hα c (Or.inr rfl) x hx
  obtain ⟨c, e, hw, he, hc⟩ := exists_split hn (by omega) α hα w hB'
  have hcomm : c * e = e * c := comm_of_disjoint hc (supportedOn_e he) (by
    rw [Set.disjoint_left]; intro x hx hx'; exact hx hx')
  have hcσ : ∀ x ∈ Set.range (emb α hα), c.perm x = x := fun x hx => (hc x (by simpa using hx)).2
  have hc4 := pow_four_eq_one_of_sq c (perm_sq_eq (emb α hα) hn6 c.perm hcσ)
  have he2 := e_sq he
  have hw4 : w ^ 4 = 1 := by
    rw [hw, (show Commute c e from hcomm).mul_pow, hc4, one_mul]
    calc e ^ 4 = (e * e) * (e * e) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      _ = 1 := by rw [he2, one_mul]
  have hw3 : w ^ (3 ^ a) = w ∨ w ^ (3 ^ a) = w⁻¹ := by
    rw [pow_eq_pow_mod _ hw4]
    rcases three_pow_mod_four a with h | h <;> rw [h]
    · left; simp
    · right
      have : w ^ 3 * w = 1 := by rw [← pow_succ]; exact hw4
      exact eq_inv_of_mul_eq_one_left this
  intro x hx
  rcases hw3 with h | h
  · have := hA x hx
    rwa [h] at this
  · have := hA x hx
    rw [h, map_inv, inv_inv] at this
    have h1 : (mkQ n w)⁻¹ * x * mkQ n w = x := by simpa using this
    have h1' : mkQ n w * x = x * mkQ n w := by
      calc mkQ n w * x = mkQ n w * ((mkQ n w)⁻¹ * x * mkQ n w) := by rw [h1]
        _ = x * mkQ n w := by group
    exact mul_inv_eq_iff_eq_mul.mpr h1'

theorem aePerm_seven : TwinThinPf8.AEPerm 7 := fun _ _ _ _ _ => Or.inl rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
