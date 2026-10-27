module

public import CFSG.Certificates.Kernel.OrbRow.Tight

public section

namespace CFSG.KC.OrbRow

open Subgroup

variable {α : Type*} [DecidableEq α]

theorem tight_orbit (b : ℕ → α) (G : ℕ → Subgroup (Equiv.Perm α)) (k : ℕ → ℕ)
    (t : ℕ → ℕ → Equiv.Perm α) {i : ℕ} (ht : ∀ j < k i, t i j ∈ G i)
    (hpts : ∀ j < k i, ∀ j' < k i, t i j (b i) = t i j' (b i) → j = j') :
    ∃ s : Finset α, s.card = k i ∧ ∀ x ∈ s, ∃ g ∈ G i, g (b i) = x := by
  refine ⟨(Finset.range (k i)).image (fun j => t i j (b i)), ?_, fun x hx => ?_⟩
  · rw [Finset.card_image_of_injOn (fun j hj j' hj' he => hpts j (Finset.mem_range.mp hj) j'
      (Finset.mem_range.mp hj') he), Finset.card_range]
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨t i j, ht j (Finset.mem_range.mp hj), rfl⟩

theorem tight_factor (P : Subgroup (Equiv.Perm α)) [Finite P] (b : ℕ → α) (L : ℕ)
    (G : ℕ → Subgroup (Equiv.Perm α)) (k : ℕ → ℕ) (hGP : ∀ i ≤ L, G i ≤ P)
    (hfix : ∀ i ≤ L, ∀ g ∈ G i, ∀ t < i, g (b t) = b t) (hdec : ∀ i < L, G (i + 1) ≤ G i)
    (t : ℕ → ℕ → Equiv.Perm α) (ht : ∀ i < L, ∀ j < k i, t i j ∈ G i)
    (hpts : ∀ i < L, ∀ j < k i, ∀ j' < k i, t i j (b i) = t i j' (b i) → j = j')
    (hprod : Nat.card P = ∏ s ∈ Finset.range L, k s) :
    ∀ g ∈ P, ∃ f : ℕ → ℕ, (∀ i < L, f i < k i) ∧
      g = ((List.range L).map (fun i => t i (f i))).prod := by
  have hT := tight_chain P b L G k hGP hfix hdec
    (fun i hi => tight_orbit b G k t (ht i hi) (hpts i hi)) hprod
  have hfinG : ∀ i ≤ L, Finite (G i) := fun i hi =>
    Finite.of_injective (fun g : G i => (⟨g.1, hGP i hi g.2⟩ : P)) fun g h he => by
      apply Subtype.ext
      simpa using congrArg Subtype.val he
  have key : ∀ d i, i + d = L → ∀ g ∈ G i, ∃ f : ℕ → ℕ, (∀ s, i ≤ s → s < L → f s < k s) ∧
      g = ((List.range' i d).map (fun s => t s (f s))).prod := by
    intro d
    induction d with
    | zero =>
      intro i hi g hg
      rw [Nat.add_zero] at hi
      subst hi
      have hc := (hT i le_rfl).2
      rw [Finset.Ico_self, Finset.prod_empty] at hc
      have : g = 1 := by
        have h1 := (Nat.card_eq_one_iff_exists (α := G i)).mp hc
        obtain ⟨x, hx⟩ := h1
        have e1 := hx ⟨g, hg⟩
        have e2 := hx ⟨1, (G i).one_mem⟩
        have := congrArg Subtype.val (e1.trans e2.symm)
        simpa using this
      exact ⟨fun _ => 0, fun s hs hs' => absurd hs' (by omega), by simp [this]⟩
    | succ d ih =>
      intro i hi g hg
      have hiL : i < L := by omega
      have hfi := hfinG i hiL.le
      have hfi1 := hfinG (i + 1) (by omega)
      have hex : ∃ j < k i, t i j (b i) = g (b i) := by
        by_contra hne0
        have hne : ∀ j < k i, t i j (b i) ≠ g (b i) := fun j hj he => hne0 ⟨j, hj, he⟩
        let s : Finset α := insert (g (b i)) ((Finset.range (k i)).image (fun j => t i j (b i)))
        have hs : s.card = k i + 1 := by
          rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn (fun j hj j' hj' he =>
            hpts i hiL j (Finset.mem_range.mp hj) j' (Finset.mem_range.mp hj') he),
            Finset.card_range]
          intro hm
          obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hm
          exact hne j (Finset.mem_range.mp hj) he
        have hc := card_ge_of_orbit (G i) (b i) s (fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ⟨g, hg, rfl⟩
            · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
              exact ⟨t i j, ht i hiL j (Finset.mem_range.mp hj), rfl⟩)
          (G (i + 1)) (fun g' hg' => ⟨hdec i hiL hg', hfix (i + 1) (by omega) g' hg' i
            (Nat.lt_succ_self i)⟩)
        rw [hs, (hT i hiL.le).2, (hT (i + 1) (by omega)).2,
          Finset.prod_eq_prod_Ico_succ_bot hiL] at hc
        have hpos : 0 < ∏ s ∈ Finset.Ico (i + 1) L, k s := by
          rw [← (hT (i + 1) (by omega)).2]
          exact Nat.card_pos
        exact absurd hc (Nat.not_le.mpr (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hpos))
      obtain ⟨j, hj, hjg⟩ := hex
      have hh : (t i j)⁻¹ * g ∈ G (i + 1) := by
        rw [(hT (i + 1) (by omega)).1]
        have hgS : (t i j)⁻¹ * g ∈ stabB P b i := by
          rw [← (hT i hiL.le).1]
          exact (G i).mul_mem ((G i).inv_mem (ht i hiL j hj)) hg
        refine ⟨hgS.1, fun s hs => ?_⟩
        rcases Nat.lt_or_ge s i with hsi | hsi
        · exact hgS.2 s hsi
        · have : s = i := by omega
          subst this
          rw [Equiv.Perm.mul_apply, ← hjg]
          exact (t s j).symm_apply_apply (b s)
      obtain ⟨f, hf, hfe⟩ := ih (i + 1) (by omega) _ hh
      refine ⟨fun s => if s = i then j else f s, fun s hs hs' => ?_, ?_⟩
      · by_cases hsi : s = i
        · simp only [hsi, if_true]
          exact hj
        · simp only [hsi, if_false]
          exact hf s (by omega) hs'
      · simp only [List.range'_succ, List.map_cons, List.prod_cons, if_true]
        have hmap : (List.range' (i + 1) d).map (fun s => t s (if s = i then j else f s)) =
            (List.range' (i + 1) d).map (fun s => t s (f s)) := by
          refine List.map_congr_left (fun s hs => ?_)
          have : i + 1 ≤ s := (List.mem_range'_1.mp hs).1
          rw [if_neg (by omega)]
        rw [hmap, ← hfe, mul_inv_cancel_left]
  intro g hg
  have hg0 : g ∈ G 0 := by
    rw [(hT 0 (Nat.zero_le _)).1]
    exact ⟨hg, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
  obtain ⟨f, hf, hfe⟩ := key L 0 (by omega) g hg0
  exact ⟨f, fun i hi => hf i (Nat.zero_le _) hi, by rw [hfe, List.range_eq_range']⟩

end CFSG.KC.OrbRow

end
