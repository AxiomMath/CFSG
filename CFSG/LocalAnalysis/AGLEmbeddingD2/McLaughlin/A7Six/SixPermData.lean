module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.PermData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.PermTools

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open Equiv Equiv.Perm PermTools

@[expose] def gD : List (Perm (Fin 7)) := [swap 0 1 * swap 1 2 * swap 2 3, swap 0 2, swap 4 5]

@[expose] def gE : List (Perm (Fin 7)) := [swap 0 2, swap 1 3, swap 4 5]

@[expose] def gP : Fin 3 → List (Perm (Fin 7))
  | 0 => [swap 0 2 * swap 2 6, swap 0 2, swap 1 3, swap 4 5]
  | 1 => [swap 1 3 * swap 3 6, swap 0 2, swap 1 3, swap 4 5]
  | 2 => [swap 4 5 * swap 5 6, swap 0 2, swap 1 3, swap 4 5]

@[expose] def gN : List (Perm (Fin 7)) :=
  [swap 0 2, swap 1 3, swap 4 5, swap 0 1 * swap 2 3, swap 0 4 * swap 2 5]

@[expose] def sixD : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gD}

@[expose] def sixE : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gE}

@[expose] def sixP (i : Fin 3) : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gP i}

@[expose] def sixN : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gN}

theorem hgD : gD.map enc = [1753297, 1754634, 1726088] := by decide +kernel
theorem hgE : gE.map enc = [1754634, 1753752, 1726088] := by decide +kernel
theorem hgP0 : (gP 0).map enc = [182154, 1754634, 1753752, 1726088] := by decide +kernel
theorem hgP1 : (gP 1).map enc = [445592, 1754634, 1753752, 1726088] := by decide +kernel
theorem hgP2 : (gP 2).map enc = [1267336, 1754634, 1753752, 1726088] := by decide +kernel
theorem hgN : gN.map enc = [1754634, 1753752, 1726088, 1754305, 1640268] := by decide +kernel

theorem hclD : ∀ a ∈ closeC [1753297, 1754634, 1726088] 6, ∀ g ∈ [1753297, 1754634, 1726088],
    mulC a g ∈ closeC [1753297, 1754634, 1726088] 6 := by decide +kernel
theorem hclE : ∀ a ∈ closeC [1754634, 1753752, 1726088] 6, ∀ g ∈ [1754634, 1753752, 1726088],
    mulC a g ∈ closeC [1754634, 1753752, 1726088] 6 := by decide +kernel
theorem hclP0 : ∀ a ∈ closeC [182154, 1754634, 1753752, 1726088] 6,
    ∀ g ∈ [182154, 1754634, 1753752, 1726088],
      mulC a g ∈ closeC [182154, 1754634, 1753752, 1726088] 6 := by decide +kernel
theorem hclP1 : ∀ a ∈ closeC [445592, 1754634, 1753752, 1726088] 6,
    ∀ g ∈ [445592, 1754634, 1753752, 1726088],
      mulC a g ∈ closeC [445592, 1754634, 1753752, 1726088] 6 := by decide +kernel
theorem hclP2 : ∀ a ∈ closeC [1267336, 1754634, 1753752, 1726088] 6,
    ∀ g ∈ [1267336, 1754634, 1753752, 1726088],
      mulC a g ∈ closeC [1267336, 1754634, 1753752, 1726088] 6 := by decide +kernel
theorem hclN : ∀ a ∈ closeC [1754634, 1753752, 1726088, 1754305, 1640268] 6,
    ∀ g ∈ [1754634, 1753752, 1726088, 1754305, 1640268],
      mulC a g ∈ closeC [1754634, 1753752, 1726088, 1754305, 1640268] 6 := by decide +kernel

theorem mem_sixD (x : Perm (Fin 7)) :
    x ∈ sixD ↔ enc x ∈ closeC [1753297, 1754634, 1726088] 6 :=
  mem_closure_iff_closeC gD (fun _ => Iff.rfl) _ hgD 6 hclD x

theorem mem_sixE (x : Perm (Fin 7)) :
    x ∈ sixE ↔ enc x ∈ closeC [1754634, 1753752, 1726088] 6 :=
  mem_closure_iff_closeC gE (fun _ => Iff.rfl) _ hgE 6 hclE x

theorem mem_sixP0 (x : Perm (Fin 7)) :
    x ∈ sixP 0 ↔ enc x ∈ closeC [182154, 1754634, 1753752, 1726088] 6 :=
  mem_closure_iff_closeC (gP 0) (fun _ => Iff.rfl) _ hgP0 6 hclP0 x

theorem mem_sixP1 (x : Perm (Fin 7)) :
    x ∈ sixP 1 ↔ enc x ∈ closeC [445592, 1754634, 1753752, 1726088] 6 :=
  mem_closure_iff_closeC (gP 1) (fun _ => Iff.rfl) _ hgP1 6 hclP1 x

theorem mem_sixP2 (x : Perm (Fin 7)) :
    x ∈ sixP 2 ↔ enc x ∈ closeC [1267336, 1754634, 1753752, 1726088] 6 :=
  mem_closure_iff_closeC (gP 2) (fun _ => Iff.rfl) _ hgP2 6 hclP2 x

theorem mem_sixN (x : Perm (Fin 7)) :
    x ∈ sixN ↔ enc x ∈ closeC [1754634, 1753752, 1726088, 1754305, 1640268] 6 :=
  mem_closure_iff_closeC gN (fun _ => Iff.rfl) _ hgN 6 hclN x

theorem card_sixD : Nat.card sixD = 16 :=
  (card_closure_closeC gD (S := {σ | σ ∈ gD}) (fun _ => Iff.rfl) _ hgD 6 hclD).trans
    (by decide +kernel)

theorem card_sixE : Nat.card sixE = 8 :=
  (card_closure_closeC gE (S := {σ | σ ∈ gE}) (fun _ => Iff.rfl) _ hgE 6 hclE).trans
    (by decide +kernel)

theorem card_sixP : ∀ i, Nat.card (sixP i) = 24
  | 0 => (card_closure_closeC (gP 0) (S := {σ | σ ∈ gP 0}) (fun _ => Iff.rfl) _ hgP0 6
      hclP0).trans (by decide +kernel)
  | 1 => (card_closure_closeC (gP 1) (S := {σ | σ ∈ gP 1}) (fun _ => Iff.rfl) _ hgP1 6
      hclP1).trans (by decide +kernel)
  | 2 => (card_closure_closeC (gP 2) (S := {σ | σ ∈ gP 2}) (fun _ => Iff.rfl) _ hgP2 6
      hclP2).trans (by decide +kernel)

theorem card_sixN : Nat.card sixN = 48 :=
  (card_closure_closeC gN (S := {σ | σ ∈ gN}) (fun _ => Iff.rfl) _ hgN 6 hclN).trans
    (by decide +kernel)

theorem sixE_le_sixD : sixE ≤ sixD := (Subgroup.closure_le _).2 fun g hg => by
  have h : enc g ∈ gE.map enc := List.mem_map_of_mem hg
  rw [hgE] at h
  have key : ∀ c ∈ [1754634, 1753752, 1726088], c ∈ closeC [1753297, 1754634, 1726088] 6 := by
    decide +kernel
  exact (mem_sixD g).2 (key _ h)

theorem sixE_le_sixP : ∀ i, sixE ≤ sixP i
  | 0 => (Subgroup.closure_le _).2 fun g hg => by
    have h : enc g ∈ gE.map enc := List.mem_map_of_mem hg
    rw [hgE] at h
    have key : ∀ c ∈ [1754634, 1753752, 1726088],
        c ∈ closeC [182154, 1754634, 1753752, 1726088] 6 := by decide +kernel
    exact (mem_sixP0 g).2 (key _ h)
  | 1 => (Subgroup.closure_le _).2 fun g hg => by
    have h : enc g ∈ gE.map enc := List.mem_map_of_mem hg
    rw [hgE] at h
    have key : ∀ c ∈ [1754634, 1753752, 1726088],
        c ∈ closeC [445592, 1754634, 1753752, 1726088] 6 := by decide +kernel
    exact (mem_sixP1 g).2 (key _ h)
  | 2 => (Subgroup.closure_le _).2 fun g hg => by
    have h : enc g ∈ gE.map enc := List.mem_map_of_mem hg
    rw [hgE] at h
    have key : ∀ c ∈ [1754634, 1753752, 1726088],
        c ∈ closeC [1267336, 1754634, 1753752, 1726088] 6 := by decide +kernel
    exact (mem_sixP2 g).2 (key _ h)

theorem sixD_le_sixN : sixD ≤ sixN := (Subgroup.closure_le _).2 fun g hg => by
  have h : enc g ∈ gD.map enc := List.mem_map_of_mem hg
  rw [hgD] at h
  have key : ∀ c ∈ [1753297, 1754634, 1726088],
      c ∈ closeC [1754634, 1753752, 1726088, 1754305, 1640268] 6 := by decide +kernel
  exact (mem_sixN g).2 (key _ h)

theorem swap_mem_sixE : swap 0 2 ∈ sixE := Subgroup.subset_closure (by simp [gE])

theorem sixD_fix : ∀ σ ∈ sixD, σ 6 = 6 := by
  intro σ hσ
  have key : ∀ c ∈ closeC [1753297, 1754634, 1726088] 6, dig c 6 = 6 := by decide +kernel
  have h := key _ ((mem_sixD σ).1 hσ)
  rw [dig_enc σ 6 (by norm_num)] at h
  exact Fin.ext h

theorem mem_pair_of_dig {σ : Perm (Fin 7)} {k : ℕ} (hk : k < 7) {a b : Fin 7}
    (h : dig (enc σ) k = a ∨ dig (enc σ) k = b) : σ ⟨k, hk⟩ ∈ ({a, b} : Finset (Fin 7)) := by
  rw [dig_enc σ k hk] at h
  rcases h with h | h
  · exact Finset.mem_insert.2 (Or.inl (Fin.ext h))
  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (Fin.ext h)))

theorem dig_of_mem_pair {σ : Perm (Fin 7)} {k : ℕ} (hk : k < 7) {a b : Fin 7}
    (h : σ ⟨k, hk⟩ ∈ ({a, b} : Finset (Fin 7))) : dig (enc σ) k = a ∨ dig (enc σ) k = b := by
  rw [dig_enc σ k hk]
  rcases Finset.mem_insert.1 h with h | h
  · exact Or.inl (congrArg Fin.val h)
  · exact Or.inr (congrArg Fin.val (Finset.mem_singleton.1 h))

theorem sixE_pairs : ∀ σ ∈ sixE, σ 0 ∈ ({0, 2} : Finset (Fin 7)) ∧ σ 2 ∈ ({0, 2} : Finset (Fin 7)) ∧
    σ 1 ∈ ({1, 3} : Finset (Fin 7)) ∧ σ 3 ∈ ({1, 3} : Finset (Fin 7)) ∧
    σ 4 ∈ ({4, 5} : Finset (Fin 7)) ∧ σ 5 ∈ ({4, 5} : Finset (Fin 7)) := by
  intro σ hσ
  have key : ∀ c ∈ closeC [1754634, 1753752, 1726088] 6,
      (dig c 0 = 0 ∨ dig c 0 = 2) ∧ (dig c 2 = 0 ∨ dig c 2 = 2) ∧ (dig c 1 = 1 ∨ dig c 1 = 3) ∧
        (dig c 3 = 1 ∨ dig c 3 = 3) ∧ (dig c 4 = 4 ∨ dig c 4 = 5) ∧ (dig c 5 = 4 ∨ dig c 5 = 5) := by
    decide +kernel
  obtain ⟨h0, h2, h1, h3, h4, h5⟩ := key _ ((mem_sixE σ).1 hσ)
  exact ⟨mem_pair_of_dig (k := 0) (by norm_num) (a := 0) (b := 2) h0,
    mem_pair_of_dig (k := 2) (by norm_num) (a := 0) (b := 2) h2,
    mem_pair_of_dig (k := 1) (by norm_num) (a := 1) (b := 3) h1,
    mem_pair_of_dig (k := 3) (by norm_num) (a := 1) (b := 3) h3,
    mem_pair_of_dig (k := 4) (by norm_num) (a := 4) (b := 5) h4,
    mem_pair_of_dig (k := 5) (by norm_num) (a := 4) (b := 5) h5⟩

theorem sixD_stab : ∀ σ ∈ sixD, σ 0 ∈ ({0, 2} : Finset (Fin 7)) → σ 2 ∈ ({0, 2} : Finset (Fin 7)) →
    σ 1 ∈ ({1, 3} : Finset (Fin 7)) → σ 3 ∈ ({1, 3} : Finset (Fin 7)) →
    σ 4 ∈ ({4, 5} : Finset (Fin 7)) → σ 5 ∈ ({4, 5} : Finset (Fin 7)) → σ ∈ sixE := by
  intro σ hσ h0 h2 h1 h3 h4 h5
  have key : ∀ c ∈ closeC [1753297, 1754634, 1726088] 6,
      ((dig c 0 = 0 ∨ dig c 0 = 2) ∧ (dig c 2 = 0 ∨ dig c 2 = 2) ∧ (dig c 1 = 1 ∨ dig c 1 = 3) ∧
        (dig c 3 = 1 ∨ dig c 3 = 3) ∧ (dig c 4 = 4 ∨ dig c 4 = 5) ∧ (dig c 5 = 4 ∨ dig c 5 = 5)) →
          c ∈ closeC [1754634, 1753752, 1726088] 6 := by
    decide +kernel
  exact (mem_sixE σ).2 (key _ ((mem_sixD σ).1 hσ)
    ⟨dig_of_mem_pair (k := 0) (by norm_num) h0, dig_of_mem_pair (k := 2) (by norm_num) h2,
      dig_of_mem_pair (k := 1) (by norm_num) h1, dig_of_mem_pair (k := 3) (by norm_num) h3,
      dig_of_mem_pair (k := 4) (by norm_num) h4, dig_of_mem_pair (k := 5) (by norm_num) h5⟩)

theorem sixD_trans : ∀ σ ∈ sixD, σ * σ = 1 → (∀ i, σ i ≠ i → swap i (σ i) ∈ sixD) → σ ∈ sixE := by
  intro σ hσ hsq htr
  have key : ∀ c ∈ closeC [1753297, 1754634, 1726088] 6, mulC c c = idC →
      (∀ i < 7, dig c i ≠ i → swapC i (dig c i) ∈ closeC [1753297, 1754634, 1726088] 6) →
        c ∈ closeC [1754634, 1753752, 1726088] 6 := by
    decide +kernel
  refine (mem_sixE σ).2 (key _ ((mem_sixD σ).1 hσ) ?_ ?_)
  · rw [← enc_mul, hsq, enc_one]
  · intro i hi hne
    rw [dig_enc σ i hi] at hne ⊢
    have h := htr ⟨i, hi⟩ fun heq => hne (congrArg Fin.val heq)
    rw [mem_sixD, enc_swap] at h
    exact h

theorem swap_mul_swap_mem_alternatingGroup {a b c d : Fin 7} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup, sign_mul, sign_swap hab, sign_swap hcd]
  exact Int.units_mul_self _

theorem sixP_notNormal : ∀ i, ∃ g ∈ sixP i ⊓ alternatingGroup (Fin 7), ∃ e ∈ sixE,
    g * e * g⁻¹ ∉ sixE
  | 0 => ⟨swap 2 6 * swap 4 5,
      Subgroup.mem_inf.2 ⟨(mem_sixP0 _).2 (by decide +kernel),
        swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩,
      swap 0 2, swap_mem_sixE, by rw [mem_sixE]; decide +kernel⟩
  | 1 => ⟨swap 3 6 * swap 4 5,
      Subgroup.mem_inf.2 ⟨(mem_sixP1 _).2 (by decide +kernel),
        swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩,
      swap 1 3, Subgroup.subset_closure (by simp [gE]), by rw [mem_sixE]; decide +kernel⟩
  | 2 => ⟨swap 4 5 * swap 5 6,
      Subgroup.mem_inf.2 ⟨(mem_sixP2 _).2 (by decide +kernel),
        swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩,
      swap 4 5, Subgroup.subset_closure (by simp [gE]), by rw [mem_sixE]; decide +kernel⟩

theorem sixN_notNormal : ∃ g ∈ sixN ⊓ alternatingGroup (Fin 7), ∃ d ∈ sixD,
    g * d * g⁻¹ ∉ sixD :=
  ⟨swap 0 4 * swap 2 5,
    Subgroup.mem_inf.2 ⟨Subgroup.subset_closure (by simp [gN]),
      swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩,
    swap 0 1 * swap 1 2 * swap 2 3, Subgroup.subset_closure (by simp [gD]),
    by rw [mem_sixD]; decide +kernel⟩

@[expose] def cyc : Fin 3 → Perm (Fin 7)
  | 0 => swap 0 2 * swap 2 6
  | 1 => swap 1 3 * swap 3 6
  | 2 => swap 4 5 * swap 5 6

theorem isThreeCycle_cyc : ∀ i, IsThreeCycle (cyc i)
  | 0 => by
    show IsThreeCycle (swap 0 2 * swap 2 6)
    rw [swap_comm 0 2]; exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  | 1 => by
    show IsThreeCycle (swap 1 3 * swap 3 6)
    rw [swap_comm 1 3]; exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  | 2 => by
    show IsThreeCycle (swap 4 5 * swap 5 6)
    rw [swap_comm 4 5]; exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem cyc_mem : ∀ i, cyc i ∈ sixP i ⊓ alternatingGroup (Fin 7)
  | 0 => Subgroup.mem_inf.2 ⟨Subgroup.subset_closure (by simp [gP, cyc]),
      (isThreeCycle_cyc 0).mem_alternatingGroup⟩
  | 1 => Subgroup.mem_inf.2 ⟨Subgroup.subset_closure (by simp [gP, cyc]),
      (isThreeCycle_cyc 1).mem_alternatingGroup⟩
  | 2 => Subgroup.mem_inf.2 ⟨Subgroup.subset_closure (by simp [gP, cyc]),
      (isThreeCycle_cyc 2).mem_alternatingGroup⟩

theorem sixGen_P : alternatingGroup (Fin 7) ≤
    Subgroup.closure (⋃ i, ((sixP i ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7)))) := by
  set H := Subgroup.closure (⋃ i, ((sixP i ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7))))
  have hc : ∀ i, cyc i ∈ H := fun i => Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, cyc_mem i⟩)
  refine PermTools.alternatingGroup_le_of_orbit H ⟨cyc 0, hc 0, isThreeCycle_cyc 0⟩ fun x => ?_
  fin_cases x
  · exact ⟨cyc 0, hc 0, by decide⟩
  · exact ⟨cyc 1, hc 1, by decide⟩
  · exact ⟨cyc 0 * cyc 0, H.mul_mem (hc 0) (hc 0), by decide⟩
  · exact ⟨cyc 1 * cyc 1, H.mul_mem (hc 1) (hc 1), by decide⟩
  · exact ⟨cyc 2, hc 2, by decide⟩
  · exact ⟨cyc 2 * cyc 2, H.mul_mem (hc 2) (hc 2), by decide⟩
  · exact ⟨1, H.one_mem, rfl⟩

theorem sixGen_PN (i : Fin 3) : alternatingGroup (Fin 7) ≤
    Subgroup.closure (((sixN ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7))) ∪ (sixP i ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7)))) := by
  set H := Subgroup.closure (((sixN ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7))) ∪ (sixP i ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))))
  have hc : cyc i ∈ H := Subgroup.subset_closure (Or.inr (cyc_mem i))
  have hu : swap 0 1 * swap 2 3 ∈ H := Subgroup.subset_closure (Or.inl (Subgroup.mem_inf.2
    ⟨Subgroup.subset_closure (by simp [gN]), swap_mul_swap_mem_alternatingGroup (by decide)
      (by decide)⟩))
  have hv : swap 0 4 * swap 2 5 ∈ H := Subgroup.subset_closure (Or.inl (Subgroup.mem_inf.2
    ⟨Subgroup.subset_closure (by simp [gN]), swap_mul_swap_mem_alternatingGroup (by decide)
      (by decide)⟩))
  have hc2 : cyc i * cyc i ∈ H := H.mul_mem hc hc
  refine PermTools.alternatingGroup_le_of_orbit H ⟨cyc i, hc, isThreeCycle_cyc i⟩ fun x => ?_
  fin_cases i <;> fin_cases x
  · exact ⟨_, hc, by decide⟩
  · exact ⟨_, H.mul_mem hu hc, by decide⟩
  · exact ⟨_, hc2, by decide⟩
  · exact ⟨_, H.mul_mem hu hc2, by decide⟩
  · exact ⟨_, H.mul_mem hv hc, by decide⟩
  · exact ⟨_, H.mul_mem hv hc2, by decide⟩
  · exact ⟨1, H.one_mem, rfl⟩
  · exact ⟨_, H.mul_mem hu hc, by decide⟩
  · exact ⟨_, hc, by decide⟩
  · exact ⟨_, H.mul_mem hu hc2, by decide⟩
  · exact ⟨_, hc2, by decide⟩
  · exact ⟨_, H.mul_mem hv (H.mul_mem hu hc), by decide⟩
  · exact ⟨_, H.mul_mem hv (H.mul_mem hu hc2), by decide⟩
  · exact ⟨1, H.one_mem, rfl⟩
  · exact ⟨_, H.mul_mem hv hc, by decide⟩
  · exact ⟨_, H.mul_mem hu (H.mul_mem hv hc), by decide⟩
  · exact ⟨_, H.mul_mem hv hc2, by decide⟩
  · exact ⟨_, H.mul_mem hu (H.mul_mem hv hc2), by decide⟩
  · exact ⟨_, hc, by decide⟩
  · exact ⟨_, hc2, by decide⟩
  · exact ⟨1, H.one_mem, rfl⟩

def sixPermData : PermData where
  D := sixD
  E := sixE
  P := sixP
  PN := sixN
  card_D := card_sixD
  card_E := card_sixE
  card_P := card_sixP
  card_PN := card_sixN
  E_le_D := sixE_le_sixD
  E_le_P := sixE_le_sixP
  D_le_PN := sixD_le_sixN
  swap_mem_E := swap_mem_sixE
  D_fix := sixD_fix
  P_notNormal := sixP_notNormal
  PN_notNormal := sixN_notNormal
  D_trans := sixD_trans
  D_stab := sixD_stab
  E_pairs := sixE_pairs
  gen_P := sixGen_P
  gen_PN := sixGen_PN

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
