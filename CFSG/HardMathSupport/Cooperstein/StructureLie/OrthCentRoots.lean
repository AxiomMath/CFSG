module

public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin

variable {n : ℕ}

@[expose] def partSum (n : ℕ) (e : Fin n → ℤ) (m : ℕ) : ℤ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.val ≤ m), e x

theorem partSum_toStdD_of_lt (γ : Fin n → ℤ) {m : ℕ} (hm : m + 3 ≤ n) :
    partSum n (toStdD n γ) m = γ ⟨m, by omega⟩ := by
  induction m with
  | zero =>
    have h2 : ¬ (0 + 2 = n) := by omega
    have : Finset.univ.filter (fun x : Fin n => x.val ≤ 0) = {⟨0, by omega⟩} := by
      ext x
      simp [Fin.ext_iff]
    unfold partSum
    rw [this, Finset.sum_singleton]
    simp [toStdD, h2]
  | succ m ih =>
    have h1 := ih (by omega)
    have : Finset.univ.filter (fun x : Fin n => x.val ≤ m + 1) =
        insert ⟨m + 1, by omega⟩ (Finset.univ.filter (fun x : Fin n => x.val ≤ m)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hn : ⟨m + 1, by omega⟩ ∉ Finset.univ.filter (fun x : Fin n => x.val ≤ m) := by
      simp
    unfold partSum at h1 ⊢
    rw [this, Finset.sum_insert hn, h1]
    have h2 : ¬ (m + 1 + 2 = n) := by omega
    simp [toStdD, h2]

theorem partSum_succ (e : Fin n → ℤ) {m : ℕ} (hm : m + 1 < n) :
    partSum n e (m + 1) = partSum n e m + e ⟨m + 1, hm⟩ := by
  have : Finset.univ.filter (fun x : Fin n => x.val ≤ m + 1) =
      insert ⟨m + 1, hm⟩ (Finset.univ.filter (fun x : Fin n => x.val ≤ m)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hn : (⟨m + 1, hm⟩ : Fin n) ∉ Finset.univ.filter (fun x : Fin n => x.val ≤ m) := by
    simp
  unfold partSum
  rw [this, Finset.sum_insert hn, add_comm]

theorem partSum_toStdD_pred_pred (m : ℕ) (γ : Fin (m + 3) → ℤ) :
    partSum (m + 3) (toStdD (m + 3) γ) (m + 1) = γ ⟨m + 1, by omega⟩ + γ ⟨m + 2, by omega⟩ := by
  have h1 := partSum_toStdD_of_lt γ (m := m) le_rfl
  rw [partSum_succ _ (by omega), h1]
  have h2 : (m + 1) + 2 = m + 3 := by omega
  have e : (⟨m + 1 + 1, by omega⟩ : Fin (m + 3)) = ⟨m + 2, by omega⟩ := rfl
  simp [toStdD, h2, e]
  ring

theorem partSum_toStdD_last (m : ℕ) (γ : Fin (m + 3) → ℤ) :
    partSum (m + 3) (toStdD (m + 3) γ) (m + 2) = 2 * γ ⟨m + 2, by omega⟩ := by
  have h1 := partSum_toStdD_pred_pred m γ
  rw [partSum_succ _ (by omega), h1]
  have h2 : ¬ ((m + 1 + 1) + 2 = m + 3) := by omega
  simp [toStdD]
  ring

theorem partSum_single_add_single (a b : Fin n) (x y : ℤ) (m : ℕ) :
    partSum n (Pi.single a x + Pi.single b y) m =
      (if a.val ≤ m then x else 0) + (if b.val ≤ m then y else 0) := by
  unfold partSum
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  simp [Pi.single_apply]

@[expose] def nodeA (n : ℕ) (j : Fin n) : Set (Fin n) := {a | a.val ≤ j.val ∨ n ≤ j.val + 2}

@[expose] def nodeSign (n : ℕ) (j a : Fin n) : Bool := !decide (j.val + 2 = n ∧ a.val + 1 = n)

theorem node_coord (m : ℕ) (γ : Fin (m + 3) → ℤ) (j : Fin (m + 3)) :
    (j.val ≤ m → γ j = partSum (m + 3) (toStdD (m + 3) γ) j.val) ∧
    (j.val = m + 1 → 2 * γ j = partSum (m + 3) (toStdD (m + 3) γ) (m + 1) -
        toStdD (m + 3) γ ⟨m + 2, by omega⟩) ∧
    (j.val = m + 2 → 2 * γ j = partSum (m + 3) (toStdD (m + 3) γ) (m + 2)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [partSum_toStdD_of_lt γ (by omega : j.val + 3 ≤ m + 3)]
  · have hj : j = ⟨m + 1, by omega⟩ := Fin.ext h
    rw [hj]
    rw [partSum_toStdD_pred_pred m γ]
    simp [toStdD]
    ring
  · have hj : j = ⟨m + 2, by omega⟩ := Fin.ext h
    rw [hj]
    rw [partSum_toStdD_last m γ]

theorem root_node_pos {m : ℕ} {γ : Fin (m + 3) → ℤ} {a b : Fin (m + 3)} {s t : Bool}
    (j : Fin (m + 3))
    (h : toStdD (m + 3) γ = Pi.single a (boolSign s) + Pi.single b (boolSign t))
    (ha : a ∈ nodeA (m + 3) j) (hs : s = nodeSign (m + 3) j a)
    (hb : b ∉ nodeA (m + 3) j ∨ (b ∈ nodeA (m + 3) j ∧ t = nodeSign (m + 3) j b)) :
    0 < γ j := by
  obtain ⟨c1, c2, c3⟩ := node_coord m γ j
  rw [h] at c1 c2 c3
  simp only [nodeA, Set.mem_ofPred_eq] at ha hb
  have hnA : ∀ x : Fin (m + 3), x ∈ nodeA (m + 3) j ↔ (x.val ≤ j.val ∨ m + 3 ≤ j.val + 2) :=
    fun x => Iff.rfl
  rcases Nat.lt_or_ge j.val (m + 1) with h1 | h1
  ·
    have := c1 (by omega)
    rw [partSum_single_add_single] at this
    clear c1 c2 c3
    have hja : j.val ≤ m := by omega
    simp only [nodeSign] at hs hb
    rw [this]
    cases s <;> cases t <;> simp_all [boolSign]
    all_goals omega
  · rcases Nat.lt_or_ge j.val (m + 2) with h2 | h2
    · have hj : j.val = m + 1 := by omega
      have := c2 hj
      rw [partSum_single_add_single] at this
      clear c1 c2 c3
      simp only [nodeSign] at hs hb
      cases s <;> cases t <;> simp_all [boolSign, Pi.single_apply, Fin.ext_iff]
      all_goals omega
    · have hj : j.val = m + 2 := by omega
      have := c3 hj
      rw [partSum_single_add_single] at this
      clear c1 c2 c3
      simp only [nodeSign] at hs hb
      cases s <;> cases t <;> simp_all [boolSign]
      all_goals omega

theorem longRoot_mem_radical {m : ℕ} {F : Type} [Field F] (hn : 3 ≤ m + 3) (j : Fin (m + 3))
    {a b : Fin (m + 3)} (hab : a ≠ b) (t : Bool)
    (ha : a ∈ nodeA (m + 3) j)
    (hb : b ∉ nodeA (m + 3) j ∨ (b ∈ nodeA (m + 3) j ∧ t = nodeSign (m + 3) j b)) (c : F) :
    (plusFrame (m + 3) F hn).longRoot hab (nodeSign (m + 3) j a) t (Multiplicative.ofAdd c) ∈
      CFSG.AGLEmbedding.LieOut.radical (plusDatum (m + 3) F hn) j := by
  obtain ⟨γ, hγ, hγe⟩ := exists_mem_rootsD_toStdD_eq (m + 3) hab
    (boolSign_eq_one_or_eq_neg_one (nodeSign (m + 3) j a)) (boolSign_eq_one_or_eq_neg_one t)
  have hpos := root_node_pos j hγe ha rfl hb
  have hrg := plusRootGroup_eq (K := F) hn hab _ _ hγe
  exact CFSG.AGLEmbedding.LieOut.rootGroup_le_radical (D := plusDatum (m + 3) F hn) hγ hpos
    (by rw [show (plusDatum (m + 3) F hn).rootGroup γ = plusRootGroup (m + 3) F hn γ from rfl, hrg]
        exact ⟨_, rfl⟩)

end CFSG.HardMathSupport.Cooperstein.StructureLie
