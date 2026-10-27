module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSymplectic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PartStab

public section

namespace CFSG.AGLEmbeddingD2.HeisSymplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.CurtisTits
  CFSG.AGLEmbeddingD2.SquareSymplectic CFSG.AGLEmbeddingD2.PartStab
  CFSG.AGLEmbeddingD2.ParabLevi

section Run

variable (I' : ℕ → Prop) [DecidablePred I']

@[expose] def runStart : ℕ → ℕ
  | 0 => 0
  | a + 1 => if I' a then runStart a else a + 1

theorem runStart_le (a : ℕ) : runStart I' a ≤ a := by
  induction a with
  | zero => simp [runStart]
  | succ a ih =>
    simp only [runStart]
    split_ifs
    · omega
    · exact le_rfl

theorem runStart_succ_of {a : ℕ} (h : I' a) : runStart I' (a + 1) = runStart I' a := by
  simp [runStart, h]

theorem runStart_succ_of_not {a : ℕ} (h : ¬ I' a) : runStart I' (a + 1) = a + 1 := by
  simp [runStart, h]

theorem runStart_runStart (a : ℕ) : runStart I' (runStart I' a) = runStart I' a := by
  induction a with
  | zero => simp [runStart]
  | succ a ih =>
    by_cases h : I' a
    · rw [runStart_succ_of I' h]
      exact ih
    · rw [runStart_succ_of_not I' h, runStart_succ_of_not I' h]

theorem forall_of_runStart_eq {a b : ℕ} (hab : a ≤ b) (h : runStart I' b = runStart I' a) :
    ∀ c, a ≤ c → c < b → I' c := by
  induction b with
  | zero => intro c _ hc; omega
  | succ b ih =>
    intro c hac hcb
    by_cases hb : I' b
    · rw [runStart_succ_of I' hb] at h
      by_cases hab' : a ≤ b
      · by_cases hcb' : c < b
        · exact ih hab' h c hac hcb'
        · have : c = b := by omega
          rw [this]
          exact hb
      · omega
    · rw [runStart_succ_of_not I' hb] at h
      have h1 := runStart_le I' a
      omega

end Run

section Part

open scoped Classical

variable {n : ℕ} (I : Set (Fin n))

@[expose] def NodeIn (i : ℕ) : Prop := ∃ h : i < n, (⟨i, h⟩ : Fin n) ∈ I

@[expose] noncomputable def lo (a : ℕ) : ℕ := runStart (NodeIn I) a

theorem lo_le (a : ℕ) : lo I a ≤ a := runStart_le _ a

theorem lo_succ_of {a : ℕ} (h : NodeIn I a) : lo I (a + 1) = lo I a := runStart_succ_of _ h

theorem lo_lo (a : ℕ) : lo I (lo I a) = lo I a := runStart_runStart _ a

theorem forall_of_lo_eq {a b : ℕ} (hab : a ≤ b) (h : lo I b = lo I a) :
    ∀ c, a ≤ c → c < b → NodeIn I c := forall_of_runStart_eq _ hab h

def IsTail (a : ℕ) : Prop := NodeIn I (n - 1) ∧ lo I a = lo I (n - 1)

@[expose] noncomputable def partFn : Fin n ⊕ Fin n → ℕ × ℕ
  | .inl a => if IsTail I a.val then (0, 0) else (lo I a.val + 1, 0)
  | .inr a => if IsTail I a.val then (0, 0) else (lo I a.val + 1, 1)

theorem isTail_succ_iff {a : ℕ} (h : NodeIn I a) : IsTail I (a + 1) ↔ IsTail I a := by
  simp only [IsTail, lo_succ_of I h]

theorem partFn_inl_succ {a b : Fin n} (hb : b.val = a.val + 1) (h : NodeIn I a.val) :
    partFn I (.inl b) = partFn I (.inl a) := by
  simp only [partFn, hb, isTail_succ_iff I h, lo_succ_of I h]

theorem partFn_inr_succ {a b : Fin n} (hb : b.val = a.val + 1) (h : NodeIn I a.val) :
    partFn I (.inr b) = partFn I (.inr a) := by
  simp only [partFn, hb, isTail_succ_iff I h, lo_succ_of I h]

theorem partFn_inl_inr_last {a : Fin n} (ha : a.val + 1 = n) (h : NodeIn I a.val) :
    partFn I (.inl a) = partFn I (.inr a) := by
  have hn : a.val = n - 1 := by omega
  have hT : IsTail I a.val := by
    refine ⟨?_, by rw [hn]⟩
    rw [← hn]
    exact h
  simp only [partFn, hT, ite_true]

noncomputable def tailSet : Finset (Fin n) := Finset.univ.filter fun a => IsTail I a.val

noncomputable def baseSet (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => ¬ IsTail I a.val ∧ lo I a.val = m

theorem card_baseSet_le {R : ℕ}
    (hrun : ∀ c, c + R + 1 ≤ n → ¬ ∀ i, c ≤ i → i < c + R → NodeIn I i) (m : ℕ) :
    (baseSet I m).card ≤ R := by
  by_cases hex : ∃ a : Fin n, lo I a.val = m
  · obtain ⟨a₀, ha₀⟩ := hex
    have hm : lo I m = m := by rw [← ha₀]; exact lo_lo I a₀.val
    have hsub : ∀ a ∈ baseSet I m, m ≤ a.val ∧ a.val < m + R := by
      intro a ha
      simp only [baseSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have h1 : m ≤ a.val := ha.2 ▸ lo_le I a.val
      refine ⟨h1, ?_⟩
      by_contra hlt
      have hlt' : m + R ≤ a.val := by omega
      refine hrun m (by have := a.isLt; omega) fun i hi hiR => ?_
      exact forall_of_lo_eq I h1 (by rw [ha.2, hm]) i hi (by omega)
    have : (baseSet I m).card ≤ (Finset.range R).card := by
      refine Finset.card_le_card_of_injOn (fun a => a.val - m) ?_ ?_
      · intro a ha
        have := hsub a ha
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · intro a ha b hb hab
        have h1 := hsub a ha
        have h2 := hsub b hb
        exact Fin.ext (by simp only at hab; omega)
    simpa using this
  · push Not at hex
    have : baseSet I m = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
      simp only [baseSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact hex a ha.2
    rw [this]
    simp

theorem card_tailSet_le {T : ℕ}
    (htail : ∀ c, c + T = n → ¬ ∀ i, c ≤ i → i < c + T → NodeIn I i) :
    (tailSet I).card ≤ T - 1 := by
  by_cases hN : NodeIn I (n - 1)
  · set t := lo I (n - 1) with ht
    have hn : 0 < n := by
      obtain ⟨h, -⟩ := hN
      omega
    have htn : t ≤ n - 1 := lo_le I (n - 1)
    have hlt : n - t < T := by
      by_contra hcon
      have hTn : T ≤ n - t := by omega
      refine htail (n - T) (by omega) fun i hi hiT => ?_
      by_cases hi1 : i = n - 1
      · rw [hi1]
        exact hN
      · refine forall_of_lo_eq I htn (by rw [← ht, lo_lo]) i (by omega) (by omega)
    have hsub : ∀ a ∈ tailSet I, t ≤ a.val := by
      intro a ha
      have ha' : IsTail I a.val := (Finset.mem_filter.1 ha).2
      rw [ht, ← ha'.2]
      exact lo_le I a.val
    have : (tailSet I).card ≤ (Finset.range (T - 1)).card := by
      refine Finset.card_le_card_of_injOn (fun a => a.val - t) ?_ ?_
      · intro a ha
        have := hsub a ha
        have := a.isLt
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · intro a ha b hb hab
        have h1 := hsub a ha
        have h2 := hsub b hb
        exact Fin.ext (by simp only at hab; omega)
    simpa using this
  · have : tailSet I = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
      exact hN (Finset.mem_filter.1 ha).2.1
    rw [this]
    simp

theorem card_fiber_le {M R T : ℕ} (hRM : R ≤ M) (hTM : 2 * (T - 1) ≤ M)
    (hrun : ∀ c, c + R + 1 ≤ n → ¬ ∀ i, c ≤ i → i < c + R → NodeIn I i)
    (htail : ∀ c, c + T = n → ¬ ∀ i, c ≤ i → i < c + T → NodeIn I i) (c : ℕ × ℕ) :
    Fintype.card {x : Fin n ⊕ Fin n // partFn I x = c} ≤ M := by
  rw [Fintype.card_subtype]
  have hb := card_baseSet_le I hrun
  have ht := card_tailSet_le I htail
  rcases c with ⟨p, q⟩
  cases p with
  | zero =>
    have hsub : (Finset.univ.filter fun x : Fin n ⊕ Fin n => partFn I x = (0, q)) ⊆
        (tailSet I).disjSum (tailSet I) := by
      intro x hx
      have hx' := (Finset.mem_filter.1 hx).2
      rcases x with a | a
      · simp only [partFn] at hx'
        split_ifs at hx' with hT
        · exact Finset.inl_mem_disjSum.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩)
        · simp at hx'
      · simp only [partFn] at hx'
        split_ifs at hx' with hT
        · exact Finset.inr_mem_disjSum.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩)
        · simp at hx'
    calc _ ≤ ((tailSet I).disjSum (tailSet I)).card := Finset.card_le_card hsub
      _ = (tailSet I).card + (tailSet I).card := Finset.card_disjSum _ _
      _ ≤ M := by omega
  | succ m =>
    rcases q with _ | _ | q
    · have hsub : (Finset.univ.filter fun x : Fin n ⊕ Fin n => partFn I x = (m + 1, 0)) ⊆
          (baseSet I m).map Function.Embedding.inl := by
        intro x hx
        have hx' := (Finset.mem_filter.1 hx).2
        rcases x with a | a
        · simp only [partFn] at hx'
          split_ifs at hx' with hT
          · simp at hx'
          · simp only [Prod.mk.injEq, add_left_inj, and_true] at hx'
            exact Finset.mem_map.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hT, hx'⟩, rfl⟩
        · simp only [partFn] at hx'
          split_ifs at hx' with hT <;> simp at hx'
      calc _ ≤ ((baseSet I m).map Function.Embedding.inl).card := Finset.card_le_card hsub
        _ = (baseSet I m).card := Finset.card_map _
        _ ≤ M := (hb m).trans hRM
    · have hsub : (Finset.univ.filter fun x : Fin n ⊕ Fin n => partFn I x = (m + 1, 1)) ⊆
          (baseSet I m).map Function.Embedding.inr := by
        intro x hx
        have hx' := (Finset.mem_filter.1 hx).2
        rcases x with a | a
        · simp only [partFn] at hx'
          split_ifs at hx' with hT <;> simp at hx'
        · simp only [partFn] at hx'
          split_ifs at hx' with hT
          · simp at hx'
          · simp only [Prod.mk.injEq, add_left_inj, and_true] at hx'
            exact Finset.mem_map.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hT, hx'⟩, rfl⟩
      calc _ ≤ ((baseSet I m).map Function.Embedding.inr).card := Finset.card_le_card hsub
        _ = (baseSet I m).card := Finset.card_map _
        _ ≤ M := (hb m).trans hRM
    · have : (Finset.univ.filter fun x : Fin n ⊕ Fin n => partFn I x = (m + 1, q + 2)) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
        have hx' := (Finset.mem_filter.1 hx).2
        rcases x with a | a <;> (simp only [partFn] at hx'; split_ifs at hx' <;> simp at hx')
      rw [this]
      simp

end Part

section Stab

variable {n : ℕ} {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem isPartDiag_of_mem_coordFix {ι κ : Type} [Fintype ι] [DecidableEq ι] (s : ι → κ)
    {S : Finset ι} (hS : ∀ x ∈ S, ∀ y ∈ S, s x = s y) {g : GL ι F} (hg : g ∈ coordFix S) :
    IsPartDiag s (g : Matrix ι ι F) := by
  intro x y hxy
  have hne : x ≠ y := fun h => hxy (h ▸ rfl)
  have hout : x ∉ S ∨ y ∉ S := by
    by_contra h
    push Not at h
    exact hxy (hS x h.1 y h.2)
  rw [hg x y hout, Matrix.one_apply_ne hne]

omit [Finite F] in
theorem isPartDiag_leviSp {κ : Type} (s : Fin n ⊕ Fin n → κ) {S : Finset (Fin n)}
    (hl : ∀ a ∈ S, ∀ b ∈ S, s (.inl a) = s (.inl b))
    (hr : ∀ a ∈ S, ∀ b ∈ S, s (.inr a) = s (.inr b)) {A : GL (Fin n) F} (hA : A ∈ coordFix S) :
    IsPartDiag s (mat n F (leviSp n F A)) := by
  rw [mat_leviSp]
  have hA' : A⁻¹ ∈ coordFix S := inv_mem hA
  intro x y hxy
  rcases x with a | a <;> rcases y with b | b
  · simp only [Matrix.fromBlocks_apply₁₁]
    have hne : a ≠ b := fun h => hxy (h ▸ rfl)
    have hout : a ∉ S ∨ b ∉ S := by
      by_contra h
      push Not at h
      exact hxy (hl a h.1 b h.2)
    rw [hA a b hout, Matrix.one_apply_ne hne]
  · simp only [Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [Matrix.fromBlocks_apply₂₁]
    rfl
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
    have hne : b ≠ a := fun h => hxy (h ▸ rfl)
    have hout : b ∉ S ∨ a ∉ S := by
      by_contra h
      push Not at h
      exact hxy (hr a h.2 b h.1)
    rw [hA' b a hout, Matrix.one_apply_ne hne]

theorem torus_le_partStab {κ : Type} [DecidableEq κ] (s : Fin n ⊕ Fin n → κ) :
    (⨆ k, torus n F k) ≤ (partStab F s).comap (StatedSp n F).subtype := by
  refine iSup_le fun k => ?_
  rw [torus, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  change IsPartDiag s (mat n F (equivStatedSp n F
    (TauCeti.GLSymplecticFin.diagonal (corootVec n F k c))))
  rw [mat_equiv_diagonal]
  intro x y hxy
  have hne : x ≠ y := fun h => hxy (h ▸ rfl)
  exact Matrix.diagonal_apply_ne _ hne

open scoped Classical in
theorem leviM_le_partStab (I : Set (Fin n)) :
    leviM (rootDatum n F) I ≤ (partStab F (partFn I)).comap (StatedSp n F).subtype := by
  refine iSup₂_le fun (i : Fin n) hi => ?_
  have hNode : NodeIn I i.val := ⟨i.isLt, hi⟩
  by_cases hk : i.val + 1 < n
  · intro g hg
    obtain ⟨A, hA, rfl⟩ := rankOne_le_map_coordFix_short hk hg
    have hl : partFn I (.inl ⟨i.val + 1, hk⟩) = partFn I (.inl i) :=
      partFn_inl_succ I rfl hNode
    have hr : partFn I (.inr ⟨i.val + 1, hk⟩) = partFn I (.inr i) :=
      partFn_inr_succ I rfl hNode
    refine isPartDiag_leviSp (partFn I) ?_ ?_ hA
    · intro a ha b hb
      rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
      · rfl
      · rw [Finset.mem_singleton.1 hb, hl]
      · rw [Finset.mem_singleton.1 ha, hl]
      · rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb]
    · intro a ha b hb
      rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
      · rfl
      · rw [Finset.mem_singleton.1 hb, hr]
      · rw [Finset.mem_singleton.1 ha, hr]
      · rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb]
  · intro g hg
    have hg' := rankOne_le_comap_coordFix_long hk hg
    have hlast : partFn I (.inl i) = partFn I (.inr i) := partFn_inl_inr_last I (by omega) hNode
    refine isPartDiag_of_mem_coordFix (partFn I) ?_ hg'
    intro x hx y hy
    rcases Finset.mem_insert.1 hx with rfl | hx <;> rcases Finset.mem_insert.1 hy with rfl | hy
    · rfl
    · rw [Finset.mem_singleton.1 hy, hlast]
    · rw [Finset.mem_singleton.1 hx, hlast]
    · rw [Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy]

open scoped Classical in
theorem isMulCommutative_of_le_torus_sup_leviM {M R T : ℕ}
    (hblock : ∀ (σ : Type) [Fintype σ] [DecidableEq σ], Fintype.card σ ≤ M →
      ∀ P : Subgroup (GL σ F), IsPGroup 5 P → IsMulCommutative P)
    (hRM : R ≤ M) (hTM : 2 * (T - 1) ≤ M) {I : Set (Fin n)}
    (hrun : ∀ c, c + R + 1 ≤ n → ¬ ∀ i, c ≤ i → i < c + R → NodeIn I i)
    (htail : ∀ c, c + T = n → ¬ ∀ i, c ≤ i → i < c + T → NodeIn I i)
    {Q : Subgroup (StatedSp n F)} (hQ : Q ≤ (⨆ k, torus n F k) ⊔ leviM (rootDatum n F) I)
    (hQ5 : IsPGroup 5 Q) : IsMulCommutative Q := by
  have hle : Q ≤ (partStab F (partFn I)).comap (StatedSp n F).subtype :=
    hQ.trans (sup_le (torus_le_partStab _) (leviM_le_partStab I))
  have hQ' : Q.map (StatedSp n F).subtype ≤ partStab F (partFn I) :=
    Subgroup.map_le_iff_le_comap.2 hle
  have hcomm := isMulCommutative_of_le_partStab (partFn I)
    (fun k P hP => hblock _ (card_fiber_le I hRM hTM hrun htail k) P hP) hQ' (hQ5.map _)
  let e := Q.equivMapOfInjective _ (Subgroup.subtype_injective (StatedSp n F))
  refine ⟨⟨fun a b => e.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact hcomm.is_comm.comm (e a) (e b)

end Stab

end CFSG.AGLEmbeddingD2.HeisSymplectic
