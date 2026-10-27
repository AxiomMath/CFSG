module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabBlockAssembly
public import CFSG.ClassicalInvolution.Phan.PhanDn.KLinearIsometry
public import CFSG.ClassicalInvolution.Phan.PhanDn.PanelParabLe

public section
namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1)) {m : ℕ} {C : Set (Fin (m + 1))}

theorem flagVert_smul_eq_iff
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (U : FlagVert (unitaryInvolution K 2 1) m) :
    g • U = U ↔ U.1.map
      (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) = U.1 := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [coe_smul_flagVert] at this
  · intro h
    apply Subtype.ext
    rwa [coe_smul_flagVert]

theorem qTwoParab_mono {C C' : Set (Fin (m + 1))} (h : C ⊆ C') :
    qTwoParab E m C ≤ qTwoParab E m C' := by
  intro x hx
  rw [mem_qTwoParab] at hx ⊢
  intro j hj
  exact hx j (fun hjc => hj (h hjc))

theorem span_stdE_eq_coordSpan (I : Set (Fin (m + 1))) :
    Submodule.span K (stdE (K := K) (n := m + 1) '' I) =
      coordSpan (K := K) (m + 1) I ∅ := by
  simp [coordSpan]

theorem diagHom_map_coordSpan (t : Fin (m + 1) → normOne (unitaryInvolution K 2 1))
    (I J : Set (Fin (m + 1))) :
    (coordSpan (K := K) (m + 1) I J).map
        (bcLin E (m + 1) (diagHom F (unitaryInvolution K 2 1) (m + 1) t :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
      coordSpan (K := K) (m + 1) I J := by
  refine map_coordSpan_eq_of_bc E _ (fun i hi => ?_) (fun j hj => ?_)
  · have hvec : bc E (m + 1) (diagHom F (unitaryInvolution K 2 1) (m + 1) t)
        (stdE (K := K) (n := m + 1) i) =
        (((t i : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) • stdE (K := K) (n := m + 1) i := by
      ext p
      cases p with
      | inl a =>
          rw [bc_diagHom_inl]
          by_cases ha : a = i
          · subst a; simp [Pi.smul_apply, smul_eq_mul]
          · simp [Pi.smul_apply, smul_eq_mul, ha]
      | inr a =>
          rw [bc_diagHom_inr]
          simp [Pi.smul_apply, smul_eq_mul]
    rw [hvec]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Set.mem_image_of_mem _ hi)))
  · have hvec : bc E (m + 1) (diagHom F (unitaryInvolution K 2 1) (m + 1) t)
        (stdF (K := K) (n := m + 1) j) =
        (unitaryInvolution K 2 1) (((t j : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) •
          stdF (K := K) (n := m + 1) j := by
      ext p
      cases p with
      | inl a =>
          rw [bc_diagHom_inl]
          simp [Pi.smul_apply, smul_eq_mul]
      | inr a =>
          rw [bc_diagHom_inr]
          by_cases ha : a = j
          · subst a; simp [Pi.smul_apply, smul_eq_mul]
          · simp [Pi.smul_apply, smul_eq_mul, ha]
    rw [hvec]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr (Set.mem_image_of_mem _ hj)))

theorem diagHom_mem_qTwoParab_empty (hK : Nat.card K = 4) (hm : 3 ≤ m)
    (t : Fin (m + 1) → normOne (unitaryInvolution K 2 1)) :
    (⟨diagHom F (unitaryInvolution K 2 1) (m + 1) t,
      diagTorusV_le_orthDerived E (by omega : 4 ≤ m + 1)
        (by rw [diagTorusV]; exact ⟨t, rfl⟩)⟩ :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) ∈
      qTwoParab E m ∅ := by
  rw [mem_qTwoParab]
  intro j hj
  simp only [Set.mem_empty_iff_false, not_false_eq_true] at hj
  rw [flagVert_smul_eq_iff, coe_flagChamber]
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
  · by_cases hj' : (j' : ℕ) + 1 = m
    · rw [stdDChamber_elt_eq_alt_coordSpan (j := Fin.castSucc j')
        (by intro h; have := congrArg Fin.val h; simp at this; omega) hj']
      exact diagHom_map_coordSpan E t _ _
    · rw [stdDChamber_elt_eq_sub (i := Fin.castSucc j')
        (by intro h; have := congrArg Fin.val h; simp at this; omega) hj',
        stdDChamber_sub_eq_span, span_stdE_eq_coordSpan]
      exact diagHom_map_coordSpan E t _ _
  · rw [stdDChamber_elt_last_eq_coordSpan]
    exact diagHom_map_coordSpan E t _ _

namespace ChainScratch

variable (C : Set (Fin (m + 1)))

@[expose] noncomputable def cutSet (C : Set (Fin (m + 1))) : Finset ℕ :=
  by
    classical
    exact insert 0 ((Finset.univ.filter (fun j : Fin (m + 1) => j ∉ C)).image
      (fun j => j.val + 1))

@[expose] noncomputable def blockIndex (C : Set (Fin (m + 1))) (i : Fin (m + 1)) : ℕ :=
  ((cutSet C).filter (fun c => c ≤ i.val)).card

variable {C}

theorem zero_mem_cutSet : 0 ∈ cutSet C := by
  rw [cutSet]; exact Finset.mem_insert_self _ _

theorem succ_mem_cutSet {j : Fin (m + 1)} (hj : j ∉ C) : j.val + 1 ∈ cutSet C := by
  rw [cutSet]
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, by simp [hj], rfl⟩)

theorem mem_cutSet_iff {c : ℕ} :
    c ∈ cutSet C ↔ c = 0 ∨ ∃ j : Fin (m + 1), j ∉ C ∧ j.val + 1 = c := by
  rw [cutSet]
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact Or.inl rfl
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨j, by simpa using hj, rfl⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact zero_mem_cutSet
    · exact succ_mem_cutSet hj

theorem cutSet_le (hlast : Fin.last m ∉ C) {c : ℕ} (hc : c ∈ cutSet C) : c ≤ m + 1 := by
  rcases (mem_cutSet_iff).mp hc with rfl | ⟨j, hj, rfl⟩
  · omega
  · omega

theorem last_cut_mem (hlast : Fin.last m ∉ C) : m + 1 ∈ cutSet C := by
  simpa using succ_mem_cutSet (C := C) hlast

theorem nextCut_exists (hlast : Fin.last m ∉ C) (i : Fin (m + 1)) :
    ∃ c, c ∈ cutSet C ∧ i.val < c :=
  ⟨m + 1, last_cut_mem hlast, i.isLt⟩

noncomputable def nextCut (hlast : Fin.last m ∉ C) (i : Fin (m + 1)) : ℕ :=
  Nat.find (nextCut_exists (C := C) hlast i)

theorem blockIndex_pos (i : Fin (m + 1)) : 0 < blockIndex C i := by
  rw [blockIndex, Finset.card_pos]
  exact ⟨0, Finset.mem_filter.mpr ⟨zero_mem_cutSet, by omega⟩⟩

theorem blockIndex_mono {i j : Fin (m + 1)} (hij : i ≤ j) :
    blockIndex C i ≤ blockIndex C j := by
  rw [blockIndex, blockIndex]
  apply Finset.card_le_card
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, hc.2.trans (by simpa using hij)⟩

theorem nextCut_mem (hlast : Fin.last m ∉ C) (i : Fin (m + 1)) :
    nextCut (C := C) hlast i ∈ cutSet C :=
  (Nat.find_spec (nextCut_exists (C := C) hlast i)).1

theorem nextCut_gt (hlast : Fin.last m ∉ C) (i : Fin (m + 1)) :
    i.val < nextCut (C := C) hlast i :=
  (Nat.find_spec (nextCut_exists (C := C) hlast i)).2

theorem nextCut_min (hlast : Fin.last m ∉ C) (i : Fin (m + 1)) {c : ℕ}
    (hc : c ∈ cutSet C) (hi : i.val < c) : nextCut (C := C) hlast i ≤ c :=
  Nat.find_min' (nextCut_exists (C := C) hlast i) ⟨hc, hi⟩

theorem nextCut_le_of_blockIndex_lt (hlast : Fin.last m ∉ C) {i j : Fin (m + 1)}
    (hij : blockIndex C j < blockIndex C i) : nextCut (C := C) hlast j ≤ i.val := by
  by_contra hcon
  rw [not_le] at hcon
  have hle : blockIndex C i ≤ blockIndex C j := by
    rw [blockIndex, blockIndex]
    apply Finset.card_le_card
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨hc.1, ?_⟩
    by_contra hcj
    rw [not_le] at hcj
    exact absurd (nextCut_min hlast j hc.1 (by omega)) (by omega)
  omega

noncomputable def V (c : ℕ) : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
  coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < c} ∅

theorem V_zero : V (K := K) (m := m) 0 = ⊥ := by
  rw [V, show {i : Fin (m + 1) | i.val < 0} = (∅ : Set (Fin (m + 1))) by
    ext i; simp]
  simp [coordSpan]

theorem stdE_mem_V {j : Fin (m + 1)} {c : ℕ} (hj : j.val < c) :
    stdE (K := K) (n := m + 1) j ∈ V (K := K) (m := m) c := by
  rw [V, coordSpan]
  exact Submodule.subset_span (Or.inl (Set.mem_image_of_mem _ hj))

theorem V_apply_eq_zero {c : ℕ} {v : Fin (m + 1) ⊕ Fin (m + 1) → K}
    (hv : v ∈ V (K := K) (m := m) c) {i : Fin (m + 1)} (hi : c ≤ i.val) :
    v (Sum.inl i) = 0 := by
  rw [V, coordSpan, Set.image_empty, Set.union_empty] at hv
  refine Submodule.span_induction (p := fun v _ => v (Sum.inl i) = 0) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨k, hk, rfl⟩
    rw [stdE_inl, if_neg (by
      intro h
      have h' : i.val = k.val := congrArg Fin.val h
      have hk' : k.val < c := hk
      omega)]
  · simp
  · intro u w _ _ hu hw
    simp [Pi.add_apply, hu, hw]
  · intro a u _ hu
    simp [Pi.smul_apply, hu]

theorem elt_eq_V_of_val_add_one_ne {j : Fin (m + 1)}
    (hjlast : j ≠ Fin.last m) (hjm : j.val + 1 ≠ m) :
    (stdDChamber (unitaryInvolution K 2 1) (m + 1)).elt j = V (K := K) (m := m) (j.val + 1) := by
  rw [stdDChamber_elt_eq_sub hjlast hjm, V, stdDChamber_sub_eq_span, coordSpan]
  simp only [Set.image_empty, Set.union_empty]

theorem elt_last_eq_V :
    (stdDChamber (unitaryInvolution K 2 1) (m + 1)).elt (Fin.last m) =
      V (K := K) (m := m) (m + 1) := by
  rw [stdDChamber_elt_last_eq_coordSpan, V]
  congr 1
  ext v
  exact ⟨fun _ => v.isLt, fun _ => trivial⟩

theorem elt_alt_eq (hm : 1 ≤ m) :
    (stdDChamber (unitaryInvolution K 2 1) (m + 1)).elt
        (⟨m - 1, by omega⟩ : Fin (m + 1)) =
      coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m} {Fin.last m} := by
  refine stdDChamber_elt_eq_alt_coordSpan (j := (⟨m - 1, by omega⟩ : Fin (m + 1))) ?_ ?_
  · intro h
    have := congrArg Fin.val h
    simp [Fin.val_last] at this
    omega
  · simp only [Fin.val_mk]
    omega

theorem elt_alt_eq_coordSpan (hm : 1 ≤ m) :
    (stdDChamber (unitaryInvolution K 2 1) (m + 1)).alt =
      coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m} {Fin.last m} := by
  have h := elt_alt_eq (K := K) (m := m) hm
  rw [stdDChamber_elt_eq_alt (i := (⟨m - 1, by omega⟩ : Fin (m + 1))) ?_ ?_] at h
  · exact h
  · intro hcon
    have := congrArg Fin.val hcon
    simp [Fin.val_last] at this
    omega
  · simp only [Fin.val_mk]
    omega

theorem V_last : V (K := K) (m := m) (m + 1) = stdLag (m + 1) K := by
  rw [V, stdLag_eq_span_stdE, coordSpan]
  congr 1
  ext v
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi⟩)
    · exact ⟨i, rfl⟩
    · simp at hi
  · rintro ⟨i, rfl⟩
    exact Or.inl ⟨i, i.isLt, rfl⟩

theorem V_m_eq_elt_inf (E : QuadExt F K (unitaryInvolution K 2 1)) (hm : 1 ≤ m) :
    V (K := K) (m := m) m =
      (stdDChamber (unitaryInvolution K 2 1) (m + 1)).elt (Fin.last m) ⊓
        (stdDChamber (unitaryInvolution K 2 1) (m + 1)).elt
          (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
  rw [V, coordSpan, Set.image_empty, Set.union_empty]
  rw [elt_last_eq_V, V_last, elt_alt_eq (K := K) (m := m) hm,
    ← elt_alt_eq_coordSpan (K := K) (m := m) hm,
    ← stdDChamber_elt_last_eq_stdLag (K := K) (m := m) (f := 1)]
  rw [FlipFrame.elt_last_inf_alt (m := m) E.isUnitary.invol
    (stdDChamber (unitaryInvolution K 2 1) (m + 1)).toFlipFrame]
  rw [stdDChamber_sub_eq_span]

theorem map_stdLag_le_of_isKLinear
    {g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)}
    (hKl : ∀ (a : K) x, g (a • x) = a • g x) :
    (stdLag (m + 1) K).map
        (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) ≤
      stdLag (m + 1) K := by
  rw [stdLag_eq_span_stdE, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨i, ⟨k, rfl⟩, rfl⟩
  have h := bcLin_stdLag_of_isKLinear E (m + 1)
    (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) hKl
    (Pi.single k (1 : K))
  rw [stdLag_eq_span_stdE] at h
  simpa [stdE] using h

theorem map_V_le_of_cut (hm : 1 ≤ m) (hlast : Fin.last m ∉ C)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (hKl : ∀ (a : K) x,
      (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • x) =
        a • (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) x)
    (hfix : ∀ j ∉ C, (flagChamber E m j).1.map
      (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (flagChamber E m j).1)
    {c : ℕ} (hc : c ∈ cutSet C) :
    (V (K := K) (m := m) c).map
        (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) ≤
      V (K := K) (m := m) c := by
  rcases (mem_cutSet_iff).mp hc with rfl | ⟨j, hj, rfl⟩
  · rw [V_zero, Submodule.map_bot]
  · have hc_le : j.val + 1 ≤ m + 1 := by omega
    have hfixj := hfix j hj
    rw [coe_flagChamber] at hfixj
    rcases lt_or_eq_of_le hc_le with hlt | heq
    · by_cases hjm : j.val + 1 = m
      ·
        have hj_eq : j = (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
          apply Fin.ext
          simp
          omega
        rw [hj_eq] at hfixj
        rw [show j.val + 1 = m by omega, V_m_eq_elt_inf E (by omega)]
        rw [Submodule.map_inf _ (by
          intro a b hab
          rw [bcLin_eq_coe_bc] at hab
          exact (bc E (m + 1) g).injective hab)]
        have hlastfix := hfix (Fin.last m) hlast
        rw [coe_flagChamber] at hlastfix
        rw [hfixj, hlastfix]
      ·
        have hj_last : j ≠ Fin.last m := by
          intro h
          have := congrArg Fin.val h
          simp [Fin.val_last] at this
          omega
        rw [elt_eq_V_of_val_add_one_ne hj_last hjm] at hfixj
        exact le_of_eq hfixj
    ·
      have hj_last : j = Fin.last m := by
        apply Fin.ext
        have := j.isLt
        simp [Fin.val_last]
        omega
      subst hj_last
      rw [show ((Fin.last m : Fin (m + 1)) : ℕ) + 1 = m + 1 by simp, V_last]
      exact map_stdLag_le_of_isKLinear E hKl

end ChainScratch

open ChainScratch

namespace ChainAssembly

variable (hlast : Fin.last m ∉ C)

noncomputable abbrev starts (C' : Set (Fin (m + 1))) (h' : Fin.last m ∉ C') : Finset ℕ :=
  (cutSet C').erase (m + 1)

theorem mem_starts_iff {c : ℕ} :
    c ∈ starts C hlast ↔ c ∈ cutSet C ∧ c ≠ m + 1 := by
  simp only [starts, Finset.mem_erase, and_comm]

theorem starts_mem_cut {c : ℕ} (hc : c ∈ starts C hlast) : c ∈ cutSet C :=
  ((mem_starts_iff (C := C) hlast).mp hc).1

theorem starts_ne_last {c : ℕ} (hc : c ∈ starts C hlast) : c ≠ m + 1 :=
  ((mem_starts_iff (C := C) hlast).mp hc).2

theorem starts_le {c : ℕ} (hc : c ∈ starts C hlast) : c ≤ m := by
  have h1 := cutSet_le (C := C) hlast (starts_mem_cut (C := C) hlast hc)
  have h2 := starts_ne_last (C := C) hlast hc
  omega

theorem starts_lt {c : ℕ} (hc : c ∈ starts C hlast) : c < m + 1 := by
  have := starts_le (C := C) hlast hc; omega

theorem zero_mem_starts : 0 ∈ starts C hlast := by
  rw [mem_starts_iff]
  exact ⟨zero_mem_cutSet, by omega⟩

noncomputable def blockLen (c : ℕ) (hc : c < m + 1) : ℕ :=
  nextCut (C := C) hlast ⟨c, hc⟩ - c

theorem blockLen_pos {c : ℕ} (hc : c < m + 1) : 0 < blockLen (C := C) hlast c hc := by
  unfold blockLen
  exact Nat.sub_pos_of_lt (nextCut_gt (C := C) hlast ⟨c, hc⟩)

theorem block_start_add_len {c : ℕ} (hc : c < m + 1) :
    c + blockLen (C := C) hlast c hc =
      nextCut (C := C) hlast ⟨c, hc⟩ := by
  unfold blockLen
  exact Nat.add_sub_of_le (le_of_lt (nextCut_gt (C := C) hlast ⟨c, hc⟩))

theorem block_len_le {c : ℕ} (hc : c < m + 1) :
    c + blockLen (C := C) hlast c hc ≤ m + 1 := by
  rw [block_start_add_len]
  exact cutSet_le (C := C) hlast (nextCut_mem (C := C) hlast ⟨c, hc⟩)

theorem blockStartNonempty (i : Fin (m + 1)) :
    ((cutSet C).filter (fun c => c ≤ i.val)).Nonempty := by
  refine ⟨0, Finset.mem_filter.mpr ⟨zero_mem_cutSet, by omega⟩⟩

noncomputable def blockStart (i : Fin (m + 1)) : ℕ :=
  ((cutSet C).filter (fun c => c ≤ i.val)).max' (blockStartNonempty (C := C) i)

theorem blockStart_mem_cut (i : Fin (m + 1)) : blockStart (C := C) i ∈ cutSet C := by
  have h := Finset.max'_mem ((cutSet C).filter (fun c => c ≤ i.val))
    (blockStartNonempty (C := C) i)
  simpa [blockStart] using (Finset.mem_filter.mp h).1

theorem blockStart_le (i : Fin (m + 1)) : blockStart (C := C) i ≤ i.val := by
  have h := Finset.max'_mem ((cutSet C).filter (fun c => c ≤ i.val))
    (blockStartNonempty (C := C) i)
  simpa [blockStart] using (Finset.mem_filter.mp h).2

theorem blockIndex_eq (i : Fin (m + 1)) :
    blockIndex C i = ((cutSet C).filter (fun c => c ≤ i.val)).card := rfl

theorem blockStart_lt (i : Fin (m + 1)) : blockStart (C := C) i < m + 1 :=
  lt_of_le_of_lt (blockStart_le (C := C) i) i.isLt

theorem blockStart_mem_starts (i : Fin (m + 1)) :
    blockStart (C := C) i ∈ starts C hlast := by
  rw [mem_starts_iff]
  refine ⟨blockStart_mem_cut (C := C) i, ?_⟩
  have := blockStart_le (C := C) i
  omega

theorem blockStart_lt_next (i : Fin (m + 1)) :
    i.val < nextCut (C := C) hlast ⟨blockStart (C := C) i, blockStart_lt (C := C) i⟩ := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmem : nextCut (C := C) hlast ⟨blockStart (C := C) i, blockStart_lt (C := C) i⟩ ∈
      (cutSet C).filter (fun c => c ≤ i.val) :=
    Finset.mem_filter.mpr ⟨nextCut_mem (C := C) hlast _, hcon⟩
  have hle : nextCut (C := C) hlast
      ⟨blockStart (C := C) i, blockStart_lt (C := C) i⟩ ≤ blockStart (C := C) i := by
    simpa [blockStart] using Finset.le_max' _ _ hmem
  have hgt := nextCut_gt (C := C) hlast ⟨blockStart (C := C) i, blockStart_lt (C := C) i⟩
  simp only [Fin.val_mk] at hle hgt
  omega

theorem blockStart_eq_of_mem {c : ℕ} (hc : c ∈ starts C hlast) {i : Fin (m + 1)}
    (hi1 : c ≤ i.val)
    (hi2 : i.val < nextCut (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩) :
    blockStart (C := C) i = c := by
  have hmem : c ∈ (cutSet C).filter (fun d => d ≤ i.val) :=
    Finset.mem_filter.mpr ⟨starts_mem_cut (C := C) hlast hc, hi1⟩
  have hcle : c ≤ blockStart (C := C) i := Finset.le_max' _ _ hmem
  by_contra hne
  have hlt : c < blockStart (C := C) i := lt_of_le_of_ne hcle (Ne.symm hne)
  have hmin := nextCut_min (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩
    (blockStart_mem_cut (C := C) i) hlt
  have hble := blockStart_le (C := C) i
  omega

theorem blockStart_ne_of_not_mem {c : ℕ} (hc : c ∈ starts C hlast) {i : Fin (m + 1)}
    (hi : i.val < c ∨
      nextCut (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩ ≤ i.val) :
    blockStart (C := C) i ≠ c := by
  rcases hi with hi | hi
  · have := blockStart_le (C := C) i; omega
  · have hmem : nextCut (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩ ∈
        (cutSet C).filter (fun d => d ≤ i.val) :=
      Finset.mem_filter.mpr ⟨nextCut_mem (C := C) hlast _, hi⟩
    have hle : nextCut (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩ ≤
        blockStart (C := C) i := by
      simpa [blockStart] using Finset.le_max' _ _ hmem
    have hgt := nextCut_gt (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩
    simp only [Fin.val_mk] at hle hgt
    omega

theorem blockIndex_eq_of_interval {c : ℕ} (hc : c ∈ starts C hlast)
    {i : Fin (m + 1)} (hi1 : c ≤ i.val)
    (hi2 : i.val < nextCut (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩) :
    blockIndex C ⟨c, starts_lt (C := C) hlast hc⟩ = blockIndex C i := by
  rw [blockIndex_eq, blockIndex_eq]
  congr 1
  apply Finset.ext
  intro d
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hd, hdi⟩
    have hcv : (⟨c, starts_lt (C := C) hlast hc⟩ : Fin (m + 1)).val = c := rfl
    exact ⟨hd, by omega⟩
  · rintro ⟨hd, hdi⟩
    refine ⟨hd, ?_⟩
    by_contra hdc
    rw [not_le] at hdc
    have hmin := nextCut_min (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩ hd (by omega)
    omega

theorem blockIndex_lt_of_cut {i j : Fin (m + 1)} {d : ℕ} (hd : d ∈ cutSet C)
    (hi : i.val < d) (hj : d ≤ j.val) : blockIndex C i < blockIndex C j := by
  rw [blockIndex_eq, blockIndex_eq]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, by omega⟩
  · intro hEq
    have hmem : d ∈ (cutSet C).filter (fun e => e ≤ j.val) :=
      Finset.mem_filter.mpr ⟨hd, hj⟩
    have : d ∈ (cutSet C).filter (fun e => e ≤ i.val) := by
      rw [hEq]; exact hmem
    rw [Finset.mem_filter] at this
    omega

theorem blockIndex_ne_of_not_interval {c : ℕ} (hc : c ∈ starts C hlast)
    {i : Fin (m + 1)} {j : Fin (m + 1)}
    (hj1 : c ≤ j.val)
    (hj2 : j.val < nextCut (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩)
    (hi : i.val < c ∨
      nextCut (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩ ≤ i.val) :
    blockIndex C i ≠ blockIndex C j := by
  rcases hi with hi | hi
  · have hlt := blockIndex_lt_of_cut (C := C) (d := c)
      (starts_mem_cut (C := C) hlast hc) hi hj1
    omega
  · have hlt := blockIndex_lt_of_cut (C := C) (d :=
      nextCut (C := C) hlast ⟨c, starts_lt (C := C) hlast hc⟩)
      (nextCut_mem (C := C) hlast _) hj2 hi
    omega


theorem nextCut_congr {c : ℕ} (h1 h2 : c < m + 1) :
    nextCut (C := C) hlast ⟨c, h1⟩ = nextCut (C := C) hlast ⟨c, h2⟩ := by
  congr 1

theorem blockLen_congr {c : ℕ} (h1 h2 : c < m + 1) :
    blockLen (C := C) hlast c h1 = blockLen (C := C) hlast c h2 := by
  unfold blockLen
  rw [nextCut_congr (C := C) hlast h1 h2]


abbrev blockKappa (C : Set (Fin (m + 1))) (hlast : Fin.last m ∉ C) :=
  {c : ℕ // c ∈ starts C hlast}

end ChainAssembly



theorem bcLin_suEndN_stdE_apply (s : SUid (unitaryInvolution K 2 1) (m + 1))
    (i j : Fin (m + 1)) :
    bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
        (stdE (K := K) (n := m + 1) j) (Sum.inl i) =
      (((s : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j) := by
  rw [bcLin_suEndN, blockDiag_inl]
  rw [show (fun j' => stdE (K := K) (n := m + 1) j (Sum.inl j')) =
      (Pi.single j (1 : K) : Fin (m + 1) → K) from by
    funext j'; simp [stdE, Pi.single_apply, Sum.inl.injEq]]
  rw [Matrix.mulVec_single_one, Matrix.col_apply]

theorem isKLinear_suEndN (s : SUid (unitaryInvolution K 2 1) (m + 1)) :
    ∀ (a : K) x,
      (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • x) =
      a • (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) x := by
  intro a x
  rw [suEndN_apply, suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def,
    CFSG.ClassicalGroups.Unitary.smul_def]
  exact Matrix.mulVec_smul _ _ _

theorem blockTriangular_of_fixes (hm : 3 ≤ m) (hlast : Fin.last m ∉ C)
    (s : SUid (unitaryInvolution K 2 1) (m + 1))
    (hfix : ∀ j ∉ C, (flagChamber E m j).1.map
      (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (flagChamber E m j).1) :
    (((s : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).BlockTriangular
      (blockIndex C) := by
  intro i j hij
  have hmemV : bcLin E (m + 1)
      (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
      (stdE (K := K) (n := m + 1) j) ∈ V (K := K) (m := m) (nextCut (C := C) hlast j) := by
    refine map_V_le_of_cut (E := E) (C := C) (by omega) hlast
      (⟨suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s,
        suEndN_mem_orthDerived E (by omega) s⟩ :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
      (isKLinear_suEndN (K := K) (m := m) s) hfix (nextCut_mem hlast j) ?_
    exact Submodule.mem_map_of_mem (stdE_mem_V (K := K) (m := m) (nextCut_gt hlast j))
  have hzero := V_apply_eq_zero (K := K) (m := m) hmemV
    (nextCut_le_of_blockIndex_lt hlast hij)
  rwa [bcLin_suEndN_stdE_apply] at hzero


theorem blockTriangular_inv_of_fixes (hm : 3 ≤ m) (hlast : Fin.last m ∉ C)
    (s : SUid (unitaryInvolution K 2 1) (m + 1))
    (hfix : ∀ j ∉ C, (flagChamber E m j).1.map
      (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (flagChamber E m j).1) :
    (((s⁻¹ : SUid (unitaryInvolution K 2 1) (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K).BlockTriangular (blockIndex C) := by
  have hfix_inv : ∀ j ∉ C, (flagChamber E m j).1.map
      (bcLin E (m + 1)
        (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s⁻¹ :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (flagChamber E m j).1 := by
    intro j hj
    have h := hfix j hj
    have h2 := map_bcLin_inv_map_bcLin E (m + 1)
      (⟨suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s,
        suEndN_mem_orthDerived E (by omega) s⟩ :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
      ((flagChamber E m j).1)
    rw [h] at h2
    rwa [show (⟨suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s,
        suEndN_mem_orthDerived E (by omega) s⟩ :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))⁻¹ =
        (⟨suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s⁻¹,
          suEndN_mem_orthDerived E (by omega) s⁻¹⟩ :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) from by
      apply Subtype.ext
      simp] at h2
  exact blockTriangular_of_fixes (E := E) (C := C) hm hlast s⁻¹ hfix_inv

theorem matrix_eq_zero_of_blockIndex_ne (hm : 3 ≤ m) (hlast : Fin.last m ∉ C)
    (s : SUid (unitaryInvolution K 2 1) (m + 1))
    (hfix : ∀ j ∉ C, (flagChamber E m j).1.map
      (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (flagChamber E m j).1)
    {i j : Fin (m + 1)} (hij : blockIndex C i ≠ blockIndex C j) :
    (((s : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j) = 0 := by
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((s : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have htri := blockTriangular_inv_of_fixes (E := E) (C := C) hm hlast s hfix
    have hzero := htri (i := j) (j := i) hlt
    have hunit : conjTr (unitaryInvolution K 2 1) A * A = 1 := s.2.2
    have hmul : A * conjTr (unitaryInvolution K 2 1) A = 1 := mul_eq_one_comm.mp hunit
    have hinv : A⁻¹ = conjTr (unitaryInvolution K 2 1) A := Matrix.inv_eq_right_inv hmul
    have hcoe : (((s⁻¹ : SUid (unitaryInvolution K 2 1) (m + 1)) : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) = A⁻¹ := by
      rw [show ((s⁻¹ : SUid (unitaryInvolution K 2 1) (m + 1)) : GL (Fin (m + 1)) K) =
          (s : GL (Fin (m + 1)) K)⁻¹ from rfl, Matrix.GeneralLinearGroup.coe_inv]
    rw [hcoe, hinv, conjTr_apply] at hzero
    exact (unitaryInvolution K 2 1).injective (by simpa using hzero)
  · exact blockTriangular_of_fixes (E := E) (C := C) hm hlast s hfix (i := i) (j := j) hgt



theorem isKLinear_of_mem_qTwoParab_of_last_not_mem
    (hlast : Fin.last m ∉ C)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : x ∈ qTwoParab E m C) :
    ∀ (a : K) v,
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • v) =
      a • (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v := by
  have hfix := (mem_qTwoParab (E := E) (m := m) (C := C)).mp hx (Fin.last m) hlast
  have hmap : (stdLag (m + 1) K).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
      stdLag (m + 1) K := by
    have h := (flagVert_smul_eq_iff (E := E) (m := m) x
      (flagChamber E m (Fin.last m))).mp hfix
    rwa [coe_flagChamber, stdDChamber_elt_last_eq_stdLag] at h
  exact (map_stdLag_bcLin_le_iff E (m + 1)
    (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))).mp (le_of_eq hmap)

theorem exists_diagHom_suEndN_eq_of_mem_qTwoParab_of_last_not_mem
    (hlast : Fin.last m ∉ C)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : x ∈ qTwoParab E m C) :
    ∃ (t : Fin (m + 1) → normOne (unitaryInvolution K 2 1))
      (s : SUid (unitaryInvolution K 2 1) (m + 1)),
      diagHom F (unitaryInvolution K 2 1) (m + 1) t *
        suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s =
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  exists_diagHom_mul_suEndN_eq E (by omega)
    (mem_orthogonalGroup_of_mem_orthDerived E (m + 1) x.2)
    (isKLinear_of_mem_qTwoParab_of_last_not_mem (E := E) (C := C) hlast hx)

open ChainAssembly in
theorem qTwoParab_prod_of_last_not_mem
    (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))}
    (hC : C ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1)))
    (hlast : Fin.last m ∉ C)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : x ∈ qTwoParab E m C) :
    ∃ t ∈ ⨆ i, qTwoTor E m hm i,
      ∃ l ∈ (qTwoStdFamily E hK m hm).levi C, x = t * l := by
  classical
  let σ := unitaryInvolution K 2 1
  obtain ⟨d0, s, hfac⟩ :=
    exists_diagHom_suEndN_eq_of_mem_qTwoParab_of_last_not_mem (E := E) (C := C) hlast hx
  have hdiag_mem : diagHom F σ (m + 1) d0 ∈ diagTorusV F σ (m + 1) := ⟨d0, rfl⟩
  have horth : diagHom F σ (m + 1) d0 ∈
      CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) :=
    diagTorusV_le_orthDerived E (by omega) hdiag_mem
  have hmap : diagHom F σ (m + 1) d0 ∈ Subgroup.map
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
      (⨆ i, qTwoTor E m hm i) := by
    rw [map_qTwoTor_iSup_eq_diagTorus E hK m hm]
    exact hdiag_mem
  obtain ⟨t0, ht0, ht0eq⟩ := Subgroup.mem_map.mp hmap
  have ht0empty : t0 ∈ qTwoParab E m ∅ := by
    have hdiagEmpty := diagHom_mem_qTwoParab_empty (E := E) hK hm d0
    have hsub : t0 = (⟨diagHom F σ (m + 1) d0, horth⟩ :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
      apply Subtype.ext
      exact ht0eq
    rw [hsub]
    exact hdiagEmpty
  have ht0C : t0 ∈ qTwoParab E m C :=
    qTwoParab_mono (E := E) (Set.empty_subset C) ht0empty
  let y : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
    ⟨suEndN (F := F) σ (m + 1) s, suEndN_mem_orthDerived E (by omega) s⟩
  have hx_eq : x = t0 * y := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    change x.1 = (t0 : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
      suEndN (F := F) σ (m + 1) s
    have ht0val : (↑t0 : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
        diagHom F σ (m + 1) d0 := ht0eq
    rw [ht0val]
    exact hfac.symm
  have hy : y ∈ qTwoParab E m C := by
    have hy_eq : y = t0⁻¹ * x := by
      rw [hx_eq]
      group
    rw [hy_eq]
    exact (qTwoParab E m C).mul_mem ((qTwoParab E m C).inv_mem ht0C) hx
  have hfix_s : ∀ j ∉ C, (flagChamber E m j).1.map
      (bcLin E (m + 1) (suEndN (F := F) σ (m + 1) s :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
      (flagChamber E m j).1 := by
    intro j hj
    have h := (mem_qTwoParab (E := E) (m := m) (C := C)).mp hy j hj
    simpa [y] using
      (flagVert_smul_eq_iff (E := E) (m := m) y (flagChamber E m j)).mp h
  letI : Fintype (blockKappa C hlast) := Finset.Subtype.fintype (starts C hlast)
  let k : blockKappa C hlast → ℕ := fun a =>
    blockLen (C := C) hlast a.1 (starts_lt (C := C) hlast a.2)
  let b : blockKappa C hlast → ℕ := fun a => a.1
  have hk : ∀ a, 0 < k a := fun a => blockLen_pos (C := C) hlast (starts_lt (C := C) hlast a.2)
  have hbk : ∀ a, b a + k a ≤ m + 1 := fun a =>
    block_len_le (C := C) hlast (starts_lt (C := C) hlast a.2)
  have hdisj : ∀ a c : blockKappa C hlast, a ≠ c →
      b a + k a ≤ b c ∨ b c + k c ≤ b a := by
    intro a c hne
    have hnac : a.1 ≠ c.1 := fun h => hne (Subtype.ext h)
    rcases lt_or_gt_of_ne hnac with hlt | hgt
    · left
      have h := nextCut_min (C := C) hlast
        ⟨a.1, starts_lt (C := C) hlast a.2⟩
        (starts_mem_cut (C := C) hlast c.2) (by simpa [b] using hlt)
      rwa [← block_start_add_len (C := C) hlast
        (starts_lt (C := C) hlast a.2)] at h
    · right
      have h := nextCut_min (C := C) hlast
        ⟨c.1, starts_lt (C := C) hlast c.2⟩
        (starts_mem_cut (C := C) hlast a.2) (by simpa [b] using hgt)
      rwa [← block_start_add_len (C := C) hlast
        (starts_lt (C := C) hlast c.2)] at h
  have hcover : ∀ j : Fin (m + 1), ∃ a : blockKappa C hlast,
      b a ≤ j.val ∧ j.val < b a + k a := by
    intro j
    let a : blockKappa C hlast :=
      ⟨blockStart (C := C) j, blockStart_mem_starts (C := C) hlast j⟩
    refine ⟨a, by simpa [b, a] using blockStart_le (C := C) j, ?_⟩
    rw [show b a + k a = nextCut (C := C) hlast
        ⟨a.1, starts_lt (C := C) hlast a.2⟩ from
      block_start_add_len (C := C) hlast (starts_lt (C := C) hlast a.2)]
    simpa [a] using blockStart_lt_next (C := C) hlast j
  have hCint : ∀ a : blockKappa C hlast, ∀ j : Fin (k a - 1),
      (⟨b a + j.val, by have hb := hbk a; have hj := j.isLt; omega⟩ :
        Fin (m + 1)) ∈ C := by
    intro a j
    by_contra hnot
    have hcut : a.1 + j.val + 1 ∈ cutSet C := by
      simpa [b] using succ_mem_cutSet (C := C) hnot
    have hgt : a.1 < a.1 + j.val + 1 := by omega
    have hlt : a.1 + j.val + 1 < nextCut (C := C) hlast
        ⟨a.1, starts_lt (C := C) hlast a.2⟩ := by
      have hj := j.isLt
      have hkpos : 0 < k a := hk a
      have hlen := block_start_add_len (C := C) hlast
        (starts_lt (C := C) hlast a.2)
      dsimp [k] at hj ⊢
      omega
    have hmin := nextCut_min (C := C) hlast
      ⟨a.1, starts_lt (C := C) hlast a.2⟩ hcut hgt
    omega
  let sM : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((s : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  have hoff : ∀ a : blockKappa C hlast, ∀ (i : Fin (m + 1)) (j : Fin (k a)),
      (i.val < b a ∨ b a + k a ≤ i.val) → sM i
        ⟨b a + j.val, by have hb := hbk a; have hj := j.isLt; omega⟩ = 0 := by
    intro a i j hi
    have hj1 : b a ≤ (⟨b a + j.val,
        by have hb := hbk a; have hj := j.isLt; omega⟩ : Fin (m + 1)).val := by
      simp [b]
    have hj2 : (⟨b a + j.val,
        by have hb := hbk a; have hj := j.isLt; omega⟩ : Fin (m + 1)).val <
        nextCut (C := C) hlast ⟨a.1, starts_lt (C := C) hlast a.2⟩ := by
      have hj := j.isLt
      have hlen := block_start_add_len (C := C) hlast
        (starts_lt (C := C) hlast a.2)
      simp only [Fin.val_mk]
      change b a + j.val < nextCut (C := C) hlast
        ⟨a.1, starts_lt (C := C) hlast a.2⟩
      dsimp [b, k] at hj ⊢
      omega
    have hi' : i.val < a.1 ∨
        nextCut (C := C) hlast ⟨a.1, starts_lt (C := C) hlast a.2⟩ ≤ i.val := by
      rcases hi with hi | hi
      · exact Or.inl (by simpa [b] using hi)
      · right
        have hlen := block_start_add_len (C := C) hlast
          (starts_lt (C := C) hlast a.2)
        dsimp [b, k] at hi
        omega
    have hne := blockIndex_ne_of_not_interval (C := C) hlast a.2 hj1 hj2 hi'
    simpa [sM] using
      matrix_eq_zero_of_blockIndex_ne (E := E) (C := C) hm hlast s hfix_s hne
  obtain ⟨t1, ht1, l, hl, hsu⟩ :=
    qTwo_su_prod_of_intervals (E := E) hK m hm (ι := blockKappa C hlast)
      k b hk hbk hdisj hcover hCint s hoff
  refine ⟨t0 * t1, (⨆ i, qTwoTor E m hm i).mul_mem ht0 ht1, l, hl, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  change x.1 = (t0 : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
    ((t1 : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
      (l : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))
  have ht0val : (↑t0 : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      diagHom F σ (m + 1) d0 := ht0eq
  rw [← hfac, ht0val, hsu]

end CFSG.ClassicalInvolution.PhanDn.QTwo
