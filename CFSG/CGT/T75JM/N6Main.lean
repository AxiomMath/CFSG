module

public import CFSG.CGT.T75JM.N6Sem6
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable

variable {G : Type*} [Group G] {T : Subgroup G}

theorem exists_coords (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hsq : ∀ a ∈ T, a ^ 2 = 1)
    (h16 : Nat.card T = 16) : Nonempty (Coords T) := by
  have : Finite T := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := T) (n := 4)
    (fun a b => Subtype.ext (hcomm a a.2 b b.2)) (fun a => Subtype.ext (hsq a a.2))
    (by rw [h16]; norm_num)
  exact ⟨Coords.ofEquiv e⟩

theorem cols_ext {A B : Cols} (h : ∀ i : Fin 4, applyC A (2 ^ i.val) = applyC B (2 ^ i.val)) :
    A = B := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  rw [applyC_basis, applyC_basis] at h0 h1 h2 h3
  obtain ⟨a0, a1, a2, a3⟩ := A
  obtain ⟨b0, b1, b2, b3⟩ := B
  simp only [Cols.col] at h0 h1 h2 h3
  simp [h0, h1, h2, h3]

theorem card_a6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

@[expose] def tGen (i : Fin 4) : PG 6 rels6 := PresentedGroup.of (⟨2 + i.val, by omega⟩ : Fin 6)

theorem exists_mulEquiv_normalizer (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hsq : ∀ a ∈ T, a ^ 2 = 1) (h16 : Nat.card T = 16)
    (hC : Subgroup.centralizer (T : Set G) = T) (φ : NQ T ≃* alternatingGroup (Fin 6))
    (hmod : ModClass) (hnodup : A6Nodup)
    (hcard : Finite (PG 6 rels6) ∧ Nat.card (PG 6 rels6) ≤ 5760) :
    ∃ Ψ : PG 6 rels6 ≃* Subgroup.normalizer (T : Set G),
      Subgroup.map Ψ.toMonoidHom (Subgroup.closure (Set.range tGen)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
  classical
  obtain ⟨c⟩ := exists_coords hcomm hsq h16
  obtain ⟨a, b, ⟨hr1, hr2, hr3, hr4⟩, hcl, hequiv⟩ := branch_data c hC φ hmod hnodup
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
  rw [colsQ_mk, colsQ_mk] at hequiv
  obtain ⟨Q, Qi, hQ⟩ := hequiv
  set c' := c.change Q Qi hQ.1 hQ.2.1 (fun v hv => hQ.left_inv hv) (fun v hv => hQ.right_inv hv)
    with hc'
  have hgX : colsOf c' g = modelX := by
    apply cols_ext
    intro i
    have h2i : 2 ^ i.val < 16 := by fin_cases i <;> decide
    rw [colsOf_change c Q Qi hQ.1 hQ.2.1 (fun v hv => hQ.left_inv hv) (fun v hv => hQ.right_inv hv)
      g _ h2i, hQ.intertwine_x, hQ.left_inv (applyC_lt modelX_lt _)]
  have hhY : colsOf c' h = modelY := by
    apply cols_ext
    intro i
    have h2i : 2 ^ i.val < 16 := by fin_cases i <;> decide
    rw [colsOf_change c Q Qi hQ.1 hQ.2.1 (fun v hv => hQ.left_inv hv) (fun v hv => hQ.right_inv hv)
      h _ h2i, hQ.intertwine_y, hQ.left_inv (applyC_lt modelY_lt _)]
  set Tn := T.subgroupOf (Subgroup.normalizer (T : Set G)) with hTn
  have memT : ∀ w : List ℕ, evalG (QuotientGroup.mk g : NQ T) (QuotientGroup.mk h) w = 1 →
      ∃ t : T, ((evalG g h w : Subgroup.normalizer (T : Set G)) : G) = (t : G) := by
    intro w hw
    have h1 : (QuotientGroup.mk (evalG g h w) : NQ T) = 1 :=
      (evalG_map (QuotientGroup.mk' Tn) g h w).symm.trans hw
    rw [QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨_, h1⟩, rfl⟩
  obtain ⟨t1, ht1⟩ := memT wordR1 hr1
  obtain ⟨t2, ht2⟩ := memT wordR2 hr2
  obtain ⟨t3, ht3⟩ := memT wordR3 hr3
  obtain ⟨t4, ht4⟩ := memT wordR4 hr4
  obtain ⟨a, b, k1, k2, k3, k4⟩ := exists_adjust c' g h hgX hhY t1 t2 t3 t4
    ((evalG_coe _ g h _).symm.trans ht1) ((evalG_coe _ g h _).symm.trans ht2)
    ((evalG_coe _ g h _).symm.trans ht3) ((evalG_coe _ g h _).symm.trans ht4)
  set g' : Subgroup.normalizer (T : Set G) := g * inN a with hg'
  set h' : Subgroup.normalizer (T : Set G) := h * inN b with hh'
  have R : ∀ w, evalG ((g : G) * a) ((h : G) * b) w = 1 → evalG g' h' w = 1 := by
    intro w hw
    apply Subtype.ext
    rw [evalG_coe]
    exact hw
  have hg'X : colsOf c' g' = modelX := by
    rw [hg', colsOf_mul, colsOf_of_mem c' (inN a) a.2, compC_idC, hgX]
  have hh'Y : colsOf c' h' = modelY := by
    rw [hh', colsOf_mul, colsOf_of_mem c' (inN b) b.2, compC_idC, hhY]
  have hsem := sem6_of_data c' g' h' hg'X hh'Y (R _ k1) (R _ k2) (R _ k3) (R _ k4)
  set f : Fin 6 → Subgroup.normalizer (T : Set G) :=
    ![g', h', tN c' 0, tN c' 1, tN c' 2, tN c' 3] with hf
  let Φ : PG 6 rels6 →* Subgroup.normalizer (T : Set G) :=
    PresentedGroup.toGroup (f := f) fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      exact lift_rels6_eq_one hsem w hw
  have hmem : ∀ j : Fin 6, f j ∈ Φ.range := fun j => ⟨PresentedGroup.of j,
    PresentedGroup.toGroup.of _⟩
  set S := Subgroup.map Φ (Subgroup.closure (Set.range tGen)) with hS
  have hSt : ∀ j : Fin 4, f ⟨2 + j.val, by omega⟩ ∈ S := fun j =>
    ⟨tGen j, Subgroup.subset_closure ⟨j, rfl⟩, PresentedGroup.toGroup.of _⟩
  have hpart : ∀ (b : Bool) (n : ℕ), (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) →
      inN (tOf c' (if b then n else 0)) ∈ S := by
    intro b n hn
    cases b
    · simp only [Bool.false_eq_true, ite_false, tOf_zero c']
      exact S.one_mem
    · simp only [ite_true]
      rcases hn with rfl | rfl | rfl | rfl
      · exact hSt 0
      · exact hSt 1
      · exact hSt 2
      · exact hSt 3
  have hT : ∀ t : T, inN t ∈ S := by
    intro t
    rw [decomp c' t]
    simp only [← inN_mul]
    refine S.mul_mem (S.mul_mem (hpart _ _ (by simp)) (hpart _ _ (by simp)))
      (S.mul_mem (hpart _ _ (by simp)) (hpart _ _ (by simp)))
  have hSR : S ≤ Φ.range := Subgroup.map_le_range _ _
  have hsurj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro x _
    have hx : (QuotientGroup.mk x : NQ T) ∈ Subgroup.map (QuotientGroup.mk' Tn) Φ.range := by
      have hle : Subgroup.closure ({(QuotientGroup.mk g : NQ T), QuotientGroup.mk h} :
          Set (NQ T)) ≤ Subgroup.map (QuotientGroup.mk' Tn) Φ.range := by
        rw [Subgroup.closure_le]
        rintro q (rfl | rfl)
        · refine ⟨g', hmem 0, ?_⟩
          show (QuotientGroup.mk (g * inN a) : NQ T) = QuotientGroup.mk g
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (inN a)).2 a.2, mul_one]
        · refine ⟨h', hmem 1, ?_⟩
          show (QuotientGroup.mk (h * inN b) : NQ T) = QuotientGroup.mk h
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (inN b)).2 b.2, mul_one]
      rw [hcl] at hle
      exact hle (Subgroup.mem_top _)
    obtain ⟨r, hr, hrx⟩ := hx
    have hmem2 : r⁻¹ * x ∈ Tn := QuotientGroup.eq.1 hrx
    have hxr : x = r * inN (⟨((r⁻¹ * x : Subgroup.normalizer (T : Set G)) : G), hmem2⟩ : T) := by
      apply Subtype.ext
      simp [inN]
    rw [hxr]
    exact Φ.range.mul_mem hr (hSR (hT _))
  have hcardN : Nat.card (Subgroup.normalizer (T : Set G)) = 5760 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Tn]
    have hq : Nat.card (NQ T) = 360 := (Nat.card_congr φ.toEquiv).trans card_a6
    have ht : Nat.card Tn = 16 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv).trans h16
    rw [hq, ht]
  have hfinN : Finite (Subgroup.normalizer (T : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardN]; norm_num)
  obtain ⟨hfin, hle⟩ := hcard
  have hbij : Function.Bijective Φ := hsurj.bijective_of_nat_card_le (by rw [hcardN]; exact hle)
  refine ⟨MulEquiv.ofBijective Φ hbij, ?_⟩
  show S = Tn
  refine le_antisymm ?_ ?_
  · rw [hS, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have h0 : Φ (tGen i) = f ⟨2 + i.val, by omega⟩ := PresentedGroup.toGroup.of _
    have h1 : f ⟨2 + i.val, by omega⟩ = tN c' i.val := by fin_cases i <;> rfl
    show Φ (tGen i) ∈ Tn
    rw [h0, h1]
    exact (tOf c' (2 ^ i.val)).2
  · intro x hx
    have : x = inN (⟨(x : G), hx⟩ : T) := Subtype.ext rfl
    rw [this]
    exact hT _

end CFSG.CGT.T75JM
