module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentNode

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin

variable {n : ℕ} {F : Type} [Field F]

structure Shape1 (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (p : Fin n ⊕ Fin n) : Prop where
  delta : ∀ x y, ¬ ((x = p ∧ y ≠ p) ∨ (y = bar p ∧ x ≠ bar p)) → G x y = if x = y then 1 else 0
  symm : ∀ y, y ≠ p → y ≠ bar p → G p y = G (bar y) (bar p)

@[expose] noncomputable def cnt1 (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (p : Fin n ⊕ Fin n) : ℕ :=
  open Classical in
  (Finset.univ.filter fun y : Fin n ⊕ Fin n => y ≠ p ∧ y ≠ bar p ∧ G p y ≠ 0).card

variable {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} {p : Fin n ⊕ Fin n}

theorem shape1_of_cfg [CharP F 2] (hQ : ∀ v, Qf n (G.mulVec v) = Qf n v) (C : Cfg G {p}) :
    Shape1 G p := by
  classical
  have hp : p ∈ ({p} : Set (Fin n ⊕ Fin n)) := rfl
  have hmem : ∀ r, bar r ≠ p → r ≠ p → HM G p r := fun r h1 h2 =>
    C.hm p hp r (by simpa using h1) h2
  obtain ⟨r₁, r₂, h12, ⟨h1, h1'⟩, h2⟩ := C.two p hp
  have hl : G p p = 1 := C.lam_one_free hQ hp (r := r₁) h1 h1' (by simpa using h1') (by simpa using h1)
  have hmu : G (bar p) (bar p) = 1 := by
    have := C.lam_mu hQ hp
    rwa [hl, one_mul] at this
  have hT : ∀ r, r ≠ p → r ≠ bar p → G r r = 1 := fun r h1 h2 => by
    rw [C.diag_r hp (r := r) (by simpa [bar_ne] using (fun e : bar r = p => h2 (by rw [← e, bar_bar]))) h1, hmu]
  refine ⟨fun x y hxy => ?_, fun y h1 h2 => ?_⟩
  · by_cases hy : y = p
    · subst hy
      by_cases hx : x = y
      · subst hx; simp [hl]
      · rw [C.col_p_zero hp hx]; simp [hx]
    · by_cases hx : x = bar p
      · subst hx
        by_cases hy' : y = bar p
        · subst hy'; simp [hmu]
        · rw [C.row_bar_zero hp hy']
          simp [Ne.symm hy']
      · have hxp : x ≠ p := fun e => hxy (Or.inl ⟨e, hy⟩)
        have hyb : y ≠ bar p := fun e => hxy (Or.inr ⟨e, hx⟩)
        have hbar : bar y ≠ p := fun e => hyb (by rw [← e, bar_bar])
        have hc := (hmem y hbar hy).col_r (Ne.symm hy) x
        rw [hc, hmu]
        simp [hxp]
  · have hbar : bar y ≠ p := fun e => h2 (by rw [← e, bar_bar])
    have hc := (hmem y hbar h1).col_r (Ne.symm h1) p
    have h2' : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
    rw [hc]
    simp [Ne.symm h1]
    linear_combination (-G (bar y) (bar p)) * h2'

theorem mul_root_entry_gen {p q : Fin n ⊕ Fin n} {c : F}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hX : ∀ z y, X z y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) z y +
      (if z = p ∧ y = bar q then c else 0) - (if z = q ∧ y = bar p then c else 0)) (x y : Fin n ⊕ Fin n) :
    (G * X) x y = G x y + G x p * (if y = bar q then c else 0) -
      G x q * (if y = bar p then c else 0) := by
  simp only [Matrix.mul_apply, hX, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem peel_shape1 [CharP F 2] (hS : Shape1 G p) {r : Fin n ⊕ Fin n} (hr1 : r ≠ p)
    (hr2 : r ≠ bar p) (hc : G p (bar r) ≠ 0) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hX : ∀ z y, X z y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) z y +
      (if z = p ∧ y = bar r then -G p (bar r) else 0) -
        (if z = r ∧ y = bar p then -G p (bar r) else 0)) :
    Shape1 (G * X) p ∧ cnt1 (G * X) p < cnt1 G p := by
  classical
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have hpb : p ≠ bar p := fun e => bar_ne p e.symm
  have hbr1 : bar r ≠ p := fun e => hr2 (by rw [← e, bar_bar])
  have hbr2 : bar r ≠ bar p := fun e => hr1 (bar_inj.mp e)
  have hcp : ∀ x, G x p = if x = p then 1 else 0 := fun x =>
    hS.delta x p (by simp [hpb])
  have hcr : ∀ x, x ≠ p → G x r = if x = r then 1 else 0 := fun x hx =>
    hS.delta x r (by simp [hx, hr2])
  have hE := mul_root_entry_gen (G := G) (p := p) (q := r) (c := -G p (bar r)) X hX
  have hrow : ∀ y, y ≠ bar p → (G * X) p y = G p y + (if y = bar r then -G p (bar r) else 0) := by
    intro y hy
    rw [hE, hcp p]
    simp [hy]
  have hbar_iff : ∀ y, bar y = r ↔ y = bar r := fun y =>
    ⟨fun h => by rw [← h, bar_bar], fun h => by rw [h, bar_bar]⟩
  have hcol : ∀ y, y ≠ bar p → (G * X) (bar y) (bar p) =
      G (bar y) (bar p) - (if y = bar r then -G p (bar r) else 0) := by
    intro y hy
    have hby : bar y ≠ p := fun e => hy (by rw [← e, bar_bar])
    rw [hE, hcp (bar y), hcr (bar y) hby]
    simp [hbr2.symm, hby, hbar_iff]
    split_ifs <;> ring
  refine ⟨⟨fun x y hxy => ?_, fun y h1 h3 => ?_⟩, ?_⟩
  · have t1 : ¬ (x = p ∧ y = bar r) := fun h => hxy (Or.inl ⟨h.1, h.2 ▸ hbr1⟩)
    have t2 : y = bar p → G x r = 0 := fun hy => by
      have hxb : x = bar p := by
        by_contra hne
        exact hxy (Or.inr ⟨hy, hne⟩)
      rw [hcr x (by rw [hxb]; exact Ne.symm hpb)]
      simp [hxb, Ne.symm hr2]
    rw [hE, hS.delta x y hxy, hcp x]
    by_cases hy : y = bar p
    · rw [t2 hy]
      simp [hy, hbr2.symm]
    · simp only [hy, ite_false, mul_zero, sub_zero]
      by_cases hx : x = p
      · by_cases hy' : y = bar r
        · exact absurd ⟨hx, hy'⟩ t1
        · simp [hx, hy']
      · simp [hx]
  · rw [hrow y h3, hcol y h3, hS.symm y h1 h3]
    by_cases h : y = bar r
    · simp only [if_pos h]
      linear_combination (-G p (bar r)) * h2
    · simp [h]
  · refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨bar r, ?_, ?_⟩
      · simp [hbr1, hbr2, hc]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
        intro _ _
        rw [hrow _ hbr2]
        simp
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨hy1, hy2, hy3⟩ := hy
      refine ⟨hy1, hy2, fun h0 => hy3 ?_⟩
      rw [hrow y hy2, h0]
      by_cases hh : y = bar r
      · exact absurd (hh ▸ h0) hc
      · simp [hh]

theorem hQ_spinMat_gen (k : spinGroup (quadPlus n F)) :
    ∀ v, Qf n ((spinMat (quadPlus n F) k).mulVec v) = Qf n v := fun v => by
  have := spinMatrix_mem (quadPlus n F) k v
  rw [spinMat_eq_coe]
  simpa [Qf, quadPlus_apply] using this

theorem Qf_single' (q : Fin n ⊕ Fin n) (c : F) : Qf n (Pi.single q c) = 0 := by
  unfold Qf
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : Sum.inl i = q
  · subst h; simp
  · simp [Pi.single_apply, Ne.symm h]

theorem lift1_mem [CharP F 2] (hn : 3 ≤ n) (R : Subgroup (spinGroup (quadPlus n F))) (a0 : Fin n)
    (σ0 : Bool)
    (hroot : ∀ b t, ∀ hab : a0 ≠ b, ∀ c : F,
      (plusFrame n F hn).longRoot hab σ0 t (Multiplicative.ofAdd c) ∈ R) :
    ∀ (N : ℕ) (k : spinGroup (quadPlus n F)),
      Shape1 (spinMat (quadPlus n F) k) (kap a0 σ0) →
      cnt1 (spinMat (quadPlus n F) k) (kap a0 σ0) = N →
      k ∈ R ⊔ Subgroup.center (spinGroup (quadPlus n F)) := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k hS hN
    set p := kap a0 σ0 with hp
    have hpb : p ≠ bar p := fun e => bar_ne p e.symm
    by_cases hN0 : N = 0
    · subst hN0
      have hz : ∀ y, y ≠ p → y ≠ bar p → spinMat (quadPlus n F) k p y = 0 := by
        intro y h1 h2
        by_contra hne
        unfold cnt1 at hN
        have : y ∈ Finset.univ.filter fun y : Fin n ⊕ Fin n =>
            y ≠ p ∧ y ≠ bar p ∧ spinMat (quadPlus n F) k p y ≠ 0 := by simp [h1, h2, hne]
        rw [Finset.card_eq_zero] at hN
        simp [hN] at this
      have hz' : ∀ z, z ≠ p → z ≠ bar p → spinMat (quadPlus n F) k z (bar p) = 0 := by
        intro z h1 h2
        have := hS.symm (bar z) (fun e => h2 (by rw [← e, bar_bar])) (fun e => h1 (bar_inj.mp e))
        rw [bar_bar] at this
        rw [← this]
        exact hz _ (fun e => h2 (by rw [← e, bar_bar])) (fun e => h1 (bar_inj.mp e))
      have hX0 : spinMat (quadPlus n F) k p (bar p) = 0 := by
        have hQ := hQ_spinMat_gen k (Pi.single (bar p) 1)
        have hc : (spinMat (quadPlus n F) k).mulVec (Pi.single (bar p) (1 : F)) =
            Pi.single (bar p) 1 + Pi.single p (spinMat (quadPlus n F) k p (bar p)) := by
          ext z
          have e1 : (spinMat (quadPlus n F) k).mulVec (Pi.single (bar p) (1 : F)) z =
              spinMat (quadPlus n F) k z (bar p) := by simp [Matrix.mulVec, dotProduct, Pi.single_apply]
          rw [e1, Pi.add_apply]
          by_cases hz1 : z = p
          · subst hz1
            simp [Pi.single_apply, hpb]
          · by_cases hz2 : z = bar p
            · subst hz2
              rw [hS.delta _ _ (by simp [hpb.symm])]
              simp [Pi.single_apply, hz1]
            · rw [hz' z hz1 hz2]
              simp [Pi.single_apply, hz1, hz2]
        rw [hc, Qf_add, Qf_single, Qf_single', Bf_single_left, bar_bar] at hQ
        simpa [Pi.single_apply] using hQ
      have h1 : spinMat (quadPlus n F) k = 1 := by
        ext x y
        by_cases hB : (x = p ∧ y ≠ p) ∨ (y = bar p ∧ x ≠ bar p)
        · rcases hB with ⟨hx, hy⟩ | ⟨hy, hx⟩
          · rw [hx]
            by_cases hy' : y = bar p
            · rw [hy', hX0]
              simp [Matrix.one_apply, hpb]
            · rw [hz y hy hy']
              simp [Matrix.one_apply, Ne.symm hy]
          · rw [hy]
            by_cases hx' : x = p
            · rw [hx', hX0]
              simp [Matrix.one_apply, hpb]
            · rw [hz' x hx' hx]
              simp [Matrix.one_apply, hx]
        · rw [hS.delta x y hB]
          simp [Matrix.one_apply]
      have h2 := spinAction_eq_one_of_spinMat_eq_one h1
      exact Subgroup.mem_sup_right (ker_spinAction_le_center (quadPlus n F) h2)
    ·
      have hpos : 0 < cnt1 (spinMat (quadPlus n F) k) p := by omega
      unfold cnt1 at hpos
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨hy1, hy2, hy3⟩ := hy
      obtain ⟨b, t, hrbt⟩ := kap_surj (bar y)
      have hr1 : bar y ≠ p := fun e => hy2 (by rw [← e, bar_bar])
      have hr2 : bar y ≠ bar p := fun e => hy1 (bar_inj.mp e)
      have hab : a0 ≠ b := by
        intro h
        subst h
        have e1 : kap a0 t ≠ kap a0 σ0 := by rw [← hrbt]; exact hr1
        have e2 : kap a0 t ≠ kap a0 (!σ0) := by
          rw [← hrbt]
          have := hr2
          rwa [hp, bar_kap] at this
        by_cases ht : t = σ0
        · exact e1 (by rw [ht])
        · exact e2 (by cases t <;> cases σ0 <;> simp_all)
      have hy' : y = kap b (!t) := by rw [← bar_kap, ← hrbt, bar_bar]
      have hc : spinMat (quadPlus n F) k p (bar (bar y)) ≠ 0 := by rwa [bar_bar]
      set c' := -spinMat (quadPlus n F) k p (bar (bar y)) with hc'
      have hX : ∀ z w, spinMat (quadPlus n F)
          ((plusFrame n F hn).longRoot hab σ0 t (Multiplicative.ofAdd c')) z w =
          (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) z w +
          (if z = p ∧ w = bar (bar y) then -spinMat (quadPlus n F) k p (bar (bar y)) else 0) -
          (if z = bar y ∧ w = bar p then -spinMat (quadPlus n F) k p (bar (bar y)) else 0) := by
        intro z w
        have e1 : bar (bar y) = kap b (!t) := by rw [bar_bar, hy']
        have e3 : bar p = kap a0 (!σ0) := by rw [hp, bar_kap]
        rw [(isCoord_plusFrame' (F := F) hn).spinMat_longRoot hab σ0 t c' z w, e1, hrbt, e3]
        simp only [hc', e1]
        rfl
      obtain ⟨hS', hlt⟩ := peel_shape1 hS hr1 hr2 hc _ hX
      rw [← map_mul] at hS' hlt
      have key := ih _ (by omega) _ hS' rfl
      have hk : k = (k * (plusFrame n F hn).longRoot hab σ0 t (Multiplicative.ofAdd c')) *
          ((plusFrame n F hn).longRoot hab σ0 t (Multiplicative.ofAdd c'))⁻¹ :=
        (mul_inv_cancel_right _ _).symm
      rw [hk]
      exact Subgroup.mul_mem _ key (Subgroup.inv_mem _ (Subgroup.mem_sup_left (hroot b t hab c')))

theorem mem_radical_sup_center_of_comm_one {m : ℕ} [CharP F 2] (hn : 3 ≤ m + 3) (j : Fin (m + 3))
    (a0 : Fin (m + 3)) (ha0 : a0 ∈ nodeA (m + 3) j) (hA1 : ∀ b ∈ nodeA (m + 3) j, b = a0)
    (k : spinGroup (quadPlus (m + 3) F))
    (hk : ∀ u ∈ CFSG.AGLEmbedding.LieOut.radical (plusDatum (m + 3) F hn) j, k * u = u * k) :
    k ∈ CFSG.AGLEmbedding.LieOut.radical (plusDatum (m + 3) F hn) j ⊔
      Subgroup.center (spinGroup (quadPlus (m + 3) F)) := by
  classical
  have hP : pSet (nodeA (m + 3) j) (nodeSign (m + 3) j) =
      {kap a0 (nodeSign (m + 3) j a0)} := by
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hA1 a ha]
      rfl
    · rintro rfl
      exact ⟨a0, ha0, rfl⟩
  have C := cfg_node hn j k hk
  rw [hP] at C
  have hS := shape1_of_cfg (hQ_spinMat k) C
  exact lift1_mem hn _ a0 (nodeSign (m + 3) j a0)
    (fun b t hab c => longRoot_mem_radical hn j hab t ha0
      (Or.inl fun hb => hab (hA1 b hb).symm) c) _ k hS rfl

end CFSG.HardMathSupport.Cooperstein.StructureLie
