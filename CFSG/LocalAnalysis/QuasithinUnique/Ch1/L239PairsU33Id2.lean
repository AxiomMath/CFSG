module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Id

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.U33

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.ClassicalGroups.UnitaryFlag

open scoped commutatorElement

variable {F : Type} [Field F] {hF : Nat.card F = 9} {d : Idata F}

variable (hF)

@[expose] def diagSub : Subgroup (StatedSU 3 3 F) where
  carrier := {g | ∀ j k : Fin 3, j ≠ k → ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j k = 0}
  one_mem' := fun j k hjk => by
    simp [hjk]
  mul_mem' := fun {a b} ha hb j k hjk => by
    rw [coe_mul_matrix, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = j
    · subst hl
      rw [hb _ _ hjk, mul_zero]
    · rw [ha _ _ (Ne.symm hl), zero_mul]
  inv_mem' := fun {a} ha j k hjk => by
    have hinv : (((a⁻¹ : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (· ^ 3))ᵀ := by
      have hmem : (a : GL (Fin 3) F) ∈ (StatedSU 3 3 F : Set (GL (Fin 3) F)) := a.2
      rw [coe_statedSU hF] at hmem
      have h1 := hmem.1
      have h2 : (((a⁻¹ : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
        rw [← coe_mul_matrix, inv_mul_cancel]
        rfl
      exact Matrix.left_inv_eq_left_inv h2 h1
    rw [hinv]
    simp [ha _ _ hjk.symm]

variable {hF}

variable (hF d)

@[expose] noncomputable def A0 : Subgroup (StatedSU 3 3 F) :=
  Subgroup.closure {sEl hF d, tEl hF d}

variable {hF d}

theorem sEl_mem_A0 : sEl hF d ∈ A0 hF d := Subgroup.subset_closure (Set.mem_insert _ _)

theorem tEl_mem_A0 : tEl hF d ∈ A0 hF d :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem A0_le_S0 : A0 hF d ≤ S0 hF d := Subgroup.closure_mono fun x hx => by
  rcases hx with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem sEl_diag : sEl hF d ∈ diagSub hF := fun j k hjk => by
  rw [coe_sEl]
  fin_cases j <;> fin_cases k <;> first | exact absurd rfl hjk | simp [sM]

theorem tEl_diag : tEl hF d ∈ diagSub hF := fun j k hjk => by
  rw [coe_tEl]
  fin_cases j <;> fin_cases k <;> first | exact absurd rfl hjk | simp [tM]

theorem wEl_not_diag : wEl hF ∉ diagSub hF := fun h => by
  have := h 1 2 (by decide)
  simp [coe_wEl, wM] at this

theorem A0_commute {x y : StatedSU 3 3 F} (hx : x ∈ A0 hF d) (hy : y ∈ A0 hF d) : x * y = y * x := by
  have hs : ∀ x ∈ A0 hF d, Commute (sEl hF d) x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact Commute.refl _
      · exact sEl_mul_tEl_comm
    | one => exact Commute.one_right _
    | mul y z _ _ ihy ihz => exact ihy.mul_right ihz
    | inv y _ ih => exact ih.inv_right
  have ht : ∀ x ∈ A0 hF d, Commute (tEl hF d) x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact sEl_mul_tEl_comm.symm
      · exact Commute.refl _
    | one => exact Commute.one_right _
    | mul y z _ _ ihy ihz => exact ihy.mul_right ihz
    | inv y _ ih => exact ih.inv_right
  have hxy : ∀ x ∈ A0 hF d, Commute x y := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact hs y hy
      · exact ht y hy
    | one => exact Commute.one_left _
    | mul a b _ _ iha ihb => exact iha.mul_left ihb
    | inv a _ ih => exact ih.inv_left
  exact hxy x hx

theorem wEl_conj_s' : wEl hF * sEl hF d * (wEl hF)⁻¹ = tEl hF d := by
  have h := wEl_conj_sEl (hF := hF) (d := d)
  rw [wEl_inv] at h ⊢
  exact h

theorem wEl_conj_t' : wEl hF * tEl hF d * (wEl hF)⁻¹ = sEl hF d := by
  have h := wEl_conj_tEl (hF := hF) (d := d)
  rw [wEl_inv] at h ⊢
  exact h

theorem A0_conj_w {x : StatedSU 3 3 F} (hx : x ∈ A0 hF d) : wEl hF * x * (wEl hF)⁻¹ ∈ A0 hF d := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [wEl_conj_s']
      exact tEl_mem_A0
    · rw [wEl_conj_t']
      exact sEl_mem_A0
  | one => simp
  | mul y z _ _ ihy ihz =>
    rw [show wEl hF * (y * z) * (wEl hF)⁻¹ = (wEl hF * y * (wEl hF)⁻¹) * (wEl hF * z * (wEl hF)⁻¹)
      by group]
    exact (A0 hF d).mul_mem ihy ihz
  | inv y _ ih =>
    rw [show wEl hF * y⁻¹ * (wEl hF)⁻¹ = (wEl hF * y * (wEl hF)⁻¹)⁻¹ by group]
    exact (A0 hF d).inv_mem ih

theorem S0_le_normalizer_A0 : S0 hF d ≤ Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F)) := by
  rw [S0, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact Subgroup.le_normalizer sEl_mem_A0
  · exact Subgroup.le_normalizer tEl_mem_A0
  · refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => A0_conj_w hx, fun hx => ?_⟩
    have := A0_conj_w hx
    have e : wEl hF * (wEl hF * x * (wEl hF)⁻¹) * (wEl hF)⁻¹ = x := by
      have h1 : wEl hF * wEl hF = 1 := wEl_mul_self
      calc wEl hF * (wEl hF * x * (wEl hF)⁻¹) * (wEl hF)⁻¹ =
          (wEl hF * wEl hF) * x * ((wEl hF)⁻¹ * (wEl hF)⁻¹) := by group
        _ = x := by rw [h1, wEl_inv, h1]; group
    rwa [e] at this

theorem commutator_le_A0 : ⁅S0 hF d, S0 hF d⁆ ≤ A0 hF d := by
  have hnorm : ((A0 hF d).subgroupOf (S0 hF d)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer A0_le_S0).2 S0_le_normalizer_A0
  let w' : ↥(S0 hF d) := ⟨wEl hF, wEl_mem_S0⟩
  have hsup : ((A0 hF d).subgroupOf (S0 hF d)) ⊔ Subgroup.zpowers w' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (show (⟨sEl hF d, sEl_mem_S0⟩ : ↥(S0 hF d)) ∈
          (A0 hF d).subgroupOf (S0 hF d) from sEl_mem_A0)
      · exact Subgroup.mem_sup_left (show (⟨tEl hF d, tEl_mem_S0⟩ : ↥(S0 hF d)) ∈
          (A0 hF d).subgroupOf (S0 hF d) from tEl_mem_A0)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w')
    | one => exact Subgroup.one_mem _
    | mul y z hy hz ihy ihz => exact Subgroup.mul_mem _ ihy ihz
    | inv y hy ih => exact Subgroup.inv_mem _ ih
  have hcomm : IsMulCommutative (Subgroup.zpowers w') := inferInstance
  have h := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hcomm
  refine Subgroup.commutator_le.2 fun g hg h' hh => ?_
  have h1 : (⁅(⟨g, hg⟩ : ↥(S0 hF d)), ⟨h', hh⟩⁆ : ↥(S0 hF d)) ∈ commutator ↥(S0 hF d) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact h h1

theorem tEl_mul_inv_sEl_matrix :
    (((tEl hF d * (sEl hF d)⁻¹ : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![1, -d.i, d.i] := by
  have hi := d.sq
  have h3 := d.three
  rw [coe_mul_matrix, coe_tEl, coe_inv_sEl]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [tM, sM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem canA_eq_A0 : canA (S0 hF d) = A0 hF d := by
  apply le_antisymm
  · rintro g ⟨hgS, hgc⟩
    have hcomm : ⁅wEl hF, sEl hF d⁆ ∈ ⁅S0 hF d, S0 hF d⁆ :=
      Subgroup.commutator_mem_commutator wEl_mem_S0 sEl_mem_S0
    have hcw : ⁅wEl hF, sEl hF d⁆ = tEl hF d * (sEl hF d)⁻¹ := by
      rw [commutatorElement_def, wEl_conj_s']
    rw [hcw] at hcomm
    have h1 : (tEl hF d * (sEl hF d)⁻¹) * g = g * (tEl hF d * (sEl hF d)⁻¹) :=
      Subgroup.mem_centralizer_iff.1 hgc _ hcomm
    have hM : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![1, -d.i, d.i] =
        diagonal ![1, -d.i, d.i] * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have := congrArg (fun x : StatedSU 3 3 F => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
      rw [coe_mul_matrix (tEl hF d * (sEl hF d)⁻¹) g, coe_mul_matrix g (tEl hF d * (sEl hF d)⁻¹),
        tEl_mul_inv_sEl_matrix] at this
      exact this.symm
    obtain ⟨h01, h02, h10, h12, h20, h21⟩ := offdiag_zero_of_commute_diagonal
      (neg_i_ne_one d).symm (i_ne_one d).symm (neg_i_ne_i d) hM
    have hgd : g ∈ diagSub hF := fun j k hjk => by
      fin_cases j <;> fin_cases k <;> first | exact absurd rfl hjk | assumption
    have hwg : g ∈ Subgroup.closure {sEl hF d, tEl hF d, wEl hF} := hgS
    obtain ⟨a, b, e, he, hge⟩ := CFSG.LieType.Steinberg.exists_zpow_mul_zpow_mul_pow
      (u := sEl hF d) (v := tEl hF d) (t := wEl hF) sEl_mul_tEl_comm (wEl_conj_sEl).symm
      (by rw [pow_two]; exact wEl_mul_self) hwg
    interval_cases e
    · rw [hge, pow_zero, mul_one]
      exact (A0 hF d).mul_mem (zpow_mem sEl_mem_A0 a) (zpow_mem tEl_mem_A0 b)
    · exfalso
      have hd : (sEl hF d ^ a * tEl hF d ^ b)⁻¹ ∈ diagSub hF :=
        (diagSub hF).inv_mem ((diagSub hF).mul_mem (zpow_mem sEl_diag a) (zpow_mem tEl_diag b))
      have hw : (sEl hF d ^ a * tEl hF d ^ b)⁻¹ * g = wEl hF := by
        rw [hge, pow_one]
        group
      exact wEl_not_diag (hw ▸ (diagSub hF).mul_mem hd hgd)
  · intro x hx
    exact ⟨A0_le_S0 hx, Subgroup.mem_centralizer_iff.2 fun y hy =>
      A0_commute (commutator_le_A0 hy) hx⟩

variable (hF)

@[expose] noncomputable def fixPts : Subgroup (StatedSU 3 3 F) where
  carrier := {g | ∀ j : Fin 3, lineAct hF g (Pt hF j) = Pt hF j}
  one_mem' := fun j => lineAct_one hF _
  mul_mem' := fun {a b} ha hb j => by rw [lineAct_mul, hb j, ha j]
  inv_mem' := fun {a} ha j => by
    have := congrArg (lineAct hF a⁻¹) (ha j)
    rw [← lineAct_mul, inv_mul_cancel, lineAct_one] at this
    exact this.symm

variable {hF}

theorem lineAct_tEl (j : Fin 3) : lineAct hF (tEl hF d) (Pt hF j) = Pt hF j := by
  fin_cases j
  · exact lineAct_Pt_eq hF (neg_ne_zero.2 (i_ne_zero d)) (by
      rw [coe_tEl, mulVec_ev]; ext k; fin_cases k <;> simp [tM, ev_apply])
  · exact lineAct_Pt_eq hF one_ne_zero (by
      rw [coe_tEl, mulVec_ev, one_smul]; ext k; fin_cases k <;> simp [tM, ev_apply])
  · exact lineAct_Pt_eq hF (i_ne_zero d) (by
      rw [coe_tEl, mulVec_ev]; ext k; fin_cases k <;> simp [tM, ev_apply])

theorem A0_le_fixPts : A0 hF d ≤ fixPts hF := by
  rw [A0, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact fun j => lineAct_sEl j
  · exact fun j => lineAct_tEl j

theorem eq_Pt_of_fixed {g : StatedSU 3 3 F} {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![a, b, c])
    {q : NonisoLine F} (hq : lineAct hF g q = q) : ∃ k : Fin 3, q = Pt hF k := by
  have hne : ∀ j k : Fin 3, j ≠ k → (![a, b, c] : Fin 3 → F) j ≠ ![a, b, c] k := by
    intro j k hjk
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · simpa using hab
    · simpa using hac
    · simpa using hab.symm
    · exact absurd rfl hjk
    · simpa using hbc
    · simpa using hac.symm
    · simpa using hbc.symm
    · exact absurd rfl hjk
  set v := q.gen with hv
  have hvq : v ∈ q.1 := q.gen_mem
  have hv0 : v ≠ 0 := q.gen_ne_zero
  have hmem : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ q.1 := by
    have : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ (lineAct hF g q).1 :=
      Submodule.mem_map.2 ⟨v, hvq, by rw [Matrix.toLin'_apply]⟩
    rwa [hq] at this
  rw [q.eq_span_gen] at hmem
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 hmem
  rw [hg] at hc'
  have hc'' : ∀ j, c' * v j = ![a, b, c] j * v j := fun j => by
    have := congrFun hc' j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal] at this
    exact this
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hck : c' = ![a, b, c] k := by
    exact mul_right_cancel₀ (by simpa using hk) (hc'' k)
  have hvj : ∀ j, j ≠ k → v j = 0 := by
    intro j hjk
    have h1 := hc'' j
    rw [hck] at h1
    have h2 : (![a, b, c] k - ![a, b, c] j) * v j = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm (hne j k hjk)
    · exact h3
  refine ⟨k, Subtype.ext ?_⟩
  rw [q.eq_span_gen, Pt_val]
  have hvk : v = v k • ev F k := by
    ext j
    by_cases hj : j = k
    · subst hj
      simp [ev_apply]
    · simp [ev_apply, hj, hvj j hj]
  rw [← hv, hvk]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hk) _

theorem normalizer_A0_le_stab0 :
    Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F)) ≤ stab0 hF := by
  intro g hg
  refine mem_stab0_of_forall fun j => ?_
  have hginv : g⁻¹ ∈ Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F)) :=
    Subgroup.inv_mem _ hg
  have hs : g⁻¹ * sEl hF d * g ∈ A0 hF d := by
    have := (Subgroup.mem_normalizer_iff.1 hginv (sEl hF d)).1 sEl_mem_A0
    simpa using this
  have hfix : lineAct hF (sEl hF d) (lineAct hF g (Pt hF j)) = lineAct hF g (Pt hF j) := by
    have h1 : sEl hF d * g = g * (g⁻¹ * sEl hF d * g) := by group
    rw [← lineAct_mul, h1, lineAct_mul, A0_le_fixPts hs j]
  obtain ⟨k, hk⟩ := eq_Pt_of_fixed (hF := hF) (g := sEl hF d) (neg_i_ne_i d) (neg_i_ne_one d)
    (i_ne_one d) (by rw [coe_sEl, sM_eq_diagonal]) hfix
  exact ⟨k, hk⟩

theorem cEl_conj_sEl : cEl hF * sEl hF d * (cEl hF)⁻¹ = (sEl hF d)⁻¹ * tEl hF d := by
  rw [mul_inv_eq_iff_eq_mul]
  have hi := d.sq
  have h3 := d.three
  apply eq_of_matrix
  simp only [coe_mul_matrix]
  rw [coe_cEl, coe_sEl, coe_tEl, coe_inv_sEl]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cM, sM, tM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem cEl_conj_tEl : cEl hF * tEl hF d * (cEl hF)⁻¹ = (sEl hF d)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  have hi := d.sq
  have h3 := d.three
  apply eq_of_matrix
  simp only [coe_mul_matrix]
  rw [coe_cEl, coe_tEl, coe_inv_sEl]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cM, sM, tM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem A0_conj_c {x : StatedSU 3 3 F} (hx : x ∈ A0 hF d) : cEl hF * x * (cEl hF)⁻¹ ∈ A0 hF d := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [cEl_conj_sEl]
      exact (A0 hF d).mul_mem ((A0 hF d).inv_mem sEl_mem_A0) tEl_mem_A0
    · rw [cEl_conj_tEl]
      exact (A0 hF d).inv_mem sEl_mem_A0
  | one => simp
  | mul y z _ _ ihy ihz =>
    rw [show cEl hF * (y * z) * (cEl hF)⁻¹ = (cEl hF * y * (cEl hF)⁻¹) * (cEl hF * z * (cEl hF)⁻¹)
      by group]
    exact (A0 hF d).mul_mem ihy ihz
  | inv y _ ih =>
    rw [show cEl hF * y⁻¹ * (cEl hF)⁻¹ = (cEl hF * y * (cEl hF)⁻¹)⁻¹ by group]
    exact (A0 hF d).inv_mem ih

theorem cEl_mem_normalizer_A0 : cEl hF ∈ Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F)) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => A0_conj_c hx, fun hx => ?_⟩
  have h := A0_conj_c (A0_conj_c hx)
  have hc3 : cEl hF * cEl hF * cEl hF = 1 := by
    rw [← pow_two, ← pow_succ]
    exact cEl_pow_three
  have e : cEl hF * (cEl hF * (cEl hF * x * (cEl hF)⁻¹) * (cEl hF)⁻¹) * (cEl hF)⁻¹ = x := by
    calc cEl hF * (cEl hF * (cEl hF * x * (cEl hF)⁻¹) * (cEl hF)⁻¹) * (cEl hF)⁻¹ =
        (cEl hF * cEl hF * cEl hF) * x * ((cEl hF * cEl hF * cEl hF)⁻¹) := by group
      _ = x := by rw [hc3]; group
  rwa [e] at h

theorem normalizer_A0_eq_stab0 (hcard : Nat.card (S0 hF d) = 32) :
    Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F)) = stab0 hF := by
  have := finite_K hF
  refine Subgroup.eq_of_le_of_card_ge normalizer_A0_le_stab0 ?_
  rw [card_stab0 d]
  have h32 : 32 ∣ Nat.card (Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F))) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le S0_le_normalizer_A0
  have h3 : 3 ∣ Nat.card (Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F))) := by
    have := orderOf_dvd_natCard
      (⟨cEl hF, cEl_mem_normalizer_A0⟩ : Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F)))
    rwa [Subgroup.orderOf_mk, orderOf_cEl] at this
  have h96 : 96 ∣ Nat.card (Subgroup.normalizer (A0 hF d : Set (StatedSU 3 3 F))) :=
    (show Nat.Coprime 32 3 by norm_num).mul_dvd_of_dvd_of_dvd h32 h3
  exact Nat.le_of_dvd Nat.card_pos h96

theorem canK2_eq_stab0 (hcard : Nat.card (S0 hF d) = 32) : canK2 (S0 hF d) = stab0 hF := by
  rw [canK2, canA_eq_A0]
  exact normalizer_A0_eq_stab0 hcard

end CFSG.QuasithinUnique.Vol2Native.L239.U33
