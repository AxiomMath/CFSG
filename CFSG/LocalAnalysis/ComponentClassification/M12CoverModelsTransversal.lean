module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversalCheck

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

theorem rCodeArr_get {i p : ℕ} (hi : i < 1485) (hp : p < 12) :
    rCodeArr[12 * i + p]! = rCode i p :=
  Nat.eq_of_beq_eq_true (all_range (all_range rCodeCheck_eq hi) hp)

theorem cosetCheck_spec {i : ℕ} (hi : i < 1485) :
    (i = 0 ∨ (tpar i < i ∧ (tlet i = 1 ∨ tlet i = 2))) ∧
      ∀ l ∈ [1, 2], tact l i < 1485 ∧ twit l i < 64 ∧
        ∀ p < 12, r0CodeAux 1485 i (letterCode l p) =
          SylowTable.nth 0 (SylowTable.code (twit l i)) (r0CodeAux 1485 (tact l i) p) := by
  have h := all_range cosetCheck_eq hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, and_assoc] at h
  exact h

theorem tpar_lt {i : ℕ} (hi : i < 1485) (h0 : i ≠ 0) : tpar i < i :=
  ((cosetCheck_spec hi).1.resolve_left h0).1

@[expose] def r0Aux : ℕ → ℕ → Equiv.Perm (Fin 12)
  | 0, _ => 1
  | n + 1, i => if i = 0 then 1 else r0Aux n (tpar i) * letter (tlet i)

@[expose] def r0βAux : ℕ → ℕ → Equiv.Perm (Fin 12)
  | 0, _ => 1
  | n + 1, i => if i = 0 then 1 else r0βAux n (tpar i) * letterβ (tlet i)

theorem r0Aux_succ (n i : ℕ) :
    r0Aux (n + 1) i = if i = 0 then 1 else r0Aux n (tpar i) * letter (tlet i) := rfl

theorem r0Aux_mem : ∀ n i, r0Aux n i ∈ NativeSporadic.M12
  | 0, _ => one_mem _
  | n + 1, i => by
    unfold r0Aux
    split_ifs
    · exact one_mem _
    · exact mul_mem (r0Aux_mem n _) (letter_mem _)

theorem r0βAux_succ (n i : ℕ) :
    r0βAux (n + 1) i = if i = 0 then 1 else r0βAux n (tpar i) * letterβ (tlet i) := rfl

theorem r0Aux_pair_mem : ∀ n i, (r0Aux n i, r0βAux n i) ∈ m12Pairs
  | 0, _ => m12Pairs.one_mem
  | n + 1, i => by
    rw [r0Aux_succ, r0βAux_succ]
    split_ifs
    · exact m12Pairs.one_mem
    · have := m12Pairs.mul_mem (r0Aux_pair_mem n (tpar i)) (letter_pair_mem (tlet i))
      simpa only [Prod.mk_mul_mk] using this

theorem isFCode_r0Aux : ∀ n i, IsFCode (r0CodeAux n i) (r0Aux n i)
  | 0, _ => fun _ => rfl
  | n + 1, i => by
    by_cases hi : i = 0
    · intro p
      simp [r0CodeAux, r0Aux, hi]
    · have h := (isFCode_r0Aux n (tpar i)).mul (isFCode_letter (tlet i))
      intro p
      simp only [r0CodeAux, r0Aux, hi, ↓reduceIte]
      exact h p

theorem isFCode_r0βAux : ∀ n i, IsFCode (r0βCodeAux n i) (r0βAux n i)
  | 0, _ => fun _ => rfl
  | n + 1, i => by
    by_cases hi : i = 0
    · intro p
      simp [r0βCodeAux, r0βAux, hi]
    · have h := (isFCode_r0βAux n (tpar i)).mul (isFCode_letterβ (tlet i))
      intro p
      simp only [r0βCodeAux, r0βAux, hi, ↓reduceIte]
      exact h p

theorem r0Aux_stable : ∀ i, i < 1485 → ∀ n m, i < n → i < m → r0Aux n i = r0Aux m i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi n m hn hm
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    by_cases h0 : i = 0
    · simp [r0Aux, h0]
    · have hp := tpar_lt hi h0
      simp only [r0Aux, h0, ↓reduceIte]
      rw [ih _ hp (by omega) n m (by omega) (by omega)]

@[expose] def r0 (i : Fin 1485) : NativeSporadic.M12 := ⟨r0Aux 1485 i, r0Aux_mem _ _⟩

@[expose] def letterM (l : ℕ) : NativeSporadic.M12 := ⟨letter l, letter_mem l⟩

@[expose] def parF (i : Fin 1485) : Fin 1485 := ⟨tpar i % 1485, Nat.mod_lt _ (by norm_num)⟩

@[expose] def letF (i : Fin 1485) : ℕ := tlet i

theorem r0Aux_1485 (i : ℕ) :
    r0Aux 1485 i = if i = 0 then 1 else r0Aux 1484 (tpar i) * letter (tlet i) :=
  r0Aux_succ 1484 i

theorem r0_zero : r0 0 = 1 := by
  apply Subtype.ext
  show r0Aux 1485 0 = 1
  rw [r0Aux_1485]
  rfl

theorem r0_rec (i : Fin 1485) (hi : i ≠ 0) :
    r0 i = r0 (parF i) * letterM (letF i) ∧ parF i < i ∧ (letF i = 1 ∨ letF i = 2) := by
  have h0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
  have hspec := ((cosetCheck_spec i.2).1.resolve_left h0)
  have hp : (parF i : ℕ) = tpar i := Nat.mod_eq_of_lt (by omega)
  refine ⟨Subtype.ext ?_, by rw [Fin.lt_def, hp]; exact hspec.1, hspec.2⟩
  rw [Subgroup.coe_mul]
  show r0Aux 1485 i = r0Aux 1485 (parF i) * letter (tlet i)
  rw [r0Aux_1485, hp, r0Aux_stable _ (by omega) 1484 1485 (by omega) (by omega)]
  simp only [h0, ↓reduceIte]

@[expose] def actF (l : ℕ) (i : Fin 1485) : Fin 1485 :=
  ⟨tact l i % 1485, Nat.mod_lt _ (by norm_num)⟩

@[expose] def witF (l : ℕ) (i : Fin 1485) : Fin 64 := ⟨twit l i % 64, Nat.mod_lt _ (by norm_num)⟩

theorem isFCode_r0 (i : Fin 1485) : IsFCode (r0CodeAux 1485 i) (r0 i : Equiv.Perm (Fin 12)) :=
  isFCode_r0Aux _ _

theorem r0_mul_letter (i : Fin 1485) {l : ℕ} (hl : l = 1 ∨ l = 2) :
    r0 i * letterM l = eltM (witF l i) * r0 (actF l i) := by
  obtain ⟨ha, hw, hc⟩ := (cosetCheck_spec i.2).2 l (by rcases hl with rfl | rfl <;> simp)
  have ha' : (actF l i : ℕ) = tact l i := Nat.mod_eq_of_lt ha
  have hw' : (witF l i : ℕ) = twit l i := Nat.mod_eq_of_lt hw
  apply Subtype.ext
  change (r0 i : Equiv.Perm (Fin 12)) * letter l = SylowTable.elt (witF l i) * (r0 (actF l i) :
    Equiv.Perm (Fin 12))
  refine ((isFCode_r0 i).mul (isFCode_letter l)).perm_eq
    (((isFCode_of_isCode (SylowTable.isCode_elt _ (witF l i).2)).mul (isFCode_r0 _)).congr
      fun p hp => ?_)
  rw [hw', ha']
  exact hc p hp

theorem letter_one : letter 1 = m12gA := by simp [letter]

theorem letter_two : letter 2 = m12gB := by simp [letter]

theorem m12gA_inv : m12gA⁻¹ = m12gA := by decide

theorem m12gB_inv : m12gB⁻¹ = m12gB * m12gB := by decide

theorem exists_elt_mul_r0 (x : NativeSporadic.M12) : ∃ k : Fin 64, ∃ i : Fin 1485,
    eltM k * r0 i = x := by
  have stepM : ∀ (y : NativeSporadic.M12) (l : ℕ), (l = 1 ∨ l = 2) →
      (∃ k : Fin 64, ∃ i : Fin 1485, eltM k * r0 i = y) →
      ∃ k : Fin 64, ∃ i : Fin 1485, eltM k * r0 i = y * letterM l := by
    rintro y l hl ⟨k, i, rfl⟩
    obtain ⟨hlt, hmul⟩ := SylowTable.mulIdx_spec k.2 (witF l i).2
    refine ⟨⟨_, hlt⟩, actF l i, ?_⟩
    have he : eltM (SylowTable.mulIdx k (witF l i)) = eltM k * eltM (witF l i) :=
      Subtype.ext (by simp [eltM, hmul])
    change eltM (SylowTable.mulIdx k (witF l i)) * r0 (actF l i) = _
    rw [he, mul_assoc, ← r0_mul_letter i hl, mul_assoc]
  let P : Equiv.Perm (Fin 12) → Prop := fun σ =>
    ∃ k : Fin 64, ∃ i : Fin 1485, ((eltM k * r0 i : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = σ
  have step : ∀ σ (l : ℕ), (l = 1 ∨ l = 2) → P σ → P (σ * letter l) := by
    rintro σ l hl ⟨k, i, hσ⟩
    obtain ⟨k', i', h⟩ := stepM (eltM k * r0 i) l hl ⟨k, i, rfl⟩
    exact ⟨k', i', by rw [h, Subgroup.coe_mul, hσ]; rfl⟩
  have key : ∀ σ : Equiv.Perm (Fin 12), σ ∈ Subgroup.closure {m12gA, m12gB} → P σ := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction_right with
    | one =>
      refine ⟨0, 0, ?_⟩
      rw [r0_zero, mul_one]
      exact congrArg Subtype.val SylowTable.elt_zero
    | mul_right σ _ y hy ih =>
      rcases hy with rfl | rfl
      · simpa [letter_one] using step σ 1 (Or.inl rfl) ih
      · simpa [letter_two] using step σ 2 (Or.inr rfl) ih
    | mul_inv_cancel σ _ y hy ih =>
      rcases hy with rfl | rfl
      · rw [m12gA_inv]
        simpa [letter_one] using step σ 1 (Or.inl rfl) ih
      · rw [m12gB_inv, ← mul_assoc]
        have h1 := step σ 2 (Or.inr rfl) ih
        rw [letter_two] at h1
        simpa [letter_two] using step _ 2 (Or.inr rfl) h1
  obtain ⟨k, i, h⟩ := key x (by rw [← m12_eq]; exact x.2)
  exact ⟨k, i, Subtype.ext h⟩

theorem bijective_elt_mul_r0 :
    Function.Bijective fun x : Fin 64 × Fin 1485 => eltM x.1 * r0 x.2 := by
  refine Function.Surjective.bijective_of_nat_card_le (fun x => ?_) ?_
  · obtain ⟨k, i, h⟩ := exists_elt_mul_r0 x
    exact ⟨(k, i), h⟩
  · rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin, card_M12]

theorem eltM_injective : Function.Injective fun k : Fin 64 => eltM k := by
  intro x y h
  have h' : eltM x = eltM y := h
  have h'' := congrArg (fun z : NativeSporadic.M12 => (z : Equiv.Perm (Fin 12))) h'
  exact Fin.ext (SylowTable.elt_injective x.2 y.2 (Subtype.ext h''))

theorem r0_coset_injective {i j : Fin 1485} {s : NativeSporadic.M12}
    (hs : (s : Equiv.Perm (Fin 12)) ∈ M12Cover.S) (h : r0 i = s * r0 j) : i = j := by
  obtain ⟨k, hk, hks⟩ := SylowTable.exists_elt hs
  have := bijective_elt_mul_r0.1 (a₁ := (0, i)) (a₂ := (⟨k, hk⟩, j)) (by
    simp only
    rw [show eltM ((0 : Fin 64) : ℕ) = 1 from Subtype.ext (by simp [eltM, SylowTable.elt_zero]),
      one_mul, h]
    congr 1
    exact Subtype.ext hks.symm)
  exact (Prod.ext_iff.1 this).2

theorem qtfe_m12_sylow_coset_actions :
    (∃ P : Sylow 2 NativeSporadic.M12,
      (P : Subgroup NativeSporadic.M12) = M12Cover.S.subgroupOf NativeSporadic.M12) ∧
    Nat.card M12Cover.S = 64 ∧
    Function.Bijective (fun k : Fin 64 => SylowTable.elt k) ∧ SylowTable.elt 0 = 1 ∧
    r0 0 = 1 ∧
    (∀ i : Fin 1485, i ≠ 0 →
      r0 i = r0 (parF i) * letterM (letF i) ∧ parF i < i ∧ (letF i = 1 ∨ letF i = 2)) ∧
    (∀ i : Fin 1485, ∀ l : ℕ, (l = 1 ∨ l = 2) →
      r0 i * letterM l = eltM (witF l i) * r0 (actF l i)) ∧
    Function.Bijective (fun x : Fin 64 × Fin 1485 => eltM x.1 * r0 x.2) ∧
    (∀ l : ℕ, (l = 1 ∨ l = 2) → Function.Bijective (actF l)) ∧
    Nat.card NativeSporadic.M12 = 95040 := by
  refine ⟨M12Cover.exists_sylow_eq_S, M12Cover.card_S,
    ⟨fun x y h => Fin.ext (SylowTable.elt_injective x.2 y.2 h),
    fun s => ?_⟩, SylowTable.elt_zero, r0_zero, r0_rec, fun i l hl => r0_mul_letter i hl,
    bijective_elt_mul_r0, fun l hl => ?_, card_M12⟩
  · obtain ⟨k, hk, h⟩ := SylowTable.elt_surjective s
    exact ⟨⟨k, hk⟩, h⟩
  · refine Finite.injective_iff_bijective.1 fun i j hij => ?_
    have hi := r0_mul_letter i hl
    have hj := r0_mul_letter j hl
    rw [hij] at hi
    have : r0 i = (eltM (witF l i) * (eltM (witF l j))⁻¹) * r0 j := by
      have h1 : r0 i = eltM (witF l i) * r0 (actF l j) * (letterM l)⁻¹ := by
        rw [← hi, mul_inv_cancel_right]
      have h2 : r0 (actF l j) = (eltM (witF l j))⁻¹ * (r0 j * letterM l) := by
        rw [hj, inv_mul_cancel_left]
      rw [h1, h2]
      group
    refine r0_coset_injective ?_ this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, eltM]
    exact mul_mem (SylowTable.elt _).2 (inv_mem (SylowTable.elt _).2)

@[expose] def r (i : Fin 1485) : NativeSporadic.M12 := g * r0 i * g⁻¹

theorem r_zero : r 0 = 1 := by rw [r, r0_zero, mul_one, mul_inv_cancel]

theorem isFCode_r (i : Fin 1485) : IsFCode (rCode i) (r i : Equiv.Perm (Fin 12)) := by
  have h := (isFCode_g.mul (isFCode_r0 i)).mul isFCode_g_inv
  simp only [r, Subgroup.coe_mul, Subgroup.coe_inv]
  exact h

theorem kIdx_injective : Function.Injective fun j : Fin 64 => (⟨kIdx j, kIdx_lt j⟩ : Fin 64) := by
  intro x y h
  apply d_injective
  apply Subtype.ext
  simp only [d]
  rw [show kIdx x = kIdx y from congrArg Fin.val h]

theorem d_eq_conj (j : Fin 64) :
    (d j : NativeSporadic.M12) = g * eltM (⟨kIdx j, kIdx_lt j⟩ : Fin 64) * g⁻¹ := rfl

theorem bijective_d_mul_r :
    Function.Bijective fun x : Fin 64 × Fin 1485 => (d x.1 : NativeSporadic.M12) * r x.2 := by
  have hk : Function.Bijective fun j : Fin 64 => (⟨kIdx j, kIdx_lt j⟩ : Fin 64) :=
    Finite.injective_iff_bijective.1 kIdx_injective
  have hc : Function.Bijective (MulAut.conj g) := (MulAut.conj g).bijective
  have hprod : Function.Bijective
      (Prod.map (fun j : Fin 64 => (⟨kIdx j, kIdx_lt j⟩ : Fin 64)) (id : Fin 1485 → Fin 1485)) :=
    ⟨hk.1.prodMap Function.injective_id, hk.2.prodMap Function.surjective_id⟩
  have := hc.comp (bijective_elt_mul_r0.comp hprod)
  convert this using 1
  ext x
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id, MulAut.conj_apply, d_eq_conj, r]
  group

theorem existsUnique_mul_r (x : NativeSporadic.M12) :
    ∃! y : S × Fin 1485, (y.1 : NativeSporadic.M12) * r y.2 = x := by
  obtain ⟨⟨j, i⟩, hji⟩ := bijective_d_mul_r.2 x
  simp only at hji
  refine ⟨(d j, i), hji, fun y hy => ?_⟩
  simp only at hy
  obtain ⟨j', hj'⟩ := d_surjective y.1
  have : ((j', y.2) : Fin 64 × Fin 1485) = (j, i) :=
    bijective_d_mul_r.1 (show (d j' : NativeSporadic.M12) * r y.2 = (d j : NativeSporadic.M12) * r i
      by rw [hj', hy, hji])
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 this
  simp only at h1 h2
  exact Prod.ext (by rw [← hj', h1]) h2

theorem decompCheck_spec {i h : ℕ} (hi : i < 1485) (hh : h < 64) :
    tp i h < 64 ∧ tih i h < 1485 ∧ ∀ p < 12,
      rCodeArr[12 * i + dCode h p]! = dCode (tp i h) rCodeArr[12 * tih i h + p]! := by
  have hc := all_range (all_range decompCheck_eq hi) hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hc
  exact ⟨hc.1.1, hc.1.2, hc.2⟩

@[expose] noncomputable def pS (i : Fin 1485) (h : S) : S :=
  d ⟨tp i (idx h) % 64, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def iS (i : Fin 1485) (h : S) : Fin 1485 :=
  ⟨tih i (idx h) % 1485, Nat.mod_lt _ (by norm_num)⟩

theorem pS_d (i : Fin 1485) (j : Fin 64) :
    pS i (d j) = d ⟨tp i j % 64, Nat.mod_lt _ (by norm_num)⟩ := by
  simp only [pS, idx_d]

theorem iS_d (i : Fin 1485) (j : Fin 64) :
    iS i (d j) = ⟨tih i j % 1485, Nat.mod_lt _ (by norm_num)⟩ := by
  simp only [iS, idx_d]

theorem idx_pS (i : Fin 1485) (j : Fin 64) : (idx (pS i (d j)) : ℕ) = tp i j := by
  rw [pS_d, idx_d]
  exact Nat.mod_eq_of_lt (decompCheck_spec i.2 j.2).1

theorem val_iS (i : Fin 1485) (j : Fin 64) : (iS i (d j) : ℕ) = tih i j := by
  rw [iS_d]
  exact Nat.mod_eq_of_lt (decompCheck_spec i.2 j.2).2.1

theorem isFCode_d_of_val {j : Fin 64} {n : ℕ} (h : (j : ℕ) = n) : IsFCode (dCode n) (dPerm j) :=
  h ▸ isFCode_d j

theorem isFCode_pS (i : Fin 1485) (j : Fin 64) :
    IsFCode (dCode (tp i j)) ((pS i (d j) : NativeSporadic.M12) : Equiv.Perm (Fin 12)) := by
  rw [← d_idx (pS i (d j))]
  exact isFCode_d_of_val (idx_pS i j)

theorem r_mul (i : Fin 1485) (h : S) :
    r i * (h : NativeSporadic.M12) = (pS i h : NativeSporadic.M12) * r (iS i h) := by
  obtain ⟨j, rfl⟩ := d_surjective h
  obtain ⟨-, -, hc⟩ := decompCheck_spec i.2 j.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  refine ((isFCode_r i).mul (isFCode_d j)).perm_eq
    (((isFCode_pS i j).mul (isFCode_r _)).congr fun p hp => ?_)
  have h1 := hc p hp
  rw [rCodeArr_get i.2 ((isFCode_d j).lt hp)] at h1
  rw [← val_iS i j, rCodeArr_get (iS i (d j)).2 hp] at h1
  exact h1

theorem pS_iS_unique (i : Fin 1485) (h : S) (s : S) (k : Fin 1485)
    (hs : r i * (h : NativeSporadic.M12) = (s : NativeSporadic.M12) * r k) :
    s = pS i h ∧ k = iS i h := by
  obtain ⟨y, -, hy⟩ := existsUnique_mul_r (r i * h)
  have h1 := hy (s, k) hs.symm
  have h2 := hy (pS i h, iS i h) (r_mul i h).symm
  rw [← h2] at h1
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

theorem betaCheck_spec : ((List.range 1485).map tsig).Nodup ∧ ∀ i < 1485,
    taIdx i < 64 ∧ tsig i < 1485 ∧
      ∀ p < 12, rβCode i p = dCode (taIdx i) rCodeArr[12 * tsig i + p]! := by
  have h := betaCheck_eq
  rw [betaCheck, Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1, fun i hi => ?_⟩
  have hc := all_range h.2 hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hc
  exact ⟨hc.1.1, hc.1.2, hc.2⟩

@[expose] noncomputable def aS (i : Fin 1485) : S := d ⟨taIdx i % 64, Nat.mod_lt _ (by norm_num)⟩

@[expose] def σI (i : Fin 1485) : Fin 1485 := ⟨tsig i % 1485, Nat.mod_lt _ (by norm_num)⟩

theorem val_σI (i : Fin 1485) : (σI i : ℕ) = tsig i :=
  Nat.mod_eq_of_lt (betaCheck_spec.2 i i.2).2.1

theorem idx_aS (i : Fin 1485) : (idx (aS i) : ℕ) = taIdx i := by
  rw [aS, idx_d]
  exact Nat.mod_eq_of_lt (betaCheck_spec.2 i i.2).1

theorem isFCode_aS (i : Fin 1485) :
    IsFCode (dCode (taIdx i)) ((aS i : NativeSporadic.M12) : Equiv.Perm (Fin 12)) := by
  rw [← d_idx (aS i)]
  exact isFCode_d_of_val (idx_aS i)

theorem σI_bijective : Function.Bijective σI := by
  refine Finite.injective_iff_bijective.1 fun i j h => ?_
  have h' : tsig i = tsig j := by rw [← val_σI, ← val_σI, h]
  have hn := betaCheck_spec.1
  rw [List.nodup_iff_injective_get] at hn
  have := @hn ⟨i, by simp⟩ ⟨j, by simp⟩ (by simpa using h')
  exact Fin.ext (by simpa using this)

theorem gβ_pair : ((g : Equiv.Perm (Fin 12)), evalWordβ gWord) ∈ m12Pairs := word_pair_mem gWord

theorem isFCode_gβ_inv :
    IsFCode (SylowTable.nth 0 gβInvCode) (evalWordβ gWord)⁻¹ :=
  (isFCode_evalWordβ gWord).inv (by decide) (by decide)

theorem pair_mem_r (i : Fin 1485) :
    ((r i : Equiv.Perm (Fin 12)),
      (((aS i : NativeSporadic.M12) * r (σI i) : NativeSporadic.M12) : Equiv.Perm (Fin 12))) ∈
      m12Pairs := by
  have hpair : ((r i : Equiv.Perm (Fin 12)), evalWordβ gWord * r0βAux 1485 i *
      (evalWordβ gWord)⁻¹) ∈ m12Pairs := by
    have := m12Pairs.mul_mem (m12Pairs.mul_mem gβ_pair (r0Aux_pair_mem 1485 i))
      (m12Pairs.inv_mem gβ_pair)
    simpa [r, r0] using this
  convert hpair using 2
  obtain ⟨-, -, hc⟩ := betaCheck_spec.2 i i.2
  have h := ((isFCode_evalWordβ gWord).mul (isFCode_r0βAux 1485 i)).mul isFCode_gβ_inv
  refine Eq.symm (h.perm_eq ?_)
  rw [Subgroup.coe_mul]
  refine ((isFCode_aS i).mul (isFCode_r _)).congr fun p hp => ?_
  have h1 := hc p hp
  rw [← val_σI, rCodeArr_get (σI i).2 hp] at h1
  exact h1

theorem quotCheck_spec {i h : ℕ} (hi : i < 1485) (hh : h < 64) :
    mIdx (mIdx (invIdx (taIdx i)) (bIdx (tp i h))) (taIdx (tih i h)) = tp (tsig i) (bIdx h) :=
  Nat.eq_of_beq_eq_true (all_range (all_range quotCheck_eq hi) hh)

theorem idx_βS (s : S) : (idx (βS s) : ℕ) = bIdx (idx s) := by
  rw [← d_idx s, βS_d, idx_d, idx_d]
  rfl

theorem quotient_eq (i : Fin 1485) (h : S) :
    (aS i)⁻¹ * βS (pS i h) * aS (iS i h) = pS (σI i) (βS h) := by
  obtain ⟨j, rfl⟩ := d_surjective h
  rw [← d_idx (aS i), ← d_idx (aS (iS i (d j))), ← d_idx (βS (pS i (d j))), d_inv, ← d_mul,
    ← d_mul, ← d_idx (pS (σI i) (βS (d j)))]
  congr 1
  apply Fin.ext
  change mIdx (mIdx (invIdx (idx (aS i))) (idx (βS (pS i (d j))))) (idx (aS (iS i (d j)))) = _
  rw [idx_aS, idx_aS, idx_βS, idx_pS, val_iS]
  rw [show (idx (pS (σI i) (βS (d j))) : ℕ) = tp (tsig i) (bIdx j) by
    rw [βS_d, idx_pS, val_σI]
    rfl]
  exact quotCheck_spec i.2 j.2

end CFSG.ComponentClassification.M12Cover.InternalSylow
