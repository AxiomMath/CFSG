module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsSylowData
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylow
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

@[expose] def IsFCode (c : ℕ → ℕ) (σ : Equiv.Perm (Fin 12)) : Prop :=
  ∀ p : Fin 12, c p = σ p

theorem IsFCode.lt {c : ℕ → ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsFCode c σ) {p : ℕ}
    (hp : p < 12) : c p < 12 := by
  have := h ⟨p, hp⟩
  simp only at this
  rw [this]
  exact (σ ⟨p, hp⟩).2

theorem IsFCode.one : IsFCode (fun p => p) 1 := fun _ => rfl

theorem IsFCode.mul {c c' : ℕ → ℕ} {σ τ : Equiv.Perm (Fin 12)} (h : IsFCode c σ)
    (h' : IsFCode c' τ) : IsFCode (fun p => c (c' p)) (σ * τ) := by
  intro p
  simp only [Equiv.Perm.mul_apply]
  rw [h' p, h (τ p)]

theorem IsFCode.perm_eq {c : ℕ → ℕ} {σ τ : Equiv.Perm (Fin 12)} (h : IsFCode c σ)
    (h' : IsFCode c τ) : σ = τ :=
  Equiv.ext fun p => Fin.ext ((h p).symm.trans (h' p))

theorem IsFCode.congr {c c' : ℕ → ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsFCode c σ)
    (hc : ∀ p < 12, c' p = c p) : IsFCode c' σ :=
  fun p => (hc p p.2).trans (h p)

theorem IsFCode.inv {c c' : ℕ → ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsFCode c σ)
    (hlt : ∀ p < 12, c' p < 12) (hinv : ∀ p < 12, c (c' p) = p) : IsFCode c' σ⁻¹ := by
  intro p
  have h1 := h ⟨c' p, hlt p p.2⟩
  simp only [hinv p p.2] at h1
  have h2 : σ ⟨c' p, hlt p p.2⟩ = p := Fin.ext h1.symm
  have h3 : σ⁻¹ p = ⟨c' p, hlt p p.2⟩ := Equiv.Perm.inv_eq_iff_eq.2 h2.symm
  rw [h3]

theorem isFCode_of_isCode {l : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : SylowTable.IsCode l σ) :
    IsFCode (SylowTable.nth 0 l) σ :=
  h.2

@[expose] def imageArray (σ : Equiv.Perm (Fin 12)) : List ℕ := List.ofFn fun p => (σ p : ℕ)

theorem imageArray_eq {c : ℕ → ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsFCode c σ) :
    imageArray σ = (List.range 12).map c := by
  rw [imageArray, List.ofFn_eq_map]
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  exact (h ⟨k, by simpa using h1⟩).symm

theorem card_fixed_eq {c : ℕ → ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsFCode c σ) :
    (Finset.univ.filter fun p : Fin 12 => σ p = p).card =
      (List.range 12).countP fun p => c p == p := by
  rw [← card_fin_subtype_eq_countP, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq, h p]
  exact ⟨fun hp => by rw [hp], fun hp => Fin.ext hp⟩

@[expose] def letter (k : ℕ) : Equiv.Perm (Fin 12) := if k = 1 then m12gA else m12gB

@[expose] def letterβ (k : ℕ) : Equiv.Perm (Fin 12) := if k = 1 then m12gA else m12bp

@[expose] def evalWord (w : List ℕ) : Equiv.Perm (Fin 12) := (w.map letter).prod

@[expose] def evalWordβ (w : List ℕ) : Equiv.Perm (Fin 12) := (w.map letterβ).prod

@[expose] def aCode : List ℕ := [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]

@[expose] def bCode : List ℕ := [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

@[expose] def bpCode : List ℕ := [5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6]

@[expose] def letterCode (k p : ℕ) : ℕ := SylowTable.nth 0 (if k = 1 then aCode else bCode) p

@[expose] def letterCodeβ (k p : ℕ) : ℕ := SylowTable.nth 0 (if k = 1 then aCode else bpCode) p

@[expose] def wordCode (w : List ℕ) (p : ℕ) : ℕ := w.foldr letterCode p

@[expose] def wordCodeβ (w : List ℕ) (p : ℕ) : ℕ := w.foldr letterCodeβ p

theorem isFCode_letter (k : ℕ) : IsFCode (letterCode k) (letter k) := by
  unfold letterCode letter
  split_ifs <;> intro p <;> revert p <;> decide

theorem isFCode_letterβ (k : ℕ) : IsFCode (letterCodeβ k) (letterβ k) := by
  unfold letterCodeβ letterβ
  split_ifs <;> intro p <;> revert p <;> decide

theorem isFCode_evalWord : ∀ w : List ℕ, IsFCode (wordCode w) (evalWord w)
  | [] => IsFCode.one
  | k :: w => (isFCode_letter k).mul (isFCode_evalWord w)

theorem isFCode_evalWordβ : ∀ w : List ℕ, IsFCode (wordCodeβ w) (evalWordβ w)
  | [] => IsFCode.one
  | k :: w => (isFCode_letterβ k).mul (isFCode_evalWordβ w)

theorem evalWord_cons (k : ℕ) (w : List ℕ) : evalWord (k :: w) = letter k * evalWord w := rfl

theorem evalWordβ_cons (k : ℕ) (w : List ℕ) : evalWordβ (k :: w) = letterβ k * evalWordβ w :=
  rfl

theorem letter_mem (k : ℕ) : letter k ∈ NativeSporadic.M12 := by
  unfold letter
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem evalWord_mem (w : List ℕ) : evalWord w ∈ NativeSporadic.M12 := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact letter_mem k

theorem letter_pair_mem (k : ℕ) : (letter k, letterβ k) ∈ m12Pairs := by
  unfold letter letterβ
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem word_pair_mem : ∀ w : List ℕ, (evalWord w, evalWordβ w) ∈ m12Pairs
  | [] => m12Pairs.one_mem
  | k :: w => by
    rw [evalWord_cons, evalWordβ_cons]
    exact m12Pairs.mul_mem (letter_pair_mem k) (word_pair_mem w)

@[expose] def gWord : List ℕ := [2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2]

@[expose] def g : NativeSporadic.M12 := ⟨evalWord gWord, evalWord_mem gWord⟩

@[expose] def gInvCode : List ℕ := [5, 4, 0, 1, 7, 8, 3, 2, 11, 6, 10, 9]

theorem isFCode_g : IsFCode (wordCode gWord) (g : Equiv.Perm (Fin 12)) := isFCode_evalWord gWord

theorem isFCode_g_inv :
    IsFCode (SylowTable.nth 0 gInvCode) ((g : Equiv.Perm (Fin 12))⁻¹) :=
  isFCode_g.inv (by decide) (by decide)

theorem imageArray_g :
    imageArray (g : Equiv.Perm (Fin 12)) = [2, 3, 7, 6, 1, 0, 9, 4, 5, 11, 10, 8] := by
  rw [imageArray_eq isFCode_g]
  decide

@[expose] def u : Fin 4 → NativeSporadic.M12 :=
  ![⟨s₁, s₁_mem_M12⟩, ⟨s₂, s₂_mem_M12⟩, ⟨s₃, s₃_mem_M12⟩, ⟨s₄, s₄_mem_M12⟩]

@[expose] def S : Subgroup NativeSporadic.M12 :=
  Subgroup.closure (Set.range fun j => g * u j * g⁻¹)

theorem range_u_coe : (Set.range fun j => ((u j : NativeSporadic.M12) : Equiv.Perm (Fin 12))) =
    {s₁, s₂, s₃, s₄} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [u]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem subgroupOf_S_eq_closure :
    M12Cover.S.subgroupOf NativeSporadic.M12 = Subgroup.closure (Set.range u) := by
  apply Subgroup.map_injective NativeSporadic.M12.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left S_le_M12, MonoidHom.map_closure,
    ← Set.range_comp]
  exact (congrArg Subgroup.closure range_u_coe).symm

theorem S_eq_map : S = (M12Cover.S.subgroupOf NativeSporadic.M12).map (MulAut.conj g).toMonoidHom :=
  by
  rw [subgroupOf_S_eq_closure, MonoidHom.map_closure, ← Set.range_comp, S]
  rfl

theorem mem_S_iff (x : NativeSporadic.M12) :
    x ∈ S ↔ ((g⁻¹ * x * g : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ M12Cover.S := by
  rw [S_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc, Subgroup.mem_subgroupOf] using hy
  · intro hx
    refine ⟨g⁻¹ * x * g, Subgroup.mem_subgroupOf.2 hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

@[expose] noncomputable def sylowS : Sylow 2 NativeSporadic.M12 := g • M12Cover.sylow

theorem coe_sylowS : (sylowS : Subgroup NativeSporadic.M12) = S := by
  ext x
  rw [mem_S_iff, sylowS, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    coe_sylow, Subgroup.mem_subgroupOf]
  simp [MulAut.inv_def, mul_assoc]

theorem exists_sylow_eq_S : ∃ P : Sylow 2 NativeSporadic.M12, (P : Subgroup _) = S :=
  ⟨sylowS, coe_sylowS⟩

theorem card_S : Nat.card S = 64 := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [S_eq_map, Subgroup.card_map_of_injective hinj, card_subgroupOf_S]

@[expose] def eltM (k : ℕ) : NativeSporadic.M12 :=
  ⟨SylowTable.elt k, S_le_M12 (SylowTable.elt k).2⟩

@[expose] def kIdx (j : ℕ) : ℕ := packEntry kTable 6 j

theorem conj_eltM_mem (k : ℕ) : g * eltM k * g⁻¹ ∈ S := by
  rw [mem_S_iff]
  simp [mul_assoc, eltM]

@[expose] def d (j : Fin 64) : S := ⟨g * eltM (kIdx j) * g⁻¹, conj_eltM_mem _⟩

abbrev dPerm (j : Fin 64) : Equiv.Perm (Fin 12) :=
  ((d j : NativeSporadic.M12) : Equiv.Perm (Fin 12))

@[expose] def dCode (j p : ℕ) : ℕ := packEntry dTable 4 (12 * j + p)

def conjCheck : Bool :=
  (List.range 64).all fun j => (List.range 12).all fun p =>
    dCode j p == wordCode gWord (SylowTable.nth 0 (SylowTable.code (kIdx j))
      (SylowTable.nth 0 gInvCode p))

theorem conjCheck_eq : conjCheck = true := by decide +kernel

theorem kIdx_lt (j : ℕ) : kIdx j < 64 := packEntry_lt _ 6 j

theorem isFCode_d (j : Fin 64) : IsFCode (dCode j) (dPerm j) := by
  have h := (isFCode_g.mul (isFCode_of_isCode (SylowTable.isCode_elt _ (kIdx_lt j)))).mul
    isFCode_g_inv
  exact h.congr fun p hp => eq_of_beq (all_range (all_range conjCheck_eq j.2) hp)

theorem sorted_codes :
    (List.ofFn fun j : Fin 64 => (List.range 12).map (dCode j)).Pairwise (· < ·) := by
  decide +kernel

theorem sorted_imageArray :
    (List.ofFn fun j : Fin 64 => imageArray (dPerm j)).Pairwise (· < ·) := by
  have h : (fun j : Fin 64 => imageArray (dPerm j)) =
      fun j : Fin 64 => (List.range 12).map (dCode j) :=
    funext fun j => imageArray_eq (isFCode_d j)
  rw [h]
  exact sorted_codes

theorem d_injective : Function.Injective d := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := (List.pairwise_ofFn.1 sorted_imageArray) h
    simp only [dPerm, hij, lt_irrefl] at this
  · have := (List.pairwise_ofFn.1 sorted_imageArray) h
    simp only [dPerm, hij, lt_irrefl] at this

theorem d_bijective : Function.Bijective d :=
  d_injective.bijective_of_nat_card_le (by rw [card_S, Nat.card_eq_fintype_card, Fintype.card_fin])

@[expose] noncomputable def dEquiv : Fin 64 ≃ S := Equiv.ofBijective d d_bijective

@[expose] noncomputable def idx (s : S) : Fin 64 := dEquiv.symm s

@[simp] theorem d_idx (s : S) : d (idx s) = s := dEquiv.apply_symm_apply s

@[simp] theorem idx_d (j : Fin 64) : idx (d j) = j := dEquiv.symm_apply_apply j

theorem d_surjective (s : S) : ∃ j, d j = s := ⟨idx s, d_idx s⟩

theorem d_zero : d 0 = 1 := by
  have hk : kIdx ((0 : Fin 64) : ℕ) = 0 := by decide +kernel
  have he : eltM 0 = 1 := Subtype.ext (by simp [eltM, SylowTable.elt_zero])
  apply Subtype.ext
  change g * eltM (kIdx ((0 : Fin 64) : ℕ)) * g⁻¹ = 1
  rw [hk, he, mul_one, mul_inv_cancel]

theorem imageArray_d27 : imageArray (dPerm 27) = [3, 6, 9, 0, 4, 5, 1, 8, 7, 2, 10, 11] := by
  rw [imageArray_eq (isFCode_d 27)]
  decide +kernel

@[expose] def mIdx (i j : ℕ) : ℕ := packEntry mTable 6 (64 * i + j)

@[expose] def mTab (i j : Fin 64) : Fin 64 := ⟨mIdx i j, packEntry_lt _ 6 _⟩

@[expose] def invIdx (j : ℕ) : ℕ := packEntry invTable 6 j

@[expose] def bIdx (j : ℕ) : ℕ := packEntry bTable 6 j

@[expose] def bTab (j : Fin 64) : Fin 64 := ⟨bIdx j, packEntry_lt _ 6 _⟩

def mulCheck : Bool :=
  (List.range 64).all fun i => (List.range 64).all fun j => (List.range 12).all fun p =>
    dCode (mIdx i j) p == dCode i (dCode j p)

theorem mulCheck_eq : mulCheck = true := by decide +kernel

theorem d_mul (i j : Fin 64) : d (mTab i j) = d i * d j := by
  apply Subtype.ext
  apply Subtype.ext
  change dPerm (mTab i j) = dPerm i * dPerm j
  exact (isFCode_d _).perm_eq (((isFCode_d i).mul (isFCode_d j)).congr fun p hp =>
    eq_of_beq (all_range (all_range (all_range mulCheck_eq i.2) j.2) hp))

theorem idx_mul (s t : S) : idx (s * t) = mTab (idx s) (idx t) := by
  rw [← d_idx s, ← d_idx t, ← d_mul, idx_d, idx_d, idx_d]

def tableCheck : Bool :=
  (List.range 64).all (fun j => mIdx j (invIdx j) == 0 && bIdx (bIdx j) == j) &&
    bIdx 0 == 0 &&
    (List.range 64).all fun i => (List.range 64).all fun j =>
      bIdx (mIdx i j) == mIdx (bIdx i) (bIdx j)

theorem tableCheck_eq : tableCheck = true := by decide +kernel

theorem tableCheck_spec :
    (∀ j < 64, mIdx j (invIdx j) = 0 ∧ bIdx (bIdx j) = j) ∧ bIdx 0 = 0 ∧
      ∀ i < 64, ∀ j < 64, bIdx (mIdx i j) = mIdx (bIdx i) (bIdx j) := by
  have h := tableCheck_eq
  rw [tableCheck, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun j hj => ?_, eq_of_beq h2, fun i hi j hj => eq_of_beq (all_range (all_range h3 hi) hj)⟩
  have := all_range h1 hj
  rw [Bool.and_eq_true] at this
  exact ⟨eq_of_beq this.1, eq_of_beq this.2⟩

theorem d_inv (j : Fin 64) : (d j)⁻¹ = d ⟨invIdx j, packEntry_lt _ 6 _⟩ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← d_mul, ← d_zero]
  congr 1
  exact Fin.ext ((tableCheck_spec.1 j j.2).1)

theorem bTab_bTab (j : Fin 64) : bTab (bTab j) = j := Fin.ext (tableCheck_spec.1 j j.2).2

theorem bTab_mul (i j : Fin 64) : bTab (mTab i j) = mTab (bTab i) (bTab j) :=
  Fin.ext (tableCheck_spec.2.2 i i.2 j j.2)

theorem bTab_zero : bTab 0 = 0 := Fin.ext tableCheck_spec.2.1

@[expose] noncomputable def βS : S ≃* S where
  toFun s := d (bTab (idx s))
  invFun s := d (bTab (idx s))
  left_inv s := by simp [bTab_bTab]
  right_inv s := by simp [bTab_bTab]
  map_mul' s t := by
    simp only [idx_mul, bTab_mul, d_mul]

theorem βS_d (j : Fin 64) : βS (d j) = d (bTab j) := by simp [βS]

theorem βS_βS (s : S) : βS (βS s) = s := by simp [βS, bTab_bTab]

def wordCheck : Bool :=
  (List.range 64).all fun j => (List.range 12).all fun p =>
    wordCode (SylowTable.nth [] dWords j) p == dCode j p &&
      wordCodeβ (SylowTable.nth [] dWords j) p == dCode (bIdx j) p

theorem wordCheck_eq : wordCheck = true := by decide +kernel

theorem pair_mem_d (j : Fin 64) : (dPerm j, dPerm (bTab j)) ∈ m12Pairs := by
  have hc : ∀ p < 12, wordCode (SylowTable.nth [] dWords j) p = dCode j p ∧
      wordCodeβ (SylowTable.nth [] dWords j) p = dCode (bIdx j) p := fun p hp => by
    have := all_range (all_range wordCheck_eq j.2) hp
    rw [Bool.and_eq_true] at this
    exact ⟨eq_of_beq this.1, eq_of_beq this.2⟩
  have h1 : evalWord (SylowTable.nth [] dWords j) = dPerm j :=
    (isFCode_evalWord _).perm_eq ((isFCode_d j).congr fun p hp => (hc p hp).1)
  have h2 : evalWordβ (SylowTable.nth [] dWords j) = dPerm (bTab j) :=
    (isFCode_evalWordβ _).perm_eq ((isFCode_d _).congr fun p hp => (hc p hp).2)
  rw [← h1, ← h2]
  exact word_pair_mem _

@[expose] def uCode (k : ℕ) : List ℕ :=
  SylowTable.nth [] [[2, 3, 0, 1, 5, 4, 11, 9, 10, 7, 8, 6], [1, 0, 4, 11, 2, 6, 5, 9, 10, 7, 8, 3],
    [4, 2, 5, 0, 6, 11, 3, 9, 10, 7, 8, 1], [1, 0, 2, 4, 3, 6, 5, 10, 8, 9, 7, 11]] k

@[expose] def genIdx : Fin 4 → Fin 64 := ![8, 61, 54, 59]

theorem isFCode_u (k : Fin 4) :
    IsFCode (SylowTable.nth 0 (uCode k)) (u k : Equiv.Perm (Fin 12)) := by
  fin_cases k
  exacts [isFCode_of_isCode SylowTable.isCode_s₁, isFCode_of_isCode SylowTable.isCode_s₂,
    isFCode_of_isCode SylowTable.isCode_s₃, isFCode_of_isCode SylowTable.isCode_s₄]

def genCheck : Bool :=
  (List.range 4).all fun k => (List.range 12).all fun p =>
    dCode (SylowTable.nth 0 [8, 61, 54, 59] k) p ==
      wordCode gWord (SylowTable.nth 0 (uCode k) (SylowTable.nth 0 gInvCode p))

theorem genCheck_eq : genCheck = true := by decide +kernel

theorem d_genIdx (k : Fin 4) : (d (genIdx k) : NativeSporadic.M12) = g * u k * g⁻¹ := by
  apply Subtype.ext
  change dPerm (genIdx k) = _
  have h := (isFCode_g.mul (isFCode_u k)).mul isFCode_g_inv
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  refine (isFCode_d _).perm_eq (h.congr fun p hp => ?_)
  have := eq_of_beq (all_range (all_range genCheck_eq k.2) hp)
  fin_cases k <;> exact this

def centerCheck : Bool :=
  (List.range 64).all fun z =>
    ((List.range 64).all fun j => mIdx z j == mIdx j z) == (z == 0 || z == 27)

theorem centerCheck_eq : centerCheck = true := by decide +kernel

theorem mem_center_iff (s : S) : s ∈ Subgroup.center S ↔ s = 1 ∨ s = d 27 := by
  obtain ⟨z, rfl⟩ := d_surjective s
  have hz : ((List.range 64).all fun j => mIdx z j == mIdx j z) = (z.val == 0 || z.val == 27) :=
    eq_of_beq (all_range centerCheck_eq z.2)
  have key : d z ∈ Subgroup.center S ↔
      ((List.range 64).all fun j => mIdx z j == mIdx j z) = true := by
    rw [Subgroup.mem_center_iff, List.all_eq_true]
    constructor
    · intro h j hj
      rw [List.mem_range] at hj
      have := h (d ⟨j, hj⟩)
      rw [← d_mul, ← d_mul] at this
      exact beq_iff_eq.2 (congrArg Fin.val (d_injective this)).symm
    · intro h t
      obtain ⟨j, rfl⟩ := d_surjective t
      rw [← d_mul, ← d_mul]
      exact congrArg d (Fin.ext (eq_of_beq (h j (List.mem_range.2 j.2))).symm)
  rw [key, hz, ← d_zero, d_injective.eq_iff, d_injective.eq_iff, Fin.ext_iff, Fin.ext_iff]
  simp

theorem orderOf_d27 : orderOf (d 27) = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [sq, ← d_mul, ← d_zero]
    exact congrArg d (by decide +kernel : mTab 27 27 = 0)
  · have := d_injective (h.trans d_zero.symm)
    exact absurd this (by decide)

theorem card_fixed_d27 : (Finset.univ.filter fun p : Fin 12 => dPerm 27 p = p).card = 4 := by
  rw [card_fixed_eq (isFCode_d 27)]
  decide +kernel

end CFSG.ComponentClassification.M12Cover.InternalSylow
