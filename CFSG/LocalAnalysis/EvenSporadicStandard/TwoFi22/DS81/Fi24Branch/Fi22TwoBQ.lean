module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBGens
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ExtraspecialAction
public import Certificates.Certificate450106

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore CFSG.Certificates.ExtraspecialNF
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ExtraspecialAction

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def cMat (i j : Fin 10) : ZMod 2 := if cBit i j then 1 else 0

theorem cMat_mul_self : Matrix.of cMat * Matrix.of cMat = 1 := by decide

theorem nondegenerate_cMat : Nondegenerate cMat := .of_mul_eq_one cMat_mul_self

@[expose] def qGen (j : Fin 10) : Equiv.Perm (Fin 3510) :=
  Quiver.SchreierGraph.evalWord cGen (toLetters 10 (qWords.getD j []))

@[expose] def codeVec (code : ℕ) : Fin 10 → ZMod 2 := fun i => if code.testBit i then 1 else 0

@[expose] def codeSgn (code : ℕ) : ZMod 2 := if code.testBit 10 then 1 else 0

@[expose] def actCode (k j : Fin 10) : ℕ := actCodes.getD (10 * k + j) 0

@[expose] def actVec (k j : Fin 10) : Fin 10 → ZMod 2 := codeVec (actCode k j)

@[expose] def actSgn (k j : Fin 10) : ZMod 2 := codeSgn (actCode k j)

@[expose] def actMat (k : Fin 10) : Matrix (Fin 10) (Fin 10) (ZMod 2) := Matrix.of fun i j =>
  actVec k j i

theorem getElem!_ofFn_arr {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem rep_tPowA {t : Array ℕ} {T : Equiv.Perm (Fin 3510)} (hT : Rep 3510 t T) (b : Bool) :
    Rep 3510 (tPowA t b) (T ^ (if b then 1 else 0 : ZMod 2).val) := by
  cases b
  · have e : T ^ (if false then 1 else 0 : ZMod 2).val = 1 := by simp
    rw [e]
    simpa [tPowA] using (rep_idA (n := 3510))
  · simpa [val_one_two, tPowA] using hT

theorem rep_prodA {m : ℕ} {f : Fin m → Array ℕ} {g : Fin m → Equiv.Perm (Fin 3510)}
    (h : ∀ i, Rep 3510 (f i) (g i)) : Rep 3510 (prodA (List.ofFn f)) (List.ofFn g).prod := by
  induction m with
  | zero => simpa [prodA] using (rep_idA (n := 3510))
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, prodA, List.prod_cons]
    exact rep_compA (h 0) (ih fun i => h i.succ)

theorem rep_monA {qa : Array (Array ℕ)} {Q : Fin 10 → Equiv.Perm (Fin 3510)}
    (hQ : ∀ j : Fin 10, Rep 3510 qa[(j : ℕ)]! (Q j)) (v : ℕ) :
    Rep 3510 (monA qa v) (mon Q (codeVec v)) := by
  unfold monA mon
  refine rep_prodA (f := fun i : Fin 10 => if v.testBit i then qa[(i : ℕ)]! else idA 3510)
    (g := fun i : Fin 10 => Q i ^ (codeVec v i).val) fun i => ?_
  by_cases hb : v.testBit i
  · simpa [codeVec, hb, val_one_two] using hQ i
  · simpa [codeVec, hb] using (rep_idA (n := 3510))

theorem rep_nfA {t : Array ℕ} {T : Equiv.Perm (Fin 3510)} (hT : Rep 3510 t T)
    {qa : Array (Array ℕ)} {Q : Fin 10 → Equiv.Perm (Fin 3510)}
    (hQ : ∀ j : Fin 10, Rep 3510 qa[(j : ℕ)]! (Q j)) (code : ℕ) :
    Rep 3510 (nfA t qa code) (nf T Q (codeSgn code) (codeVec code)) :=
  rep_compA (rep_tPowA hT (code.testBit 10)) (rep_monA hQ code)

theorem relOK_spec {t : Array ℕ} {T : Equiv.Perm (Fin 3510)} (hT : Rep 3510 t T)
    {qa : Array (Array ℕ)} {Q : Fin 10 → Equiv.Perm (Fin 3510)}
    (hQ : ∀ j : Fin 10, Rep 3510 qa[(j : ℕ)]! (Q j)) (h : relOK t qa = true) :
    T * T = 1 ∧ T ≠ 1 ∧ (∀ j, T * Q j = Q j * T) ∧ ∀ j, Q j * Q j = 1 := by
  unfold relOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨eq_of_eqA (rep_compA hT hT) rep_idA h1, fun hT1 => ?_, fun j => ?_, fun j => ?_⟩
  · have := (eqA_iff hT rep_idA).2 hT1
    rw [this] at h2
    exact absurd h2 (by simp)
  · exact eq_of_eqA (rep_compA hT (hQ j)) (rep_compA (hQ j) hT) (h3 j j.2).1
  · exact eq_of_eqA (rep_compA (hQ j) (hQ j)) rep_idA (h3 j j.2).2

theorem commOK_spec {t : Array ℕ} {T : Equiv.Perm (Fin 3510)} (hT : Rep 3510 t T)
    {qa : Array (Array ℕ)} {Q : Fin 10 → Equiv.Perm (Fin 3510)}
    (hQ : ∀ j : Fin 10, Rep 3510 qa[(j : ℕ)]! (Q j)) (h : commOK t qa = true) :
    ∀ i j : Fin 10, Q i * Q j = Q j * Q i * T ^ (cMat i j).val := by
  unfold commOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  intro i j
  exact eq_of_eqA (rep_compA (hQ i) (hQ j))
    (rep_compA (rep_compA (hQ j) (hQ i)) (rep_tPowA hT (cBit i j))) (h i i.2 j j.2)

theorem conjOK_spec {S Si : Array (Array ℕ)} {G : Fin 10 → Equiv.Perm (Fin 3510)}
    (hS : ∀ k : Fin 10, Rep 3510 S[(k : ℕ)]! (G k))
    (hSi : ∀ k : Fin 10, Rep 3510 Si[(k : ℕ)]! (G k)⁻¹)
    {t : Array ℕ} {T : Equiv.Perm (Fin 3510)} (hT : Rep 3510 t T)
    {qa : Array (Array ℕ)} {Q : Fin 10 → Equiv.Perm (Fin 3510)}
    (hQ : ∀ j : Fin 10, Rep 3510 qa[(j : ℕ)]! (Q j)) (h : conjOK S Si t qa = true) :
    ∀ k j : Fin 10, G k * Q j * (G k)⁻¹ = nf T Q (actSgn k j) (actVec k j) := by
  unfold conjOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  intro k j
  exact eq_of_eqA (rep_compA (rep_compA (hS k) (hQ j)) (hSi k)) (rep_nfA hT hQ (actCode k j))
    (h k k.2 j j.2)

theorem centOK_spec {S : Array (Array ℕ)} {G : Fin 10 → Equiv.Perm (Fin 3510)}
    (hS : ∀ k : Fin 10, Rep 3510 S[(k : ℕ)]! (G k)) {t : Array ℕ} {T : Equiv.Perm (Fin 3510)}
    (hT : Rep 3510 t T) (h : centOK S t = true) : ∀ k, G k * T = T * G k := by
  unfold centOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  intro k
  exact eq_of_eqA (rep_compA (hS k) hT) (rep_compA hT (hS k)) (h k k.2)

theorem rep_genArr (h : Fin 10) : Rep 3510 (genArr h) (cGen h) :=
  rep_fi22CentPerm (cLine_lt h)

theorem rep_t1Arr : Rep 3510 t1Arr t1 :=
  rep_fi22ExtRep (k := 1) (by norm_num)

theorem lettersOK_qWords {j : ℕ} (hj : j < 10) (h : qWordsOK = true) :
    lettersOK 10 (qWords.getD j []) = true := by
  unfold qWordsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hl, hall⟩ := h
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hall _ (List.getElem_mem _)

theorem checkQ_spec
    (h : checkQ () = true) :
    Rel t1 qGen cMat ∧ t1 ≠ 1 ∧
      (∀ k j : Fin 10, cGen k * qGen j * (cGen k)⁻¹ = nf t1 qGen (actSgn k j) (actVec k j)) ∧
      ∀ k : Fin 10, cGen k * t1 = t1 * cGen k := by
  unfold checkQ at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  set S : Array (Array ℕ) := Array.ofFn (n := 10) fun h => genArr h with hS
  set Si : Array (Array ℕ) := S.map (invCand 3510) with hSi
  set qa : Array (Array ℕ) :=
    Array.ofFn (n := 10) fun j => wordA 3510 S Si (qWords.getD j []) with hqa
  have hSrep : ∀ k : Fin 10, Rep 3510 S[(k : ℕ)]! (cGen k) := by
    intro k
    rw [hS, getElem!_ofFn_arr _ k.2]
    exact rep_genArr k
  have hSirep : ∀ k : Fin 10, Rep 3510 Si[(k : ℕ)]! (cGen k)⁻¹ := by
    intro k
    have hk : (k : ℕ) < S.size := by simp [hS]
    rw [hSi, getElem!_pos (S.map (invCand 3510)) (k : ℕ) (by simpa using hk), Array.getElem_map,
      ← getElem!_pos S (k : ℕ) hk, hS, getElem!_ofFn_arr _ k.2]
    exact rep_fi22CentPerm_inv (cLine_lt k)
  have hqrep : ∀ j : Fin 10, Rep 3510 qa[(j : ℕ)]! (qGen j) := by
    intro j
    rw [hqa, getElem!_ofFn_arr _ j.2]
    exact rep_wordA (gs := fun h => fi22CentPerm (cLine h)) (j := 10)
      (fun h hh => hSrep ⟨h, hh⟩) (fun h hh => hSirep ⟨h, hh⟩) _ (lettersOK_qWords j.2 h1)
  obtain ⟨hz, hz1, hzc, hqq⟩ := relOK_spec rep_t1Arr hqrep h2
  exact ⟨⟨hz, hzc, hqq, commOK_spec rep_t1Arr hqrep h3⟩, hz1,
    conjOK_spec hSrep hSirep rep_t1Arr hqrep h4, centOK_spec hSrep rep_t1Arr h5⟩

@[expose] def Qbar : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure (insert t1 (Set.range qGen))

theorem t1_mem_Qbar : t1 ∈ Qbar := Subgroup.subset_closure (Set.mem_insert _ _)

theorem qGen_mem_Qbar (j : Fin 10) : qGen j ∈ Qbar :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self j))

theorem rel_qGen :
    Rel t1 qGen cMat :=
  (checkQ_spec Certificates.certificate450106).1

theorem t1_ne_one :
    t1 ≠ 1 :=
  (checkQ_spec Certificates.certificate450106).2.1

theorem cGen_conj_qGen
    (k j : Fin 10) :
    cGen k * qGen j * (cGen k)⁻¹ = nf t1 qGen (actSgn k j) (actVec k j) :=
  (checkQ_spec Certificates.certificate450106).2.2.1 k j

theorem cGen_comm_t1
    (k : Fin 10) : cGen k * t1 = t1 * cGen k :=
  (checkQ_spec Certificates.certificate450106).2.2.2 k

theorem injective_nf_qGen :
    Function.Injective (Function.uncurry (nf t1 qGen)) :=
  injective_nf_of_nondeg rel_qGen t1_ne_one nondegenerate_cMat

theorem card_Qbar :
    Nat.card Qbar = 2 ^ 11 :=
  card_closure rel_qGen injective_nf_qGen

theorem map_center_Qbar :
    (Subgroup.center Qbar).map Qbar.subtype = Subgroup.zpowers t1 :=
  map_center_eq rel_qGen injective_nf_qGen nondegenerate_cMat

theorem exists_nf_of_mem_Qbar
    {x : Equiv.Perm (Fin 3510)} (hx : x ∈ Qbar) :
    ∃ (s : ZMod 2) (v : Fin 10 → ZMod 2), nf t1 qGen s v = x :=
  (mem_closure_iff rel_qGen).1 hx

theorem sq_mem_zpowers_t1
    {x : Equiv.Perm (Fin 3510)} (hx : x ∈ Qbar) :
    x ^ 2 ∈ Subgroup.zpowers t1 := by
  obtain ⟨s, v, rfl⟩ := exists_nf_of_mem_Qbar hx
  rw [sq, nf_mul_self rel_qGen]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers t1) _

theorem commutator_mem_zpowers_t1
    {x y : Equiv.Perm (Fin 3510)} (hx : x ∈ Qbar)
    (hy : y ∈ Qbar) : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers t1 := by
  obtain ⟨s, v, rfl⟩ := exists_nf_of_mem_Qbar hx
  obtain ⟨t, w, rfl⟩ := exists_nf_of_mem_Qbar hy
  have hz1 := t1_ne_one
  have e := commutator_eq_zpow (rel_qGen) (rel_qGen.symm_of_ne_one hz1)
    (rel_qGen.diag_eq_zero hz1) s t v w
  rw [commutatorElement_def] at e
  rw [e]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers t1) _

theorem cGen_conj_t1
    (k : Fin 10) : cGen k * t1 * (cGen k)⁻¹ = t1 := by
  rw [cGen_comm_t1, mul_inv_cancel_right]

theorem t1_mem_Cbar :
    t1 ∈ Cbar := by
  have hq : ∀ j, qGen j ∈ Cbar := fun j =>
    closure_cGen_le (Quiver.SchreierGraph.evalWord_mem_closure cGen _)
  have h := rel_qGen.comm 0 1
  have hc : cMat 0 1 = 1 := by decide
  rw [hc, val_one_two, pow_one] at h
  have e : t1 = (qGen 1 * qGen 0)⁻¹ * (qGen 0 * qGen 1) := by rw [h]; group
  rw [e]
  exact mul_mem (inv_mem (mul_mem (hq 1) (hq 0))) (mul_mem (hq 0) (hq 1))

theorem Qbar_le_Cbar :
    Qbar ≤ Cbar := by
  rw [Qbar, Subgroup.closure_le]
  rintro x (rfl | ⟨j, rfl⟩)
  · exact t1_mem_Cbar
  · exact closure_cGen_le (Quiver.SchreierGraph.evalWord_mem_closure cGen _)

theorem cGen_conj_nf
    (k : Fin 10) (s : ZMod 2) (v : Fin 10 → ZMod 2) :
    HasVec t1 qGen (cGen k * nf t1 qGen s v * (cGen k)⁻¹) ((actMat k).mulVec v) :=
  conj_nf_hasVec rel_qGen (cGen_conj_t1 k) (actMat k) (fun j => ⟨actSgn k j, cGen_conj_qGen k j⟩)
    s v

theorem central_iff_mem_zpowers_t1
    {x : Equiv.Perm (Fin 3510)} (hx : x ∈ Qbar) :
    (∀ y ∈ Qbar, x * y = y * x) ↔ x ∈ Subgroup.zpowers t1 := by
  rw [← map_center_Qbar]
  constructor
  · intro hc
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  · rintro ⟨⟨x', hx'⟩, hcen, rfl⟩ y hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨y, hy⟩)).symm

theorem det_cMat_ne_zero : (Matrix.of cMat).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det cMat_mul_self
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem card_le_of_abelian
    {B : Subgroup (Equiv.Perm (Fin 3510))} (hB : B ≤ Qbar)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 2 ^ 6 := by
  have hrel := rel_qGen
  have hz1 := t1_ne_one
  have hsymm := hrel.symm_of_ne_one hz1
  have hdiag := hrel.diag_eq_zero hz1
  let W : Submodule (ZMod 2) (Fin 10 → ZMod 2) :=
    { carrier := {v | ∃ s, nf t1 qGen s v ∈ B}
      add_mem' := by
        rintro v w ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t + collect cMat v w, by rw [← nf_mul_nf hrel]; exact B.mul_mem hs ht⟩
      zero_mem' := ⟨0, by rw [nf_zero_zero]; exact B.one_mem⟩
      smul_mem' := by
        rintro a v ⟨s, hs⟩
        rcases zmod_two_cases a with rfl | rfl
        · exact ⟨0, by rw [zero_smul, nf_zero_zero]; exact B.one_mem⟩
        · exact ⟨s, by rwa [one_smul]⟩ }
  have hW : ∀ v ∈ W, ∀ w ∈ W, bil cMat v w = 0 := by
    rintro v ⟨s, hs⟩ w ⟨t, ht⟩
    have h1 := nf_mul_comm hrel hsymm hdiag s t v w
    rw [hab _ hs _ ht, eq_comm, mul_eq_left] at h1
    exact zpow_val_inj hz1 (by rw [h1]; rfl)
  have hcard := card_sq_le_of_isotropic det_cMat_ne_zero W hW
  have hW5 : Nat.card W ≤ 2 ^ 5 := by
    by_contra hlt
    have := Nat.pow_lt_pow_left (not_le.1 hlt) (two_ne_zero)
    norm_num at this hcard
    omega
  have key : ∀ x : B, ∃ (s : ZMod 2) (v : Fin 10 → ZMod 2), nf t1 qGen s v = x :=
    fun x => exists_nf_of_mem_Qbar (hB x.2)
  choose s v hsv using key
  have hvW : ∀ x : B, v x ∈ W := fun x => ⟨s x, by rw [hsv x]; exact x.2⟩
  have hinj : Function.Injective fun x : B => ((s x, ⟨v x, hvW x⟩) : ZMod 2 × W) := by
    intro x y hxy
    have h1 : s x = s y := congrArg Prod.fst hxy
    have h2 : v x = v y := congrArg (fun p => (p.2 : Fin 10 → ZMod 2)) hxy
    apply Subtype.ext
    rw [← hsv x, ← hsv y, h1, h2]
  calc Nat.card B ≤ Nat.card (ZMod 2 × W) := Nat.card_le_card_of_injective _ hinj
    _ = 2 * Nat.card W := by rw [Nat.card_prod, Nat.card_zmod]
    _ ≤ 2 ^ 6 := by omega

theorem vec_eq_of_mul_inv_mem_zpowers
    {x y : Equiv.Perm (Fin 3510)} {s t : ZMod 2}
    {v w : Fin 10 → ZMod 2} (hx : x = nf t1 qGen s v) (hy : y = nf t1 qGen t w)
    (h : x * y⁻¹ ∈ Subgroup.zpowers t1) : v = w := by
  obtain ⟨b, hb⟩ := (mem_zpowers_iff_exists rel_qGen).1 h
  have hx' : x = nf t1 qGen b 0 * y := by
    rw [nf_zero_vec, hb]
    group
  have e : nf t1 qGen b 0 * nf t1 qGen t w = nf t1 qGen (b + t + collect cMat 0 w) (0 + w) :=
    nf_mul_nf rel_qGen b t 0 w
  have hc : collect cMat (0 : Fin 10 → ZMod 2) w = 0 := by simp [collect]
  rw [hy, e, hc, zero_add] at hx'
  rw [hx] at hx'
  exact (eq_of_nf_eq injective_nf_qGen hx').2

theorem hasVec_conj_two
    (i j m : Fin 10) :
    HasVec t1 qGen ((cGen i * cGen j) * qGen m * (cGen i * cGen j)⁻¹)
      ((actMat i).mulVec ((actMat j).mulVec (Pi.single m 1))) := by
  obtain ⟨s, hs⟩ := cGen_conj_nf j 0 (Pi.single m 1)
  rw [nf_single] at hs
  obtain ⟨s', hs'⟩ := cGen_conj_nf i s ((actMat j).mulVec (Pi.single m 1))
  refine ⟨s', ?_⟩
  rw [← hs', ← hs]
  group

theorem exists_comm_not_mem_cent_mul :
    ∃ a ∈ Cbar, ∃ b ∈ Cbar, ∀ d ∈ Subgroup.centralizer (Qbar : Set (Equiv.Perm (Fin 3510))),
      ∀ q ∈ Qbar, a * b * a⁻¹ * b⁻¹ ≠ d * q := by
  refine ⟨cGen 1, cGen_mem_Cbar 1, cGen 2, cGen_mem_Cbar 2, ?_⟩
  intro d hd q hq hc
  obtain ⟨s₁, hs₁⟩ := hasVec_conj_two 1 2 0
  obtain ⟨s₂, hs₂⟩ := hasVec_conj_two 2 1 0
  set x : Equiv.Perm (Fin 3510) := (cGen 2 * cGen 1) * qGen 0 * (cGen 2 * cGen 1)⁻¹ with hx
  have hxQ : x ∈ Qbar := by rw [hs₂]; exact nf_mem_closure _ _ _ _
  have e1 : (cGen 1 * cGen 2 * (cGen 1)⁻¹ * (cGen 2)⁻¹) * x *
      (cGen 1 * cGen 2 * (cGen 1)⁻¹ * (cGen 2)⁻¹)⁻¹ =
      (cGen 1 * cGen 2) * qGen 0 * (cGen 1 * cGen 2)⁻¹ := by rw [hx]; group
  have hyQ : q * x * q⁻¹ ∈ Qbar := Qbar.mul_mem (Qbar.mul_mem hq hxQ) (Qbar.inv_mem hq)
  have e2 : (d * q) * x * (d * q)⁻¹ = q * x * q⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.1 hd _ hyQ
    calc (d * q) * x * (d * q)⁻¹ = d * (q * x * q⁻¹) * d⁻¹ := by group
      _ = q * x * q⁻¹ := by rw [← h]; group
  have h3 : ((cGen 1 * cGen 2) * qGen 0 * (cGen 1 * cGen 2)⁻¹) * x⁻¹ ∈ Subgroup.zpowers t1 := by
    rw [← e1, hc, e2]
    exact commutator_mem_zpowers_t1 hq hxQ
  have h4 := vec_eq_of_mul_inv_mem_zpowers hs₁ hs₂ h3
  revert h4
  decide

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
