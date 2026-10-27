module

public import CFSG.LargeExtraspecial.AS62C36RigidInputs
public import CFSG.LargeExtraspecial.AS62Model2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Emb

public section

namespace CFSG.LargeExtraspecial.AS62.Rigid

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 CFSG.Quasithin.H13.F431.U42Aut
  CFSG.LargeExtraspecial.AS62.Sem

@[expose] def RepA (a : Array Nat) (σ : P45) : Prop := RepL a.toList σ

@[expose] def RepE (e : Array Nat × Array Nat) (σ : P45) : Prop := RepA e.1 σ ∧ RepA e.2 σ⁻¹

theorem toList_getD (a : Array Nat) (j : Nat) : a.toList.getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem toList_cmpA (a b : Array Nat) : (cmpA a b).toList = compL a.toList b.toList := by
  simp [cmpA, compL, toList_getD]

theorem toList_idA : idA.toList = List.range 45 := by
  simp [idA]

theorem toList_evalA {α : Type} (L : α × Bool → Array Nat) (w : List (α × Bool)) :
    (evalA L w).toList = evalLs (fun x => (L x).toList) w := by
  induction w with
  | nil => simp [evalA, evalLs, toList_idA]
  | cons a w ih =>
    simp only [evalA, evalLs, List.foldr_cons, toList_cmpA] at ih ⊢
    rw [ih]

theorem repA_cmpA {a b : Array Nat} {σ τ : P45} (ha : RepA a σ) (hb : RepA b τ) :
    RepA (cmpA a b) (σ * τ) := by
  unfold RepA at *
  rw [toList_cmpA]
  exact repL_mul ha hb

theorem repA_idA : RepA idA 1 := by
  unfold RepA
  rw [toList_idA]
  exact repL_one 45

theorem eq_of_repA {a b : Array Nat} {σ : P45} (ha : RepA a σ) (hb : RepA b σ) : a = b :=
  Array.ext' (repL_unique ha hb)

theorem eq_of_repA' {a : Array Nat} {σ τ : P45} (hσ : RepA a σ) (hτ : RepA a τ) : σ = τ :=
  eq_of_repL hσ hτ

theorem repA_evalA {ι : Type} (σ : ι → P45) (L : ι × Bool → Array Nat)
    (hL : ∀ x, RepA (L x) (cond x.2 (σ x.1) (σ x.1)⁻¹)) (w : List (ι × Bool)) :
    RepA (evalA L w) (FreeGroup.lift σ (FreeGroup.mk w)) := by
  unfold RepA at *
  rw [toList_evalA]
  exact repL_evalLs σ _ hL w

theorem lift_mk_invWord {ι : Type} {H : Type*} [Group H] (f : ι → H) (w : List (ι × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (invWord w)) = (FreeGroup.lift f (FreeGroup.mk w))⁻¹ := by
  rw [← map_inv, FreeGroup.inv_mk]
  rfl

theorem repA_letA {k : ℕ} (hk : k < 6) (b : Bool) :
    RepA (letA (k, b)) (cond b (genU k : P45) (genU k : P45)⁻¹) := by
  cases b
  · exact repL_genU_inv hk
  · exact repL_genU hk

theorem repA_genA {k : ℕ} (hk : k < 6) : RepA (genA k) (genU k : P45) := repL_genU hk

theorem repA_genInvA {k : ℕ} (hk : k < 6) : RepA (genInvA k) (genU k : P45)⁻¹ :=
  repL_genU_inv hk

theorem repE_one : RepE (idA, idA) 1 := ⟨repA_idA, by rw [inv_one]; exact repA_idA⟩

theorem repE_mul {e e' : Array Nat × Array Nat} {σ τ : P45} (he : RepE e σ) (he' : RepE e' τ) :
    RepE (cmpA e.1 e'.1, cmpA e'.2 e.2) (σ * τ) :=
  ⟨repA_cmpA he.1 he'.1, by rw [mul_inv_rev]; exact repA_cmpA he'.2 he.2⟩

theorem repE_gen {k : ℕ} (hk : k < 6) : RepE (genA k, genInvA k) (genU k : P45) :=
  ⟨repA_genA hk, repA_genInvA hk⟩

noncomputable def bVal (k : Fin 192) : ↥B0 := FreeGroup.lift genB0 (FreeGroup.mk (bWord k))

theorem coe_bVal (k : Fin 192) :
    (((bVal k : ↥B0) : Y) : P45) =
      FreeGroup.lift (fun i : Fin 4 => (genU i.val : P45)) (FreeGroup.mk (bWord k)) :=
  hom_freeLift (Xs.subtype.comp B0.subtype) genB0 (FreeGroup.mk (bWord k))

theorem repE_bPair (k : Fin 192) : RepE (bPair k) (((bVal k : ↥B0) : Y) : P45) := by
  rw [coe_bVal]
  have hL : ∀ x : Fin 4 × Bool, RepA (letA (x.1.val, x.2))
      (cond x.2 (genU x.1.val : P45) (genU x.1.val : P45)⁻¹) :=
    fun x => repA_letA (x.1.isLt.trans (by norm_num)) x.2
  refine ⟨repA_evalA (fun i : Fin 4 => (genU i.val : P45)) _ hL _, ?_⟩
  rw [← lift_mk_invWord]
  exact repA_evalA (fun i : Fin 4 => (genU i.val : P45)) _ hL _

noncomputable def p2Val (k : Fin 960) : ↥P2 := FreeGroup.lift genP2 (FreeGroup.mk (h2Word k))

theorem coe_p2Val (k : Fin 960) :
    (((p2Val k : ↥P2) : Y) : P45) =
      FreeGroup.lift (fun i : Fin 5 => (genU (code2 i) : P45)) (FreeGroup.mk (h2Word k)) :=
  hom_freeLift (Xs.subtype.comp P2.subtype) genP2 (FreeGroup.mk (h2Word k))

theorem repE_p2Pair (k : Fin 960) : RepE (p2Pair k) (((p2Val k : ↥P2) : Y) : P45) := by
  rw [coe_p2Val]
  have hL : ∀ x : Fin 5 × Bool, RepA (letA (code2 x.1, x.2))
      (cond x.2 (genU (code2 x.1) : P45) (genU (code2 x.1) : P45)⁻¹) :=
    fun x => repA_letA (code2_lt x.1) x.2
  refine ⟨repA_evalA (fun i : Fin 5 => (genU (code2 i) : P45)) _ hL _, ?_⟩
  rw [← lift_mk_invWord]
  exact repA_evalA (fun i : Fin 5 => (genU (code2 i) : P45)) _ hL _

theorem repE_yPow {j : ℕ} (hj : j < 3) : RepE (yPow j) ((genU 4 : P45) ^ j) := by
  unfold yPow
  split_ifs with h0 h1
  · subst h0
    simpa using repE_one
  · subst h1
    simpa using repE_gen (k := 4) (by norm_num)
  · have h2 : j = 2 := by omega
    subst h2
    have := repE_mul (repE_gen (k := 4) (by norm_num)) (repE_gen (k := 4) (by norm_num))
    rw [← pow_two] at this
    exact this

noncomputable def p1Val (i : Fin 576) : ↥P1 :=
  genP1 4 ^ (i.val / 192) *
    Subgroup.inclusion B0_le_P1 (bVal ⟨i.val % 192, Nat.mod_lt _ (by norm_num)⟩)

@[expose] def p1Pair (i : Fin 576) : Array Nat × Array Nat :=
  let y := yPow (i.val / 192)
  let b := (bTab ()).getD (i.val % 192) (idA, idA)
  (cmpA y.1 b.1, cmpA b.2 y.2)

theorem p1Tab_eq : p1Tab () = Array.ofFn p1Pair := rfl

theorem p2Tab_eq : p2Tab () = Array.ofFn p2Pair := rfl

theorem bTab_eq : bTab () = Array.ofFn bPair := rfl

theorem getD_bTab (k : Fin 192) : (bTab ()).getD k.val (idA, idA) = bPair k := by
  rw [bTab_eq, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp

theorem coe_p1Val (i : Fin 576) :
    (((p1Val i : ↥P1) : Y) : P45) = (genU 4 : P45) ^ (i.val / 192) *
      (((bVal ⟨i.val % 192, Nat.mod_lt _ (by norm_num)⟩ : ↥B0) : Y) : P45) := by
  simp [p1Val, genP1]

theorem repE_p1Pair (i : Fin 576) : RepE (p1Pair i) (((p1Val i : ↥P1) : Y) : P45) := by
  rw [coe_p1Val]
  have h := repE_mul (repE_yPow (j := i.val / 192) (by omega))
    (repE_bPair ⟨i.val % 192, Nat.mod_lt _ (by norm_num)⟩)
  unfold p1Pair
  rw [getD_bTab ⟨i.val % 192, Nat.mod_lt _ (by norm_num)⟩]
  exact h

theorem nodup_of_distinctTab {T : Array (Array Nat × Array Nat)} (h : distinctTab T = true) :
    (T.toList.map Prod.fst).Nodup := by
  unfold distinctTab at h
  exact of_decide_eq_true h

theorem injective_bPair (h : bDistinct () = true) :
    Function.Injective fun k : Fin 192 => (bPair k).1 := by
  have h' := nodup_of_distinctTab (T := bTab ()) h
  rw [bTab_eq, Array.toList_ofFn, List.map_ofFn, List.nodup_ofFn] at h'
  exact h'

theorem injective_p1Pair (h : p1Distinct () = true) :
    Function.Injective fun i : Fin 576 => (p1Pair i).1 := by
  have h' := nodup_of_distinctTab (T := p1Tab ()) h
  rw [p1Tab_eq, Array.toList_ofFn, List.map_ofFn, List.nodup_ofFn] at h'
  exact h'

theorem injective_p2Pair (h : p2Distinct () = true) :
    Function.Injective fun k : Fin 960 => (p2Pair k).1 := by
  have h' := nodup_of_distinctTab (T := p2Tab ()) h
  rw [p2Tab_eq, Array.toList_ofFn, List.map_ofFn, List.nodup_ofFn] at h'
  exact h'

theorem injective_bVal (h : bDistinct () = true) : Function.Injective bVal := by
  intro k k' hkk
  apply injective_bPair h
  have e : ((bVal k : Y) : P45) = ((bVal k' : Y) : P45) :=
    congrArg (fun x : ↥B0 => ((x : Y) : P45)) hkk
  have e2 := (repE_bPair k').1
  rw [← e] at e2
  exact eq_of_repA (repE_bPair k).1 e2

theorem injective_p1Val (h : p1Distinct () = true) : Function.Injective p1Val := by
  intro k k' hkk
  apply injective_p1Pair h
  have e : ((p1Val k : Y) : P45) = ((p1Val k' : Y) : P45) :=
    congrArg (fun x : ↥P1 => ((x : Y) : P45)) hkk
  have e2 := (repE_p1Pair k').1
  rw [← e] at e2
  exact eq_of_repA (repE_p1Pair k).1 e2

theorem injective_p2Val (h : p2Distinct () = true) : Function.Injective p2Val := by
  intro k k' hkk
  apply injective_p2Pair h
  have e : ((p2Val k : Y) : P45) = ((p2Val k' : Y) : P45) :=
    congrArg (fun x : ↥P2 => ((x : Y) : P45)) hkk
  have e2 := (repE_p2Pair k').1
  rw [← e] at e2
  exact eq_of_repA (repE_p2Pair k).1 e2

theorem bVal_surjective
    (h : bDistinct () = true) : Function.Surjective bVal :=
  ((injective_bVal h).bijective_of_nat_card_le (by simp [card_B0])).2

theorem p1Val_surjective
    (h : p1Distinct () = true) : Function.Surjective p1Val :=
  ((injective_p1Val h).bijective_of_nat_card_le (by simp [card_P1])).2

theorem p2Val_surjective
    (h : p2Distinct () = true) : Function.Surjective p2Val :=
  ((injective_p2Val h).bijective_of_nat_card_le (by simp [card_P2])).2

theorem repA_fhatA' : RepA fhatA' fhat := repL_fhat

theorem incl_mem_Bh {y : Y} (hy : y ∈ B0) : incl y ∈ Bh := by
  rw [← Subgroup.mem_comap, comap_Bh]
  exact hy

theorem mem_bhTab {e : Array Nat × Array Nat} (he : e ∈ bhTab ()) :
    ∃ φ : Ah, φ ∈ Bh ∧ RepE e (φ : P45) := by
  unfold bhTab at he
  dsimp only at he
  rw [Array.mem_append] at he
  rcases he with he | he
  · rw [bTab_eq, Array.mem_ofFn] at he
    obtain ⟨k, rfl⟩ := he
    refine ⟨incl (bVal k : Y), incl_mem_Bh (bVal k).2, ?_⟩
    rw [coe_incl]
    exact repE_bPair k
  · rw [Array.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [bTab_eq, Array.mem_ofFn] at ha
    obtain ⟨k, rfl⟩ := ha
    refine ⟨incl (bVal k : Y) * fhatA, Bh.mul_mem (incl_mem_Bh (bVal k).2) fhatA_mem_Bh, ?_⟩
    rw [Subgroup.coe_mul, coe_incl, fhatA_coe]
    refine ⟨repA_cmpA (repE_bPair k).1 repA_fhatA', ?_⟩
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right fhat_sq]
    exact repA_cmpA repA_fhatA' (repE_bPair k).2

theorem relOK_iff {ι : Type} (g : ι → Array Nat × Array Nat) (σ : ι → P45)
    (hg : ∀ i, RepE (g i) (σ i)) (w : List (ι × Bool)) :
    (evalA (fun a : ι × Bool => if a.2 then (g a.1).1 else (g a.1).2) w == idA) = true ↔
      FreeGroup.lift σ (FreeGroup.mk w) = 1 := by
  have hL : ∀ x : ι × Bool, RepA (if x.2 then (g x.1).1 else (g x.1).2)
      (cond x.2 (σ x.1) (σ x.1)⁻¹) := by
    rintro ⟨i, b⟩
    cases b
    · exact (hg i).2
    · exact (hg i).1
  have h := repA_evalA σ _ hL w
  rw [beq_iff_eq]
  constructor
  · intro he
    rw [he] at h
    exact eq_of_repA' h repA_idA
  · intro h1
    rw [h1] at h
    exact eq_of_repA h repA_idA

theorem lift_mk_congr {ι : Type} {H : Type*} [Group H] {σ τ : ι → H} {w : List (ι × Bool)}
    (h : ∀ x ∈ w, σ x.1 = τ x.1) :
    FreeGroup.lift σ (FreeGroup.mk w) = FreeGroup.lift τ (FreeGroup.mk w) := by
  simp only [FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp [h x hx]

theorem lvlOK_of {g : Fin 4 → Array Nat × Array Nat} {σ τ : Fin 4 → P45}
    (hg : ∀ i, RepE (g i) (σ i)) {l : List Nat} {n : Nat}
    (hl : ∀ i ∈ l, i < relsB.length ∧ ∀ x ∈ relsB.getD i [], x.1.val < n)
    (hστ : ∀ j : Fin 4, j.val < n → σ j = τ j)
    (hτ : ∀ w ∈ relsB, FreeGroup.lift τ (FreeGroup.mk w) = 1) : lvlOK g l = true := by
  unfold lvlOK
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨hi1, hi2⟩ := hl i hi
  unfold relOK4
  rw [relOK_iff g σ hg, lift_mk_congr (τ := τ)]
  · refine hτ _ ?_
    rw [List.getD_eq_getElem _ _ hi1]
    exact List.getElem_mem hi1
  · intro x hx
    exact hστ x.1 (hi2 x hx)

theorem conjA_sound {f : Array Nat × Array Nat} {φ : P45} (hf : RepE f φ) {g : Array Nat}
    {σ : P45} (hg : RepA g σ) : RepA (conjA f g) (φ * σ * φ⁻¹) :=
  repA_cmpA (repA_cmpA hf.1 hg) hf.2

theorem conjMatch_sound {f : Array Nat × Array Nat} {φ : P45} (hf : RepE f φ)
    {a b c d u v : Array Nat} {σa σb σc σd σu σv : P45} (ha : RepA a σa) (hb : RepA b σb)
    (hc : RepA c σc) (hd : RepA d σd) (hu : RepA u σu) (hv : RepA v σv)
    (h : conjMatch f a b c d u v = true) :
    φ * (genU 0 : P45) * φ⁻¹ = σa ∧ φ * (genU 1 : P45) * φ⁻¹ = σb ∧
      φ * (genU 2 : P45) * φ⁻¹ = σc ∧ φ * (genU 3 : P45) * φ⁻¹ = σd ∧
      φ * (genU 4 : P45) * φ⁻¹ = σu ∧ φ * (genU 5 : P45) * φ⁻¹ = σv := by
  unfold conjMatch at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨eq_of_repA' (conjA_sound hf (repA_genA (by norm_num))) (h0 ▸ ha), ?_, ?_, ?_, ?_, ?_⟩
  · exact eq_of_repA' (conjA_sound hf (repA_genA (by norm_num))) (h1 ▸ hb)
  · exact eq_of_repA' (conjA_sound hf (repA_genA (by norm_num))) (h2 ▸ hc)
  · exact eq_of_repA' (conjA_sound hf (repA_genA (by norm_num))) (h3 ▸ hd)
  · exact eq_of_repA' (conjA_sound hf (repA_genA (by norm_num))) (h4 ▸ hu)
  · exact eq_of_repA' (conjA_sound hf (repA_genA (by norm_num))) (h5 ▸ hv)

theorem eq_true_of_not_or {x y : Bool} (h : (!x || y) = true) (hx : x = true) : y = true := by
  cases x <;> simp_all

theorem repE_vec4 {e0 e1 e2 e3 : Array Nat × Array Nat} {σ0 σ1 σ2 σ3 : P45} (h0 : RepE e0 σ0)
    (h1 : RepE e1 σ1) (h2 : RepE e2 σ2) (h3 : RepE e3 σ3) :
    ∀ i : Fin 4, RepE (![e0, e1, e2, e3] i) (![σ0, σ1, σ2, σ3] i) := by
  intro i
  fin_cases i <;> simpa

theorem repE_vec5 {e0 e1 e2 e3 e4 : Array Nat × Array Nat} {σ0 σ1 σ2 σ3 σ4 : P45}
    (h0 : RepE e0 σ0) (h1 : RepE e1 σ1) (h2 : RepE e2 σ2) (h3 : RepE e3 σ3) (h4 : RepE e4 σ4) :
    ∀ i : Fin 5, RepE (![e0, e1, e2, e3, e4] i) (![σ0, σ1, σ2, σ3, σ4] i) := by
  intro i
  fin_cases i <;> simpa

theorem rigid_exists_conj
    (hR : rigidCheck () = true) (hbd : bDistinct () = true) (hp1 : p1Distinct () = true)
    (hp2 : p2Distinct () = true) {a b c d u v : Y}
    (ha : a ∈ B0) (hb : b ∈ B0) (hc : c ∈ B0) (hd : d ∈ B0) (hu : u ∈ P1) (hv : v ∈ P2)
    (hrB : ∀ w ∈ relsB,
      FreeGroup.lift ![(a : P45), (b : P45), (c : P45), (d : P45)] (FreeGroup.mk w) = 1)
    (hr1 : ∀ w ∈ rels1Extra,
      FreeGroup.lift ![(a : P45), (b : P45), (c : P45), (d : P45), (u : P45)]
        (FreeGroup.mk w) = 1)
    (hr2 : ∀ w ∈ rels2Extra,
      FreeGroup.lift ![(a : P45), (b : P45), (c : P45), (d : P45), (v : P45)]
        (FreeGroup.mk w) = 1)
    (ha1 : (a : P45) ≠ 1) :
    ∃ f : Ah, f ∈ Bh ∧ (f : P45) * (genU 0 : P45) * (f : P45)⁻¹ = a ∧
      (f : P45) * (genU 1 : P45) * (f : P45)⁻¹ = b ∧
      (f : P45) * (genU 2 : P45) * (f : P45)⁻¹ = c ∧
      (f : P45) * (genU 3 : P45) * (f : P45)⁻¹ = d ∧
      (f : P45) * (genU 4 : P45) * (f : P45)⁻¹ = u ∧
      (f : P45) * (genU 5 : P45) * (f : P45)⁻¹ = v := by
  obtain ⟨ka, hka⟩ := bVal_surjective hbd ⟨a, ha⟩
  obtain ⟨kb, hkb⟩ := bVal_surjective hbd ⟨b, hb⟩
  obtain ⟨kc, hkc⟩ := bVal_surjective hbd ⟨c, hc⟩
  obtain ⟨kd, hkd⟩ := bVal_surjective hbd ⟨d, hd⟩
  obtain ⟨iu, hiu⟩ := p1Val_surjective hp1 ⟨u, hu⟩
  obtain ⟨jv, hjv⟩ := p2Val_surjective hp2 ⟨v, hv⟩
  have ea : RepE (bPair ka) (a : P45) := by simpa [hka] using repE_bPair ka
  have eb : RepE (bPair kb) (b : P45) := by simpa [hkb] using repE_bPair kb
  have ec : RepE (bPair kc) (c : P45) := by simpa [hkc] using repE_bPair kc
  have ed : RepE (bPair kd) (d : P45) := by simpa [hkd] using repE_bPair kd
  have eu : RepE (p1Pair iu) (u : P45) := by simpa [hiu] using repE_p1Pair iu
  have ev : RepE (p2Pair jv) (v : P45) := by simpa [hjv] using repE_p2Pair jv
  have hma : bPair ka ∈ bTab () := by rw [bTab_eq, Array.mem_ofFn]; exact ⟨ka, rfl⟩
  have hmb : bPair kb ∈ bTab () := by rw [bTab_eq, Array.mem_ofFn]; exact ⟨kb, rfl⟩
  have hmc : bPair kc ∈ bTab () := by rw [bTab_eq, Array.mem_ofFn]; exact ⟨kc, rfl⟩
  have hmd : bPair kd ∈ bTab () := by rw [bTab_eq, Array.mem_ofFn]; exact ⟨kd, rfl⟩
  have hmu : p1Pair iu ∈ p1Tab () := by rw [p1Tab_eq, Array.mem_ofFn]; exact ⟨iu, rfl⟩
  have hmv : p2Pair jv ∈ p2Tab () := by rw [p2Tab_eq, Array.mem_ofFn]; exact ⟨jv, rfl⟩
  have hne : ((bPair ka).1 != idA) = true := by
    rw [bne_iff_ne]
    intro h
    apply ha1
    have h' := ea.1
    rw [h] at h'
    exact eq_of_repA' h' repA_idA
  have hl0 : lvlOK ![bPair ka, (idA, idA), (idA, idA), (idA, idA)] [0] = true :=
    lvlOK_of (σ := ![(a : P45), 1, 1, 1]) (τ := ![(a : P45), (b : P45), (c : P45), (d : P45)])
      (repE_vec4 ea repE_one repE_one repE_one) (n := 1) (by decide)
      (fun j hj => by fin_cases j <;> first | rfl | exact absurd hj (by decide)) hrB
  have hl1 : lvlOK ![bPair ka, bPair kb, (idA, idA), (idA, idA)] [1, 5] = true :=
    lvlOK_of (σ := ![(a : P45), (b : P45), 1, 1])
      (τ := ![(a : P45), (b : P45), (c : P45), (d : P45)])
      (repE_vec4 ea eb repE_one repE_one) (n := 2) (by decide)
      (fun j hj => by fin_cases j <;> first | rfl | exact absurd hj (by decide)) hrB
  have hl2 : lvlOK ![bPair ka, bPair kb, bPair kc, (idA, idA)] [2, 6, 9] = true :=
    lvlOK_of (σ := ![(a : P45), (b : P45), (c : P45), 1])
      (τ := ![(a : P45), (b : P45), (c : P45), (d : P45)])
      (repE_vec4 ea eb ec repE_one) (n := 3) (by decide)
      (fun j hj => by fin_cases j <;> first | rfl | exact absurd hj (by decide)) hrB
  have hl3 : lvlOK ![bPair ka, bPair kb, bPair kc, bPair kd] [3, 4, 7, 8, 10] = true :=
    lvlOK_of (σ := ![(a : P45), (b : P45), (c : P45), (d : P45)])
      (τ := ![(a : P45), (b : P45), (c : P45), (d : P45)])
      (repE_vec4 ea eb ec ed) (n := 4) (by decide) (fun j _ => rfl) hrB
  have hr1' : (rels1Extra.all fun w =>
      relOK5 ![bPair ka, bPair kb, bPair kc, bPair kd, p1Pair iu] w) = true := by
    rw [List.all_eq_true]
    intro w hw
    exact (relOK_iff _ _ (repE_vec5 ea eb ec ed eu) w).2 (hr1 w hw)
  have hr2' : (rels2Extra.all fun w =>
      relOK5 ![bPair ka, bPair kb, bPair kc, bPair kd, p2Pair jv] w) = true := by
    rw [List.all_eq_true]
    intro w hw
    exact (relOK_iff _ _ (repE_vec5 ea eb ec ed ev) w).2 (hr2 w hw)
  unfold rigidCheck at hR
  dsimp only at hR
  have h1 := eq_true_of_not_or (Array.all_eq_true'.1 hR _ hma)
    (by rw [Bool.and_eq_true]; exact ⟨hl0, hne⟩)
  have h2 := eq_true_of_not_or (Array.all_eq_true'.1 h1 _ hmb) hl1
  have h3 := eq_true_of_not_or (Array.all_eq_true'.1 h2 _ hmc) hl2
  have h4 := eq_true_of_not_or (Array.all_eq_true'.1 h3 _ hmd) hl3
  have h5 := eq_true_of_not_or (Array.all_eq_true'.1 h4 _ hmu) hr1'
  have h6 := eq_true_of_not_or (Array.all_eq_true'.1 h5 _ hmv) hr2'
  obtain ⟨e, hem, hf⟩ := Array.any_eq_true'.1 h6
  obtain ⟨φ, hφB, hφ⟩ := mem_bhTab hem
  exact ⟨φ, hφB, conjMatch_sound hφ ea.1 eb.1 ec.1 ed.1 eu.1 ev.1 hf⟩

theorem lift_mk_liftWord {H : Type*} [Group H] (f : Fin 5 → H) (w : List (Fin 4 × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (liftWord w)) =
      FreeGroup.lift (fun i : Fin 4 => f i.castSucc) (FreeGroup.mk w) := by
  simp [liftWord, FreeGroup.lift_mk, List.map_map, Function.comp_def]

theorem genU_zero_ne_one : (genU 0 : P45) ≠ 1 :=
  ne_of_repL_ne (repL_genU (by norm_num)) (repL_one 45) (by decide)

theorem rels1_hold (φ : ↥P1 →* P45) :
    ∀ w ∈ rels1, FreeGroup.lift (fun i => φ (genP1 i)) (FreeGroup.mk w) = 1 := by
  intro w hw
  have h := lift_genP1_rels1 (FreeGroup.mk w) (List.mem_map_of_mem hw)
  have h2 := hom_freeLift φ genP1 (FreeGroup.mk w)
  rw [h, map_one] at h2
  exact h2.symm

theorem rels2_hold (φ : ↥P2 →* P45) :
    ∀ w ∈ rels2, FreeGroup.lift (fun i => φ (genP2 i)) (FreeGroup.mk w) = 1 := by
  intro w hw
  have h := lift_genP2_rels2 (FreeGroup.mk w) (List.mem_map_of_mem hw)
  have h2 := hom_freeLift φ genP2 (FreeGroup.mk w)
  rw [h, map_one] at h2
  exact h2.symm

theorem amalgamAut_eq_conj_of_check
    (hR : rigidCheck () = true) (hbd : bDistinct () = true) (hp1 : p1Distinct () = true)
    (hp2 : p2Distinct () = true) (α₁ : P1 ≃* P1) (α₂ : P2 ≃* P2)
    (h : ∀ (b : Y) (h1 : b ∈ P1) (h2 : b ∈ P2),
      ((α₁ ⟨b, h1⟩ : Y) : P45) = ((α₂ ⟨b, h2⟩ : Y) : P45)) :
    ∃ f : Ah, f ∈ Bh ∧
      (∀ p : P1, ((α₁ p : Y) : P45) = (f : P45) * ((p : Y) : P45) * (f : P45)⁻¹) ∧
      (∀ p : P2, ((α₂ p : Y) : P45) = (f : P45) * ((p : Y) : P45) * (f : P45)⁻¹) := by
  set φ₁ : ↥P1 →* P45 := Xs.subtype.comp (P1.subtype.comp α₁.toMonoidHom) with hφ₁
  set φ₂ : ↥P2 →* P45 := Xs.subtype.comp (P2.subtype.comp α₂.toMonoidHom) with hφ₂
  have hag : ∀ k : Fin 4, φ₁ (genP1 k.castSucc) = φ₂ (genP2 k.castSucc) := by
    intro k
    have e := h (genU k.val) (genU_mem_P1 (by omega)) (genU_mem_P2 (by omega) (by omega))
    have e2 : genP2 k.castSucc = ⟨genU k.val, genU_mem_P2 (by omega) (by omega)⟩ :=
      Subtype.ext (congrArg genU (code2_castSucc k))
    show ((α₁ (genP1 k.castSucc) : Y) : P45) = ((α₂ (genP2 k.castSucc) : Y) : P45)
    rw [e2]
    exact e
  have hB0 : ∀ k : Fin 4, ((α₁ (genP1 k.castSucc) : P1) : Y) ∈ B0 := by
    intro k
    refine Subgroup.mem_inf.2 ⟨(α₁ _).2, ?_⟩
    have e : ((α₁ (genP1 k.castSucc) : P1) : Y) = ((α₂ (genP2 k.castSucc) : P2) : Y) :=
      Subtype.ext (hag k)
    rw [e]
    exact (α₂ _).2
  have ha1 : (((α₁ (genP1 0) : P1) : Y) : P45) ≠ 1 := by
    intro h0
    have h1 : α₁ (genP1 0) = 1 := Subtype.ext (Subtype.ext h0)
    have h2 : genP1 0 = 1 := α₁.injective (h1.trans (map_one α₁).symm)
    exact genU_zero_ne_one (congrArg (fun x : ↥P1 => ((x : Y) : P45)) h2)
  have hrB : ∀ w ∈ relsB,
      FreeGroup.lift ![(((α₁ (genP1 0) : P1) : Y) : P45), (((α₁ (genP1 1) : P1) : Y) : P45),
        (((α₁ (genP1 2) : P1) : Y) : P45), (((α₁ (genP1 3) : P1) : Y) : P45)]
        (FreeGroup.mk w) = 1 := by
    intro w hw
    have e := rels1_hold φ₁ (liftWord w) (List.mem_append_left _ (List.mem_map_of_mem hw))
    rw [lift_mk_liftWord] at e
    have hf : (fun i : Fin 4 => φ₁ (genP1 i.castSucc)) =
        ![(((α₁ (genP1 0) : P1) : Y) : P45), (((α₁ (genP1 1) : P1) : Y) : P45),
          (((α₁ (genP1 2) : P1) : Y) : P45), (((α₁ (genP1 3) : P1) : Y) : P45)] := by
      funext i
      fin_cases i <;> rfl
    rw [hf] at e
    exact e
  have hr1 : ∀ w ∈ rels1Extra,
      FreeGroup.lift ![(((α₁ (genP1 0) : P1) : Y) : P45), (((α₁ (genP1 1) : P1) : Y) : P45),
        (((α₁ (genP1 2) : P1) : Y) : P45), (((α₁ (genP1 3) : P1) : Y) : P45),
        (((α₁ (genP1 4) : P1) : Y) : P45)] (FreeGroup.mk w) = 1 := by
    intro w hw
    have e := rels1_hold φ₁ w (List.mem_append_right _ hw)
    have hf : (fun i : Fin 5 => φ₁ (genP1 i)) =
        ![(((α₁ (genP1 0) : P1) : Y) : P45), (((α₁ (genP1 1) : P1) : Y) : P45),
          (((α₁ (genP1 2) : P1) : Y) : P45), (((α₁ (genP1 3) : P1) : Y) : P45),
          (((α₁ (genP1 4) : P1) : Y) : P45)] := by
      funext i
      fin_cases i <;> rfl
    rw [hf] at e
    exact e
  have hr2 : ∀ w ∈ rels2Extra,
      FreeGroup.lift ![(((α₁ (genP1 0) : P1) : Y) : P45), (((α₁ (genP1 1) : P1) : Y) : P45),
        (((α₁ (genP1 2) : P1) : Y) : P45), (((α₁ (genP1 3) : P1) : Y) : P45),
        (((α₂ (genP2 4) : P2) : Y) : P45)] (FreeGroup.mk w) = 1 := by
    intro w hw
    have e := rels2_hold φ₂ w (List.mem_append_right _ hw)
    have hf : (fun i : Fin 5 => φ₂ (genP2 i)) =
        ![(((α₁ (genP1 0) : P1) : Y) : P45), (((α₁ (genP1 1) : P1) : Y) : P45),
          (((α₁ (genP1 2) : P1) : Y) : P45), (((α₁ (genP1 3) : P1) : Y) : P45),
          (((α₂ (genP2 4) : P2) : Y) : P45)] := by
      funext i
      fin_cases i
      · exact (hag 0).symm
      · exact (hag 1).symm
      · exact (hag 2).symm
      · exact (hag 3).symm
      · rfl
    rw [hf] at e
    exact e
  obtain ⟨f, hfB, hfa, hfb, hfc, hfd, hfu, hfv⟩ := rigid_exists_conj hR hbd hp1 hp2
    (a := ((α₁ (genP1 0) : P1) : Y)) (b := ((α₁ (genP1 1) : P1) : Y))
    (c := ((α₁ (genP1 2) : P1) : Y)) (d := ((α₁ (genP1 3) : P1) : Y))
    (u := ((α₁ (genP1 4) : P1) : Y)) (v := ((α₂ (genP2 4) : P2) : Y))
    (hB0 0) (hB0 1) (hB0 2) (hB0 3) (α₁ _).2 (α₂ _).2 hrB hr1 hr2 ha1
  refine ⟨f, hfB, fun p => ?_, fun p => ?_⟩
  · have hh : φ₁ = (MulAut.conj (f : P45)).toMonoidHom.comp (Xs.subtype.comp P1.subtype) := by
      refine (MonoidHom.cancel_right Ψ1_surjective).1 ?_
      apply PresentedGroup.ext
      intro i
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Ψ1_of]
      fin_cases i
      · exact hfa.symm
      · exact hfb.symm
      · exact hfc.symm
      · exact hfd.symm
      · exact hfu.symm
    exact DFunLike.congr_fun hh p
  · have hh : φ₂ = (MulAut.conj (f : P45)).toMonoidHom.comp (Xs.subtype.comp P2.subtype) := by
      refine (MonoidHom.cancel_right Ψ2_surjective).1 ?_
      apply PresentedGroup.ext
      intro i
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Ψ2_of]
      fin_cases i
      · exact (hag 0).symm.trans hfa.symm
      · exact (hag 1).symm.trans hfb.symm
      · exact (hag 2).symm.trans hfc.symm
      · exact (hag 3).symm.trans hfd.symm
      · exact hfv.symm
    exact DFunLike.congr_fun hh p

end CFSG.LargeExtraspecial.AS62.Rigid
