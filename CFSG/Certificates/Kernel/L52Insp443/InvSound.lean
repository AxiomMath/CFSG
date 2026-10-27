module

public import CFSG.Certificates.Kernel.L52Insp443.SubSound
public import Certificates.Data.Kernel.L52Insp443.Inv
public import CFSG.Certificates.Kernel.KGC31PPow
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.Literature.GL52 CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Sporadic.Schreier
  CFSG.KC.KGC31P CFSG.Sporadic.Schreier.Native

theorem ascK_cons (lo x : ℕ) (L : List ℕ) : ascK lo (x :: L) = CFSG.KC.Ord.andB (Nat.blt lo x) (ascK x L) :=
  rfl

theorem lastK_cons (lo x : ℕ) (L : List ℕ) : lastK lo (x :: L) = lastK x L := rfl

theorem lastK_ne {L : List ℕ} (h : L ≠ []) (lo lo' : ℕ) : lastK lo L = lastK lo' L := by
  cases L with
  | nil => exact absurd rfl h
  | cons x L => rw [lastK_cons, lastK_cons]

theorem ascK_facts : ∀ (L : List ℕ) (lo : ℕ), ascK lo L = true →
    L.Pairwise (· < ·) ∧ (∀ x ∈ L, lo < x ∧ x ≤ lastK lo L) ∧ lo ≤ lastK lo L
  | [], lo, _ => ⟨List.Pairwise.nil, by simp, le_refl lo⟩
  | x :: L, lo, h => by
    rw [ascK_cons, andB_true] at h
    have hx : lo < x := Nat.le_of_ble_eq_true h.1
    obtain ⟨ih1, ih2, ih3⟩ := ascK_facts L x h.2
    rw [lastK_cons]
    refine ⟨List.Pairwise.cons (fun y hy => (ih2 y hy).1) ih1, fun y hy => ?_, by omega⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hx, ih3⟩
    · exact ⟨by have := (ih2 y hy).1; omega, (ih2 y hy).2⟩

theorem nodup_flatten_of_blocks (Bs : List (List ℕ))
    (hasc : ∀ k < Bs.length, ascK (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun j _ => lastK (nat_lit 0) (Bs.getD j [])) k) (Bs.getD k []) = true)
    (hne : ∀ k < Bs.length, Bs.getD k [] ≠ []) : Bs.flatten.Nodup := by
  have hlo : ∀ k, k + 1 < Bs.length → ∀ y ∈ Bs.getD (k + 1) [], lastK 0 (Bs.getD k []) < y :=
    fun k hk y hy => ((ascK_facts _ _ (hasc (k + 1) hk)).2.1 y hy).1
  have hle : ∀ k < Bs.length, ∀ x ∈ Bs.getD k [], x ≤ lastK 0 (Bs.getD k []) := fun k hk x hx => by
    have h := ((ascK_facts _ _ (hasc k hk)).2.1 x hx).2
    rwa [lastK_ne (hne k hk) _ 0] at h
  have hmono : ∀ i j, i ≤ j → j < Bs.length → lastK 0 (Bs.getD i []) ≤ lastK 0 (Bs.getD j []) := by
    intro i j hij hj
    induction j with
    | zero => rw [Nat.le_zero.mp hij]
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h | h
      · have h1 := ih (by omega) (by omega)
        obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (hne (j + 1) hj)
        have := hlo j hj y hy
        have := hle (j + 1) hj y hy
        omega
      · rw [h]
  have hpw : (Bs.flatten).Pairwise (· < ·) := by
    rw [List.pairwise_flatten]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
      have := (ascK_facts _ _ (hasc k hk)).1
      rwa [List.getD_eq_getElem _ _ hk] at this
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij x hx y hy
      rw [← List.getD_eq_getElem _ [] hi] at hx
      rw [← List.getD_eq_getElem _ [] hj] at hy
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have h1 := hle i hi x hx
      have h2 := hmono i j' (by omega) (by omega)
      have h3 := hlo j' hj y hy
      omega
  exact hpw.imp (fun h => Nat.ne_of_lt h)

theorem mem_of_card {Γ : Type} [Fintype Γ] (κ : Γ → ℕ) (hinj : Function.Injective κ)
    (P : Γ → Prop) [DecidablePred P] {L : List ℕ} (hnd : L.Nodup)
    (hL : ∀ c ∈ L, ∃ g, P g ∧ κ g = c) (hcard : Nat.card {g // P g} = L.length) {g : Γ}
    (hg : P g) : κ g ∈ L := by
  have hS : (Finset.univ.filter P).card = L.length := by
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : L.toFinset ⊆ (Finset.univ.filter P).image κ := fun c hc => by
    obtain ⟨g, hg, rfl⟩ := hL c (List.mem_toFinset.mp hc)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
  have hle : ((Finset.univ.filter P).image κ).card ≤ L.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, Finset.card_image_of_injective _ hinj, hS]
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hm : κ g ∈ (Finset.univ.filter P).image κ :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
  rw [← heq] at hm
  exact List.mem_toFinset.mp hm

theorem invo_exists {c : ℕ} (h : invoK c = true) :
    ∃ g : G, orderOf g = 2 ∧ mcode (g : Mat) = c := by
  obtain ⟨hu, hr⟩ := and2 h
  obtain ⟨hsq, hne⟩ := and2 hr
  refine ⟨gD c, ?_, mcode_gD hu⟩
  have h2 : gD c ^ 2 = 1 := by
    rw [pow_two]
    exact gD_sq hu (Nat.eq_of_beq_eq_true hsq)
  have h1 : gD c ≠ 1 := fun h1 => by
    have e := mcode_gD hu
    rw [h1, kG_one] at e
    exact Nat.ne_of_beq_eq_false (notB_true.mp hne) e.symm
  exact orderOf_eq_prime (p := 2) h2 h1

theorem andB_eq (a b : Bool) : CFSG.KC.Ord.andB a b = (a && b) := by cases a <;> cases b <;> rfl

theorem orB_eq (a b : Bool) : CFSG.KC.Ord.orB a b = (a || b) := by cases a <;> cases b <;> rfl

theorem notB_eq (a : Bool) : CFSG.KC.Ord.notB a = !a := by cases a <;> rfl

theorem allK_eq {α : Type} (p : α → Bool) : ∀ L : List α, allK p L = L.all p
  | [] => rfl
  | x :: L => by
    change CFSG.KC.Ord.andB (p x) (allK p L) = _
    rw [andB_eq, allK_eq p L, List.all_cons]

theorem anyK_eq {α : Type} (p : α → Bool) : ∀ L : List α, anyK p L = L.any p
  | [] => rfl
  | x :: L => by
    change CFSG.KC.Ord.orB (p x) (anyK p L) = _
    rw [orB_eq, anyK_eq p L, List.any_cons]

theorem conjCommK_eq (c : ℕ) : ∀ ps qs : List ℕ, conjCommK c ps qs = (orbK ps qs c).all (commK c)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, q :: qs => by
    change CFSG.KC.Ord.andB (commK c (mmulK (mmulK p c) q)) (conjCommK c ps qs) = _
    rw [andB_eq, conjCommK_eq c ps qs, orbK, orbK, List.zipWith_cons_cons, List.all_cons]

section Gen

variable {Γ : Type} [Group Γ] [DecidableEq Γ]

theorem memK_map (κ : Γ → ℕ) (hinj : Function.Injective κ) (y : Γ) (Z : List Γ) :
    memK (κ y) (Z.map κ) = decide (y ∈ Z) := by
  rw [Bool.eq_iff_iff, memK_iff, decide_eq_true_iff, List.mem_map]
  constructor
  · rintro ⟨z, hz, e⟩
    rwa [← hinj e]
  · intro h
    exact ⟨y, h, rfl⟩

theorem beq_code (κ : Γ → ℕ) (hinj : Function.Injective κ) (a b : Γ) :
    Nat.beq (κ a) (κ b) = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  exact ⟨fun e => hinj e, fun e => by rw [e]⟩

theorem mem_gspan_cons (b : Γ) (ys : List Γ) (y : Γ) :
    y ∈ gspan (b :: ys) ↔ y ∈ gspan ys ∨ ∃ z ∈ gspan ys, b * z = y := by
  rw [mem_gspan, mem_gspan]
  constructor
  · rintro ⟨S, hS, rfl⟩
    rcases List.sublist_cons_iff.1 hS with hS | ⟨r, rfl, hr⟩
    · exact Or.inl ⟨S, hS, rfl⟩
    · exact Or.inr ⟨r.prod, (mem_gspan ys _).2 ⟨r, hr, rfl⟩, by rw [List.prod_cons]⟩
  · rintro (⟨S, hS, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨S, hS.cons b, rfl⟩
    · obtain ⟨S, hS, rfl⟩ := (mem_gspan ys z).1 hz
      exact ⟨b :: S, hS.cons₂ b, List.prod_cons⟩

variable (κ : Γ → ℕ) (hone : κ 1 = idK) (hmul : ∀ g h : Γ, κ (g * h) = mmulK (κ g) (κ h))
  (hinj : Function.Injective κ)

include hone hmul in
theorem spanK_map : ∀ ys : List Γ, ∃ Z : List Γ, spanK (ys.map κ) = Z.map κ ∧
    ∀ y, y ∈ Z ↔ y ∈ gspan ys
  | [] => ⟨[1], by rw [List.map_nil, spanK_nil, List.map_singleton, hone], fun y => by
      rw [mem_gspan, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨[], List.Sublist.slnil, rfl⟩
      · rintro ⟨S, hS, rfl⟩
        rw [List.sublist_nil.mp hS, List.prod_nil]⟩
  | b :: ys => by
    obtain ⟨Z, hZ, hm⟩ := spanK_map ys
    refine ⟨Z ++ Z.map (b * ·), ?_, fun y => ?_⟩
    · simp only [List.map_cons, spanK_cons, hZ, List.map_append, List.map_map, Function.comp_def,
        hmul]
    · simp only [mem_gspan_cons, List.mem_append, List.mem_map, hm]

include hone hmul hinj in
theorem memK_spanK (y : Γ) (ys : List Γ) :
    memK (κ y) (spanK (ys.map κ)) = decide (y ∈ gspan ys) := by
  obtain ⟨Z, hZ, hm⟩ := spanK_map κ hone hmul ys
  rw [hZ, memK_map κ hinj, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact hm y

include hone hmul hinj in
theorem orbIsK_eq (O B : List Γ) : orbIsK (O.map κ) (B.map κ) = gorbIs O B := by
  simp only [orbIsK, letL, andB_eq, allK_eq, gorbIs, List.all_map, Function.comp_def,
    memK_spanK κ hone hmul hinj]

include hmul hinj in
theorem commK_eq (a b : Γ) : commK (κ a) (κ b) = decide (a * b = b * a) := by
  unfold commK
  rw [← hmul, ← hmul, beq_code κ hinj]

theorem eq_map_range {L : List ℕ} {f : ℕ → ℕ} {m : ℕ} (hl : L.length = m)
    (h : ∀ j < m, L.getD j 0 = f j) : L = (List.range m).map f := by
  refine List.ext_getElem (by rw [List.length_map, List.length_range, hl]) fun j h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, ← h j (by omega), List.getD_eq_getElem _ _ h1]

include hone hmul hinj in
theorem orbOneK_eq {x h : Γ} {p : ℕ} (hp : 1 < p) {ps qs : List ℕ} (hpl : ps.length = p)
    (hql : qs.length = p) (hps : ∀ j < p, ps.getD j 0 = κ (x ^ j))
    (hqs : ∀ j < p, qs.getD j 0 = κ (x⁻¹ ^ j)) {cs : List (List ℕ)} {C : List (List Γ)}
    (hcs : cs = C.map (List.map κ)) :
    orbOneK ps qs cs (κ h) = (!(gbad p x h) || C.any (gorbIs (gorb p x h))) := by
  have h1 : ps.getD 1 0 = κ x := by rw [hps 1 hp, pow_one]
  have h1' : qs.getD 1 0 = κ x⁻¹ := by rw [hqs 1 hp, pow_one]
  have horb : orbK ps qs (κ h) = (gorb p x h).map κ := by
    rw [eq_map_range hpl hps, eq_map_range hql hqs]
    simp only [orbK, List.zipWith_map, List.zipWith_self, gorb, List.map_map, Function.comp_def,
      hmul, inv_pow]
  subst hcs
  unfold orbOneK badK letL
  simp only [orB_eq, notB_eq, andB_eq, anyK_eq]
  rw [h1, h1', ← hmul, ← hmul, beq_code κ hinj, conjCommK_eq, horb, gbad, List.all_map,
    List.any_map]
  simp only [Function.comp_def, commK_eq κ hmul hinj, orbIsK_eq κ hone hmul hinj]

end Gen

section Tab

variable {Γ : Type} [Group Γ] [DecidableEq Γ] (φ : Γ →* Equiv.Perm (Fin 31))
  (hφ : Function.Injective φ)

include hφ in
theorem tblEq_G {S T : Table} {a b : Γ} (hS : Rep 31 S (φ a)) (hT : Rep 31 T (φ b)) :
    tblEq 31 S T = decide (a = b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, tblEq_iff_eq hS hT, hφ.eq_iff]

theorem rep_conjTab {X XI t : Table} {x h : Γ} (hX : Rep 31 X (φ x))
    (hXI : Rep 31 XI (φ x⁻¹)) (ht : Rep 31 t (φ h)) :
    Rep 31 (conjTab 31 X XI t) (φ (x * h * x⁻¹)) := by
  unfold conjTab
  rw [map_mul, map_mul]
  exact Rep.compT (Rep.compT hX ht) hXI

theorem rep_pows {X XI : Table} {x : Γ} (hX : Rep 31 X (φ x)) (hXI : Rep 31 XI (φ x⁻¹))
    (j : ℕ) : Rep 31 (powT 31 j X) (φ (x ^ j)) ∧ Rep 31 (powT 31 j XI) (φ (x ^ j)⁻¹) := by
  rw [map_pow, ← inv_pow, map_pow]
  exact ⟨Rep.powT hn31 hX j, Rep.powT hn31 hXI j⟩

include hφ in
theorem badAct_eq {X XI t : Table} {x h : Γ} (hX : Rep 31 X (φ x))
    (hXI : Rep 31 XI (φ x⁻¹)) (ht : Rep 31 t (φ h)) (m : ℕ) :
    badAct 31 m X XI t = gbad m x h := by
  rw [badAct, gbad, tblEq_G φ hφ (rep_conjTab φ hX hXI ht) ht, gorb, List.all_map]
  congr 1
  refine congrArg (List.all _) (funext fun j => ?_)
  obtain ⟨h1, h2⟩ := rep_pows φ hX hXI j
  have hc := rep_conjTab φ h1 h2 ht
  rw [Function.comp_apply, tblEq_G φ hφ (by rw [map_mul]; exact Rep.compT ht hc)
    (by rw [map_mul]; exact Rep.compT hc ht)]

theorem f2_orbTabs {X XI t : Table} {x h : Γ} (hX : Rep 31 X (φ x))
    (hXI : Rep 31 XI (φ x⁻¹)) (ht : Rep 31 t (φ h)) (m : ℕ) :
    List.Forall₂ (fun T y => Rep 31 T (φ y)) (orbTabs 31 m X XI t) (gorb m x h) := by
  rw [orbTabs, gorb, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro j _
  obtain ⟨h1, h2⟩ := rep_pows φ hX hXI j
  exact rep_conjTab φ h1 h2 ht

theorem all_f2 {α β : Type} {R : α → β → Prop} {f : α → Bool} {g : β → Bool}
    (h : ∀ a b, R a b → f a = g b) : ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      l.all f = l'.all g
  | _, _, .nil => rfl
  | _, _, .cons hab hl => by rw [List.all_cons, List.all_cons, h _ _ hab, all_f2 h hl]

theorem any_f2 {α β : Type} {R : α → β → Prop} {f : α → Bool} {g : β → Bool}
    (h : ∀ a b, R a b → f a = g b) : ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      l.any f = l'.any g
  | _, _, .nil => rfl
  | _, _, .cons hab hl => by rw [List.any_cons, List.any_cons, h _ _ hab, any_f2 h hl]

theorem rep_maskProdG : ∀ {Ts : List Table} {B : List Γ},
    List.Forall₂ (fun T y => Rep 31 T (φ y)) Ts B → ∀ m,
      Rep 31 (maskProd 31 Ts m) (φ (gmask B m))
  | [], [], _, m => by
    rw [gmask, map_one]
    exact Rep.idT hn31
  | T :: Ts, b :: B, .cons hT h, m => by
    rw [gmask, map_mul]
    unfold maskProd
    refine Rep.compT ?_ (rep_maskProdG h (m / 2))
    by_cases hm : m % 2 = 1
    · rw [if_pos hm, if_pos hm]
      exact hT
    · rw [if_neg hm, if_neg hm, map_one]
      exact Rep.idT hn31

theorem f2_spanTabs {Ts : List Table} {B : List Γ}
    (h : List.Forall₂ (fun T y => Rep 31 T (φ y)) Ts B) :
    List.Forall₂ (fun T y => Rep 31 T (φ y)) (spanTabs 31 Ts) (gspan B) := by
  rw [spanTabs, gspan, h.length_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  exact fun m _ => rep_maskProdG φ h m

include hφ in
theorem any_tblEq {T : Table} {y : Γ} (hT : Rep 31 T (φ y)) {L : List Table} {Ys : List Γ}
    (h : List.Forall₂ (fun T y => Rep 31 T (φ y)) L Ys) :
    L.any (tblEq 31 T) = decide (y ∈ Ys) := by
  rw [any_f2 (f := tblEq 31 T) (g := fun z => decide (y = z))
    (fun S z hS => tblEq_G φ hφ hT hS) h, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  simp

include hφ in
theorem orbIs_eq' {orb bs : List Table} {O B : List Γ}
    (ho : List.Forall₂ (fun T y => Rep 31 T (φ y)) orb O)
    (hb : List.Forall₂ (fun T y => Rep 31 T (φ y)) bs B) : orbIs 31 orb bs = gorbIs O B := by
  unfold orbIs gorbIs
  rw [all_f2 (f := fun o => (spanTabs 31 bs).any (tblEq 31 o))
      (g := fun o => decide (o ∈ gspan B)) (fun T y hT => any_tblEq φ hφ hT (f2_spanTabs φ hb)) ho,
    all_f2 (f := fun b => (spanTabs 31 orb).any (tblEq 31 b))
      (g := fun b => decide (b ∈ gspan O)) (fun T y hT => any_tblEq φ hφ hT (f2_spanTabs φ ho)) hb]

include hφ in
theorem orbOne_eq {E t : Table} {y h : Γ} (hE : Rep 31 E (φ y)) (ht : Rep 31 t (φ h))
    (m : ℕ) {cands : List (List Table)} {C : List (List Γ)}
    (hc : List.Forall₂ (List.Forall₂ fun T y => Rep 31 T (φ y)) cands C) :
    (!(badAct 31 m E (invT 31 E) t) || cands.any (orbIs 31 (orbTabs 31 m E (invT 31 E) t))) =
      (!(gbad m y h) || C.any (gorbIs (gorb m y h))) := by
  have hEI : Rep 31 (invT 31 E) (φ y⁻¹) := by
    rw [map_inv]
    exact rep_invT_of_rep hn31 hE
  rw [badAct_eq φ hφ hE hEI ht, any_f2 (f := orbIs 31 (orbTabs 31 m E (invT 31 E) t))
    (g := gorbIs (gorb m y h)) (fun B B' hB => orbIs_eq' φ hφ (f2_orbTabs φ hE hEI ht m) hB) hc]

include hφ in
theorem orbCheck_of {X : Table} {x : Γ} {p : ℕ} (hp : p.Prime) (hX : Rep 31 X (φ x))
    (hx : x ^ p = 1) {cands : List (List Table)} {C : List (List Γ)}
    (hc : List.Forall₂ (List.Forall₂ fun T y => Rep 31 T (φ y)) cands C) {I : List Table}
    (hI : ∀ t ∈ I, ∃ h : Γ, Rep 31 t (φ h) ∧
      (!(gbad p x h) || C.any (gorbIs (gorb p x h))) = true) :
    orbCheck 31 p I (powTabs 31 X p) cands = true := by
  rw [orbCheck, powTabs, List.all_map, List.all_eq_true]
  intro a ha
  have hE : Rep 31 (powT 31 a X) (φ (x ^ a)) := by
    rw [map_pow]
    exact Rep.powT hn31 hX a
  rw [Function.comp_apply, Bool.and_eq_true, List.all_eq_true]
  refine ⟨invOK_invT_of_rep hn31 hE, fun t ht => ?_⟩
  obtain ⟨h, hth, hg⟩ := hI t ht
  rw [orbOne_eq φ hφ hE hth p hc]
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · rw [pow_zero, gbad_one]
    simp
  · rw [gone_pow hx hp.one_lt
      (Nat.coprime_of_lt_prime ha0.ne' (List.mem_range.mp ha) hp).symm C]
    exact hg

end Tab

end CFSG.KC.L52I

end
