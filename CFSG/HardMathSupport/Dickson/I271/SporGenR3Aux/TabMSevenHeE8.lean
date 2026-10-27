module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenHeRec
public import Certificates.Certificate17486

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Sporadic.HeldB (heP heGen heGenPerm heGenPerm_mem rep_heGen eq_one_of_fix_base)

def heWordPerm (w : List ℕ) : Equiv.Perm (Fin 8330) := (w.map heGenPerm).prod

theorem heWordPerm_nil : heWordPerm [] = 1 := by
  simp [heWordPerm]

theorem heWordPerm_cons (k : ℕ) (w : List ℕ) :
    heWordPerm (k :: w) = heGenPerm k * heWordPerm w := by
  simp [heWordPerm]

theorem heWordPerm_append (v w : List ℕ) :
    heWordPerm (v ++ w) = heWordPerm v * heWordPerm w := by
  simp [heWordPerm]

theorem letters_append_lt_two {v w : List ℕ} (hv : ∀ k ∈ v, k < 2) (hw : ∀ k ∈ w, k < 2) :
    ∀ k ∈ v ++ w, k < 2 :=
  fun k hk => (List.mem_append.1 hk).elim (hv k) (hw k)

theorem letters_ite_lt_two {c : Prop} [Decidable c] {w : List ℕ} (hw : ∀ k ∈ w, k < 2) :
    ∀ k ∈ (if c then w else []), k < 2 := by
  split_ifs
  · exact hw
  · simp

theorem evPt_heGen {w : List ℕ} (hw : ∀ k ∈ w, k < 2)
    (x : Fin 8330) : evPt (heGen 0) (heGen 1) w x = (heWordPerm w x : ℕ) := by
  induction w with
  | nil => simp [evPt, heWordPerm_nil]
  | cons k w ih =>
    have ih' := ih fun j hj => hw j (List.mem_cons_of_mem k hj)
    change (if k = 0 then (heGen 0)[evPt (heGen 0) (heGen 1) w x]!
      else (heGen 1)[evPt (heGen 0) (heGen 1) w x]!) = _
    rw [ih', heWordPerm_cons, Equiv.Perm.mul_apply]
    rcases (by have := hw k List.mem_cons_self; omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [if_pos rfl]
      exact rep_heGen (by norm_num) _
    · rw [if_neg one_ne_zero]
      exact rep_heGen (by norm_num) _

theorem heWordPerm_mem {w : List ℕ} (hw : ∀ k ∈ w, k < 2) : heWordPerm w ∈ heP := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  exact heGenPerm_mem (hw k hk)

theorem heWordPerm_eq_one {w : List ℕ} (hw : ∀ k ∈ w, k < 2)
    (h : fixesBase (heGen 0) (heGen 1) w = true) : heWordPerm w = 1 := by
  refine eq_one_of_fix_base (heWordPerm_mem hw) fun b hb => Fin.ext ?_
  rw [← evPt_heGen hw b]
  simp only [fixesBase, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h b hb

theorem baseImg_eq {v w : List ℕ} (hv : ∀ k ∈ v, k < 2)
    (hw : ∀ k ∈ w, k < 2) (h : heWordPerm v = heWordPerm w) :
    baseImg (heGen 0) (heGen 1) v = baseImg (heGen 0) (heGen 1) w := by
  refine List.map_congr_left fun b hb => ?_
  have hb' : b < 8330 := by
    rw [List.mem_range] at hb
    omega
  exact (evPt_heGen hv ⟨b, hb'⟩).trans
    ((congrArg (fun g : Equiv.Perm (Fin 8330) => (g ⟨b, hb'⟩ : ℕ)) h).trans
      (evPt_heGen hw ⟨b, hb'⟩).symm)

theorem heWordPerm_heE8Word (v : Bool × Bool × Bool) : heWordPerm (heE8Word v) =
    (if v.1 then heWordPerm heE8Word1 else 1) * (if v.2.1 then heWordPerm heE8Word2 else 1) *
      (if v.2.2 then heWordPerm heE8Word3 else 1) := by
  simp only [heE8Word, heWordPerm_append]
  split_ifs <;> simp [heWordPerm_nil]

theorem mem_boolTriples (v : Bool × Bool × Bool) : v ∈ boolTriples := by
  obtain ⟨_ | _, _ | _, _ | _⟩ := v <;> simp [boolTriples]

theorem mul_comm_of_mul_mul_eq_one {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b * a * b = 1) : a * b = b * a := by
  have h : a * b * (a * b) = 1 := by
    rw [← mul_assoc]
    exact hab
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

theorem hePE8_of {a b c : Equiv.Perm (Fin 8330)} (ha : a ∈ heP) (hb : b ∈ heP) (hc : c ∈ heP)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b)
    (hinj : Function.Injective fun v : Bool × Bool × Bool =>
      (if v.1 then a else 1) * (if v.2.1 then b else 1) * (if v.2.2 then c else 1)) :
    HePE8 := by
  have hS : ∀ x ∈ ({a, b, c} : Set (Equiv.Perm (Fin 8330))),
      ∀ y ∈ ({a, b, c} : Set (Equiv.Perm (Fin 8330))), x * y = y * x := by
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;>
      first | rfl | exact hab | exact hac | exact hbc | exact hab.symm | exact hac.symm |
        exact hbc.symm
  have hS2 : ∀ x ∈ ({a, b, c} : Set (Equiv.Perm (Fin 8330))), x * x = 1 := by
    rintro x (rfl | rfl | rfl)
    exacts [ha2, hb2, hc2]
  set A := Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 8330))) with hA
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    letI : CommGroup ↥A := Subgroup.closureCommGroupOfComm fun x hx y hy _ => hS x hx y hy
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩)
  have hA2 : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    rw [hA] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hS2 x hx
    | one => simp
    | mul x y hx hy hx' hy' =>
      have h := hAc x hx y hy
      calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
        _ = x * (x * y) * y := by rw [h]
        _ = x * x * (y * y) := by simp only [mul_assoc]
        _ = 1 := by rw [hx', hy', mul_one]
    | inv x hx hx' =>
      rw [← mul_inv_rev, hx', inv_one]
  have haA : a ∈ A := Subgroup.subset_closure (by simp)
  have hbA : b ∈ A := Subgroup.subset_closure (by simp)
  have hcA : c ∈ A := Subgroup.subset_closure (by simp)
  have hmem : ∀ v : Bool × Bool × Bool,
      (if v.1 then a else 1) * (if v.2.1 then b else 1) * (if v.2.2 then c else 1) ∈ A := by
    intro v
    refine A.mul_mem (A.mul_mem ?_ ?_) ?_ <;> split_ifs
    exacts [haA, A.one_mem, hbA, A.one_mem, hcA, A.one_mem]
  unfold HePE8
  refine ⟨A, ?_, hAc, fun x hx => by rw [sq]; exact hA2 x hx, ?_⟩
  · rw [hA, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    exacts [ha, hb, hc]
  · have h := Nat.card_le_card_of_injective (fun v : Bool × Bool × Bool => (⟨_, hmem v⟩ : ↥A))
      fun v w hvw => hinj (congrArg Subtype.val hvw)
    have h8 : Nat.card (Bool × Bool × Bool) = 8 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    omega

theorem hePE8 : HePE8 := by
  have hc : heE8OK (heGen 0) (heGen 1) = true := Certificates.certificate17486
  simp only [heE8OK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hL, h11⟩, h22⟩, h33⟩, h12⟩, h13⟩, h23⟩, hD⟩ := hc
  have l1 : ∀ k ∈ heE8Word1, k < 2 := fun k hk =>
    hL k (List.mem_append_left _ (List.mem_append_left _ hk))
  have l2 : ∀ k ∈ heE8Word2, k < 2 := fun k hk =>
    hL k (List.mem_append_left _ (List.mem_append_right _ hk))
  have l3 : ∀ k ∈ heE8Word3, k < 2 := fun k hk => hL k (List.mem_append_right _ hk)
  have lE : ∀ v, ∀ k ∈ heE8Word v, k < 2 := fun v =>
    letters_append_lt_two (letters_append_lt_two (letters_ite_lt_two l1) (letters_ite_lt_two l2))
      (letters_ite_lt_two l3)
  have hsq : ∀ {w : List ℕ}, (∀ k ∈ w, k < 2) → fixesBase (heGen 0) (heGen 1) (w ++ w) = true →
      heWordPerm w * heWordPerm w = 1 := fun hw h => by
    rw [← heWordPerm_append]
    exact heWordPerm_eq_one (letters_append_lt_two hw hw) h
  have hcomm : ∀ {v w : List ℕ}, (∀ k ∈ v, k < 2) → (∀ k ∈ w, k < 2) →
      fixesBase (heGen 0) (heGen 1) (v ++ v) = true →
      fixesBase (heGen 0) (heGen 1) (w ++ w) = true →
      fixesBase (heGen 0) (heGen 1) (v ++ w ++ v ++ w) = true →
      heWordPerm v * heWordPerm w = heWordPerm w * heWordPerm v := fun hv hw hvv hww hvw => by
    refine mul_comm_of_mul_mul_eq_one (hsq hv hvv) (hsq hw hww) ?_
    have h := heWordPerm_eq_one (letters_append_lt_two (letters_append_lt_two
      (letters_append_lt_two hv hw) hv) hw) hvw
    simpa only [heWordPerm_append] using h
  refine hePE8_of (heWordPerm_mem l1) (heWordPerm_mem l2) (heWordPerm_mem l3) (hsq l1 h11)
    (hsq l2 h22) (hsq l3 h33) (hcomm l1 l2 h11 h22 h12) (hcomm l1 l3 h11 h33 h13)
    (hcomm l2 l3 h22 h33 h23) ?_
  intro v w hvw
  have hvw' : heWordPerm (heE8Word v) = heWordPerm (heE8Word w) := by
    rw [heWordPerm_heE8Word, heWordPerm_heE8Word]
    exact hvw
  exact List.inj_on_of_nodup_map hD (mem_boolTriples v) (mem_boolTriples w)
    (baseImg_eq (lE v) (lE w) hvw')

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
