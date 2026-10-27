module

public import Certificates.Data.Kernel.Tower.T2Sq
public import CFSG.Certificates.Kernel.Tower.L3QSound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower Subgroup

theorem ninvC_eq {G : Type*} [Group G] (a : G) :
    Nat.card {x : centralizer {a} // x ^ 2 = 1 ∧ x ≠ 1} =
      Nat.card {x : G // x * a = a * x ∧ x ^ 2 = 1 ∧ x ≠ 1} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, mem_centralizer_singleton_iff.1 x.1.2,
        by simpa using congrArg Subtype.val x.2.1,
        fun h => x.2.2 (Subtype.ext (by simpa using h))⟩
      invFun := fun y => ⟨⟨y.1, mem_centralizer_singleton_iff.2 y.2.1⟩,
        Subtype.ext (by simpa using y.2.2.1),
        fun h => y.2.2.2 (by simpa using congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem ninvC_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (a : G) :
    Nat.card {x : centralizer {a} // x ^ 2 = 1 ∧ x ≠ 1} =
      Nat.card {x : centralizer {e a} // x ^ 2 = 1 ∧ x ≠ 1} := by
  rw [ninvC_eq, ninvC_eq]
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
  have h1 : e x * e a = e a * e x ↔ x * a = a * x := by
    rw [← map_mul, ← map_mul]
    exact e.injective.eq_iff
  have h2 : e x ^ 2 = 1 ↔ x ^ 2 = 1 := by
    rw [← map_pow]
    exact map_eq_one_iff e e.injective
  have h3 : e x ≠ 1 ↔ x ≠ 1 := not_congr (map_eq_one_iff e e.injective)
  change _ ↔ e x * e a = e a * e x ∧ e x ^ 2 = 1 ∧ e x ≠ 1
  rw [h1, h2, h3]

variable {X : Type*} [Group X] {n : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}

theorem cycExt_comm {D : ExtData X} {a : X} (hα : D.α a = a) (k : X) (d : Bool) :
    (⟨k, d⟩ : CycExt D) * CycExt.incl D a = CycExt.incl D a * ⟨k, d⟩ ↔ k * a = a * k := by
  change (⟨k, d⟩ * ⟨a, false⟩ : CycExt D) = ⟨a, false⟩ * ⟨k, d⟩ ↔ _
  rw [CycExt.mk_mul_mk, CycExt.mk_mul_mk]
  cases d <;> simp [CycExt.pw, CycExt.sq, hα]

theorem cycExt_sq_false {D : ExtData X} (k : X) :
    (⟨k, false⟩ : CycExt D) ^ 2 = 1 ↔ k * k = 1 := by
  rw [pow_two, CycExt.mk_mul_mk, CycExt.one_def]
  simp [CycExt.pw, CycExt.sq]

theorem cycExt_sq_true {D : ExtData X} (k : X) :
    (⟨k, true⟩ : CycExt D) ^ 2 = 1 ↔ k * D.α k * D.g = 1 := by
  rw [pow_two, CycExt.mk_mul_mk, CycExt.one_def]
  simp [CycExt.pw, CycExt.sq]

theorem ninv2_eq (M : IsModel (⊤ : Subgroup X) n mul dec) (D : ExtData X) {t HL FT g : Nat}
    (ht : t < n) (hH : hOK n mul t HL = true)
    (hFA : ∀ c < n, l16 FT c < n ∧ D.α (dec c) = dec (l16 FT c)) (hg : g < n)
    (hdg : dec g = D.g) (hαt : D.α (dec t) = dec t) :
    Nat.card {x : centralizer {CycExt.incl D (dec t)} // x ^ 2 = 1 ∧ x ≠ 1} =
      ninv2 mul HL FT g := by
  have hH' := hH
  simp only [hOK, Bool.and_eq_true, allB_eq_true] at hH'
  have hlt : ∀ j < 128, hL HL j < n := fun j hj => Nat.le_of_ble_eq_true (hH'.1.1 j hj).1
  have hcm : ∀ j < 128, dec (hL HL j) * dec t = dec t * dec (hL HL j) := fun j hj =>
    (M.comm_iff (hlt j hj) ht).1 (Nat.eq_of_beq_eq_true (hH'.1.1 j hj).2)
  have hmono : ∀ i j, i < j → j < 128 → hL HL i < hL HL j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hs : hL HL j < hL HL (j + 1) := Nat.le_of_ble_eq_true (hH'.1.2 j (by omega))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) hs
      · rw [h]
        exact hs
  have hinj : ∀ i < 128, ∀ j < 128, dec (hL HL i) = dec (hL HL j) → i = j := by
    intro i hi j hj h
    have e := M.inj _ (hlt i hi) _ (hlt j hj) h
    rcases Nat.lt_trichotomy i j with h1 | h1 | h1
    · exact absurd e (Nat.ne_of_lt (hmono i j h1 hj))
    · exact h1
    · exact absurd e (Nat.ne_of_gt (hmono j i h1 hi))
  have hp0 : ∀ j < 128, (!Nat.beq (hL HL j) 0 && Nat.beq (mul (hL HL j) (hL HL j)) 0) = true ↔
      dec (hL HL j) * dec (hL HL j) = 1 ∧ dec (hL HL j) ≠ 1 := by
    intro j hj
    rw [Bool.and_eq_true, Bool.not_eq_true', nbeq, nbeq, beq_iff_eq, beq_eq_false_iff_ne,
      ← M.dec_mul _ (hlt j hj) _ (hlt j hj), ne_eq, ne_eq,
      M.dec_eq_one_iff (M.mul_lt _ (hlt j hj) _ (hlt j hj)), M.dec_eq_one_iff (hlt j hj)]
    exact And.comm
  have hp1 : ∀ j < 128, Nat.beq (mul (mul (hL HL j) (l16 FT (hL HL j))) g) 0 = true ↔
      dec (hL HL j) * D.α (dec (hL HL j)) * D.g = 1 := by
    intro j hj
    have h1 := hlt j hj
    have h2 := (hFA _ h1).1
    rw [(hFA _ h1).2, ← hdg, ← M.dec_mul _ h1 _ h2, ← M.dec_mul _ (M.mul_lt _ h1 _ h2) _ hg,
      M.dec_eq_one_iff (M.mul_lt _ (M.mul_lt _ h1 _ h2) _ hg), nbeq, beq_iff_eq]
  rw [ninvC_eq, ninv2, cntB_eq, cntB_eq, length_filter_range, length_filter_range]
  change _ = Nat.card _ + Nat.card _
  have hf0 : Finite {c : ℕ // c < 128 ∧
      (!Nat.beq (hL HL c) 0 && Nat.beq (mul (hL HL c) (hL HL c)) 0) = true} :=
    Finite.of_injective (fun c => (⟨c.1, c.2.1⟩ : Fin 128)) fun a b h =>
      Subtype.ext (congrArg Fin.val h)
  have hf1 : Finite {c : ℕ // c < 128 ∧
      Nat.beq (mul (mul (hL HL c) (l16 FT (hL HL c))) g) 0 = true} :=
    Finite.of_injective (fun c => (⟨c.1, c.2.1⟩ : Fin 128)) fun a b h =>
      Subtype.ext (congrArg Fin.val h)
  rw [← Nat.card_sum]
  symm
  refine Nat.card_eq_of_bijective (Sum.elim
    (fun c => ⟨⟨dec (hL HL c.1), false⟩, (cycExt_comm hαt _ _).2 (hcm c.1 c.2.1),
      (cycExt_sq_false _).2 ((hp0 c.1 c.2.1).1 c.2.2).1, fun h =>
        ((hp0 c.1 c.2.1).1 c.2.2).2 (congrArg CycExt.k h)⟩)
    (fun c => ⟨⟨dec (hL HL c.1), true⟩, (cycExt_comm hαt _ _).2 (hcm c.1 c.2.1),
      (cycExt_sq_true _).2 ((hp1 c.1 c.2.1).1 c.2.2), fun h =>
        Bool.noConfusion (congrArg CycExt.d h)⟩)) ⟨?_, ?_⟩
  · rintro (a | a) (b | b) h
    · have e := congrArg (fun x => (x.1 : CycExt D).k) h
      exact congrArg Sum.inl (Subtype.ext (hinj _ a.2.1 _ b.2.1 e))
    · exact Bool.noConfusion (congrArg (fun x => (x.1 : CycExt D).d) h)
    · exact Bool.noConfusion (congrArg (fun x => (x.1 : CycExt D).d) h)
    · have e := congrArg (fun x => (x.1 : CycExt D).k) h
      exact congrArg Sum.inr (Subtype.ext (hinj _ a.2.1 _ b.2.1 e))
  · rintro ⟨⟨k, d⟩, hc, hs, hne⟩
    obtain ⟨j, hj, hjk⟩ := hOK_mem M ht hH k ((cycExt_comm hαt k d).1 hc)
    subst hjk
    cases d
    · refine ⟨Sum.inl ⟨j, hj, (hp0 j hj).2 ⟨(cycExt_sq_false _).1 hs, fun h1 => hne ?_⟩⟩, rfl⟩
      rw [h1]
      rfl
    · exact ⟨Sum.inr ⟨j, hj, (hp1 j hj).2 ((cycExt_sq_true _).1 hs)⟩, rfl⟩

end Certificates.KernelTower
