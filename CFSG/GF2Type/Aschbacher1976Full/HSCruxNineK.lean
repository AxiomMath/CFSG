module

public import CFSG.Permutation.FinPackInv
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.CruxNineK

open Equiv CFSG.Permutation.FinPack

@[expose] def presF (g : Perm (Fin 6)) : Prop :=
  ∀ x y : Fin 6, ((x : ℕ) < 3 ↔ (y : ℕ) < 3) ↔ (((g x : Fin 6) : ℕ) < 3 ↔ ((g y : Fin 6) : ℕ) < 3)

@[expose] def fin4F (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] def labF (c0 c1 c2 : Fin 6) : Fin 4 :=
  fin4F (2 * (if (c0 : ℕ) < 3 then 0 else 1) + (if ((c1 : ℕ) + 6 - (c0 : ℕ)) % 3 = 1 then 0 else 1))

@[expose] def actF (g : Perm (Fin 6)) : Fin 4 → Fin 4 :=
  ![labF (g 0) (g 1) (g 2), labF (g 0) (g 2) (g 1), labF (g 3) (g 4) (g 5), labF (g 3) (g 5) (g 4)]

@[expose] noncomputable def fc (f : Fin 4 → Fin 4) : ℕ :=
  encF (fun i => if h : i < 4 then (f ⟨i, h⟩ : ℕ) else 0) 4

theorem rd_fc (f : Fin 4 → Fin 4) (i : Fin 4) : rd (fc f) i = f i := by
  rw [fc, rd_encF (fun j hj => by rw [dif_pos hj]; exact lt_of_lt_of_le (Fin.isLt _) (by norm_num))
    i.isLt]
  simp

theorem fc_inj {f g : Fin 4 → Fin 4} (h : fc f = fc g) : f = g :=
  funext fun i => Fin.ext (by rw [← rd_fc f i, ← rd_fc g i, h])

theorem fc_comp (f g : Fin 4 → Fin 4) : fc (fun z => f (g z)) = mulK 4 (fc f) (fc g) := by
  rw [mulK]
  conv_lhs => rw [fc]
  refine encF_congr fun i hi => ?_
  have h1 : rd (fc g) i = g ⟨i, hi⟩ := rd_fc g ⟨i, hi⟩
  rw [dif_pos hi, h1, rd_fc f]

theorem fc_id : fc id = 12816 := by decide +kernel

theorem beq_fc_iff {f g : Fin 4 → Fin 4} {c : ℕ} (h : fc g = c) : Nat.beq (fc f) c = true ↔ f = g := by
  rw [Nat.beq_eq, ← h]
  exact ⟨fc_inj, congrArg fc⟩

@[expose] def labK (a b c : ℕ) : ℕ :=
  Nat.add (Bool.rec (motive := fun _ => ℕ) 2 0 (Nat.blt a 3))
    (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (Nat.mod (Nat.sub (Nat.add b 6) a) 3) 1))

@[expose] def pA (i : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 3 0 (Nat.blt i 2)

@[expose] def pB (i : ℕ) : ℕ := Nat.add (pA i) (Nat.add 1 (Nat.land i 1))

@[expose] def pC (i : ℕ) : ℕ := Nat.sub (Nat.add (pA i) 2) (Nat.land i 1)

@[expose] noncomputable def actK (c : ℕ) : ℕ :=
  encF (fun i => labK (rd c (pA i)) (rd c (pB i)) (rd c (pC i))) 4

theorem brec_blt (x y u v : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) u v (Nat.blt x y) : ℕ) = if x < y then v else u := by
  by_cases h : x < y
  · have hb : Nat.blt x y = true := by rw [Nat.blt_eq]; exact h
    rw [hb, if_pos h]
  · have hb : Nat.blt x y = false := Bool.eq_false_iff.2 fun e => h (by rw [Nat.blt_eq] at e; exact e)
    rw [hb, if_neg h]

theorem brec_beq (x y u v : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) u v (Nat.beq x y) : ℕ) = if x = y then v else u := by
  by_cases h : x = y
  · have hb : Nat.beq x y = true := by rw [Nat.beq_eq]; exact h
    rw [hb, if_pos h]
  · have hb : Nat.beq x y = false := Bool.eq_false_iff.2 fun e => h (by rw [Nat.beq_eq] at e; exact e)
    rw [hb, if_neg h]

theorem lab_eq (c0 c1 c2 : Fin 6) : (labF c0 c1 c2 : ℕ) = labK c0 c1 c2 := by
  have hm : Nat.mod (Nat.sub (Nat.add (c1 : ℕ) 6) c0) 3 = ((c1 : ℕ) + 6 - c0) % 3 := rfl
  rw [labK, brec_blt, brec_beq, hm, labF, fin4F]
  have h0 := c0.isLt
  split_ifs <;> simp

theorem rd_enc6 (g : Perm (Fin 6)) (i : Fin 6) : rd (enc g) i = g i := rd_enc (by norm_num) g i

theorem fc_actF (g : Perm (Fin 6)) : fc (actF g) = actK (enc g) := by
  rw [fc, actK]
  refine encF_congr fun i hi => ?_
  rw [dif_pos hi]
  interval_cases i
  · have e : actF g ⟨0, hi⟩ = labF (g 0) (g 1) (g 2) := rfl
    rw [e, lab_eq, ← rd_enc6 g 0, ← rd_enc6 g 1, ← rd_enc6 g 2]
    rfl
  · have e : actF g ⟨1, hi⟩ = labF (g 0) (g 2) (g 1) := rfl
    rw [e, lab_eq, ← rd_enc6 g 0, ← rd_enc6 g 1, ← rd_enc6 g 2]
    rfl
  · have e : actF g ⟨2, hi⟩ = labF (g 3) (g 4) (g 5) := rfl
    rw [e, lab_eq, ← rd_enc6 g 3, ← rd_enc6 g 4, ← rd_enc6 g 5]
    rfl
  · have e : actF g ⟨3, hi⟩ = labF (g 3) (g 5) (g 4) := rfl
    rw [e, lab_eq, ← rd_enc6 g 3, ← rd_enc6 g 4, ← rd_enc6 g 5]
    rfl

theorem fc_cI : fc (actF (swap 0 1 * swap 3 4)) = 8961 := by
  rw [fc_actF]
  decide +kernel

@[expose] def iffB (x y : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false y) y x

theorem iffB_eq (x y : Bool) : iffB x y = true ↔ (x = true ↔ y = true) := by
  cases x <;> cases y <;> decide

@[expose] noncomputable def presB (c : ℕ) : Bool :=
  allLtK (fun i => iffB (Nat.blt i 3) (iffB (Nat.blt (rd c i) 3) (Nat.blt (rd c 0) 3))) 6

theorem presB_of (g : Perm (Fin 6)) (h : presF g) : presB (enc g) = true := by
  rw [presB, allLtK_iff]
  intro i hi
  have e := h ⟨i, hi⟩ 0
  have r0 : rd (enc g) 0 = g 0 := rd_enc6 g 0
  have ri : rd (enc g) i = g ⟨i, hi⟩ := rd_enc6 g ⟨i, hi⟩
  have z : ((0 : Fin 6) : ℕ) < 3 := by decide
  rw [iffB_eq, iffB_eq, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq, r0, ri]
  change (i < 3 ↔ ((0 : Fin 6) : ℕ) < 3) ↔ _ at e
  tauto

@[expose] def NlC : List ℕ := [5517840, 4534800, 5456400, 3490320, 4411920, 3428880, 5517600, 4534560,
  5456160, 3490080, 4411680, 3428640, 5517825, 4534785, 5456385, 3490305, 4411905, 3428865, 5517345,
  4534305, 5455905, 3489825, 4411425, 3428385, 5517570, 4534530, 5456130, 3490050, 4411650, 3428610,
  5517330, 4534290, 5455890, 3489810, 4411410, 3428370, 2164035, 1180995, 2102595, 136515, 1058115,
  75075, 2163795, 1180755, 2102355, 136275, 1057875, 74835, 2164020, 1180980, 2102580, 136500,
  1058100, 75060, 2163540, 1180500, 2102100, 136020, 1057620, 74580, 2163765, 1180725, 2102325,
  136245, 1057845, 74805, 2163525, 1180485, 2102085, 136005, 1057605, 74565]

@[expose] def D8C : List ℕ := [291, 306, 4131, 4146, 8961, 8976, 12801, 12816]

@[expose] def E9C : List ℕ :=
  [5517840, 5517345, 5517570, 3490320, 3489825, 3490050, 4411920, 4411425, 4411650]

@[expose] noncomputable def nlQ (c : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) true (memK c NlC) (presB c)

theorem nl_check : walkK 6 nlQ 6 0 0 0 = true := by decide +kernel

theorem mem_NlC (g : Perm (Fin 6)) (h : presF g) : enc g ∈ NlC := by
  have hq := walkK_sound nl_check g
  rw [nlQ, presB_of g h] at hq
  exact memK_iff.1 hq

@[expose] def orB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) y true x

theorem orB_eq (x y : Bool) : orB x y = true ↔ (x = true ∨ y = true) := by
  cases x <;> cases y <;> decide

theorem ker_check :
    allK (fun c => Bool.rec (motive := fun _ => Bool) true (memK c E9C) (Nat.beq (actK c) 12816)) NlC =
      true := by
  decide +kernel

theorem hom_check :
    allK (fun c => allK (fun d => Nat.beq (actK (mulK 6 c d)) (mulK 4 (actK c) (actK d))) NlC) NlC =
      true := by
  decide +kernel

theorem sq_check :
    allK (fun c => orB (Nat.beq (actK (mulK 6 c c)) 12816) (Nat.beq (actK (mulK 6 c c)) 8961)) NlC =
      true := by
  decide +kernel

@[expose] noncomputable def commB (c d : ℕ) : Bool :=
  orB (Nat.beq (actK (mulK 6 (mulK 6 (mulK 6 c d) (invCK 6 c)) (invCK 6 d))) 12816)
    (Nat.beq (actK (mulK 6 (mulK 6 (mulK 6 c d) (invCK 6 c)) (invCK 6 d))) 8961)

theorem comm_check : allK (fun c => allK (fun d => commB c d) NlC) NlC = true := by decide +kernel

theorem img_check : allK (fun c => memK (actK c) D8C) NlC = true := by decide +kernel

@[expose] noncomputable def cdepB (a b : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (orB (Nat.beq a 12816) (orB (Nat.beq a 8961) (orB (Nat.beq b 12816) (orB (Nat.beq b 8961)
      (orB (Nat.beq b a) (Nat.beq b (mulK 4 a 8961)))))))
    (Nat.beq (mulK 4 a b) (mulK 4 b a))

theorem cdep_check : allK (fun a => allK (fun b => cdepB a b) D8C) D8C = true := by decide +kernel

theorem ker_sound (E : List (Perm (Fin 6))) (hE : (E.map enc == E9C) = true) :
    ∀ g : Perm (Fin 6), presF g → actF g = id → g ∈ E := by
  intro g hg ha
  have h1 := allK_iff.1 ker_check _ (mem_NlC g hg)
  have h2 : Nat.beq (actK (enc g)) 12816 = true := by rw [← fc_actF, ha, fc_id, Nat.beq_refl]
  rw [h2] at h1
  have h3 := memK_iff.1 h1
  rw [← beq_iff_eq.1 hE] at h3
  exact (mem_iff_enc (by norm_num) E g).2 h3

theorem hom_sound : ∀ g : Perm (Fin 6), presF g → ∀ h : Perm (Fin 6), presF h →
    ∀ x : Fin 4, actF (g * h) x = actF g (actF h x) := by
  intro g hg h hh x
  have h1 := allK_iff.1 (allK_iff.1 hom_check _ (mem_NlC g hg)) _ (mem_NlC h hh)
  rw [← enc_mul (by norm_num), ← fc_actF, ← fc_actF, ← fc_actF, ← fc_comp, Nat.beq_eq] at h1
  exact congrFun (fc_inj h1) x

theorem sq_sound : ∀ g : Perm (Fin 6), presF g →
    actF (g * g) = id ∨ actF (g * g) = actF (swap 0 1 * swap 3 4) := by
  intro g hg
  have h1 := allK_iff.1 sq_check _ (mem_NlC g hg)
  rw [← enc_mul (by norm_num), ← fc_actF, orB_eq, beq_fc_iff fc_id, beq_fc_iff fc_cI] at h1
  exact h1

theorem comm_sound : ∀ g : Perm (Fin 6), presF g → ∀ h : Perm (Fin 6), presF h →
    actF (g * h * g⁻¹ * h⁻¹) = id ∨ actF (g * h * g⁻¹ * h⁻¹) = actF (swap 0 1 * swap 3 4) := by
  intro g hg h hh
  have h1 := allK_iff.1 (allK_iff.1 comm_check _ (mem_NlC g hg)) _ (mem_NlC h hh)
  rw [commB, ← enc_inv_invCK (by norm_num), ← enc_inv_invCK (by norm_num), ← enc_mul (by norm_num),
    ← enc_mul (by norm_num), ← enc_mul (by norm_num), ← fc_actF, orB_eq, beq_fc_iff fc_id,
    beq_fc_iff fc_cI] at h1
  exact h1

theorem cdep_sound : ∀ g : Perm (Fin 6), presF g → ∀ h : Perm (Fin 6), presF h →
    (∀ z : Fin 4, actF g (actF h z) = actF h (actF g z)) →
    actF g = id ∨ actF g = actF (swap 0 1 * swap 3 4) ∨ actF h = id ∨
      actF h = actF (swap 0 1 * swap 3 4) ∨ actF h = actF g ∨
      actF h = (fun z => actF g (actF (swap 0 1 * swap 3 4) z)) := by
  intro g hg h hh hc
  have ha := memK_iff.1 (allK_iff.1 img_check _ (mem_NlC g hg))
  have hb := memK_iff.1 (allK_iff.1 img_check _ (mem_NlC h hh))
  have h1 := allK_iff.1 (allK_iff.1 cdep_check _ ha) _ hb
  have e : Nat.beq (mulK 4 (actK (enc g)) (actK (enc h))) (mulK 4 (actK (enc h)) (actK (enc g))) =
      true := by
    rw [← fc_actF, ← fc_actF, ← fc_comp, ← fc_comp, Nat.beq_eq]
    exact congrArg fc (funext hc)
  rw [cdepB, e] at h1
  rw [← fc_actF, ← fc_actF, ← fc_cI, ← fc_comp, orB_eq, orB_eq, orB_eq, orB_eq, orB_eq,
    beq_fc_iff fc_id, beq_fc_iff rfl, beq_fc_iff fc_id, beq_fc_iff rfl, beq_fc_iff rfl,
    beq_fc_iff rfl] at h1
  exact h1

@[expose] def nineC : List ℕ :=
  [5456385, 3428865, 4534785, 5455890, 3428370, 4534290, 5456160, 3428640, 4534560]

theorem enc_mem_of {L : List (Perm (Fin 6))} {C : List ℕ} (hC : (L.map enc == C) = true)
    {x : Perm (Fin 6)} (hx : x ∈ L) : enc x ∈ C := by
  rw [← beq_iff_eq.1 hC]
  exact List.mem_map_of_mem hx

theorem mem_of_enc {L : List (Perm (Fin 6))} {C : List ℕ} (hC : (L.map enc == C) = true)
    {x : Perm (Fin 6)} (hx : enc x ∈ C) : x ∈ L := by
  rw [← beq_iff_eq.1 hC] at hx
  exact (mem_iff_enc (by norm_num) L x).2 hx

theorem mul_check : allK (fun c => allK (fun d => memK (mulK 6 c d) E9C) E9C) E9C = true := by
  decide +kernel

theorem nine_mul_check : allK (fun c => allK (fun d => memK (mulK 6 c d) E9C) nineC) nineC = true := by
  decide +kernel

theorem inv_check : allK (fun c => memK (invCK 6 c) E9C) E9C = true := by decide +kernel

theorem cube_check : allK (fun c => Nat.beq (mulK 6 c (mulK 6 c c)) 5517840) E9C = true := by
  decide +kernel

theorem prod_check :
    allK (fun c => anyK (fun s => anyK (fun t => Nat.beq c (mulK 6 s t)) nineC) nineC) E9C = true := by
  decide +kernel

@[expose] noncomputable def freeB (c : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (allK (fun s => Bool.rec (motive := fun _ => Bool) true false (Nat.beq (mulK 6 c s) (mulK 6 s c))) nineC)
    true (Nat.beq c 5517840)

theorem free_check : allK freeB E9C = true := by decide +kernel

theorem act_check : allK (fun s => Nat.beq (actK s) 8961) nineC = true := by decide +kernel

theorem enc_one6 : enc (1 : Perm (Fin 6)) = 5517840 := by decide +kernel

theorem mul2_sound {A B D : List (Perm (Fin 6))} {CA CB CD : List ℕ} (hA : (A.map enc == CA) = true)
    (hB : (B.map enc == CB) = true) (hD : (D.map enc == CD) = true)
    (h : allK (fun c => allK (fun d => memK (mulK 6 c d) CD) CB) CA = true) :
    ∀ a ∈ A, ∀ b ∈ B, a * b ∈ D := by
  intro a ha b hb
  have h1 := memK_iff.1 (allK_iff.1 (allK_iff.1 h _ (enc_mem_of hA ha)) _ (enc_mem_of hB hb))
  rw [← enc_mul (n := 6) (by norm_num)] at h1
  exact mem_of_enc hD h1

theorem inv_sound {A : List (Perm (Fin 6))} (hA : (A.map enc == E9C) = true) :
    ∀ e ∈ A, e⁻¹ ∈ A := by
  intro e he
  have h1 := memK_iff.1 (allK_iff.1 inv_check _ (enc_mem_of hA he))
  rw [← enc_inv_invCK (n := 6) (by norm_num)] at h1
  exact mem_of_enc hA h1

theorem cube_sound {A : List (Perm (Fin 6))} (hA : (A.map enc == E9C) = true) :
    ∀ e ∈ A, e ^ 3 = 1 := by
  intro e he
  have h1 := allK_iff.1 cube_check _ (enc_mem_of hA he)
  rw [← enc_mul (n := 6) (by norm_num), ← enc_mul (n := 6) (by norm_num), ← enc_one6, Nat.beq_eq] at h1
  rw [pow_three]
  exact enc_inj (by norm_num) h1

theorem prod_sound {A S : List (Perm (Fin 6))} (hA : (A.map enc == E9C) = true)
    (hS : (S.map enc == nineC) = true) : ∀ e ∈ A, ∃ s ∈ S, ∃ t ∈ S, e = s * t := by
  intro e he
  obtain ⟨s', hs', h1⟩ := anyK_iff.1 (allK_iff.1 prod_check _ (enc_mem_of hA he))
  obtain ⟨t', ht', h2⟩ := anyK_iff.1 h1
  rw [← beq_iff_eq.1 hS, List.mem_map] at hs' ht'
  obtain ⟨s, hs, rfl⟩ := hs'
  obtain ⟨t, ht, rfl⟩ := ht'
  rw [← enc_mul (n := 6) (by norm_num), Nat.beq_eq] at h2
  exact ⟨s, hs, t, ht, enc_inj (by norm_num) h2⟩

theorem free_sound {A S : List (Perm (Fin 6))} (hA : (A.map enc == E9C) = true)
    (hS : (S.map enc == nineC) = true) : ∀ e ∈ A, e ≠ 1 → ∀ s ∈ S, e * s ≠ s * e := by
  intro e he h1 s hs hc
  have h2 := allK_iff.1 free_check _ (enc_mem_of hA he)
  have h3 : Nat.beq (enc e) 5517840 = false :=
    Bool.eq_false_iff.2 fun hb => h1 (enc_inj (by norm_num) ((Nat.eq_of_beq_eq_true hb).trans enc_one6.symm))
  rw [freeB, h3] at h2
  have h4 := allK_iff.1 h2 _ (enc_mem_of hS hs)
  have h5 : Nat.beq (mulK 6 (enc e) (enc s)) (mulK 6 (enc s) (enc e)) = true := by
    rw [← enc_mul (n := 6) (by norm_num), ← enc_mul (n := 6) (by norm_num), hc, Nat.beq_refl]
  rw [h5] at h4
  exact Bool.false_ne_true h4

theorem act_sound {S : List (Perm (Fin 6))} (hS : (S.map enc == nineC) = true) :
    ∀ s ∈ S, actF s = actF (swap 0 1 * swap 3 4) := by
  intro s hs
  have h1 := allK_iff.1 act_check _ (enc_mem_of hS hs)
  rw [← fc_actF, beq_fc_iff fc_cI] at h1
  exact h1

end CFSG.GF2Type.Aschbacher1976Full.HS.CruxNineK
