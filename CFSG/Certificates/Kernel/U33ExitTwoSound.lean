module

public import Certificates.Data.Kernel.U33ExitTwo
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.U33Exit

open CFSG.KS.PK CFSG.ClassicalInvolution.Q3.TA3.Check

@[expose] def AtT {M : Type*} [Group M] [DecidableEq M] (P A : Subgroup M) (t : M) : Prop :=
  (∀ a b a' b' : M, (a ∈ A ∧ b ∈ A ∧ a * a = t ∧ b * b = t ∧ b * a = t * a * b) →
      (a' ∈ A ∧ b' ∈ A ∧ a' * a' = t ∧ b' * b' = t ∧ b' * a' = t * a' * b') →
      ((a ∈ P ∧ b ∈ P) ↔ (a' ∈ P ∧ b' ∈ P)) → ∀ x ∈ q8B t a b, x ∈ q8B t a' b') ∧
    ∃ ao bo ai bi g : M, (ao ∈ A ∧ bo ∈ A ∧ ao * ao = t ∧ bo * bo = t ∧ bo * ao = t * ao * bo) ∧
      ¬(ao ∈ P ∧ bo ∈ P) ∧
      (ai ∈ A ∧ bi ∈ A ∧ ai * ai = t ∧ bi * bi = t ∧ bi * ai = t * ai * bi) ∧
      ai ∈ P ∧ bi ∈ P ∧ g ∈ A ∧
      (∃ c ∈ q8B t ao bo, c * c = t ∧ g * c * g⁻¹ * t = t * (g * c * g⁻¹)) ∧
      ∃ d ∈ q8B t ao bo, ∃ x ∈ q8B t ai bi, g * d * g⁻¹ * x * (g * d * g⁻¹)⁻¹ ∉ q8B t ai bi

theorem frc_eq {β : Sort _} (y : Nat) (k : Nat → β) : frc y k = k y := by
  cases y <;> rfl

theorem beq_iff {x y : Nat} : Nat.beq x y = true ↔ x = y :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl x⟩

theorem blt_iff {x y : Nat} : Nat.blt x y = true ↔ x < y := by
  rw [Nat.blt_eq]

theorem fx_eq (x i : Nat) : fx x i = fd 5 x i := by
  unfold fx fd
  rw [Nat.shiftRight_eq_div_pow, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem pkF_eq (f : Nat → Nat) (n : Nat) : pkF f n = enc 5 f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : pkF f (n + 1) = pkF f n + f n * 2 ^ (5 * n) := rfl
    rw [h, ih, enc_succ]

theorem fx_lt (x i : Nat) : fx x i < 32 := by
  rw [fx_eq]
  exact fd_lt 5 x i

theorem fx_pkF {f : Nat → Nat} (hf : ∀ i < 28, f i < 32) {i : Nat} (hi : i < 28) :
    fx (pkF f 28) i = f i := by
  rw [fx_eq, pkF_eq]
  exact fd_enc (fun j hj => hf j hj) hi

@[expose] def Rep (c : Nat) (σ : Equiv.Perm (Fin 28)) : Prop := ∀ i : Fin 28, fx c i = (σ i : Nat)

@[expose] def Canon (c : Nat) : Prop := c < 2 ^ 140

theorem rep_mul {x y : Nat} {σ τ : Equiv.Perm (Fin 28)} (hx : Rep x σ) (hy : Rep y τ) :
    Rep (mulC x y) (σ * τ) := by
  intro i
  unfold mulC
  rw [fx_pkF (fun j _ => fx_lt _ _) i.2, hy i, hx (τ i)]
  rfl

theorem rep_one : Rep oneC 1 := fun i => by
  unfold oneC
  rw [fx_pkF (fun j hj => by omega) i.2]
  rfl

theorem canon_pkF {f : Nat → Nat} (hf : ∀ i < 28, f i < 32) : Canon (pkF f 28) := by
  unfold Canon
  rw [pkF_eq]
  exact enc_lt (w := 5) (len := 28) fun i hi => hf i hi

theorem canon_mul (x y : Nat) : Canon (mulC x y) := canon_pkF fun _ _ => fx_lt _ _

theorem canon_one : Canon oneC := canon_pkF fun _ hj => by omega

theorem rep_eq {c : Nat} {σ τ : Equiv.Perm (Fin 28)} (h1 : Rep c σ) (h2 : Rep c τ) : σ = τ :=
  Equiv.ext fun i => Fin.ext ((h1 i).symm.trans (h2 i))

theorem rep_inj {c c' : Nat} {σ : Equiv.Perm (Fin 28)} (hc : Canon c) (hc' : Canon c')
    (h : Rep c σ) (h' : Rep c' σ) : c = c' := by
  refine eq_of_fd_eq (w := 5) (len := 28) hc hc' fun i hi => ?_
  rw [← fx_eq, ← fx_eq, h ⟨i, hi⟩, h' ⟨i, hi⟩]

theorem rep_of_repB {c : Nat} {σ : Equiv.Perm (Fin 28)} (h : repB c σ = true) : Rep c σ := by
  intro i
  exact beq_iff.1 (List.all_eq_true.1 h i (List.mem_finRange i))

@[expose] def evP (S : List (Equiv.Perm (Fin 28))) (w : List Nat) : Equiv.Perm (Fin 28) :=
  (w.map fun l => S.getD l 1).prod

theorem evP_cons (S : List (Equiv.Perm (Fin 28))) (l : Nat) (w : List Nat) :
    evP S (l :: w) = S.getD l 1 * evP S w := by
  rw [evP, List.map_cons, List.prod_cons, ← evP]

theorem evP_append (S : List (Equiv.Perm (Fin 28))) (u v : List Nat) :
    evP S (u ++ v) = evP S u * evP S v := by
  rw [evP, List.map_append, List.prod_append, ← evP, ← evP]

theorem rep_getD {gs : List Nat} {S : List (Equiv.Perm (Fin 28))} (h : List.Forall₂ Rep gs S)
    (l : Nat) : Rep (gs.getD l oneC) (S.getD l 1) := by
  induction h generalizing l with
  | nil =>
    rw [List.getD_nil, List.getD_nil]
    exact rep_one
  | cons hab _ ih =>
    cases l with
    | zero =>
      rw [List.getD_cons_zero, List.getD_cons_zero]
      exact hab
    | succ l =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact ih l

theorem evA_cons (gs : List Nat) (l : Nat) (w : List Nat) (acc : Nat) :
    evA gs (l :: w) acc = evA gs w (mulC acc (gs.getD l oneC)) :=
  frc_eq _ _

theorem rep_evA {gs : List Nat} {S : List (Equiv.Perm (Fin 28))} (hS : List.Forall₂ Rep gs S)
    (w : List Nat) : ∀ {acc : Nat} {σ : Equiv.Perm (Fin 28)}, Rep acc σ →
      Rep (evA gs w acc) (σ * evP S w) := by
  induction w with
  | nil =>
    intro acc σ h
    rw [evP, List.map_nil, List.prod_nil, mul_one]
    exact h
  | cons l w ih =>
    intro acc σ h
    rw [evA_cons, evP_cons, ← mul_assoc]
    exact ih (rep_mul h (rep_getD hS l))

theorem rep_evW {gs : List Nat} {S : List (Equiv.Perm (Fin 28))} (hS : List.Forall₂ Rep gs S)
    (w : List Nat) : Rep (evW gs w) (evP S w) := by
  have h := rep_evA hS w rep_one
  rwa [one_mul] at h

theorem canon_evA (gs w : List Nat) : ∀ {acc : Nat}, Canon acc → Canon (evA gs w acc) := by
  induction w with
  | nil => exact fun h => h
  | cons l w ih =>
    intro acc _
    rw [evA_cons]
    exact ih (canon_mul _ _)

theorem canon_evW (gs w : List Nat) : Canon (evW gs w) := canon_evA gs w canon_one

theorem getD_mem {H : Subgroup (Equiv.Perm (Fin 28))} {S : List (Equiv.Perm (Fin 28))}
    (hS : ∀ s ∈ S, s ∈ H) (l : Nat) : S.getD l 1 ∈ H := by
  induction S generalizing l with
  | nil => exact H.one_mem
  | cons s S ih =>
    cases l with
    | zero => exact hS s List.mem_cons_self
    | succ l => exact ih (fun x hx => hS x (List.mem_cons_of_mem _ hx)) l

theorem evP_mem {H : Subgroup (Equiv.Perm (Fin 28))} {S : List (Equiv.Perm (Fin 28))}
    {w : List Nat} (h : ∀ l ∈ w, S.getD l 1 ∈ H) : evP S w ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  exact h l hl

theorem innerW_iff {w : List Nat} : innerW w = true ↔ ∀ l ∈ w, l < 2 := by
  unfold innerW
  simp only [List.all_eq_true, blt_iff]

theorem mem_iff_innerW {P : Subgroup (Equiv.Perm (Fin 28))} {S : List (Equiv.Perm (Fin 28))}
    (hP : ∀ l < 2, S.getD l 1 ∈ P) (hout : ∀ x ∈ P, x * S.getD 2 1 ∉ P) {w : List Nat}
    (hw : formW w = true) : evP S w ∈ P ↔ innerW w = true := by
  by_cases hi : innerW w = true
  · exact iff_of_true (evP_mem fun l hl => hP l (innerW_iff.1 hi l hl)) hi
  · refine iff_of_false (fun hm => ?_) hi
    have hw' : innerW w.dropLast = true ∧ Nat.beq (w.getLastD 0) 2 = true := by
      unfold formW at hw
      rw [Bool.eq_false_iff.2 hi, Bool.false_or, Bool.and_eq_true] at hw
      exact hw
    have hne : w ≠ [] := by
      rintro rfl
      exact hi rfl
    have hl : w.getLast hne = 2 := by
      have h := beq_iff.1 hw'.2
      rwa [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hne, Option.getD_some] at h
    have e : w = w.dropLast ++ [2] := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      rw [hl]
    rw [e, evP_append] at hm
    have h2 : evP S [2] = S.getD 2 1 := by rw [evP_cons, evP, List.map_nil, List.prod_nil, mul_one]
    rw [h2] at hm
    exact hout _ (evP_mem fun l hl => hP l (innerW_iff.1 hw'.1 l hl)) hm

theorem memN_iff {x : Nat} {L : List Nat} : memN x L = true ↔ x ∈ L := by
  unfold memN
  rw [List.any_eq_true]
  exact ⟨fun ⟨y, hy, h⟩ => beq_iff.1 h ▸ hy, fun h => ⟨x, h, beq_iff.2 rfl⟩⟩

theorem subN_mem {L Q : List Nat} (h : subN L Q = true) {x : Nat} (hx : x ∈ L) : x ∈ Q :=
  memN_iff.1 (List.all_eq_true.1 h x hx)

theorem forall₂_left {L : List Nat} {P : List (Equiv.Perm (Fin 28))} (h : List.Forall₂ Rep L P)
    {x : Nat} (hx : x ∈ L) : ∃ y ∈ P, Rep x y := by
  induction h with
  | nil => exact absurd hx List.not_mem_nil
  | @cons a b _ _ hab _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨y, hy, h⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem forall₂_right {L : List Nat} {P : List (Equiv.Perm (Fin 28))} (h : List.Forall₂ Rep L P)
    {y : Equiv.Perm (Fin 28)} (hy : y ∈ P) : ∃ x ∈ L, Rep x y := by
  induction h with
  | nil => exact absurd hy List.not_mem_nil
  | @cons a b _ _ hab _ ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨x, hx, h⟩ := ih hy
      exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

theorem rep_q8 {t a b : Nat} {T A B : Equiv.Perm (Fin 28)} (ht : Rep t T) (ha : Rep a A)
    (hb : Rep b B) : List.Forall₂ Rep (q8C t a b) (q8B T A B) :=
  .cons rep_one (.cons ha (.cons ht (.cons (rep_mul ht ha) (.cons hb (.cons (rep_mul hb ha)
    (.cons (rep_mul hb ht) (.cons (rep_mul hb (rep_mul ht ha)) .nil)))))))

theorem canon_q8 {t a b : Nat} (ht : Canon t) (ha : Canon a) (hb : Canon b) :
    ∀ x ∈ q8C t a b, Canon x := by
  intro x hx
  simp only [q8C, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact canon_one | assumption | exact canon_mul _ _

theorem incB_pairwise : ∀ {l : List Nat} {p : Nat}, incB p l = true →
    l.Pairwise (· < ·) ∧ ∀ y ∈ l, p < y
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, p, h => by
    have h' : (Nat.blt p x && incB x l) = true := h
    rw [Bool.and_eq_true, blt_iff] at h'
    obtain ⟨h1, h2⟩ := incB_pairwise h'.2
    refine ⟨List.Pairwise.cons (fun y hy => h2 y hy) h1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h'.1
    · exact h'.1.trans (h2 y hy)

theorem pair_of_pairC {t a b : Nat} {T A B : Equiv.Perm (Fin 28)} (ht : Rep t T) (ha : Rep a A)
    (hb : Rep b B) (h : pairC t a b = true) : A * A = T ∧ B * B = T ∧ B * A = T * A * B := by
  unfold pairC relC at h
  simp only [Bool.and_eq_true, beq_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨rep_eq (h1 ▸ rep_mul ha ha) ht, rep_eq (h2 ▸ rep_mul hb hb) ht, ?_⟩
  exact rep_eq (rep_mul hb ha) (h3 ▸ rep_mul (rep_mul ht ha) hb)

variable {P A : Subgroup (Equiv.Perm (Fin 28))} {gs : List Nat} {S : List (Equiv.Perm (Fin 28))}
  {t : Nat} {T : Equiv.Perm (Fin 28)}

theorem ent_facts {E : List (Nat × List Nat)} (hS : List.Forall₂ Rep gs S) (hT : Rep t T)
    (hent : E.all (entOK gs t) = true) {e : Nat × List Nat} (he : e ∈ E) :
    evW gs e.2 = e.1 ∧ Rep e.1 (evP S e.2) ∧ formW e.2 = true ∧
      evP S e.2 * T = T * evP S e.2 := by
  have h := List.all_eq_true.1 hent e he
  unfold entOK at h
  simp only [Bool.and_eq_true, beq_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hr : Rep e.1 (evP S e.2) := h1 ▸ rep_evW hS e.2
  exact ⟨h1, hr, h2, rep_eq (rep_mul hr hT) (h3 ▸ rep_mul hT hr)⟩

theorem complete_of_checks {E : List (Nat × List Nat)} (hS : List.Forall₂ Rep gs S)
    (hT : Rep t T) (hSA : ∀ s ∈ S, s ∈ A) (hent : E.all (entOK gs t) = true)
    (hinc : incB 0 (E.map Prod.fst) = true)
    (hC : Nat.card {g // g ∈ A ∧ g * T = T * g} = E.length) {g : Equiv.Perm (Fin 28)} (hg : g ∈ A)
    (hgT : g * T = T * g) : ∃ e ∈ E, evP S e.2 = g := by
  classical
  have hcode : ∀ e ∈ E, evW gs e.2 = e.1 := fun e he => (ent_facts hS hT hent he).1
  have hpw : (E.map fun e => evP S e.2).Pairwise (· ≠ ·) := by
    rw [List.pairwise_map]
    have h1 := (incB_pairwise hinc).1
    rw [List.pairwise_map] at h1
    refine h1.imp_of_mem fun {e₁ e₂} he₁ he₂ hlt heq => ?_
    have h := rep_inj (canon_evW gs e₁.2) (canon_evW gs e₂.2) (rep_evW hS e₁.2)
      (heq ▸ rep_evW hS e₂.2)
    rw [hcode e₁ he₁, hcode e₂ he₂] at h
    exact absurd h (Nat.ne_of_lt hlt)
  set F := (E.map fun e => evP S e.2).toFinset with hF
  set Z := (Finset.univ.filter fun g : Equiv.Perm (Fin 28) => g ∈ A ∧ g * T = T * g) with hZ
  have hFcard : F.card = E.length := by
    rw [hF, List.toFinset_card_of_nodup hpw, List.length_map]
  have hZcard : Z.card = E.length := by
    rw [← hC, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hFZ : F ⊆ Z := by
    intro x hx
    rw [hF, List.mem_toFinset, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [hZ, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, evP_mem fun l _ => getD_mem hSA l, (ent_facts hS hT hent he).2.2.2⟩
  have hEq : F = Z := Finset.eq_of_subset_of_card_le hFZ (by rw [hFcard, hZcard])
  have hgZ : g ∈ Z := by
    rw [hZ, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hg, hgT⟩
  rw [← hEq, hF, List.mem_toFinset, List.mem_map] at hgZ
  exact hgZ

theorem entry_of_sq {E : List (Nat × List Nat)} (hS : List.Forall₂ Rep gs S) (hT : Rep t T)
    (hSA : ∀ s ∈ S, s ∈ A) (hent : E.all (entOK gs t) = true)
    (hinc : incB 0 (E.map Prod.fst) = true)
    (hC : Nat.card {g // g ∈ A ∧ g * T = T * g} = E.length) (htc : Canon t)
    {a : Equiv.Perm (Fin 28)} (ha : a ∈ A) (haa : a * a = T) :
    ∃ e ∈ E.filter (fun e => Nat.beq (mulC e.1 e.1) t), evP S e.2 = a := by
  obtain ⟨e, he, rfl⟩ := complete_of_checks hS hT hSA hent hinc hC ha
    (by rw [← haa, mul_assoc])
  refine ⟨e, List.mem_filter.2 ⟨he, beq_iff.2 ?_⟩, rfl⟩
  have hr := (ent_facts hS hT hent he).2.1
  exact rep_inj (canon_mul _ _) htc (haa ▸ rep_mul hr hr) hT

theorem atT_of_checks {E : List (Nat × List Nat)} {Qi Qo : List Nat} {W : List (List Nat)}
    (hS : List.Forall₂ Rep gs S) (hT : Rep t T) (hSA : ∀ s ∈ S, s ∈ A)
    (hP : ∀ l < 2, S.getD l 1 ∈ P) (hout : ∀ x ∈ P, x * S.getD 2 1 ∉ P)
    (hent : E.all (entOK gs t) = true) (hinc : incB 0 (E.map Prod.fst) = true)
    (hC : Nat.card {g // g ∈ A ∧ g * T = T * g} = E.length)
    (huniq : uniqOK t E Qi Qo = true) (hwit : witOK gs t W = true) : AtT P A T := by
  have hmemA : ∀ w, evP S w ∈ A := fun w => evP_mem fun l _ => getD_mem hSA l
  unfold uniqOK at huniq
  unfold witOK at hwit
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hwit
  obtain ⟨⟨⟨⟨⟨hf0, hf1⟩, hno⟩, hi2⟩, hi3⟩, hw⟩ := hwit
  have htc : Canon t := by
    unfold witC at hw
    simp only [Bool.and_eq_true] at hw
    exact blt_iff.1 hw.1.1.1.1.1
  refine ⟨fun a b a' b' hab hab' hty x hx => ?_, ?_⟩
  ·
    have key : ∀ {a b : Equiv.Perm (Fin 28)}, (a ∈ A ∧ b ∈ A ∧ a * a = T ∧ b * b = T ∧
        b * a = T * a * b) → ∃ ea eb : Nat × List Nat, ea ∈ E ∧ eb ∈ E ∧
          evP S ea.2 = a ∧ evP S eb.2 = b ∧
          ((a ∈ P ∧ b ∈ P) ↔ (innerW ea.2 && innerW eb.2) = true) ∧
          subN (q8C t ea.1 eb.1) (cond (innerW ea.2 && innerW eb.2) Qi Qo) = true ∧
          subN (cond (innerW ea.2 && innerW eb.2) Qi Qo) (q8C t ea.1 eb.1) = true := by
      intro a b ⟨ha, hb, haa, hbb, hba⟩
      obtain ⟨ea, hea, rfl⟩ := entry_of_sq hS hT hSA hent hinc hC htc ha haa
      obtain ⟨eb, heb, rfl⟩ := entry_of_sq hS hT hSA hent hinc hC htc hb hbb
      have hea' := (List.mem_filter.1 hea).1
      have heb' := (List.mem_filter.1 heb).1
      obtain ⟨-, hra, hfa, -⟩ := ent_facts hS hT hent hea'
      obtain ⟨-, hrb, hfb, -⟩ := ent_facts hS hT hent heb'
      have hrel : relC t ea.1 eb.1 = true := by
        unfold relC
        refine beq_iff.2 (rep_inj (canon_mul _ _) (canon_mul _ _) (rep_mul hrb hra) ?_)
        rw [hba]
        exact rep_mul (rep_mul hT hra) hrb
      have h := List.all_eq_true.1 (List.all_eq_true.1 huniq ea hea) eb heb
      rw [hrel, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      refine ⟨ea, eb, hea', heb', rfl, rfl, ?_, h.1, h.2⟩
      rw [Bool.and_eq_true, mem_iff_innerW hP hout hfa, mem_iff_innerW hP hout hfb]
    obtain ⟨ea, eb, hea, heb, rfl, rfl, hta, h1, -⟩ := key hab
    obtain ⟨ea', eb', hea', heb', rfl, rfl, hta', -, h2⟩ := key hab'
    have hty' : (innerW ea.2 && innerW eb.2) = (innerW ea'.2 && innerW eb'.2) :=
      Bool.eq_iff_iff.2 (hta.symm.trans (hty.trans hta'))
    obtain ⟨-, hra, -, -⟩ := ent_facts hS hT hent hea
    obtain ⟨-, hrb, -, -⟩ := ent_facts hS hT hent heb
    obtain ⟨-, hra', -, -⟩ := ent_facts hS hT hent hea'
    obtain ⟨-, hrb', -, -⟩ := ent_facts hS hT hent heb'
    obtain ⟨c, hc, hcx⟩ := forall₂_right (rep_q8 hT hra hrb) hx
    have hcQ := subN_mem h1 hc
    rw [hty'] at hcQ
    obtain ⟨y, hy, hcy⟩ := forall₂_left (rep_q8 hT hra' hrb') (subN_mem h2 hcQ)
    exact rep_eq hcy hcx ▸ hy
  ·
    set w0 := W.getD 0 []
    set w1 := W.getD 1 []
    set w2 := W.getD 2 []
    set w3 := W.getD 3 []
    set w4 := W.getD 4 []
    set w5 := W.getD 5 []
    have r0 := rep_evW hS w0
    have r1 := rep_evW hS w1
    have r2 := rep_evW hS w2
    have r3 := rep_evW hS w3
    have r4 := rep_evW hS w4
    have r5 := rep_evW hS w5
    unfold witC at hw
    simp only [Bool.and_eq_true] at hw
    obtain ⟨⟨⟨⟨⟨-, hpo⟩, hpi⟩, hgi⟩, hc⟩, hd⟩ := hw
    obtain ⟨hao, hbo, hrelo⟩ := pair_of_pairC hT r0 r1 hpo
    obtain ⟨hai, hbi, hreli⟩ := pair_of_pairC hT r2 r3 hpi
    have hG : evP S w5 = (evP S w4)⁻¹ :=
      eq_inv_of_mul_eq_one_right (rep_eq (beq_iff.1 hgi ▸ rep_mul r4 r5) rep_one)
    have hqo := rep_q8 hT r0 r1
    have hqi := rep_q8 hT r2 r3
    have hf2 : formW w2 = true := by
      unfold formW
      rw [hi2, Bool.true_or]
    have hf3 : formW w3 = true := by
      unfold formW
      rw [hi3, Bool.true_or]
    refine ⟨evP S w0, evP S w1, evP S w2, evP S w3, evP S w4,
      ⟨hmemA _, hmemA _, hao, hbo, hrelo⟩, ?_, ⟨hmemA _, hmemA _, hai, hbi, hreli⟩,
      (mem_iff_innerW hP hout hf2).2 hi2, (mem_iff_innerW hP hout hf3).2 hi3, hmemA _, ?_, ?_⟩
    · rw [mem_iff_innerW hP hout hf0, mem_iff_innerW hP hout hf1, ← Bool.and_eq_true, hno]
      decide
    · obtain ⟨c, hc, hcc⟩ := List.any_eq_true.1 hc
      obtain ⟨C, hC', hrc⟩ := forall₂_left hqo hc
      rw [Bool.and_eq_true, beq_iff, beq_iff] at hcc
      refine ⟨C, hC', rep_eq (hcc.1 ▸ rep_mul hrc hrc) hT, ?_⟩
      have h := rep_eq (rep_mul (rep_mul (rep_mul r4 hrc) r5) hT)
        (hcc.2 ▸ rep_mul hT (rep_mul (rep_mul r4 hrc) r5))
      rwa [hG] at h
    · obtain ⟨d, hd', hdd⟩ := List.any_eq_true.1 hd
      obtain ⟨e, he, hee⟩ := List.any_eq_true.1 hdd
      rw [Bool.and_eq_true, beq_iff] at hee
      obtain ⟨x, hx, hxx⟩ := List.any_eq_true.1 hee.2
      obtain ⟨D, hD, hrd⟩ := forall₂_left hqo hd'
      obtain ⟨E', -, hre⟩ := forall₂_left hqo he
      obtain ⟨X, hX, hrx⟩ := forall₂_left hqi hx
      have hE : E' = D⁻¹ := eq_inv_of_mul_eq_one_right (rep_eq (hee.1 ▸ rep_mul hrd hre) rep_one)
      refine ⟨D, hD, X, hX, fun hm => ?_⟩
      have hy := rep_mul (rep_mul (rep_mul (rep_mul r4 hrd) r5) hrx) (rep_mul r4 (rep_mul hre r5))
      have e1 : evP S w4 * D * evP S w5 * X * (evP S w4 * (E' * evP S w5)) =
          evP S w4 * D * (evP S w4)⁻¹ * X * (evP S w4 * D * (evP S w4)⁻¹)⁻¹ := by
        rw [hG, hE]
        group
      rw [e1] at hy
      obtain ⟨c', hc', hrc'⟩ := forall₂_right hqi hm
      have hcan := canon_q8 htc (canon_evW gs w2) (canon_evW gs w3) c' hc'
      have heq := rep_inj (canon_mul _ _) hcan hy hrc'
      rw [← heq] at hc'
      rw [memN_iff.2 hc'] at hxx
      exact absurd hxx (by decide)

section Conj

variable {M : Type*} [Group M] [DecidableEq M]

theorem q8B_map (f : M →* M) (t a b : M) : q8B (f t) (f a) (f b) = (q8B t a b).map f := by
  simp [q8B, map_mul, map_one]

theorem conj_mem_iff {A H : Subgroup M} (hH : ∀ s ∈ A, ∀ x ∈ H, s * x * s⁻¹ ∈ H) {σ : M}
    (hσ : σ ∈ A) (x : M) : MulAut.conj σ x ∈ H ↔ x ∈ H := by
  rw [MulAut.conj_apply]
  refine ⟨fun h => ?_, fun h => hH σ hσ x h⟩
  have h1 := hH σ⁻¹ (A.inv_mem hσ) _ h
  simpa [mul_assoc] using h1

theorem atT_conj {P A : Subgroup M} (hPA : ∀ s ∈ A, ∀ x ∈ P, s * x * s⁻¹ ∈ P) {t : M}
    (h : AtT P A t) {σ : M} (hσ : σ ∈ A) : AtT P A (σ * t * σ⁻¹) := by
  have hAA : ∀ s ∈ A, ∀ x ∈ A, s * x * s⁻¹ ∈ A := fun s hs x hx =>
    A.mul_mem (A.mul_mem hs hx) (A.inv_mem hs)
  set φ : M ≃* M := MulAut.conj σ with hφ
  have ht : σ * t * σ⁻¹ = φ t := (MulAut.conj_apply σ t).symm
  have hA : ∀ x, φ x ∈ A ↔ x ∈ A := conj_mem_iff hAA hσ
  have hP : ∀ x, φ x ∈ P ↔ x ∈ P := conj_mem_iff hPA hσ
  have hq : ∀ u v w : M, q8B (φ u) (φ v) (φ w) = (q8B u v w).map φ := fun u v w =>
    q8B_map φ.toMonoidHom u v w
  have hinj : ∀ u v : M, φ u = φ v ↔ u = v := fun u v => φ.injective.eq_iff
  have hpair : ∀ a b : M, (φ a ∈ A ∧ φ b ∈ A ∧ φ a * φ a = φ t ∧ φ b * φ b = φ t ∧
      φ b * φ a = φ t * φ a * φ b) ↔ (a ∈ A ∧ b ∈ A ∧ a * a = t ∧ b * b = t ∧ b * a = t * a * b) := by
    intro a b
    simp only [← map_mul, hinj, hA]
  rw [ht]
  obtain ⟨hU, ao, bo, ai, bi, g, hpo, hno, hpi, hai, hbi, hg, ⟨c, hc, hcc, hct⟩, d, hd, x, hx, hdx⟩ :=
    h
  refine ⟨fun a b a' b' hab hab' hty y hy => ?_, φ ao, φ bo, φ ai, φ bi, φ g,
    (hpair ao bo).2 hpo, by rwa [hP, hP], (hpair ai bi).2 hpi, (hP ai).2 hai, (hP bi).2 hbi,
    (hA g).2 hg, ⟨φ c, ?_, ?_, ?_⟩, φ d, ?_, φ x, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := φ.surjective a
    obtain ⟨b, rfl⟩ := φ.surjective b
    obtain ⟨a', rfl⟩ := φ.surjective a'
    obtain ⟨b', rfl⟩ := φ.surjective b'
    obtain ⟨y, rfl⟩ := φ.surjective y
    rw [hq] at hy ⊢
    rw [List.mem_map_of_injective φ.injective] at hy ⊢
    exact hU a b a' b' ((hpair a b).1 hab) ((hpair a' b').1 hab') (by rwa [hP, hP, hP, hP] at hty) y
      hy
  · rw [hq]
    exact List.mem_map_of_mem hc
  · rw [← map_mul, hcc]
  · have := congrArg φ hct
    simpa only [map_mul, map_inv] using this
  · rw [hq]
    exact List.mem_map_of_mem hd
  · rw [hq]
    exact List.mem_map_of_mem hx
  · have e : φ g * φ d * (φ g)⁻¹ * φ x * (φ g * φ d * (φ g)⁻¹)⁻¹ =
        φ (g * d * g⁻¹ * x * (g * d * g⁻¹)⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e, hq, List.mem_map_of_injective φ.injective]
    exact hdx

end Conj

end CFSG.KC.U33Exit

end
