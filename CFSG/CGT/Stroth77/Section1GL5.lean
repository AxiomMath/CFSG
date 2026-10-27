module

public import Certificates.Certificate778710
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.CGT.Stroth77.GL5

open scoped BigOperators

variable {A : Type*} [CommGroup A]

@[expose] noncomputable def Φ (b : Fin 5 → A) (r : Nat) : A :=
  ∏ j : Fin 5, if r.testBit j then b j else 1

theorem Φ_zero (b : Fin 5 → A) : Φ b 0 = 1 := by
  simp [Φ, Nat.zero_testBit]

theorem Φ_xor {b : Fin 5 → A} (hsq : ∀ a : A, a * a = 1) (r s : Nat) :
    Φ b (r ^^^ s) = Φ b r * Φ b s := by
  unfold Φ
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.testBit_xor]
  cases r.testBit j <;> cases s.testBit j <;> simp [hsq]

theorem Φ_ite (b : Fin 5 → A) (p : Prop) [Decidable p] (m : Nat) :
    Φ b (if p then m else 0) = if p then Φ b m else 1 := by
  split_ifs
  · rfl
  · exact Φ_zero b

theorem Φ_vm5 {b : Fin 5 → A} (hsq : ∀ a : A, a * a = 1) (v m0 m1 m2 m3 m4 : Nat) :
    Φ b (vm5 v m0 m1 m2 m3 m4) =
      (if v.testBit 0 then Φ b m0 else 1) * (if v.testBit 1 then Φ b m1 else 1) *
        (if v.testBit 2 then Φ b m2 else 1) * (if v.testBit 3 then Φ b m3 else 1) *
        (if v.testBit 4 then Φ b m4 else 1) := by
  unfold vm5
  simp only [Φ_xor hsq, Φ_ite]

theorem Φ_two_pow (b : Fin 5 → A) (j : Fin 5) : Φ b (2 ^ (j : Nat)) = b j := by
  unfold Φ
  rw [Finset.prod_eq_single j]
  · simp [Nat.testBit_two_pow_self]
  · intro i _ hij
    have : (i : Nat) ≠ j := fun h => hij (Fin.ext h)
    simp [Nat.testBit_two_pow, Ne.symm this]
  · simp

section Basis

variable {b : Fin 5 → A} (hsq : ∀ a : A, a * a = 1)
  (hgen : Subgroup.closure (Set.range b) = ⊤)

include hsq hgen in
theorem Φ_surj (a : A) : ∃ r, r < 32 ∧ Φ b r = a := by
  let S : Subgroup A :=
    { carrier := {a | ∃ r, r < 32 ∧ Φ b r = a}
      mul_mem' := by
        rintro _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
        exact ⟨r ^^^ s, xor_lt_32 hr hs, Φ_xor hsq r s⟩
      one_mem' := ⟨0, by decide, Φ_zero b⟩
      inv_mem' := by
        rintro _ ⟨r, hr, rfl⟩
        refine ⟨r, hr, ?_⟩
        rw [← mul_eq_one_iff_eq_inv]
        exact hsq _ }
  have hle : Subgroup.closure (Set.range b) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨2 ^ (j : Nat), ?_, Φ_two_pow b j⟩
    have := j.2
    interval_cases (j : Nat) <;> decide
  rw [hgen] at hle
  exact hle (Subgroup.mem_top a)

variable (hcard : Nat.card A = 32)

include hsq hgen hcard in
theorem Φ_inj {r s : Nat} (hr : r < 32) (hs : s < 32) (h : Φ b r = Φ b s) : r = s := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let f : Fin 32 → A := fun r => Φ b r
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨r, hr, rfl⟩ := Φ_surj hsq hgen a
    exact ⟨⟨r, hr⟩, rfl⟩
  have hbij := hf.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  have := hbij.1 (a₁ := ⟨r, hr⟩) (a₂ := ⟨s, hs⟩) h
  exact congrArg Fin.val this

@[expose] noncomputable def coord (b : Fin 5 → A) (a : A) : Nat :=
  open Classical in if h : ∃ r, r < 32 ∧ Φ b r = a then Classical.choose h else 0

include hsq hgen in
theorem coord_spec (a : A) : coord b a < 32 ∧ Φ b (coord b a) = a := by
  have h := Φ_surj hsq hgen a
  unfold coord
  rw [dif_pos h]
  exact Classical.choose_spec h

include hsq hgen in
theorem coord_lt (a : A) : coord b a < 32 := (coord_spec hsq hgen a).1

include hsq hgen in
theorem Φ_coord (a : A) : Φ b (coord b a) = a := (coord_spec hsq hgen a).2

include hsq hgen hcard in
theorem coord_Φ {r : Nat} (hr : r < 32) : coord b (Φ b r) = r :=
  Φ_inj hsq hgen hcard (coord_lt hsq hgen _) hr (Φ_coord hsq hgen _)

@[expose] noncomputable def code (b : Fin 5 → A) (f : MulAut A) : Nat :=
  ofRows (coord b (f (b 0))) (coord b (f (b 1))) (coord b (f (b 2))) (coord b (f (b 3)))
    (coord b (f (b 4)))

include hsq hgen in
theorem code_lt (f : MulAut A) : code b f < N :=
  ofRows_lt (coord_lt hsq hgen _) (coord_lt hsq hgen _) (coord_lt hsq hgen _)
    (coord_lt hsq hgen _) (coord_lt hsq hgen _)

include hsq hgen in
theorem r0_code (f : MulAut A) : r0 (code b f) = coord b (f (b 0)) :=
  r0_ofRows (coord_lt hsq hgen _) (coord_lt hsq hgen _) (coord_lt hsq hgen _)
    (coord_lt hsq hgen _) (coord_lt hsq hgen _)
include hsq hgen in
theorem r1_code (f : MulAut A) : r1 (code b f) = coord b (f (b 1)) :=
  r1_ofRows (coord_lt hsq hgen _) (coord_lt hsq hgen _) (coord_lt hsq hgen _)
    (coord_lt hsq hgen _) (coord_lt hsq hgen _)
include hsq hgen in
theorem r2_code (f : MulAut A) : r2 (code b f) = coord b (f (b 2)) :=
  r2_ofRows (coord_lt hsq hgen _) (coord_lt hsq hgen _) (coord_lt hsq hgen _)
    (coord_lt hsq hgen _) (coord_lt hsq hgen _)
include hsq hgen in
theorem r3_code (f : MulAut A) : r3 (code b f) = coord b (f (b 3)) :=
  r3_ofRows (coord_lt hsq hgen _) (coord_lt hsq hgen _) (coord_lt hsq hgen _)
    (coord_lt hsq hgen _) (coord_lt hsq hgen _)
include hsq hgen in
theorem r4_code (f : MulAut A) : r4 (code b f) = coord b (f (b 4)) :=
  r4_ofRows (coord_lt hsq hgen _) (coord_lt hsq hgen _) (coord_lt hsq hgen _)
    (coord_lt hsq hgen _) (coord_lt hsq hgen _)

include hsq hgen in
theorem apply_Φ (f : MulAut A) (v : Nat) : f (Φ b v) = Φ b (vm v (code b f)) := by
  rw [vm, Φ_vm5 hsq, r0_code hsq hgen, r1_code hsq hgen, r2_code hsq hgen, r3_code hsq hgen,
    r4_code hsq hgen, Φ_coord hsq hgen, Φ_coord hsq hgen, Φ_coord hsq hgen, Φ_coord hsq hgen,
    Φ_coord hsq hgen]
  unfold Φ
  rw [map_prod, Fin.prod_univ_five]
  simp [apply_ite f]

include hsq hgen hcard in
theorem coord_apply (f : MulAut A) (a : A) : coord b (f a) = vm (coord b a) (code b f) := by
  conv_lhs => rw [← Φ_coord hsq hgen a, apply_Φ hsq hgen f]
  exact coord_Φ hsq hgen hcard (vm_lt _ _)

include hsq hgen hcard in
theorem code_mul (f g : MulAut A) : code b (f * g) = mulC (code b f) (code b g) := by
  refine code_ext (code_lt hsq hgen _) (mulC_lt _ _) ?_ ?_ ?_ ?_ ?_
  · rw [r0_code hsq hgen, r0_mulC, r0_code hsq hgen, MulAut.mul_apply,
      coord_apply hsq hgen hcard]
  · rw [r1_code hsq hgen, r1_mulC, r1_code hsq hgen, MulAut.mul_apply,
      coord_apply hsq hgen hcard]
  · rw [r2_code hsq hgen, r2_mulC, r2_code hsq hgen, MulAut.mul_apply,
      coord_apply hsq hgen hcard]
  · rw [r3_code hsq hgen, r3_mulC, r3_code hsq hgen, MulAut.mul_apply,
      coord_apply hsq hgen hcard]
  · rw [r4_code hsq hgen, r4_mulC, r4_code hsq hgen, MulAut.mul_apply,
      coord_apply hsq hgen hcard]

include hsq hgen hcard in
theorem code_eq_of_apply {f : MulAut A} {c : Nat} (hc : c < N) (h0 : f (b 0) = Φ b (r0 c))
    (h1 : f (b 1) = Φ b (r1 c)) (h2 : f (b 2) = Φ b (r2 c)) (h3 : f (b 3) = Φ b (r3 c))
    (h4 : f (b 4) = Φ b (r4 c)) : code b f = c := by
  unfold code
  rw [h0, h1, h2, h3, h4, coord_Φ hsq hgen hcard (r0_lt c), coord_Φ hsq hgen hcard (r1_lt c),
    coord_Φ hsq hgen hcard (r2_lt c), coord_Φ hsq hgen hcard (r3_lt c),
    coord_Φ hsq hgen hcard (r4_lt c), ofRows_rows hc]

include hsq hgen hcard in
theorem coord_b (i : Fin 5) : coord b (b i) = 2 ^ (i : Nat) := by
  rw [← Φ_two_pow b i]
  refine coord_Φ hsq hgen hcard ?_
  have := i.2
  interval_cases (i : Nat) <;> decide

include hsq hgen hcard in
theorem code_one : code b 1 = idC := by
  unfold code
  simp only [MulAut.one_apply]
  rw [coord_b hsq hgen hcard 0, coord_b hsq hgen hcard 1, coord_b hsq hgen hcard 2,
    coord_b hsq hgen hcard 3, coord_b hsq hgen hcard 4]
  rfl

include hsq hgen hcard in
theorem code_pow (f : MulAut A) : ∀ k : Nat, code b (f ^ k) = powC (code b f) k
  | 0 => by rw [pow_zero, code_one hsq hgen hcard]; rfl
  | k + 1 => by rw [pow_succ', code_mul hsq hgen hcard, code_pow f k]; rfl

include hsq hgen in
theorem code_inj {f g : MulAut A} (h : code b f = code b g) : f = g := by
  have hb : ∀ i : Fin 5, f (b i) = g (b i) := by
    have e : ∀ i : Fin 5, coord b (f (b i)) = coord b (g (b i)) := by
      intro i
      fin_cases i
      · have := congrArg r0 h; rwa [r0_code hsq hgen, r0_code hsq hgen] at this
      · have := congrArg r1 h; rwa [r1_code hsq hgen, r1_code hsq hgen] at this
      · have := congrArg r2 h; rwa [r2_code hsq hgen, r2_code hsq hgen] at this
      · have := congrArg r3 h; rwa [r3_code hsq hgen, r3_code hsq hgen] at this
      · have := congrArg r4 h; rwa [r4_code hsq hgen, r4_code hsq hgen] at this
    intro i
    rw [← Φ_coord hsq hgen (f (b i)), e i, Φ_coord hsq hgen]
  have : (f : A →* A) = (g : A →* A) := by
    refine MonoidHom.eq_of_eqOn_dense hgen ?_
    rintro _ ⟨i, rfl⟩
    exact hb i
  exact MulEquiv.ext fun a => DFunLike.congr_fun this a

include hsq hgen hcard in
theorem nonsing_code (f : MulAut A) : nonsing (code b f) = true := by
  rw [nonsing_iff]
  intro v hv0 hv32 h0
  have h1 : f (Φ b v) = 1 := by rw [apply_Φ hsq hgen f, h0, Φ_zero]
  have h2 : Φ b v = Φ b 0 := by rw [Φ_zero]; exact f.injective (h1.trans (map_one f).symm)
  have := Φ_inj hsq hgen hcard hv32 (by decide) h2
  omega

include hsq hgen hcard in
theorem coord_apply_lt_sixteen (f : MulAut A) (hst : stabW4 (code b f) = true) (a : A)
    (ha : coord b a < 16) : coord b (f a) < 16 := by
  rw [coord_apply hsq hgen hcard]
  unfold stabW4 at hst
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hst
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hst
  have h4 : (coord b a).testBit 4 = false := Nat.testBit_lt_two_pow (by omega)
  have l16 : ∀ p : Prop, ∀ [Decidable p], ∀ m : Nat, m < 16 → (if p then m else 0) < 16 := by
    intro p _ m hm; split <;> omega
  unfold vm vm5
  rw [h4]
  simp only [Bool.false_eq_true, if_false, Nat.xor_zero]
  exact Nat.xor_lt_two_pow (n := 4) (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (l16 _ _ h0)
    (l16 _ _ h1)) (l16 _ _ h2)) (l16 _ _ h3)

end Basis

theorem uvC_mem_dCodes : uvC ∈ dCodes := by decide
theorem tC_mem_dCodes : tC ∈ dCodes := by decide
theorem uC_mem_dCodes : uC ∈ dCodes := by decide
theorem idC_mem_dCodes : idC ∈ dCodes := by decide
theorem mulC_mem_dCodes : ∀ a ∈ dCodes, ∀ c ∈ dCodes, mulC a c ∈ dCodes := by decide
theorem powC_eight_dCodes : ∀ a ∈ dCodes, powC a 8 = idC := by decide
theorem powC_seven_mem_dCodes : ∀ a ∈ dCodes, powC a 7 ∈ dCodes := by decide
theorem uvC_central_dCodes : ∀ a ∈ dCodes, mulC a uvC = mulC uvC a := by decide
theorem center_dCodes : ∀ a ∈ dCodes, mulC a tC = mulC tC a → mulC a uC = mulC uC a →
    a = idC ∨ a = uvC := by decide
theorem centralizer_V_dCodes : ∀ a ∈ dCodes, mulC a uvC = mulC uvC a →
    mulC a tC = mulC tC a → a ∈ vCodes := by decide
theorem normV_dCodes : ∀ a ∈ dCodes, normV a = true := by decide
theorem mulC_uvC_tC : mulC uvC tC = 19209281 := by decide
theorem mulC_mem_vCodes : ∀ a ∈ vCodes, ∀ c ∈ vCodes, mulC a c ∈ vCodes := by decide
theorem powC_two_vCodes : ∀ a ∈ vCodes, powC a 2 = idC := by decide
theorem uvC_ne_idC : uvC ≠ idC := by decide

@[expose] def agen (g0 g1 g2 g3 : MulAut A) (i : Nat) : MulAut A :=
  if i = 0 then g0 else if i = 1 then g1 else if i = 2 then g2 else if i = 3 then g3 else 1

@[expose] def Wd.evalA (gens : Nat → MulAut A) (f : MulAut A) : Wd → MulAut A
  | .gen i => gens i
  | .var => f
  | .mul a c => a.evalA gens f * c.evalA gens f
  | .pow a k => a.evalA gens f ^ k

theorem Wd.evalA_mem {X : Subgroup (MulAut A)} {gens : Nat → MulAut A} (hg : ∀ i, gens i ∈ X)
    {f : MulAut A} (hf : f ∈ X) : ∀ ω : Wd, ω.evalA gens f ∈ X
  | .gen i => hg i
  | .var => hf
  | .mul a c => X.mul_mem (Wd.evalA_mem hg hf a) (Wd.evalA_mem hg hf c)
  | .pow a k => X.pow_mem (Wd.evalA_mem hg hf a) k

section Words

variable {b : Fin 5 → A} (hsq : ∀ a : A, a * a = 1)
  (hgen : Subgroup.closure (Set.range b) = ⊤) (hcard : Nat.card A = 32)
  {guv gt gu gρ : MulAut A} (huv : code b guv = uvC) (ht : code b gt = tC) (hu : code b gu = uC)
  (hρ : code b gρ = rhoC)

include hsq hgen hcard huv ht hu hρ in
theorem code_agen (i : Nat) : code b (agen guv gt gu gρ i) = genC i := by
  unfold agen genC
  split_ifs
  · exact huv
  · exact ht
  · exact hu
  · exact hρ
  · exact code_one hsq hgen hcard

include hsq hgen hcard huv ht hu hρ in
theorem code_evalA (f : MulAut A) :
    ∀ ω : Wd, code b (ω.evalA (agen guv gt gu gρ) f) = ω.evalC (code b f)
  | .gen i => code_agen hsq hgen hcard huv ht hu hρ i
  | .var => rfl
  | .mul a c => by
    rw [Wd.evalA, code_mul hsq hgen hcard, code_evalA f a, code_evalA f c]; rfl
  | .pow a k => by rw [Wd.evalA, code_pow hsq hgen hcard, code_evalA f a]; rfl

end Words

section Main

variable {b : Fin 5 → A} (hsq : ∀ a : A, a * a = 1)
  (hgen : Subgroup.closure (Set.range b) = ⊤) (hcard : Nat.card A = 32)
  {guv gt gu gρ : MulAut A} (huv : code b guv = uvC) (ht : code b gt = tC)

include hsq hgen hcard huv ht in
theorem pow_sixtyFour_eq_one (f : MulAut A) (hfuv : f * guv = guv * f) (hft : f * gt = gt * f) :
    f ^ 64 = 1 := by
  have h := Certificates.certificate778710
  have e1 : mulC (code b f) uvC = mulC uvC (code b f) := by
    rw [← huv, ← code_mul hsq hgen hcard, ← code_mul hsq hgen hcard, hfuv]
  have e2 : mulC (code b f) tC = mulC tC (code b f) := by
    rw [← ht, ← code_mul hsq hgen hcard, ← code_mul hsq hgen hcard, hft]
  have := h.1 _ (code_lt hsq hgen f) (nonsing_code hsq hgen hcard f) e1 e2
  refine code_inj hsq hgen ?_
  rw [code_pow hsq hgen hcard, this, code_one hsq hgen hcard]

include hsq hgen hcard huv ht in
theorem code_mem_vCodes {v : MulAut A} (hv : v = 1 ∨ v = guv ∨ v = gt ∨ v = guv * gt) :
    code b v ∈ vCodes := by
  rcases hv with rfl | rfl | rfl | rfl
  · rw [code_one hsq hgen hcard]; simp [vCodes]
  · rw [huv]; simp [vCodes]
  · rw [ht]; simp [vCodes]
  · rw [code_mul hsq hgen hcard, huv, ht]
    have : mulC uvC tC = 19209281 := by decide
    rw [this]; simp [vCodes]

include hsq hgen hcard huv ht in
theorem eq_of_code_mem_vCodes {v : MulAut A} (hv : code b v ∈ vCodes) :
    v = 1 ∨ v = guv ∨ v = gt ∨ v = guv * gt := by
  have h4 : code b (guv * gt) = 19209281 := by
    rw [code_mul hsq hgen hcard, huv, ht]; decide
  simp only [vCodes, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h
  · exact Or.inl (code_inj hsq hgen (h.trans (code_one hsq hgen hcard).symm))
  · exact Or.inr (Or.inl (code_inj hsq hgen (h.trans huv.symm)))
  · exact Or.inr (Or.inr (Or.inl (code_inj hsq hgen (h.trans ht.symm))))
  · exact Or.inr (Or.inr (Or.inr (code_inj hsq hgen (h.trans h4.symm))))

include hsq hgen hcard huv ht in
theorem exists_mul_eq_of_normV (d : MulAut A) (hd : normV (code b d) = true) :
    ∀ v ∈ [guv, gt], ∃ v' : MulAut A, (v' = 1 ∨ v' = guv ∨ v' = gt ∨ v' = guv * gt) ∧
      d * v = v' * d := by
  unfold normV at hd
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at hd
  intro v hv
  have hcv : code b v ∈ [uvC, tC] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    rcases hv with rfl | rfl
    · exact Or.inl huv
    · exact Or.inr ht
  obtain ⟨c', hc'V, hc'⟩ := hd _ hcv
  have hc'' := hc'V
  simp only [vCodes, List.mem_cons, List.not_mem_nil, or_false] at hc''
  obtain ⟨v', hv'⟩ : ∃ v' : MulAut A, (v' = 1 ∨ v' = guv ∨ v' = gt ∨ v' = guv * gt) ∧
      code b v' = c' := by
    rcases hc'' with rfl | rfl | rfl | rfl
    · exact ⟨1, Or.inl rfl, code_one hsq hgen hcard⟩
    · exact ⟨guv, Or.inr (Or.inl rfl), huv⟩
    · exact ⟨gt, Or.inr (Or.inr (Or.inl rfl)), ht⟩
    · exact ⟨guv * gt, Or.inr (Or.inr (Or.inr rfl)), by
        rw [code_mul hsq hgen hcard, huv, ht]; decide⟩
  refine ⟨v', hv'.1, code_inj hsq hgen ?_⟩
  rw [code_mul hsq hgen hcard, code_mul hsq hgen hcard, hv'.2]
  exact hc'

variable (hu : code b gu = uC)

include hsq hgen hcard huv ht hu in
theorem normalizes_V (f : MulAut A) (hfuv : f * guv = guv * f)
    (hD : ∀ d ∈ [guv, gt, gu], ∃ d' : MulAut A, code b d' ∈ dCodes ∧ f * d = d' * f) :
    ∀ v ∈ [guv, gt], ∃ v' : MulAut A, (v' = 1 ∨ v' = guv ∨ v' = gt ∨ v' = guv * gt) ∧
      f * v = v' * f := by
  have h := Certificates.certificate778710
  have e1 : mulC (code b f) uvC = mulC uvC (code b f) := by
    rw [← huv, ← code_mul hsq hgen hcard, ← code_mul hsq hgen hcard, hfuv]
  have hnD : normD (code b f) = true := by
    unfold normD
    simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq]
    intro d hd
    have hd' : ∃ d0 ∈ [guv, gt, gu], code b d0 = d := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact ⟨guv, by simp, huv⟩
      · exact ⟨gt, by simp, ht⟩
      · exact ⟨gu, by simp, hu⟩
    obtain ⟨d0, hd0, rfl⟩ := hd'
    obtain ⟨d', hd'D, hfd⟩ := hD d0 hd0
    refine ⟨code b d', hd'D, ?_⟩
    rw [← code_mul hsq hgen hcard, ← code_mul hsq hgen hcard, hfd]
  exact exists_mul_eq_of_normV hsq hgen hcard huv ht f
    (h.2.1 _ (code_lt hsq hgen f) (nonsing_code hsq hgen hcard f) e1 hnD)

variable (hρ : code b gρ = rhoC)

include hsq hgen hcard huv ht hu hρ in
theorem coord_lt_sixteen (X : Subgroup (MulAut A)) (hXuv : guv ∈ X) (hXt : gt ∈ X) (hXu : gu ∈ X)
    (hXρ : gρ ∈ X)
    (hC : ∀ h ∈ X, h * guv = guv * h → h * gt = gt * h →
      h = 1 ∨ h = guv ∨ h = gt ∨ h = guv * gt)
    {f : MulAut A} (hf : f ∈ X) {a : A} (ha : coord b a < 16) : coord b (f a) < 16 := by
  have hcert := Certificates.certificate778710
  by_cases hst : stabW4 (code b f) = true
  · exact coord_apply_lt_sixteen hsq hgen hcard f hst a ha
  · exfalso
    rw [Bool.not_eq_true] at hst
    obtain ⟨ω, hω⟩ := hcert.2.2 _ (code_lt hsq hgen f) (nonsing_code hsq hgen hcard f) hst
    set g := ω.evalA (agen guv gt gu gρ) f
    have hgX : g ∈ X := Wd.evalA_mem (fun i => by
      unfold agen; split_ifs
      · exact hXuv
      · exact hXt
      · exact hXu
      · exact hXρ
      · exact X.one_mem) hf ω
    have hcg : code b g = ω.evalC (code b f) := code_evalA hsq hgen hcard huv ht hu hρ f ω
    rw [← hcg] at hω
    unfold good at hω
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hω
    obtain ⟨⟨h1, h2⟩, h3⟩ := hω
    have c1 : g * guv = guv * g := code_inj hsq hgen (by
      rw [code_mul hsq hgen hcard, code_mul hsq hgen hcard, huv]; exact h1)
    have c2 : g * gt = gt * g := code_inj hsq hgen (by
      rw [code_mul hsq hgen hcard, code_mul hsq hgen hcard, ht]; exact h2)
    exact h3 (code_mem_vCodes hsq hgen hcard huv ht (hC g hgX c1 c2))

end Main

end CFSG.CGT.Stroth77.GL5
