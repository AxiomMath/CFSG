module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime]

section RelativeCentralizer

variable {P : Type*} [Group P] [Finite P]

omit [Finite P] in
theorem comm_of_forall_eq_zpow_mul {A B : Subgroup P} {b : P}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hbcen : b ∈ centralizer (A : Set P))
    (hform : ∀ x ∈ B, ∃ k : ℤ, ∃ a ∈ A, x = b ^ k * a) : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  have hbA : ∀ a ∈ A, ∀ k : ℤ, a * b ^ k = b ^ k * a := fun a ha k =>
    mem_centralizer_iff.1 (zpow_mem hbcen k) a ha
  intro x hx y hy
  obtain ⟨k, a, ha, rfl⟩ := hform x hx
  obtain ⟨l, a', ha', rfl⟩ := hform y hy
  calc b ^ k * a * (b ^ l * a') = b ^ k * (a * b ^ l) * a' := by group
    _ = b ^ k * (b ^ l * a) * a' := by rw [hbA a ha l]
    _ = (b ^ k * b ^ l) * (a * a') := by group
    _ = (b ^ l * b ^ k) * (a' * a) := by
        rw [((Commute.refl b).zpow_zpow k l).eq, hA a ha a' ha']
    _ = b ^ l * (b ^ k * a') * a := by group
    _ = b ^ l * (a' * b ^ k) * a := by rw [hbA a' ha' k]
    _ = b ^ l * a' * (b ^ k * a) := by group

theorem relative_abelian_centralizer (hP : IsPGroup p P) {N A : Subgroup P} [N.Normal]
    [A.Normal] (hAN : A ≤ N) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hmax : ∀ B : Subgroup P, B.Normal → B ≤ N → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      A ≤ B → B = A) :
    N ⊓ centralizer (A : Set P) = A := by
  set C := N ⊓ centralizer (A : Set P) with hCdef
  have hAC : A ≤ C := le_inf hAN fun x hx => mem_centralizer_iff.2 fun y hy => hA y hy x hx
  by_contra hne
  have hlt : A < C := lt_of_le_of_ne hAC (Ne.symm hne)
  obtain ⟨b, hbC, -, -, B, hBn, hAB, hBC, -, hform, -⟩ := exists_central_extension hP hlt
  have hBab := comm_of_forall_eq_zpow_mul hA (mem_inf.1 hbC).2 hform
  exact hAB.ne (hmax B hBn (hBC.trans inf_le_left) hBab hAB.le).symm

theorem maximal_abelian_normal_self_centralizing (hP : IsPGroup p P) {H : Subgroup P}
    [H.Normal] (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hmax : ∀ B : Subgroup P, B.Normal → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → H ≤ B → B = H) :
    centralizer (H : Set P) = H := by
  have h := relative_abelian_centralizer hP (N := ⊤) le_top hH
    (fun B hB _ hBc hHB => hmax B hB hBc hHB)
  rwa [top_inf_eq] at h

end RelativeCentralizer

section OddAbelian

theorem odd_abelian_order_p_endomorphism {B : Type*} [AddCommGroup B] (hp2 : p ≠ 2)
    (hB : ∀ b : B, ∃ k : ℕ, p ^ k • b = 0) (f : AddMonoid.End B) (hf : f ^ p = 1)
    (hfix : ∀ b : B, p • b = 0 → f b = b) : ∀ b : B, p • (f b - b) = 0 := by
  have hp3 : 3 ≤ p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
  set δ : AddMonoid.End B := f - 1 with hδdef
  have hδ : ∀ b : B, δ b = f b - b := fun b => rfl
  have hmono : ∀ {i j : ℕ} {x : B}, i ≤ j → p ^ i • x = 0 → p ^ j • x = 0 := by
    intro i j x hij hx
    rw [← Nat.sub_add_cancel hij, pow_add, mul_smul, hx, smul_zero]
  have hlow : ∀ i : ℕ, ∀ b : B, p ^ (i + 1) • b = 0 → p ^ i • δ b = 0 := by
    intro i b hb
    have h1 : p • (p ^ i • b) = 0 := by rw [smul_smul, ← pow_succ']; exact hb
    rw [← map_nsmul, hδ, hfix _ h1, sub_self]
  have hiter : ∀ s : ℕ, ∀ b : B, p ^ s • δ b = 0 →
      ∀ k : ℕ, p ^ (s - k) • (δ ^ (k + 1)) b = 0 := by
    intro s b hb k
    induction k with
    | zero => simpa using hb
    | succ k ih =>
      rw [pow_succ']
      change p ^ (s - (k + 1)) • δ ((δ ^ (k + 1)) b) = 0
      rcases Nat.lt_or_ge k s with hks | hks
      · have e : s - k = (s - (k + 1)) + 1 := by omega
        rw [e] at ih
        exact hlow _ _ ih
      · have e : s - k = 0 := by omega
        rw [e, pow_zero, one_smul] at ih
        rw [ih, map_zero, smul_zero]
  have hexp : (δ + 1) ^ p = 1 := by rw [hδdef, sub_add_cancel, hf]
  have hterm : ∀ (b : B) (m : ℕ), (δ ^ m * 1 ^ (p - m) * (p.choose m : AddMonoid.End B)) b =
      p.choose m • (δ ^ m) b := by
    intro b m
    rw [one_pow, mul_one]
    change (δ ^ m) ((p.choose m : AddMonoid.End B) b) = _
    rw [AddMonoid.End.natCast_apply, map_nsmul]
  have hsumapp : ∀ (s : Finset ℕ) (g : ℕ → AddMonoid.End B) (b : B),
      (∑ m ∈ s, g m) b = ∑ m ∈ s, g m b := by
    intro s g b
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
  have hkey : ∀ s : ℕ, ∀ b : B, p ^ (s + 2) • δ b = 0 → p ^ (s + 1) • δ b = 0 := by
    intro s b hb
    have hsum := congrArg (fun g : AddMonoid.End B => p ^ s • g b) hexp
    rw [(Commute.one_right δ).add_pow, hsumapp, Finset.smul_sum, Finset.sum_range_succ'] at hsum
    simp only [hterm] at hsum
    simp only [Nat.choose_zero_right, one_smul, pow_zero] at hsum
    change _ + p ^ s • b = p ^ s • b at hsum
    rw [add_eq_right, Finset.sum_eq_single 0] at hsum
    · rw [zero_add, Nat.choose_one_right, pow_one, smul_comm, ← mul_smul, ← pow_succ'] at hsum
      exact hsum
    · intro m hm hm0
      rw [Finset.mem_range] at hm
      have hit := hiter (s + 2) b hb m
      rcases Nat.lt_or_ge (m + 1) p with hlt | hge
      · obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (k := m + 1) (by omega) hlt
        rw [hc, smul_comm, mul_comm, mul_smul, smul_smul p (p ^ s), ← pow_succ',
          hmono (i := s + 2 - m) (j := s + 1) (by omega) hit, smul_zero]
      · have hmp : m + 1 = p := by omega
        have hm2 : s + 2 - m ≤ s := by omega
        rw [hmp, Nat.choose_self, one_smul]
        rw [hmp] at hit
        exact hmono hm2 hit
    · intro h
      simp at h
      omega
  intro b
  obtain ⟨e, he⟩ := hB (δ b)
  have hdesc : ∀ e : ℕ, p ^ (e + 1) • δ b = 0 → p • δ b = 0 := by
    intro e
    induction e with
    | zero => simp
    | succ e ih => intro h; exact ih (hkey e b h)
  rw [← hδ]
  exact hdesc e (hmono (i := e) (j := e + 1) (by omega) he)

theorem odd_abelian_order_p_automorphism {A : Type*} [CommGroup A] (hp2 : p ≠ 2)
    (hA : IsPGroup p A) (α : MulAut A) (hα : α ^ p = 1) (hfix : ∀ a : A, a ^ p = 1 → α a = a) :
    ∀ a : A, (a⁻¹ * α a) ^ p = 1 := by
  let f : AddMonoid.End (Additive A) := α.toMonoidHom.toAdditive
  have hfn : ∀ n : ℕ, ∀ x : Additive A, (f ^ n) x = Additive.ofMul ((α ^ n) x.toMul) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ]
      change (f ^ n) (f x) = _
      rw [ih]
      rfl
  have hfp : f ^ p = 1 := by
    ext x
    rw [hfn, hα]
    rfl
  have h := odd_abelian_order_p_endomorphism hp2 (fun x => by
      obtain ⟨k, hk⟩ := hA x.toMul
      exact ⟨k, by rw [← ofMul_toMul x, ← ofMul_pow, hk, ofMul_one]⟩) f hfp
    (fun x hx => by
      have hx' : x.toMul ^ p = 1 := by rw [← toMul_nsmul, hx, toMul_zero]
      change Additive.ofMul (α x.toMul) = x
      rw [hfix _ hx', ofMul_toMul])
  intro a
  have ha := h (Additive.ofMul a)
  rw [← toMul_eq_one, toMul_nsmul, toMul_sub] at ha
  change (α a / a) ^ p = 1 at ha
  rwa [div_eq_mul_inv, mul_comm] at ha

end OddAbelian

section SectionAutomorphisms

variable {A : Type*} [CommGroup A]

@[expose] def sectionAutomorphisms (E : Subgroup A) : Subgroup (MulAut A) where
  carrier := {α | (∀ e ∈ E, α e = e) ∧ ∀ a : A, a⁻¹ * α a ∈ E}
  mul_mem' := by
    rintro α β ⟨hα1, hα2⟩ ⟨hβ1, hβ2⟩
    refine ⟨fun e he => by rw [MulAut.mul_apply, hβ1 e he, hα1 e he], fun a => ?_⟩
    rw [MulAut.mul_apply]
    have e : a⁻¹ * α (β a) = (a⁻¹ * β a) * ((β a)⁻¹ * α (β a)) := by group
    rw [e]
    exact mul_mem (hβ2 a) (hα2 (β a))
  one_mem' := ⟨fun e _ => rfl, fun a => by rw [MulAut.one_apply, inv_mul_cancel]; exact one_mem E⟩
  inv_mem' := by
    rintro α ⟨hα1, hα2⟩
    refine ⟨fun e he => ?_, fun a => ?_⟩
    · conv_lhs => rw [← hα1 e he]
      exact MulAut.inv_apply_self A α e
    · have h := inv_mem (hα2 (α⁻¹ a))
      rw [MulAut.apply_inv_self] at h
      simpa using h

theorem mem_sectionAutomorphisms {E : Subgroup A} {α : MulAut A} :
    α ∈ sectionAutomorphisms E ↔ (∀ e ∈ E, α e = e) ∧ ∀ a : A, a⁻¹ * α a ∈ E :=
  Iff.rfl

theorem sectionAutomorphisms_comm (E : Subgroup A) {α β : MulAut A}
    (hα : α ∈ sectionAutomorphisms E) (hβ : β ∈ sectionAutomorphisms E) : α * β = β * α := by
  ext a
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have hαa : α (β a) = α a * (a⁻¹ * β a) := by
    rw [show β a = a * (a⁻¹ * β a) by group, map_mul, hα.1 _ (hβ.2 a)]
    group
  have hβa : β (α a) = β a * (a⁻¹ * α a) := by
    rw [show α a = a * (a⁻¹ * α a) by group, map_mul, hβ.1 _ (hα.2 a)]
    group
  rw [hαa, hβa, mul_left_comm, mul_left_comm (β a), mul_comm (α a)]

end SectionAutomorphisms

section TorsionGenerated

variable {X : Type*} [Group X]

theorem odd_torsion_generated_exponent (hp2 : p ≠ 2) (A : Subgroup X) [A.Normal]
    (_hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hXA : commutator X ≤ A) (E : Subgroup X)
    (hE : ∀ a : X, a ∈ E ↔ a ∈ A ∧ a ^ p = 1) (hEZ : E ≤ center X)
    (hAE : ⁅A, (⊤ : Subgroup X)⁆ ≤ E) (hgen : closure {x : X | x ^ p = 1} = ⊤) :
    commutator X ≤ E ∧ ∀ x : X, x ^ p = 1 := by
  have hcomA : ∀ x y : X, ⁅x, y⁆ ∈ A := fun x y =>
    hXA (commutator_mem_commutator (mem_top x) (mem_top y))
  have hcentral : ∀ e ∈ E, ∀ g : X, Commute g e := fun e he g => mem_center_iff.1 (hEZ he) g
  have hEpow : ∀ e ∈ E, e ^ p = 1 := fun e he => ((hE e).1 he).2
  have hstep1 : ∀ x : X, x ^ p = 1 → ∀ y : X, ⁅x, y⁆ ∈ E := by
    intro x hx y
    have hcA : ⁅x, y⁆ ∈ A := hcomA x y
    have heE : ⁅x, ⁅x, y⁆⁆ ∈ E := by
      rw [← commutatorElement_inv]
      exact hAE (inv_mem (commutator_mem_commutator hcA (mem_top x)))
    set c := ⁅x, y⁆ with hcdef
    set e := ⁅x, c⁆ with hedef
    have hxc : x * c * x⁻¹ = e * c := by rw [hedef, commutatorElement_def]; group
    have hec : Commute e c := (hcentral e heE c).symm
    have hconj : ∀ m : ℕ, ⁅x ^ m, y⁆ = c ^ m * e ^ m.choose 2 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h1 : ⁅x ^ (m + 1), y⁆ = x * ⁅x ^ m, y⁆ * x⁻¹ * ⁅x, y⁆ := by
          simp only [commutatorElement_def]; group
        have h2 : x * c ^ m * x⁻¹ = (e * c) ^ m := by rw [← hxc, conj_pow]
        have h3 : x * e ^ m.choose 2 * x⁻¹ = e ^ m.choose 2 := by
          rw [((hcentral e heE x).pow_right _).eq, mul_inv_cancel_right]
        have hz1 : e ^ m * c ^ m = c ^ m * e ^ m := ((hcentral _ (pow_mem heE m) (c ^ m)).eq).symm
        have hz2 : (e ^ m * e ^ m.choose 2) * c = c * (e ^ m * e ^ m.choose 2) :=
          ((hcentral _ (mul_mem (pow_mem heE m) (pow_mem heE _)) c).eq).symm
        have hch : (m + 1).choose 2 = m + m.choose 2 := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
        rw [h1, ih, hch, pow_add e m]
        calc x * (c ^ m * e ^ m.choose 2) * x⁻¹ * ⁅x, y⁆
            = (x * c ^ m * x⁻¹) * (x * e ^ m.choose 2 * x⁻¹) * c := by rw [← hcdef]; group
          _ = e ^ m * c ^ m * e ^ m.choose 2 * c := by rw [h2, h3, hec.mul_pow]
          _ = c ^ m * e ^ m * e ^ m.choose 2 * c := by rw [hz1]
          _ = c ^ m * ((e ^ m * e ^ m.choose 2) * c) := by group
          _ = c ^ m * (c * (e ^ m * e ^ m.choose 2)) := by rw [hz2]
          _ = c ^ (m + 1) * (e ^ m * e ^ m.choose 2) := by group
    have hpc := hconj p
    rw [hx, commutatorElement_one_left] at hpc
    obtain ⟨k, hk⟩ := dvd_choose_two_of_ne_two hp.out hp2
    rw [hk, pow_mul, hEpow e heE, one_pow, mul_one] at hpc
    exact (hE c).2 ⟨hcA, hpc.symm⟩
  let S : Subgroup X :=
    { carrier := {x | ∀ y : X, ⁅x, y⁆ ∈ E}
      mul_mem' := fun {x z} hx hz y => by
        have e : ⁅x * z, y⁆ = x * ⁅z, y⁆ * x⁻¹ * ⁅x, y⁆ := by
          simp only [commutatorElement_def]; group
        rw [e, ((hcentral _ (hz y) x).eq), mul_inv_cancel_right]
        exact mul_mem (hz y) (hx y)
      one_mem' := fun y => by rw [commutatorElement_one_left]; exact one_mem E
      inv_mem' := fun {x} hx y => by
        rw [commutatorElement_inv_left, ← commutatorElement_inv]
        have h := inv_mem (hx y)
        rw [((hcentral _ h x⁻¹).eq), inv_mul_cancel_right]
        exact h }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hgen, closure_le]
    intro x hx
    exact hstep1 x hx
  have hall : ∀ x y : X, ⁅x, y⁆ ∈ E := fun x y => by
    have : x ∈ S := hS ▸ mem_top x
    exact this y
  refine ⟨?_, ?_⟩
  · rw [_root_.commutator_def, commutator_le]
    exact fun x _ y _ => hall x y
  let T : Subgroup X :=
    { carrier := {x | x ^ p = 1}
      mul_mem' := fun {x y} hx hy => by
        change (x * y) ^ p = 1
        rw [mul_pow_prime_eq_of_commute hp.out hp2 (hcentral _ (hall y x) x)
          (hcentral _ (hall y x) y) (hEpow _ (hall y x))]
        rw [hx, hy, one_mul]
      one_mem' := one_pow p
      inv_mem' := fun {x} hx => by
        change x⁻¹ ^ p = 1
        rw [inv_pow, hx, inv_one] }
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hgen, closure_le]
    exact fun x hx => hx
  intro x
  have : x ∈ T := hT ▸ mem_top x
  exact this

end TorsionGenerated

end CFSG.SectionRank.Ccomm
