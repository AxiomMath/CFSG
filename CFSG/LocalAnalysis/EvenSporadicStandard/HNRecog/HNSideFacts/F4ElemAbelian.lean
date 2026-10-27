module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

private def sp {Γ : Type*} [Group Γ] (e : ℕ → Γ) (a n : ℕ) : Γ :=
  (List.range n).foldl (fun acc i => if a.testBit i then acc * e i else acc) 1

private lemma sp_zero {Γ : Type*} [Group Γ] (e : ℕ → Γ) (a : ℕ) : sp e a 0 = 1 := by
  simp [sp]

private lemma sp_succ {Γ : Type*} [Group Γ] (e : ℕ → Γ) (a n : ℕ) :
    sp e a (n + 1) = sp e a n * (if a.testBit n then e n else 1) := by
  unfold sp
  rw [Nat.add_one, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases h : a.testBit n <;> simp [h]

private lemma foldl_mem {Γ : Type*} [Group Γ] (H : Subgroup Γ) (f : ℕ → Γ) :
    ∀ (l : List ℕ), (∀ i ∈ l, f i ∈ H) → ∀ (a : ℕ) (acc : Γ), acc ∈ H →
      l.foldl (fun acc i => if a.testBit i then acc * f i else acc) acc ∈ H := by
  intro l
  induction l with
  | nil => intro _ a acc hacc; simpa using hacc
  | cons i l ih =>
      intro hf a acc hacc
      rw [List.foldl_cons]
      exact ih (fun j hj => hf j (List.mem_cons_of_mem i hj)) a
        (if a.testBit i then acc * f i else acc) (by
          cases h : a.testBit i
          · exact hacc
          · exact H.mul_mem hacc (hf i List.mem_cons_self))

private lemma map_foldl {Γ A : Type*} [Group Γ] [Group A] (θ : Γ →* A) (e : ℕ → Γ) (a : ℕ) :
    ∀ (l : List ℕ) (acc : Γ),
      θ (l.foldl (fun acc i => if a.testBit i then acc * e i else acc) acc) =
        l.foldl (fun acc i => if a.testBit i then acc * θ (e i) else acc) (θ acc) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons i l ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons]
      by_cases h : a.testBit i
      · simp only [h, if_true]
        rw [ih (acc * e i), map_mul]
      · simp only [h, if_false]
        exact ih acc

private lemma map_sp {Γ A : Type*} [Group Γ] [Group A] (θ : Γ →* A) (e : ℕ → Γ) (a n : ℕ) :
    θ (sp e a n) = sp (fun i => θ (e i)) a n := by
  unfold sp
  rw [map_foldl θ e a (List.range n) 1, map_one]

private lemma sp_eq_one_of_bits_false {Γ : Type*} [Group Γ] (e : ℕ → Γ) (a : ℕ) :
    ∀ n, (∀ j < n, a.testBit j = false) → sp e a n = 1 := by
  intro n
  induction n with
  | zero => intro _; exact sp_zero e a
  | succ n ih =>
      intro h
      rw [sp_succ, h n (Nat.lt_succ_self n)]
      simpa only [Bool.false_eq_true, if_false, mul_one] using
        ih fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n))

private lemma commute_sp {Γ : Type*} [Group Γ] (e : ℕ → Γ)
    (hc : ∀ i < 5, ∀ j < 5, Commute (e i) (e j)) :
    ∀ n a i, n ≤ i → i < 5 → Commute (e i) (sp e a n) := by
  intro n
  induction n with
  | zero => intro a i _ _; rw [sp_zero]; exact Commute.one_right _
  | succ n ih =>
      intro a i hni hi
      rw [sp_succ]
      refine Commute.mul_right (ih a i (Nat.le_of_succ_le hni) hi) ?_
      cases h : a.testBit n
      · simpa using Commute.one_right (e i)
      · simpa using hc i hi n (by omega)

private lemma rearrange {G : Type*} [Group G] (A B ca cb c : G)
    (h1 : Commute ca B) (h2 : ca * cb = c) :
    (A * ca) * (B * cb) = (A * B) * c := by
  calc (A * ca) * (B * cb)
      = A * (ca * (B * cb)) := by rw [mul_assoc]
    _ = A * ((ca * B) * cb) := by rw [← mul_assoc ca B cb]
    _ = A * ((B * ca) * cb) := by rw [h1.eq]
    _ = A * (B * (ca * cb)) := by rw [mul_assoc B ca cb]
    _ = A * (B * c) := by rw [h2]
    _ = (A * B) * c := by rw [← mul_assoc]

private lemma sp_mul {Γ : Type*} [Group Γ] (e : ℕ → Γ)
    (hc : ∀ i < 5, ∀ j < 5, Commute (e i) (e j))
    (hs : ∀ i < 5, e i * e i = 1) :
    ∀ n ≤ 5, ∀ a b, sp e a n * sp e b n = sp e (a ^^^ b) n := by
  intro n
  induction n with
  | zero => intro _ a b; rw [sp_zero, sp_zero, sp_zero, one_mul]
  | succ n ih =>
      intro hn a b
      have hn5 : n < 5 := by omega
      have hnle : n ≤ 5 := le_of_lt hn5
      rw [sp_succ, sp_succ, sp_succ]
      have h1 : Commute (if a.testBit n then e n else 1) (sp e b n) := by
        cases h : a.testBit n
        · simpa using Commute.one_left (sp e b n)
        · simpa using commute_sp e hc n b n le_rfl hn5
      have h2 : (if a.testBit n then e n else 1) * (if b.testBit n then e n else 1)
          = (if (a ^^^ b).testBit n then e n else 1) := by
        cases ha : a.testBit n <;> cases hb : b.testBit n <;>
          simp [ha, hb, Nat.testBit_xor, hs n hn5]
      have hrearr := rearrange (sp e a n) (sp e b n)
        (if a.testBit n then e n else 1) (if b.testBit n then e n else 1)
        (if (a ^^^ b).testBit n then e n else 1) h1 h2
      rw [hrearr, ih hnle a b]

private lemma sp_two_pow {Γ : Type*} [Group Γ] (e : ℕ → Γ) :
    ∀ i n, i < n → sp e (2 ^ i) n = e i := by
  intro i n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro h
      rw [sp_succ]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hlt | heq
      · have hbit : (2 ^ i).testBit n = false := by
          rw [Nat.testBit_two_pow, decide_eq_false_iff_not]
          omega
        rw [hbit]
        simpa only [Bool.false_eq_true, if_false, mul_one] using ih hlt
      · rw [heq]
        have hbit : (2 ^ n).testBit n = true := by
          rw [Nat.testBit_two_pow]; simp
        have hzero : sp e (2 ^ n) n = 1 :=
          sp_eq_one_of_bits_false e (2 ^ n) n (by
            intro j hj
            rw [Nat.testBit_two_pow, decide_eq_false_iff_not]
            omega)
        rw [hbit, hzero]
        simp

private lemma two_pow_lt_thirtyTwo {i : ℕ} (hi : i < 5) : 2 ^ i < 32 := by
  interval_cases i <;> norm_num

private lemma xor_lt_thirtyTwo {a b : ℕ} (ha : a < 32) (hb : b < 32) : a ^^^ b < 32 := by
  have h : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [← h] at ha hb ⊢
  exact Nat.xor_lt_two_pow ha hb

private lemma isMulCommutative_of_mulEquiv {M N : Type*} [Mul M] [Mul N] (f : M ≃* N)
    [IsMulCommutative M] : IsMulCommutative N := by
  rw [isMulCommutative_iff]
  intro x y
  calc x * y = f (f.symm x * f.symm y) := by
        rw [map_mul, f.apply_symm_apply, f.apply_symm_apply]
    _ = f (f.symm y * f.symm x) := by rw [mul_comm' (f.symm x) (f.symm y)]
    _ = y * x := by rw [map_mul, f.apply_symm_apply, f.apply_symm_apply]

theorem exists_isElemAbelian_card_thirtyTwo {Γ Γ' A : Type*} [Group Γ] [Group Γ'] [Group A]
    (θ : Γ →* A) (hθ : Function.Injective θ) (ι : Γ →* Γ') (hι : Function.Injective ι)
    (e : ℕ → Γ) (hcomm : ∀ i < 5, ∀ j < 5, θ (e i) * θ (e j) = θ (e j) * θ (e i))
    (hsq : ∀ i < 5, θ (e i) * θ (e i) = 1)
    (hdist : ∀ a < 32, ∀ b < 32,
      (List.range 5).foldl (fun acc i => if a.testBit i then acc * θ (e i) else acc) 1 =
        (List.range 5).foldl (fun acc i => if b.testBit i then acc * θ (e i) else acc) 1 →
        a = b) :
    ∃ E : Subgroup Γ', CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32 ∧
      E = Subgroup.closure (ι ∘ e '' {i | i < 5}) := by
  have hcΓ : ∀ i < 5, ∀ j < 5, Commute (e i) (e j) := by
    intro i hi j hj
    apply hθ
    rw [map_mul, map_mul]
    exact hcomm i hi j hj
  have hsqΓ : ∀ i < 5, e i * e i = 1 := by
    intro i hi
    apply hθ
    rw [map_mul, hsq i hi, map_one]
  let E₀ : Subgroup Γ := Subgroup.closure (e '' {i | i < 5})
  let E : Subgroup Γ' := Subgroup.closure (ι ∘ e '' {i | i < 5})
  have hE : E = E₀.map ι := by
    change Subgroup.closure (ι ∘ e '' {i | i < 5})
      = (Subgroup.closure (e '' {i | i < 5})).map ι
    rw [MonoidHom.map_closure, Set.image_comp]
  have hcommE₀ : IsMulCommutative E₀ := by
    change IsMulCommutative (Subgroup.closure (e '' {i | i < 5}))
    apply Subgroup.isMulCommutative_closure
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ -
    exact hcΓ i hi j hj
  have hsqE₀ : ∀ x ∈ E₀, x ^ 2 = 1 := by
    intro x hx
    change x ∈ Subgroup.closure (e '' {i | i < 5}) at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        rw [pow_two]
        exact hsqΓ i hi
    | one => exact one_pow 2
    | mul y z hy hz ihy ihz =>
        have hcommyz : Commute y z := by
          have h := hcommE₀.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩
          exact congrArg Subtype.val h
        rw [Commute.mul_pow hcommyz 2, ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  have hgenE₀ : ∀ i ∈ List.range 5, e i ∈ E₀ := by
    intro i hi
    change e i ∈ Subgroup.closure (e '' {i | i < 5})
    exact Subgroup.subset_closure ⟨i, List.mem_range.mp hi, rfl⟩
  have hspE₀ : ∀ a : ℕ, sp e a 5 ∈ E₀ := by
    intro a
    change sp e a 5 ∈ Subgroup.closure (e '' {i | i < 5})
    exact foldl_mem (Subgroup.closure (e '' {i | i < 5})) e (List.range 5) hgenE₀ a 1
      (Subgroup.one_mem _)
  have hmem : ∀ x ∈ E₀, ∃ a < 32, x = sp e a 5 := by
    intro x hx
    change x ∈ Subgroup.closure (e '' {i | i < 5}) at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        exact ⟨2 ^ i, two_pow_lt_thirtyTwo hi, (sp_two_pow e i 5 hi).symm⟩
    | one =>
        exact ⟨0, by norm_num, (sp_eq_one_of_bits_false e 0 5 (by intro j _; simp)).symm⟩
    | mul y z hy hz ihy ihz =>
        obtain ⟨a, ha, rfl⟩ := ihy
        obtain ⟨b, hb, rfl⟩ := ihz
        exact ⟨a ^^^ b, xor_lt_thirtyTwo ha hb, sp_mul e hcΓ hsqΓ 5 le_rfl a b⟩
    | inv y hy ihy =>
        obtain ⟨a, ha, rfl⟩ := ihy
        refine ⟨a, ha, ?_⟩
        have hxx : sp e a 5 * sp e a 5 = 1 := by
          have h := sp_mul e hcΓ hsqΓ 5 le_rfl a a
          rw [Nat.xor_self, sp_eq_one_of_bits_false e 0 5 (by intro j _; simp)] at h
          exact h
        exact inv_eq_of_mul_eq_one_right hxx
  let ψ : Fin 32 → E₀ := fun a => ⟨sp e a.val 5, hspE₀ a.val⟩
  have hinj : Function.Injective ψ := by
    intro a b hab
    have hval : sp e a.val 5 = sp e b.val 5 := congrArg Subtype.val hab
    have hθ : sp (fun i => θ (e i)) a.val 5 = sp (fun i => θ (e i)) b.val 5 := by
      have h := congrArg θ hval
      rwa [map_sp θ e a.val 5, map_sp θ e b.val 5] at h
    exact Fin.ext (hdist a.val a.isLt b.val b.isLt hθ)
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨a, ha, hya⟩ := hmem y.val y.property
    exact ⟨⟨a, ha⟩, Subtype.ext hya.symm⟩
  have hcardE₀ : Nat.card E₀ = 32 := by
    have h := Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)
    rw [Nat.card_fin] at h
    exact h.symm
  have hcommE : IsMulCommutative E := by
    rw [hE]
    haveI := hcommE₀
    exact isMulCommutative_of_mulEquiv (Subgroup.equivMapOfInjective E₀ ι hι)
  have hsqE : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    rw [hE] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow ι y 2, hsqE₀ y hy, map_one]
  have hcardE : Nat.card E = 32 := by
    rw [hE, Subgroup.card_map_of_injective hι, hcardE₀]
  exact ⟨E, ⟨hcommE, hsqE⟩, hcardE, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.SideF4
