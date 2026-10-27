module

public import Mathlib.Algebra.Module.ZMod
public import CFSG.GH74.GLS.Bg.TwoGroups.L23V

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

theorem elemAbelian_equiv {V : Type} [Group V] [Finite V] (hc : ∀ a b : V, a * b = b * a)
    (h2 : ∀ a : V, a * a = 1) (n : ℕ) (hcard : Nat.card V = 2 ^ n) :
    Nonempty (V ≃* E2 n) := by
  classical
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hadd : ∀ x : Additive V, 2 • x = 0 := by
    intro x
    show Additive.ofMul ((Additive.toMul x) ^ 2) = 0
    rw [pow_two, h2]; rfl
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule hadd
  have : Finite (Additive V) := ‹Finite V›
  have : Fintype (Additive V) := Fintype.ofFinite _
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod 2) (Additive V) = n := by
    have h1 : Fintype.card (Additive V) = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive V) :=
      Module.card_eq_pow_finrank
    have h2' : Fintype.card (Additive V) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]; exact hcard
    rw [h2', ZMod.card] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hfr
  exact ⟨AddEquiv.toMultiplicativeRight (b.equivFun.toAddEquiv)⟩

theorem homocyclic {T : Type} [Group T] [Finite T] (hp : IsPGroup 2 T) (α : MulAut T)
    (A E : Subgroup T) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAa : ∀ a ∈ A, α a ∈ A) (hfix : ∀ a ∈ A, α a = a → a = 1)
    (hEA : E ≤ A) (hEcard : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    (hΩ : ∀ a ∈ A, a * a = 1 → a ∈ E) :
    ∃ (k : ℕ) (a : T), 1 ≤ k ∧ a ∈ A ∧ orderOf a = 2 ^ k ∧
      Nonempty (↥A ≃* Multiplicative (ZMod (2 ^ k) × ZMod (2 ^ k))) := by
  classical
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, Commute x y := fun x hx y hy => hAc x hx y hy
  have hord : ∀ b : T, ∃ j : ℕ, orderOf b = 2 ^ j := by
    intro b
    obtain ⟨n, hn⟩ := hp b
    have h1 : orderOf b ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨j, hj⟩
  have : Nonempty A := ⟨1⟩
  obtain ⟨a₀, ha₀⟩ := Finite.exists_max (fun x : A => orderOf (x : T))
  set a : T := (a₀ : T) with ha
  have haA : a ∈ A := a₀.2
  have hmax : ∀ b ∈ A, orderOf b ≤ orderOf a := fun b hb => ha₀ ⟨b, hb⟩
  obtain ⟨k, hk⟩ := hord a
  have hpowk : ∀ b ∈ A, b ^ (2 ^ k) = 1 := by
    intro b hb
    obtain ⟨j, hj⟩ := hord b
    have h1 := hmax b hb
    rw [hj, hk] at h1
    have hjk : j ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    have : orderOf b ∣ 2 ^ k := by rw [hj]; exact Nat.pow_dvd_pow 2 hjk
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hk1 : 1 ≤ k := by
    have hn : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hEcard]; norm_num)
    obtain ⟨e, he⟩ := exists_ne (1 : E)
    have h2 : orderOf (e : T) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hE2 e e.2) (fun h => he (Subtype.ext h))
    have h3 := hmax e (hEA e.2)
    rw [h2, hk] at h3
    by_contra h0
    have : k = 0 := by omega
    rw [this] at h3
    omega
  set b : T := α a with hb
  have hbA : b ∈ A := hAa a haA
  have hpow2k : a ^ (2 ^ k) = 1 := hpowk a haA
  have hb2k : b ^ (2 ^ k) = 1 := hpowk b hbA
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set e₀ : T := a ^ (2 ^ k') with he₀
  set f₀ : T := b ^ (2 ^ k') with hf₀
  have hsq : ∀ x : T, x ^ (2 ^ (k' + 1)) = (x ^ (2 ^ k')) * (x ^ (2 ^ k')) := by
    intro x; rw [pow_succ, pow_mul, pow_two]
  have he₀sq : e₀ * e₀ = 1 := by rw [he₀, ← hsq]; exact hpow2k
  have hf₀sq : f₀ * f₀ = 1 := by rw [hf₀, ← hsq]; exact hb2k
  have he₀A : e₀ ∈ A := pow_mem haA _
  have hf₀A : f₀ ∈ A := pow_mem hbA _
  have he₀E : e₀ ∈ E := hΩ e₀ he₀A he₀sq
  have hf₀E : f₀ ∈ E := hΩ f₀ hf₀A hf₀sq
  have he₀1 : e₀ ≠ 1 := by
    intro h
    have h1 : orderOf a ∣ 2 ^ k' := orderOf_dvd_of_pow_eq_one h
    rw [hk] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ k' < 2 ^ (k' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hf₀eq : f₀ = α e₀ := by rw [hf₀, he₀, map_pow]
  have hf₀1 : f₀ ≠ 1 := by
    intro h
    apply he₀1
    rw [hf₀eq] at h
    simpa using h
  have hfe : f₀ ≠ e₀ := by
    intro h
    apply he₀1
    apply hfix e₀ he₀A
    rw [← hf₀eq]
    exact h
  have hg1 : e₀ * f₀ ≠ 1 := by
    intro h
    apply hfe
    have : f₀ = e₀⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (eq_inv_of_mul_eq_one_left he₀sq).symm
  have hE4 := L23.subgroup_card_four E hEcard e₀ f₀ (e₀ * f₀) he₀E hf₀E (mul_mem he₀E hf₀E)
    (Ne.symm he₀1) (Ne.symm hf₀1) (Ne.symm hg1) (Ne.symm hfe)
    (fun h => hf₀1 (mul_eq_left.mp h.symm)) (fun h => he₀1 (mul_eq_right.mp h.symm))
  have hsq1 : ∀ x : T, x * x = 1 → ∀ m : ℕ, x ^ (2 * m) = 1 := by
    intro x hx m; rw [pow_mul, pow_two, hx, one_pow]
  have hpe : ∀ i : ℕ, a ^ (i * 2 ^ k') = e₀ ^ i := fun i => by
    rw [he₀, ← pow_mul, mul_comm]
  have hpf : ∀ j : ℕ, b ^ (j * 2 ^ k') = f₀ ^ j := fun j => by
    rw [hf₀, ← pow_mul, mul_comm]
  have hdist : ∀ i j : ℕ, a ^ (i * 2 ^ k') * b ^ (j * 2 ^ k') = 1 → 2 ∣ i ∧ 2 ∣ j := by
    intro i j h
    rw [hpe, hpf] at h
    obtain ⟨i', hi | hi⟩ := Nat.even_or_odd' i <;> obtain ⟨j', hj | hj⟩ := Nat.even_or_odd' j
    · exact ⟨⟨i', hi⟩, ⟨j', hj⟩⟩
    · exfalso
      rw [hi, hj, hsq1 _ he₀sq, pow_succ, hsq1 _ hf₀sq, one_mul, one_mul] at h
      exact hf₀1 h
    · exfalso
      rw [hi, hj, hsq1 _ hf₀sq, pow_succ, hsq1 _ he₀sq, one_mul, mul_one] at h
      exact he₀1 h
    · exfalso
      rw [hi, hj, pow_succ, pow_succ, hsq1 _ he₀sq, hsq1 _ hf₀sq, one_mul, one_mul] at h
      exact hg1 h
  have hinj : ∀ i j : ℕ, a ^ i * b ^ j = 1 → 2 ^ (k' + 1) ∣ i ∧ 2 ^ (k' + 1) ∣ j := by
    have key : ∀ s : ℕ, s ≤ k' + 1 → ∀ i j : ℕ, a ^ i * b ^ j = 1 → 2 ^ s ∣ i ∧ 2 ^ s ∣ j := by
      intro s
      induction s with
      | zero => intro _ i j _; simp
      | succ s ih =>
        intro hs i j h
        obtain ⟨⟨i', hi⟩, ⟨j', hj⟩⟩ := ih (by omega) i j h
        have hab : Commute (a ^ i') (b ^ j') := (hcomm a haA b hbA).pow_pow i' j'
        have h1 : (a ^ i' * b ^ j') ^ (2 ^ s) = 1 := by
          rw [hab.mul_pow, ← pow_mul, ← pow_mul, mul_comm i', mul_comm j', ← hi, ← hj]
          exact h
        have h2 : (a ^ i' * b ^ j') ^ (2 ^ k') = 1 := by
          have : 2 ^ k' = 2 ^ s * 2 ^ (k' - s) := by rw [← pow_add]; congr 1; omega
          rw [this, pow_mul, h1, one_pow]
        rw [hab.mul_pow, ← pow_mul, ← pow_mul] at h2
        obtain ⟨⟨i'', hi'⟩, ⟨j'', hj'⟩⟩ := hdist i' j' h2
        refine ⟨⟨i'', ?_⟩, ⟨j'', ?_⟩⟩
        · rw [hi, hi', pow_succ]; ring
        · rw [hj, hj', pow_succ]; ring
    exact fun i j h => key (k' + 1) le_rfl i j h
  have hmulab : ∀ i j i' j' : ℕ,
      (a ^ i * b ^ j) * (a ^ i' * b ^ j') = a ^ (i + i') * b ^ (j + j') := by
    intro i j i' j'
    rw [pow_add, pow_add]
    have := (hcomm a haA b hbA).pow_pow i' j
    calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by
          simp only [mul_assoc]
      _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [this.symm.eq]
      _ = a ^ i * a ^ i' * (b ^ j * b ^ j') := by simp only [mul_assoc]
  let inB : T → Prop := fun x => ∃ i j : ℕ, x = a ^ i * b ^ j
  have hinB_mul : ∀ x y, inB x → inB y → inB (x * y) := by
    rintro x y ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    exact ⟨i + i', j + j', hmulab i j i' j'⟩
  have hE_B : ∀ w ∈ E, inB w := by
    intro w hw
    rcases hE4 w hw with h | h | h | h
    · exact ⟨0, 0, by simp [h]⟩
    · exact ⟨2 ^ k', 0, by simp [h, he₀]⟩
    · exact ⟨0, 2 ^ k', by simp [h, hf₀]⟩
    · rw [h]
      exact hinB_mul _ _ ⟨2 ^ k', 0, by simp [he₀]⟩ ⟨0, 2 ^ k', by simp [hf₀]⟩
  have hsurj : ∀ x ∈ A, inB x := by
    by_contra hcon
    simp only [not_forall] at hcon
    obtain ⟨x₀, hx₀A, hx₀⟩ := hcon
    have hex : ∃ s : ℕ, inB (x₀ ^ (2 ^ s)) := ⟨k' + 1, ⟨0, 0, by simp [hpowk x₀ hx₀A]⟩⟩
    let s := Nat.find hex
    have hs : inB (x₀ ^ (2 ^ s)) := Nat.find_spec hex
    have hs0 : s ≠ 0 := by
      intro h0
      apply hx₀
      have := hs
      rw [h0] at this
      simpa using this
    obtain ⟨s', hs'⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    set y : T := x₀ ^ (2 ^ s') with hy
    have hyA : y ∈ A := pow_mem hx₀A _
    have hyB : ¬ inB y := Nat.find_min hex (by omega)
    have hy2 : y * y = x₀ ^ (2 ^ s) := by
      rw [hs', pow_succ, pow_mul, pow_two]
    rw [← hy2] at hs
    obtain ⟨i, j, hij⟩ := hs
    have hy2k : (y * y) ^ (2 ^ k') = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ']; exact hpowk y hyA
    rw [hij, ((hcomm a haA b hbA).pow_pow i j).mul_pow, ← pow_mul, ← pow_mul] at hy2k
    obtain ⟨⟨i', hi⟩, ⟨j', hj⟩⟩ := hdist i j hy2k
    have hwA : a ^ i' * b ^ j' ∈ A := mul_mem (pow_mem haA _) (pow_mem hbA _)
    have hww : (a ^ i' * b ^ j') * (a ^ i' * b ^ j') = y * y := by
      rw [hij, hmulab, hi, hj]; congr 1 <;> congr 1 <;> ring
    have hcw : Commute y (a ^ i' * b ^ j')⁻¹ := hcomm y hyA _ (inv_mem hwA)
    have hyw : (y * (a ^ i' * b ^ j')⁻¹) * (y * (a ^ i' * b ^ j')⁻¹) = 1 := by
      rw [hcw.symm.mul_mul_mul_comm, ← hww]
      group
    have hyE : y * (a ^ i' * b ^ j')⁻¹ ∈ E :=
      hΩ _ (mul_mem hyA (inv_mem hwA)) hyw
    apply hyB
    have h3 := hinB_mul _ _ (hE_B _ hyE) ⟨i', j', rfl⟩
    rwa [inv_mul_cancel_right] at h3
  have : NeZero (2 ^ (k' + 1)) := ⟨by positivity⟩
  have hbord : orderOf b = 2 ^ (k' + 1) := by
    rw [hb]; exact (MulEquiv.orderOf_eq α a).trans hk
  have hpa : ∀ n : ℕ, a ^ (n % 2 ^ (k' + 1)) = a ^ n := fun n => by
    have := pow_mod_orderOf a n
    rwa [hk] at this
  have hpb : ∀ n : ℕ, b ^ (n % 2 ^ (k' + 1)) = b ^ n := fun n => by
    have := pow_mod_orderOf b n
    rwa [hbord] at this
  let φ : Multiplicative (ZMod (2 ^ (k' + 1)) × ZMod (2 ^ (k' + 1))) →* ↥A :=
    { toFun := fun u => ⟨a ^ (Multiplicative.toAdd u).1.val * b ^ (Multiplicative.toAdd u).2.val,
        mul_mem (pow_mem haA _) (pow_mem hbA _)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add, Subgroup.coe_mul]
        rw [hmulab, hpa, hpb] }
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : a ^ (Multiplicative.toAdd u).1.val * b ^ (Multiplicative.toAdd u).2.val = 1 :=
      congrArg Subtype.val hu
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hinj _ _ h1
    have h1' : (Multiplicative.toAdd u).1.val < 2 ^ (k' + 1) := ZMod.val_lt _
    have h2' : (Multiplicative.toAdd u).2.val < 2 ^ (k' + 1) := ZMod.val_lt _
    have e1 : (Multiplicative.toAdd u).1.val = 0 := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [hc, h]; simp
      · have := Nat.le_mul_of_pos_right (2 ^ (k' + 1)) h; omega
    have e2 : (Multiplicative.toAdd u).2.val = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · rw [hd, h]; simp
      · have := Nat.le_mul_of_pos_right (2 ^ (k' + 1)) h; omega
    apply Multiplicative.toAdd.injective
    exact Prod.ext ((ZMod.val_eq_zero _).mp e1) ((ZMod.val_eq_zero _).mp e2)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨i, j, rfl⟩ := hsurj x hx
    refine ⟨Multiplicative.ofAdd ((i : ZMod (2 ^ (k' + 1))), (j : ZMod (2 ^ (k' + 1)))), ?_⟩
    apply Subtype.ext
    show a ^ (i : ZMod (2 ^ (k' + 1))).val * b ^ (j : ZMod (2 ^ (k' + 1))).val = a ^ i * b ^ j
    rw [ZMod.val_natCast, ZMod.val_natCast, hpa, hpb]
  exact ⟨k' + 1, a, by omega, haA, hk, ⟨(MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm⟩⟩

theorem elem_of_fpf {T : Type} [Group T] [Finite T] (α : MulAut T) (hα : α ^ 3 = 1)
    (E : Subgroup T) (hcard : Nat.card E = 4) (hinv : ∀ e ∈ E, α e ∈ E)
    (hfpf : ∀ e ∈ E, α e = e → e = 1) :
    (∀ e ∈ E, e * e = 1) ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : IsMulCommutative E :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hcard]; norm_num)
  have hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  refine ⟨?_, hc⟩
  intro e he
  by_contra hee
  have h4 : e ^ 4 = 1 := by
    have h1 : orderOf (⟨e, he⟩ : E) ∣ Nat.card E := orderOf_dvd_natCard _
    rw [hcard] at h1
    have h2 : (⟨e, he⟩ : E) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    exact congrArg Subtype.val h2
  have h4' : e * e * (e * e) = 1 := by
    rw [← h4]; simp [pow_succ, mul_assoc]
  have he1 : e ≠ 1 := fun h => hee (by rw [h]; simp)
  have he3 : e * e * e ≠ 1 := by
    intro h
    apply he1
    calc e = e ^ 4 * (e * e * e)⁻¹ := by group
      _ = 1 := by rw [h4, h]; simp
  have hfour := L23.subgroup_card_four E hcard e (e * e) (e * e * e) he (mul_mem he he)
    (mul_mem (mul_mem he he) he) (Ne.symm he1) (Ne.symm hee) (Ne.symm he3)
    (fun h => he1 (by simpa using h)) (fun h => hee (by
      have : e * e = e * e * e * e⁻¹ := by group
      have h' : e * e * e = e := h.symm
      calc e * e = e * e * e * e⁻¹ := this
        _ = e * e⁻¹ := by rw [h']
        _ = 1 := by simp))
    (fun h => he1 (by
      have : e = (e * e)⁻¹ * (e * e * e) := by group
      rw [this, ← h]; simp))
  rcases hfour (α e) (hinv e he) with h | h | h | h
  · exact he1 ((map_eq_one_iff α α.injective).mp h)
  · exact he1 (hfpf e he h)
  · apply hee
    have h1 : α (e * e) = 1 := by
      rw [map_mul, h]
      exact h4'
    exact (map_eq_one_iff α α.injective).mp h1
  · apply he1
    apply hfpf e he
    have h1 : α (α (α e)) = e := by
      have := congrArg (fun s : MulAut T => s e) hα
      simpa [pow_succ] using this
    have h9 : e ^ 9 = e := by
      calc e ^ 9 = e ^ (4 * 2 + 1) := by norm_num
        _ = (e ^ 4) ^ 2 * e := by rw [pow_succ, pow_mul]
        _ = e := by rw [h4]; simp
    have h2 : α (α e) = e := by
      rw [h, map_mul, map_mul, h]
      calc e * e * e * (e * e * e) * (e * e * e) = e ^ 9 := by simp [pow_succ, mul_assoc]
        _ = e := h9
    rw [h2] at h1
    exact h1

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
