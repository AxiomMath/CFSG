module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Equiv

variable {Ω : Type*}

private abbrev OrbQ (A : Subgroup (Perm Ω)) := Quotient (MulAction.orbitRel A Ω)

private abbrev omk (A : Subgroup (Perm Ω)) (x : Ω) : OrbQ A :=
  Quotient.mk (MulAction.orbitRel A Ω) x

private theorem omk_eq_iff (A : Subgroup (Perm Ω)) (x y : Ω) :
    omk A y = omk A x ↔ ∃ a : A, (a : Perm Ω) x = y := by
  unfold omk
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  rfl

private theorem omk_apply (A : Subgroup (Perm Ω)) (a : A) (x : Ω) :
    omk A ((a : Perm Ω) x) = omk A x :=
  (omk_eq_iff A x _).2 ⟨a, rfl⟩

private theorem omk_out (A : Subgroup (Perm Ω)) (q : OrbQ A) : omk A q.out = q :=
  Quotient.out_eq q

private theorem fib_dvd [Finite Ω] (A : Subgroup (Perm Ω)) (q : OrbQ A) :
    Nat.card {x // omk A x = q} ∣ Nat.card A := by
  have e : {x // omk A x = q} ≃ MulAction.orbit A q.out :=
    Equiv.subtypeEquivRight fun x => by
      refine (Iff.of_eq (congrArg (omk A x = ·) (omk_out A q).symm)).trans ?_
      rw [omk_eq_iff, MulAction.mem_orbit_iff]
      rfl
  rw [Nat.card_congr e, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

private theorem card_le_prod [Finite Ω] (A : Subgroup (Perm Ω)) (hAc : IsMulCommutative A)
    [Fintype (OrbQ A)] :
    Nat.card A ≤ ∏ q : OrbQ A, Nat.card {x // omk A x = q} := by
  let f : A → ∀ q : OrbQ A, {x // omk A x = q} := fun a q =>
    ⟨(a : Perm Ω) q.out, by rw [omk_apply, omk_out]⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨c, hc⟩ := (omk_eq_iff A (omk A x).out x).1 (omk_out A (omk A x)).symm
    have hcomm : ∀ (u v : A) (y : Ω), (u : Perm Ω) ((v : Perm Ω) y) = (v : Perm Ω) ((u : Perm Ω) y) :=
      fun u v y => by
        have := congrArg (fun g : A => (g : Perm Ω) y) (hAc.is_comm.comm u v)
        simpa using this
    have hab : (a : Perm Ω) (omk A x).out = (b : Perm Ω) (omk A x).out :=
      congrArg Subtype.val (congrFun h (omk A x))
    rw [← hc, hcomm a c, hab, hcomm c b]
  calc Nat.card A ≤ Nat.card (∀ q : OrbQ A, {x // omk A x = q}) :=
        Nat.card_le_card_of_injective f hf
    _ = _ := Nat.card_pi

private theorem exists_exp {p : ℕ} (hp : p.Prime) [Finite Ω] (A : Subgroup (Perm Ω))
    (hAc : IsMulCommutative A) (hAe : ∀ x ∈ A, x ^ p = 1) [Fintype (OrbQ A)] :
    ∃ β : ℕ, Nat.card A = p ^ β ∧ ∃ e : OrbQ A → ℕ,
      (∀ q, Nat.card {x // omk A x = q} = p ^ e q) ∧ β ≤ ∑ q, e q := by
  have := Fact.mk hp
  have hP : IsPGroup p A := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hAe g.1 g.2⟩
  obtain ⟨β, hβ⟩ := (IsPGroup.iff_card).1 hP
  have h1 : ∀ q : OrbQ A, ∃ e : ℕ, Nat.card {x // omk A x = q} = p ^ e := fun q => by
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).1 (hβ ▸ fib_dvd A q)
    exact ⟨e, he⟩
  choose e he using h1
  refine ⟨β, hβ, e, he, ?_⟩
  have h2 := card_le_prod A hAc
  rw [hβ] at h2
  simp only [he] at h2
  rw [Finset.prod_pow_eq_pow_sum] at h2
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2

private theorem mul_le_pow {p : ℕ} (hp : 2 ≤ p) (e : ℕ) : p * e ≤ p ^ e := by
  rcases e with _ | k
  · simp
  · have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp k
    rw [pow_succ, mul_comm (p ^ k) p]
    exact Nat.mul_le_mul_left p (by omega)

private theorem sq_mul_le_two_pow {p : ℕ} (hp : 3 ≤ p) {e : ℕ} (he : 2 ≤ e) :
    p ^ 2 * e ≤ 2 * p ^ e := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  have key : ∀ k : ℕ, k + 2 ≤ 2 * 3 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  have h1 := key k
  have h2 : 3 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp k
  rw [pow_add]
  calc p ^ 2 * (k + 2) ≤ p ^ 2 * (2 * p ^ k) := Nat.mul_le_mul_left _ (h1.trans (by omega))
    _ = 2 * (p ^ k * p ^ 2) := by ring

theorem card_le_of_fixedSet_two
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (F : Finset Ω) (hF : F.card ≤ p + 1)
    (A D : Subgroup (Equiv.Perm Ω)) (hDA : D ≤ A) (hAc : IsMulCommutative A)
    (hAe : ∀ x ∈ A, x ^ p = 1) (hD2 : Nat.card D = p ^ 2)
    (hDF : ∀ d ∈ D, d ≠ 1 → ∀ x, d x = x ↔ x ∈ F) :
    p ^ 2 ≤ Fintype.card Ω ∧ ∃ β : ℕ, Nat.card A = p ^ β ∧
      p ^ 2 * β ≤ 2 * Fintype.card Ω + p ^ 2 := by
  classical
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨d0, hd0D, hd0⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card D = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩, ⟨1⟩⟩
    rw [hD2] at this
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
    omega
  have hFinv : ∀ a ∈ A, ∀ x, a x ∈ F ↔ x ∈ F := by
    intro a ha x
    rw [← hDF d0 hd0D hd0, ← hDF d0 hd0D hd0]
    have hc : d0 * a = a * d0 := by
      have := hAc.is_comm.comm (⟨d0, hDA hd0D⟩ : A) ⟨a, ha⟩
      simpa using congrArg Subtype.val this
    have : d0 (a x) = a (d0 x) := by
      have := congrArg (fun g : Perm Ω => g x) hc
      simpa using this
    rw [this]
    exact a.injective.eq_iff
  have hDinj : ∀ x, x ∉ F → Function.Injective (fun d : D => (d : Perm Ω) x) := by
    intro x hx d d' h
    by_contra hne
    have hne' : (d⁻¹ * d' : D) ≠ 1 := by
      intro h1
      exact hne (inv_mul_eq_one.1 h1)
    apply hx
    rw [← hDF (d⁻¹ * d' : D) (d⁻¹ * d').2 (fun h1 => hne' (Subtype.ext h1))]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    have h' : (d : Perm Ω) x = (d' : Perm Ω) x := h
    rw [← h']
    simp
  obtain ⟨x0, hx0⟩ : ∃ x, x ∉ F := by
    by_contra hcon
    push Not at hcon
    exact hd0 (Equiv.ext fun x => (hDF d0 hd0D hd0 x).2 (hcon x))
  have hΩ : p ^ 2 ≤ Fintype.card Ω := by
    rw [← hD2, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective _ (hDinj x0 hx0)
  refine ⟨hΩ, ?_⟩
  let : Fintype (OrbQ A) := Fintype.ofFinite _
  obtain ⟨β, hβ, e, he, hβe⟩ := exists_exp hp A hAc hAe
  refine ⟨β, hβ, ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (OrbQ A), T = F.image (omk A) := ⟨_, rfl⟩
  have hfibF : ∀ q ∈ T, ∀ x, omk A x = q → x ∈ F := by
    intro q hq x hx
    rw [hT] at hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨a, ha⟩ := (omk_eq_iff A y x).1 hx
    rw [← ha]
    exact (hFinv a a.2 y).2 hy
  have hcardfib : ∀ q, Nat.card {x // omk A x = q} =
      (Finset.univ.filter fun x => omk A x = q).card := by
    intro q; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsumT : ∑ q ∈ T, Nat.card {x // omk A x = q} = F.card := by
    rw [hT, Finset.card_eq_sum_card_image (omk A) F]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hcardfib]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨hfibF q (hT ▸ hq) x h, h⟩, fun h => h.2⟩
  have htot : ∑ q : OrbQ A, Nat.card {x // omk A x = q} = Fintype.card Ω := by
    have := Finset.card_eq_sum_card_fiberwise (f := omk A) (s := (Finset.univ : Finset Ω))
      (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.card_univ] at this
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcardfib]
  have hTe : ∑ q ∈ T, e q ≤ 1 := by
    have h1 : ∑ q ∈ T, p * e q ≤ ∑ q ∈ T, Nat.card {x // omk A x = q} :=
      Finset.sum_le_sum fun q _ => by rw [he q]; exact mul_le_pow (by omega) _
    rw [hsumT, ← Finset.mul_sum] at h1
    by_contra hcon
    push Not at hcon
    have : p * 2 ≤ p * ∑ q ∈ T, e q := Nat.mul_le_mul_left _ hcon
    omega
  have hTc : ∀ q ∈ Tᶜ, 2 ≤ e q := by
    intro q hq
    have hx : q.out ∉ F := fun h => (Finset.mem_compl.1 hq) (by
      rw [hT, ← omk_out A q]
      exact Finset.mem_image_of_mem _ h)
    have hmem : ∀ d : D, omk A ((d : Perm Ω) q.out) = q := fun d =>
      (omk_apply A ⟨d, hDA d.2⟩ q.out).trans (omk_out A q)
    have hle : p ^ 2 ≤ Nat.card {x // omk A x = q} := by
      rw [← hD2]
      exact Nat.card_le_card_of_injective
        (fun d : D => (⟨(d : Perm Ω) q.out, hmem d⟩ : {x // omk A x = q}))
        (fun d d' h => hDinj _ hx (congrArg Subtype.val h))
    rw [he q] at hle
    exact (Nat.pow_le_pow_iff_right hp1).1 hle
  have hGsum : ∑ q ∈ Tᶜ, p ^ 2 * e q ≤ 2 * Fintype.card Ω :=
    calc _ ≤ ∑ q ∈ Tᶜ, 2 * Nat.card {x // omk A x = q} :=
          Finset.sum_le_sum fun q hq => by rw [he q]; exact sq_mul_le_two_pow hp3 (hTc q hq)
      _ = 2 * ∑ q ∈ Tᶜ, Nat.card {x // omk A x = q} := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑ q : OrbQ A, Nat.card {x // omk A x = q} :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      _ = _ := by rw [htot]
  have hsplit : ∑ q ∈ T, e q + ∑ q ∈ Tᶜ, e q = ∑ q, e q := Finset.sum_add_sum_compl T e
  rw [← Finset.mul_sum] at hGsum
  have h2 : p ^ 2 * β ≤ p ^ 2 * (∑ q ∈ T, e q + ∑ q ∈ Tᶜ, e q) :=
    Nat.mul_le_mul_left _ (hsplit ▸ hβe)
  have h3 : p ^ 2 * ∑ q ∈ T, e q ≤ p ^ 2 * 1 := Nat.mul_le_mul_left _ hTe
  rw [mul_add] at h2
  omega

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
