module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 QuaternionGroup

@[expose] def Q16Pair {G : Type*} [Group G] (x y : G) : Prop :=
  x ^ 4 ≠ 1 ∧ x ^ 8 = 1 ∧ y ^ 2 = x ^ 4 ∧ y * x * y⁻¹ = x⁻¹

@[expose] def NoQ16 (G : Type*) [Group G] : Prop := ∀ x y : G, ¬ Q16Pair x y

theorem Q16Pair.map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    {x y : G} (h : Q16Pair x y) : Q16Pair (f x) (f y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun h => h1 (hf (by rw [map_pow, h, map_one])), by rw [← map_pow, h2, map_one],
    by rw [← map_pow, ← map_pow, h3], ?_⟩
  simpa only [map_mul, map_inv] using congrArg f h4

theorem NoQ16.of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : NoQ16 H) : NoQ16 G :=
  fun x y hxy => h (f x) (f y) (hxy.map f hf)

theorem quaternionGroup_q16Pair {n m : ℕ} (hm : 0 < m) (hn : n = 4 * m) :
    Q16Pair (a (m : ZMod (2 * n)) : QuaternionGroup n) (xa 0) := by
  subst hn
  have hx : (a (m : ZMod (2 * (4 * m))) : QuaternionGroup (4 * m)) = (a 1) ^ m :=
    (a_one_pow m).symm
  have h4 : (a (m : ZMod (2 * (4 * m))) : QuaternionGroup (4 * m)) ^ 4 =
      a ((4 * m : ℕ) : ZMod (2 * (4 * m))) := by
    rw [hx, ← pow_mul, mul_comm m 4, a_one_pow]
  have h2n : (2 : ZMod (2 * (4 * m))) * ((4 * m : ℕ) : ZMod (2 * (4 * m))) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 * (4 * m))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h4, one_def]
    intro h
    have := QuaternionGroup.a.inj h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  · rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, h4, ← a_one_pow, ← pow_mul,
      show (4 * m) * 2 = 2 * (4 * m) by ring, a_one_pow_n]
  · rw [xa_sq, h4]
  · have e1 : (xa 0 : QuaternionGroup (4 * m))⁻¹ =
        xa (((4 * m : ℕ) : ZMod (2 * (4 * m))) + 0) := rfl
    have e2 : (a (m : ZMod (2 * (4 * m))) : QuaternionGroup (4 * m))⁻¹ =
        a (-(m : ZMod (2 * (4 * m)))) := rfl
    rw [e1, e2, xa_mul_a, xa_mul_xa]
    congr 1
    linear_combination h2n

theorem exists_q16Pair_of_injective {Y : Type*} [Group Y] {r : ℕ} (hr : 4 ≤ r)
    (ι : QuaternionGroup (2 ^ (r - 2)) →* Y) (hι : Function.Injective ι) :
    ∃ x y : Y, Q16Pair x y := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℕ, 0 < m ∧ 2 ^ (r - 2) = 4 * m :=
    ⟨2 ^ (r - 4), by positivity, by rw [show r - 2 = (r - 4) + 2 by omega, pow_add]; ring⟩
  exact ⟨_, _, (quaternionGroup_q16Pair (n := 2 ^ (r - 2)) hm0 hm).map ι hι⟩

@[expose] def EmbedsAut (K A : Type) [Group K] [Group A] : Prop :=
  ∀ (Y : Type) [Group Y] (N : Subgroup Y) [N.Normal], Nonempty (↥N ≃* K) →
    Subgroup.centralizer (N : Set Y) = ⊥ → ∃ f : Y →* A, Function.Injective f

theorem smallLeafR_of_noQ16 {r : ℕ} (hr : 4 ≤ r) {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → ∃ (A : Type) (_ : Group A), EmbedsAut F A ∧ NoQ16 A) :
    SmallLeafR r P := by
  intro Y _ _ _ hnab _ hPF R S t hd hc _
  exfalso
  have := genFittingFStar_normal Y
  obtain ⟨A, _, hE, hA⟩ := h _ hPF
  obtain ⟨f, hf⟩ := hE Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hnab)
  obtain ⟨e⟩ := hc.1
  let ι : QuaternionGroup (2 ^ (r - 2)) →* Y :=
    R.subtype.comp ((S : Subgroup R).subtype.comp e.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.symm.injective)
  obtain ⟨x, y, hxy⟩ := exists_q16Pair_of_injective hr ι hι
  exact hA (f x) (f y) (hxy.map f hf)

end CFSG.CGT.PushingUpLit.SolKNA.R4
