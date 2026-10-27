module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888YPl
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma function_eq_id_of_iterate_eq_id_of_coprime {X : Type*} [Finite X] (g : X → X)
    (hg : Function.Injective g) {p : ℕ} (hp : g^[p] = id)
    (hcop : Nat.Coprime p (Nat.factorial (Nat.card X))) : g = id := by
  haveI : Fintype X := Fintype.ofFinite X
  have hsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hg
  let ge : Equiv.Perm X := Equiv.ofBijective g ⟨hg, hsurj⟩
  have hge_pow : ge ^ p = 1 := by
    apply Equiv.ext
    intro x
    rw [Equiv.Perm.coe_pow]
    change g^[p] x = x
    exact congrFun hp x
  have h1 : orderOf ge ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hge_pow
  have h2 : orderOf ge ∣ Nat.factorial (Nat.card X) := by
    rw [← Nat.card_perm]
    exact orderOf_dvd_natCard ge
  have h3 : orderOf ge = 1 := by
    have hgcd : orderOf ge ∣ Nat.gcd p (Nat.factorial (Nat.card X)) := Nat.dvd_gcd h1 h2
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
    exact Nat.dvd_one.mp hgcd
  have hge1 : ge = 1 := orderOf_eq_one_iff.mp h3
  funext x
  have hx : ge x = x := by
    have := congrFun (congrArg (fun e : Equiv.Perm X => (e : X → X)) hge1) x
    simpa using this
  exact hx

theorem centralizes_of_pow_centralizes {Y : Type} [Group Y] {D : Subgroup Y}
    {W : Fin 4 → Subgroup Y} (hP : IsPlanes D W) (y : Y) (hy : ∀ x ∈ D, y * x * y⁻¹ ∈ D)
    (hperm : ∀ i, ∃ j, ∀ w ∈ W i, y * w * y⁻¹ ∈ W j) {p : ℕ} (hp : p = 5 ∨ p = 7)
    (hyp : ∀ d ∈ D, y ^ p * d * (y ^ p)⁻¹ = d) : ∀ d ∈ D, y * d * y⁻¹ = d := by
  classical
  choose σ hσ using hperm
  let c : MulAut Y := MulAut.conj y
  have hc_inj : Function.Injective (c : Y → Y) := c.injective
  have hc_iter : ∀ n (x : Y), c^[n] x = y ^ n * x * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply', ih, pow_succ']
        show y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ = (y * y ^ n) * x * (y * y ^ n)⁻¹
        simp only [mul_inv_rev, mul_assoc]
  have hfixD : ∀ x ∈ D, c^[p] x = x := by
    intro x hx
    rw [hc_iter p x]
    exact hyp x hx
  have hmap : ∀ i, (W i).map (c : Y →* Y) = W (σ i) := by
    intro i
    haveI : Finite (W (σ i)) := Nat.finite_of_card_ne_zero (by rw [hP.card (σ i)]; decide)
    have hcard_map : Nat.card ((W i).map (c : Y →* Y)) = Nat.card (W i) :=
      Subgroup.card_map_of_injective (K := W i) (f := (c : Y →* Y)) hc_inj
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact hσ i w hw
    · rw [hP.card (σ i), hcard_map, hP.card i]
  have hW_inj : Function.Injective W := by
    let φ : (∀ i : Fin 4, W i) → D := fun w =>
      ⟨w 0 * w 1 * w 2 * w 3, by
        exact D.mul_mem (D.mul_mem (D.mul_mem (hP.le 0 (w 0).2) (hP.le 1 (w 1).2))
          (hP.le 2 (w 2).2)) (hP.le 3 (w 3).2)⟩
    have hφ_surj : Function.Surjective φ := by
      intro d
      obtain ⟨w, hw, hd⟩ := hP.decomp d d.2
      exact ⟨fun i => ⟨w i, hw i⟩, Subtype.ext hd.symm⟩
    have hcard_dom : Nat.card (∀ i : Fin 4, W i) = 2 ^ 8 := by
      rw [Nat.card_pi]
      simp only [hP.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      decide
    have hφ_bij : Function.Bijective φ := by
      haveI : Finite (∀ i : Fin 4, W i) :=
        Nat.finite_of_card_ne_zero (by rw [hcard_dom]; decide)
      refine Function.Surjective.bijective_of_nat_card_le hφ_surj ?_
      rw [hcard_dom, hP.card_D]
    have hφ_inj : Function.Injective φ := hφ_bij.1
    let hone : ∀ i : Fin 4, W i := fun _ => 1
    have hφ_val : ∀ (k : Fin 4) (x : W k), (φ (Function.update hone k x)).1 = (x : Y) := by
      intro k x
      change (Function.update hone k x 0 : Y) * (Function.update hone k x 1 : Y)
        * (Function.update hone k x 2 : Y) * (Function.update hone k x 3 : Y) = (x : Y)
      fin_cases k <;> simp [hone]
    intro i j hW
    by_contra hij
    have hne : W i ≠ ⊥ := by
      intro hbot
      have hc1 : Nat.card (W i) = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hP.card i] at hc1
      exact (by decide : (4 : ℕ) ≠ 1) hc1
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    let b : W j := ⟨(a : Y), hW ▸ a.2⟩
    have h1 : φ (Function.update hone i a) = φ (Function.update hone j b) :=
      Subtype.ext (by rw [hφ_val i a, hφ_val j b])
    have h2 : Function.update hone i a ≠ Function.update hone j b := by
      intro h
      have hh := congrFun h i
      rw [Function.update_self, Function.update_of_ne hij b hone] at hh
      exact ha hh
    exact h2 (hφ_inj h1)
  have hσ_inj : Function.Injective σ := by
    intro i j hij
    exact hW_inj (Subgroup.map_injective hc_inj (by rw [hmap i, hmap j, hij]))
  have hiter_sub : ∀ n (i : Fin 4), c^[n] '' (W i : Set Y) ⊆ (W (σ^[n] i) : Set Y) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
        intro i x hx
        obtain ⟨w, hw, rfl⟩ := hx
        simp only [Function.iterate_succ_apply]
        exact ih (σ i) ⟨c w, hσ i w hw, rfl⟩
  have hiter_image : ∀ i, c^[p] '' (W i : Set Y) = (W i : Set Y) := by
    intro i
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hfixD w (hP.le i hw)]
      exact hw
    · intro hx
      exact ⟨x, hx, hfixD x (hP.le i hx)⟩
  have hσp : ∀ i, σ^[p] i = i := by
    intro i
    have hle : W i ≤ W (σ^[p] i) := by
      show (W i : Set Y) ⊆ (W (σ^[p] i) : Set Y)
      rw [← hiter_image i]
      exact hiter_sub p i
    have heq : W i = W (σ^[p] i) := by
      haveI : Finite (W (σ^[p] i)) :=
        Nat.finite_of_card_ne_zero (by rw [hP.card (σ^[p] i)]; decide)
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hP.card (σ^[p] i), hP.card i]
    exact (hW_inj heq).symm
  have hcop4 : Nat.Coprime p (Nat.factorial (Nat.card (Fin 4))) := by
    rw [Nat.card_fin]
    rcases hp with rfl | rfl <;> decide
  have hσ_id : σ = id :=
    function_eq_id_of_iterate_eq_id_of_coprime σ hσ_inj (funext hσp) hcop4
  have hσ_apply : ∀ i, σ i = i := fun i => congrFun hσ_id i
  have hmap_id : ∀ i, (W i).map (c : Y →* Y) = W i := by
    intro i
    rw [hmap i, hσ_apply i]
  have hc_image : ∀ i, c '' (W i : Set Y) = (W i : Set Y) := by
    intro i
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hx : c w ∈ (W i).map (c : Y →* Y) := Subgroup.mem_map_of_mem (c : Y →* Y) hw
      rwa [hmap_id i] at hx
    · intro hx
      have hx' : x ∈ (W i).map (c : Y →* Y) := by rwa [hmap_id i]
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx'
      exact ⟨w, hw, rfl⟩
  have hfixW : ∀ i, ∀ w ∈ W i, c w = w := by
    intro i w hw
    haveI : Finite (W i) := Nat.finite_of_card_ne_zero (by rw [hP.card i]; decide)
    let g : W i → W i := fun x => ⟨c x, by
      have hx : c x ∈ (W i).map (c : Y →* Y) := Subgroup.mem_map_of_mem (c : Y →* Y) x.2
      rwa [hmap_id i] at hx⟩
    have hg_inj : Function.Injective g := by
      intro x z hxz
      exact Subtype.ext (hc_inj (congrArg Subtype.val hxz))
    have hg_val : ∀ n (x : W i), ((g^[n] x : W i) : Y) = c^[n] (x : Y) := by
      intro n
      induction n with
      | zero => intro x; rfl
      | succ n ih =>
          intro x
          rw [Function.iterate_succ_apply']
          show c (((g^[n] x : W i) : Y)) = c^[n+1] (x : Y)
          rw [ih x, Function.iterate_succ_apply']
    have hg_pow : g^[p] = id := by
      funext x
      apply Subtype.ext
      rw [hg_val p x]
      exact hfixD (x : Y) (hP.le i x.2)
    have hcopW : Nat.Coprime p (Nat.factorial (Nat.card (W i))) := by
      rw [hP.card i]
      rcases hp with rfl | rfl <;> decide
    have hg_id : g = id :=
      function_eq_id_of_iterate_eq_id_of_coprime g hg_inj hg_pow hcopW
    exact congrArg Subtype.val (congrFun hg_id ⟨w, hw⟩)
  intro d hd
  obtain ⟨w, hw, rfl⟩ := hP.decomp d hd
  change c (w 0 * w 1 * w 2 * w 3) = w 0 * w 1 * w 2 * w 3
  rw [map_mul, map_mul, map_mul, hfixW 0 (w 0) (hw 0), hfixW 1 (w 1) (hw 1),
    hfixW 2 (w 2) (hw 2), hfixW 3 (w 3) (hw 3)]

end CFSG.OddStandard.SmallF3.Omega
