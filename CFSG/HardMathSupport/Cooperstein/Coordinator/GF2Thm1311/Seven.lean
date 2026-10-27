module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

section Seven

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def commMap (x : MulAut V) : V →* V where
  toFun v := x v * v⁻¹
  map_one' := by simp
  map_mul' v w := by simp [mul_comm, mul_assoc, mul_left_comm]

theorem commMap_apply (x : MulAut V) (v : V) : commMap x v = x v * v⁻¹ := rfl

theorem mem_ker_commMap {x : MulAut V} {v : V} : v ∈ (commMap x).ker ↔ x v = v := by
  rw [MonoidHom.mem_ker, commMap_apply, mul_inv_eq_one]


theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem prod_shift (f : ℕ → V) (h : f 7 = f 0) :
    ∏ i ∈ Finset.range 7, (f (i + 1) * (f i)⁻¹) = 1 := by
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have h1 : (∏ i ∈ Finset.range 7, f (i + 1)) * f 0 = ∏ i ∈ Finset.range 8, f i :=
    (Finset.prod_range_succ' f 7).symm
  have h2 : ∏ i ∈ Finset.range 8, f i = (∏ i ∈ Finset.range 7, f i) * f 7 :=
    Finset.prod_range_succ f 7
  rw [h2, h] at h1
  have h3 := mul_right_cancel h1
  rw [h3, mul_inv_cancel]

theorem eq_one_of_commMap_fixed (hV : ∀ v : V, v * v = 1) {x : MulAut V} (hx7 : x ^ 7 = 1) {v : V}
    (hfix : x (commMap x v) = commMap x v) : commMap x v = 1 := by
  set w := commMap x v with hw
  have hpow : ∀ i : ℕ, (x ^ i) w = w := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih, hfix]
  have h1 : ∏ i ∈ Finset.range 7, (x ^ i) w = w ^ 7 := by
    rw [Finset.prod_congr rfl (fun i _ => hpow i)]
    simp
  have h2 : ∏ i ∈ Finset.range 7, (x ^ i) w = 1 := by
    have : ∀ i : ℕ, (x ^ i) w = (x ^ (i + 1)) v * ((x ^ i) v)⁻¹ := by
      intro i
      rw [hw, commMap_apply, map_mul, map_inv, ← MulAut.mul_apply, ← pow_succ]
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    refine prod_shift (fun i => (x ^ i) v) ?_
    simp [hx7]
  have h3 : w ^ 7 = w := by
    have : w ^ 2 = 1 := by rw [pow_two]; exact hV w
    calc w ^ 7 = (w ^ 2) ^ 3 * w := by group
      _ = w := by rw [this]; simp
  rw [h1, h3] at h2
  exact h2


theorem card_modEq_card_fixV {p : ℕ} [hp : Fact p.Prime] {g : MulAut V} (hg : orderOf g = p) :
    Nat.card V ≡ Nat.card (fixV (Subgroup.zpowers g)) [MOD p] := by
  have hpg : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod := hpg.card_modEq_card_fixedPoints V
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) =
      Nat.card (fixV (Subgroup.zpowers g)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun w => by
      rw [MulAction.mem_fixedPoints, mem_fixV_zpowers]
      constructor
      · intro h
        exact h ⟨g, Subgroup.mem_zpowers g⟩
      · intro h x
        obtain ⟨k, hk⟩ := x.2
        have : ((x : MulAut V)) w = w := by
          rw [← hk]
          have h' : g⁻¹ w = w := by
            conv_lhs => rw [← h]
            exact MulAut.inv_apply_self V g w
          have : ∀ k : ℤ, (g ^ k) w = w := by
            intro k
            induction k using Int.induction_on with
            | zero => rfl
            | succ k ih => rw [zpow_add_one, MulAut.mul_apply, h, ih]
            | pred k ih => rw [zpow_sub_one, MulAut.mul_apply, h', ih]
          exact this k
        exact this
  rwa [hfix] at hmod


theorem false_of_seven_pair (hV : ∀ v : V, v * v = 1) {a b : MulAut V} (ha : a * a = 1)
    (hb : b * b = 1) (h7 : orderOf (a * b) = 7)
    (hidx : (fixV (Subgroup.zpowers a)).index * (fixV (Subgroup.zpowers b)).index ≤ 16) :
    False := by
  classical
  have hfact : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  obtain ⟨x, hxdef⟩ : ∃ x : MulAut V, x = a * b := ⟨_, rfl⟩
  rw [← hxdef] at h7
  have hx7 : x ^ 7 = 1 := by rw [← h7]; exact pow_orderOf_eq_one _
  have hax : a * x * a = x⁻¹ := by
    rw [hxdef, ← mul_assoc, ha, one_mul, mul_inv_rev, hai, hbi]
  have hge : 8 ≤ (fixV (Subgroup.zpowers x)).index := by
    have h1 := two_pow_orderOf_le_index_fixV hV (p := 7) (by norm_num) h7
    rwa [orderOf_two_zmod_seven] at h1
  have hle : (fixV (Subgroup.zpowers x)).index ≤ 16 := by
    rw [hxdef]; exact (index_fixV_mul_le a b).trans hidx
  obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hV (Subgroup.zpowers x)
  have hm3 : m = 3 := by
    have h8 : 8 ≤ 2 ^ m := hm ▸ hge
    have h16 : 2 ^ m ≤ 16 := hm ▸ hle
    have hm3' : 3 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m <;> omega
    have hm4' : m ≤ 4 := by
      by_contra h
      push Not at h
      have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
      omega
    by_contra hne
    have hm4 : m = 4 := by omega
    subst hm4
    have hmod := card_modEq_card_fixV (p := 7) h7
    have hcard := Subgroup.card_mul_index (fixV (Subgroup.zpowers x))
    rw [hm] at hcard
    set c := Nat.card (fixV (Subgroup.zpowers x)) with hc
    have hVc : Nat.card V = 16 * c := by rw [← hcard]; ring
    have hdvd : 7 ∣ 15 * c := by
      have h1 : c ≤ Nat.card V := by rw [hVc]; omega
      have := (Nat.modEq_iff_dvd' h1).mp hmod.symm
      rw [hVc] at this
      have e : 16 * c - c = 15 * c := by omega
      rwa [e] at this
    have h7c : 7 ∣ c := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 7 15) hdvd)
    have hp2 : IsPGroup 2 V := by
      intro w
      refine ⟨1, ?_⟩
      simpa [pow_one, sq] using hV w
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hp2
    have hcV : c ∣ Nat.card V := ⟨16, by rw [hVc]; ring⟩
    rw [hn] at hcV
    have : 7 ∣ 2 ^ n := h7c.trans hcV
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) this)
    omega
  set φ := commMap x with hφ
  set W := φ.range with hW
  have hker : φ.ker = fixV (Subgroup.zpowers x) := by
    ext v
    rw [hφ, mem_ker_commMap, mem_fixV_zpowers]
  have hWcard : Nat.card W = 8 := by
    rw [← Subgroup.index_ker, hker, hm, hm3]; norm_num
  have hWx : ∀ w ∈ W, x w ∈ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨x v, ?_⟩
    simp [hφ, commMap_apply]
  have hWa : ∀ w ∈ W, a w ∈ W := by
    rintro _ ⟨v, rfl⟩
    have h1 : ∀ u : V, a (x u) = x⁻¹ (a u) := by
      intro u
      have := congrArg (fun f : MulAut V => f (a u)) hax
      simp only [MulAut.mul_apply] at this
      have h2 : a (a u) = u := by
        have := congrArg (fun f : MulAut V => f u) ha
        simpa using this
      rw [h2] at this
      rw [← this]
    have h3 : a (φ v) = (φ (x⁻¹ (a v)))⁻¹ := by
      simp only [hφ, commMap_apply, map_mul, map_inv, h1, MulAut.apply_inv_self, mul_inv_rev,
        inv_inv]
    rw [h3]
    exact W.inv_mem ⟨_, rfl⟩
  have hWfix : ∀ w ∈ W, x w = w → w = 1 := by
    rintro _ ⟨v, rfl⟩ h
    exact eq_one_of_commMap_fixed hV hx7 h
  have hpowW : ∀ i : ℕ, ∀ w ∈ W, (x ^ i) w ∈ W := by
    intro i
    induction i with
    | zero => intro w hw; simpa using hw
    | succ i ih => intro w hw; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hWx w hw)
  have hfree : ∀ w ∈ W, w ≠ 1 → ∀ i : ℕ, (x ^ i) w = w → 7 ∣ i := by
    intro w hw hw1 i hi
    by_contra h7i
    have hcop : Nat.Coprime i 7 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hfact.out).2 h7i))
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
    have h1 : ∀ k : ℕ, (x ^ (i * k)) w = w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [mul_add, mul_one, pow_add, MulAut.mul_apply, hi, ih]
    have h2 : x ^ (i * s) = x := by
      have : i * s = 7 * (i * s / 7) + 1 := by
        have := Nat.div_add_mod (i * s) 7
        omega
      rw [this, pow_add, pow_mul, hx7, one_pow, one_mul, pow_one]
    have := h1 s
    rw [h2] at this
    exact hw1 (hWfix w hw this)
  have : Fintype W := Fintype.ofFinite W
  have hWcard' : Fintype.card W = 8 := by rw [← Nat.card_eq_fintype_card]; exact hWcard
  have horbit : ∀ w ∈ W, w ≠ 1 → ∀ w' ∈ W, w' ≠ 1 → ∃ i : ℕ, (x ^ i) w = w' := by
    intro w hw hw1 w' hw' hw'1
    let f : Fin 7 → W := fun i => ⟨(x ^ (i : ℕ)) w, hpowW i w hw⟩
    have hfinj : Function.Injective f := by
      intro i j hij
      have h1 : (x ^ (i : ℕ)) w = (x ^ (j : ℕ)) w := congrArg Subtype.val hij
      have key : ∀ i j : Fin 7, (i : ℕ) ≤ j → (x ^ (i : ℕ)) w = (x ^ (j : ℕ)) w → i = j := by
        intro i j hle h
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
        have h2 : (x ^ d) w = w := by
          have : (x ^ (i : ℕ)) ((x ^ d) w) = (x ^ (i : ℕ)) w := by
            rw [← MulAut.mul_apply, ← pow_add, ← hd]; exact h.symm
          exact (x ^ (i : ℕ)).injective this
        have h3 := hfree w hw hw1 d h2
        have hj7 := j.2
        have : d = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
        omega
      rcases le_total (i : ℕ) j with h | h
      · exact key i j h h1
      · exact (key j i h h1.symm).symm
    have hsub : Finset.univ.image f ⊆ (Finset.univ : Finset W).erase 1 := by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨i, -, rfl⟩ := hu
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      have : (x ^ (i : ℕ)) w = 1 := congrArg Subtype.val h
      apply hw1
      have h' : (x ^ (i : ℕ)) w = (x ^ (i : ℕ)) 1 := by rw [this, map_one]
      exact (x ^ (i : ℕ)).injective h'
    have hcard1 : ((Finset.univ : Finset W).erase 1).card = 7 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hWcard']
    have hcard2 : (Finset.univ.image f).card = 7 := by
      rw [Finset.card_image_of_injective _ hfinj]; simp
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard1, hcard2])
    have hmem : (⟨w', hw'⟩ : W) ∈ (Finset.univ : Finset W).erase 1 := by
      rw [Finset.mem_erase]
      exact ⟨fun h => hw'1 (congrArg Subtype.val h), Finset.mem_univ _⟩
    rw [← heq, Finset.mem_image] at hmem
    obtain ⟨i, -, hi⟩ := hmem
    exact ⟨i, congrArg Subtype.val hi⟩
  have hsqW : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hV w)
  have haa : ∀ u : V, a (a u) = u := fun u => by
    have := congrArg (fun f : MulAut V => f u) ha
    simpa using this
  let ψ : W →* W := MonoidHom.codRestrict ((commMap a).comp W.subtype) W (fun w => by
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, commMap_apply]
    exact W.mul_mem (hWa w w.2) (W.inv_mem w.2))
  have hψ : ∀ w : W, ((ψ w : W) : V) = a w * (w : V)⁻¹ := fun w => rfl
  have hψker : ∀ w : W, w ∈ ψ.ker ↔ a (w : V) = w := by
    intro w
    rw [MonoidHom.mem_ker, Subtype.ext_iff, hψ]
    simp [mul_inv_eq_one]
  have hrange : ψ.range ≤ ψ.ker := by
    rintro _ ⟨w, rfl⟩
    rw [hψker, hψ, map_mul, map_inv, haa, hsqW (a w), hsqW (w : V), mul_comm]
  have hcardW : Nat.card ψ.ker * Nat.card ψ.range = 8 := by
    rw [← hWcard, ← Subgroup.index_ker ψ]
    exact Subgroup.card_mul_index ψ.ker
  have hker3 : 3 ≤ Nat.card ψ.ker := by
    have h1 : Nat.card ψ.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hrange
    by_contra h
    push Not at h
    have : Nat.card ψ.ker * Nat.card ψ.range ≤ 2 * 2 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have : Fintype ψ.ker := Fintype.ofFinite _
  have hkcard : 3 ≤ Fintype.card ψ.ker := by rw [← Nat.card_eq_fintype_card]; exact hker3
  have hs : 1 < ((Finset.univ : Finset ψ.ker).erase 1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hs
  rw [Finset.mem_erase] at hu hv
  have hu1 : (u : V) ≠ 1 := fun h => hu.1 (Subtype.ext (Subtype.ext h))
  have hv1 : (v : V) ≠ 1 := fun h => hv.1 (Subtype.ext (Subtype.ext h))
  have hua : a ((u : W) : V) = ((u : W) : V) := (hψker _).1 u.2
  have hva : a ((v : W) : V) = ((v : W) : V) := (hψker _).1 v.2
  obtain ⟨i, hi⟩ := horbit ((u : W) : V) (u : W).2 hu1 ((v : W) : V) (v : W).2 hv1
  have hxi : a * x ^ i = (x ^ i)⁻¹ * a := by
    have h1 : a * x ^ i * a = (x ^ i)⁻¹ := by
      have : a * x ^ i * a⁻¹ = (a * x * a⁻¹) ^ i := (conj_pow).symm
      rw [hai] at this
      rw [this, hax, inv_pow]
    calc a * x ^ i = a * x ^ i * a * a := by rw [mul_assoc _ a a, ha, mul_one]
      _ = (x ^ i)⁻¹ * a := by rw [h1]
  have h2 : (x ^ i) (v : V) = (u : V) := by
    have h3 : a (v : V) = (x ^ i)⁻¹ (a (u : V)) := by
      rw [← hi, ← MulAut.mul_apply, ← MulAut.mul_apply, hxi]
    rw [hva, hua] at h3
    have := congrArg (fun y => (x ^ i) y) h3
    simpa using this
  have h4 : (x ^ (i + i)) (u : V) = (u : V) := by
    rw [pow_add, MulAut.mul_apply, hi, h2]
  have h5 := hfree _ (u : W).2 hu1 (i + i) h4
  have h6 : 7 ∣ i := by omega
  have h7i : (x ^ i) (u : V) = u := by
    obtain ⟨k, hk⟩ := h6
    rw [hk, pow_mul, hx7, one_pow]; rfl
  exact huv (Subtype.ext (Subtype.ext (by rw [← hi, h7i])))

end Seven

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
