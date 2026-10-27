module

public import CFSG.CGT.Stroth77.Section223Step

public section

namespace CFSG.CGT.Stroth77

open CFSG.GroupTheory.HuppertProduct (mho_le_of_forall pow_mem_mho conj_mem_mho)

namespace S223

variable {G : Type} [Group G]

theorem conj_mem_of_mem_sup {K L H : Subgroup G} {g : G}
    (hK : ∀ k ∈ K, g * k * g⁻¹ ∈ H) (hL : ∀ l ∈ L, g * l * g⁻¹ ∈ H) {y : G}
    (hy : y ∈ K ⊔ L) : g * y * g⁻¹ ∈ H := by
  have hle : K ⊔ L ≤ H.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun k hk => by simpa [MulAut.conj_apply] using hK k hk)
      (fun l hl => by simpa [MulAut.conj_apply] using hL l hl)
  simpa [MulAut.conj_apply] using hle hy

theorem mem_normalizer_mho_sup_omegaIn [Finite G] {D : Subgroup G}
    (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (N i : ℕ) {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer
      ((GroupTheory.HuppertProduct.mho D N ⊔ omegaIn i D : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => conj_mem_of_mem_sup (fun k hk => ?_)
    (fun l hl => ?_) hy
  · exact Subgroup.mem_sup_left
      (conj_mem_mho (fun s hs => (Subgroup.mem_normalizer_iff.mp hg s).mp hs) hk)
  · have := conj_mem_omegaIn hcomm (inv_mem hg) hl
    rw [inv_inv] at this
    exact Subgroup.mem_sup_right this

theorem zsmul_eq_zero_of_dvd {k : ℕ} {N : ℤ} (h : (2 ^ k : ℤ) ∣ N) (z : ZMod (2 ^ k)) :
    N • z = 0 := by
  obtain ⟨q, rfl⟩ := h
  have h0 : ((2 ^ k : ℕ) : ZMod (2 ^ k)) = 0 := ZMod.natCast_self _
  push_cast at h0
  rw [zsmul_eq_mul]
  push_cast
  rw [h0, zero_mul, zero_mul]

theorem card_two_torsion_zmod_two_pow {m : ℕ} (hm : 1 ≤ m) :
    Nat.card {z : ZMod (2 ^ m) // (2 : ℤ) • z = 0} = 2 := by
  have h1 : (2 : ℤ) • ((2 : ZMod (2 ^ m)) ^ (m - 1)) = 0 := by
    rw [two_zsmul, ← two_mul]
    exact two_mul_two_pow_pred m
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨0, smul_zero _⟩, ⟨2 ^ (m - 1), h1⟩,
    fun h => two_pow_pred_ne_zero hm (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨z, hz⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases zmod_two_pow_eq_zero_or_of_add_self z (by rwa [two_zsmul] at hz) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem exists_zsmul_eq_of_four_zsmul_eq_zero {n : ℕ} (hn : 2 ≤ n) {z : ZMod (2 ^ n)}
    (hz : (4 : ℤ) • z = 0) : ∃ w : ZMod (2 ^ n), (2 ^ (n - 2) : ℤ) • w = z := by
  have hN : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add, show 2 + (n - 2) = n by omega]
  have hz' : ((4 * z.val : ℕ) : ZMod (2 ^ n)) = 0 := by
    rw [zsmul_eq_mul] at hz
    simpa [Nat.cast_mul, ZMod.natCast_zmod_val, Int.cast_ofNat] using hz
  have hdiv : 2 ^ n ∣ 4 * z.val := (ZMod.natCast_eq_zero_iff _ _).mp hz'
  have h4dvd : 4 * 2 ^ (n - 2) ∣ 4 * z.val := by
    rw [← hN]
    exact hdiv
  obtain ⟨q, hq⟩ := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp h4dvd
  refine ⟨(q : ZMod (2 ^ n)), ?_⟩
  have hcast : ((2 ^ (n - 2) * q : ℕ) : ZMod (2 ^ n)) = z := by
    rw [← hq, ZMod.natCast_zmod_val]
  rw [zsmul_eq_mul]
  push_cast at hcast ⊢
  exact hcast

theorem card_coord_torsion_torus (k : Fin 3 → ℕ) (c : Fin 3 → ℤ) :
    Nat.card {v : Torus k // ∀ i, c i • v i = 0} =
      ∏ i, Nat.card {z : ZMod (2 ^ k i) // c i • z = 0} := by
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i (z : ZMod (2 ^ k i)) => c i • z = 0)),
    Nat.card_pi]

end S223

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem A_eq_mho_sup_omegaIn_one (h : F.IsD D dD) (hmn : τ.m < τ.n) :
    F.A = GroupTheory.HuppertProduct.mho D (2 ^ (τ.n - 2)) ⊔ omegaIn 1 D := by
  have hcomm := h.comm
  have hm : 1 ≤ τ.k 0 := h.isTyped.one_le_k 0
  have hmn' : τ.k 0 < τ.k 1 := hmn
  have hk2 : τ.k 2 = τ.k 1 := τ.k_two
  have hn : 2 ≤ τ.k 1 := by omega
  show F.A = GroupTheory.HuppertProduct.mho D (2 ^ (τ.k 1 - 2)) ⊔ omegaIn 1 D
  set M := GroupTheory.HuppertProduct.mho D (2 ^ (τ.k 1 - 2))
  let c : Fin 3 → ℤ := ![2, 4, 4]
  have hdvd : ∀ i, (2 ^ τ.k i : ℤ) ∣ c i * 2 ^ (τ.k 1 - 2) := by
    intro i
    fin_cases i
    · show (2 ^ τ.k 0 : ℤ) ∣ 2 * 2 ^ (τ.k 1 - 2)
      rw [← pow_succ']
      exact pow_dvd_pow 2 (by omega)
    · show (2 ^ τ.k 1 : ℤ) ∣ 4 * 2 ^ (τ.k 1 - 2)
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
      exact pow_dvd_pow 2 (by omega)
    · show (2 ^ τ.k 2 : ℤ) ∣ 4 * 2 ^ (τ.k 1 - 2)
      rw [hk2, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
      exact pow_dvd_pow 2 (by omega)
  have htwo : ∀ i, ∃ d : ℤ, c i = d * 2 := by
    intro i
    fin_cases i
    exacts [⟨1, rfl⟩, ⟨2, rfl⟩, ⟨2, rfl⟩]
  have hfour : ∀ i, ∃ d : ℤ, (4 : ℤ) = d * c i := by
    intro i
    fin_cases i
    exacts [⟨2, rfl⟩, ⟨1, rfl⟩, ⟨1, rfl⟩]
  let T₀ : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ D, ∀ i, c i • dD.e (Additive.ofMul (⟨x, hx⟩ : D)) i = 0}
      mul_mem' := by
        rintro a b ⟨ha, hPa⟩ ⟨hb, hPb⟩
        refine ⟨mul_mem ha hb, fun i => ?_⟩
        have e : dD.e (Additive.ofMul (⟨a * b, mul_mem ha hb⟩ : D)) =
            dD.e (Additive.ofMul (⟨a, ha⟩ : D)) + dD.e (Additive.ofMul (⟨b, hb⟩ : D)) := by
          rw [← map_add, ← ofMul_mul]
          rfl
        rw [e, Pi.add_apply, smul_add, hPa i, hPb i, add_zero]
      one_mem' := ⟨one_mem _, fun i => by
        rw [show (⟨1, one_mem D⟩ : D) = 1 from rfl, ofMul_one, map_zero, Pi.zero_apply,
          smul_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, hPa⟩
        refine ⟨inv_mem ha, fun i => ?_⟩
        have e : dD.e (Additive.ofMul (⟨a⁻¹, inv_mem ha⟩ : D)) =
            -dD.e (Additive.ofMul (⟨a, ha⟩ : D)) := by
          rw [← map_neg, ← ofMul_inv]
          rfl
        rw [e, Pi.neg_apply, smul_neg, hPa i, neg_zero] }
  have hT₀ : ∀ {x : G}, x ∈ T₀ →
      ∃ hx : x ∈ D, ∀ i, c i • dD.e (Additive.ofMul (⟨x, hx⟩ : D)) i = 0 := fun hx => hx
  have hmhoT : M ≤ T₀ := by
    refine mho_le_of_forall fun g hg => ⟨pow_mem hg _, fun i => ?_⟩
    have e : dD.e (Additive.ofMul (⟨g ^ 2 ^ (τ.k 1 - 2), pow_mem hg _⟩ : D)) =
        (2 ^ (τ.k 1 - 2) : ℕ) • dD.e (Additive.ofMul (⟨g, hg⟩ : D)) := by
      rw [← map_nsmul, ← ofMul_pow]
      rfl
    rw [e, Pi.smul_apply, ← natCast_zsmul, smul_smul]
    apply S223.zsmul_eq_zero_of_dvd
    push_cast
    exact hdvd i
  have hΩT : omegaIn 1 D ≤ T₀ := by
    intro x hx
    have hxD := omegaIn_le 1 D hx
    have h2 : (2 : ℤ) • dD.e (Additive.ofMul (⟨x, hxD⟩ : D)) = 0 :=
      (dD.mul_self_eq_one_iff _).mp (Subtype.ext (mul_self_eq_one_of_mem_omegaIn_one hcomm hx))
    refine ⟨hxD, fun i => ?_⟩
    have h2i : (2 : ℤ) • dD.e (Additive.ofMul (⟨x, hxD⟩ : D)) i = 0 := by
      rw [← Pi.smul_apply, h2, Pi.zero_apply]
    obtain ⟨d, hd⟩ := htwo i
    rw [hd, mul_smul, h2i, smul_zero]
  have hXT : M ⊔ omegaIn 1 D ≤ T₀ := sup_le hmhoT hΩT
  have hback : ∀ (x : G) (hx : x ∈ D),
      (∀ i, c i • dD.e (Additive.ofMul (⟨x, hx⟩ : D)) i = 0) →
        x ∈ M ⊔ omegaIn 1 D := by
    intro x hx hP
    obtain ⟨v, hv⟩ : ∃ v, v = dD.e (Additive.ofMul (⟨x, hx⟩ : D)) := ⟨_, rfl⟩
    rw [← hv] at hP
    let z : Torus τ.k := Pi.single 0 (v 0)
    have hwex : ∀ i, ∃ wi : ZMod (2 ^ τ.k i), (2 ^ (τ.k 1 - 2) : ℤ) • wi = (v - z) i := by
      intro i
      fin_cases i
      · exact ⟨0, by simp [z]⟩
      · obtain ⟨w, hw⟩ := S223.exists_zsmul_eq_of_four_zsmul_eq_zero hn (hP 1)
        exact ⟨w, by simpa [z] using hw⟩
      · obtain ⟨w, hw⟩ := S223.exists_zsmul_eq_of_four_zsmul_eq_zero (hk2 ▸ hn) (hP 2)
        refine ⟨w, ?_⟩
        rw [← hk2]
        simpa [z] using hw
    choose w hw using hwex
    have hwv : (2 ^ (τ.k 1 - 2) : ℕ) • (w : Torus τ.k) + z = v := by
      funext i
      rw [Pi.add_apply, Pi.smul_apply, ← natCast_zsmul]
      push_cast
      rw [hw i, Pi.sub_apply, sub_add_cancel]
    have hz2 : z + z = 0 := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp only [z, Pi.add_apply, Pi.single_eq_same, Pi.zero_apply]
        rw [← two_zsmul]
        exact hP 0
      · simp [z, Pi.single_eq_of_ne hi]
    have hzΩ : ((Additive.toMul (dD.e.symm z) : D) : G) ∈ omegaIn 1 D := by
      refine mem_omegaIn_one_of_mul_self (Additive.toMul (dD.e.symm z) : D).2 ?_
      have : (Additive.toMul (dD.e.symm z) : D) * Additive.toMul (dD.e.symm z) = 1 := by
        rw [dD.mul_self_eq_one_iff, two_zsmul]
        simpa using hz2
      exact congrArg Subtype.val this
    have hxeq : (⟨x, hx⟩ : D) =
        (Additive.toMul (dD.e.symm w) : D) ^ (2 ^ (τ.k 1 - 2)) *
          Additive.toMul (dD.e.symm z) := by
      apply Additive.ofMul.injective
      apply dD.e.injective
      rw [ofMul_mul, map_add, ofMul_pow, map_nsmul, ofMul_toMul, ofMul_toMul,
        AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hwv, hv]
    have hx' : x = ((Additive.toMul (dD.e.symm w) : D) : G) ^ (2 ^ (τ.k 1 - 2)) *
        ((Additive.toMul (dD.e.symm z) : D) : G) := congrArg Subtype.val hxeq
    rw [hx']
    exact mul_mem (Subgroup.mem_sup_left (pow_mem_mho (Additive.toMul (dD.e.symm w) : D).2))
      (Subgroup.mem_sup_right hzΩ)
  have hcard : Nat.card (M ⊔ omegaIn 1 D : Subgroup G) = Nat.card F.A := by
    have eqv : (M ⊔ omegaIn 1 D : Subgroup G) ≃
        {v : Torus τ.k // ∀ i, c i • v i = 0} :=
      { toFun := fun x => ⟨dD.e (Additive.ofMul ⟨x.1, (hT₀ (hXT x.2)).1⟩), (hT₀ (hXT x.2)).2⟩
        invFun := fun v => ⟨((Additive.toMul (dD.e.symm v.1) : D) : G),
          hback _ (Additive.toMul (dD.e.symm v.1) : D).2 (by simpa using v.2)⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
    rw [Nat.card_congr eqv, S223.card_coord_torsion_torus, Fin.prod_univ_three, F.card_A]
    show Nat.card {z : ZMod (2 ^ τ.k 0) // (2 : ℤ) • z = 0} *
        Nat.card {z : ZMod (2 ^ τ.k 1) // (4 : ℤ) • z = 0} *
        Nat.card {z : ZMod (2 ^ τ.k 2) // (4 : ℤ) • z = 0} = 32
    rw [S223.card_two_torsion_zmod_two_pow hm, card_four_torsion_zmod_two_pow _ hn,
      card_four_torsion_zmod_two_pow _ (hk2 ▸ hn)]
  have hXΩ₂ : M ⊔ omegaIn 1 D ≤ omegaIn 2 D := by
    intro x hx
    obtain ⟨hxD, hP⟩ := hT₀ (hXT hx)
    refine mem_omegaIn_of_pow_eq_one hxD ?_
    have h4 : (4 : ℤ) • dD.e (Additive.ofMul (⟨x, hxD⟩ : D)) = 0 := by
      funext i
      rw [Pi.smul_apply, Pi.zero_apply]
      obtain ⟨d, hd⟩ := hfour i
      rw [hd, mul_smul, hP i, smul_zero]
    have hx4 : (⟨x, hxD⟩ : D) ^ (2 ^ 2) = 1 := by
      apply Additive.ofMul.injective
      apply dD.e.injective
      rw [ofMul_pow, map_nsmul, ofMul_one, map_zero, ← natCast_zsmul]
      exact_mod_cast h4
    simpa using congrArg Subtype.val hx4
  exact (h.eq_A_of_le_omegaIn_two le_sup_right hXΩ₂ hcard
    (S223.mem_normalizer_mho_sup_omegaIn hcomm _ 1 h.uv_mem_normalizer)
    (S223.mem_normalizer_mho_sup_omegaIn hcomm _ 1 h.t_mem_normalizer)).symm

theorem normalizer_le_normalizer_A (h : F.IsD D dD) (hmn : τ.m < τ.n) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (F.A : Set G) := by
  rw [h.A_eq_mho_sup_omegaIn_one hmn]
  exact fun g hg => S223.mem_normalizer_mho_sup_omegaIn h.comm _ 1 hg

end StrothFrame.IsD

end CFSG.CGT.Stroth77
