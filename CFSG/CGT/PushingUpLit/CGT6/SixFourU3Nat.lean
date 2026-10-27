module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Alg
public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Frame

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped MatrixGroups

section Conj

variable {K V : Type*} [Group K] [Group V]

theorem orderOf_conj_eq (k x : K) : orderOf (k⁻¹ * x * k) = orderOf x := by
  have h := orderOf_injective (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).injective x
  simpa [MulAut.conj_apply, mul_assoc] using h

theorem mem_centralizer_conj_iff (Y : Subgroup K) (k e : K) :
    e ∈ Subgroup.centralizer ((Y.map (MulAut.conj k).toMonoidHom : Subgroup K) : Set K) ↔
      k⁻¹ * e * k ∈ Subgroup.centralizer (Y : Set K) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro H y hy
    have h1 := H (k * y * k⁻¹) ⟨y, hy, rfl⟩
    calc y * (k⁻¹ * e * k) = k⁻¹ * ((k * y * k⁻¹) * e) * k := by group
      _ = k⁻¹ * (e * (k * y * k⁻¹)) * k := by rw [h1]
      _ = (k⁻¹ * e * k) * y := by group
  · rintro H _ ⟨y, hy, rfl⟩
    have h1 := H y hy
    calc (MulAut.conj k).toMonoidHom y * e = k * (y * (k⁻¹ * e * k)) * k⁻¹ := by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]; group
      _ = k * ((k⁻¹ * e * k) * y) * k⁻¹ := by rw [h1]
      _ = e * (MulAut.conj k).toMonoidHom y := by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]; group

theorem NatQ.conj {θ : K →* MulAut V} {Y : Subgroup K} {m : ℕ} (h : NatQ θ Y m) (k : K) :
    NatQ θ (Y.map (MulAut.conj k).toMonoidHom) m := by
  have hfix : ∀ v : V, v ∈ fixQ θ (Y.map (MulAut.conj k).toMonoidHom) ↔
      θ k⁻¹ v ∈ fixQ θ Y := fun v => by
    rw [fixQ_conj, Subgroup.mem_comap]
    rfl
  refine ⟨fun e he hco v => ?_, fun e he y hy hy1 hyo hyc v hv => ?_⟩
  · rw [hfix]
    have he' := (mem_centralizer_conj_iff Y k e).mp he
    have hco' : Nat.Coprime (orderOf (k⁻¹ * e * k)) m := by rwa [orderOf_conj_eq]
    have h1 := h.triv _ he' hco' (θ k⁻¹ v)
    have e1 : θ (k⁻¹ * e * k) (θ k⁻¹ v) = θ k⁻¹ (θ e v) := by
      rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
      congr 2
      group
    rw [e1] at h1
    simpa [map_mul, map_inv] using h1
  · obtain ⟨y₀, hy₀, rfl⟩ := hy
    have he' := (mem_centralizer_conj_iff Y k e).mp he
    have hy₀1 : y₀ ≠ 1 := fun hh => hy1 (by simp [hh])
    have hord : orderOf ((MulAut.conj k).toMonoidHom y₀) = orderOf y₀ := by
      have := orderOf_conj_eq k⁻¹ y₀
      rw [inv_inv] at this
      simpa [MulAut.conj_apply] using this
    rw [hord] at hyo hyc
    rw [hfix]
    refine h.fpf _ he' y₀ hy₀ hy₀1 hyo hyc (θ k⁻¹ v) ?_
    have hv' := (hfix _).mp hv
    · have hv2 : θ k⁻¹ (θ (e * (MulAut.conj k).toMonoidHom y₀) v * v⁻¹) ∈ fixQ θ Y := by
        rw [← hfix]
        exact hv
      have e1 : θ (k⁻¹ * e * k * y₀) (θ k⁻¹ v) = θ k⁻¹ (θ (e * (MulAut.conj k).toMonoidHom y₀) v) := by
        rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
        congr 2
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
        group
      rw [e1]
      simpa [map_mul, map_inv] using hv2

end Conj

section Data

variable {K V : Type*} [Group K] [Group V]

structure NatQData (θ : K →* MulAut V) (Y : Subgroup K) (n : ℕ) where
  φ : ↥Y ≃* SL(2, GaloisField 2 n)
  Ψ : V →* Multiplicative (Fin 2 → GaloisField 2 n)
  Ψ_surj : Function.Surjective Ψ
  Ψ_ker : Ψ.ker = fixQ θ Y
  Ψ_equiv : ∀ (y : ↥Y) (v : V), Ψ (θ (y : K) v) = Multiplicative.ofAdd
    (((φ y : SL(2, GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
      (Multiplicative.toAdd (Ψ v)))

theorem sl_pow_mulVec_eq {F : Type*} [Field F] (M : SL(2, F)) (w : Fin 2 → F) (c : F)
    (h : (M : Matrix (Fin 2) (Fin 2) F).mulVec w = c • w) (k : ℕ) :
    ((M ^ k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = c ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ih,
      Matrix.mulVec_smul, h, smul_smul, pow_succ]

variable {θ : K →* MulAut V} {Y : Subgroup K} {n : ℕ}

theorem NatQData.exists_scalar (D : NatQData θ Y n) {e : K}
    (he : e ∈ Subgroup.centralizer (Y : Set K)) :
    ∃ ℓ : GaloisField 2 n, ∀ v : V,
      Multiplicative.toAdd (D.Ψ (θ e v)) = ℓ • Multiplicative.toAdd (D.Ψ v) := by
  classical
  have hcomm : ∀ y : ↥Y, e * (y : K) = (y : K) * e := fun y =>
    (Subgroup.mem_centralizer_iff.mp he (y : K) y.2).symm
  have hker : ∀ c : V, D.Ψ c = 1 → D.Ψ (θ e c) = 1 := by
    intro c hc
    have hc' : c ∈ fixQ θ Y := by rw [← D.Ψ_ker]; exact hc
    rw [← MonoidHom.mem_ker, D.Ψ_ker, mem_fixQ]
    intro y hy
    have h1 := mem_fixQ.mp hc' y hy
    calc θ y (θ e c) = θ (y * e) c := by rw [map_mul, MulAut.mul_apply]
      _ = θ (e * y) c := by rw [(hcomm ⟨y, hy⟩).symm]
      _ = θ e (θ y c) := by rw [map_mul, MulAut.mul_apply]
      _ = θ e c := by rw [h1]
  obtain ⟨s, hs⟩ : ∃ s : (Fin 2 → GaloisField 2 n) → V,
      ∀ w, D.Ψ (s w) = Multiplicative.ofAdd w :=
    ⟨fun w => (D.Ψ_surj (Multiplicative.ofAdd w)).choose,
      fun w => (D.Ψ_surj (Multiplicative.ofAdd w)).choose_spec⟩
  let E : (Fin 2 → GaloisField 2 n) → (Fin 2 → GaloisField 2 n) :=
    fun w => Multiplicative.toAdd (D.Ψ (θ e (s w)))
  have hE : ∀ v : V, E (Multiplicative.toAdd (D.Ψ v)) = Multiplicative.toAdd (D.Ψ (θ e v)) := by
    intro v
    obtain ⟨w, hw⟩ : ∃ w, w = Multiplicative.toAdd (D.Ψ v) := ⟨_, rfl⟩
    rw [← hw]
    have h1 : D.Ψ (s w * v⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, hw, ofAdd_toAdd, mul_inv_cancel]
    have hc : s w = (s w * v⁻¹) * v := by group
    show Multiplicative.toAdd (D.Ψ (θ e (s w))) = _
    rw [hc, map_mul, map_mul, hker _ h1, one_mul]
  have hEadd : ∀ a b, E (a + b) = E a + E b := by
    intro a b
    have h1 : D.Ψ (s a * s b) = Multiplicative.ofAdd (a + b) := by
      rw [map_mul, hs, hs, ofAdd_add]
    have h2 := hE (s a * s b)
    rw [h1, toAdd_ofAdd, map_mul, map_mul, toAdd_mul] at h2
    rw [h2]
  have hEcomm : ∀ (g : SL(2, GaloisField 2 n)) (w : Fin 2 → GaloisField 2 n),
      E ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w) =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (E w) := by
    intro g w
    obtain ⟨y, rfl⟩ := D.φ.surjective g
    have h1 : D.Ψ (θ (y : K) (s w)) = Multiplicative.ofAdd
        (((D.φ y : SL(2, GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w) := by
      rw [D.Ψ_equiv, hs, toAdd_ofAdd]
    have h2 := hE (θ (y : K) (s w))
    rw [h1, toAdd_ofAdd] at h2
    rw [h2]
    have e1 : θ e (θ (y : K) (s w)) = θ (y : K) (θ e (s w)) := by
      rw [← MulAut.mul_apply, ← map_mul, hcomm y, map_mul, MulAut.mul_apply]
    rw [e1, D.Ψ_equiv, toAdd_ofAdd]
  obtain ⟨ℓ, hℓ⟩ := exists_smul_of_comm_sl2 E hEadd hEcomm
  refine ⟨ℓ, fun v => ?_⟩
  rw [← hE v, hℓ]

theorem NatQData.scalar_pow [Finite K] (D : NatQData θ Y n) {e : K} {ℓ : GaloisField 2 n}
    (hℓ : ∀ v : V, Multiplicative.toAdd (D.Ψ (θ e v)) = ℓ • Multiplicative.toAdd (D.Ψ v)) :
    ℓ ^ orderOf e = 1 ∧ ℓ ≠ 0 := by
  have hk : ∀ (k : ℕ) (v : V), Multiplicative.toAdd (D.Ψ (θ (e ^ k) v)) =
      ℓ ^ k • Multiplicative.toAdd (D.Ψ v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ' e k, map_mul, MulAut.mul_apply, hℓ, ih, smul_smul, pow_succ' ℓ k]
  obtain ⟨v, hv⟩ := D.Ψ_surj (Multiplicative.ofAdd (Pi.single 0 1))
  have h1 := hk (orderOf e) v
  rw [pow_orderOf_eq_one, map_one, MulAut.one_apply, hv, toAdd_ofAdd] at h1
  have h2 := congrFun h1 0
  simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] at h2
  have hpos : 0 < orderOf e := orderOf_pos e
  refine ⟨h2.symm, fun h0 => ?_⟩
  rw [h0, zero_pow hpos.ne'] at h2
  exact one_ne_zero h2

theorem NatQData.natQ [Finite K] (D : NatQData θ Y n) (hn : n ≠ 0) : NatQ θ Y (2 ^ n - 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  have hFlt : ∀ ℓ : GaloisField 2 n, ℓ ≠ 0 → ℓ ^ (2 ^ n - 1) = 1 := by
    intro ℓ hℓ
    let _ := Fintype.ofFinite (GaloisField 2 n)
    have := FiniteField.pow_card_sub_one_eq_one ℓ hℓ
    rwa [← Nat.card_eq_fintype_card, hcardF] at this
  refine ⟨fun e he hco v => ?_, fun e he y hy hy1 hyo hyc v hv => ?_⟩
  · obtain ⟨ℓ, hℓ⟩ := D.exists_scalar he
    obtain ⟨hpow, hne⟩ := D.scalar_pow hℓ
    have hl1 : ℓ = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hpow, hFlt ℓ hne⟩
      rwa [hco, pow_one] at this
    rw [← D.Ψ_ker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    apply Multiplicative.toAdd.injective
    rw [hℓ, hl1, one_smul]
  · obtain ⟨ℓ, hℓ⟩ := D.exists_scalar he
    obtain ⟨hpow, hne⟩ := D.scalar_pow hℓ
    rw [← D.Ψ_ker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hv
    rw [← D.Ψ_ker, MonoidHom.mem_ker]
    have hv' : D.Ψ (θ (e * y) v) = D.Ψ v := hv
    set w : Fin 2 → GaloisField 2 n := Multiplicative.toAdd (D.Ψ v) with hw
    set M : SL(2, GaloisField 2 n) := D.φ ⟨y, hy⟩ with hM
    have hMw : ℓ • (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w = w := by
      have h1 := congrArg Multiplicative.toAdd hv'
      have h2 : D.Ψ (θ y v) = Multiplicative.ofAdd
          ((M : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w) := D.Ψ_equiv ⟨y, hy⟩ v
      rw [map_mul, MulAut.mul_apply, hℓ, h2, toAdd_ofAdd] at h1
      exact h1
    by_contra hw0
    have hw0' : w ≠ 0 := by
      intro h0
      apply hw0
      have : D.Ψ v = Multiplicative.ofAdd w := by rw [hw]; exact (ofAdd_toAdd _).symm
      rw [this, h0]
      rfl
    have hMw' : (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w = ℓ⁻¹ • w := by
      calc (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w
          = ℓ⁻¹ • (ℓ • (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w) := by
            rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        _ = ℓ⁻¹ • w := by rw [hMw]
    set t := orderOf y with ht
    have hMt : M ^ t = 1 := by
      rw [hM, ← map_pow]
      have : (⟨y, hy⟩ : ↥Y) ^ t = 1 := Subtype.ext (by simp [ht])
      rw [this, map_one]
    have h2 := sl_pow_mulVec_eq M w ℓ⁻¹ hMw' t
    rw [hMt] at h2
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0' (funext hall)
    have h3 := congrFun h2 i
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul] at h3
    have h4 : (ℓ⁻¹) ^ t = 1 := by
      have := mul_right_cancel₀ hi (h3.symm.trans (one_mul _).symm)
      exact this
    have h5 : ℓ ^ t = 1 := by
      rw [← inv_inv ℓ, inv_pow, h4, inv_one]
    have hl1 : ℓ = 1 := by
      have := pow_gcd_eq_one.mpr ⟨h5, hFlt ℓ hne⟩
      rwa [hyc, pow_one] at this
    rw [hl1, one_smul] at hMw
    have hMo : Odd (orderOf M) := Odd.of_dvd_nat hyo (orderOf_dvd_of_pow_eq_one hMt)
    have hM1 : M ≠ 1 := by
      intro hM1
      have : D.φ ⟨y, hy⟩ = D.φ 1 := by rw [← hM, hM1, map_one]
      have := D.φ.injective this
      exact hy1 (congrArg Subtype.val this)
    exact hw0' (eq_zero_of_fixed_vec_of_odd_order hMo hM1 hMw)

end Data

end CFSG.CGT.PushingUpLit.CGT6
