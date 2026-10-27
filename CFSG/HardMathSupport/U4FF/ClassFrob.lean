module

public import CFSG.HardMathSupport.U4FF.ClassTmodWt

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso fixedSub)


section Frob

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
variable (E : Type) [Field E] [Algebra K E] [CharP E 2]

private theorem ylocC_fixed (φ : E →+* E) (a b c : Bool) (x : Fin (locM a b c)) :
    φ (ylocC a b c E x) = ylocC a b c E x := by
  have hφ : φ.comp (f2 E) = f2 E := RingHom.ext_zmod _ _
  obtain ⟨y, hy⟩ : ∃ y : ZMod 2, ylocC a b c E x = f2 E y := by
    rw [ylocC, yloc_eq_map]
    exact ⟨_, rfl⟩
  rw [hy]
  exact DFunLike.congr_fun hφ y

theorem comp_hwv (φ : E →+* E) (l : Lbl n) : φ ∘ hwv l E = hwv l E := by
  funext x
  rw [Function.comp_apply, hwv, pureTensor_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => ylocC_fixed E φ (l.a i) (l.b i) (l.c i) (x i)

theorem map_mulVec_hwv (φ : E →+* E) (l : Lbl n) (M : Matrix (TIdx l) (TIdx l) E) :
    (M.map φ) *ᵥ hwv l E = φ ∘ (M *ᵥ hwv l E) := by
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec, comp_hwv E φ l]

theorem fixed_frob [Finite E] (hK : Nat.card K = (2 ^ n) ^ 2) (φ : E →+* E) (l : Lbl n)
    {v : TIdx l → E} (hv : ∀ u ∈ UpperU K n, ((Tmod K l E u).map φ) *ᵥ v = v) :
    ∃ c : E, v = c • hwv l E := by
  have hbij : Function.Bijective φ :=
    ⟨φ.injective, Finite.surjective_of_injective φ.injective⟩
  let ψ := RingEquiv.ofBijective φ hbij
  set w : TIdx l → E := fun x => ψ.symm (v x) with hwdef
  have hφw : φ ∘ w = v := funext fun x => ψ.apply_symm_apply (v x)
  have hwfix : w ∈ fixedSub (Trep K l E) (UpperU K n) := by
    intro u hu
    rw [Trep_apply]
    funext i
    apply φ.injective
    rw [RingHom.map_mulVec, hφw, hv u hu, ← hφw]
    rfl
  rw [(Tmod_fixed_and_irreducible (k := E) hK l).1, Submodule.mem_span_singleton] at hwfix
  obtain ⟨c, hc⟩ := hwfix
  refine ⟨φ c, ?_⟩
  rw [← hφw, ← hc]
  funext x
  have := congrFun (comp_hwv E φ l) x
  simp only [Function.comp_apply] at this
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, this]

theorem e_modEq_of_frob [Finite E] (hK : Nat.card K = (2 ^ n) ^ 2) {l : Lbl n} {κ : Type}
    [Fintype κ] [DecidableEq κ] (R : SU4 K n →* Matrix κ κ E) (d : ℕ)
    (hR : ∀ g, (R g).map (iterateFrobenius E 2 d) = R g)
    (Φ : (matRep (Tmod K l E)).Equiv (matRep R)) :
    2 ^ d * l.e1 ≡ l.e1 [MOD (2 ^ n) ^ 2 - 1] ∧ 2 ^ d * l.e2 ≡ l.e2 [MOD 2 ^ n - 1] := by
  classical
  set φ : E →+* E := iterateFrobenius E 2 d with hφ
  obtain ⟨P, Q, h⟩ := MatIso.exists_of_equiv Φ
  have h1 := h.map φ
  have hR' : matMap φ R = R := MonoidHom.ext fun g => hR g
  rw [hR'] at h1
  have h2 := h.trans h1.symm
  obtain ⟨A, hA⟩ : ∃ A, A = Q.map φ * P := ⟨_, rfl⟩
  rw [← hA] at h2
  have hfix : ∀ u ∈ UpperU K n, ((Tmod K l E u).map φ) *ᵥ (A *ᵥ hwv l E) = A *ᵥ hwv l E := by
    intro u hu
    have hc := h2.comm u
    rw [matMap_apply] at hc
    rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec]
    have hT : Tmod K l E u *ᵥ hwv l E = hwv l E :=
      TmodΦ_upper_fix hK l (fun i => frobTw K E i) hu
    rw [hT]
  obtain ⟨c, hc⟩ := fixed_frob E hK φ l hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    apply hwv_ne_zero (k := E) l
    have h3 := h2.inv_mul
    rw [← Matrix.one_mulVec (hwv l E), ← h3, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  have hchar : ∀ (u v : Kˣ) (hv : (v : K) ^ 2 ^ n = v),
      algebraMap K E ((u : K) ^ l.e1 * (v : K) ^ l.e2) =
        algebraMap K E ((u : K) ^ l.e1 * (v : K) ^ l.e2) ^ (2 ^ d) := by
    intro u v hv
    have h3 := congrArg (fun M => M *ᵥ hwv l E) (h2.comm (torusElt hK u v hv))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Tmod_torus_weight (k := E) hK l u v hv,
      Matrix.mulVec_smul, hc, Matrix.mulVec_smul, matMap_apply, map_mulVec_hwv E φ l,
      Tmod_torus_weight (k := E) hK l u v hv, smul_smul] at h3
    have h4 : φ ∘ (algebraMap K E ((u : K) ^ l.e1 * (v : K) ^ l.e2) • hwv l E) =
        φ (algebraMap K E ((u : K) ^ l.e1 * (v : K) ^ l.e2)) • hwv l E := by
      funext x
      have := congrFun (comp_hwv E φ l) x
      simp only [Function.comp_apply] at this
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, this]
    rw [h4, smul_smul] at h3
    have h5 := smul_left_injective E (hwv_ne_zero (k := E) l) h3
    have h6 : algebraMap K E ((u : K) ^ l.e1 * (v : K) ^ l.e2) =
        φ (algebraMap K E ((u : K) ^ l.e1 * (v : K) ^ l.e2)) :=
      mul_left_cancel₀ hc0 (by linear_combination h5)
    rw [hφ, iterateFrobenius_def] at h6
    exact h6
  have hK' : ∀ (u v : Kˣ) (hv : (v : K) ^ 2 ^ n = v),
      ((u : K) ^ l.e1 * (v : K) ^ l.e2) ^ 2 ^ d = (u : K) ^ l.e1 * (v : K) ^ l.e2 := by
    intro u v hv
    apply (algebraMap K E).injective
    rw [map_pow]
    exact (hchar u v hv).symm
  have hexp : ∀ (u v : Kˣ) (hv : (v : K) ^ 2 ^ n = v),
      (u : K) ^ (2 ^ d * l.e1) * (v : K) ^ (2 ^ d * l.e2) = (u : K) ^ l.e1 * (v : K) ^ l.e2 := by
    intro u v hv
    rw [← hK' u v hv, mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ d) l.e1,
      mul_comm (2 ^ d) l.e2]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (2 ^ n) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = t + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel h2n).symm⟩
  have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [ht, Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hdvd : 2 ^ n + 1 ∣ orderOf g := by
    rw [hord, hfac]
    exact dvd_mul_left _ _
  have e : (2 ^ n + 1) * 2 ^ n = orderOf g + (2 ^ n + 1) := by
    rw [hord, hfac, ht, Nat.add_sub_cancel]
    ring
  have hgn : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  obtain ⟨w, hw⟩ : ∃ w : Kˣ, w = g ^ (2 ^ n + 1) := ⟨_, rfl⟩
  have hwpow : w ^ 2 ^ n = w := by
    rw [hw, ← pow_mul, e, pow_add g (orderOf g) (2 ^ n + 1), hgn, one_mul]
  have hvK : ((w : Kˣ) : K) ^ 2 ^ n = (w : K) := by
    rw [← Units.val_pow_eq_pow_val, hwpow]
  have hw_ord : orderOf w = 2 ^ n - 1 := by
    rw [hw, orderOf_pow_of_dvd (by positivity) hdvd, hord, hfac]
    exact Nat.mul_div_cancel _ (by positivity)
  have hone : ((1 : Kˣ) : K) ^ 2 ^ n = ((1 : Kˣ) : K) := by simp
  have hgpow : g ^ l.e1 = g ^ (2 ^ d * l.e1) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    have h := hexp g 1 hone
    simp only [Units.val_one, one_pow, mul_one] at h
    exact h.symm
  have hwpow' : w ^ l.e2 = w ^ (2 ^ d * l.e2) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    have h := hexp 1 w hvK
    simp only [Units.val_one, one_pow, one_mul] at h
    exact h.symm
  have hm1 := pow_eq_pow_iff_modEq.mp hgpow
  have hm2 := pow_eq_pow_iff_modEq.mp hwpow'
  rw [hord] at hm1
  rw [hw_ord] at hm2
  exact ⟨hm1.symm, hm2.symm⟩

end Frob

end CFSG.HardMathSupport.U4FF
