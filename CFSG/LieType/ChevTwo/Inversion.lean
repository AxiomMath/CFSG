module

public import CFSG.LieType.ChevTwo.InversionBase

public import Certificates.Certificate214001

public section

namespace CFSG.LieType.ChevTwo

namespace GL4Native

theorem chk_all :
    ∀ v : Fin 16 → ZMod 2, chk (List.ofFn v) = true :=
  Certificates.certificate214001

theorem key_matrix (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h315 : A ^ 315 = 1) (htr : A.trace = (A ^ 314).trace) : A = 1 ∨ A ^ 3 = 1 ∨ A ^ 5 = 1 := by
  have hc : chk (toL A) = true := chk_all (fun k => A (ij k).1 (ij k).2)
  unfold chk at hc
  have h315' : toL (A ^ 315) = oneL := by rw [h315, oneL_toL]
  have hne : decide (trL (toL A) ≠ trL (toL (A ^ 314))) = false := by
    rw [trL_toL, trL_toL, htr]
    simp
  simp only [powL_toL, h315', hne, decide_true, Bool.not_true, Bool.false_or] at hc
  simp only [Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with (h | h) | h
  · exact Or.inl (toL_injective (h.trans oneL_toL.symm))
  · exact Or.inr (Or.inl (toL_injective (h.trans oneL_toL.symm)))
  · exact Or.inr (Or.inr (toL_injective (h.trans oneL_toL.symm)))

end GL4Native

theorem gl4_stronglyReal (x t : GL (Fin 4) (ZMod 2))
    (ht : t ^ 2 = 1) (hxt : t * x * t⁻¹ = x⁻¹) (hx : Odd (orderOf x)) :
    orderOf x = 1 ∨ orderOf x = 3 ∨ orderOf x = 5 := by
  have hcard : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := Matrix.card_GL_field (𝔽 := ZMod 2) (n := 4)
    rw [ZMod.card] at h
    rw [h]
    simp [Fin.prod_univ_four]
  have hdvd : orderOf x ∣ 20160 := hcard ▸ orderOf_dvd_natCard x
  have hcop : Nat.Coprime (orderOf x) (2 ^ 6) := Nat.Coprime.pow_right _ hx.coprime_two_right
  have hodd315 : orderOf x ∣ 315 := by
    have h2 : orderOf x ∣ 2 ^ 6 * 315 := by simpa using hdvd
    exact hcop.dvd_of_dvd_mul_left h2
  have hx315 : x ^ 315 = 1 := orderOf_dvd_iff_pow_eq_one.mp hodd315
  have hinv : x⁻¹ = x ^ 314 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hx315
  have hcyc : ((t⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (t : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : (x : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace = ((x ^ 314 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace := by
    have h1 : ((t * x * t⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace = (x : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace := by
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, hcyc, Matrix.one_mul]
    rw [← h1, hxt, hinv]
  have hm : (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 315 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx315, Units.val_one]
  have hm314 : (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 314 = ((x ^ 314 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    rw [Units.val_pow_eq_pow_val]
  rw [← hm314] at htr
  rcases GL4Native.key_matrix _ hm htr with h | h | h
  · left
    apply orderOf_eq_one_iff.mpr
    exact Units.ext (by simpa using h)
  · have h3 : x ^ 3 = 1 := by
      apply Units.ext
      simpa [Units.val_pow_eq_pow_val] using h
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h' | h'
    · left; exact h'
    · right; left; exact h'
  · have h5 : x ^ 5 = 1 := by
      apply Units.ext
      simpa [Units.val_pow_eq_pow_val] using h
    rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one h5) with h' | h'
    · left; exact h'
    · right; right; exact h'

namespace OffNative

theorem orderOf_mem_of_finrank_le_four {U : Type}
    [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (hU : Module.finrank (ZMod 2) U ≤ 4) (g h : U ≃ₗ[ZMod 2] U) (hh : h ^ 2 = 1)
    (hhg : h * g * h⁻¹ = g⁻¹) (hg : Odd (orderOf g)) :
    orderOf g = 1 ∨ orderOf g = 3 ∨ orderOf g = 5 := by
  obtain ⟨m, hm⟩ : ∃ m, m = 4 - Module.finrank (ZMod 2) U := ⟨_, rfl⟩
  letI hM : Module (ZMod 2) (Fin m → ZMod 2) := Pi.module (Fin m) (fun _ => ZMod 2) (ZMod 2)
  letI : Module.Free (ZMod 2) (Fin m → ZMod 2) := Module.Free.pi _ _
  have hE : Module.finrank (ZMod 2) (U × (Fin m → ZMod 2)) = 4 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
    omega
  let e : (U × (Fin m → ZMod 2)) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hE, Module.finrank_fin_fun])
  let P : (U ≃ₗ[ZMod 2] U) →* ((U × (Fin m → ZMod 2)) ≃ₗ[ZMod 2] (U × (Fin m → ZMod 2))) :=
    @prodHom U (Fin m → ZMod 2) _ _ _ hM
  let Φ : (U ≃ₗ[ZMod 2] U) →* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
    { toFun := fun g => e.symm.trans ((P g).trans e)
      map_one' := by
        ext v
        simp
      map_mul' := fun g g' => by
        ext v
        simp }
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hP : P g = 1 := by
      apply LinearEquiv.ext
      intro p
      apply e.injective
      have := congrArg (fun S : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) => S (e p)) hg
      simpa [Φ] using this
    exact @prodHom_injective U (Fin m → ZMod 2) _ _ _ hM g 1 (hP.trans (map_one P).symm)
  have hΦh : (Φ h) ^ 2 = 1 := by
    rw [← map_pow, hh, map_one]
  have hΦhg : Φ h * Φ g * (Φ h)⁻¹ = (Φ g)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, hhg]
  have hord : orderOf (Φ g) = orderOf g := orderOf_injective Φ hΦinj g
  let γ := glEquivAut.symm (Φ h)
  let δ := glEquivAut.symm (Φ g)
  have hγ : γ ^ 2 = 1 := by
    simp only [γ, ← map_pow, hΦh, map_one]
  have hγδ : γ * δ * γ⁻¹ = δ⁻¹ := by
    simp only [γ, δ, ← map_mul, ← map_inv]
    rw [hhg]
  have hδ : orderOf δ = orderOf g := by
    rw [← hord]
    exact (glEquivAut.symm.orderOf_eq (Φ g)).trans rfl
  have hodd : Odd (orderOf δ) := hδ ▸ hg
  rw [← hδ]
  rcases gl4_stronglyReal δ γ hγ hγδ hodd with h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr h')

end OffNative

theorem odd_inverted_of_offender {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (a x : V ≃ₗ[ZMod 2] V) (ha : a ^ 2 = 1) (hxa : a * x * a⁻¹ = x⁻¹) (hx : Odd (orderOf x))
    (hoff : Nat.card V ≤ 4 * Nat.card (LinearMap.ker ((a : V →ₗ[ZMod 2] V) - LinearMap.id))) :
    orderOf x = 1 ∨ orderOf x = 3 ∨ orderOf x = 5 := by
  classical
  obtain ⟨j, hj⟩ := hx
  have hxn : (x ^ orderOf x) = 1 := pow_orderOf_eq_one x
  have hA2 : ∀ v, a (a v) = v := fun v => by
    have := congrArg (fun T : V ≃ₗ[ZMod 2] V => T v) ha
    simpa [pow_two] using this
  have hainv : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ha]
  have hAX : ∀ v, a (x v) = x⁻¹ (a v) := by
    intro v
    have := congrArg (fun T : V ≃ₗ[ZMod 2] V => T (a v)) hxa
    simpa [hainv, hA2] using this
  have hxinv : ∀ w, x (x⁻¹ w) = w := fun w => by
    have := congrArg (fun T : V ≃ₗ[ZMod 2] V => T w) (mul_inv_cancel x)
    simpa using this
  have hxinv' : ∀ w, x⁻¹ (x w) = w := fun w => by
    have := congrArg (fun T : V ≃ₗ[ZMod 2] V => T w) (inv_mul_cancel x)
    simpa using this
  let T : V →ₗ[ZMod 2] V := (x : V →ₗ[ZMod 2] V) - LinearMap.id
  have hTv : ∀ v, T v = x v - v := fun v => by simp [T]
  let W : Submodule (ZMod 2) V := LinearMap.range T
  let C : Submodule (ZMod 2) V := LinearMap.ker T
  have hC : ∀ c, c ∈ C ↔ x c = c := fun c => by
    simp [C, hTv, sub_eq_zero]
  have hAT : ∀ v, a (T v) = T (x⁻¹ (a v)) := by
    intro v
    have h1 : x (x⁻¹ (a v)) = a v := hxinv _
    have h2 := OffNative.neg_eq_self_of_zmod2 (x⁻¹ (a v) - a v)
    rw [neg_sub] at h2
    rw [hTv, map_sub, hAX, hTv, h1]
    exact h2.symm
  have hWx : ∀ w ∈ W, x w ∈ W := by
    rintro w ⟨v, rfl⟩
    exact ⟨x v, by simp only [T, LinearMap.sub_apply, LinearMap.id_apply, map_sub, LinearEquiv.coe_coe]⟩
  have hWa : ∀ w ∈ W, a w ∈ W := by
    rintro w ⟨v, rfl⟩
    exact ⟨x⁻¹ (a v), (hAT v).symm⟩
  have hWxi : ∀ w ∈ W, x⁻¹ w ∈ W := by
    intro w hw
    have : x⁻¹ w = a (x (a w)) := by
      rw [hAX, hA2]
    rw [this]
    exact hWa _ (hWx _ (hWa _ hw))
  have hfix : ∀ c ∈ C, ∀ k : ℕ, (x ^ k) c = c := by
    intro c hc k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, (hC c).mp hc]
  have hWpow : ∀ k : ℕ, ∀ w ∈ W, (x ^ k) w ∈ W := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', LinearEquiv.mul_apply]
      exact hWx _ (ih w hw)
  have hAxpow : ∀ (k : ℕ) (w : V), a ((x ^ k) w) = ((x⁻¹) ^ k) (a w) := by
    intro k w
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, hAX, ih, pow_succ', LinearEquiv.mul_apply]
  have htel : ∀ v, ∑ i ∈ Finset.range (orderOf x), (x ^ i) (T v) = 0 := by
    intro v
    have h : ∀ i ∈ Finset.range (orderOf x), (x ^ i) (T v) = (x ^ (i + 1)) v - (x ^ i) v := by
      intro i _
      rw [hTv, map_sub, pow_succ, LinearEquiv.mul_apply]
    rw [Finset.sum_congr rfl h]
    have := Finset.sum_range_sub (fun i => (x ^ i) v) (orderOf x)
    rw [this, hxn]
    simp
  have hodd_smul : ∀ y : V, (orderOf x) • y = y := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_eq_one_iff_odd.mpr ⟨j, hj⟩, one_smul]
  have hCW : C ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwC, v, rfl⟩
    have hfixT : ∀ i : ℕ, (x ^ i) (T v) = T v := fun i => hfix _ hwC i
    have hsum : ∑ i ∈ Finset.range (orderOf x), (x ^ i) (T v) = (orderOf x) • T v := by
      rw [Finset.sum_congr rfl (fun i _ => hfixT i), Finset.sum_const, Finset.card_range]
    have h0 := htel v
    rw [hsum, hodd_smul] at h0
    rw [h0]
    exact Submodule.zero_mem _
  have hsup : C ⊔ W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq C W
    rw [hCW, finrank_bot, add_zero] at h1
    have h2 : Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) C = Module.finrank (ZMod 2) V :=
      LinearMap.finrank_range_add_finrank_ker T
    omega

  have hmapx : W.map (x : V →ₗ[ZMod 2] V) = W := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hWx w hw
    · intro w hw
      exact ⟨x⁻¹ w, hWxi w hw, hxinv w⟩
  have hmapa : W.map (a : V →ₗ[ZMod 2] V) = W := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hWa w hw
    · intro w hw
      exact ⟨a w, hWa w hw, hA2 w⟩
  let xW : W ≃ₗ[ZMod 2] W := LinearEquiv.ofSubmodules x W W hmapx
  let aW : W ≃ₗ[ZMod 2] W := LinearEquiv.ofSubmodules a W W hmapa
  have hxW : ∀ w : W, ((xW w : W) : V) = x (w : V) := fun w => rfl
  have haW : ∀ w : W, ((aW w : W) : V) = a (w : V) := fun w => rfl
  have hxWpow : ∀ (k : ℕ) (w : W), (((xW ^ k) w : W) : V) = (x ^ k) (w : V) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ', LinearEquiv.mul_apply, hxW, ih, pow_succ', LinearEquiv.mul_apply]
  have hpow : ∀ k : ℕ, xW ^ k = 1 ↔ x ^ k = 1 := by
    intro k
    constructor
    · intro h
      apply LinearEquiv.ext
      intro v
      have hv : v ∈ C ⊔ W := by rw [hsup]; exact Submodule.mem_top
      obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      have key : ∀ u : W, (xW ^ k) u = u := fun u => by rw [h]; rfl
      have hw1 : (x ^ k) w = w := by
        have h3 := hxWpow k ⟨w, hw⟩
        rw [key] at h3
        exact h3.symm
      rw [map_add, hfix c hc k, hw1]
      rfl
    · intro h
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      rw [hxWpow, h]
      rfl
  have hordxW : orderOf xW = orderOf x := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_iff_pow_eq_one.mpr ((hpow _).mpr hxn)
    · exact orderOf_dvd_iff_pow_eq_one.mpr ((hpow _).mp (pow_orderOf_eq_one xW))
  set R : V →ₗ[ZMod 2] V := (a : V →ₗ[ZMod 2] V) - LinearMap.id with hRdef
  have hRrank : Module.finrank (ZMod 2) (LinearMap.range R) ≤ 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker R
    have h2 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have h3 : Nat.card (LinearMap.ker R) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker R) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rw [h2, h3] at hoff
    have h4 : 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ (Module.finrank (ZMod 2) (LinearMap.ker R) + 2) := by
      rw [pow_add]
      simpa [mul_comm] using hoff
    have h5 := (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp h4
    omega
  let R' : W →ₗ[ZMod 2] V := R.comp W.subtype
  have hR'rank : Module.finrank (ZMod 2) (LinearMap.range R') ≤ 2 :=
    le_trans (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)) hRrank
  let K' : Submodule (ZMod 2) W := LinearMap.ker R'
  let S : Submodule (ZMod 2) V := K'.map W.subtype
  have hSmem : ∀ s : V, s ∈ S ↔ s ∈ W ∧ a s = s := by
    intro s
    constructor
    · rintro ⟨w, hwK, rfl⟩
      refine ⟨w.2, ?_⟩
      have h0 : R (w : V) = 0 := LinearMap.mem_ker.mp hwK
      rw [hRdef, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe] at h0
      exact sub_eq_zero.mp h0
    · rintro ⟨hsW, has⟩
      refine ⟨⟨s, hsW⟩, ?_, rfl⟩
      show R s = 0
      rw [hRdef, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, has, sub_self]
  have hKS : Module.finrank (ZMod 2) K' = Module.finrank (ZMod 2) S :=
    (Submodule.finrank_map_subtype_eq W K').symm
  have hWdim : Module.finrank (ZMod 2) (LinearMap.range R') + Module.finrank (ZMod 2) K' =
      Module.finrank (ZMod 2) W :=
    LinearMap.finrank_range_add_finrank_ker R'
  let xj : V ≃ₗ[ZMod 2] V := x ^ j
  let T' : Submodule (ZMod 2) V := S.map (xj : V →ₗ[ZMod 2] V)
  have hT'fin : Module.finrank (ZMod 2) T' = Module.finrank (ZMod 2) S :=
    LinearEquiv.finrank_map_eq xj S
  have hSW : S ≤ W := fun s hs => ((hSmem s).mp hs).1
  have hT'W : T' ≤ W := by
    rintro _ ⟨s, hs, rfl⟩
    exact hWpow j s (hSW hs)
  have hST : S ⊓ T' = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvS, s, hsS, rfl⟩
    obtain ⟨hsW, has⟩ := (hSmem s).mp hsS
    have hav : a ((x ^ j) s) = (x ^ j) s := ((hSmem _).mp hvS).2
    have h1 : (x⁻¹ ^ j) s = (x ^ j) s := by
      have h := hAxpow j s
      rw [has] at h
      exact h.symm.trans hav
    have hs2 : (x ^ j) ((x⁻¹ ^ j) s) = s := by
      rw [← LinearEquiv.mul_apply, inv_pow, mul_inv_cancel]
      rfl
    have hs3 : (x ^ j) ((x ^ j) s) = s := by
      rw [← h1, hs2]
    have hpow2 : x * (x ^ j * x ^ j) = x ^ orderOf x := by
      rw [hj, ← pow_add, ← pow_succ']
      congr 2
      ring
    have hsx : x s = s := by
      calc x s = x ((x ^ j) ((x ^ j) s)) := by rw [hs3]
        _ = (x * (x ^ j * x ^ j)) s := by rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        _ = (x ^ orderOf x) s := by rw [hpow2]
        _ = s := by rw [hxn]; rfl
    have hsCW : s ∈ C ⊓ W := ⟨(hC s).mpr hsx, hsW⟩
    rw [hCW, Submodule.mem_bot] at hsCW
    rw [Submodule.mem_bot]
    rw [hsCW, map_zero]
  have hSTW : S ⊔ T' ≤ W := sup_le hSW hT'W
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S T'
  rw [hST, finrank_bot, add_zero, hT'fin] at hsum
  have hle := Submodule.finrank_mono hSTW
  have hWle4 : Module.finrank (ZMod 2) W ≤ 4 := by omega
  have hodd : Odd (orderOf xW) := ⟨j, by rw [hordxW]; exact hj⟩
  have hA2W : aW ^ 2 = 1 := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    simp only [pow_two, LinearEquiv.mul_apply, haW]
    exact hA2 w
  have hainvW : aW⁻¹ = aW := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hA2W]
  have hxWinv : ∀ w : W, ((xW⁻¹ w : W) : V) = x⁻¹ (w : V) := by
    intro w
    have h0 : xW (xW⁻¹ w) = w := by
      calc xW (xW⁻¹ w) = (xW * xW⁻¹) w := rfl
        _ = (1 : W ≃ₗ[ZMod 2] W) w := by rw [mul_inv_cancel]
        _ = w := rfl
    have h1 : x ((xW⁻¹ w : W) : V) = (w : V) := by
      rw [← hxW, h0]
    rw [← h1, hxinv']
  have hconj : aW * xW * aW⁻¹ = xW⁻¹ := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [hainvW, LinearEquiv.mul_apply, LinearEquiv.mul_apply, haW, hxW, haW, hxWinv, hAX, hA2]
  have key := OffNative.orderOf_mem_of_finrank_le_four hWle4 xW aW hA2W hconj hodd
  rw [hordxW] at key
  exact key

end CFSG.LieType.ChevTwo
