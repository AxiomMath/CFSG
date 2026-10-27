module

public import CFSG.CGT.Stroth77.L4Sylow.StdIso
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Dih

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open Equiv CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.ShapeModel

theorem r0_eq_words (r : Fin81.R0) :
    r = 1 ∨ r = uvR0 ∨ r = tR0 ∨ r = uvR0 * tR0 ∨ r = uR0 ∨ r = uvR0 * uR0 ∨ r = tR0 * uR0 ∨
      r = uvR0 * tR0 * uR0 := by
  revert r
  decide

theorem eR_symm_uvR0 : Fin81.eR.symm uvR0 = DihedralGroup.r 2 := by
  apply Fin81.eR.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  decide

theorem eR_symm_tR0 : Fin81.eR.symm tR0 = DihedralGroup.sr 1 := by
  apply Fin81.eR.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  decide

theorem eR_symm_uR0 : Fin81.eR.symm uR0 = DihedralGroup.sr 2 := by
  apply Fin81.eR.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  decide

section D8

variable {G : Type*} [Group G] {uv t u : G} (huv : uv * uv = 1) (ht : t * t = 1)
  (hu : u * u = 1) (hcu : uv * u = u * uv) (htu : t * u = u * uv * t)

include ht hu hcu htu in
theorem tu_mul_tu : t * u * (t * u) = uv := by
  calc t * u * (t * u) = u * uv * t * (t * u) := by nth_rewrite 1 [htu]; rfl
    _ = u * uv * (t * t) * u := by group
    _ = uv * (u * u) := by rw [ht, mul_one, ← hcu, mul_assoc]
    _ = uv := by rw [hu, mul_one]

include huv ht hu hcu htu in
theorem tu_pow_four : (t * u) ^ 4 = 1 := by
  rw [show 4 = 2 + 2 from rfl, pow_add, sq, tu_mul_tu ht hu hcu htu, huv]

include huv hu hcu in
theorem uvu_mul_uvu : uv * u * (uv * u) = 1 := by
  calc uv * u * (uv * u) = uv * (u * uv) * u := by group
    _ = uv * (uv * u) * u := by rw [← hcu]
    _ = uv * uv * (u * u) := by group
    _ = 1 := by rw [huv, hu, one_mul]

include huv hu htu in
theorem uvu_mul_tu : uv * u * (t * u) = t := by
  calc uv * u * (t * u) = uv * u * (u * uv * t) := by rw [htu]
    _ = uv * (u * u) * uv * t := by group
    _ = t := by rw [hu, mul_one, huv, one_mul]

include huv ht hu hcu htu in
theorem uvu_conj_tu : uv * u * (t * u) * (uv * u)⁻¹ = (t * u)⁻¹ := by
  have hτ : (uv * u)⁻¹ = uv * u := inv_eq_of_mul_eq_one_right (uvu_mul_uvu huv hu hcu)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * u = (uv * u)⁻¹ * t := by
    rw [eq_inv_mul_iff_mul_eq]
    exact uvu_mul_tu huv hu htu
  rw [uvu_mul_tu huv hu htu, h1, hτ, mul_inv_rev, htinv, hτ]

@[expose] noncomputable def d8Hom : Fin81.R0 →* G :=
  (Fin81.dihedralHom (t * u) (uv * u) (tu_pow_four huv ht hu hcu htu)
    (uvu_mul_uvu huv hu hcu) (uvu_conj_tu huv ht hu hcu htu)).comp
    Fin81.eR.symm.toMonoidHom

theorem d8Hom_apply (r : Fin81.R0) :
    d8Hom huv ht hu hcu htu r = Fin81.dihedralHom (t * u) (uv * u)
      (tu_pow_four huv ht hu hcu htu) (uvu_mul_uvu huv hu hcu) (uvu_conj_tu huv ht hu hcu htu)
      (Fin81.eR.symm r) := rfl

theorem cycHom_tu_two :
    cycHom 4 (t * u) (tu_pow_four huv ht hu hcu htu) (Multiplicative.ofAdd 2) = uv := by
  have h := cycHom_intCast 4 (t * u) (tu_pow_four huv ht hu hcu htu) 2
  simp only [Int.cast_ofNat, zpow_ofNat] at h
  rw [h, sq, tu_mul_tu ht hu hcu htu]

theorem d8Hom_uvR0 : d8Hom huv ht hu hcu htu uvR0 = uv := by
  rw [d8Hom_apply, eR_symm_uvR0]
  exact cycHom_tu_two huv ht hu hcu htu

theorem d8Hom_tR0 : d8Hom huv ht hu hcu htu tR0 = t := by
  rw [d8Hom_apply, eR_symm_tR0]
  show uv * u * cycHom 4 (t * u) (tu_pow_four huv ht hu hcu htu) (Multiplicative.ofAdd 1) = t
  rw [cycHom_ofAdd_one, uvu_mul_tu huv hu htu]

theorem d8Hom_uR0 : d8Hom huv ht hu hcu htu uR0 = u := by
  rw [d8Hom_apply, eR_symm_uR0]
  show uv * u * cycHom 4 (t * u) (tu_pow_four huv ht hu hcu htu) (Multiplicative.ofAdd 2) = u
  rw [cycHom_tu_two huv ht hu hcu htu, hcu, mul_assoc, huv, mul_one]

theorem range_d8Hom : (d8Hom huv ht hu hcu htu).range = Subgroup.closure {uv, t, u} := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    have hmem : ∀ g ∈ ({uv, t, u} : Set G), g ∈ Subgroup.closure {uv, t, u} :=
      fun g hg => Subgroup.subset_closure hg
    have h1 := hmem uv (by simp)
    have h2 := hmem t (by simp)
    have h3 := hmem u (by simp)
    rcases r0_eq_words r with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [map_one, map_mul, d8Hom_uvR0, d8Hom_tR0, d8Hom_uR0] <;>
      first
      | exact Subgroup.one_mem _
      | exact h1
      | exact h2
      | exact h3
      | exact Subgroup.mul_mem _ h1 h2
      | exact Subgroup.mul_mem _ h1 h3
      | exact Subgroup.mul_mem _ h2 h3
      | exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact ⟨uvR0, d8Hom_uvR0 huv ht hu hcu htu⟩
    · exact ⟨tR0, d8Hom_tR0 huv ht hu hcu htu⟩
    · exact ⟨uR0, d8Hom_uR0 huv ht hu hcu htu⟩

end D8

theorem exists_wVec_single_ne (π : Fin81.R0) (hπ : π ≠ 1) :
    ∃ r j : Fin 3, r ≠ 0 ∧ wVec π (Pi.single j 1) r ≠ (Pi.single j 1 : Fin 3 → ℤ) r ∧
      |wVec π (Pi.single j 1) r - (Pi.single j 1 : Fin 3 → ℤ) r| < 8 := by
  revert π
  decide

theorem ψ200_faithful {m : ℕ} (hm : 1 ≤ m) {π : Fin81.R0} (h : ∀ y, ψ200 m π y = y) : π = 1 := by
  by_contra hπ
  obtain ⟨r, j, hr, hne, hlt⟩ := exists_wVec_single_ne π hπ
  have h2 := congrArg (fun y : Multiplicative (Torus (Type200.k m)) => Multiplicative.toAdd y r)
    (h (Multiplicative.ofAdd (Torus.ofInt _ (Pi.single j 1))))
  simp only [toAdd_ψ200, toAdd_ofAdd, matAct_wM_ofInt, Torus.ofInt_apply] at h2
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
  have hk : Type200.k m r = m + 2 := by
    fin_cases r
    · exact absurd rfl hr
    · rfl
    · rfl
  rw [hk] at h2
  have h8 : (8 : ℤ) ≤ ((2 ^ (m + 2) : ℕ) : ℤ) := by
    have : 2 ^ 3 ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have h0 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_sub_comm]; linarith)
  exact hne (by linarith)

theorem right_eq_one_of_mem_center {m : ℕ} (hm : 1 ≤ m) {a : L4Std m}
    (ha : a ∈ Subgroup.center (L4Std m)) : a.right = 1 := by
  refine ψ200_faithful hm fun y => ?_
  have hl := congrArg SemidirectProduct.left
    (Subgroup.mem_center_iff.mp ha (SemidirectProduct.inl y))
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hl
  rw [mul_comm] at hl
  exact (mul_left_cancel hl).symm

structure L4Frame {G : Type*} [Group G] (D : Subgroup G) (m : ℕ) where
  e : Additive D ≃+ Torus (Type200.k m)
  uv : G
  t : G
  u : G
  uv_mem : uv ∈ Subgroup.normalizer D
  t_mem : t ∈ Subgroup.normalizer D
  u_mem : u ∈ Subgroup.normalizer D
  uv_conj : ∀ x : D,
    e (Additive.ofMul (conjBy uv_mem x)) = (Type200.action m).φuv (e (Additive.ofMul x))
  t_conj : ∀ x : D,
    e (Additive.ofMul (conjBy t_mem x)) = (Type200.action m).φt (e (Additive.ofMul x))
  u_conj : ∀ x : D,
    e (Additive.ofMul (conjBy u_mem x)) = (Type200.action m).φu (e (Additive.ofMul x))
  uv_sq : uv * uv = 1
  t_sq : t * t = 1
  u_sq : u * u = 1
  uv_comm_u : uv * u = u * uv
  t_u : t * u = u * uv * t

namespace L4Frame

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (F : L4Frame D m)

@[expose] def torusHom : Multiplicative (Torus (Type200.k m)) →* G where
  toFun x := ((Additive.toMul (F.e.symm (Multiplicative.toAdd x)) : D) : G)
  map_one' := by
    rw [toAdd_one, map_zero, toMul_zero, OneMemClass.coe_one]
  map_mul' x y := by
    rw [toAdd_mul, map_add, toMul_add, Subgroup.coe_mul]

theorem torusHom_apply (x : Multiplicative (Torus (Type200.k m))) :
    F.torusHom x = ((Additive.toMul (F.e.symm (Multiplicative.toAdd x)) : D) : G) := rfl

theorem torusHom_mem (x : Multiplicative (Torus (Type200.k m))) : F.torusHom x ∈ D :=
  (Additive.toMul (F.e.symm (Multiplicative.toAdd x)) : D).2

theorem torusHom_ofAdd_e (b : D) :
    F.torusHom (Multiplicative.ofAdd (F.e (Additive.ofMul b))) = b := by
  rw [torusHom_apply, toAdd_ofAdd, AddEquiv.symm_apply_apply]
  rfl

theorem torusHom_injective : Function.Injective F.torusHom := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply F.e.symm.injective
  exact Additive.toMul.injective (Subtype.ext h)

theorem torusHom_conj {g : G} (hg : g ∈ Subgroup.normalizer D) (hg2 : g * g = 1)
    (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (hφ : ∀ x : D, F.e (Additive.ofMul (conjBy hg x)) = φ (F.e (Additive.ofMul x)))
    (x : Multiplicative (Torus (Type200.k m))) :
    F.torusHom (Multiplicative.ofAdd (φ (Multiplicative.toAdd x))) =
      g * F.torusHom x * g⁻¹ := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  set b : D := Additive.toMul (F.e.symm (Multiplicative.toAdd x)) with hb
  have h1 := hφ b
  have h2 : F.e (Additive.ofMul b) = Multiplicative.toAdd x := by
    rw [hb, ofMul_toMul, AddEquiv.apply_symm_apply]
  rw [h2] at h1
  have h3 : conjBy hg b = Additive.toMul (F.e.symm (φ (Multiplicative.toAdd x))) := by
    rw [← h1, AddEquiv.symm_apply_apply, toMul_ofMul]
  rw [torusHom_apply, toAdd_ofAdd, ← h3, torusHom_apply, ← hb]
  show g⁻¹ * (b : G) * g = g * (b : G) * g⁻¹
  rw [hginv]

@[expose] noncomputable def d8 : Fin81.R0 →* G :=
  d8Hom F.uv_sq F.t_sq F.u_sq F.uv_comm_u F.t_u

theorem torusHom_ψ200_mul {π σ : Fin81.R0}
    (hπ : ∀ x, F.torusHom (ψ200 m π x) = F.d8 π * F.torusHom x * (F.d8 π)⁻¹)
    (hσ : ∀ x, F.torusHom (ψ200 m σ x) = F.d8 σ * F.torusHom x * (F.d8 σ)⁻¹)
    (x : Multiplicative (Torus (Type200.k m))) :
    F.torusHom (ψ200 m (π * σ) x) = F.d8 (π * σ) * F.torusHom x * (F.d8 (π * σ))⁻¹ := by
  rw [(ψ200 m).map_mul, MulAut.mul_apply, hπ, hσ, F.d8.map_mul, mul_inv_rev]
  group

theorem torusHom_ψ200 (π : Fin81.R0) (x : Multiplicative (Torus (Type200.k m))) :
    F.torusHom (ψ200 m π x) = F.d8 π * F.torusHom x * (F.d8 π)⁻¹ := by
  have h1 : ∀ x, F.torusHom (ψ200 m 1 x) = F.d8 1 * F.torusHom x * (F.d8 1)⁻¹ :=
    fun x => by simp
  have huv : ∀ x, F.torusHom (ψ200 m uvR0 x) = F.d8 uvR0 * F.torusHom x * (F.d8 uvR0)⁻¹ :=
    fun x => by
      have hψ : ψ200 m uvR0 x =
          Multiplicative.ofAdd ((Type200.action m).φuv (Multiplicative.toAdd x)) :=
        Multiplicative.toAdd.injective (toAdd_ψ200_uvR0 m x)
      rw [hψ, F.torusHom_conj F.uv_mem F.uv_sq _ F.uv_conj x, d8, d8Hom_uvR0]
  have ht : ∀ x, F.torusHom (ψ200 m tR0 x) = F.d8 tR0 * F.torusHom x * (F.d8 tR0)⁻¹ :=
    fun x => by
      have hψ : ψ200 m tR0 x =
          Multiplicative.ofAdd ((Type200.action m).φt (Multiplicative.toAdd x)) :=
        Multiplicative.toAdd.injective (toAdd_ψ200_tR0 m x)
      rw [hψ, F.torusHom_conj F.t_mem F.t_sq _ F.t_conj x, d8, d8Hom_tR0]
  have hu : ∀ x, F.torusHom (ψ200 m uR0 x) = F.d8 uR0 * F.torusHom x * (F.d8 uR0)⁻¹ :=
    fun x => by
      have hψ : ψ200 m uR0 x =
          Multiplicative.ofAdd ((Type200.action m).φu (Multiplicative.toAdd x)) :=
        Multiplicative.toAdd.injective (toAdd_ψ200_uR0 m x)
      rw [hψ, F.torusHom_conj F.u_mem F.u_sq _ F.u_conj x, d8, d8Hom_uR0]
  rcases r0_eq_words π with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 x
  · exact huv x
  · exact ht x
  · exact F.torusHom_ψ200_mul huv ht x
  · exact hu x
  · exact F.torusHom_ψ200_mul huv hu x
  · exact F.torusHom_ψ200_mul ht hu x
  · exact F.torusHom_ψ200_mul (F.torusHom_ψ200_mul huv ht) hu x

@[expose] noncomputable def l4StdHom : L4Std m →* G :=
  SemidirectProduct.lift F.torusHom F.d8 fun π => by
    refine MonoidHom.ext fun x => ?_
    exact F.torusHom_ψ200 π x

theorem l4StdHom_apply (a : L4Std m) : F.l4StdHom a = F.torusHom a.left * F.d8 a.right := rfl

theorem range_l4StdHom : F.l4StdHom.range = D ⊔ Subgroup.closure {F.uv, F.t, F.u} := by
  have hD : F.d8.range = Subgroup.closure {F.uv, F.t, F.u} := range_d8Hom _ _ _ _ _
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    rw [l4StdHom_apply]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (F.torusHom_mem a.left))
      (Subgroup.mem_sup_right ?_)
    rw [← hD]
    exact ⟨a.right, rfl⟩
  · refine sup_le (fun g hg => ?_) ?_
    · refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd (F.e (Additive.ofMul ⟨g, hg⟩))), ?_⟩
      rw [l4StdHom, SemidirectProduct.lift_inl, torusHom_ofAdd_e]
    · rw [← hD]
      rintro _ ⟨r, rfl⟩
      exact ⟨SemidirectProduct.inr r, SemidirectProduct.lift_inr _ _ _ r⟩

theorem l4StdHom_injective (hm : 1 ≤ m) : Function.Injective F.l4StdHom := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (L4Std m) := Nat.finite_of_card_ne_zero (by rw [card_L4Std]; positivity)
  haveI := (IsPGroup.of_card (card_L4Std m)).isNilpotent
  apply Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨hker, hcen⟩ := Subgroup.mem_inf.mp ha
  have hr := right_eq_one_of_mem_center hm hcen
  rw [MonoidHom.mem_ker, l4StdHom_apply, hr, map_one, mul_one] at hker
  have hl : a.left = 1 := F.torusHom_injective (hker.trans (map_one _).symm)
  exact Subgroup.mem_bot.mpr (SemidirectProduct.ext hl hr)

theorem nonempty_mulEquiv_l4Std (hm : 1 ≤ m) {S : Subgroup G}
    (hS : D ⊔ Subgroup.closure {F.uv, F.t, F.u} = S) : Nonempty (S ≃* L4Std m) := by
  have hrange : F.l4StdHom.range = S := F.range_l4StdHom.trans hS
  exact ⟨((MonoidHom.ofInjective (F.l4StdHom_injective hm)).trans
    (MulEquiv.subgroupCongr hrange)).symm⟩

theorem nonempty_mulEquiv_l4Model (hm : 1 ≤ m) {S : Subgroup G}
    (hS : D ⊔ Subgroup.closure {F.uv, F.t, F.u} = S) : Nonempty (S ≃* L4Model (m + 2)) := by
  obtain ⟨e⟩ := F.nonempty_mulEquiv_l4Std hm hS
  exact ⟨e.trans (l4ModelEquivStd hm).symm⟩

end L4Frame

end CFSG.CGT.Stroth77.L4Sylow
