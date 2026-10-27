module

public import CFSG.CGT.Stroth77.Stroth3VTheta

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

@[expose] def InW {k : Fin 3 → ℕ} (w : Torus k) : Prop := w 0 = 0 ∧ w + w = 0

structure VFacts (τ : StrothTypeIndex) : Prop where
  two_le : 2 ≤ τ.k 0
  classify : ∀ δ : Torus τ.k →+ Torus τ.k,
    (∀ x, δ (τ.action.φuv x) = τ.action.φuv (δ x)) →
    (∀ x, δ (τ.action.φt x) = τ.action.φt (δ x)) →
    (∀ x, x + x = 0 → δ x = x) → (∀ x, δ (δ x) = x) →
    ∃ α : ℤ, Odd α ∧ ∃ w, InW w ∧ ∀ x, δ x = α • x + (x 0).val • w
  even_uv : ∀ r : Torus τ.k, r + τ.action.φuv r = 0 → (r 0).val % 2 = 0
  even_t : ∀ r : Torus τ.k, r + τ.action.φt r = 0 → (r 0).val % 2 = 0
  fixed : ∀ z : Torus τ.k, τ.action.φuv z = z → τ.action.φt z = z → InW z
  par_uv : ∀ x : Torus τ.k, ((τ.action.φuv x) 0).val % 2 = (x 0).val % 2
  par_t : ∀ x : Torus τ.k, ((τ.action.φt x) 0).val % 2 = (x 0).val % 2
  par_u : ∀ x : Torus τ.k, ((τ.action.φu x) 0).val % 2 = (x 0).val % 2
  par_ρ : ∀ x : Torus τ.k, ((τ.action.φρ x) 0).val % 2 = (x 0).val % 2
  W_uv : ∀ w, InW w → τ.action.φuv w = w
  W_t : ∀ w, InW w → τ.action.φt w = w
  W_u : ∀ w : Torus τ.k, InW w → (τ.action.φu w) 0 = 0
  W_ρ : ∀ w : Torus τ.k, InW w → (τ.action.φρ w) 0 = 0
  W_fpf : ∀ w, InW w → τ.action.φρ w = w → w = 0
  sq_W : ∀ v : Torus τ.k, v + v = 0 → τ.action.φρ (τ.action.φρ v) = v + τ.action.φρ v → v 0 = 0
  W_orbit : ∀ v w : Torus τ.k, InW v → v ≠ 0 → InW w →
    w = 0 ∨ w = v ∨ w = τ.action.φρ v ∨ w = v + τ.action.φρ v

namespace VFacts

variable {τ : StrothTypeIndex} (hτ : VFacts τ)
include hτ

theorem one_le : 1 ≤ τ.k 0 := le_trans (by norm_num) hτ.two_le

theorem inW_ρ {w : Torus τ.k} (hw : InW w) : InW (τ.action.φρ w) :=
  ⟨hτ.W_ρ w hw, by rw [← map_add, hw.2, map_zero]⟩

theorem inW_u {w : Torus τ.k} (hw : InW w) : InW (τ.action.φu w) :=
  ⟨hτ.W_u w hw, by rw [← map_add, hw.2, map_zero]⟩

end VFacts

namespace Local.Setting

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} (hS : Local.Setting S D)

@[expose] def R1 (x y : G) : Subgroup G where
  carrier := {e | e ∈ hS.R ∧ e⁻¹ * x * e * x⁻¹ ∈ D ∧ e⁻¹ * y * e * y⁻¹ ∈ D}
  mul_mem' {a b} ha hb := by
    have key : ∀ z : G, a⁻¹ * z * a * z⁻¹ ∈ D → b ∈ hS.R → b⁻¹ * z * b * z⁻¹ ∈ D →
        (a * b)⁻¹ * z * (a * b) * z⁻¹ ∈ D := fun z h1 hbR h2 => by
      have h1' := (Subgroup.mem_normalizer_iff''.mp (hS.R_le_normalizer hbR) _).mp h1
      have := mul_mem h1' h2
      convert this using 1
      group
    exact ⟨mul_mem ha.1 hb.1, key x ha.2.1 hb.1 hb.2.1, key y ha.2.2 hb.1 hb.2.2⟩
  one_mem' := ⟨one_mem _, by simp, by simp⟩
  inv_mem' {a} ha := by
    have key : ∀ z : G, a⁻¹ * z * a * z⁻¹ ∈ D → a⁻¹⁻¹ * z * a⁻¹ * z⁻¹ ∈ D := fun z h1 => by
      have := (Subgroup.mem_normalizer_iff''.mp (inv_mem (hS.R_le_normalizer ha.1)) _).mp
        (inv_mem h1)
      convert this using 1
      group
    exact ⟨inv_mem ha.1, key x ha.2.1, key y ha.2.2⟩

theorem exists_sq_mem {x y e₀ : G} (he₀ : e₀ ∈ hS.R1 x y) (he₀D : e₀ ∉ D) :
    ∃ e ∈ hS.R1 x y, e ∉ D ∧ e * e ∈ D := by
  classical
  obtain ⟨a, ha⟩ := hS.isPGroup ⟨e₀, hS.R_le_S he₀.1⟩
  have ha' : e₀ ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hex : ∃ j, e₀ ^ 2 ^ j ∈ D := ⟨a, by rw [ha']; exact one_mem _⟩
  have hjD : e₀ ^ 2 ^ Nat.find hex ∈ D := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := fun h0 => he₀D (by simpa [h0] using hjD)
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨e₀ ^ 2 ^ i, pow_mem he₀ _, fun hiD => ?_, ?_⟩
  · exact Nat.find_min hex (show i < Nat.find hex by omega) hiD
  · rw [← pow_add, ← two_mul, ← pow_succ']
    rw [hi] at hjD
    exact hjD

end Local.Setting

namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

theorem thetaT_congr {g g' : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hg' : g' ∈ Subgroup.normalizer (D : Set G)) (h : g = g') (x : Torus τ.k) :
    dD.thetaT hg x = dD.thetaT hg' x := by
  subst h; rfl

theorem thetaT_thetaT_inv {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (x : Torus τ.k) :
    dD.thetaT hg (dD.thetaT (inv_mem hg) x) = x := by
  rw [← dD.thetaT_mul (inv_mem hg) hg]
  exact dD.thetaT_of_mem_centralizer _ (by rw [inv_mul_cancel]; exact one_mem _) x

theorem thetaT_inv_thetaT {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (x : Torus τ.k) :
    dD.thetaT (inv_mem hg) (dD.thetaT hg x) = x := by
  rw [← dD.thetaT_mul hg (inv_mem hg)]
  exact dD.thetaT_of_mem_centralizer _ (by rw [mul_inv_cancel]; exact one_mem _) x

theorem thetaT_conj {e h : G} (he : e ∈ Subgroup.normalizer (D : Set G))
    (hh : h ∈ Subgroup.normalizer (D : Set G)) (x : Torus τ.k) :
    dD.thetaT (mul_mem (mul_mem (inv_mem hh) he) hh) x =
      dD.thetaT hh (dD.thetaT he (dD.thetaT (inv_mem hh) x)) := by
  rw [dD.thetaT_mul (mul_mem (inv_mem hh) he) hh, dD.thetaT_mul (inv_mem hh) he]

theorem thetaT_comm_of_conj_mem {e g : G} (he : e ∈ Subgroup.normalizer (D : Set G))
    (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : e⁻¹ * g * e * g⁻¹ ∈ D) (x : Torus τ.k) :
    dD.thetaT he (dD.thetaT hg x) = dD.thetaT hg (dD.thetaT he x) := by
  have hrN : e⁻¹ * g * e * g⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer hr
  have key := dD.thetaT_congr (mul_mem hg he) (mul_mem (mul_mem he hrN) hg) (by group) x
  rw [dD.thetaT_mul hg he, dD.thetaT_mul (mul_mem he hrN) hg, dD.thetaT_mul he hrN,
    dD.thetaT_of_mem _ hr] at key
  exact key

theorem thetaT_of_two {e : G} (he : e ∈ Subgroup.normalizer (D : Set G))
    (hc : e ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) {x : Torus τ.k}
    (hx : x + x = 0) : dD.thetaT he x = x := by
  have hsq : dD.ofT x * dD.ofT x = 1 := by rw [← dD.ofT_add, hx, dD.ofT_zero]
  have hmem : dD.ofT x ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self (dD.ofT_mem x) hsq
  rw [thetaT_apply, mul_assoc, Subgroup.mem_centralizer_iff.mp hc _ hmem, inv_mul_cancel_left,
    crdT_ofT]

theorem thetaT_thetaT_of_sq {e : G} (he : e ∈ Subgroup.normalizer (D : Set G)) (hsq : e * e ∈ D)
    (x : Torus τ.k) : dD.thetaT he (dD.thetaT he x) = x := by
  rw [← dD.thetaT_mul he he]
  exact dD.thetaT_of_mem _ hsq x

theorem thetaT_proj {S : Subgroup G} (hS : Local.Setting S D) {h r : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ hS.R) (x : Torus τ.k) :
    dD.thetaT (hS.R_le_normalizer (hS.proj_mem hh hr)) x =
      dD.thetaT (mul_mem (mul_mem (inv_mem hh) (hS.R_le_normalizer hr)) hh) x := by
  obtain ⟨hp, o, ho, e⟩ := hS.proj_spec hh hr
  rw [dD.thetaT_congr _ (mul_mem (hS.R_le_normalizer hp) (hS.O_le_normalizer ho)) e,
    dD.thetaT_mul (hS.R_le_normalizer hp) (hS.O_le_normalizer ho),
    dD.thetaT_of_mem_centralizer _ (hS.O_le_centralizer ho)]

theorem thetaT_rho_conj (hτ : VFacts τ) {e : G} (he : e ∈ Subgroup.normalizer (D : Set G))
    {α : ℤ} {w : Torus τ.k} (hw : InW w) (hδ : ∀ x, dD.thetaT he x = α • x + (x 0).val • w)
    (x : Torus τ.k) :
    dD.thetaT (mul_mem (mul_mem (inv_mem dD.ρ_mem) he) dD.ρ_mem) x =
      α • x + (x 0).val • τ.action.φρ w := by
  rw [dD.thetaT_conj he dD.ρ_mem, hδ, map_add, map_zsmul, map_nsmul, dD.thetaT_thetaT_inv,
    dD.thetaT_ρ]
  congr 1
  apply nsmul_eq_of_mod_two (hτ.inW_ρ hw).2
  rw [dD.thetaT_ρ_inv, hτ.par_ρ, hτ.par_ρ]

theorem exists_nu_pair (hτ : VFacts τ) {S : Subgroup G} (hS : Local.Setting S D)
    (hkill : ∀ e ∈ hS.R, e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D → e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D →
      (∀ d ∈ D, (dD.ρ⁻¹ * e * dD.ρ)⁻¹ * d * (dD.ρ⁻¹ * e * dD.ρ) = e⁻¹ * d * e) → e ∈ D)
    {e₁ : G} (he₁ : e₁ ∈ hS.R1 dD.uv dD.t) (he₁D : e₁ ∉ D) (hsq : e₁ * e₁ ∈ D) :
    ∃ e, ∃ he : e ∈ hS.R, ∃ f, ∃ hf : f ∈ hS.R, ∃ w : Torus τ.k, InW w ∧ w ≠ 0 ∧
      τ.action.φρ w ≠ w ∧ (∀ x, dD.thetaT (hS.R_le_normalizer he) x = nuMap w x) ∧
      (∀ x, dD.thetaT (hS.R_le_normalizer hf) x = nuMap (τ.action.φρ w) x) := by
  obtain ⟨he₁R, huv, ht⟩ := he₁
  have hN := hS.R_le_normalizer he₁R
  have hC := hS.R_le_centralizer_omega he₁R
  obtain ⟨α, hα, w₁, hw₁, hδ⟩ := hτ.classify (dD.thetaT hN)
    (fun x => by
      have := dD.thetaT_comm_of_conj_mem hN dD.uv_mem huv x
      rwa [dD.thetaT_uv, dD.thetaT_uv] at this)
    (fun x => by
      have := dD.thetaT_comm_of_conj_mem hN dD.t_mem ht x
      rwa [dD.thetaT_t, dD.thetaT_t] at this)
    (fun x hx => dD.thetaT_of_two hN hC hx) (fun x => dD.thetaT_thetaT_of_sq hN hsq x)
  have hk := hτ.one_le
  have hval : ∀ y : Torus τ.k, ((α • y + (y 0).val • w₁) 0).val % 2 = (y 0).val % 2 := fun y => by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hw₁.1, smul_zero, add_zero]
    exact val_zsmul_odd_mod_two hk hα (y 0)
  have hαw : ∀ m : ℕ, α • (m • w₁) = m • w₁ := fun m => by
    rw [smul_comm, zsmul_eq_self_of_odd hw₁.2 hα]
  have hαα : ∀ y : Torus τ.k, α • α • y = y := fun y => by
    have key := dD.thetaT_thetaT_of_sq hN hsq y
    rw [hδ (dD.thetaT hN y), hδ y, smul_add, hαw, nsmul_eq_of_mod_two hw₁.2 (hval y)] at key
    have e2 : (y 0).val • w₁ + (y 0).val • w₁ = 0 := by rw [← nsmul_add, hw₁.2, nsmul_zero]
    calc α • α • y = α • α • y + ((y 0).val • w₁ + (y 0).val • w₁) := by rw [e2, add_zero]
      _ = α • α • y + (y 0).val • w₁ + (y 0).val • w₁ := by abel
      _ = y := key
  have hw₁0 : w₁ ≠ 0 := by
    rintro rfl
    apply he₁D
    refine hkill e₁ he₁R huv ht fun d hd => ?_
    have hd1 := (Subgroup.mem_normalizer_iff''.mp
      (mul_mem (mul_mem (inv_mem dD.ρ_mem) hN) dD.ρ_mem) d).mp hd
    have hd2 := (Subgroup.mem_normalizer_iff''.mp hN d).mp hd
    refine crdT_inj dD.e hd1 hd2 ?_
    rw [← dD.thetaT_crdT (mul_mem (mul_mem (inv_mem dD.ρ_mem) hN) dD.ρ_mem) hd,
      ← dD.thetaT_crdT hN hd, dD.thetaT_conj hN dD.ρ_mem, hδ, hδ]
    simp only [smul_zero, add_zero, map_zsmul, dD.thetaT_thetaT_inv]
  have hpR := hS.proj_mem dD.ρ_mem he₁R
  have hθp : ∀ x, dD.thetaT (hS.R_le_normalizer hpR) x =
      α • x + (x 0).val • τ.action.φρ w₁ := fun x => by
    rw [dD.thetaT_proj hS dD.ρ_mem he₁R, dD.thetaT_rho_conj hτ hN hw₁ hδ]
  have hθinv : ∀ x, dD.thetaT (inv_mem hN) x = dD.thetaT hN x := fun x => by
    conv_lhs => rw [← dD.thetaT_thetaT_of_sq hN hsq x]
    exact dD.thetaT_inv_thetaT hN _
  set w₂ := w₁ + τ.action.φρ w₁ with hw₂def
  have hw₂ : InW w₂ := ⟨by
      show (w₁ + τ.action.φρ w₁) 0 = 0
      rw [Pi.add_apply, hw₁.1, hτ.W_ρ w₁ hw₁, add_zero],
    by rw [hw₂def, add_add_add_comm, hw₁.2, (hτ.inW_ρ hw₁).2, add_zero]⟩
  have he₂R : e₁⁻¹ * hS.proj dD.ρ e₁ ∈ hS.R := mul_mem (inv_mem he₁R) hpR
  have hθe₂ : ∀ x, dD.thetaT (hS.R_le_normalizer he₂R) x = nuMap w₂ x := fun x => by
    rw [dD.thetaT_congr _ (mul_mem (inv_mem hN) (hS.R_le_normalizer hpR)) rfl,
      dD.thetaT_mul (inv_mem hN) (hS.R_le_normalizer hpR), hθinv, hθp, hδ x, smul_add, hαα,
      hαw, nsmul_eq_of_mod_two (hτ.inW_ρ hw₁).2 (hval x), nuMap, hw₂def, nsmul_add, add_assoc]
  have hw₂0 : w₂ ≠ 0 := fun h0 => hw₁0 (hτ.W_fpf w₁ hw₁ (by
    rw [eq_neg_of_add_eq_zero_right h0, neg_eq_of_add_eq_zero_left hw₁.2]))
  have hfR := hS.proj_mem dD.ρ_mem he₂R
  have hθe₂' : ∀ x, dD.thetaT (hS.R_le_normalizer he₂R) x = (1 : ℤ) • x + (x 0).val • w₂ :=
    fun x => by rw [one_zsmul, hθe₂ x]; rfl
  refine ⟨_, he₂R, _, hfR, w₂, hw₂, hw₂0, fun hfix => hw₂0 (hτ.W_fpf w₂ hw₂ hfix), hθe₂,
    fun x => ?_⟩
  rw [dD.thetaT_proj hS dD.ρ_mem he₂R, dD.thetaT_rho_conj hτ _ hw₂ hθe₂' x, one_zsmul]
  rfl

theorem mem_of_thetaT_id {S : Subgroup G} (hS : Local.Setting S D) {g : G} (hgS : g ∈ S)
    (hg : g ∈ Subgroup.normalizer (D : Set G)) (hid : ∀ x, dD.thetaT hg x = x) : g ∈ D := by
  rw [← hS.cent]
  exact Subgroup.mem_inf.mpr ⟨hgS, dD.mem_centralizer_of_thetaT hg hid⟩

theorem conj_mem_of_thetaT_comm {S : Subgroup G} (hS : Local.Setting S D) {e g : G} (heS : e ∈ S)
    (hgS : g ∈ S) (he : e ∈ Subgroup.normalizer (D : Set G))
    (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hc : ∀ x, dD.thetaT he (dD.thetaT hg x) = dD.thetaT hg (dD.thetaT he x)) :
    e⁻¹ * g * e * g⁻¹ ∈ D := by
  refine dD.mem_of_thetaT_id hS (mul_mem (mul_mem (mul_mem (inv_mem heS) hgS) heS) (inv_mem hgS))
    (mul_mem (mul_mem (mul_mem (inv_mem he) hg) he) (inv_mem hg)) fun x => ?_
  rw [dD.thetaT_mul (mul_mem (mul_mem (inv_mem he) hg) he) (inv_mem hg),
    dD.thetaT_mul (mul_mem (inv_mem he) hg) he, dD.thetaT_mul (inv_mem he) hg, hc,
    dD.thetaT_thetaT_inv he, dD.thetaT_inv_thetaT hg]

theorem nu_comm_uv (hτ : VFacts τ) {w : Torus τ.k} (hw : InW w) (x : Torus τ.k) :
    nuMap w (τ.action.φuv x) = τ.action.φuv (nuMap w x) := by
  simp only [nuMap, map_add, map_nsmul, hτ.W_uv w hw]
  congr 1
  exact nsmul_eq_of_mod_two hw.2 (hτ.par_uv x)

theorem nu_comm_t (hτ : VFacts τ) {w : Torus τ.k} (hw : InW w) (x : Torus τ.k) :
    nuMap w (τ.action.φt x) = τ.action.φt (nuMap w x) := by
  simp only [nuMap, map_add, map_nsmul, hτ.W_t w hw]
  congr 1
  exact nsmul_eq_of_mod_two hw.2 (hτ.par_t x)

theorem thetaT_inv_of_nu {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) {v : Torus τ.k}
    (hv : InW v) (hθ : ∀ x, dD.thetaT hg x = nuMap v x) (x : Torus τ.k) :
    dD.thetaT (inv_mem hg) x = nuMap v x := by
  have key := dD.thetaT_inv_thetaT hg (nuMap v x)
  rwa [hθ, nuMap_nuMap hv.1, hv.2, nuMap_zero] at key

theorem crdT_commutator_mul (hk : 1 ≤ τ.k 0) {e f d₁ d₂ : G}
    (he : e ∈ Subgroup.normalizer (D : Set G)) (hf : f ∈ Subgroup.normalizer (D : Set G))
    (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hz : e⁻¹ * f⁻¹ * e * f ∈ D) {v v' : Torus τ.k} (hv : InW v)
    (hθe : ∀ x, dD.thetaT he x = nuMap v x) (hθf : ∀ x, dD.thetaT hf x = nuMap v' x) :
    (e * d₁)⁻¹ * (f * d₂)⁻¹ * (e * d₁) * (f * d₂) ∈ D ∧
      crdT dD.e ((e * d₁)⁻¹ * (f * d₂)⁻¹ * (e * d₁) * (f * d₂)) =
        crdT dD.e (e⁻¹ * f⁻¹ * e * f) + (crdT dD.e d₁ 0).val • v' +
          (crdT dD.e d₂ 0).val • v := by
  have hid : (e * d₁)⁻¹ * (f * d₂)⁻¹ * (e * d₁) * (f * d₂) =
      d₁⁻¹ * (e⁻¹ * d₂⁻¹ * e) * (e⁻¹ * f⁻¹ * e * f) * (f⁻¹ * d₁ * f) * d₂ := by group
  have h1 : e⁻¹ * d₂⁻¹ * e ∈ D := (Subgroup.mem_normalizer_iff''.mp he _).mp (inv_mem hd₂)
  have h2 : f⁻¹ * d₁ * f ∈ D := (Subgroup.mem_normalizer_iff''.mp hf _).mp hd₁
  rw [hid]
  refine ⟨mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hd₁) h1) hz) h2) hd₂, ?_⟩
  rw [crdT_mul dD.e (mul_mem (mul_mem (mul_mem (inv_mem hd₁) h1) hz) h2) hd₂,
    crdT_mul dD.e (mul_mem (mul_mem (inv_mem hd₁) h1) hz) h2,
    crdT_mul dD.e (mul_mem (inv_mem hd₁) h1) hz, crdT_mul dD.e (inv_mem hd₁) h1,
    crdT_inv dD.e hd₁, ← dD.thetaT_crdT he (inv_mem hd₂), ← dD.thetaT_crdT hf hd₁, hθe, hθf,
    crdT_inv dD.e hd₂, nuMap, nuMap, Pi.neg_apply,
    nsmul_eq_of_mod_two hv.2 (val_neg_mod_two hk (crdT dD.e d₂ 0))]
  abel

theorem exists_comm_nu_pair (hτ : VFacts τ) {S : Subgroup G} (hS : Local.Setting S D)
    (huvS : dD.uv ∈ S) (htS : dD.t ∈ S) {e f : G} (he : e ∈ hS.R) (hf : f ∈ hS.R)
    {w : Torus τ.k} (hw : InW w) (hw0 : w ≠ 0) (hPw : τ.action.φρ w ≠ w)
    (hθe : ∀ x, dD.thetaT (hS.R_le_normalizer he) x = nuMap w x)
    (hθf : ∀ x, dD.thetaT (hS.R_le_normalizer hf) x = nuMap (τ.action.φρ w) x) :
    ∃ e', ∃ he' : e' ∈ hS.R, ∃ f', ∃ hf' : f' ∈ hS.R, e' * f' = f' * e' ∧
      (∀ x, dD.thetaT (hS.R_le_normalizer he') x = nuMap w x) ∧
      (∀ x, dD.thetaT (hS.R_le_normalizer hf') x = nuMap (τ.action.φρ w) x) := by
  have hk := hτ.one_le
  set w' := τ.action.φρ w with hw'def
  have hw' : InW w' := hτ.inW_ρ hw
  have hw'0 : w' ≠ 0 := fun h0 => hw0 (by
    have := DFunLike.congr_fun τ.action.rels.rho_cube w
    change τ.action.φρ (τ.action.φρ (τ.action.φρ w)) = w at this
    rw [← hw'def, h0, map_zero, map_zero] at this
    exact this.symm)
  have heN := hS.R_le_normalizer he
  have hfN := hS.R_le_normalizer hf
  have hcoc : ∀ {g : G} (hg : g ∈ hS.R) {v : Torus τ.k}, InW v →
      (∀ x, dD.thetaT (hS.R_le_normalizer hg) x = nuMap v x) →
      g⁻¹ * dD.uv * g * dD.uv⁻¹ ∈ D ∧ g⁻¹ * dD.t * g * dD.t⁻¹ ∈ D := fun {g} hg {v} hv hθ =>
    ⟨dD.conj_mem_of_thetaT_comm hS (hS.R_le_S hg) huvS (hS.R_le_normalizer hg) dD.uv_mem
      fun x => by rw [dD.thetaT_uv, dD.thetaT_uv, hθ, hθ, nu_comm_uv hτ hv],
     dD.conj_mem_of_thetaT_comm hS (hS.R_le_S hg) htS (hS.R_le_normalizer hg) dD.t_mem
      fun x => by rw [dD.thetaT_t, dD.thetaT_t, hθ, hθ, nu_comm_t hτ hv]⟩
  obtain ⟨heuv, het⟩ := hcoc he hw hθe
  obtain ⟨hfuv, hft⟩ := hcoc hf hw' hθf
  have hcent : ∀ {d : G}, d ∈ D → (crdT dD.e d 0).val % 2 = 0 → Commute d e ∧ Commute d f :=
    fun {d} hd hev => by
      have h1 : e⁻¹ * d * e = d := crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN d).mp hd)
        hd (by rw [← dD.thetaT_crdT heN hd, hθe, (nuMap_eq_self_iff hw.2 hw0 _).mpr hev])
      have h2 : f⁻¹ * d * f = d := crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp hfN d).mp hd)
        hd (by rw [← dD.thetaT_crdT hfN hd, hθf, (nuMap_eq_self_iff hw'.2 hw'0 _).mpr hev])
      exact ⟨by
          show d * e = e * d
          calc d * e = e * (e⁻¹ * d * e) := by group
            _ = e * d := by rw [h1],
        by
          show d * f = f * d
          calc d * f = f * (f⁻¹ * d * f) := by group
            _ = f * d := by rw [h2]⟩
  have hcomm_D : ∀ {d d' : G}, d ∈ D → d' ∈ D → Commute d d' := fun hd hd' =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm (⟨_, hd⟩ : D) ⟨_, hd'⟩)
  have hθfinv := dD.thetaT_inv_of_nu hfN hw' hθf
  have hz : e⁻¹ * f⁻¹ * e * f ∈ D := by
    have := dD.conj_mem_of_thetaT_comm hS (hS.R_le_S he) (inv_mem (hS.R_le_S hf)) heN
      (inv_mem hfN) fun x => by
        rw [hθfinv, hθfinv, hθe, hθe, nuMap_nuMap hw'.1, nuMap_nuMap hw.1, add_comm]
    simpa using this
  have hfix : ∀ {x : G}, x ∈ Subgroup.normalizer (D : Set G) → x * x = 1 →
      e⁻¹ * x * e * x⁻¹ ∈ D → f⁻¹ * x * f * x⁻¹ ∈ D →
      (crdT dD.e (e⁻¹ * x * e * x⁻¹) 0).val % 2 = 0 →
      (crdT dD.e (f⁻¹ * x * f * x⁻¹) 0).val % 2 = 0 →
      x⁻¹ * (e⁻¹ * f⁻¹ * e * f) * x = e⁻¹ * f⁻¹ * e * f := fun {x} _ hx2 h1 h2 hev1 hev2 => by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have ke : x⁻¹ * e * x = e * (e⁻¹ * x * e * x⁻¹) := by rw [hxi]; group
    have kf : x⁻¹ * f * x = f * (f⁻¹ * x * f * x⁻¹) := by rw [hxi]; group
    obtain ⟨c1e, c1f⟩ := hcent h1 hev1
    obtain ⟨c2e, c2f⟩ := hcent h2 hev2
    calc x⁻¹ * (e⁻¹ * f⁻¹ * e * f) * x
        = (x⁻¹ * e * x)⁻¹ * (x⁻¹ * f * x)⁻¹ * (x⁻¹ * e * x) * (x⁻¹ * f * x) := by group
      _ = e⁻¹ * f⁻¹ * e * f := by
        rw [ke, kf]
        exact commutator_mul_of_commute c1e c1f c2e c2f (hcomm_D h1 h2)
  have hevc : ∀ {g : G}, g⁻¹ * dD.uv * g * dD.uv⁻¹ ∈ D → g⁻¹ * dD.t * g * dD.t⁻¹ ∈ D →
      (crdT dD.e (g⁻¹ * dD.uv * g * dD.uv⁻¹) 0).val % 2 = 0 ∧
        (crdT dD.e (g⁻¹ * dD.t * g * dD.t⁻¹) 0).val % 2 = 0 := fun {g} h1 h2 => by
    obtain ⟨c1, c2, -⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
      dD.uv_conj dD.t_conj h1 h2
    exact ⟨hτ.even_uv _ c1, hτ.even_t _ c2⟩
  obtain ⟨eu, et⟩ := hevc heuv het
  obtain ⟨fu, ft⟩ := hevc hfuv hft
  have hzU : τ.action.φuv (crdT dD.e (e⁻¹ * f⁻¹ * e * f)) = crdT dD.e (e⁻¹ * f⁻¹ * e * f) := by
    rw [← crdT_conj dD.e dD.uv_mem dD.uv_conj hz,
      hfix dD.uv_mem dD.uv_sq heuv hfuv eu fu]
  have hzT : τ.action.φt (crdT dD.e (e⁻¹ * f⁻¹ * e * f)) = crdT dD.e (e⁻¹ * f⁻¹ * e * f) := by
    rw [← crdT_conj dD.e dD.t_mem dD.t_conj hz, hfix dD.t_mem dD.t_sq het hft et ft]
  have hzW := hτ.fixed _ hzU hzT
  have finish : ∀ {d₁ d₂ : G}, d₁ ∈ D → d₂ ∈ D →
      crdT dD.e (e⁻¹ * f⁻¹ * e * f) + (crdT dD.e d₁ 0).val • w' + (crdT dD.e d₂ 0).val • w = 0 →
      ∃ e', ∃ he' : e' ∈ hS.R, ∃ f', ∃ hf' : f' ∈ hS.R, e' * f' = f' * e' ∧
        (∀ x, dD.thetaT (hS.R_le_normalizer he') x = nuMap w x) ∧
        (∀ x, dD.thetaT (hS.R_le_normalizer hf') x = nuMap w' x) := fun {d₁ d₂} hd₁ hd₂ h0 => by
    obtain ⟨hmem, hcrd⟩ := dD.crdT_commutator_mul hk heN hfN hd₁ hd₂ hz hw hθe hθf
    rw [h0] at hcrd
    have h1 := crdT_inj dD.e hmem (one_mem D) (hcrd.trans (crdT_one dD.e).symm)
    refine ⟨e * d₁, mul_mem he (hS.D_le_R hd₁), f * d₂, mul_mem hf (hS.D_le_R hd₂), ?_,
      fun x => ?_, fun x => ?_⟩
    · rw [show (e * d₁)⁻¹ * (f * d₂)⁻¹ * (e * d₁) * (f * d₂) =
          (f * d₂ * (e * d₁))⁻¹ * (e * d₁ * (f * d₂)) by group] at h1
      exact (inv_mul_eq_one.mp h1).symm
    · rw [dD.thetaT_congr _ (mul_mem heN (Subgroup.le_normalizer hd₁)) rfl,
        dD.thetaT_mul heN (Subgroup.le_normalizer hd₁), dD.thetaT_of_mem _ hd₁, hθe]
    · rw [dD.thetaT_congr _ (mul_mem hfN (Subgroup.le_normalizer hd₂)) rfl,
        dD.thetaT_mul hfN (Subgroup.le_normalizer hd₂), dD.thetaT_of_mem _ hd₂, hθf]
  have hg₀ := dD.ofT_mem (gen τ.k 0)
  have v₀ : (crdT dD.e (dD.ofT (gen τ.k 0)) 0).val = 1 := by
    rw [crdT_ofT, gen_zero_val hk]
  have v₁ : (crdT dD.e (1 : G) 0).val = 0 := by rw [crdT_one]; simp
  rcases hτ.W_orbit w _ hw hw0 hzW with h | h | h | h
  · exact finish (one_mem D) (one_mem D) (by rw [h, v₁, zero_nsmul, zero_nsmul, add_zero, add_zero])
  · exact finish (one_mem D) hg₀ (by rw [h, v₁, v₀, zero_nsmul, one_nsmul, add_zero, hw.2])
  · exact finish hg₀ (one_mem D) (by rw [h, v₁, v₀, zero_nsmul, one_nsmul, add_zero, ← hw'def,
      hw'.2])
  · exact finish hg₀ hg₀ (by
      rw [h, v₀, one_nsmul, one_nsmul, ← hw'def,
        show w + w' + w' + w = (w + w) + (w' + w') by abel, hw.2, hw'.2, add_zero])

end StrothWeakTypeData

end CFSG.CGT.Stroth77
