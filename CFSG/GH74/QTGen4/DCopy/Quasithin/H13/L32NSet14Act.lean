module

public import CFSG.Quasithin.H13.L32NSet14Act
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14

public section

namespace CFSG.Quasithin.H13.L32NSet14

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

namespace Setting_F4
open CFSG.Quasithin.H13.L32NSet14.Setting_F4
open CFSG.Quasithin.H13.L32NSet14.Setting

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting_F4 G T L V V₂)
include S

theorem sq_mem_cent_F4 {g : G} (hg : g ∈ trivSub V (fsuV1 T V)) :
    g ^ 2 ∈ centralizer (V : Set G) := by
  obtain ⟨-, hg1, hg⟩ := hg
  rw [mem_centralizer_iff]
  intro v hv
  set d := g * v * g⁻¹ * v⁻¹ with hddef
  have hd : d ∈ fsuV1 T V := hg v hv
  have hgd : g * d = d * g :=
    mem_centralizer_iff.mp (le_centralizer_normalizer_of_card_eq_two S.card_V1_F4 hd) g hg1
  have hdV : d ∈ V := (Subgroup.mem_inf.mp hd).1
  have e2 : g * v * g⁻¹ = d * v := by rw [hddef]; group
  have e3 : g * d * g⁻¹ = d := by rw [hgd]; group
  have e4 : g ^ 2 * v * (g ^ 2)⁻¹ = v := by
    calc g ^ 2 * v * (g ^ 2)⁻¹ = (g * d * g⁻¹) * (g * v * g⁻¹) := by rw [hddef, pow_two]; group
      _ = d * (d * v) := by rw [e3, e2]
      _ = v := by rw [← mul_assoc, S.mul_self_V_F4 hdV, one_mul]
  calc v * g ^ 2 = (g ^ 2 * v * (g ^ 2)⁻¹) * g ^ 2 := by rw [e4]
    _ = g ^ 2 * v := by group

theorem le_pCoreOf_F4 {H : Subgroup G} (hHX : H ≤ nX T V) (hHLT : H ≤ L ⊔ T) :
    H ⊓ trivSub V (fsuV1 T V) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun h hh => ?_) ?_
  · refine Subgroup.mem_normalizer_fintype fun g hg => ⟨H.mul_mem (H.mul_mem hh hg.1)
      (H.inv_mem hh), ?_⟩
    exact conj_mem_trivSub (hHX hh).1 (hHX hh).2 hg.2
  · rintro ⟨g, hg⟩
    have hmem : g ^ 2 ∈ (L ⊔ T) ⊓ centralizer (V : Set G) :=
      ⟨(L ⊔ T).pow_mem (hHLT hg.1) 2, S.sq_mem_cent_F4 hg.2⟩
    obtain ⟨k, hk⟩ := S.isPGroup_cent_sup_F4 ⟨_, hmem⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
    rw [pow_succ', pow_mul]
    exact h1

theorem L1_le_X_F4 : L₁Of L (fsuV1 T V) ≤ nX T V := fun _ hg =>
  ⟨S.LV_F4 (L1_le hg).1, (L1_le hg).2⟩

theorem T_le_X_F4 : T ≤ nX T V := fun _ ht => ⟨S.TV_F4 ht, S.T_V1_F4 ht⟩

theorem exists_x_F4 {z a c : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hc : c ∈ V) (hcV : c ∉ V₂) :
    ∃ x ∈ L₁Of L (fsuV1 T V), x * z * x⁻¹ = z ∧ x * a * x⁻¹ = c ∧ x * c * x⁻¹ = a * c := by
  have hzV₂ : z ∈ V₂ := S.hV2.1 hz
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have haV' : a ∈ V := S.hV2.2.1 ha
  obtain ⟨x, hxL, hx3, hxz, hxa, hxc⟩ := S.exists_rot_F4 hzV haV' hc
    (fun h => haV (h ▸ one_mem _)) (fun h => hcV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz)) (fun h => hcV (h ▸ hzV₂)) (fun h => hcV (h ▸ ha))
    (fun h => hcV (h ▸ mul_mem hzV₂ ha))
  refine ⟨x, subset_closure ⟨⟨hxL, S.mem_g1_F4 hz hz1 hxz⟩, 3, by decide, hx3⟩, hxz, hxa, hxc⟩

theorem exists_rep_F4 : ∃ ψ : ↥(nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    ∀ x, ψ x = 1 ↔ (x : G) ∈ trivSub V (fsuV1 T V) := by
  classical
  let _ := zmodModuleOf (fun v hv => S.sq_V_F4 hv)
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  set V₁ := fsuV1 T V with hV₁
  set W₁ := subOf (V := V) V₁ with hW₁
  have : Finite (Additive ↥V ⧸ W₁) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective W₁)
  have hdimV : Module.finrank (ZMod 2) (Additive ↥V) = 3 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥V)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive ↥V) = 2 ^ 3 := S.card_V_F4
    rw [h2] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hdimW : Module.finrank (ZMod 2) W₁ = 1 :=
    finrank_subOf inf_le_left (by rw [S.card_V1_F4]; rfl)
  have hdimQ : Module.finrank (ZMod 2) (Additive ↥V ⧸ W₁) = 2 := by
    have := Submodule.finrank_quotient_add_finrank W₁
    omega
  obtain ⟨eQ⟩ := nonempty_linearEquiv_mulEquiv_sl hdimQ
  have hXV : nX T V ≤ normalizer (V : Set G) := inf_le_left
  let σ : ↥(nX T V) →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    linHom.comp ((conjAct V).comp (Subgroup.inclusion hXV))
  have hσ : ∀ (x : ↥(nX T V)) (v : Additive ↥V), ((Additive.toMul (σ x v) : ↥V) : G) =
      (x : G) * ((Additive.toMul v : ↥V) : G) * (x : G)⁻¹ := fun x v => rfl
  have hσle : ∀ x : ↥(nX T V), W₁.map (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) ≤ W₁ := by
    rintro x _ ⟨w, hw, rfl⟩
    have hw' : ((w.toMul : ↥V) : G) ∈ V₁ := mem_subOf.1 hw
    show (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w ∈ subOf (V := V) V₁
    rw [mem_subOf, show ((σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w) = σ x w from rfl, hσ]
    exact (Subgroup.mem_normalizer_iff.1 x.2.2 _).1 hw'
  have hσW : ∀ x : ↥(nX T V), W₁.map (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) = W₁ := by
    intro x
    refine le_antisymm (hσle x) fun w hw => ?_
    refine ⟨σ x⁻¹ w, hσle x⁻¹ ⟨w, hw, rfl⟩, ?_⟩
    show σ x (σ x⁻¹ w) = w
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  let ρX : ↥(nX T V) →* ((Additive ↥V ⧸ W₁) ≃ₗ[ZMod 2] (Additive ↥V ⧸ W₁)) :=
    { toFun := fun x => Submodule.Quotient.equiv W₁ W₁ (σ x) (hσW x)
      map_one' := by
        apply LinearEquiv.ext
        intro q
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁ q
        simp [map_one]
      map_mul' := fun x y => by
        apply LinearEquiv.ext
        intro q
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁ q
        simp [map_mul] }
  have hρX : ∀ (x : ↥(nX T V)) (v : Additive ↥V),
      ρX x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (σ x v) := fun x v => rfl
  refine ⟨eQ.toMonoidHom.comp ρX, fun x => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  constructor
  · intro hx
    refine ⟨x.2.1, x.2.2, fun v hv => ?_⟩
    have h1 := LinearEquiv.congr_fun hx (Submodule.Quotient.mk (Additive.ofMul (⟨v, hv⟩ : ↥V)))
    rw [hρX, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq, hW₁, mem_subOf] at h1
    have e1 : ((Additive.toMul (σ x (Additive.ofMul ⟨v, hv⟩) - Additive.ofMul ⟨v, hv⟩) :
        ↥V) : G) = (x : G) * v * (x : G)⁻¹ * v⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, hσ, div_eq_mul_inv]
      rfl
    rw [← e1]
    exact h1
  · intro hx
    apply LinearEquiv.ext
    intro q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁ q
    rw [hρX, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq, hW₁, mem_subOf]
    have e1 : ((Additive.toMul (σ x v - v) : ↥V) : G) =
        (x : G) * ((Additive.toMul v : ↥V) : G) * (x : G)⁻¹ *
          ((Additive.toMul v : ↥V) : G)⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, hσ, div_eq_mul_inv]
    rw [e1]
    exact hx.2.2 _ (Additive.toMul v).2

theorem cube_eq_one_F4 (ψ : ↥(nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) {g : G}
    (hg : g ∈ L₁Of L (fsuV1 T V)) : ψ ⟨g, S.L1_le_X_F4 hg⟩ ^ 3 = 1 := by
  refine Subgroup.closure_induction
    (k := {x | x ∈ L ⊓ normalizer (fsuV1 T V : Set G) ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1})
    (p := fun g hg => ψ ⟨g, S.L1_le_X_F4 hg⟩ ^ 3 = 1) ?_ ?_ ?_ ?_ hg
  · intro g hg'
    obtain ⟨-, m, hm, hgm⟩ := id hg'
    refine sl2_cube_of_odd hm ?_
    rw [← map_pow]
    have : (⟨g, S.L1_le_X_F4 (subset_closure hg')⟩ : ↥(nX T V)) ^ m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hgm)
    rw [this, map_one]
  · show ψ 1 ^ 3 = 1
    rw [map_one, one_pow]
  · intro g g' hg hg' ih ih'
    show ψ (⟨g, S.L1_le_X_F4 hg⟩ * ⟨g', S.L1_le_X_F4 hg'⟩) ^ 3 = 1
    rw [map_mul]
    exact sl2_cube_mul _ _ ih ih'
  · intro g hg ih
    show ψ (⟨g, S.L1_le_X_F4 hg⟩)⁻¹ ^ 3 = 1
    rw [map_inv, inv_pow, ih, inv_one]

theorem pCoreOf_L1_le_F4 : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ trivSub V (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := S.exists_rep_F4
  intro q hq
  have hqL : q ∈ L₁Of L (fsuV1 T V) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V))) ⟨q, hq⟩
  have hk' : q ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow] at this
  have h3 := S.cube_eq_one_F4 ψ hqL
  have h2 : ψ ⟨q, S.L1_le_X_F4 hqL⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨q, S.L1_le_X_F4 hqL⟩ : ↥(nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hk')
    rw [this, map_one]
  have ho : orderOf (ψ ⟨q, S.L1_le_X_F4 hqL⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
      (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  exact (hψ _).mp (orderOf_eq_one_iff.mp ho)

theorem Lp3_F4 : (pCoreOf 2 (L₁Of L (fsuV1 T V))).relIndex (L₁Of L (fsuV1 T V)) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ, hψ⟩ := S.exists_rep_F4
  set φ : ↥(L₁Of L (fsuV1 T V)) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    ψ.comp (Subgroup.inclusion S.L1_le_X_F4) with hφ
  have hφ_apply : ∀ y : ↥(L₁Of L (fsuV1 T V)), φ y = ψ ⟨y, S.L1_le_X_F4 y.2⟩ := fun y => rfl
  have hker : φ.ker = (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V)) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ_apply, hψ]
    constructor
    · intro h
      exact S.le_pCoreOf_F4 S.L1_le_X_F4 ((L1_le.trans inf_le_left).trans le_sup_left) ⟨y.2, h⟩
    · intro h
      exact S.pCoreOf_L1_le_F4 h
  have hrange : Nat.card φ.range = 3 := by
    have hp3 : IsPGroup 3 φ.range := by
      rintro ⟨s, hs⟩
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hs
      exact ⟨1, Subtype.ext (by
        show φ y ^ 3 ^ 1 = 1
        rw [pow_one, hφ_apply]
        exact S.cube_eq_one_F4 ψ y.2)⟩
    obtain ⟨k, hk⟩ := hp3.exists_card_eq
    have hdvd : Nat.card φ.range ∣ 6 := card_sl2 ▸ Subgroup.card_subgroup_dvd_card φ.range
    obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S.exists_basis_F4
    obtain ⟨x, hxL, -, hxa, -⟩ := S.exists_x_F4 hz hz1 ha haV hb hbV
    have hφx : φ ⟨x, hxL⟩ ≠ 1 := by
      rw [hφ_apply, Ne, hψ]
      intro h
      have h1 := h.2.2 a (S.hV2.2.1 ha)
      rw [hxa] at h1
      apply hbV
      have h2 := mul_mem (S.hV2.1 h1) ha
      rwa [inv_mul_cancel_right] at h2
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hk
      have : φ ⟨x, hxL⟩ ∈ φ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rw [hk, Subgroup.mem_bot] at this
      exact hφx this
    have hk2 : k < 2 := by
      by_contra h
      push Not at h
      rw [hk] at hdvd
      exact absurd ((Nat.pow_dvd_pow 3 h).trans hdvd) (by decide)
    obtain rfl : k = 1 := by omega
    rw [hk, pow_one]
  rw [show (pCoreOf 2 (L₁Of L (fsuV1 T V))).relIndex (L₁Of L (fsuV1 T V)) =
      ((pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))).index from rfl,
    ← hker, Subgroup.index_ker, hrange]

theorem comm3_F4 : ⁅V, pCoreOf 2 (L₁Of L (fsuV1 T V))⁆ = fsuV1 T V := by
  obtain ⟨ψ, hψ⟩ := S.exists_rep_F4
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv q hq
    have hq' := (S.pCoreOf_L1_le_F4 hq).2.2 v hv
    have e : ⁅v, q⁆ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact inv_mem hq'
  · obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S.exists_basis_F4
    have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
    have haV' : a ∈ V := S.hV2.2.1 ha
    have hzz := S.mul_self_V_F4 hzV
    have hbz : b * z ∈ V := mul_mem hb hzV
    have hbzV : b * z ∉ V₂ := fun h => hbV (by
      have := mul_mem h (S.hV2.1 hz)
      rwa [mul_assoc, hzz, mul_one] at this)
    obtain ⟨x, hxL, hxz, hxa, hxb⟩ := S.exists_x_F4 hz hz1 ha haV hb hbV
    obtain ⟨y, hyL, hyz, hya, hybz⟩ := S.exists_x_F4 hz hz1 ha haV hbz hbzV
    set k := x * y * x⁻¹ * y⁻¹ with hk
    have hkL : k ∈ L₁Of L (fsuV1 T V) :=
      mul_mem (mul_mem (mul_mem hxL hyL) (inv_mem hxL)) (inv_mem hyL)
    have hkQ : k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
      refine S.le_pCoreOf_F4 S.L1_le_X_F4 ((L1_le.trans inf_le_left).trans le_sup_left)
        ⟨hkL, (hψ ⟨k, S.L1_le_X_F4 hkL⟩).mp ?_⟩
      have e : (⟨k, S.L1_le_X_F4 hkL⟩ : ↥(nX T V)) = ⟨x, S.L1_le_X_F4 hxL⟩ * ⟨y, S.L1_le_X_F4 hyL⟩ *
          (⟨x, S.L1_le_X_F4 hxL⟩ : ↥(nX T V))⁻¹ * (⟨y, S.L1_le_X_F4 hyL⟩ : ↥(nX T V))⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
        sl2_cube_comm _ _ (S.cube_eq_one_F4 ψ hxL) (S.cube_eq_one_F4 ψ hyL)]
      group
    have hyb : y * b * y⁻¹ = a * b := by
      calc y * b * y⁻¹ = y * ((b * z) * z) * y⁻¹ := by rw [mul_assoc b z z, hzz, mul_one]
        _ = (y * (b * z) * y⁻¹) * (y * z * y⁻¹) := by group
        _ = (a * (b * z)) * z := by rw [hybz, hyz]
        _ = a * b := by rw [mul_assoc, mul_assoc, hzz, mul_one]
    have e1 : y⁻¹ * (a * b) * y = b := by
      calc y⁻¹ * (a * b) * y = y⁻¹ * (y * b * y⁻¹) * y := by rw [hyb]
        _ = b := by group
    have e2 : x⁻¹ * b * x = a := by
      calc x⁻¹ * b * x = x⁻¹ * (x * a * x⁻¹) * x := by rw [hxa]
        _ = a := by group
    have e3 : x * (b * z) * x⁻¹ = a * b * z := by
      calc x * (b * z) * x⁻¹ = (x * b * x⁻¹) * (x * z * x⁻¹) := by group
        _ = a * b * z := by rw [hxb, hxz]
    have hkab : k * (a * b) * k⁻¹ = a * b * z := by
      calc k * (a * b) * k⁻¹ = x * (y * (x⁻¹ * (y⁻¹ * (a * b) * y) * x) * y⁻¹) * x⁻¹ := by
            rw [hk]; group
        _ = a * b * z := by rw [e1, e2, hya, e3]
    have hab : a * b ∈ V := mul_mem haV' hb
    have hzC : z ∈ ⁅V, pCoreOf 2 (L₁Of L (fsuV1 T V))⁆ := by
      have h1 := Subgroup.commutator_mem_commutator hkQ hab
      rw [Subgroup.commutator_comm] at h1
      have e : ⁅k, a * b⁆ = z := by
        rw [commutatorElement_def, hkab]
        calc a * b * z * (a * b)⁻¹ = z * (a * b) * (a * b)⁻¹ := by rw [S.comm_V_F4 hab hzV]
          _ = z := by group
      rwa [e] at h1
    intro v hv
    rcases S.eq_of_mem_V1_F4 hz hz1 hv with rfl | rfl
    · exact one_mem _
    · exact hzC

theorem index2_le_F4 : (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).relIndex T ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := S.exists_rep_F4
  have hHX : L₁Of L (fsuV1 T V) ⊔ T ≤ nX T V := sup_le S.L1_le_X_F4 S.T_le_X_F4
  have hHLT : L₁Of L (fsuV1 T V) ⊔ T ≤ L ⊔ T :=
    sup_le ((L1_le.trans inf_le_left).trans le_sup_left) le_sup_right
  set φ : ↥T →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    ψ.comp (Subgroup.inclusion S.T_le_X_F4) with hφ
  have hφ_apply : ∀ t : ↥T, φ t = ψ ⟨t, S.T_le_X_F4 t.2⟩ := fun t => rfl
  have hker : φ.ker ≤ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf T := by
    intro t ht
    rw [MonoidHom.mem_ker, hφ_apply, hψ] at ht
    exact Subgroup.mem_subgroupOf.mpr (S.le_pCoreOf_F4 hHX hHLT ⟨Subgroup.mem_sup_right t.2, ht⟩)
  have hrange : Nat.card φ.range ≤ 2 := by
    have hp2 : IsPGroup 2 φ.range := by
      rintro ⟨s, hs⟩
      obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hs
      obtain ⟨k, hk⟩ := S.hH.sylow.1 t
      exact ⟨k, Subtype.ext (by
        show φ t ^ 2 ^ k = 1
        rw [← map_pow, hk, map_one])⟩
    obtain ⟨j, hj⟩ := hp2.exists_card_eq
    have hdvd : Nat.card φ.range ∣ 6 := card_sl2 ▸ Subgroup.card_subgroup_dvd_card φ.range
    rw [hj] at hdvd ⊢
    have hj2 : j < 2 := by
      by_contra h
      push Not at h
      exact absurd ((Nat.pow_dvd_pow 2 h).trans hdvd) (by decide)
    interval_cases j <;> norm_num
  calc (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).relIndex T =
      ((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf T).index := rfl
    _ ≤ φ.ker.index := Subgroup.index_antitone hker
    _ = Nat.card φ.range := Subgroup.index_ker φ
    _ ≤ 2 := hrange

end Setting_F4

end CFSG.Quasithin.H13.L32NSet14
