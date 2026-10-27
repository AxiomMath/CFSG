module

public import CFSG.CGT.Stroth77.Arch76FrameLemma2

public section

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Stroth77

namespace Arch76

@[expose] def mS : Mat := ((1, 0, 0), (0, 3, 0), (0, 0, 3))
@[expose] def mI : Mat := ((1, 0, 0), (0, 1, 0), (0, 0, 1))
@[expose] def lUV : Mat := ((1, 2, 2), (0, 1, 2), (0, 2, 1))
@[expose] def lT : Mat := ((1, 2, 0), (0, 3, 0), (0, 2, 3))
@[expose] def lU : Mat := ((1, 0, 0), (0, 0, 1), (0, 1, 0))
@[expose] def lUVS : Mat := ((1, 2, 2), (0, 3, 2), (0, 2, 3))
@[expose] def gens8 : List Mat := [lUV, lT, lU]
@[expose] def gens16 : List Mat := [lUV, lT, lU, mS]

@[expose] def d16 : List Mat :=
  [((1, 0, 0), (0, 0, 1), (0, 1, 0)), ((1, 0, 0), (0, 0, 3), (0, 3, 0)),
    ((1, 0, 0), (0, 1, 0), (0, 0, 1)), ((1, 0, 0), (0, 3, 0), (0, 0, 3)),
    ((1, 0, 2), (0, 0, 1), (0, 1, 2)), ((1, 0, 2), (0, 0, 3), (0, 3, 2)),
    ((1, 0, 2), (0, 1, 2), (0, 0, 1)), ((1, 0, 2), (0, 3, 2), (0, 0, 3)),
    ((1, 2, 0), (0, 1, 0), (0, 2, 1)), ((1, 2, 0), (0, 2, 1), (0, 1, 0)),
    ((1, 2, 0), (0, 2, 3), (0, 3, 0)), ((1, 2, 0), (0, 3, 0), (0, 2, 3)),
    ((1, 2, 2), (0, 1, 2), (0, 2, 1)), ((1, 2, 2), (0, 2, 1), (0, 1, 2)),
    ((1, 2, 2), (0, 2, 3), (0, 3, 2)), ((1, 2, 2), (0, 3, 2), (0, 2, 3))]

@[expose] def v8 : List Mat :=
  [mI, mS, ((1, 0, 2), (0, 1, 2), (0, 0, 1)), ((1, 0, 2), (0, 3, 2), (0, 0, 3)),
    ((1, 2, 0), (0, 1, 0), (0, 2, 1)), lT, lUV, lUVS]

@[expose] def basisCo : List Co := [(1, 0, 0), (0, 1, 0), (0, 0, 1)]

@[expose] def W1 : List Co := [(0, 0, 0), (0, 2, 2)]

@[expose] def W2 : List Co :=
  [(0, 0, 0), (0, 0, 2), (0, 2, 0), (0, 2, 2), (1, 1, 1), (1, 1, 3), (1, 3, 1), (1, 3, 3)]

@[expose] def W3 : List Co :=
  [(0, 0, 0), (0, 0, 2), (0, 1, 1), (0, 1, 3), (0, 2, 0), (0, 2, 2), (0, 3, 1), (0, 3, 3),
    (1, 0, 0), (1, 0, 2), (1, 1, 1), (1, 1, 3), (1, 2, 0), (1, 2, 2), (1, 3, 1), (1, 3, 3)]

theorem matMul_mem_d16 : ∀ m ∈ d16, ∀ n ∈ d16, matMul m n ∈ d16 := by decide +kernel
theorem mI_mem_d16 : mI ∈ d16 := by decide
theorem lUV_mem_d16 : lUV ∈ d16 := by decide
theorem lT_mem_d16 : lT ∈ d16 := by decide
theorem lU_mem_d16 : lU ∈ d16 := by decide
theorem mS_mem_d16 : mS ∈ d16 := by decide

theorem W3_step : ∀ v ∈ W3, ∀ m ∈ d16, v - matAct m v ∈ W2 := by decide +kernel
theorem W2_step16 : ∀ v ∈ W2, ∀ m ∈ d16, v - matAct m v ∈ W1 := by decide +kernel
theorem W1_step16 : ∀ v ∈ W1, ∀ m ∈ d16, v - matAct m v = 0 := by decide +kernel
theorem W2_step8 : ∀ v ∈ W2, ∀ m ∈ d8, v - matAct m v ∈ W1 := by decide +kernel
theorem W1_step8 : ∀ v ∈ W1, ∀ m ∈ d8, v - matAct m v = 0 := by decide +kernel

theorem fix_W3 : ∀ m ∈ d16, m = mI ∨ ∃ v ∈ W3, matAct m v ≠ v := by decide +kernel

theorem fix_W2 : ∀ m ∈ d8, m = mI ∨ m = lUV ∨ ∃ v ∈ W2, matAct m v ≠ v := by decide +kernel

theorem Z2_mat : ∀ M ∈ d8, ∀ M' ∈ d8, matMul M M' = mI → M = mI ∨
    ∃ e ∈ basisCo, ∃ G ∈ gens8, (matAct M' e - e) - matAct G (matAct M' e - e) ≠ 0 := by
  decide +kernel

theorem Z3_mat_a : ∀ M' ∈ d16, M' ∈ v8 ∨
    ∃ e ∈ basisCo, ∃ G₂ ∈ gens16, ∃ G₃ ∈ gens16,
      let c := matAct M' e - e; let c₂ := c - matAct G₂ c; c₂ - matAct G₃ c₂ ≠ 0 := by
  decide +kernel

theorem v8_inv : ∀ M ∈ d16, ∀ M' ∈ v8, matMul M M' = mI → M ∈ v8 := by decide +kernel

theorem Z3_mat_b_bool : (v8.all fun M => v8.all fun M' => !(matMul M M' == mI) ||
    [mI, lUV, mS, lUVS].contains M ||
    (gens16.any fun G₁ => basisCo.any fun e => gens16.any fun G₃ =>
      (matAct (matMul (matMul (matMul G₁ M) G₁) M') e - e) -
        matAct G₃ (matAct (matMul (matMul (matMul G₁ M) G₁) M') e - e) != 0)) = true := by
  decide +kernel

theorem Z3_mat_b {M M' : Mat} (hM : M ∈ v8) (hM' : M' ∈ v8) (h : matMul M M' = mI) :
    M ∈ [mI, lUV, mS, lUVS] ∨ ∃ G₁ ∈ gens16, ∃ e ∈ basisCo, ∃ G₃ ∈ gens16,
      (matAct (matMul (matMul (matMul G₁ M) G₁) M') e - e) -
        matAct G₃ (matAct (matMul (matMul (matMul G₁ M) G₁) M') e - e) ≠ 0 := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp Z3_mat_b_bool M hM) M' hM'
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    List.contains_iff_mem, List.any_eq_true, bne_iff_ne, ne_eq] at h1
  exact h1

theorem Z3_rest : ∀ va ∈ [((0, 1, 1) : Co), (0, 3, 1)], ∀ v : Co,
    (let c := v + kmap al0 va - kmap al0 v; let c₂ := c - ft c; c₂ - fu c₂ ≠ 0) ∧
      (let c := v + va - fuv v; let c₂ := c - ft c; c₂ - fu c₂ ≠ 0) ∧
      (let c := v + fuv va - fuv v; let c₂ := c - ft c; c₂ - fu c₂ ≠ 0) := by
  decide +kernel

theorem sq_uv_mem : ∀ v : Co, v + fuv v ∈ W1 := by decide +kernel

theorem d8_fix_xy2 : ∀ m ∈ d8, matAct m (0, 2, 2) = (0, 2, 2) := by decide +kernel

theorem mUV_eq : Config.mUV = lUV := by decide
theorem mT_eq : Config.mT = lT := by decide
theorem mU_eq : Config.mU = lU := by decide

namespace Config

variable {Y : Type*} [Group Y] (C : Config Y) [C.A.Normal]

theorem act_neg (g : Y) (v : Co) : C.act g (-v) = -C.act g v :=
  C.act_eq_of (by rw [ev_neg, ev_neg, ev_act]; group)

theorem comm_left_ev (z : Y) (e : Co) : ⁅z, C.ev e⁆ = C.ev (C.act z⁻¹ e - e) := by
  rw [commutatorElement_def, sub_eq_add_neg, ev_add, ev_neg, ev_act, inv_inv]

theorem comm_ev_right (c : Co) (g : Y) : ⁅C.ev c, g⁆ = C.ev (c - C.act g⁻¹ c) := by
  have h : C.ev (c - C.act g⁻¹ c) = C.ev c * C.ev (C.act g⁻¹ (-c)) := by
    rw [← ev_add, act_neg, sub_eq_add_neg]
  rw [h, commutatorElement_def, ev_act, inv_inv, ev_neg]
  group

theorem mat_mul_inv (g : Y) : matMul (C.mat g) (C.mat g⁻¹) = mI := by
  rw [← mat_mul, mul_inv_cancel, C.mat_one_eq]; rfl

theorem act_mI {g : Y} (h : C.mat g = mI) (v : Co) : C.act g v = v := by
  rw [act_eq_matAct, h]; exact lin_basis v

theorem mem_centralizer_of_mat {g : Y} (h : C.mat g = mI) :
    g ∈ Subgroup.centralizer (C.A : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨v, rfl⟩ := C.exists_ev ha
  have h1 := C.ev_act g v
  rw [C.act_mI h] at h1
  calc C.ev v * g = g * (g⁻¹ * C.ev v * g) := by group
    _ = g * C.ev v := by rw [← h1]

theorem mat_mem_of_mem_sup {X : Set Y} {L : List Mat}
    (hL : ∀ d ∈ Subgroup.closure X, C.mat d ∈ L) {q : Y} (hq : q ∈ C.A ⊔ Subgroup.closure X) :
    C.mat q ∈ L := by
  have hq' : q ∈ ((C.A ⊔ Subgroup.closure X : Subgroup Y) : Set Y) := hq
  rw [Subgroup.normal_mul, Set.mem_mul] at hq'
  obtain ⟨a, ha, d, hd, rfl⟩ := hq'
  obtain ⟨v, rfl⟩ := C.exists_ev ha
  rw [C.mat_ev_mul]; exact hL d hd

theorem mat_mem_d8_of_T {q : Y} (hq : q ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u}) :
    C.mat q ∈ d8 :=
  C.mat_mem_of_mem_sup (fun _ hd => C.mat_mem_d8 hd) hq

theorem mat_mem_d16_of_closure {s : Y} (hs : C.mat s = mS) (hs2 : s⁻¹ = s) {d : Y}
    (hd : d ∈ Subgroup.closure {C.uv, C.t, C.u, s}) : C.mat d ∈ d16 := by
  have huv : C.mat C.uv ∈ d16 := by rw [C.mat_uv_eq, mUV_eq]; exact lUV_mem_d16
  have ht : C.mat C.t ∈ d16 := by rw [C.mat_t_eq, mT_eq]; exact lT_mem_d16
  have hu : C.mat C.u ∈ d16 := by rw [C.mat_u_eq, mU_eq]; exact lU_mem_d16
  have hs' : C.mat s ∈ d16 := by rw [hs]; exact mS_mem_d16
  induction hd using Subgroup.closure_induction'' with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    exacts [huv, ht, hu, hs']
  | inv_mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rwa [C.uv_inv]
    · rwa [C.t_inv]
    · rwa [C.u_inv]
    · rwa [hs2]
  | one => rw [C.mat_one_eq]; exact mI_mem_d16
  | mul g h _ _ ihg ihh => rw [mat_mul]; exact matMul_mem_d16 _ ihg _ ihh

theorem mat_mem_d16_of_T₁ {s : Y} (hs : C.mat s = mS) (hs2 : s⁻¹ = s) {q : Y}
    (hq : q ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u, s}) : C.mat q ∈ d16 :=
  C.mat_mem_of_mem_sup (fun _ hd => C.mat_mem_d16_of_closure hs hs2 hd) hq

theorem act_uv_inv_eq (v : Co) : C.act C.uv⁻¹ v = matAct lUV v := C.act_uv_inv v
theorem act_t_inv_eq (v : Co) : C.act C.t⁻¹ v = matAct lT v := C.act_t_inv v
theorem act_u_inv_eq (v : Co) : C.act C.u⁻¹ v = matAct lU v := C.act_u_inv v

end Config

section Conj

variable {G : Type*} [Group G] {Q : Subgroup G} (σ : G ≃* G) (hσ : ∀ x, σ x ∈ Q ↔ x ∈ Q)
include hσ

theorem forall_mem_map_iff (P : G → Prop) : (∀ q ∈ Q, P (σ q)) ↔ (∀ q ∈ Q, P q) := by
  constructor
  · intro h q hq
    have := h (σ.symm q) ((hσ _).mp (by rwa [MulEquiv.apply_symm_apply]))
    rwa [MulEquiv.apply_symm_apply] at this
  · intro h q hq
    exact h _ ((hσ q).mpr hq)

theorem comm_map_iff (x y : G) : σ x * σ y = σ y * σ x ↔ x * y = y * x := by
  rw [← map_mul, ← map_mul, σ.injective.eq_iff]

theorem Z1_map_iff (z : G) : (σ z ∈ Q ∧ ∀ q ∈ Q, σ z * q = q * σ z) ↔
    (z ∈ Q ∧ ∀ q ∈ Q, z * q = q * z) := by
  rw [hσ, ← forall_mem_map_iff σ hσ (fun q => σ z * q = q * σ z)]
  simp only [comm_map_iff σ hσ]

theorem Z2_map_iff (z : G) : (σ z ∈ Q ∧ ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ⁅⁅σ z, q₁⁆, q₂⁆ = 1) ↔
    (z ∈ Q ∧ ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ⁅⁅z, q₁⁆, q₂⁆ = 1) := by
  refine and_congr (hσ z) ?_
  refine (forall_mem_map_iff σ hσ (fun q₁ => ∀ q₂ ∈ Q, ⁅⁅σ z, q₁⁆, q₂⁆ = 1)).symm.trans ?_
  refine forall₂_congr fun q₁ _ => ?_
  refine (forall_mem_map_iff σ hσ (fun q₂ => ⁅⁅σ z, σ q₁⁆, q₂⁆ = 1)).symm.trans ?_
  refine forall₂_congr fun q₂ _ => ?_
  rw [← map_commutatorElement, ← map_commutatorElement, map_eq_one_iff _ σ.injective]

theorem Z3_map_iff (z : G) :
    (σ z ∈ Q ∧ ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ q₃ ∈ Q, ⁅⁅⁅σ z, q₁⁆, q₂⁆, q₃⁆ = 1) ↔
      (z ∈ Q ∧ ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ q₃ ∈ Q, ⁅⁅⁅z, q₁⁆, q₂⁆, q₃⁆ = 1) := by
  refine and_congr (hσ z) ?_
  refine (forall_mem_map_iff σ hσ
    (fun q₁ => ∀ q₂ ∈ Q, ∀ q₃ ∈ Q, ⁅⁅⁅σ z, q₁⁆, q₂⁆, q₃⁆ = 1)).symm.trans ?_
  refine forall₂_congr fun q₁ _ => ?_
  refine (forall_mem_map_iff σ hσ
    (fun q₂ => ∀ q₃ ∈ Q, ⁅⁅⁅σ z, σ q₁⁆, q₂⁆, q₃⁆ = 1)).symm.trans ?_
  refine forall₂_congr fun q₂ _ => ?_
  refine (forall_mem_map_iff σ hσ (fun q₃ => ⁅⁅⁅σ z, σ q₁⁆, σ q₂⁆, q₃⁆ = 1)).symm.trans ?_
  refine forall₂_congr fun q₃ _ => ?_
  rw [← map_commutatorElement, ← map_commutatorElement, ← map_commutatorElement,
    map_eq_one_iff _ σ.injective]

end Conj

theorem kmap_al0_eq : ∀ v : Co, kmap al0 v = matAct mS v := by decide +kernel

theorem matMul_uv_uv : matMul lUV lUV = mI := by decide
theorem matMul_s_s : matMul mS mS = mI := by decide
theorem lUVS_eq : lUVS = matMul lUV mS := by decide
theorem matMul_uvs_inv : matMul (matMul lUV mS) (matMul mS lUV) = mI := by decide

namespace Config

variable {Y : Type*} [Group Y] (C : Config Y) [C.A.Normal]

theorem comm_ev_mul (v : Co) (x g : Y) :
    ⁅C.ev v * x, g⁆ = C.ev v * ⁅x, g⁆ * C.ev (C.act g⁻¹ (-v)) := by
  rw [commutatorElement_def, commutatorElement_def, ev_act, inv_inv, ev_neg]; group

variable {s : Y} (hs2 : s⁻¹ = s) {va : Co} (hsuv : s⁻¹ * C.uv * s = C.ev va * C.uv)
include hsuv

theorem comm_uv_s : ⁅C.uv, s⁆ = C.ev (C.act s⁻¹ va) := by
  have h : C.uv * s = s * (C.ev va * C.uv) := by rw [← hsuv]; group
  rw [commutatorElement_def, h, ev_act, inv_inv]; group

include hs2

theorem comm_s_uv : ⁅s, C.uv⁆ = C.ev va := by
  rw [commutatorElement_def]
  calc s * C.uv * s⁻¹ * C.uv⁻¹ = (s⁻¹ * C.uv * s) * C.uv⁻¹ := by rw [hs2]
    _ = C.ev va := by rw [hsuv]; group

theorem comm_uvs_uv : ⁅C.uv * s, C.uv⁆ = C.ev (fuv va) := by
  have h1 : s * C.uv * s⁻¹ = C.ev va * C.uv := by
    rw [show s * C.uv * s⁻¹ = s⁻¹ * C.uv * s by rw [hs2], hsuv]
  rw [commutatorElement_def]
  calc C.uv * s * C.uv * (C.uv * s)⁻¹ * C.uv⁻¹ =
        C.uv * (s * C.uv * s⁻¹) * C.uv⁻¹ * C.uv⁻¹ := by group
    _ = C.uv * C.ev va * C.uv⁻¹ := by rw [h1]; group
    _ = C.ev (fuv va) := by rw [← C.act_uv_inv va, ev_act, inv_inv]

end Config

end Arch76

namespace StrothFrame

open Arch76

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

@[expose] def evG (v : Co) : G := ((F.configN.ev v : Subgroup.normalizer (F.A : Set G)) : G)

theorem evG_mem (v : Co) : F.evG v ∈ F.A := Subgroup.mem_subgroupOf.mp (F.configN.ev_mem v)

theorem exists_evG {q : G} (hq : q ∈ F.A) : ∃ v, F.evG v = q := by
  obtain ⟨v, hv⟩ := F.configN.exists_ev
    (show (⟨q, Subgroup.le_normalizer hq⟩ : Subgroup.normalizer (F.A : Set G)) ∈ F.configN.A
      from Subgroup.mem_subgroupOf.mpr hq)
  exact ⟨v, congrArg Subtype.val hv⟩

theorem coe_comm (a b : Subgroup.normalizer (F.A : Set G)) :
    ((⁅a, b⁆ : Subgroup.normalizer (F.A : Set G)) : G) = ⁅(a : G), (b : G)⁆ :=
  map_commutatorElement (Subgroup.normalizer (F.A : Set G)).subtype a b

theorem lift_T {q : G} (hq : q ∈ F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u}) :
    ∃ q' : Subgroup.normalizer (F.A : Set G),
      q' ∈ F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} ∧
        (q' : G) = q := by
  rw [← F.T_map] at hq
  obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
  exact ⟨q', hq', rfl⟩

theorem coe_mem_T {q' : Subgroup.normalizer (F.A : Set G)}
    (hq' : q' ∈ F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u}) :
    (q' : G) ∈ F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} := by
  rw [← F.T_map]; exact Subgroup.mem_map_of_mem _ hq'

theorem evG_mem_T (v : Co) : F.evG v ∈ F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} :=
  Subgroup.mem_sup_left (F.evG_mem v)

theorem evG_mul_comm_iff {q : Subgroup.normalizer (F.A : Set G)} {v : Co} :
    (q : G) * F.evG v = F.evG v * q ↔ F.configN.act q v = v := by
  constructor
  · intro h
    apply F.configN.act_eq_of
    have h' : q * F.configN.ev v = F.configN.ev v * q := Subtype.ext h
    rw [mul_assoc, ← h']; group
  · intro h
    have h1 := F.configN.ev_act q v
    rw [h] at h1
    show ((q * F.configN.ev v : Subgroup.normalizer (F.A : Set G)) : G) =
      ((F.configN.ev v * q : Subgroup.normalizer (F.A : Set G)) : G)
    congr 1
    calc q * F.configN.ev v = q * (q⁻¹ * F.configN.ev v * q) := by rw [← h1]
      _ = F.configN.ev v * q := by group

theorem mem_A_of_centralizer (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A)
    {q : G} (hqS : q ∈ (F.S : Subgroup G)) (hq : q ∈ Subgroup.centralizer (F.A : Set G)) :
    q ∈ F.A := by
  rw [← hCA]; exact ⟨hq, hqS⟩

theorem coe_mem_centralizer {q : Subgroup.normalizer (F.A : Set G)}
    (hq : q ∈ Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G)))) :
    (q : G) ∈ Subgroup.centralizer (F.A : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hq ⊢
  intro a ha
  have := congrArg Subtype.val (hq ⟨a, Subgroup.le_normalizer ha⟩
    (Subgroup.mem_subgroupOf.mpr ha))
  simpa using this

theorem A_comm {a b : G} (ha : a ∈ F.A) (hb : b ∈ F.A) : a * b = b * a := by
  haveI := F.dA.isMulCommutative
  exact Subgroup.mul_comm_of_mem_isMulCommutative F.A ha hb

theorem u_mem_T : F.dA.u ∈ F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem normalizes_A_of_T
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) {g : G}
    (hg : g ∈ Subgroup.normalizer
      ((F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (F.A : Set G) := by
  set T := F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} with hT
  have hcen : ∀ q ∈ T, q ∈ Subgroup.centralizer (F.A : Set G) → q ∈ F.A :=
    fun q hq h => F.mem_A_of_centralizer hCA (F.T_le_S hq) h
  have hZ2A : ∀ z, (z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅z, q₁⁆, q₂⁆ = 1) → z ∈ F.A := by
    rintro z ⟨hzT, hz⟩
    obtain ⟨z', hz'T, rfl⟩ := F.lift_T hzT
    rcases Z2_mat _ (F.configN.mat_mem_d8_of_T hz'T) _ (F.configN.mat_mem_d8_of_T (inv_mem hz'T))
      (F.configN.mat_mul_inv z') with h | ⟨e, -, G', hG', hne⟩
    · exact hcen _ hzT (F.coe_mem_centralizer (F.configN.mem_centralizer_of_mat h))
    · exfalso
      apply hne
      have key : ∀ g' : Subgroup.normalizer (F.A : Set G),
          g' ∈ F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} →
            (∀ v, F.configN.act g'⁻¹ v = Arch76.matAct G' v) →
            (Arch76.matAct (F.configN.mat z'⁻¹) e - e) -
              Arch76.matAct G' (Arch76.matAct (F.configN.mat z'⁻¹) e - e) = 0 := by
        intro g' hg'T hact
        have h1 := hz _ (F.evG_mem_T e) _ (F.coe_mem_T hg'T)
        rw [show F.evG e = ((F.configN.ev e : Subgroup.normalizer (F.A : Set G)) : G) from rfl,
          ← F.coe_comm, ← F.coe_comm] at h1
        have h2 : ⁅⁅z', F.configN.ev e⁆, g'⁆ = 1 := Subtype.ext h1
        rw [F.configN.comm_left_ev, F.configN.comm_ev_right, F.configN.ev_eq_one_iff,
          F.configN.act_eq_matAct z'⁻¹, hact] at h2
        exact h2
      simp only [gens8, List.mem_cons, List.not_mem_nil, or_false] at hG'
      rcases hG' with rfl | rfl | rfl
      · exact key _ F.configN.uv_mem_T F.configN.act_uv_inv_eq
      · exact key _ F.configN.t_mem_T F.configN.act_t_inv_eq
      · exact key _ F.configN.u_mem_T F.configN.act_u_inv_eq
  have hW2 : ∀ v ∈ W2, F.evG v ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅F.evG v, q₁⁆, q₂⁆ = 1 := by
    intro v hv
    refine ⟨F.evG_mem_T v, fun q₁ hq₁ q₂ hq₂ => ?_⟩
    obtain ⟨q₁', hq₁'T, rfl⟩ := F.lift_T hq₁
    obtain ⟨q₂', hq₂'T, rfl⟩ := F.lift_T hq₂
    rw [show F.evG v = ((F.configN.ev v : Subgroup.normalizer (F.A : Set G)) : G) from rfl,
      ← F.coe_comm, ← F.coe_comm, F.configN.comm_ev_right, F.configN.comm_ev_right,
      F.configN.act_eq_matAct q₁'⁻¹,
      F.configN.act_eq_matAct q₂'⁻¹]
    have h1 := W2_step8 v hv _ (F.configN.mat_mem_d8_of_T (inv_mem hq₁'T))
    rw [W1_step8 _ h1 _ (F.configN.mat_mem_d8_of_T (inv_mem hq₂'T)), F.configN.ev_zero]
    rfl
  have hY2 : ∀ q, (q ∈ T ∧ ∀ z, (z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅z, q₁⁆, q₂⁆ = 1) →
      q * z = z * q) → q ∈ F.A ∨ q * F.dA.uv⁻¹ ∈ F.A := by
    rintro q ⟨hqT, hq⟩
    obtain ⟨q', hq'T, rfl⟩ := F.lift_T hqT
    have hfix : ∀ v ∈ W2, Arch76.matAct (F.configN.mat q') v = v := fun v hv => by
      rw [← F.configN.act_eq_matAct]
      exact F.evG_mul_comm_iff.mp (hq _ (hW2 v hv))
    rcases fix_W2 _ (F.configN.mat_mem_d8_of_T hq'T) with h | h | ⟨v, hv, hne⟩
    · left; exact hcen _ hqT (F.coe_mem_centralizer (F.configN.mem_centralizer_of_mat h))
    · right
      have h1 : F.configN.mat (q' * F.configN.uv⁻¹) = mI := by
        rw [Config.mat_mul, h, F.configN.uv_inv, F.configN.mat_uv_eq, mUV_eq]; decide
      have hmem : q' * F.configN.uv⁻¹ ∈
          F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} :=
        mul_mem hq'T (inv_mem F.configN.uv_mem_T)
      have h2 := hcen _ (F.coe_mem_T hmem)
        (F.coe_mem_centralizer (F.configN.mem_centralizer_of_mat h1))
      simpa using h2
    · exact absurd (hfix v hv) hne
  have hAY2 : ∀ q ∈ F.A, q ∈ T ∧ ∀ z, (z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅z, q₁⁆, q₂⁆ = 1) →
      q * z = z * q := fun q hq => ⟨Subgroup.mem_sup_left hq, fun z hz => F.A_comm hq (hZ2A z hz)⟩
  have hZ1sq : ∀ q, q * F.dA.uv⁻¹ ∈ F.A → q ^ 2 ∈ T ∧ ∀ q₁ ∈ T, q ^ 2 * q₁ = q₁ * q ^ 2 := by
    intro q hq
    obtain ⟨v, hv⟩ := F.exists_evG hq
    have hq' : q = ((F.configN.ev v * F.configN.uv : Subgroup.normalizer (F.A : Set G)) : G) := by
      rw [Subgroup.coe_mul, coe_configN_uv, show ((F.configN.ev v : _) : G) = F.evG v from rfl, hv]
      group
    have hsq : (F.configN.ev v * F.configN.uv) ^ 2 = F.configN.ev (v + fuv v) := by
      calc (F.configN.ev v * F.configN.uv) ^ 2 =
            F.configN.ev v * (F.configN.uv * F.configN.ev v) * F.configN.uv := by
              rw [pow_two]; group
        _ = F.configN.ev v * F.configN.ev (fuv v) * (F.configN.uv * F.configN.uv) := by
              rw [F.configN.uv_mul_ev]; group
        _ = F.configN.ev (v + fuv v) := by rw [← Config.ev_add, ← pow_two, F.configN.huv2, mul_one]
    have hW1 := sq_uv_mem v
    rw [hq', ← Subgroup.coe_pow, hsq]
    refine ⟨F.evG_mem_T _, fun q₁ hq₁ => ?_⟩
    obtain ⟨q₁', hq₁'T, rfl⟩ := F.lift_T hq₁
    have hfix := d8_fix_xy2 _ (F.configN.mat_mem_d8_of_T hq₁'T)
    have hact : F.configN.act q₁' (v + fuv v) = v + fuv v := by
      simp only [W1, List.mem_cons, List.not_mem_nil, or_false] at hW1
      rcases hW1 with h | h <;> rw [h]
      · exact F.configN.act_zero q₁'
      · rw [F.configN.act_eq_matAct]; exact hfix
    exact (F.evG_mul_comm_iff.mpr hact).symm
  have hx2 : ¬ (F.evG (0, 2, 0) ∈ T ∧ ∀ q₁ ∈ T, F.evG (0, 2, 0) * q₁ = q₁ * F.evG (0, 2, 0)) := by
    rintro ⟨-, h⟩
    have h1 := (h _ F.u_mem_T).symm
    rw [show F.dA.u = ((F.configN.u : Subgroup.normalizer (F.A : Set G)) : G) from rfl,
      F.evG_mul_comm_iff, F.configN.act_u] at h1
    exact absurd h1 (by decide)
  have hnc : ∀ q, q * F.dA.uv⁻¹ ∈ F.A → q * F.evG (0, 1, 0) ≠ F.evG (0, 1, 0) * q := by
    intro q hq h
    obtain ⟨v, hv⟩ := F.exists_evG hq
    have hq' : q = ((F.configN.ev v * F.configN.uv : Subgroup.normalizer (F.A : Set G)) : G) := by
      rw [Subgroup.coe_mul, coe_configN_uv, show ((F.configN.ev v : _) : G) = F.evG v from rfl, hv]
      group
    rw [hq', F.evG_mul_comm_iff, Config.act_mul, F.configN.act_of_mem_A (F.configN.ev_mem v),
      F.configN.act_uv] at h
    exact absurd h (by decide)
  have hchar : ∀ q, q ∈ F.A ↔ ((q ∈ T ∧ ∀ z, (z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅z, q₁⁆, q₂⁆ = 1) →
      q * z = z * q) ∧ ∀ q', (q' ∈ T ∧ ∀ z, (z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅z, q₁⁆, q₂⁆ = 1) →
        q' * z = z * q') → ¬ (q' ^ 2 ∈ T ∧ ∀ q₁ ∈ T, q' ^ 2 * q₁ = q₁ * q' ^ 2) →
          q * q' = q' * q) := by
    intro q
    constructor
    · intro hq
      refine ⟨hAY2 q hq, fun q' hq' hsq => ?_⟩
      rcases hY2 q' hq' with h | h
      · exact F.A_comm hq h
      · exact absurd (hZ1sq q' h) hsq
    · rintro ⟨hqY, hq⟩
      rcases hY2 q hqY with h | h
      · exact h
      · exfalso
        refine hnc q h (hq _ (hAY2 _ (F.evG_mem _)) ?_)
        have hsq : F.evG (0, 1, 0) ^ 2 = F.evG (0, 2, 0) := by
          show ((F.configN.ev (0, 1, 0) : Subgroup.normalizer (F.A : Set G)) : G) ^ 2 = _
          rw [← Subgroup.coe_pow, ← F.configN.ev_nsmul,
            show (2 • ((0, 1, 0) : Co)) = (0, 2, 0) by decide]
          rfl
        rw [hsq]
        exact hx2
  set σ := MulAut.conj g
  have hσ : ∀ x, σ x ∈ T ↔ x ∈ T := fun x => by
    rw [MulAut.conj_apply]; exact ((Subgroup.mem_normalizer_iff.mp hg) x).symm
  have hZ2σ : ∀ z, ((σ z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅σ z, q₁⁆, q₂⁆ = 1) ↔
      (z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅z, q₁⁆, q₂⁆ = 1)) := Z2_map_iff σ hσ
  have hforall : ∀ P : G → Prop, (∀ z, P (σ z)) ↔ ∀ z, P z := fun P =>
    ⟨fun h z => by simpa using h (σ.symm z), fun h z => h _⟩
  have hY2σ : ∀ q, ((σ q ∈ T ∧ ∀ z, (z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅z, q₁⁆, q₂⁆ = 1) →
      σ q * z = z * σ q) ↔ (q ∈ T ∧ ∀ z, (z ∈ T ∧ ∀ q₁ ∈ T, ∀ q₂ ∈ T, ⁅⁅z, q₁⁆, q₂⁆ = 1) →
        q * z = z * q)) := by
    intro q
    refine and_congr (hσ q) ?_
    rw [← hforall]
    simp only [hZ2σ, comm_map_iff σ hσ]
  have hZ1σ : ∀ z, ((σ z ∈ T ∧ ∀ q₁ ∈ T, σ z * q₁ = q₁ * σ z) ↔
      (z ∈ T ∧ ∀ q₁ ∈ T, z * q₁ = q₁ * z)) := Z1_map_iff σ hσ
  have hcharσ : ∀ q, σ q ∈ F.A ↔ q ∈ F.A := by
    intro q
    rw [hchar, hchar, hY2σ]
    refine and_congr Iff.rfl ?_
    rw [← hforall]
    simp only [hY2σ, ← map_pow, hZ1σ, comm_map_iff σ hσ]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← MulAut.conj_apply, hcharσ]

theorem normalizes_A_of_T₁
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) {s : G}
    (hsS : s ∈ (F.S : Subgroup G)) (hsN : s ∈ Subgroup.normalizer (F.A : Set G))
    (hs2 : s * s = 1) (hsc : s⁻¹ * (F.dA.c : G) * s = F.dA.c)
    (hsa : s⁻¹ * (F.dA.a : G) * s = (F.dA.a : G)⁻¹)
    (hsb : s⁻¹ * (F.dA.b : G) * s = (F.dA.b : G)⁻¹)
    (hsuv : s⁻¹ * F.dA.uv * s = (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ * F.dA.uv ∨
      s⁻¹ * F.dA.uv * s = (F.dA.a : G) * (F.dA.b : G)⁻¹ * F.dA.uv) {g : G}
    (hg : g ∈ Subgroup.normalizer
      ((F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, s} : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (F.A : Set G) := by
  set N := Subgroup.normalizer (F.A : Set G) with hN
  set s' : N := ⟨s, hsN⟩ with hs'
  set Q := F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, s} with hQ
  set QY := F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u, s'} with hQY
  have hQS : Q ≤ F.S := by
    refine sup_le F.A_le_S ?_
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    exacts [F.uv_mem_S, F.t_mem_S, F.u_mem_S, hsS]
  have hcen : ∀ q ∈ Q, q ∈ Subgroup.centralizer (F.A : Set G) → q ∈ F.A :=
    fun q hq h => F.mem_A_of_centralizer hCA (hQS hq) h
  have hQmap : QY.map N.subtype = Q := F.T_s_map s'
  have hlift : ∀ q ∈ Q, ∃ q' : N, q' ∈ QY ∧ (q' : G) = q := fun q hq => by
    rw [← hQmap] at hq
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨q', hq', rfl⟩
  have hcoe : ∀ q' : N, q' ∈ QY → (q' : G) ∈ Q := fun q' hq' => by
    rw [← hQmap]; exact Subgroup.mem_map_of_mem _ hq'
  have hAQY : ∀ v, F.configN.ev v ∈ QY := fun v => Subgroup.mem_sup_left (F.configN.ev_mem v)
  have huvY : F.configN.uv ∈ QY := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have htY : F.configN.t ∈ QY := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have huY : F.configN.u ∈ QY := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hsY : s' ∈ QY := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hs2' : s'⁻¹ = s' := Subtype.ext (inv_eq_of_mul_eq_one_right hs2)
  have h1 : F.configN.act s' (1, 0, 0) = (1, 0, 0) := F.configN.act_eq_of (by
    rw [F.configN.ev_w]
    exact Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_configN_w]; exact hsc.symm))
  have h2 : F.configN.act s' X0 = (0, 3, 0) := F.configN.act_eq_of (by
    rw [F.configN.ev_030, show X0 = (0, 1, 0) from rfl, F.configN.ev_x]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_configN_x]
    rw [show s⁻¹ * (F.dA.a : G)⁻¹ * s = (s⁻¹ * (F.dA.a : G) * s)⁻¹ by group, hsa])
  have h3 : F.configN.act s' Y0 = (0, 0, 3) := F.configN.act_eq_of (by
    rw [F.configN.ev_003, show Y0 = (0, 0, 1) from rfl, F.configN.ev_y]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_configN_y]
    rw [show s⁻¹ * (F.dA.b : G)⁻¹ * s = (s⁻¹ * (F.dA.b : G) * s)⁻¹ by group, hsb])
  have hmat : F.configN.mat s' = mS := by
    show (F.configN.act s' (1, 0, 0), F.configN.act s' X0, F.configN.act s' Y0) = mS
    rw [h1, h2, h3]; rfl
  have hsinv : ∀ v, F.configN.act s'⁻¹ v = kmap al0 v := fun v => by
    rw [hs2', F.configN.act_eq_matAct, hmat, kmap_al0_eq]
  obtain ⟨va, hva, hsuv'⟩ : ∃ va ∈ [((0, 1, 1) : Co), (0, 3, 1)],
      s'⁻¹ * F.configN.uv * s' = F.configN.ev va * F.configN.uv := by
    rcases hsuv with h | h
    · refine ⟨(0, 1, 1), by simp, Subtype.ext ?_⟩
      rw [F.configN.ev_011]
      simpa using h
    · refine ⟨(0, 3, 1), by simp, Subtype.ext ?_⟩
      rw [F.configN.ev_031]
      simpa using h
  have hdQY : ∀ q' ∈ QY, F.configN.mat q' ∈ d16 := fun q' hq' =>
    F.configN.mat_mem_d16_of_T₁ hmat hs2' hq'
  have hgen : ∀ G' ∈ gens16, ∃ g' : N, g' ∈ QY ∧ (∀ v, F.configN.act g'⁻¹ v = Arch76.matAct G' v) ∧
      F.configN.mat g' = G' ∧ g'⁻¹ = g' := by
    intro G' hG'
    simp only [gens16, List.mem_cons, List.not_mem_nil, or_false] at hG'
    rcases hG' with rfl | rfl | rfl | rfl
    · exact ⟨_, huvY, F.configN.act_uv_inv_eq, by rw [F.configN.mat_uv_eq, mUV_eq],
        F.configN.uv_inv⟩
    · exact ⟨_, htY, F.configN.act_t_inv_eq, by rw [F.configN.mat_t_eq, mT_eq],
        F.configN.t_inv⟩
    · exact ⟨_, huY, F.configN.act_u_inv_eq, by rw [F.configN.mat_u_eq, mU_eq],
        F.configN.u_inv⟩
    · exact ⟨_, hsY, fun v => by rw [hsinv, kmap_al0_eq], hmat, hs2'⟩
  have hZ3A : ∀ z, (z ∈ Q ∧ ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ q₃ ∈ Q, ⁅⁅⁅z, q₁⁆, q₂⁆, q₃⁆ = 1) →
      z ∈ F.A := by
    rintro z ⟨hzQ, hz⟩
    obtain ⟨z', hz'Q, rfl⟩ := hlift z hzQ
    have hY : ∀ q₁ q₂ q₃ : N, q₁ ∈ QY → q₂ ∈ QY → q₃ ∈ QY → ⁅⁅⁅z', q₁⁆, q₂⁆, q₃⁆ = 1 := by
      intro q₁ q₂ q₃ h₁ h₂ h₃
      have := hz _ (hcoe _ h₁) _ (hcoe _ h₂) _ (hcoe _ h₃)
      rw [← F.coe_comm, ← F.coe_comm, ← F.coe_comm] at this
      exact Subtype.ext this
    have hM := hdQY _ hz'Q
    have hM' := hdQY _ (inv_mem hz'Q)
    have hMM := F.configN.mat_mul_inv z'
    have hM'v8 : F.configN.mat z'⁻¹ ∈ v8 := by
      rcases Z3_mat_a _ hM' with h | ⟨e, -, G₂, hG₂, G₃, hG₃, hne⟩
      · exact h
      · exfalso
        apply hne
        obtain ⟨g₂, hg₂, hact₂, -, -⟩ := hgen G₂ hG₂
        obtain ⟨g₃, hg₃, hact₃, -, -⟩ := hgen G₃ hG₃
        have h := hY _ _ _ (hAQY e) hg₂ hg₃
        rw [F.configN.comm_left_ev, F.configN.comm_ev_right, F.configN.comm_ev_right,
          F.configN.ev_eq_one_iff, F.configN.act_eq_matAct z'⁻¹, hact₂, hact₃] at h
        exact h
    have hMv8 := v8_inv _ hM _ hM'v8 hMM
    have hM4 : F.configN.mat z' ∈ [mI, lUV, mS, lUVS] := by
      rcases Z3_mat_b hMv8 hM'v8 hMM with h | ⟨G₁, hG₁, e, -, G₃, hG₃, hne⟩
      · exact h
      · exfalso
        apply hne
        obtain ⟨g₁, hg₁, -, hmat₁, hinv₁⟩ := hgen G₁ hG₁
        obtain ⟨g₃, hg₃, hact₃, -, -⟩ := hgen G₃ hG₃
        have h := hY _ _ _ hg₁ (hAQY e) hg₃
        have hinv : (⁅z', g₁⁆)⁻¹ = g₁ * z' * g₁⁻¹ * z'⁻¹ := by
          rw [commutatorElement_def]; group
        have hmatc : F.configN.mat (⁅z', g₁⁆)⁻¹ =
            matMul (matMul (matMul G₁ (F.configN.mat z')) G₁) (F.configN.mat z'⁻¹) := by
          rw [hinv, Config.mat_mul, Config.mat_mul, Config.mat_mul, hinv₁, hmat₁]
        rw [F.configN.comm_left_ev, F.configN.comm_ev_right, F.configN.ev_eq_one_iff,
          F.configN.act_eq_matAct (⁅z', g₁⁆)⁻¹, hmatc, hact₃] at h
        exact h
    have hcenY : ∀ q' ∈ QY, F.configN.mat q' = mI → q' ∈ F.configN.A := fun q' hq' h =>
      Subgroup.mem_subgroupOf.mpr
        (hcen _ (hcoe _ hq') (F.coe_mem_centralizer (F.configN.mem_centralizer_of_mat h)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM4
    rcases hM4 with h | h | h | h
    · exact hcen _ hzQ (F.coe_mem_centralizer (F.configN.mem_centralizer_of_mat h))
    · exfalso
      have hm : F.configN.mat (z' * F.configN.uv⁻¹) = mI := by
        rw [Config.mat_mul, h, F.configN.uv_inv, F.configN.mat_uv_eq, mUV_eq, matMul_uv_uv]
      obtain ⟨v', hv'⟩ := F.configN.exists_ev (hcenY _ (mul_mem hz'Q (inv_mem huvY)) hm)
      have hz' : z' = F.configN.ev v' * F.configN.uv := by rw [hv']; group
      have hh := hY _ _ _ hsY htY huY
      rw [hz', F.configN.comm_ev_mul, F.configN.comm_uv_s hsuv', ← Config.ev_add, ← Config.ev_add,
        F.configN.comm_ev_right, F.configN.comm_ev_right, F.configN.ev_eq_one_iff,
        F.configN.act_t_inv, F.configN.act_u_inv, F.configN.act_neg, hsinv, hsinv,
        ← sub_eq_add_neg] at hh
      exact (Z3_rest va hva v').1 hh
    · exfalso
      have hm : F.configN.mat (z' * s'⁻¹) = mI := by
        rw [Config.mat_mul, h, hs2', hmat, matMul_s_s]
      obtain ⟨v', hv'⟩ := F.configN.exists_ev (hcenY _ (mul_mem hz'Q (inv_mem hsY)) hm)
      have hz' : z' = F.configN.ev v' * s' := by rw [hv']; group
      have hh := hY _ _ _ huvY htY huY
      rw [hz', F.configN.comm_ev_mul, F.configN.comm_s_uv hs2' hsuv', ← Config.ev_add,
        ← Config.ev_add, F.configN.comm_ev_right, F.configN.comm_ev_right,
        F.configN.ev_eq_one_iff, F.configN.act_t_inv, F.configN.act_u_inv, F.configN.act_neg,
        F.configN.act_uv_inv, ← sub_eq_add_neg] at hh
      exact (Z3_rest va hva v').2.1 hh
    · exfalso
      have hm : F.configN.mat (z' * (F.configN.uv * s')⁻¹) = mI := by
        rw [Config.mat_mul, h, mul_inv_rev, Config.mat_mul, hs2', hmat, F.configN.uv_inv,
          F.configN.mat_uv_eq, mUV_eq, lUVS_eq, matMul_uvs_inv]
      obtain ⟨v', hv'⟩ := F.configN.exists_ev
        (hcenY _ (mul_mem hz'Q (inv_mem (mul_mem huvY hsY))) hm)
      have hz' : z' = F.configN.ev v' * (F.configN.uv * s') := by rw [hv']; group
      have hh := hY _ _ _ huvY htY huY
      rw [hz', F.configN.comm_ev_mul, F.configN.comm_uvs_uv hs2' hsuv', ← Config.ev_add,
        ← Config.ev_add, F.configN.comm_ev_right, F.configN.comm_ev_right,
        F.configN.ev_eq_one_iff, F.configN.act_t_inv, F.configN.act_u_inv, F.configN.act_neg,
        F.configN.act_uv_inv, ← sub_eq_add_neg] at hh
      exact (Z3_rest va hva v').2.2 hh
  have hW3 : ∀ v ∈ W3, F.evG v ∈ Q ∧ ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ q₃ ∈ Q,
      ⁅⁅⁅F.evG v, q₁⁆, q₂⁆, q₃⁆ = 1 := by
    intro v hv
    refine ⟨Subgroup.mem_sup_left (F.evG_mem v), fun q₁ hq₁ q₂ hq₂ q₃ hq₃ => ?_⟩
    obtain ⟨q₁', hq₁', rfl⟩ := hlift q₁ hq₁
    obtain ⟨q₂', hq₂', rfl⟩ := hlift q₂ hq₂
    obtain ⟨q₃', hq₃', rfl⟩ := hlift q₃ hq₃
    rw [show F.evG v = ((F.configN.ev v : N) : G) from rfl, ← F.coe_comm, ← F.coe_comm,
      ← F.coe_comm, F.configN.comm_ev_right, F.configN.comm_ev_right, F.configN.comm_ev_right,
      F.configN.act_eq_matAct q₁'⁻¹, F.configN.act_eq_matAct q₂'⁻¹,
      F.configN.act_eq_matAct q₃'⁻¹]
    have k1 := W3_step v hv _ (hdQY _ (inv_mem hq₁'))
    have k2 := W2_step16 _ k1 _ (hdQY _ (inv_mem hq₂'))
    rw [W1_step16 _ k2 _ (hdQY _ (inv_mem hq₃')), F.configN.ev_zero]
    rfl
  have hchar : ∀ q, q ∈ F.A ↔ (q ∈ Q ∧ ∀ z, (z ∈ Q ∧ ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ q₃ ∈ Q,
      ⁅⁅⁅z, q₁⁆, q₂⁆, q₃⁆ = 1) → q * z = z * q) := by
    intro q
    constructor
    · intro hq
      exact ⟨Subgroup.mem_sup_left hq, fun z hz => F.A_comm hq (hZ3A z hz)⟩
    · rintro ⟨hqQ, hq⟩
      obtain ⟨q', hq', rfl⟩ := hlift q hqQ
      rcases fix_W3 _ (hdQY _ hq') with h | ⟨v, hv, hne⟩
      · exact hcen _ hqQ (F.coe_mem_centralizer (F.configN.mem_centralizer_of_mat h))
      · exfalso
        apply hne
        rw [← F.configN.act_eq_matAct]
        exact F.evG_mul_comm_iff.mp (hq _ (hW3 v hv))
  set σ := MulAut.conj g
  have hσ : ∀ x, σ x ∈ Q ↔ x ∈ Q := fun x => by
    rw [MulAut.conj_apply]; exact ((Subgroup.mem_normalizer_iff.mp hg) x).symm
  have hforall : ∀ P : G → Prop, (∀ z, P (σ z)) ↔ ∀ z, P z := fun P =>
    ⟨fun h z => by simpa using h (σ.symm z), fun h z => h _⟩
  have hcharσ : ∀ q, σ q ∈ F.A ↔ q ∈ F.A := by
    intro q
    rw [hchar, hchar]
    refine and_congr (hσ q) ?_
    rw [← hforall]
    simp only [Z3_map_iff σ hσ, comm_map_iff σ hσ]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← MulAut.conj_apply, hcharσ]

theorem le_normalizer_A
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) :
    (F.S : Subgroup G) ≤ Subgroup.normalizer (F.A : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (F.A : Set G) with hN
  set Q := (F.S : Subgroup G) ⊓ N with hQ
  have hQN : ∀ g : G, g ∈ Subgroup.normalizer (Q : Set G) → g ∈ N := by
    intro g hg
    rcases F.arch76Lemma2_normalizer hCA with h | ⟨s, hs, hQeq, hs2, hsc, hsa, hsb, hrel⟩
    · rw [hQ, h] at hg
      exact F.normalizes_A_of_T hCA hg
    · rw [hQ, hQeq] at hg
      exact F.normalizes_A_of_T₁ hCA (Subgroup.mem_inf.mp hs).1 (Subgroup.mem_inf.mp hs).2 hs2
        hsc hsa hsb (hrel.imp (fun h => h.1) (fun h => h.1)) hg
  haveI : Group.IsNilpotent (F.S : Subgroup G) := F.S.isPGroup'.isNilpotent
  set Q' := Q.subgroupOf (F.S : Subgroup G) with hQ'
  have hself : Subgroup.normalizer (Q' : Set (F.S : Subgroup G)) = Q' := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    have hxQ : (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.mem_normalizer_iff] at hx ⊢
      intro h
      by_cases hhS : h ∈ (F.S : Subgroup G)
      · have := hx ⟨h, hhS⟩
        simpa [Q', Subgroup.mem_subgroupOf] using this
      · constructor
        · intro hh; exact absurd (Subgroup.mem_inf.mp hh).1 hhS
        · intro hh
          exfalso
          apply hhS
          have h1 := mul_mem (mul_mem (inv_mem x.2) (Subgroup.mem_inf.mp hh).1) x.2
          rwa [show (x : G)⁻¹ * ((x : G) * h * (x : G)⁻¹) * x = h by group] at h1
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨x.2, hQN _ hxQ⟩)
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    normalizerCondition_of_isNilpotent) Q' hself
  intro g hg
  have hmem : (⟨g, hg⟩ : (F.S : Subgroup G)) ∈ Q' := htop ▸ Subgroup.mem_top _
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2

theorem arch76Lemma2
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) :
    (F.S : Subgroup G) = F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ∨
    ∃ s ∈ (F.S : Subgroup G),
      (F.S : Subgroup G) = F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, s} ∧ s * s = 1 ∧
      s⁻¹ * (F.dA.c : G) * s = F.dA.c ∧ s⁻¹ * (F.dA.a : G) * s = (F.dA.a : G)⁻¹ ∧
      s⁻¹ * (F.dA.b : G) * s = (F.dA.b : G)⁻¹ ∧
      ((s⁻¹ * F.dA.uv * s = (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ * F.dA.uv ∧
          s⁻¹ * F.dA.t * s = (F.dA.a : G) * F.dA.t ∧ s⁻¹ * F.dA.u * s = F.dA.u) ∨
        (s⁻¹ * F.dA.uv * s = (F.dA.a : G) * (F.dA.b : G)⁻¹ * F.dA.uv ∧
          s⁻¹ * F.dA.t * s = (F.dA.a : G) * (F.dA.b : G) ^ 2 * F.dA.t ∧
          s⁻¹ * F.dA.u * s = (F.dA.c : G) * F.dA.u)) := by
  have hQ : (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G) = F.S :=
    inf_eq_left.mpr (F.le_normalizer_A hCA)
  have h := F.arch76Lemma2_normalizer hCA
  rw [hQ] at h
  exact h

end StrothFrame

end CFSG.CGT.Stroth77
