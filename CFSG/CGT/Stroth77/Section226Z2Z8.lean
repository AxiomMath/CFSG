module

public import CFSG.CGT.Stroth77.Section226Z2Z8Fin
public import CFSG.CGT.Stroth77.Stroth34Layer
public import CFSG.CGT.Stroth77.Section41

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open Sec226Z

theorem torus_eq_val_smul {k : Fin 3 → ℕ} (w : Torus k) :
    w = (w 0).val • gen k 0 + (w 1).val • gen k 1 + (w 2).val • gen k 2 := by
  funext i
  fin_cases i <;> simp [gen, -nsmul_eq_mul]

namespace StrothWeakTypeData

variable {G : Type} [Group G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

@[expose] noncomputable def shiftOf {x : G} (hx : x ∈ Subgroup.normalizer (D : Set G)) : Pair τ :=
  (dD.thetaT hx (gen τ.k 1) - gen τ.k 1, dD.thetaT hx (gen τ.k 2) - gen τ.k 2)

theorem thetaT_eq_add_βlin {x : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hc : dD.thetaT hx (gen τ.k 0) = gen τ.k 0) (w : Torus τ.k) :
    dD.thetaT hx w = w + βlin τ (dD.shiftOf hx) w := by
  have ha : dD.thetaT hx (gen τ.k 1) = gen τ.k 1 + (dD.shiftOf hx).1 := by
    simp [shiftOf]
  have hb : dD.thetaT hx (gen τ.k 2) = gen τ.k 2 + (dD.shiftOf hx).2 := by
    simp [shiftOf]
  calc dD.thetaT hx w
      = dD.thetaT hx ((w 0).val • gen τ.k 0 + (w 1).val • gen τ.k 1 + (w 2).val • gen τ.k 2) := by
        rw [← torus_eq_val_smul w]
    _ = ((w 0).val • gen τ.k 0 + (w 1).val • gen τ.k 1 + (w 2).val • gen τ.k 2) +
          ((w 1).val • (dD.shiftOf hx).1 + (w 2).val • (dD.shiftOf hx).2) := by
        rw [map_add, map_add, map_nsmul, map_nsmul, map_nsmul, hc, ha, hb, smul_add, smul_add]
        abel
    _ = w + βlin τ (dD.shiftOf hx) w := by rw [← torus_eq_val_smul w]; rfl

theorem shiftOf_of_mem {d : G} (hd : d ∈ D) (hdN : d ∈ Subgroup.normalizer (D : Set G)) :
    dD.shiftOf hdN = 0 := by
  simp [shiftOf, dD.thetaT_of_mem hdN hd]

@[expose] noncomputable def coc (g : G) : Pair τ :=
  (crdT dD.e (g⁻¹ * dD.uv * g * dD.uv⁻¹), crdT dD.e (g⁻¹ * dD.t * g * dD.t⁻¹))

theorem coc_mul_mem {g d : G} (huv : g⁻¹ * dD.uv * g * dD.uv⁻¹ ∈ D)
    (ht : g⁻¹ * dD.t * g * dD.t⁻¹ ∈ D) (hd : d ∈ D) :
    dD.coc (g * d) = dD.coc g + cob τ (crdT dD.e d) := by
  obtain ⟨-, c1⟩ := crdT_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv hd
  obtain ⟨-, c2⟩ := crdT_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht hd
  refine Prod.ext ?_ ?_
  · show crdT dD.e ((g * d)⁻¹ * dD.uv * (g * d) * dD.uv⁻¹) =
      crdT dD.e (g⁻¹ * dD.uv * g * dD.uv⁻¹) + (τ.action.φuv (crdT dD.e d) - crdT dD.e d)
    rw [c1]
    abel
  · show crdT dD.e ((g * d)⁻¹ * dD.t * (g * d) * dD.t⁻¹) =
      crdT dD.e (g⁻¹ * dD.t * g * dD.t⁻¹) + (τ.action.φt (crdT dD.e d) - crdT dD.e d)
    rw [c2]
    abel

theorem isCoc_coc {g : G} (huv : g⁻¹ * dD.uv * g * dD.uv⁻¹ ∈ D)
    (ht : g⁻¹ * dD.t * g * dD.t⁻¹ ∈ D) : IsCoc τ (dD.coc g) :=
  cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem dD.uv_conj dD.t_conj huv ht

end StrothWeakTypeData

namespace Sec226Z

structure Facts (τ : StrothTypeIndex) : Prop where
  card4 : Nat.card {w : Torus τ.k // 4 • w = 0} ≤ 32
  c4 : 4 • gen τ.k 0 = 0
  a8 : 8 • gen τ.k 1 = 0
  b8 : 8 • gen τ.k 2 = 0
  a5 : gen τ.k 1 + (w₂ τ).1 = 5 • gen τ.k 1
  b5 : gen τ.k 2 + (w₂ τ).2 = 5 • gen τ.k 2
  inv_even : ∀ v : Torus τ.k, v + v = 0 → 2 ∣ (v 1).val ∧ 2 ∣ (v 2).val
  w4 : ∀ m : Pair τ, IsCoc τ m → ∃ d : Torus τ.k, W4Hyp τ (m + cob τ d) → W4Concl τ (m + cob τ d)
  u2 : ∀ m : Pair τ, U2Hyp τ m → U2Concl τ m
  eFact : EFact τ
  comm : ∀ β : Pair τ, IsShift τ β → IsShift16 τ (actUv τ β + β) ∧ IsShift16 τ (actT τ β + β)
  fix : ∀ β : Pair τ, IsShift τ β → (actUv τ β + β = 0 ∨ actUv τ β + β = w₂ τ) →
    (actT τ β + β = 0 ∨ actT τ β + β = w₂ τ) → IsShift16 τ β
  socle : ∀ β : Pair τ, IsShift16 τ β → β ≠ 0 → β ≠ w₂ τ →
    (actRho τ β + actRho τ (actRho τ β) = β₁ τ ∨ actRho τ β + actRho τ (actRho τ β) = β₂ τ ∨
      actRho τ β + actRho τ (actRho τ β) = β₃ τ) ∨
    (actRho τ β + actRho τ (actRho τ β) = 0 ∧ (β = β₅ τ ∨ β = β₆ τ))
  orbit₁ : OrbitFact₁ τ
  orbit₅ : OrbitFact₅ τ
  sum : SumFact τ

theorem card4_t200 : Nat.card {w : Torus τ₀.k // 4 • w = 0} ≤ 32 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem card4_t201 : Nat.card {w : Torus τ₁.k // 4 • w = 0} ≤ 32 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem facts_t200 : Facts τ₀ where
  card4 := card4_t200
  c4 := by decide
  a8 := by decide
  b8 := by decide
  a5 := by decide
  b5 := by decide
  inv_even := by decide +kernel
  w4 := fun m hm => by
    obtain ⟨d, hd⟩ := exists_rep_t200 m.1 m.2 hm
    exact ⟨d, w4_finite_t200 _ _ hd⟩
  u2 := fun m => u2_finite_t200 m.1 m.2
  eFact := eFact_t200
  comm := fun β => commFact_t200 β.1 β.2
  fix := fun β => fixFact_t200 β.1 β.2
  socle := fun β => socleFact_t200 β.1 β.2
  orbit₁ := orbitFact₁_t200
  orbit₅ := orbitFact₅_t200
  sum := sumFact_t200

theorem facts_t201 : Facts τ₁ where
  card4 := card4_t201
  c4 := by decide
  a8 := by decide
  b8 := by decide
  a5 := by decide
  b5 := by decide
  inv_even := by decide +kernel
  w4 := fun m hm => by
    obtain ⟨d, hd⟩ := exists_rep_t201 m.1 m.2 hm
    exact ⟨d, w4_finite_t201 _ _ hd⟩
  u2 := fun m => u2_finite_t201 m.1 m.2
  eFact := eFact_t201
  comm := fun β => commFact_t201 β.1 β.2
  fix := fun β => fixFact_t201 β.1 β.2
  socle := fun β => socleFact_t201 β.1 β.2
  orbit₁ := orbitFact₁_t201
  orbit₅ := orbitFact₅_t201
  sum := sumFact_t201

theorem βlin_eq_zero_of_inv {τ : StrothTypeIndex} (hF : Facts τ) {β : Pair τ}
    (hβ : IsShift τ β) {v : Torus τ.k} (hv : v + v = 0) : βlin τ β v = 0 := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hF.inv_even v hv
  obtain ⟨h1, h2⟩ := hβ
  unfold βlin
  rw [hi, hj, mul_nsmul', mul_nsmul', two_nsmul, two_nsmul, ← nsmul_add, ← nsmul_add, h1, h2,
    nsmul_zero, nsmul_zero, add_zero]

end Sec226Z

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem crdT_four_smul_of_mem_A (h : F.IsD D dD) {y : G} (hy : y ∈ F.A) :
    4 • crdT dD.e y = 0 := by
  have hyD := h.A_le hy
  have h4 : y ^ 4 = 1 := by
    have e : F.dA.ofTorus (F.dA.e (Additive.ofMul ⟨y, hy⟩)) = y := F.dA.ofTorus_e ⟨y, hy⟩
    rw [← e, ← F.dA.ofTorus_nsmul,
      show ∀ v : Torus (StrothTypeIndex.t100 1).k, 4 • v = 0 by decide +kernel, F.dA.ofTorus_zero]
  have e2 : crdT dD.e (y ^ 4) = 4 • crdT dD.e y := by
    rw [show y ^ 4 = y * y * y * y by
        rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one],
      crdT_mul dD.e (mul_mem (mul_mem hyD hyD) hyD) hyD, crdT_mul dD.e (mul_mem hyD hyD) hyD,
      crdT_mul dD.e hyD hyD]
    abel
  rw [← e2, h4, crdT_one]

theorem mem_A_of_four_smul (h : F.IsD D dD) (hcard : Nat.card {w : Torus τ.k // 4 • w = 0} ≤ 32)
    {g : G} (hg : g ∈ D) (h4 : 4 • crdT dD.e g = 0) : g ∈ F.A := by
  let f : F.A → {w : Torus τ.k // 4 • w = 0} :=
    fun y => ⟨crdT dD.e y, h.crdT_four_smul_of_mem_A y.2⟩
  have hf : Function.Injective f := fun y z hyz => Subtype.ext
    (crdT_inj dD.e (h.A_le y.2) (h.A_le z.2) (congrArg Subtype.val hyz))
  have hA : Nat.card F.A = 32 := F.dA.card_eq_32
  obtain ⟨y, hy⟩ := (hf.bijective_of_nat_card_le (by omega)).2 ⟨crdT dD.e g, h4⟩
  have := crdT_inj dD.e (h.A_le y.2) hg (congrArg Subtype.val hy)
  rw [← this]
  exact y.2

theorem centralizer_A_le (h : F.IsD D dD) :
    Subgroup.centralizer ((F.A : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  apply Subgroup.centralizer_le
  rw [h.omegaIn_one_eq]
  exact omegaIn_le 1 F.A

theorem mem_centralizer_A_of_mem (h : F.IsD D dD) {d : G} (hd : d ∈ D) :
    d ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨y, h.A_le hy⟩ ⟨d, hd⟩)

variable (hF : Sec226Z.Facts τ)
include hF

theorem c_mem_A (h : F.IsD D dD) : (dD.c : G) ∈ F.A := by
  refine h.mem_A_of_four_smul hF.card4 dD.c.2 ?_
  rw [dD.c_eq_ofT, dD.crdT_ofT]
  exact hF.c4

theorem a_sq_mem_A (h : F.IsD D dD) : (dD.a : G) ^ 2 ∈ F.A := by
  refine h.mem_A_of_four_smul hF.card4 (pow_mem dD.a.2 2) ?_
  rw [pow_two, crdT_mul dD.e dD.a.2 dD.a.2, show (dD.a : G) = dD.ofT (gen τ.k 1) from rfl,
    dD.crdT_ofT, ← two_nsmul, ← mul_nsmul']
  exact hF.a8

theorem b_sq_mem_A (h : F.IsD D dD) : (dD.b : G) ^ 2 ∈ F.A := by
  refine h.mem_A_of_four_smul hF.card4 (pow_mem dD.b.2 2) ?_
  rw [pow_two, crdT_mul dD.e dD.b.2 dD.b.2, show (dD.b : G) = dD.ofT (gen τ.k 2) from rfl,
    dD.crdT_ofT, ← two_nsmul, ← mul_nsmul']
  exact hF.b8

theorem thetaT_c (h : F.IsD D dD) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    dD.thetaT hxN (gen τ.k 0) = gen τ.k 0 := by
  have hc := Subgroup.mem_centralizer_iff.mp hxA _ (h.c_mem_A hF)
  rw [show gen τ.k 0 = crdT dD.e (dD.c : G) by rw [dD.c_eq_ofT, dD.crdT_ofT],
    dD.thetaT_crdT hxN dD.c.2, mul_assoc, hc, inv_mul_cancel_left]

theorem isShift_shiftOf (h : F.IsD D dD) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    IsShift τ (dD.shiftOf hxN) := by
  have key : ∀ (j : Fin 3) (g : G), g ∈ D → g = dD.ofT (gen τ.k j) → g ^ 2 ∈ F.A →
      dD.thetaT hxN (gen τ.k j) - gen τ.k j + (dD.thetaT hxN (gen τ.k j) - gen τ.k j) = 0 := by
    intro j g hgD hg hgA
    have hc := Subgroup.mem_centralizer_iff.mp hxA _ hgA
    have e1 : dD.thetaT hxN (2 • gen τ.k j) = 2 • gen τ.k j := by
      rw [show 2 • gen τ.k j = crdT dD.e (g ^ 2) by
          rw [pow_two, crdT_mul dD.e hgD hgD, hg, dD.crdT_ofT, two_nsmul],
        dD.thetaT_crdT hxN (pow_mem hgD 2), mul_assoc, hc, inv_mul_cancel_left]
    rw [map_nsmul, two_nsmul, two_nsmul] at e1
    rw [sub_add_sub_comm, e1, sub_self]
  exact ⟨key 1 _ dD.a.2 rfl (h.a_sq_mem_A hF), key 2 _ dD.b.2 rfl (h.b_sq_mem_A hF)⟩

theorem thetaT_eq (h : F.IsD D dD) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) (w : Torus τ.k) :
    dD.thetaT hxN w = w + βlin τ (dD.shiftOf hxN) w :=
  dD.thetaT_eq_add_βlin hxN (h.thetaT_c hF hxN hxA) w

theorem shiftOf_mul (h : F.IsD D dD) {x y : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (hyA : y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    dD.shiftOf (mul_mem hxN hyN) = dD.shiftOf hxN + dD.shiftOf hyN := by
  have hx := h.isShift_shiftOf hF hxN hxA
  have key : ∀ j : Fin 3, j = 1 ∨ j = 2 →
      dD.thetaT (mul_mem hxN hyN) (gen τ.k j) - gen τ.k j =
        (dD.thetaT hxN (gen τ.k j) - gen τ.k j) + (dD.thetaT hyN (gen τ.k j) - gen τ.k j) := by
    intro j hj
    have hinv : dD.thetaT hxN (gen τ.k j) - gen τ.k j +
        (dD.thetaT hxN (gen τ.k j) - gen τ.k j) = 0 := by
      rcases hj with rfl | rfl
      · exact hx.1
      · exact hx.2
    rw [dD.thetaT_mul hxN hyN,
      show dD.thetaT hxN (gen τ.k j) = gen τ.k j + (dD.thetaT hxN (gen τ.k j) - gen τ.k j) by
        abel, map_add, h.thetaT_eq hF hyN hyA (dD.thetaT hxN (gen τ.k j) - gen τ.k j),
      Sec226Z.βlin_eq_zero_of_inv hF (h.isShift_shiftOf hF hyN hyA) hinv]
    abel
  exact Prod.ext (key 1 (Or.inl rfl)) (key 2 (Or.inr rfl))

theorem mem_of_shiftOf_eq_zero (h : F.IsD D dD) {x : G} (hxS : x ∈ (F.S : Subgroup G))
    (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (h0 : dD.shiftOf hxN = 0) : x ∈ D := by
  refine h.mem_of_mem_centralizer hxS (Subgroup.mem_centralizer_iff.mpr fun d hd => ?_)
  have e := h.thetaT_eq hF hxN hxA (crdT dD.e d)
  rw [h0, dD.thetaT_crdT hxN hd] at e
  have e' : x⁻¹ * d * x = d := by
    refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp hxN d).mp hd) hd ?_
    rw [e]
    simp [βlin]
  calc d * x = x * (x⁻¹ * d * x) := by group
    _ = x * d := by rw [e']

theorem shiftOf_mul_mem (h : F.IsD D dD) {x d : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) (hd : d ∈ D) :
    dD.shiftOf (mul_mem hxN (Subgroup.le_normalizer hd)) = dD.shiftOf hxN := by
  rw [h.shiftOf_mul hF hxN hxA (Subgroup.le_normalizer hd) (h.mem_centralizer_A_of_mem hd),
    dD.shiftOf_of_mem hd, add_zero]

theorem shiftOf_inv (h : F.IsD D dD) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    dD.shiftOf (inv_mem hxN) = -dD.shiftOf hxN := by
  have e := h.shiftOf_mul hF (inv_mem hxN) (inv_mem hxA) hxN hxA
  have h1 : x⁻¹ * x ∈ D := by rw [inv_mul_cancel]; exact one_mem D
  rw [dD.shiftOf_of_mem h1] at e
  exact (neg_eq_of_add_eq_zero_left e.symm).symm

theorem inv_mul_mem_of_shiftOf_eq (h : F.IsD D dD) {x y : G} (hxS : x ∈ (F.S : Subgroup G))
    (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hyS : y ∈ (F.S : Subgroup G)) (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (hyA : y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (he : dD.shiftOf hxN = dD.shiftOf hyN) : x⁻¹ * y ∈ D := by
  refine h.mem_of_shiftOf_eq_zero hF (mul_mem (inv_mem hxS) hyS) (mul_mem (inv_mem hxN) hyN)
    (mul_mem (inv_mem hxA) hyA) ?_
  rw [h.shiftOf_mul hF (inv_mem hxN) (inv_mem hxA) hyN hyA, h.shiftOf_inv hF hxN hxA, he,
    neg_add_cancel]

theorem shiftOf_eq_of_mul_inv_mem (h : F.IsD D dD) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (hyA : y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) (hxy : x * y⁻¹ ∈ D) :
    dD.shiftOf hxN = dD.shiftOf hyN := by
  have e := h.shiftOf_mul hF hxN hxA (inv_mem hyN) (inv_mem hyA)
  rw [dD.shiftOf_of_mem hxy, h.shiftOf_inv hF hyN hyA] at e
  exact add_neg_eq_zero.mp e.symm

theorem coc_mul_of_mem_centralizer (h : F.IsD D dD) {e f : G}
    (hfN : f ∈ Subgroup.normalizer (D : Set G))
    (hfA : f ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (heuv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D) (het : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D)
    (hfuv : f⁻¹ * dD.uv * f * dD.uv⁻¹ ∈ D) (hft : f⁻¹ * dD.t * f * dD.t⁻¹ ∈ D) :
    dD.coc (e * f) = dD.coc e + βapp τ (dD.shiftOf hfN) (dD.coc e) + dD.coc f := by
  obtain ⟨-, c1⟩ := dD.crdT_cocycle_mul hfN heuv hfuv
  obtain ⟨-, c2⟩ := dD.crdT_cocycle_mul hfN het hft
  refine Prod.ext ?_ ?_
  · show crdT dD.e ((e * f)⁻¹ * dD.uv * (e * f) * dD.uv⁻¹) =
      crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) +
        βlin τ (dD.shiftOf hfN) (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹)) +
        crdT dD.e (f⁻¹ * dD.uv * f * dD.uv⁻¹)
    rw [c1, h.thetaT_eq hF hfN hfA]
  · show crdT dD.e ((e * f)⁻¹ * dD.t * (e * f) * dD.t⁻¹) =
      crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) +
        βlin τ (dD.shiftOf hfN) (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹)) +
        crdT dD.e (f⁻¹ * dD.t * f * dD.t⁻¹)
    rw [c2, h.thetaT_eq hF hfN hfA]

end StrothFrame.IsD

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem conj_mem_centralizer_A {l x : G} (hlA : l ∈ Subgroup.normalizer (F.A : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    l⁻¹ * x * l ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : l * y * l⁻¹ ∈ F.A := by
    have := (Subgroup.mem_normalizer_iff''.mp (inv_mem hlA) y).mp hy
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hxA _ hy'
  calc y * (l⁻¹ * x * l) = l⁻¹ * ((l * y * l⁻¹) * x) * l := by group
    _ = l⁻¹ * (x * (l * y * l⁻¹)) * l := by rw [hc]
    _ = l⁻¹ * x * l * y := by group

variable (hF : Sec226Z.Facts τ)
include hF

theorem shiftOf_conj (h : F.IsD D dD) {l : G} (hlN : l ∈ Subgroup.normalizer (D : Set G))
    (hl2 : l * l = 1) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ y : D, dD.e (Additive.ofMul (conjBy hlN y)) = φ (dD.e (Additive.ofMul y)))
    (hφφ : ∀ w, φ (φ w) = w) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    dD.shiftOf (mul_mem (mul_mem (inv_mem hlN) hxN) hlN) = act τ φ φ (dD.shiftOf hxN) := by
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl2
  have key : ∀ w, dD.thetaT (mul_mem (mul_mem (inv_mem hlN) hxN) hlN) w =
      w + φ (βlin τ (dD.shiftOf hxN) (φ w)) := by
    intro w
    have hw := dD.ofT_mem w
    have h1 : l⁻¹ * dD.ofT w * l ∈ D := (Subgroup.mem_normalizer_iff''.mp hlN _).mp hw
    have h1' : l * dD.ofT w * l⁻¹ ∈ D := by rw [hli]; rw [hli] at h1; exact h1
    have h2 : x⁻¹ * (l * dD.ofT w * l⁻¹) * x ∈ D :=
      (Subgroup.mem_normalizer_iff''.mp hxN _).mp h1'
    have c1 : crdT dD.e (l * dD.ofT w * l⁻¹) = φ w := by
      have := crdT_conj dD.e hlN hφ hw
      rw [dD.crdT_ofT] at this
      rw [← this, hli]
    rw [dD.thetaT_apply,
      show (l⁻¹ * x * l)⁻¹ * dD.ofT w * (l⁻¹ * x * l) =
        l⁻¹ * (x⁻¹ * (l * dD.ofT w * l⁻¹) * x) * l by group,
      crdT_conj dD.e hlN hφ h2, ← dD.thetaT_crdT hxN h1', c1, h.thetaT_eq hF hxN hxA, map_add,
      hφφ]
  refine Prod.ext ?_ ?_
  · show dD.thetaT _ (gen τ.k 1) - gen τ.k 1 = _
    rw [key]; simp [act]
  · show dD.thetaT _ (gen τ.k 2) - gen τ.k 2 = _
    rw [key]; simp [act]

theorem shiftOf_conj_uv (h : F.IsD D dD) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    dD.uv⁻¹ * x * dD.uv ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) ∧
      dD.shiftOf (mul_mem (mul_mem (inv_mem dD.uv_mem) hxN) dD.uv_mem) =
        actUv τ (dD.shiftOf hxN) :=
  ⟨conj_mem_centralizer_A (h.uv_eq ▸ F.dA.uv_mem) hxA,
    h.shiftOf_conj hF dD.uv_mem dD.uv_sq dD.uv_conj
      (fun w => DFunLike.congr_fun τ.action.rels.uv_sq w) hxN hxA⟩

theorem shiftOf_conj_t (h : F.IsD D dD) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    dD.t⁻¹ * x * dD.t ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) ∧
      dD.shiftOf (mul_mem (mul_mem (inv_mem dD.t_mem) hxN) dD.t_mem) =
        actT τ (dD.shiftOf hxN) :=
  ⟨conj_mem_centralizer_A (h.t_eq ▸ F.dA.t_mem) hxA,
    h.shiftOf_conj hF dD.t_mem dD.t_sq dD.t_conj
      (fun w => DFunLike.congr_fun τ.action.rels.t_sq w) hxN hxA⟩

theorem shiftOf_conj_u (h : F.IsD D dD) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    dD.u⁻¹ * x * dD.u ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) ∧
      dD.shiftOf (mul_mem (mul_mem (inv_mem dD.u_mem) hxN) dD.u_mem) =
        actU τ (dD.shiftOf hxN) :=
  ⟨conj_mem_centralizer_A (h.u_eq ▸ F.dA.u_mem) hxA,
    h.shiftOf_conj hF dD.u_mem dD.u_sq dD.u_conj
      (fun w => DFunLike.congr_fun τ.action.rels.u_sq w) hxN hxA⟩

theorem shiftOf_proj (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {x : G}
    (hxR : x ∈ hS.R) (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    hS.proj dD.ρ x ∈ hS.R ∧
      hS.proj dD.ρ x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) ∧
      dD.shiftOf (hS.R_le_normalizer (hS.proj_mem dD.ρ_mem hxR)) =
        actRho τ (dD.shiftOf (hS.R_le_normalizer hxR)) := by
  have hxN := hS.R_le_normalizer hxR
  have hpR := hS.proj_mem dD.ρ_mem hxR
  have hpN := hS.R_le_normalizer hpR
  have hρA : dD.ρ ∈ Subgroup.normalizer (F.A : Set G) := h.ρ_eq ▸ F.dA.ρ_mem
  have hconj : ∀ d ∈ D, (hS.proj dD.ρ x)⁻¹ * d * hS.proj dD.ρ x =
      dD.ρ⁻¹ * (x⁻¹ * (dD.ρ * d * dD.ρ⁻¹) * x) * dD.ρ := fun d hd => by
    rw [hS.proj_conj_D dD.ρ_mem hxR hd]; group
  refine ⟨hpR, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyD := h.A_le hy
    have hy' : dD.ρ * y * dD.ρ⁻¹ ∈ F.A := by
      have := (Subgroup.mem_normalizer_iff''.mp (inv_mem hρA) y).mp hy
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hxA _ hy'
    have e := hconj y hyD
    rw [mul_assoc x⁻¹, hc, inv_mul_cancel_left] at e
    calc y * hS.proj dD.ρ x = hS.proj dD.ρ x * ((hS.proj dD.ρ x)⁻¹ * y * hS.proj dD.ρ x) := by
          group
      _ = hS.proj dD.ρ x * y := by rw [e]; group
  · have key : ∀ w, dD.thetaT hpN w =
        w + τ.action.φρ (βlin τ (dD.shiftOf hxN) (τ.action.φρ (τ.action.φρ w))) := by
      intro w
      have hw := dD.ofT_mem w
      have h1 : dD.ρ * dD.ofT w * dD.ρ⁻¹ ∈ D := by
        have := (Subgroup.mem_normalizer_iff''.mp (inv_mem dD.ρ_mem) _).mp hw
        simpa using this
      have h2 : x⁻¹ * (dD.ρ * dD.ofT w * dD.ρ⁻¹) * x ∈ D :=
        (Subgroup.mem_normalizer_iff''.mp hxN _).mp h1
      have c1 : crdT dD.e (dD.ρ * dD.ofT w * dD.ρ⁻¹) = τ.action.φρ (τ.action.φρ w) := by
        have e1 := crdT_conj dD.e dD.ρ_mem dD.ρ_conj h1
        rw [show dD.ρ⁻¹ * (dD.ρ * dD.ofT w * dD.ρ⁻¹) * dD.ρ = dD.ofT w by group,
          dD.crdT_ofT] at e1
        calc crdT dD.e (dD.ρ * dD.ofT w * dD.ρ⁻¹)
            = τ.action.φρ (τ.action.φρ (τ.action.φρ
                (crdT dD.e (dD.ρ * dD.ofT w * dD.ρ⁻¹)))) :=
              (StrothWeakTypeData.φρ_cube _).symm
          _ = τ.action.φρ (τ.action.φρ w) := by rw [← e1]
      rw [dD.thetaT_apply, hconj _ hw, crdT_conj dD.e dD.ρ_mem dD.ρ_conj h2,
        ← dD.thetaT_crdT hxN h1, c1, h.thetaT_eq hF hxN hxA, map_add,
        StrothWeakTypeData.φρ_cube w]
    refine Prod.ext ?_ ?_
    · show dD.thetaT _ (gen τ.k 1) - gen τ.k 1 = _
      rw [key]; simp [actRho, act]
    · show dD.thetaT _ (gen τ.k 2) - gen τ.k 2 = _
      rw [key]; simp [actRho, act]

theorem mem_R1_of_shiftOf (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {x : G}
    (hxR : x ∈ hS.R) (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (huv : actUv τ (dD.shiftOf (hS.R_le_normalizer hxR)) = dD.shiftOf (hS.R_le_normalizer hxR))
    (ht : actT τ (dD.shiftOf (hS.R_le_normalizer hxR)) = dD.shiftOf (hS.R_le_normalizer hxR)) :
    x ∈ hS.R1 dD.uv dD.t := by
  have hxN := hS.R_le_normalizer hxR
  have hxS := hS.R_le_S hxR
  obtain ⟨huvA, huvs⟩ := h.shiftOf_conj_uv hF hxN hxA
  obtain ⟨htA, hts⟩ := h.shiftOf_conj_t hF hxN hxA
  have m1 := h.inv_mul_mem_of_shiftOf_eq hF hxS hxN hxA
    (mul_mem (mul_mem (inv_mem h.uv_mem_S) hxS) h.uv_mem_S)
    (mul_mem (mul_mem (inv_mem dD.uv_mem) hxN) dD.uv_mem) huvA (huvs.trans huv).symm
  have m2 := h.inv_mul_mem_of_shiftOf_eq hF hxS hxN hxA
    (mul_mem (mul_mem (inv_mem h.t_mem_S) hxS) h.t_mem_S)
    (mul_mem (mul_mem (inv_mem dD.t_mem) hxN) dD.t_mem) htA (hts.trans ht).symm
  have iuv : dD.uv⁻¹ = dD.uv := inv_eq_of_mul_eq_one_right dD.uv_sq
  have it : dD.t⁻¹ = dD.t := inv_eq_of_mul_eq_one_right dD.t_sq
  refine ⟨hxR, ?_, ?_⟩
  · convert m1 using 1
    rw [iuv]
    group
  · convert m2 using 1
    rw [it]
    group

omit hF in
theorem coc_proj (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {g : G}
    (hg : g ∈ hS.R1 dD.uv dD.t) :
    hS.proj dD.ρ g ∈ hS.R1 dD.uv dD.t ∧ dD.coc (hS.proj dD.ρ g) = tw τ (dD.coc g) := by
  obtain ⟨hgR, huv, ht⟩ := hg
  obtain ⟨puv, pt, p1, p2⟩ := h.cocycle_proj_rho hS hgR huv ht
  exact ⟨⟨hS.proj_mem dD.ρ_mem hgR, puv, pt⟩, Prod.ext p1 p2⟩

omit hF in
theorem coc_conj_u (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {g : G}
    (hg : g ∈ hS.R1 dD.uv dD.t) :
    dD.u⁻¹ * g * dD.u ∈ hS.R1 dD.uv dD.t ∧ dD.coc (dD.u⁻¹ * g * dD.u) = uw τ (dD.coc g) := by
  obtain ⟨hgR, huv, ht⟩ := hg
  obtain ⟨puv, pt, p1, p2⟩ := cocycle_conj_u hS huv ht
  exact ⟨⟨h.conj_u_mem_R hS hgR, puv, pt⟩, Prod.ext p1 p2⟩

theorem mem_of_isE (h : F.IsD D dD) {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgC : g ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (huv : g⁻¹ * dD.uv * g * dD.uv⁻¹ ∈ D) (ht : g⁻¹ * dD.t * g * dD.t⁻¹ ∈ D)
    (hE : IsE τ (dD.coc g)) : g ∈ D := by
  obtain ⟨c2, c0, -, cE⟩ := h.crd_x1
  have hx₁D : ((F.dA.a : F.A) : G) ^ 2 ∈ D := h.A_le (F.A.pow_mem F.dA.a.2 2)
  have hfix : τ.action.φuv (crdT dD.e (((F.dA.a : F.A) : G) ^ 2)) =
      crdT dD.e (((F.dA.a : F.A) : G) ^ 2) := by
    rw [← crdT_conj dD.e dD.uv_mem dD.uv_conj hx₁D, h.uv_eq, mul_assoc,
      ← F.E_comm F.uv_mem_E F.a_sq_mem_E, inv_mul_cancel_left]
  have key : ∀ y ∈ D, InE τ (crdT dD.e y) → y ∈ F.E := fun y hy hw =>
    cE y hy (hF.eFact _ c2 c0 hfix _ hw)
  obtain ⟨hE1, hE2⟩ := hE
  exact h.mem_of_conj_mem_E hgS hgC (key _ huv hE1) (key _ ht hE2)

theorem shiftOf_eq_zero_of_isE (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {g : G}
    (hg : g ∈ hS.R1 dD.uv dD.t) (hgA : g ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    {d : Torus τ.k} (hE : IsE τ (dD.coc g + cob τ d)) :
    dD.shiftOf (hS.R_le_normalizer hg.1) = 0 := by
  have hgR := hg.1
  have hd := dD.ofT_mem d
  have hc := dD.coc_mul_mem hg.2.1 hg.2.2 hd
  rw [dD.crdT_ofT] at hc
  have hgd : g * dD.ofT d ∈ D := by
    refine h.mem_of_isE hF (mul_mem (hS.R_le_S hgR) (h.le_S hd))
      (mul_mem (hS.R_le_centralizer_omega hgR) (hS.R_le_centralizer_omega (hS.D_le_R hd)))
      (crdT_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj hg.2.1 hd).1
      (crdT_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj hg.2.2 hd).1 ?_
    rw [hc]
    exact hE
  rw [← h.shiftOf_mul_mem hF (hS.R_le_normalizer hgR) hgA hd]
  exact dD.shiftOf_of_mem hgd _

theorem shiftOf_eq_of_coc (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e f : G}
    (he : e ∈ hS.R1 dD.uv dD.t) (heA : e ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hf : f ∈ hS.R1 dD.uv dD.t) (hfA : f ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    {d₁ d₂ : Torus τ.k} (hc : dD.coc e + cob τ d₁ = dD.coc f + cob τ d₂) :
    dD.shiftOf (hS.R_le_normalizer he.1) = dD.shiftOf (hS.R_le_normalizer hf.1) := by
  have hd₁ := dD.ofT_mem d₁
  have hd₂ := dD.ofT_mem d₂
  have he' : e * dD.ofT d₁ ∈ hS.R1 dD.uv dD.t := mul_mem he
    ⟨hS.D_le_R hd₁, (dD.crdT_cocycle_of_mem_uv hd₁).1, (dD.crdT_cocycle_of_mem_t hd₁).1⟩
  have hf' : f * dD.ofT d₂ ∈ hS.R1 dD.uv dD.t := mul_mem hf
    ⟨hS.D_le_R hd₂, (dD.crdT_cocycle_of_mem_uv hd₂).1, (dD.crdT_cocycle_of_mem_t hd₂).1⟩
  have ce := dD.coc_mul_mem he.2.1 he.2.2 hd₁
  have cf := dD.coc_mul_mem hf.2.1 hf.2.2 hd₂
  rw [dD.crdT_ofT] at ce cf
  have hcc : dD.coc (e * dD.ofT d₁) = dD.coc (f * dD.ofT d₂) := ce.trans (hc.trans cf.symm)
  have hmem := h.mul_inv_mem_of_cocycle_cob hS he' hf' 0
    (by rw [map_zero, sub_zero, add_zero]; exact congrArg Prod.fst hcc)
    (by rw [map_zero, sub_zero, add_zero]; exact congrArg Prod.snd hcc)
  have := h.shiftOf_eq_of_mul_inv_mem hF (hS.R_le_normalizer he'.1)
    (mul_mem heA (h.mem_centralizer_A_of_mem hd₁)) (hS.R_le_normalizer hf'.1)
    (mul_mem hfA (h.mem_centralizer_A_of_mem hd₂)) hmem
  rwa [h.shiftOf_mul_mem hF (hS.R_le_normalizer he.1) heA hd₁,
    h.shiftOf_mul_mem hF (hS.R_le_normalizer hf.1) hfA hd₂] at this

theorem exists_coc_eq_of_shiftOf_eq (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    {e f : G} (he : e ∈ hS.R1 dD.uv dD.t)
    (heA : e ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) (hfR : f ∈ hS.R)
    (hfA : f ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hs : dD.shiftOf (hS.R_le_normalizer he.1) = dD.shiftOf (hS.R_le_normalizer hfR)) :
    ∃ d : Torus τ.k, dD.coc f = dD.coc e + cob τ d := by
  have hd := h.inv_mul_mem_of_shiftOf_eq hF (hS.R_le_S he.1) (hS.R_le_normalizer he.1) heA
    (hS.R_le_S hfR) (hS.R_le_normalizer hfR) hfA hs
  refine ⟨crdT dD.e (e⁻¹ * f), ?_⟩
  rw [← dD.coc_mul_mem he.2.1 he.2.2 hd, mul_inv_cancel_left]

theorem false_of_W4 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {y : G}
    (hy1 : y ∈ hS.R1 dD.uv dD.t) (hyA : y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hy : dD.shiftOf (hS.R_le_normalizer hy1.1) = β₁ τ)
    (hW : W4Hyp τ (dD.coc y) → W4Concl τ (dD.coc y)) : False := by
  obtain ⟨o1, o2, o3, -, -, o6⟩ := hF.orbit₁
  obtain ⟨s1, -, s3, s4, s5, s6, -, -, -⟩ := hF.sum
  have hyN := hS.R_le_normalizer hy1.1
  obtain ⟨hy₂, cy₂⟩ := h.coc_proj hS hy1
  obtain ⟨-, hy₂A, sy₂⟩ := h.shiftOf_proj hF hS hy1.1 hyA
  obtain ⟨hy₃, cy₃⟩ := h.coc_proj hS hy₂
  obtain ⟨-, hy₃A, sy₃⟩ := h.shiftOf_proj hF hS hy₂.1 hy₂A
  obtain ⟨hy₄, cy₄⟩ := h.coc_proj hS hy₃
  obtain ⟨-, hy₄A, sy₄⟩ := h.shiftOf_proj hF hS hy₃.1 hy₃A
  rw [hy, o1] at sy₂
  rw [sy₂, o2] at sy₃
  rw [sy₃, o3] at sy₄
  obtain ⟨hyu, cyu⟩ := h.coc_conj_u hS hy1
  obtain ⟨hyuA, syu⟩ := h.shiftOf_conj_u hF hyN hyA
  rw [hy, o6] at syu
  have hyy : y * hS.proj dD.ρ y ∈ hS.R1 dD.uv dD.t := mul_mem hy1 hy₂
  have hyyA := mul_mem hyA hy₂A
  have syy : dD.shiftOf (hS.R_le_normalizer hyy.1) = β₃ τ := by
    rw [← s1, ← hy, ← sy₂]
    exact h.shiftOf_mul hF hyN hyA (hS.R_le_normalizer hy₂.1) hy₂A
  have cyy : dD.coc (y * hS.proj dD.ρ y) =
      dD.coc y + βapp τ (β₂ τ) (dD.coc y) + tw τ (dD.coc y) := by
    rw [h.coc_mul_of_mem_centralizer hF (hS.R_le_normalizer hy₂.1) hy₂A hy1.2.1 hy1.2.2 hy₂.2.1
      hy₂.2.2, sy₂, cy₂]
  have hyp : W4Hyp τ (dD.coc y) := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨du, hdu⟩ :=
        h.exists_coc_eq_of_shiftOf_eq hF hS hy1 hyA hyu.1 hyuA (hy.trans syu.symm)
      exact ⟨du, cyu.symm.trans hdu⟩
    · obtain ⟨d, hd⟩ :=
        h.exists_coc_eq_of_shiftOf_eq hF hS hyy hyyA hy₃.1 hy₃A (syy.trans sy₃.symm)
      refine ⟨d, ?_⟩
      rw [← cy₂, ← cy₃, hd, cyy, cy₂]
    · obtain ⟨d, hd⟩ :=
        h.exists_coc_eq_of_shiftOf_eq hF hS hy1 hyA hy₄.1 hy₄A (hy.trans sy₄.symm)
      refine ⟨d, ?_⟩
      rw [← cy₂, ← cy₃, ← cy₄, hd]
  rcases hW hyp with ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨d, hd⟩
  · exact s4 (hy.symm.trans (h.shiftOf_eq_zero_of_isE hF hS hy1 hyA hd))
  · rw [← cy₂] at hd
    exact s5 (sy₂.symm.trans (h.shiftOf_eq_zero_of_isE hF hS hy₂ hy₂A hd))
  · rw [← cy₂, ← cy₃] at hd
    exact s6 (sy₃.symm.trans (h.shiftOf_eq_zero_of_isE hF hS hy₃ hy₃A hd))
  · rw [← cy₂] at hd
    exact s3 (hy.symm.trans ((h.shiftOf_eq_of_coc hF hS hy₂ hy₂A hy1 hyA hd).symm.trans sy₂))

theorem false_of_shiftOf_eq_β₁ (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    {x : G} (hxR : x ∈ hS.R) (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hx : dD.shiftOf (hS.R_le_normalizer hxR) = β₁ τ) : False := by
  obtain ⟨-, -, -, o4, o5, -⟩ := hF.orbit₁
  have hx1 := h.mem_R1_of_shiftOf hF hS hxR hxA (by rw [hx, o4]) (by rw [hx, o5])
  obtain ⟨d, hd⟩ := hF.w4 (dD.coc x) (dD.isCoc_coc hx1.2.1 hx1.2.2)
  have hdD := dD.ofT_mem d
  have hy1 : x * dD.ofT d ∈ hS.R1 dD.uv dD.t := mul_mem hx1
    ⟨hS.D_le_R hdD, (dD.crdT_cocycle_of_mem_uv hdD).1, (dD.crdT_cocycle_of_mem_t hdD).1⟩
  have hcy := dD.coc_mul_mem hx1.2.1 hx1.2.2 hdD
  rw [dD.crdT_ofT] at hcy
  exact h.false_of_W4 hF hS hy1 (mul_mem hxA (h.mem_centralizer_A_of_mem hdD))
    ((h.shiftOf_mul_mem hF (hS.R_le_normalizer hxR) hxA hdD).trans hx)
    (by rw [hcy]; exact hd)

theorem false_of_U2 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {y : G}
    (hy1 : y ∈ hS.R1 dD.uv dD.t) (hyA : y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hy : dD.shiftOf (hS.R_le_normalizer hy1.1) = β₅ τ) (hp : hS.proj dD.ρ y = y) : False := by
  obtain ⟨-, -, -, p4, -⟩ := hF.orbit₅
  obtain ⟨-, s2, -, -, -, -, s7, s8, s9⟩ := hF.sum
  have hyN := hS.R_le_normalizer hy1.1
  have hyS := hS.R_le_S hy1.1
  have hsq : y * y ∈ D := by
    obtain ⟨i1, i2⟩ := h.isShift_shiftOf hF hyN hyA
    refine h.mem_of_shiftOf_eq_zero hF (mul_mem hyS hyS) (mul_mem hyN hyN) (mul_mem hyA hyA) ?_
    rw [h.shiftOf_mul hF hyN hyA hyN hyA]
    exact Prod.ext i1 i2
  obtain ⟨q1, q2, q3⟩ := sq_normalized hS hy1 hp hsq
  have hq0 : βlin τ (β₅ τ) (crdT dD.e (y * y)) = 0 := by
    have e1 := h.thetaT_eq hF hyN hyA (crdT dD.e (y * y))
    rw [dD.thetaT_crdT hyN hsq, show y⁻¹ * (y * y) * y = y * y by group, hy] at e1
    have e2 : crdT dD.e (y * y) + βlin τ (β₅ τ) (crdT dD.e (y * y)) = crdT dD.e (y * y) + 0 := by
      rw [add_zero]; exact e1.symm
    exact add_left_cancel e2
  obtain ⟨-, hm⟩ := h.coc_proj hS hy1
  rw [hp] at hm
  rw [h.thetaT_eq hF hyN hyA, hy, sub_eq_iff_eq_add] at q2 q3
  have hyp : U2Hyp τ (dD.coc y) := by
    refine ⟨dD.isCoc_coc hy1.2.1 hy1.2.2, hm.symm, crdT dD.e (y * y), q1, hq0, ?_, ?_⟩
    · show τ.action.φuv (crdT dD.e (y * y)) = crdT dD.e (y * y) +
        2 • crdT dD.e (y⁻¹ * dD.uv * y * dD.uv⁻¹) +
        βlin τ (β₅ τ) (crdT dD.e (y⁻¹ * dD.uv * y * dD.uv⁻¹))
      rw [q2, two_nsmul]
      abel
    · show τ.action.φt (crdT dD.e (y * y)) = crdT dD.e (y * y) +
        2 • crdT dD.e (y⁻¹ * dD.t * y * dD.t⁻¹) +
        βlin τ (β₅ τ) (crdT dD.e (y⁻¹ * dD.t * y * dD.t⁻¹))
      rw [q3, two_nsmul]
      abel
  obtain ⟨hyu, cyu⟩ := h.coc_conj_u hS hy1
  obtain ⟨hyuA, syu⟩ := h.shiftOf_conj_u hF hyN hyA
  rw [hy, p4] at syu
  have hr : y * (dD.u⁻¹ * y * dD.u) ∈ hS.R1 dD.uv dD.t := mul_mem hy1 hyu
  have hrA := mul_mem hyA hyuA
  have sr : dD.shiftOf (hS.R_le_normalizer hr.1) = w₂ τ := by
    rw [← s2, ← hy, ← syu]
    exact h.shiftOf_mul hF hyN hyA (hS.R_le_normalizer hyu.1) hyuA
  have cr : dD.coc (y * (dD.u⁻¹ * y * dD.u)) =
      dD.coc y + βapp τ (β₆ τ) (dD.coc y) + uw τ (dD.coc y) := by
    rw [h.coc_mul_of_mem_centralizer hF (hS.R_le_normalizer hyu.1) hyuA hy1.2.1 hy1.2.2 hyu.2.1
      hyu.2.2, syu, cyu]
  rcases hF.u2 _ hyp with ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨d, hd⟩
  · exact s7 (hy.symm.trans (h.shiftOf_eq_zero_of_isE hF hS hy1 hyA hd))
  · rw [← cyu] at hd
    exact s8 (syu.symm.trans (h.shiftOf_eq_zero_of_isE hF hS hyu hyuA hd))
  · rw [← cr] at hd
    exact s9 (sr.symm.trans (h.shiftOf_eq_zero_of_isE hF hS hr hrA hd))

theorem false_of_shiftOf_eq_β₅ (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    {x : G} (hxR : x ∈ hS.R) (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G))
    (hx : dD.shiftOf (hS.R_le_normalizer hxR) = β₅ τ) : False := by
  obtain ⟨p1, p2, p3, -, -⟩ := hF.orbit₅
  have hxN := hS.R_le_normalizer hxR
  have hx1 := h.mem_R1_of_shiftOf hF hS hxR hxA (by rw [hx, p1]) (by rw [hx, p2])
  obtain ⟨hpR, hpA, hps⟩ := h.shiftOf_proj hF hS hxR hxA
  rw [hx, p3] at hps
  have hfix : x⁻¹ * hS.proj dD.ρ x ∈ D :=
    h.inv_mul_mem_of_shiftOf_eq hF (hS.R_le_S hxR) hxN hxA (hS.R_le_S hpR)
      (hS.R_le_normalizer hpR) hpA (hx.trans hps.symm)
  obtain ⟨d₁, hd₁, hp⟩ := hS.exists_proj_fixed dD.ρ_mem dD.rho_odd hxR hfix
  have hx'1 : x * d₁ ∈ hS.R1 dD.uv dD.t := mul_mem hx1
    ⟨hS.D_le_R hd₁, (dD.crdT_cocycle_of_mem_uv hd₁).1, (dD.crdT_cocycle_of_mem_t hd₁).1⟩
  exact h.false_of_U2 hF hS hx'1 (mul_mem hxA (h.mem_centralizer_A_of_mem hd₁))
    ((h.shiftOf_mul_mem hF hxN hxA hd₁).trans hx) hp

theorem shiftOf_eq_zero_or_w₂ (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {x : G}
    (hxR : x ∈ hS.R) (hxA : x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    dD.shiftOf (hS.R_le_normalizer hxR) = 0 ∨ dD.shiftOf (hS.R_le_normalizer hxR) = w₂ τ := by
  obtain ⟨-, o2, o3, -, -, -⟩ := hF.orbit₁
  obtain ⟨-, -, -, -, p5⟩ := hF.orbit₅
  by_contra hne
  rw [not_or] at hne
  have hxN := hS.R_le_normalizer hxR
  obtain ⟨y, hyR, hyA, h16, hy0, hyw⟩ : ∃ y, ∃ hyR : y ∈ hS.R,
      y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) ∧
      IsShift16 τ (dD.shiftOf (hS.R_le_normalizer hyR)) ∧
      dD.shiftOf (hS.R_le_normalizer hyR) ≠ 0 ∧ dD.shiftOf (hS.R_le_normalizer hyR) ≠ w₂ τ := by
    by_cases h16 : IsShift16 τ (dD.shiftOf hxN)
    · exact ⟨x, hxR, hxA, h16, hne.1, hne.2⟩
    have hs := h.isShift_shiftOf hF hxN hxA
    have huvR : dD.uv⁻¹ * x * dD.uv ∈ hS.R := (Subgroup.mem_normalizer_iff''.mp
      (mem_normalizer_inf_centralizer_omegaIn h.uv_mem_S dD.uv_mem dD.uv_sq) x).mp hxR
    have htR : dD.t⁻¹ * x * dD.t ∈ hS.R := (Subgroup.mem_normalizer_iff''.mp
      (mem_normalizer_inf_centralizer_omegaIn h.t_mem_S dD.t_mem dD.t_sq) x).mp hxR
    obtain ⟨huvA, huvs⟩ := h.shiftOf_conj_uv hF hxN hxA
    obtain ⟨htA, hts⟩ := h.shiftOf_conj_t hF hxN hxA
    by_cases huv : actUv τ (dD.shiftOf hxN) + dD.shiftOf hxN = 0 ∨
        actUv τ (dD.shiftOf hxN) + dD.shiftOf hxN = w₂ τ
    · have ht : ¬ (actT τ (dD.shiftOf hxN) + dD.shiftOf hxN = 0 ∨
          actT τ (dD.shiftOf hxN) + dD.shiftOf hxN = w₂ τ) := fun ht =>
        h16 (hF.fix _ hs huv ht)
      rw [not_or] at ht
      have e : dD.shiftOf (hS.R_le_normalizer (mul_mem htR hxR)) =
          actT τ (dD.shiftOf hxN) + dD.shiftOf hxN := by
        rw [← hts]
        exact h.shiftOf_mul hF (mul_mem (mul_mem (inv_mem dD.t_mem) hxN) dD.t_mem) htA hxN hxA
      refine ⟨_, mul_mem htR hxR, mul_mem htA hxA, ?_, ?_, ?_⟩ <;> rw [e]
      · exact (hF.comm _ hs).2
      · exact ht.1
      · exact ht.2
    · rw [not_or] at huv
      have e : dD.shiftOf (hS.R_le_normalizer (mul_mem huvR hxR)) =
          actUv τ (dD.shiftOf hxN) + dD.shiftOf hxN := by
        rw [← huvs]
        exact h.shiftOf_mul hF (mul_mem (mul_mem (inv_mem dD.uv_mem) hxN) dD.uv_mem) huvA hxN hxA
      refine ⟨_, mul_mem huvR hxR, mul_mem huvA hxA, ?_, ?_, ?_⟩ <;> rw [e]
      · exact (hF.comm _ hs).1
      · exact huv.1
      · exact huv.2
  have hyN := hS.R_le_normalizer hyR
  obtain ⟨hp₁R, hp₁A, hps₁⟩ := h.shiftOf_proj hF hS hyR hyA
  obtain ⟨hp₂R, hp₂A, hps₂⟩ := h.shiftOf_proj hF hS hp₁R hp₁A
  have hzR := mul_mem hp₁R hp₂R
  have hzA := mul_mem hp₁A hp₂A
  have hzs : dD.shiftOf (hS.R_le_normalizer hzR) =
      actRho τ (dD.shiftOf hyN) + actRho τ (actRho τ (dD.shiftOf hyN)) := by
    rw [h.shiftOf_mul hF (hS.R_le_normalizer hp₁R) hp₁A (hS.R_le_normalizer hp₂R) hp₂A, hps₂,
      hps₁]
  rcases hF.socle _ h16 hy0 hyw with (h1 | h2 | h3) | ⟨-, h5 | h6⟩
  · exact h.false_of_shiftOf_eq_β₁ hF hS hzR hzA (hzs.trans h1)
  · obtain ⟨hq₁R, hq₁A, hqs₁⟩ := h.shiftOf_proj hF hS hzR hzA
    obtain ⟨hq₂R, hq₂A, hqs₂⟩ := h.shiftOf_proj hF hS hq₁R hq₁A
    exact h.false_of_shiftOf_eq_β₁ hF hS hq₂R hq₂A (by rw [hqs₂, hqs₁, hzs, h2, o2, o3])
  · obtain ⟨hq₁R, hq₁A, hqs₁⟩ := h.shiftOf_proj hF hS hzR hzA
    exact h.false_of_shiftOf_eq_β₁ hF hS hq₁R hq₁A (by rw [hqs₁, hzs, h3, o3])
  · exact h.false_of_shiftOf_eq_β₅ hF hS hyR hyA h5
  · obtain ⟨huA, hus⟩ := h.shiftOf_conj_u hF hyN hyA
    exact h.false_of_shiftOf_eq_β₅ hF hS (h.conj_u_mem_R hS hyR) huA (by rw [hus, h6, p5])

omit hF in
theorem conj_eq_of_mem_centralizer_A_of_t2m1 (h : F.IsD D dD) (hτ : τ = .t200 1 ∨ τ = .t201 1)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    {x : G} (hx : x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    (∀ d ∈ D, x⁻¹ * d * x = d) ∨
      (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
        x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5) := by
  have hF : Facts τ := by
    rcases hτ with rfl | rfl
    · exact facts_t200
    · exact facts_t201
  have hS := h.setting hns
  obtain ⟨hxSN, hxA⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.mp hxSN
  have hxR : x ∈ hS.R := Subgroup.mem_inf.mpr ⟨hxSN, h.centralizer_A_le hxA⟩
  have hconj : ∀ g : G, g ∈ D → x⁻¹ * g * x ∈ D := fun g hg =>
    (Subgroup.mem_normalizer_iff''.mp hxN g).mp hg
  rcases h.shiftOf_eq_zero_or_w₂ hF hS hxR hxA with h0 | hw
  · left
    have hxD := h.mem_of_shiftOf_eq_zero hF hxS hxN hxA h0
    intro d hd
    have hc : x * d = d * x :=
      congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hxD⟩ ⟨d, hd⟩)
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  · right
    have hpow : ∀ j : Fin 3, crdT dD.e (dD.ofT (gen τ.k j) ^ 5) = 5 • gen τ.k j := fun j => by
      have e := dD.ofT_zsmul ((5 : ℕ) : ℤ) (gen τ.k j)
      rw [natCast_zsmul, zpow_natCast] at e
      rw [← e, dD.crdT_ofT]
    have hθ : ∀ j : Fin 3, crdT dD.e (x⁻¹ * dD.ofT (gen τ.k j) * x) =
        gen τ.k j + (dD.thetaT hxN (gen τ.k j) - gen τ.k j) := fun j => by
      rw [← dD.thetaT_crdT hxN (dD.ofT_mem _), dD.crdT_ofT]
      abel
    refine ⟨crdT_inj dD.e (hconj _ dD.c.2) dD.c.2 ?_,
      crdT_inj dD.e (hconj _ dD.a.2) (pow_mem dD.a.2 5) ?_,
      crdT_inj dD.e (hconj _ dD.b.2) (pow_mem dD.b.2 5) ?_⟩
    · rw [← dD.thetaT_crdT hxN dD.c.2, dD.c_eq_ofT, dD.crdT_ofT]
      exact h.thetaT_c hF hxN hxA
    · have e := hθ 1
      rw [show dD.thetaT hxN (gen τ.k 1) - gen τ.k 1 = (dD.shiftOf hxN).1 from rfl, hw,
        hF.a5, ← hpow] at e
      exact e
    · have e := hθ 2
      rw [show dD.thetaT hxN (gen τ.k 2) - gen τ.k 2 = (dD.shiftOf hxN).2 from rfl, hw,
        hF.b5, ← hpow] at e
      exact e

end StrothFrame.IsD

end CFSG.CGT.Stroth77
