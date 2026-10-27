module

public import CFSG.LieType.Chevalley.E6EvenInvolutionCommutant
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.E6GraphLeviRealization

public noncomputable section

namespace CFSG.LieType.Chevalley.E6EvenInvolution

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.LieType.Chevalley.E6GraphHighestRoot

variable {k : Type} [Field k]

@[expose] def frame₁ : List (Fin TwistTag.E6.tag.rank → ℤ) := [Pi.single (e6Idx 0) 1]

@[expose] def frame₂ : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [Pi.single (e6Idx 0) 1, Pi.single (e6Idx 5) 1]

@[expose] def frame₃ : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [Pi.single (e6Idx 0) 1, Pi.single (e6Idx 3) 1, Pi.single (e6Idx 5) 1]

variable (k) in
@[expose] def jRep
    (F : List (Fin TwistTag.E6.tag.rank → ℤ)) :
    ModGL TwistTag.E6.tag k :=
  (F.map fun σ => pinnedX TwistTag.E6.tag k σ 1).prod

abbrev trv {a b : Fin 6} (h : a ≠ b) : SpecialLinearGroup (Fin 6) k :=
  SpecialLinearGroup.transvection h 1

@[expose] def sl1 : SpecialLinearGroup (Fin 6) k := trv (a := 0) (b := 1) (by decide)

@[expose] def sl2 : SpecialLinearGroup (Fin 6) k :=
  trv (a := 0) (b := 1) (by decide) * trv (a := 4) (b := 5) (by decide)

@[expose] def sl3 : SpecialLinearGroup (Fin 6) k :=
  trv (a := 0) (b := 1) (by decide) * trv (a := 2) (b := 3) (by decide) *
    trv (a := 4) (b := 5) (by decide)

theorem coe_trv {a b : Fin 6} (h : a ≠ b) :
    ((trv h : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) = 1 + E k a b :=
  SpecialLinearGroup.transvection_coe h 1

theorem coe_trv_mul_trv {x y z w : Fin 6} (hxy : x ≠ y) (hzw : z ≠ w) (hyz : y ≠ z) :
    ((trv hxy * trv hzw : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) =
      1 + (E k x y + E k z w) := by
  change ((trv hxy : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) *
    ((trv hzw : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) = _
  rw [coe_trv, coe_trv, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, E_mul_E]
  simp only [hyz, ↓reduceIte, add_zero]
  abel

theorem coe_sl1 : ((sl1 : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) =
    1 + nMat1 k :=
  coe_trv (a := 0) (b := 1) (by decide)

theorem coe_sl2 : ((sl2 : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) =
    1 + nMat2 k :=
  coe_trv_mul_trv (x := 0) (y := 1) (z := 4) (w := 5) (by decide) (by decide) (by decide)

theorem coe_sl3 : ((sl3 : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) =
    1 + nMat3 k := by
  change ((trv (a := 0) (b := 1) (by decide) * trv (a := 2) (b := 3) (by decide) :
    SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) *
      ((trv (a := 4) (b := 5) (by decide) : SpecialLinearGroup (Fin 6) k) :
        Matrix (Fin 6) (Fin 6) k) = _
  rw [coe_trv_mul_trv (x := 0) (y := 1) (z := 2) (w := 3) (by decide) (by decide) (by decide),
    coe_trv, nMat3, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.add_mul, E_mul_E, E_mul_E]
  simp only [show (1 : Fin 6) ≠ 4 by decide, show (3 : Fin 6) ≠ 4 by decide, ↓reduceIte,
    add_zero]
  abel

theorem nMat1_sq : nMat1 k * nMat1 k = 0 := by
  rw [nMat1, E_mul_E]
  simp

theorem nMat2_sq : nMat2 k * nMat2 k = 0 := by
  simp only [nMat2, Matrix.add_mul, Matrix.mul_add, E_mul_E]
  simp

theorem nMat3_sq : nMat3 k * nMat3 k = 0 := by
  simp only [nMat3, Matrix.add_mul, Matrix.mul_add, E_mul_E]
  simp

theorem eq_zero_or_eq_one_of_card (hk : Nat.card k = 2) (c : k) : c = 0 ∨ c = 1 := by
  classical
  by_contra hc
  rw [not_or] at hc
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have : Fintype k := Fintype.ofFinite k
  have h0c : (0 : k) ≠ c := fun h => hc.1 h.symm
  have h3 : ({0, 1, c} : Finset k).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h0c]), Finset.card_pair (Ne.symm hc.2)]
  have h4 := Finset.card_le_univ ({0, 1, c} : Finset k)
  rw [h3, ← Nat.card_eq_fintype_card, hk] at h4
  omega

theorem comm_of_comm_one_add {B s : SpecialLinearGroup (Fin 6) k}
    {M : Matrix (Fin 6) (Fin 6) k} (hs : (s : Matrix (Fin 6) (Fin 6) k) = 1 + M)
    (h : B * s = s * B) : (B : Matrix (Fin 6) (Fin 6) k) * M = M * B := by
  have e : (B : Matrix (Fin 6) (Fin 6) k) * s = s * B :=
    congrArg (fun g : SpecialLinearGroup (Fin 6) k => (g : Matrix (Fin 6) (Fin 6) k)) h
  rw [hs, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at e
  exact add_left_cancel e

theorem comm_of_coe {s J : SpecialLinearGroup (Fin 6) k} {M N : Matrix (Fin 6) (Fin 6) k}
    (hs : (s : Matrix (Fin 6) (Fin 6) k) = 1 + M) (hJ : (J : Matrix (Fin 6) (Fin 6) k) = 1 + N)
    (h : M * N = N * M) : s * J = J * s := by
  refine Subtype.ext ?_
  change (s : Matrix (Fin 6) (Fin 6) k) * J = (J : Matrix (Fin 6) (Fin 6) k) * s
  rw [hs, hJ, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, h]
  simp only [Matrix.one_mul, Matrix.mul_one]
  abel

@[expose] def gens1 : List (SpecialLinearGroup (Fin 6) k) :=
  [trv (a := 0) (b := 1) (by decide),
    trv (a := 2) (b := 3) (by decide),
    trv (a := 3) (b := 2) (by decide),
    trv (a := 4) (b := 5) (by decide),
    trv (a := 0) (b := 4) (by decide),
    trv (a := 5) (b := 2) (by decide)]

theorem gens1_comm : ∀ s ∈ gens1 (k := k), s * sl1 = sl1 * s := by
  simp only [gens1, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact comm_of_coe (coe_trv (a := 0) (b := 1) (by decide)) coe_sl1 (by simp [nMat1])
  · exact comm_of_coe (coe_trv (a := 2) (b := 3) (by decide)) coe_sl1 (by simp [nMat1])
  · exact comm_of_coe (coe_trv (a := 3) (b := 2) (by decide)) coe_sl1 (by simp [nMat1])
  · exact comm_of_coe (coe_trv (a := 4) (b := 5) (by decide)) coe_sl1 (by simp [nMat1])
  · exact comm_of_coe (coe_trv (a := 0) (b := 4) (by decide)) coe_sl1 (by simp [nMat1])
  · exact comm_of_coe (coe_trv (a := 5) (b := 2) (by decide)) coe_sl1 (by simp [nMat1])

theorem gens1_commutant (B : SpecialLinearGroup (Fin 6) k)
    (hB : ∀ s ∈ gens1 (k := k), B * s = s * B) :
    (B : Matrix (Fin 6) (Fin 6) k) = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) k) + B 0 1 • nMat1 k :=
  commutant1
    (comm_of_comm_one_add (coe_trv (a := 0) (b := 1) (by decide)) (hB _ (by simp [gens1])))
    (comm_of_comm_one_add (coe_trv (a := 2) (b := 3) (by decide)) (hB _ (by simp [gens1])))
    (comm_of_comm_one_add (coe_trv (a := 3) (b := 2) (by decide)) (hB _ (by simp [gens1])))
    (comm_of_comm_one_add (coe_trv (a := 4) (b := 5) (by decide)) (hB _ (by simp [gens1])))
    (comm_of_comm_one_add (coe_trv (a := 0) (b := 4) (by decide)) (hB _ (by simp [gens1])))
    (comm_of_comm_one_add (coe_trv (a := 5) (b := 2) (by decide)) (hB _ (by simp [gens1])))

@[expose] def gens2 : List (SpecialLinearGroup (Fin 6) k) :=
  [(trv (a := 0) (b := 4) (by decide) * trv (a := 1) (b := 5) (by decide)),
    (trv (a := 4) (b := 0) (by decide) * trv (a := 5) (b := 1) (by decide)),
    trv (a := 0) (b := 2) (by decide),
    trv (a := 0) (b := 3) (by decide),
    trv (a := 0) (b := 1) (by decide)]

theorem gens2_comm : ∀ s ∈ gens2 (k := k), s * sl2 = sl2 * s := by
  simp only [gens2, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl)
  · exact comm_of_coe (coe_trv_mul_trv (x := 0) (y := 4) (z := 1) (w := 5) (by decide) (by decide)
      (by decide)) coe_sl2 (by simp [nMat2, Matrix.mul_add, Matrix.add_mul])
  · exact comm_of_coe (coe_trv_mul_trv (x := 4) (y := 0) (z := 5) (w := 1) (by decide) (by decide)
      (by decide)) coe_sl2 (by simp [nMat2, Matrix.mul_add, Matrix.add_mul])
  · exact comm_of_coe (coe_trv (a := 0) (b := 2) (by decide)) coe_sl2 (by simp [nMat2,
      Matrix.mul_add, Matrix.add_mul])
  · exact comm_of_coe (coe_trv (a := 0) (b := 3) (by decide)) coe_sl2 (by simp [nMat2,
      Matrix.mul_add, Matrix.add_mul])
  · exact comm_of_coe (coe_trv (a := 0) (b := 1) (by decide)) coe_sl2 (by simp [nMat2,
      Matrix.mul_add, Matrix.add_mul])

theorem gens2_commutant (B : SpecialLinearGroup (Fin 6) k)
    (hB : ∀ s ∈ gens2 (k := k), B * s = s * B) :
    (B : Matrix (Fin 6) (Fin 6) k) = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) k) + B 0 1 • nMat2 k :=
  commutant2
    (comm_of_comm_one_add (coe_trv_mul_trv (x := 0) (y := 4) (z := 1) (w := 5) (by decide) (by
      decide) (by decide)) (hB _ (by simp [gens2])))
    (comm_of_comm_one_add (coe_trv_mul_trv (x := 4) (y := 0) (z := 5) (w := 1) (by decide) (by
      decide) (by decide)) (hB _ (by simp [gens2])))
    (comm_of_comm_one_add (coe_trv (a := 0) (b := 2) (by decide)) (hB _ (by simp [gens2])))
    (comm_of_comm_one_add (coe_trv (a := 0) (b := 3) (by decide)) (hB _ (by simp [gens2])))
    (comm_of_comm_one_add (coe_trv (a := 0) (b := 1) (by decide)) (hB _ (by simp [gens2])))

@[expose] def gens3 : List (SpecialLinearGroup (Fin 6) k) :=
  [(trv (a := 0) (b := 2) (by decide) * trv (a := 1) (b := 3) (by decide)),
    (trv (a := 2) (b := 0) (by decide) * trv (a := 3) (b := 1) (by decide)),
    (trv (a := 0) (b := 4) (by decide) * trv (a := 1) (b := 5) (by decide)),
    trv (a := 0) (b := 1) (by decide)]

theorem gens3_comm : ∀ s ∈ gens3 (k := k), s * sl3 = sl3 * s := by
  simp only [gens3, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl)
  · exact comm_of_coe (coe_trv_mul_trv (x := 0) (y := 2) (z := 1) (w := 3) (by decide) (by decide)
      (by decide)) coe_sl3 (by simp [nMat3, Matrix.mul_add, Matrix.add_mul])
  · exact comm_of_coe (coe_trv_mul_trv (x := 2) (y := 0) (z := 3) (w := 1) (by decide) (by decide)
      (by decide)) coe_sl3 (by simp [nMat3, Matrix.mul_add, Matrix.add_mul])
  · exact comm_of_coe (coe_trv_mul_trv (x := 0) (y := 4) (z := 1) (w := 5) (by decide) (by decide)
      (by decide)) coe_sl3 (by simp [nMat3, Matrix.mul_add, Matrix.add_mul])
  · exact comm_of_coe (coe_trv (a := 0) (b := 1) (by decide)) coe_sl3 (by simp [nMat3,
      Matrix.mul_add, Matrix.add_mul])

theorem gens3_commutant (B : SpecialLinearGroup (Fin 6) k)
    (hB : ∀ s ∈ gens3 (k := k), B * s = s * B) :
    (B : Matrix (Fin 6) (Fin 6) k) = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) k) + B 0 1 • nMat3 k :=
  commutant3
    (comm_of_comm_one_add (coe_trv_mul_trv (x := 0) (y := 2) (z := 1) (w := 3) (by decide) (by
      decide) (by decide)) (hB _ (by simp [gens3])))
    (comm_of_comm_one_add (coe_trv_mul_trv (x := 2) (y := 0) (z := 3) (w := 1) (by decide) (by
      decide) (by decide)) (hB _ (by simp [gens3])))
    (comm_of_comm_one_add (coe_trv_mul_trv (x := 0) (y := 4) (z := 1) (w := 5) (by decide) (by
      decide) (by decide)) (hB _ (by simp [gens3])))
    (comm_of_comm_one_add (coe_trv (a := 0) (b := 1) (by decide)) (hB _ (by simp [gens3])))

variable (h2 : (2 : k) = 0)
include h2

theorem realize_trv (t : Fin 5) :
    realize h2 (trv (castSucc_ne_succ t)) =
      pinnedX TwistTag.E6.tag k (Pi.single (pathIdx t) 1) 1 := by
  rw [realize_x h2, pinnedX_single]

theorem realize_sl1
    : realize h2 sl1 = jRep k frame₁ := by
  rw [jRep, frame₁, List.map_singleton, List.prod_singleton, sl1]
  exact realize_trv h2 0

theorem realize_sl2
    : realize h2 sl2 = jRep k frame₂ := by
  rw [jRep, frame₂, List.map_cons, List.map_singleton, List.prod_cons, List.prod_singleton, sl2,
    map_mul]
  exact congrArg₂ (· * ·) (realize_trv h2 0) (realize_trv h2 4)

theorem realize_sl3
    : realize h2 sl3 = jRep k frame₃ := by
  rw [jRep, frame₃, List.map_cons, List.map_cons, List.map_singleton, List.prod_cons,
    List.prod_cons, List.prod_singleton, sl3, map_mul, map_mul, mul_assoc]
  exact congrArg₂ (· * ·) (realize_trv h2 0) (congrArg₂ (· * ·) (realize_trv h2 2)
    (realize_trv h2 4))

theorem realize_mem
    (B : SpecialLinearGroup (Fin 6) k) :
    realize h2 B ∈ subsystemGroup TwistTag.E6.tag k setA := by
  rw [← range_realize h2]
  exact ⟨B, rfl⟩

omit h2 in
theorem sq_eq_one_of_coe (h2 : (2 : k) = 0) {J : SpecialLinearGroup (Fin 6) k}
    {N : Matrix (Fin 6) (Fin 6) k} (hJ : (J : Matrix (Fin 6) (Fin 6) k) = 1 + N)
    (hN : N * N = 0) : J * J = 1 := by
  refine Subtype.ext ?_
  change (J : Matrix (Fin 6) (Fin 6) k) * (J : Matrix (Fin 6) (Fin 6) k) = 1
  rw [hJ, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hN, add_zero, add_assoc, ← two_smul k N, h2, zero_smul, add_zero]

omit h2 in
theorem realize_ne_one
    (h2 : (2 : k) = 0) {J : SpecialLinearGroup (Fin 6) k}
    {N : Matrix (Fin 6) (Fin 6) k} (hJ : (J : Matrix (Fin 6) (Fin 6) k) = 1 + N)
    (hN : N 0 1 = 1) : realize h2 J ≠ 1 := by
  intro h
  obtain ⟨l, -, hl⟩ := (mem_ker_realize h2 J).1 h
  have e := congrFun (congrFun hl 0) 1
  rw [hJ, Matrix.add_apply, hN, Matrix.one_apply_ne (by decide), zero_add] at e
  simp [Matrix.scalar_apply] at e

theorem jRep₁_facts
    : jRep k frame₁ ∈ subsystemGroup TwistTag.E6.tag k setA ∧
    jRep k frame₁ * jRep k frame₁ = 1 ∧ jRep k frame₁ ≠ 1 := by
  rw [← realize_sl1 h2, ← map_mul, sq_eq_one_of_coe h2 coe_sl1 nMat1_sq, map_one]
  exact ⟨realize_mem h2 _, rfl, realize_ne_one h2 coe_sl1 (by simp [nMat1])⟩

theorem jRep₂_facts
    : jRep k frame₂ ∈ subsystemGroup TwistTag.E6.tag k setA ∧
    jRep k frame₂ * jRep k frame₂ = 1 ∧ jRep k frame₂ ≠ 1 := by
  rw [← realize_sl2 h2, ← map_mul, sq_eq_one_of_coe h2 coe_sl2 nMat2_sq, map_one]
  exact ⟨realize_mem h2 _, rfl, realize_ne_one h2 coe_sl2 (by simp [nMat2])⟩

theorem jRep₃_facts
    : jRep k frame₃ ∈ subsystemGroup TwistTag.E6.tag k setA ∧
    jRep k frame₃ * jRep k frame₃ = 1 ∧ jRep k frame₃ ≠ 1 := by
  rw [← realize_sl3 h2, ← map_mul, sq_eq_one_of_coe h2 coe_sl3 nMat3_sq, map_one]
  exact ⟨realize_mem h2 _, rfl, realize_ne_one h2 coe_sl3 (by simp [nMat3])⟩

theorem eq_one_or_eq_of_commutant
    (hk : Nat.card k = 2)
    {J : SpecialLinearGroup (Fin 6) k} {N : Matrix (Fin 6) (Fin 6) k}
    (hJ : (J : Matrix (Fin 6) (Fin 6) k) = 1 + N) (hN : N * N = 0)
    (S : Set (SpecialLinearGroup (Fin 6) k)) (hS : ∀ s ∈ S, s * J = J * s)
    (hcomm : ∀ B : SpecialLinearGroup (Fin 6) k, (∀ s ∈ S, B * s = s * B) →
      (B : Matrix (Fin 6) (Fin 6) k) = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) k) + B 0 1 • N)
    {w : ModGL TwistTag.E6.tag k} (hw : w ∈ subsystemGroup TwistTag.E6.tag k setA)
    (hc : ∀ c ∈ subsystemGroup TwistTag.E6.tag k setA, c * realize h2 J = realize h2 J * c →
      w * c = c * w) :
    w = 1 ∨ w = realize h2 J := by
  have hinj : Function.Injective (realize h2) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro B hB
    obtain ⟨l, hl3, hl⟩ := (mem_ker_realize h2 B).1 hB
    have hl1 : l = 1 := by
      rcases eq_zero_or_eq_one_of_card hk l with rfl | rfl
      · simp at hl3
      · rfl
    rw [mem_bot]
    refine Subtype.ext ?_
    change _ = (1 : Matrix (Fin 6) (Fin 6) k)
    rw [hl, hl1]
    exact map_one _
  obtain ⟨B, rfl⟩ : w ∈ (realize h2).range := (range_realize h2).symm ▸ hw
  have hBS : ∀ s ∈ S, B * s = s * B := fun s hs => hinj (by
    rw [map_mul, map_mul]
    exact hc _ (realize_mem h2 s) (by rw [← map_mul, ← map_mul, hS s hs]))
  have hB := hcomm B hBS
  have ha : B 0 0 = 1 := by
    rcases eq_zero_or_eq_one_of_card hk (B 0 0) with h0 | h1
    · exfalso
      have hBB : (B : Matrix (Fin 6) (Fin 6) k) * B = 0 := by
        rw [hB, h0, zero_smul, zero_add, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero,
          smul_zero]
      have hdet := congrArg Matrix.det hBB
      rw [Matrix.det_mul, B.2, mul_one, Matrix.det_zero] at hdet
      exact one_ne_zero hdet
    · exact h1
  rcases eq_zero_or_eq_one_of_card hk (B 0 1) with hb | hb
  · left
    have : B = 1 := Subtype.ext (by
      change _ = (1 : Matrix (Fin 6) (Fin 6) k)
      rw [hB, ha, hb, one_smul, zero_smul, add_zero])
    rw [this, map_one]
  · right
    have : B = J := Subtype.ext (by rw [hB, ha, hb, one_smul, one_smul, hJ])
    rw [this]

theorem eq_one_or_eq_jRep₁
    (hk : Nat.card k = 2) {w : ModGL TwistTag.E6.tag k}
    (hw : w ∈ subsystemGroup TwistTag.E6.tag k setA)
    (hc : ∀ c ∈ subsystemGroup TwistTag.E6.tag k setA, c * jRep k frame₁ = jRep k frame₁ * c →
      w * c = c * w) :
    w = 1 ∨ w = jRep k frame₁ := by
  rw [← realize_sl1 h2] at hc ⊢
  exact eq_one_or_eq_of_commutant h2 hk coe_sl1 nMat1_sq {s | s ∈ gens1} gens1_comm
    gens1_commutant hw hc

theorem eq_one_or_eq_jRep₂
    (hk : Nat.card k = 2) {w : ModGL TwistTag.E6.tag k}
    (hw : w ∈ subsystemGroup TwistTag.E6.tag k setA)
    (hc : ∀ c ∈ subsystemGroup TwistTag.E6.tag k setA, c * jRep k frame₂ = jRep k frame₂ * c →
      w * c = c * w) :
    w = 1 ∨ w = jRep k frame₂ := by
  rw [← realize_sl2 h2] at hc ⊢
  exact eq_one_or_eq_of_commutant h2 hk coe_sl2 nMat2_sq {s | s ∈ gens2} gens2_comm
    gens2_commutant hw hc

theorem eq_one_or_eq_jRep₃
    (hk : Nat.card k = 2) {w : ModGL TwistTag.E6.tag k}
    (hw : w ∈ subsystemGroup TwistTag.E6.tag k setA)
    (hc : ∀ c ∈ subsystemGroup TwistTag.E6.tag k setA, c * jRep k frame₃ = jRep k frame₃ * c →
      w * c = c * w) :
    w = 1 ∨ w = jRep k frame₃ := by
  rw [← realize_sl3 h2] at hc ⊢
  exact eq_one_or_eq_of_commutant h2 hk coe_sl3 nMat3_sq {s | s ∈ gens3} gens3_comm
    gens3_commutant hw hc

end CFSG.LieType.Chevalley.E6EvenInvolution
