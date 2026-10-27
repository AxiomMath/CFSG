module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank

structure E8Triple {G : Type*} [Group G] (u v w : G) : Prop where
  sq_u : u * u = 1
  sq_v : v * v = 1
  sq_w : w * w = 1
  comm_uv : u * v = v * u
  comm_uw : u * w = w * u
  comm_vw : v * w = w * v
  ne_u : u ≠ 1
  ne_v : v ≠ 1
  ne_w : w ≠ 1
  ne_uv : u * v ≠ 1
  ne_uw : u * w ≠ 1
  ne_vw : v * w ≠ 1
  ne_uvw : u * v * w ≠ 1

namespace E8Triple

variable {G H : Type*} [Group G] [Group H] {u v w : G}

theorem sq_of_comm {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem sq_uv (h : E8Triple u v w) : u * v * (u * v) = 1 := sq_of_comm h.sq_u h.sq_v h.comm_uv

theorem sq_uw (h : E8Triple u v w) : u * w * (u * w) = 1 := sq_of_comm h.sq_u h.sq_w h.comm_uw

theorem sq_vw (h : E8Triple u v w) : v * w * (v * w) = 1 := sq_of_comm h.sq_v h.sq_w h.comm_vw

theorem comm_uv_w (h : E8Triple u v w) : u * v * w = w * (u * v) := by
  calc u * v * w = u * (v * w) := by group
    _ = u * (w * v) := by rw [h.comm_vw]
    _ = (u * w) * v := by group
    _ = (w * u) * v := by rw [h.comm_uw]
    _ = w * (u * v) := by group

theorem sq_uvw (h : E8Triple u v w) : u * v * w * (u * v * w) = 1 :=
  sq_of_comm h.sq_uv h.sq_w h.comm_uv_w

theorem map (h : E8Triple u v w) (φ : G →* H) (hφ : ∀ g, g * g = 1 → φ g = 1 → g = 1) :
    E8Triple (φ u) (φ v) (φ w) where
  sq_u := by rw [← map_mul, h.sq_u, map_one]
  sq_v := by rw [← map_mul, h.sq_v, map_one]
  sq_w := by rw [← map_mul, h.sq_w, map_one]
  comm_uv := by rw [← map_mul, h.comm_uv, map_mul]
  comm_uw := by rw [← map_mul, h.comm_uw, map_mul]
  comm_vw := by rw [← map_mul, h.comm_vw, map_mul]
  ne_u := fun h1 => h.ne_u (hφ u h.sq_u h1)
  ne_v := fun h1 => h.ne_v (hφ v h.sq_v h1)
  ne_w := fun h1 => h.ne_w (hφ w h.sq_w h1)
  ne_uv := fun h1 => h.ne_uv (hφ _ h.sq_uv (by rw [map_mul]; exact h1))
  ne_uw := fun h1 => h.ne_uw (hφ _ h.sq_uw (by rw [map_mul]; exact h1))
  ne_vw := fun h1 => h.ne_vw (hφ _ h.sq_vw (by rw [map_mul]; exact h1))
  ne_uvw := fun h1 => h.ne_uvw (hφ _ h.sq_uvw (by rw [map_mul, map_mul]; exact h1))

theorem map_injective (h : E8Triple u v w) (φ : G →* H) (hφ : Function.Injective φ) :
    E8Triple (φ u) (φ v) (φ w) :=
  h.map φ fun _ _ h1 => hφ (h1.trans (map_one φ).symm)

end E8Triple

theorem eq_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {a b : C}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq]
      exact ha
    · rw [sq]
      exact hb
  have h1 : (1 : C) ∉ ({a, b} : Finset C) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have hcard : ({1, a, b} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_pair_eq_two_iff.mpr hab]
  have h3 := Finset.card_le_card hsub
  have h4 : (Finset.univ.filter (fun x : C => x ^ 2 = 1)).card ≤ 2 := by
    convert hle
  omega

theorem false_of_cyclic_index_two {G : Type*} [Group G] {P₀ : Subgroup G} [Finite P₀] {y : G}
    (hy : y ∈ P₀) (hcard : Nat.card P₀ = 2 * orderOf y) {u v w : G} (hu : u ∈ P₀) (hv : v ∈ P₀)
    (hw : w ∈ P₀) (h : E8Triple u v w) : False := by
  set y' : P₀ := ⟨y, hy⟩ with hy'
  set C : Subgroup P₀ := zpowers y' with hC
  have hCc : Nat.card C = orderOf y := by
    rw [hC, Nat.card_zpowers, hy', Subgroup.orderOf_mk]
  have hpos : 0 < orderOf y := by
    have := Nat.card_pos (α := P₀)
    omega
  have hidx : C.index = 2 := by
    have h1 := C.card_mul_index
    rw [hCc, hcard] at h1
    have h2 : orderOf y * C.index = orderOf y * 2 := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hmul := fun a b => mul_mem_iff_of_index_two (H := C) hidx (a := a) (b := b)
  have huniq : ∀ a b : P₀, a ∈ C → b ∈ C → a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a = b := by
    intro a b ha hb ha2 hb2 ha1 hb1
    have e := eq_of_isCyclic (C := C) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (Subtype.ext ha2)
      (Subtype.ext hb2) (fun h' => ha1 (congrArg Subtype.val h')) (fun h' => hb1
        (congrArg Subtype.val h'))
    exact congrArg Subtype.val e
  set U : P₀ := ⟨u, hu⟩
  set V : P₀ := ⟨v, hv⟩
  set W : P₀ := ⟨w, hw⟩
  have hT : E8Triple U V W :=
    ⟨Subtype.ext h.sq_u, Subtype.ext h.sq_v, Subtype.ext h.sq_w, Subtype.ext h.comm_uv,
      Subtype.ext h.comm_uw, Subtype.ext h.comm_vw, fun h' => h.ne_u (congrArg Subtype.val h'),
      fun h' => h.ne_v (congrArg Subtype.val h'), fun h' => h.ne_w (congrArg Subtype.val h'),
      fun h' => h.ne_uv (congrArg Subtype.val h'), fun h' => h.ne_uw (congrArg Subtype.val h'),
      fun h' => h.ne_vw (congrArg Subtype.val h'), fun h' => h.ne_uvw (congrArg Subtype.val h')⟩
  clear_value U V W
  by_cases hUC : U ∈ C <;> by_cases hVC : V ∈ C <;> by_cases hWC : W ∈ C
  · exact hT.ne_uv (by rw [huniq U V hUC hVC hT.sq_u hT.sq_v hT.ne_u hT.ne_v, hT.sq_v])
  · exact hT.ne_uv (by rw [huniq U V hUC hVC hT.sq_u hT.sq_v hT.ne_u hT.ne_v, hT.sq_v])
  · exact hT.ne_uw (by rw [huniq U W hUC hWC hT.sq_u hT.sq_w hT.ne_u hT.ne_w, hT.sq_w])
  ·
    have hVW : V * W ∈ C := (hmul V W).mpr (iff_of_false hVC hWC)
    have e := huniq U (V * W) hUC hVW hT.sq_u hT.sq_vw hT.ne_u hT.ne_vw
    exact hT.ne_uvw (by rw [mul_assoc, ← e, hT.sq_u])
  · exact hT.ne_vw (by rw [huniq V W hVC hWC hT.sq_v hT.sq_w hT.ne_v hT.ne_w, hT.sq_w])
  ·
    have hUW : U * W ∈ C := (hmul U W).mpr (iff_of_false hUC hWC)
    have e := huniq V (U * W) hVC hUW hT.sq_v hT.sq_uw hT.ne_v hT.ne_uw
    exact hT.ne_uvw (by
      rw [e]
      calc U * (U * W) * W = (U * U) * (W * W) := by group
        _ = 1 := by rw [hT.sq_u, hT.sq_w, one_mul])
  ·
    have hUV : U * V ∈ C := (hmul U V).mpr (iff_of_false hUC hVC)
    have e := huniq W (U * V) hWC hUV hT.sq_w hT.sq_uv hT.ne_w hT.ne_uv
    exact hT.ne_uvw (by rw [e, hT.sq_uv])
  ·
    have hUV : U * V ∈ C := (hmul U V).mpr (iff_of_false hUC hVC)
    have hUW : U * W ∈ C := (hmul U W).mpr (iff_of_false hUC hWC)
    have e := huniq (U * V) (U * W) hUV hUW hT.sq_uv hT.sq_uw hT.ne_uv hT.ne_uw
    have e' : V = W := mul_left_cancel e
    exact hT.ne_vw (by rw [e', hT.sq_w])

section PSL

variable {F : Type} [Field F]

theorem det_eq_one_of_mem_statedSL {A : GL (Fin 2) F} (hA : A ∈ StatedSL 2 F) :
    (A : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem eq_one_or_neg_one_of_sq (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 2) (Fin 2) F}
    (hdet : A.det = 1) (hA : A * A = 1) : A = 1 ∨ A = -1 := by
  have e : ∀ i j, (A * A) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [hA]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have htr : A 0 0 + A 1 1 ≠ 0 := by
    intro h0
    have h11 : A 1 1 = -A 0 0 := by linear_combination h0
    rw [h11] at hdet e11
    have : (2 : F) = 0 := by linear_combination -hdet - e00
    exact h2 this
  have hb : A 0 1 = 0 := by
    have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right htr
  have hc : A 1 0 = 0 := by
    have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right htr
  have e00' : A 0 0 * A 0 0 = 1 := by rw [hb, zero_mul, add_zero] at e00; exact e00
  have hdet' : A 0 0 * A 1 1 = 1 := by rw [hb, zero_mul, sub_zero] at hdet; exact hdet
  have ha : A 0 0 = 1 ∨ A 0 0 = -1 := by
    have : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by linear_combination e00'
    rcases mul_eq_zero.1 this with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  rcases ha with ha | ha
  · left
    have hd : A 1 1 = 1 := by rw [ha, one_mul] at hdet'; exact hdet'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · right
    have hd : A 1 1 = -1 := by linear_combination -hdet' + (A 1 1) * ha
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem sq_eq_neg_one_of_statedProj (h2 : (2 : F) ≠ 0) (X : StatedSL 2 F)
    (hX2 : (QuotientGroup.mk X : StatedProj (StatedSL 2 F)) *
      (QuotientGroup.mk X : StatedProj (StatedSL 2 F)) = 1)
    (hX1 : (QuotientGroup.mk X : StatedProj (StatedSL 2 F)) ≠ 1) :
    ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (X : GL (Fin 2) F) = -1 := by
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf] at hX2
  obtain ⟨c, hc⟩ := hX2
  have hdet := det_eq_one_of_mem_statedSL X.2
  have hcm : ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (X : GL (Fin 2) F) =
      (c : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have e := congrArg Units.val hc
    rw [GeneralLinearGroup.coe_scalar] at e
    rw [Subgroup.coe_mul, Units.val_mul] at e
    rw [← e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hc2 : (c : F) * c = 1 := by
    have e := congrArg Matrix.det hcm
    rw [Matrix.det_mul, hdet, one_mul, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin, pow_two] at e
    exact e.symm
  have hc' : (c : F) = 1 ∨ (c : F) = -1 := by
    have : ((c : F) - 1) * ((c : F) + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.1 this with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  rcases hc' with h1 | h1
  · exfalso
    apply hX1
    rw [h1, one_smul] at hcm
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    rcases eq_one_or_neg_one_of_sq h2 hdet hcm with h | h
    · exact ⟨1, Units.ext (by
        rw [GeneralLinearGroup.coe_scalar, h]
        ext i j
        fin_cases i <;> fin_cases j <;> simp)⟩
    · exact ⟨-1, Units.ext (by
        rw [GeneralLinearGroup.coe_scalar, h]
        ext i j
        fin_cases i <;> fin_cases j <;> simp)⟩
  · rw [h1, neg_one_smul] at hcm
    exact hcm

theorem false_of_statedProjSL (h2 : (2 : F) ≠ 0) {x y z : StatedProj (StatedSL 2 F)}
    (h : E8Triple x y z) : False := by
  obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨Z, rfl⟩ := QuotientGroup.mk_surjective z
  set A := ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hA
  set B := ((Y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hB
  set C := ((Z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hC
  have sq := fun (W : StatedSL 2 F) hW2 hW1 => sq_eq_neg_one_of_statedProj h2 W hW2 hW1
  have hAA : A * A = -1 := sq X h.sq_u h.ne_u
  have hBB : B * B = -1 := sq Y h.sq_v h.ne_v
  have hCC : C * C = -1 := sq Z h.sq_w h.ne_w
  have hAB : A * B * (A * B) = -1 := by
    have := sq (X * Y) (by rw [QuotientGroup.mk_mul]; exact h.sq_uv)
      (by rw [QuotientGroup.mk_mul]; exact h.ne_uv)
    simpa [hA, hB, Subgroup.coe_mul, Units.val_mul] using this
  have hAC : A * C * (A * C) = -1 := by
    have := sq (X * Z) (by rw [QuotientGroup.mk_mul]; exact h.sq_uw)
      (by rw [QuotientGroup.mk_mul]; exact h.ne_uw)
    simpa [hA, hC, Subgroup.coe_mul, Units.val_mul] using this
  have hBC : B * C * (B * C) = -1 := by
    have := sq (Y * Z) (by rw [QuotientGroup.mk_mul]; exact h.sq_vw)
      (by rw [QuotientGroup.mk_mul]; exact h.ne_vw)
    simpa [hB, hC, Subgroup.coe_mul, Units.val_mul] using this
  have anti : ∀ P R : Matrix (Fin 2) (Fin 2) F, P * P = -1 → R * R = -1 →
      P * R * (P * R) = -1 → R * P = -(P * R) := by
    intro P R hP hR hPR
    have e1 : P * (P * R * (P * R)) = -P := by rw [hPR, mul_neg, mul_one]
    have e2 : P * (P * R * (P * R)) = -(R * P * R) := by
      calc P * (P * R * (P * R)) = (P * P) * R * P * R := by simp only [Matrix.mul_assoc]
        _ = -(R * P * R) := by rw [hP]; simp only [neg_mul, one_mul]
    have e3 : R * P * R = P := by
      have := e2.symm.trans e1
      rwa [neg_inj] at this
    calc R * P = R * P * (R * R) * (-1) := by rw [hR]; simp
      _ = (R * P * R) * R * (-1) := by simp only [Matrix.mul_assoc]
      _ = -(P * R) := by rw [e3]; simp
  have hBA := anti A B hAA hBB hAB
  have hCA := anti A C hAA hCC hAC
  have hCB := anti B C hBB hCC hBC
  have hABC : A * B * C * (A * B * C) = 1 := by
    calc A * B * C * (A * B * C) = A * B * (C * A) * B * C := by
          simp only [Matrix.mul_assoc]
      _ = -(A * B * A * (C * B) * C) := by
          rw [hCA]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(A * (B * A) * (C * B) * C) := by simp only [Matrix.mul_assoc]
      _ = -(A * (A * B) * (B * C) * C) := by
          rw [hBA, hCB]; simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
      _ = -((A * A) * (B * B) * (C * C)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAA, hBB, hCC]; simp
  have hdet : (A * B * C).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hA, hB, hC, det_eq_one_of_mem_statedSL X.2,
      det_eq_one_of_mem_statedSL Y.2, det_eq_one_of_mem_statedSL Z.2, one_mul, one_mul]
  apply h.ne_uvw
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hval : (((X * Y * Z : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      A * B * C := by simp [hA, hB, hC, Subgroup.coe_mul, Units.val_mul]
  rcases eq_one_or_neg_one_of_sq h2 hdet hABC with h1 | h1
  · exact ⟨1, Units.ext (by
      rw [GeneralLinearGroup.coe_scalar, hval, h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp)⟩
  · exact ⟨-1, Units.ext (by
      rw [GeneralLinearGroup.coe_scalar, hval, h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp)⟩

end PSL

end CFSG.ComponentClassification.GSThmB.X10Orth
