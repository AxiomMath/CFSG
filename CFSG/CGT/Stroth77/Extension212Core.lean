module

public import CFSG.CGT.Stroth77.Extension24
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

section TwoTorsion

variable {K : Fin 3 → ℕ}

@[expose] def invGen (K : Fin 3 → ℕ) (j : Fin 3) : Torus K :=
  ((2 : ℤ) ^ (K j - 1)) • gen K j

@[expose] def tw (K : Fin 3 → ℕ) (x y z : ℤ) : Torus K :=
  x • invGen K 0 + y • invGen K 1 + z • invGen K 2

theorem two_pow_zsmul_gen (K : Fin 3 → ℕ) (j : Fin 3) : ((2 : ℤ) ^ K j) • gen K j = 0 := by
  have h := addOrderOf_nsmul_eq_zero (gen K j)
  rw [addOrderOf_gen] at h
  rw [show ((2 : ℤ) ^ K j) = ((2 ^ K j : ℕ) : ℤ) by push_cast; rfl, natCast_zsmul, h]

theorem two_zsmul_invGen {j : Fin 3} (hK : 1 ≤ K j) : (2 : ℤ) • invGen K j = 0 := by
  rw [invGen, smul_smul, ← pow_succ', Nat.sub_add_cancel hK, two_pow_zsmul_gen]

theorem tw_eq_ofInt (x y z : ℤ) :
    tw K x y z = Torus.ofInt K ![x * 2 ^ (K 0 - 1), y * 2 ^ (K 1 - 1), z * 2 ^ (K 2 - 1)] := by
  rw [Torus.ofInt_eq_zsmul_gens]
  simp only [tw, invGen, smul_smul]
  rfl

theorem modEq_mul_two_pow_pred_iff {e : ℕ} (he : 1 ≤ e) (a b : ℤ) :
    a * 2 ^ (e - 1) ≡ b * 2 ^ (e - 1) [ZMOD 2 ^ e] ↔ 2 ∣ b - a := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  rw [Nat.add_sub_cancel, Int.modEq_iff_dvd,
    show b * 2 ^ f - a * 2 ^ f = (b - a) * 2 ^ f by ring, pow_succ, mul_comm ((2 : ℤ) ^ f) 2]
  exact mul_dvd_mul_iff_right (pow_ne_zero f two_ne_zero)

theorem tw_eq_iff (hK : ∀ j, 1 ≤ K j) {x y z x' y' z' : ℤ} :
    tw K x y z = tw K x' y' z' ↔ 2 ∣ x' - x ∧ 2 ∣ y' - y ∧ 2 ∣ z' - z := by
  rw [tw_eq_ofInt, tw_eq_ofInt, Torus.ofInt_eq_ofInt_iff]
  constructor
  · intro h
    exact ⟨(modEq_mul_two_pow_pred_iff (hK 0) _ _).1 (by simpa using h 0),
      (modEq_mul_two_pow_pred_iff (hK 1) _ _).1 (by simpa using h 1),
      (modEq_mul_two_pow_pred_iff (hK 2) _ _).1 (by simpa using h 2)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa using (modEq_mul_two_pow_pred_iff (hK 0) _ _).2 h0
    · simpa using (modEq_mul_two_pow_pred_iff (hK 1) _ _).2 h1
    · simpa using (modEq_mul_two_pow_pred_iff (hK 2) _ _).2 h2

theorem tw_congr (hK : ∀ j, 1 ≤ K j) {x y z x' y' z' : ℤ} (h0 : 2 ∣ x' - x) (h1 : 2 ∣ y' - y)
    (h2 : 2 ∣ z' - z) : tw K x y z = tw K x' y' z' :=
  (tw_eq_iff hK).2 ⟨h0, h1, h2⟩

@[simp] theorem tw_zero : tw K 0 0 0 = 0 := by
  simp [tw]

theorem tw_eq_zero_iff (hK : ∀ j, 1 ≤ K j) {x y z : ℤ} :
    tw K x y z = 0 ↔ 2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  rw [← tw_zero, tw_eq_iff hK]
  simp

theorem tw_add (x y z x' y' z' : ℤ) :
    tw K x y z + tw K x' y' z' = tw K (x + x') (y + y') (z + z') := by
  simp only [tw, add_zsmul]
  abel

theorem zsmul_tw (n x y z : ℤ) : n • tw K x y z = tw K (n * x) (n * y) (n * z) := by
  simp only [tw, smul_add, smul_smul]

theorem neg_tw (x y z : ℤ) : -tw K x y z = tw K (-x) (-y) (-z) := by
  simp only [tw, neg_add, neg_zsmul]

theorem tw_sub (x y z x' y' z' : ℤ) :
    tw K x y z - tw K x' y' z' = tw K (x - x') (y - y') (z - z') := by
  rw [sub_eq_add_neg, neg_tw, tw_add]
  ring_nf

theorem two_zsmul_tw (hK : ∀ j, 1 ≤ K j) (x y z : ℤ) : (2 : ℤ) • tw K x y z = 0 := by
  simp only [tw, smul_add, smul_comm (2 : ℤ) x, smul_comm (2 : ℤ) y, smul_comm (2 : ℤ) z,
    two_zsmul_invGen (hK _), smul_zero, add_zero]

theorem exists_tw (hK : ∀ j, 1 ≤ K j) {w : Torus K} (hw : (2 : ℤ) • w = 0) :
    ∃ x y z : ℤ, w = tw K x y z := by
  obtain ⟨e, -, rfl⟩ := (Torus.two_zsmul_eq_zero_iff hK w).1 hw
  refine ⟨e 0, e 1, e 2, ?_⟩
  rw [tw_eq_ofInt]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem tw_mul_odd (hK : ∀ j, 1 ≤ K j) {n : ℤ} (hn : Odd n) (x y z : ℤ) :
    tw K (n * x) (n * y) (n * z) = tw K x y z := by
  obtain ⟨w, rfl⟩ := hn
  exact tw_congr hK ⟨-(w * x), by ring⟩ ⟨-(w * y), by ring⟩ ⟨-(w * z), by ring⟩

theorem tw_mul_even (hK : ∀ j, 1 ≤ K j) {n : ℤ} (hn : Even n) (x y z : ℤ) :
    tw K (n * x) (n * y) (n * z) = 0 := by
  obtain ⟨w, rfl⟩ := hn
  rw [← tw_zero]
  exact tw_congr hK ⟨-(w * x), by ring⟩ ⟨-(w * y), by ring⟩ ⟨-(w * z), by ring⟩

theorem eq_tw_of_two_zsmul (hK : ∀ j, 1 ≤ K j) {w : Torus K} (hw : (2 : ℤ) • w = 0) :
    ∃ x y z : ℤ, w = tw K x y z :=
  exists_tw hK hw

end TwoTorsion

section SmallDev

variable {A : Type*} [AddCommGroup A]

structure IsSmallDev (δ : A →+ A) : Prop where
  two_zsmul : ∀ x, (2 : ℤ) • δ x = 0
  kill : ∀ x, (2 : ℤ) • x = 0 → δ x = 0

namespace IsSmallDev

variable {δ δ' : A →+ A}

theorem kill_dev (h : IsSmallDev δ) (h' : IsSmallDev δ') (x : A) : δ (δ' x) = 0 :=
  h.kill _ (h'.two_zsmul x)

theorem kill_comp_dev (h : IsSmallDev δ) (h' : IsSmallDev δ') (f : A →+ A) (x : A) :
    δ (f (δ' x)) = 0 :=
  h.kill _ (by rw [← map_zsmul, h'.two_zsmul, map_zero])

theorem kill_comp2_dev (h : IsSmallDev δ) (h' : IsSmallDev δ') (f g : A →+ A) (x : A) :
    δ (f (g (δ' x))) = 0 :=
  h.kill _ (by rw [← map_zsmul, ← map_zsmul, h'.two_zsmul, map_zero, map_zero])

theorem two_zsmul_comp (h : IsSmallDev δ) (f : A →+ A) (x : A) : (2 : ℤ) • f (δ x) = 0 := by
  rw [← map_zsmul, h.two_zsmul, map_zero]

end IsSmallDev

structure LinRels (aV aW aU aR dV dW dU dR : A →+ A) : Prop where
  uv_sq : ∀ x, aV (dV x) + dV (aV x) = 0
  t_sq : ∀ x, aW (dW x) + dW (aW x) = 0
  uv_comm_t : ∀ x, aW (dV x) + dW (aV x) = aV (dW x) + dV (aW x)
  rho_cube : ∀ x, aR (aR (dR x)) + aR (dR (aR x)) + dR (aR (aR x)) = 0
  u_sq : ∀ x, aU (dU x) + dU (aU x) = 0
  u_rho : ∀ x, aR (aU (aR (dU x))) + aR (aU (dR (aU x))) + aR (dU (aR (aU x))) +
    dR (aU (aR (aU x))) = 0
  uv_rho : ∀ x, aR (dV x) + dR (aV x) = aW (dR x) + dW (aR x)
  t_rho : ∀ x, aR (dW x) + dR (aW x) = aW (aV (dR x)) + aW (dV (aR x)) + dW (aV (aR x))
  uv_comm_u : ∀ x, aU (dV x) + dU (aV x) = aV (dU x) + dV (aU x)
  t_u : ∀ x, aU (dW x) + dU (aW x) = aW (aV (dU x)) + aW (dV (aU x)) + dW (aV (aU x))

section Expand

variable {a₁ a₂ a₃ a₄ d₁ d₂ d₃ d₄ : A →+ A}

theorem expand2 (h₁ : IsSmallDev d₁) (h₂ : IsSmallDev d₂) (x : A) :
    (a₁ + d₁) ((a₂ + d₂) x) = a₁ (a₂ x) + (a₁ (d₂ x) + d₁ (a₂ x)) := by
  simp only [AddMonoidHom.add_apply, map_add, h₁.kill_dev h₂, add_zero]
  abel

theorem two_zsmul_expand2 (h₁ : IsSmallDev d₁) (h₂ : IsSmallDev d₂) (x : A) :
    (2 : ℤ) • (a₁ (d₂ x) + d₁ (a₂ x)) = 0 := by
  rw [smul_add, h₂.two_zsmul_comp, h₁.two_zsmul, add_zero]

theorem expand3 (h₁ : IsSmallDev d₁) (h₂ : IsSmallDev d₂) (h₃ : IsSmallDev d₃) (x : A) :
    (a₁ + d₁) ((a₂ + d₂) ((a₃ + d₃) x)) =
      a₁ (a₂ (a₃ x)) + (a₁ (a₂ (d₃ x)) + a₁ (d₂ (a₃ x)) + d₁ (a₂ (a₃ x))) := by
  simp only [AddMonoidHom.add_apply, map_add, h₂.kill_dev h₃, h₁.kill_comp_dev h₃,
    h₁.kill_dev h₂, map_zero, add_zero]
  abel

theorem two_zsmul_expand3 (h₁ : IsSmallDev d₁) (h₂ : IsSmallDev d₂) (h₃ : IsSmallDev d₃)
    (x : A) : (2 : ℤ) • (a₁ (a₂ (d₃ x)) + a₁ (d₂ (a₃ x)) + d₁ (a₂ (a₃ x))) = 0 := by
  rw [smul_add, smul_add, ← map_zsmul a₁, ← map_zsmul a₂, h₃.two_zsmul, map_zero, map_zero,
    h₂.two_zsmul_comp, h₁.two_zsmul, add_zero, add_zero]

theorem expand4 (h₁ : IsSmallDev d₁) (h₂ : IsSmallDev d₂) (h₃ : IsSmallDev d₃)
    (h₄ : IsSmallDev d₄) (x : A) :
    (a₁ + d₁) ((a₂ + d₂) ((a₃ + d₃) ((a₄ + d₄) x))) =
      a₁ (a₂ (a₃ (a₄ x))) + (a₁ (a₂ (a₃ (d₄ x))) + a₁ (a₂ (d₃ (a₄ x))) +
        a₁ (d₂ (a₃ (a₄ x))) + d₁ (a₂ (a₃ (a₄ x)))) := by
  simp only [AddMonoidHom.add_apply, map_add, h₃.kill_dev h₄, h₂.kill_dev h₃, h₁.kill_dev h₂,
    h₂.kill_comp_dev h₄, h₁.kill_comp_dev h₃, h₁.kill_comp2_dev h₄, map_zero, add_zero]
  abel

end Expand

theorem linRels_of {aV aW aU aR dV dW dU dR : A →+ A}
    (h : SigmaFourRels (aV + dV) (aW + dW) (aU + dU) (aR + dR))
    (ha : SigmaFourRels aV aW aU aR) (hV : IsSmallDev dV) (hW : IsSmallDev dW)
    (hU : IsSmallDev dU) (hR : IsSmallDev dR) : LinRels aV aW aU aR dV dW dU dR := by
  have e1 {f g : A →+ A} (hfg : f = g) (x : A) : f x = g x := DFunLike.congr_fun hfg x
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_,
    fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have h1 := e1 h.uv_sq x
    have h2 := e1 ha.uv_sq x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h1 h2
    rw [expand2 hV hV, h2] at h1
    exact (add_eq_left.mp h1)
  · have h1 := e1 h.t_sq x
    have h2 := e1 ha.t_sq x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h1 h2
    rw [expand2 hW hW, h2] at h1
    exact (add_eq_left.mp h1)
  · have h1 := e1 h.uv_comm_t x
    have h2 := e1 ha.uv_comm_t x
    simp only [AddMonoidHom.comp_apply] at h1 h2
    rw [expand2 hW hV, expand2 hV hW, h2] at h1
    exact add_left_cancel h1
  · have h1 := e1 h.rho_cube x
    have h2 := e1 ha.rho_cube x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h1 h2
    rw [expand3 hR hR hR, h2] at h1
    exact (add_eq_left.mp h1)
  · have h1 := e1 h.u_sq x
    have h2 := e1 ha.u_sq x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h1 h2
    rw [expand2 hU hU, h2] at h1
    exact (add_eq_left.mp h1)
  · have h1 := e1 h.u_rho x
    have h2 := e1 ha.u_rho x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h1 h2
    rw [expand4 hR hU hR hU, h2] at h1
    exact (add_eq_left.mp h1)
  · have h1 := e1 h.uv_rho x
    have h2 := e1 ha.uv_rho x
    simp only [AddMonoidHom.comp_apply] at h1 h2
    rw [expand2 hR hV, expand2 hW hR, h2] at h1
    exact add_left_cancel h1
  · have h1 := e1 h.t_rho x
    have h2 := e1 ha.t_rho x
    simp only [AddMonoidHom.comp_apply] at h1 h2
    rw [expand2 hR hW, expand3 hW hV hR, h2] at h1
    exact add_left_cancel h1
  · have h1 := e1 h.uv_comm_u x
    have h2 := e1 ha.uv_comm_u x
    simp only [AddMonoidHom.comp_apply] at h1 h2
    rw [expand2 hU hV, expand2 hV hU, h2] at h1
    exact add_left_cancel h1
  · have h1 := e1 h.t_u x
    have h2 := e1 ha.t_u x
    simp only [AddMonoidHom.comp_apply] at h1 h2
    rw [expand2 hU hW, expand3 hW hV hU, h2] at h1
    exact add_left_cancel h1

theorem add_sub_cancel_hom (X aX : A →+ A) : aX + (X - aX) = X := by
  ext x
  simp

@[expose] def basisChange (ε : A →+ A) : A →+ A := AddMonoidHom.id A + ε

theorem basisChange_apply (ε : A →+ A) (x : A) : basisChange ε x = x + ε x := rfl

theorem basisChange_basisChange {ε : A →+ A} (hε : IsSmallDev ε) (x : A) :
    basisChange ε (basisChange ε x) = x := by
  simp only [basisChange_apply, map_add, hε.kill_dev hε, add_zero]
  rw [add_assoc, ← two_zsmul, hε.two_zsmul, add_zero]

@[expose] def basisChangeEquiv {ε : A →+ A} (hε : IsSmallDev ε) : A ≃+ A where
  toFun := basisChange ε
  invFun := basisChange ε
  left_inv := basisChange_basisChange hε
  right_inv := basisChange_basisChange hε
  map_add' := map_add _

theorem basisChangeEquiv_apply {ε : A →+ A} (hε : IsSmallDev ε) (x : A) :
    basisChangeEquiv hε x = x + ε x := rfl

theorem basisChangeEquiv_symm_apply {ε : A →+ A} (hε : IsSmallDev ε) (x : A) :
    (basisChangeEquiv hε).symm x = x + ε x := rfl

theorem basisChange_conj {ε δ : A →+ A} (hε : IsSmallDev ε) (hδ : IsSmallDev δ) (a : A →+ A)
    (x : A) :
    basisChange ε ((a + δ) (basisChange ε x)) = a x + (δ x + ε (a x) + a (ε x)) := by
  simp only [basisChange_apply, AddMonoidHom.add_apply, map_add, hδ.kill_dev hε,
    hε.kill_comp_dev hε, hε.kill_dev hδ, add_zero]
  abel

theorem IsSmallDev.basisChange_dev {ε δ : A →+ A} (hε : IsSmallDev ε) (hδ : IsSmallDev δ)
    (a : A →+ A) : IsSmallDev (δ + ε.comp a + a.comp ε) where
  two_zsmul x := by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, smul_add, hδ.two_zsmul,
      hε.two_zsmul, hε.two_zsmul_comp, add_zero]
  kill x hx := by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hδ.kill x hx, hε.kill x hx,
      map_zero, add_zero, zero_add]
    exact hε.kill _ (by rw [← map_zsmul, hx, map_zero])

end SmallDev

section TorusDev

variable {K : Fin 3 → ℕ}

theorem isSmallDev_of_gens (hK : ∀ j, 1 ≤ K j) (f : Torus K →+ Torus K)
    (h20 : (2 : ℤ) • f (gen K 0) = 0) (h21 : (2 : ℤ) • f (gen K 1) = 0)
    (h22 : (2 : ℤ) • f (gen K 2) = 0) (hi0 : f (invGen K 0) = 0) (hi1 : f (invGen K 1) = 0)
    (hi2 : f (invGen K 2) = 0) : IsSmallDev f where
  two_zsmul x := by
    obtain ⟨p, q, r, rfl⟩ := torus_eq_zsmul_gens K x
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, smul_add, smul_add,
      smul_comm (2 : ℤ) p, smul_comm (2 : ℤ) q, smul_comm (2 : ℤ) r, h20, h21, h22, smul_zero,
      smul_zero, smul_zero, add_zero, add_zero]
  kill x hx := by
    obtain ⟨p, q, r, rfl⟩ := exists_tw hK hx
    rw [tw, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hi0, hi1, hi2, smul_zero,
      smul_zero, smul_zero, add_zero, add_zero]

theorem map_invGen_eq_zero {f : Torus K →+ Torus K} {j : Fin 3} (hKj : 2 ≤ K j)
    (h : f ((2 : ℤ) • gen K j) = 0) : f (invGen K j) = 0 := by
  rw [invGen, show K j - 1 = (K j - 2) + 1 by omega, pow_succ, mul_smul, map_zsmul, h,
    smul_zero]

theorem map_invGen_eq_zero_of_gen {f : Torus K →+ Torus K} {j : Fin 3} (h : f (gen K j) = 0) :
    f (invGen K j) = 0 := by
  rw [invGen, map_zsmul, h, smul_zero]

theorem isSmallDev_sub_idx4 (hK : ∀ j, 1 ≤ K j) (hK1 : 2 ≤ K 1) (hK2 : 2 ≤ K 2)
    {X aX : Torus K →+ Torus K} (h0 : X (gen K 0) = aX (gen K 0))
    (h1 : X ((2 : ℤ) • gen K 1) = aX ((2 : ℤ) • gen K 1))
    (h2 : X ((2 : ℤ) • gen K 2) = aX ((2 : ℤ) • gen K 2)) : IsSmallDev (X - aX) := by
  have e0 : (X - aX) (gen K 0) = 0 := by rw [AddMonoidHom.sub_apply, h0, sub_self]
  have e1 : (X - aX) ((2 : ℤ) • gen K 1) = 0 := by rw [AddMonoidHom.sub_apply, h1, sub_self]
  have e2 : (X - aX) ((2 : ℤ) • gen K 2) = 0 := by rw [AddMonoidHom.sub_apply, h2, sub_self]
  refine isSmallDev_of_gens hK _ (by rw [e0, smul_zero]) (by rw [← map_zsmul]; exact e1)
    (by rw [← map_zsmul]; exact e2) (map_invGen_eq_zero_of_gen e0) (map_invGen_eq_zero hK1 e1)
    (map_invGen_eq_zero hK2 e2)

theorem isSmallDev_sub_idx2 (hK : ∀ j, 1 ≤ K j) (hK0 : 2 ≤ K 0)
    {X aX : Torus K →+ Torus K} (h0 : X ((2 : ℤ) • gen K 0) = aX ((2 : ℤ) • gen K 0))
    (h1 : X (gen K 1) = aX (gen K 1)) (h2 : X (gen K 2) = aX (gen K 2)) :
    IsSmallDev (X - aX) := by
  have e0 : (X - aX) ((2 : ℤ) • gen K 0) = 0 := by rw [AddMonoidHom.sub_apply, h0, sub_self]
  have e1 : (X - aX) (gen K 1) = 0 := by rw [AddMonoidHom.sub_apply, h1, sub_self]
  have e2 : (X - aX) (gen K 2) = 0 := by rw [AddMonoidHom.sub_apply, h2, sub_self]
  refine isSmallDev_of_gens hK _ (by rw [← map_zsmul]; exact e0) (by rw [e1, smul_zero])
    (by rw [e2, smul_zero]) (map_invGen_eq_zero hK0 e0) (map_invGen_eq_zero_of_gen e1)
    (map_invGen_eq_zero_of_gen e2)

theorem nsmul_tw_eq_zero (hK : ∀ j, 1 ≤ K j) (j : Fin 3) (x y z : ℤ) :
    (2 ^ K j) • tw K x y z = 0 := by
  obtain ⟨e, he⟩ : ∃ e, K j = e + 1 := ⟨K j - 1, by have := hK j; omega⟩
  have h2 : (2 : ℕ) • tw K x y z = 0 := by
    rw [← natCast_zsmul]
    exact two_zsmul_tw hK x y z
  rw [he, pow_succ, mul_smul, h2, smul_zero]

@[expose] noncomputable def eps4 (K : Fin 3 → ℕ) (hK : ∀ j, 1 ≤ K j) (p₀ p₁ p₂ q₀ q₁ q₂ : ℤ) :
    Torus K →+ Torus K :=
  torusHomOfGens K ![0, tw K p₀ p₁ p₂, tw K q₀ q₁ q₂] (fun i => by
    fin_cases i
    · simp
    · exact nsmul_tw_eq_zero hK 1 _ _ _
    · exact nsmul_tw_eq_zero hK 2 _ _ _)

theorem eps4_gen0 (hK : ∀ j, 1 ≤ K j) (p₀ p₁ p₂ q₀ q₁ q₂ : ℤ) :
    eps4 K hK p₀ p₁ p₂ q₀ q₁ q₂ (gen K 0) = 0 := by
  simp [eps4, torusHomOfGens_gen]

theorem eps4_gen1 (hK : ∀ j, 1 ≤ K j) (p₀ p₁ p₂ q₀ q₁ q₂ : ℤ) :
    eps4 K hK p₀ p₁ p₂ q₀ q₁ q₂ (gen K 1) = tw K p₀ p₁ p₂ := by
  simp [eps4, torusHomOfGens_gen]

theorem eps4_gen2 (hK : ∀ j, 1 ≤ K j) (p₀ p₁ p₂ q₀ q₁ q₂ : ℤ) :
    eps4 K hK p₀ p₁ p₂ q₀ q₁ q₂ (gen K 2) = tw K q₀ q₁ q₂ := by
  simp [eps4, torusHomOfGens_gen]

theorem isSmallDev_eps4 (hK : ∀ j, 1 ≤ K j) (hK1 : 2 ≤ K 1) (hK2 : 2 ≤ K 2)
    (p₀ p₁ p₂ q₀ q₁ q₂ : ℤ) : IsSmallDev (eps4 K hK p₀ p₁ p₂ q₀ q₁ q₂) := by
  refine isSmallDev_of_gens hK _ (by rw [eps4_gen0, smul_zero])
    (by rw [eps4_gen1, two_zsmul_tw hK]) (by rw [eps4_gen2, two_zsmul_tw hK])
    (map_invGen_eq_zero_of_gen (eps4_gen0 hK _ _ _ _ _ _))
    (map_invGen_eq_zero hK1 (by rw [map_zsmul, eps4_gen1, two_zsmul_tw hK]))
    (map_invGen_eq_zero hK2 (by rw [map_zsmul, eps4_gen2, two_zsmul_tw hK]))

@[expose] noncomputable def eps2 (K : Fin 3 → ℕ) (hK : ∀ j, 1 ≤ K j) (p₀ p₁ p₂ : ℤ) :
    Torus K →+ Torus K :=
  torusHomOfGens K ![tw K p₀ p₁ p₂, 0, 0] (fun i => by
    fin_cases i
    · exact nsmul_tw_eq_zero hK 0 _ _ _
    · simp
    · simp)

theorem eps2_gen0 (hK : ∀ j, 1 ≤ K j) (p₀ p₁ p₂ : ℤ) :
    eps2 K hK p₀ p₁ p₂ (gen K 0) = tw K p₀ p₁ p₂ := by
  simp [eps2, torusHomOfGens_gen]

theorem eps2_gen1 (hK : ∀ j, 1 ≤ K j) (p₀ p₁ p₂ : ℤ) : eps2 K hK p₀ p₁ p₂ (gen K 1) = 0 := by
  simp [eps2, torusHomOfGens_gen]

theorem eps2_gen2 (hK : ∀ j, 1 ≤ K j) (p₀ p₁ p₂ : ℤ) : eps2 K hK p₀ p₁ p₂ (gen K 2) = 0 := by
  simp [eps2, torusHomOfGens_gen]

theorem isSmallDev_eps2 (hK : ∀ j, 1 ≤ K j) (hK0 : 2 ≤ K 0) (p₀ p₁ p₂ : ℤ) :
    IsSmallDev (eps2 K hK p₀ p₁ p₂) := by
  refine isSmallDev_of_gens hK _ (by rw [eps2_gen0, two_zsmul_tw hK])
    (by rw [eps2_gen1, smul_zero]) (by rw [eps2_gen2, smul_zero])
    (map_invGen_eq_zero hK0 (by rw [map_zsmul, eps2_gen0, two_zsmul_tw hK]))
    (map_invGen_eq_zero_of_gen (eps2_gen1 hK _ _ _))
    (map_invGen_eq_zero_of_gen (eps2_gen2 hK _ _ _))

theorem dev_zsmul_gens_idx4 {δ : Torus K →+ Torus K} (h0 : δ (gen K 0) = 0) (x y z : ℤ) :
    δ (x • gen K 0 + y • gen K 1 + z • gen K 2) = y • δ (gen K 1) + z • δ (gen K 2) := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, smul_zero, zero_add]

theorem dev_zsmul_gens_idx2 {δ : Torus K →+ Torus K} (h1 : δ (gen K 1) = 0)
    (h2 : δ (gen K 2) = 0) (x y z : ℤ) :
    δ (x • gen K 0 + y • gen K 1 + z • gen K 2) = x • δ (gen K 0) := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h1, h2, smul_zero, smul_zero, add_zero,
    add_zero]

end TorusDev

end CFSG.CGT.Stroth77
