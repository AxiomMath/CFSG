module

public import CFSG.LinearAlgebra.DesarguesianPlanes.RootModules
public import CFSG.LinearAlgebra.DesarguesianPlanes.JordanDerivation
public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition

public section

namespace CFSG.DesarguesianPlanes

open Matrix
open scoped commutatorElement MatrixGroups

variable {G : Type*} [Group G] {F : Type} [Field F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  {J : G} {φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z} {Y : G}

structure RootCoordData (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z) (Y : G) where
  x02 : F → G
  x12 : F → G
  x21 : F → G
  x20 : F → G
  κ : F
  hκ : κ ≠ 0
  add02 : ∀ c d, x02 (c + d) = x02 c * x02 d
  add12 : ∀ c d, x12 (c + d) = x12 c * x12 d
  add21 : ∀ c d, x21 (c + d) = x21 c * x21 d
  add20 : ∀ c d, x20 (c + d) = x20 c * x20 d
  mem02 : ∀ c, x02 c ∈ rootSub φ Y 0 2
  mem12 : ∀ c, x12 c ∈ rootSub φ Y 1 2
  mem21 : ∀ c, x21 c ∈ rootSub φ Y 2 1
  mem20 : ∀ c, x20 c ∈ rootSub φ Y 2 0
  up12 : ∀ c d, ⁅rootUp φ c, x12 d⁆ = x02 (c * d)
  low02 : ∀ c d, ⁅rootLow φ c, x02 d⁆ = x12 (c * d)
  up20 : ∀ c d, ⁅rootUp φ c, x20 d⁆ = x21 (c * d)
  low21 : ∀ c d, ⁅rootLow φ c, x21 d⁆ = x20 (c * d)
  pair : ∀ c d, ⁅x02 c, x21 d⁆ = rootUp φ (κ * c * d)
  pair' : ∀ c d, ⁅x12 c, x20 d⁆ = rootLow φ (-(κ * c * d))


theorem exists_ne_one_of_card_eq [Finite F] {H : Subgroup G} (hc : Nat.card H = Nat.card F) :
    ∃ e : H, e ≠ 1 := by
  have hlt : 1 < Nat.card H := by
    rw [hc]
    exact Finite.one_lt_card
  have : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have := Finite.one_lt_card_iff_nontrivial.mp hlt
  exact exists_ne 1

section Exists

variable [Finite F] (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
  (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
  (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)
  (hR : BrauerRootRelations φ Y)
include hZ hZodd h2 hJ hY₁ hY₂ hR

theorem nonempty_rootCoordData : Nonempty (RootCoordData φ Y) := by
  have hVu := isRootModule_upper hZ hZodd h2 hJ hY₁ hY₂ hR
  have hVl := isRootModule_lower hZ hZodd h2 hJ hY₁ hY₂ hR
  obtain ⟨e, he⟩ := exists_ne_one_of_card_eq (card_rootSub_02 (Y := Y) hZ)
  obtain ⟨e', he'⟩ := exists_ne_one_of_card_eq (card_rootSub_21 (Y := Y) hZ)
  set X02 : F → G := fun c => (hVu.xi₁ e c : G) with hX02
  set X12 : F → G := fun c => (hVu.xi₂ e c : G) with hX12
  set X21 : F → G := fun c => (hVl.xi₁ e' c : G) with hX21
  set X20 : F → G := fun c => (hVl.xi₂ e' c : G) with hX20
  have hm02 : ∀ c, X02 c ∈ rootSub φ Y 0 2 := fun c => (hVu.xi₁ e c).2
  have hm21 : ∀ c, X21 c ∈ rootSub φ Y 2 1 := fun c => (hVl.xi₁ e' c).2
  have hpair_mem : ∀ c d, ⁅X02 c, X21 d⁆ ∈ rootX₁ φ := fun c d =>
    hR.commIn_X₂_one_X₂_two.symm _ (hm02 c) _ (hm21 d)
  choose P hP using fun c d => (mem_rootX₁ φ).mp (hpair_mem c d)
  have hinj := rootUp_injective φ hZ
  have hmulUp : ∀ a b : F, rootUp φ a * rootUp φ b = rootUp φ (a + b) := fun a b => by
    rw [rootUp, rootUp, rootUp, ← map_mul, upperGL_add]
  have hadd₁ : ∀ c c' d, P (c + c') d = P c d + P c' d := by
    intro c c' d
    apply hinj
    have hk : X02 c * ⁅X02 c', X21 d⁆ * (X02 c)⁻¹ = ⁅X02 c', X21 d⁆ := by
      rw [← hR.commutes_X₁_X₂_two _ (hpair_mem c' d) _ (hm02 c), mul_inv_cancel_right]
    have hsplit : ⁅X02 (c + c'), X21 d⁆ = ⁅X02 c', X21 d⁆ * ⁅X02 c, X21 d⁆ := by
      rw [show X02 (c + c') = X02 c * X02 c' by simp only [hX02, hVu.xi₁_add, Subgroup.coe_mul],
        commutatorElement_mul_left', hk]
    rw [hP, hsplit, ← hP c' d, ← hP c d, hmulUp, add_comm]
  have hadd₂ : ∀ c d d', P c (d + d') = P c d + P c d' := by
    intro c d d'
    apply hinj
    have hsplit : ⁅X02 c, X21 (d + d')⁆ = ⁅X02 c, X21 d⁆ * ⁅X02 c, X21 d'⁆ := by
      rw [show X21 (d + d') = X21 d * X21 d' by simp only [hX21, hVl.xi₁_add, Subgroup.coe_mul]]
      apply commutatorElement_mul_right_of_commute
      exact (hR.commutes_X₁_X₂_one _ (hpair_mem c d') _ (hm21 d)).symm
    rw [hP, hsplit, ← hP c d, ← hP c d', hmulUp]
  have hsq : ∀ a c d, a ≠ 0 → P (a * c) (a * d) = a ^ 2 * P c d := by
    intro a c d ha
    apply hinj
    set u : Fˣ := Units.mk0 a ha
    have hu : (u : F) = a := rfl
    set h := linearCentralizerHom φ (diagGL u u⁻¹)
    have h02 : h * X02 c * h⁻¹ = X02 (a * c) := by
      rw [hX02]
      simp only
      rw [hVu.torus₁ e u c, hu]
    have h21 : h * X21 d * h⁻¹ = X21 (a * d) := by
      rw [hX21]
      simp only
      rw [hVl.torus₁ e' u d, hu]
    have hcomm : h * ⁅X02 c, X21 d⁆ * h⁻¹ = ⁅h * X02 c * h⁻¹, h * X21 d * h⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have hup : h * rootUp φ (P c d) * h⁻¹ = rootUp φ (a ^ 2 * P c d) := by
      have := diag_conj_rootUp φ u u⁻¹ (P c d)
      rw [conjHom_apply] at this
      rw [this, inv_inv, hu]
      congr 1
      ring
    rw [hP, ← h02, ← h21, ← hcomm, ← hP, hup]
  have hP' : ∀ c d, P c d = P 1 1 * c * d :=
    biadditive_eq_of_sq_equivariant h2 P hadd₁ hadd₂ hsq
  have hκ : P 1 1 ≠ 0 := by
    intro hκ0
    obtain ⟨a, ha, b, hb, hab⟩ := hR.nonTriv_X₂_one_X₂_two
    obtain ⟨d, hd⟩ := (hVl.xi₁_bijective e' he').2 ⟨a, ha⟩
    obtain ⟨c, hc⟩ := (hVu.xi₁_bijective e he).2 ⟨b, hb⟩
    have ha' : X21 d = a := by rw [hX21]; simp only; rw [hd]
    have hb' : X02 c = b := by rw [hX02]; simp only; rw [hc]
    apply hab
    rw [← ha', ← hb', ← commutatorElement_inv, ← hP, hP', hκ0, zero_mul, zero_mul, rootUp,
      upperGL_zero, map_one, inv_one]
  have hweylUp : ∀ t : F, linearCentralizerHom φ (weylGL 1) * rootUp φ t *
      (linearCentralizerHom φ (weylGL 1))⁻¹ = rootLow φ (-t) := fun t => by
    rw [rootUp, rootLow, ← map_mul, ← map_inv, ← map_mul, weylGL_one_mul_upperGL,
      mul_inv_cancel_right]
  have hpair' : ∀ c d, ⁅X12 c, X20 d⁆ = rootLow φ (-(P 1 1 * c * d)) := by
    intro c d
    set w := linearCentralizerHom φ (weylGL 1)
    have h12 : w * X02 (-c) * w⁻¹ = X12 c := by
      rw [hX02, hX12]
      simp only
      rw [hVu.weyl₁ e (-c), neg_neg]
    have h20 : w * X21 (-d) * w⁻¹ = X20 d := by
      rw [hX21, hX20]
      simp only
      rw [hVl.weyl₁ e' (-d), neg_neg]
    have hcomm : w * ⁅X02 (-c), X21 (-d)⁆ * w⁻¹ = ⁅w * X02 (-c) * w⁻¹, w * X21 (-d) * w⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [← h12, ← h20, ← hcomm, ← hP, hweylUp, hP']
    congr 2
    ring
  exact ⟨{ x02 := X02, x12 := X12, x21 := X21, x20 := X20, κ := P 1 1, hκ := hκ
           add02 := fun c d => by simp only [hX02, hVu.xi₁_add, Subgroup.coe_mul]
           add12 := fun c d => by simp only [hX12, hVu.xi₂_add, Subgroup.coe_mul]
           add21 := fun c d => by simp only [hX21, hVl.xi₁_add, Subgroup.coe_mul]
           add20 := fun c d => by simp only [hX20, hVl.xi₂_add, Subgroup.coe_mul]
           mem02 := hm02
           mem12 := fun c => (hVu.xi₂ e c).2
           mem21 := hm21
           mem20 := fun c => (hVl.xi₂ e' c).2
           up12 := fun c d => hVu.comm_up e c d
           low02 := fun c d => hVu.comm_low e d c
           up20 := fun c d => hVl.comm_up e' c d
           low21 := fun c d => hVl.comm_low e' d c
           pair := fun c d => by rw [← hP, hP']
           pair' := hpair' }⟩

end Exists



namespace RootCoordData

variable (D : RootCoordData φ Y)

@[expose] noncomputable def family : Fin 3 → Fin 3 → F → G :=
  ![![fun _ => 1, rootUp φ, D.x02],
    ![rootLow φ, fun _ => 1, D.x12],
    ![fun c => D.x20 (-(D.κ⁻¹ * c)), fun c => D.x21 (D.κ⁻¹ * c), fun _ => 1]]

@[simp] theorem family_01 : D.family 0 1 = rootUp φ := rfl
@[simp] theorem family_10 : D.family 1 0 = rootLow φ := rfl
@[simp] theorem family_02 : D.family 0 2 = D.x02 := rfl
@[simp] theorem family_12 : D.family 1 2 = D.x12 := rfl
@[simp] theorem family_21 (c : F) : D.family 2 1 c = D.x21 (D.κ⁻¹ * c) := rfl
@[simp] theorem family_20 (c : F) : D.family 2 0 c = D.x20 (-(D.κ⁻¹ * c)) := rfl

theorem rootUp_add (c d : F) : rootUp φ c * rootUp φ d = rootUp φ (c + d) := by
  rw [rootUp, rootUp, rootUp, ← map_mul, upperGL_add]

theorem rootLow_add (c d : F) : rootLow φ c * rootLow φ d = rootLow φ (c + d) := by
  rw [rootLow, rootLow, rootLow, ← map_mul, lowerGL_add]

theorem family_add (i j : Fin 3) (hij : i ≠ j) (c d : F) :
    D.family i j c * D.family i j d = D.family i j (c + d) := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
  · exact absurd rfl hij
  · rw [family_01, rootUp_add]
  · rw [family_02, D.add02]
  · rw [family_10, rootLow_add]
  · exact absurd rfl hij
  · rw [family_12, D.add12]
  · rw [family_20, family_20, family_20, ← D.add20]
    congr 1
    ring
  · rw [family_21, family_21, family_21, ← D.add21]
    congr 1
    ring
  · exact absurd rfl hij

theorem x02_zero : D.x02 0 = 1 := by
  have h := D.add02 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem x12_zero : D.x12 0 = 1 := by
  have h := D.add12 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem x21_zero : D.x21 0 = 1 := by
  have h := D.add21 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem x20_zero : D.x20 0 = 1 := by
  have h := D.add20 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem rootUp_zero : rootUp φ (0 : F) = 1 := by rw [rootUp, upperGL_zero, map_one]

theorem rootLow_zero : rootLow φ (0 : F) = 1 := by rw [rootLow, lowerGL_zero, map_one]

theorem family_zero (i j : Fin 3) : D.family i j 0 = 1 := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rfl
  · exact rootUp_zero
  · exact D.x02_zero
  · exact rootLow_zero
  · rfl
  · exact D.x12_zero
  · rw [family_20, mul_zero, neg_zero, D.x20_zero]
  · rw [family_21, mul_zero, D.x21_zero]
  · rfl

theorem family_neg (i j : Fin 3) (hij : i ≠ j) (c : F) :
    (D.family i j c)⁻¹ = D.family i j (-c) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, D.family_add i j hij, neg_add_cancel, D.family_zero]

theorem comm_eq_one_of {a b : G} (h : a * b = b * a) : ⁅a, b⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.mpr h

theorem comm_swap_eq {a b r : G} (h : ⁅a, b⁆ = r) : ⁅b, a⁆ = r⁻¹ := by
  rw [← h, commutatorElement_inv]

section Core

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
  (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
  (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)
  (hR : BrauerRootRelations φ Y)

include hR in
theorem c01_21 (c d : F) : ⁅D.family 0 1 c, D.family 2 1 d⁆ = 1 :=
  comm_eq_one_of (hR.commutes_X₁_X₂_one _ ((mem_rootX₁ φ).mpr ⟨c, rfl⟩) _ (D.mem21 _))

include hR in
theorem c01_02 (c d : F) : ⁅D.family 0 1 c, D.family 0 2 d⁆ = 1 :=
  comm_eq_one_of (hR.commutes_X₁_X₂_two _ ((mem_rootX₁ φ).mpr ⟨c, rfl⟩) _ (D.mem02 _))

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem c12_02 (c d : F) : ⁅D.family 1 2 c, D.family 0 2 d⁆ = 1 :=
  comm_eq_one_of (hR.commutes_12_02 hZ hZodd h2 hJ hY₁ hY₂ _ (D.mem12 _) _ (D.mem02 _))

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem c20_10 (c d : F) : ⁅D.family 2 0 c, D.family 1 0 d⁆ = 1 :=
  comm_eq_one_of (hR.commutes_20_10 hZ hZodd h2 hJ hY₁ hY₂ _ (D.mem20 _) _
    ((mem_rootX₂ φ).mpr ⟨d, rfl⟩))

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem c12_10 (c d : F) : ⁅D.family 1 2 c, D.family 1 0 d⁆ = 1 :=
  comm_eq_one_of (hR.commutes_12_10 hZ hZodd h2 hJ hY₁ hY₂ _ (D.mem12 _) _
    ((mem_rootX₂ φ).mpr ⟨d, rfl⟩))

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem c20_21 (c d : F) : ⁅D.family 2 0 c, D.family 2 1 d⁆ = 1 :=
  comm_eq_one_of (hR.commutes_20_21 hZ hZodd h2 hJ hY₁ hY₂ _ (D.mem20 _) _ (D.mem21 _))

theorem n01_12 (c d : F) : ⁅D.family 0 1 c, D.family 1 2 d⁆ = D.family 0 2 (c * d) :=
  D.up12 c d

theorem n10_02 (c d : F) : ⁅D.family 1 0 c, D.family 0 2 d⁆ = D.family 1 2 (c * d) :=
  D.low02 c d

theorem n02_21 (c d : F) : ⁅D.family 0 2 c, D.family 2 1 d⁆ = D.family 0 1 (c * d) := by
  rw [family_02, family_21, family_01, D.pair]
  congr 1
  field_simp [D.hκ]

theorem n12_20 (c d : F) : ⁅D.family 1 2 c, D.family 2 0 d⁆ = D.family 1 0 (c * d) := by
  rw [family_12, family_20, family_10, D.pair']
  congr 1
  field_simp [D.hκ]

theorem x20_inv (t : F) : (D.x20 t)⁻¹ = D.x20 (-t) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← D.add20, neg_add_cancel, D.x20_zero]

theorem x21_inv (t : F) : (D.x21 t)⁻¹ = D.x21 (-t) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← D.add21, neg_add_cancel, D.x21_zero]

theorem n21_10 (c d : F) : ⁅D.family 2 1 c, D.family 1 0 d⁆ = D.family 2 0 (c * d) := by
  rw [family_21, family_10, family_20, comm_swap_eq (D.low21 d (D.κ⁻¹ * c)), x20_inv]
  congr 1
  ring

theorem n20_01 (c d : F) : ⁅D.family 2 0 c, D.family 0 1 d⁆ = D.family 2 1 (c * d) := by
  rw [family_21, family_01, family_20, comm_swap_eq (D.up20 d (-(D.κ⁻¹ * c))), x21_inv]
  congr 1
  ring

theorem family_comm_self (i j : Fin 3) (hij : i ≠ j) (c d : F) :
    D.family i j c * D.family i j d = D.family i j d * D.family i j c := by
  rw [D.family_add i j hij, D.family_add i j hij, add_comm]

include hR in
theorem comm_row_01 (k l : Fin 3) (hkl : k ≠ l) (hex : ¬ (k = 1 ∧ l = 0)) (c d : F) :
    ⁅D.family 0 1 c, D.family k l d⁆ =
      if 1 = k then D.family 0 l (c * d) else if 0 = l then D.family k 1 (-(c * d)) else 1 := by
  fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte]
  · exact absurd rfl hkl
  · exact comm_eq_one_of (D.family_comm_self _ _ (by decide) c d)
  · exact D.c01_02 hR c d
  · exact absurd ⟨rfl, rfl⟩ hex
  · exact absurd rfl hkl
  · exact D.n01_12 c d
  · rw [comm_swap_eq (D.n20_01 d c), D.family_neg _ _ (by decide), mul_comm]
  · exact D.c01_21 hR c d
  · exact absurd rfl hkl

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem comm_row_02 (k l : Fin 3) (hkl : k ≠ l) (hex : ¬ (k = 2 ∧ l = 0)) (c d : F) :
    ⁅D.family 0 2 c, D.family k l d⁆ =
      if 2 = k then D.family 0 l (c * d) else if 0 = l then D.family k 2 (-(c * d)) else 1 := by
  fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte]
  · exact absurd rfl hkl
  · rw [comm_swap_eq (D.c01_02 hR d c), inv_one]
  · exact comm_eq_one_of (D.family_comm_self _ _ (by decide) c d)
  · rw [comm_swap_eq (D.n10_02 d c), D.family_neg _ _ (by decide), mul_comm]
  · exact absurd rfl hkl
  · rw [comm_swap_eq (D.c12_02 hZ hZodd h2 hJ hY₁ hY₂ hR d c), inv_one]
  · exact absurd ⟨rfl, rfl⟩ hex
  · exact D.n02_21 c d
  · exact absurd rfl hkl

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem comm_row_10 (k l : Fin 3) (hkl : k ≠ l) (hex : ¬ (k = 0 ∧ l = 1)) (c d : F) :
    ⁅D.family 1 0 c, D.family k l d⁆ =
      if 0 = k then D.family 1 l (c * d) else if 1 = l then D.family k 0 (-(c * d)) else 1 := by
  fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte]
  · exact absurd rfl hkl
  · exact absurd ⟨rfl, rfl⟩ hex
  · exact D.n10_02 c d
  · exact comm_eq_one_of (D.family_comm_self _ _ (by decide) c d)
  · exact absurd rfl hkl
  · rw [comm_swap_eq (D.c12_10 hZ hZodd h2 hJ hY₁ hY₂ hR d c), inv_one]
  · rw [comm_swap_eq (D.c20_10 hZ hZodd h2 hJ hY₁ hY₂ hR d c), inv_one]
  · rw [comm_swap_eq (D.n21_10 d c), D.family_neg _ _ (by decide), mul_comm]
  · exact absurd rfl hkl

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem comm_row_12 (k l : Fin 3) (hkl : k ≠ l) (hex : ¬ (k = 2 ∧ l = 1)) (c d : F) :
    ⁅D.family 1 2 c, D.family k l d⁆ =
      if 2 = k then D.family 1 l (c * d) else if 1 = l then D.family k 2 (-(c * d)) else 1 := by
  fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte]
  · exact absurd rfl hkl
  · rw [comm_swap_eq (D.n01_12 d c), D.family_neg _ _ (by decide), mul_comm]
  · exact D.c12_02 hZ hZodd h2 hJ hY₁ hY₂ hR c d
  · exact D.c12_10 hZ hZodd h2 hJ hY₁ hY₂ hR c d
  · exact absurd rfl hkl
  · exact comm_eq_one_of (D.family_comm_self _ _ (by decide) c d)
  · exact D.n12_20 c d
  · exact absurd ⟨rfl, rfl⟩ hex
  · exact absurd rfl hkl

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem comm_row_20 (k l : Fin 3) (hkl : k ≠ l) (hex : ¬ (k = 0 ∧ l = 2)) (c d : F) :
    ⁅D.family 2 0 c, D.family k l d⁆ =
      if 0 = k then D.family 2 l (c * d) else if 2 = l then D.family k 0 (-(c * d)) else 1 := by
  fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte]
  · exact absurd rfl hkl
  · exact D.n20_01 c d
  · exact absurd ⟨rfl, rfl⟩ hex
  · exact D.c20_10 hZ hZodd h2 hJ hY₁ hY₂ hR c d
  · exact absurd rfl hkl
  · rw [comm_swap_eq (D.n12_20 d c), D.family_neg _ _ (by decide), mul_comm]
  · exact comm_eq_one_of (D.family_comm_self _ _ (by decide) c d)
  · exact D.c20_21 hZ hZodd h2 hJ hY₁ hY₂ hR c d
  · exact absurd rfl hkl

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem comm_row_21 (k l : Fin 3) (hkl : k ≠ l) (hex : ¬ (k = 1 ∧ l = 2)) (c d : F) :
    ⁅D.family 2 1 c, D.family k l d⁆ =
      if 1 = k then D.family 2 l (c * d) else if 2 = l then D.family k 1 (-(c * d)) else 1 := by
  fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte]
  · exact absurd rfl hkl
  · rw [comm_swap_eq (D.c01_21 hR d c), inv_one]
  · rw [comm_swap_eq (D.n02_21 d c), D.family_neg _ _ (by decide), mul_comm]
  · exact D.n21_10 c d
  · exact absurd rfl hkl
  · exact absurd ⟨rfl, rfl⟩ hex
  · rw [comm_swap_eq (D.c20_21 hZ hZodd h2 hJ hY₁ hY₂ hR d c), inv_one]
  · exact comm_eq_one_of (D.family_comm_self _ _ (by decide) c d)
  · exact absurd rfl hkl

include hZ hZodd h2 hJ hY₁ hY₂ hR in
theorem isSteinbergFamily : IsSteinbergFamily D.family where
  add := D.family_add
  comm := by
    intro i j k l hij hkl hex c d
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij hex ⊢
    · exact absurd rfl hij
    · exact D.comm_row_01 hR k l hkl hex c d
    · exact D.comm_row_02 hZ hZodd h2 hJ hY₁ hY₂ hR k l hkl hex c d
    · exact D.comm_row_10 hZ hZodd h2 hJ hY₁ hY₂ hR k l hkl hex c d
    · exact absurd rfl hij
    · exact D.comm_row_12 hZ hZodd h2 hJ hY₁ hY₂ hR k l hkl hex c d
    · exact D.comm_row_20 hZ hZodd h2 hJ hY₁ hY₂ hR k l hkl hex c d
    · exact D.comm_row_21 hZ hZodd h2 hJ hY₁ hY₂ hR k l hkl hex c d
    · exact absurd rfl hij

end Core

end RootCoordData

section Recognition

variable [Finite F] (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
  (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
  (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)
  (hR : BrauerRootRelations φ Y)
include hZ hZodd h2 hJ hY₁ hY₂ hR

theorem nonempty_mulEquiv_psl_of_brauerRootRelations [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hcard : Nat.card G ≤ Nat.card (SL(3, F))) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  obtain ⟨D⟩ := nonempty_rootCoordData hZ hZodd h2 hJ hY₁ hY₂ hR
  have hx := D.isSteinbergFamily hZ hZodd h2 hJ hY₁ hY₂ hR
  have hne : D.family 0 1 1 ≠ 1 := by
    rw [RootCoordData.family_01]
    intro h
    have := rootUp_injective φ hZ (h.trans RootCoordData.rootUp_zero.symm)
    exact one_ne_zero this
  exact nonempty_mulEquiv_psl_of_steinbergFamily hnonab hx (by decide : (0 : Fin 3) ≠ 1) hne hcard

end Recognition

theorem statedClassicalModel_of_brauerRootRelations {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {F : Type} [Field F] [Finite F]
    {Z : Subgroup (GL (Fin 2) F)} [Z.Normal] {J : G}
    {φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z} {Y : G}
    (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
    (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
    (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)
    (hR : BrauerRootRelations φ Y) (hcard : Nat.card G ≤ Nat.card (SL(3, F)))
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_of_brauerRootRelations hZ hZodd h2 hJ hY₁ hY₂ hR hnonab hcard
  refine ⟨⟨hp, hf, by norm_num, by simp, by simp⟩, F, inferInstance, inferInstance, hF,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)⟩⟩


end CFSG.DesarguesianPlanes
