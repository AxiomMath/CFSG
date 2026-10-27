module

public import CFSG.LinearAlgebra.DesarguesianPlanes.LinearCentralizerData

public section

namespace CFSG.DesarguesianPlanes

open Matrix
open scoped commutatorElement

variable {G : Type*} [Group G] {F : Type} [Field F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)

noncomputable abbrev conjHom (g : G) : G →* G := (MulAut.conj g).toMonoidHom

theorem conjHom_apply (g x : G) : conjHom g x = g * x * g⁻¹ := rfl

theorem conjHom_mul (g h : G) : conjHom (g * h) = (conjHom g).comp (conjHom h) := by
  ext x
  simp only [conjHom_apply, MonoidHom.comp_apply, _root_.mul_inv_rev]
  group

theorem map_conjHom_map (g h : G) (H : Subgroup G) :
    (H.map (conjHom h)).map (conjHom g) = H.map (conjHom (g * h)) := by
  rw [Subgroup.map_map, conjHom_mul]

@[expose] noncomputable def upHom : Multiplicative F →* G where
  toFun c := rootUp φ (Multiplicative.toAdd c)
  map_one' := by simp only [toAdd_one, rootUp, upperGL_zero, map_one]
  map_mul' c d := by simp only [toAdd_mul, rootUp, ← upperGL_add, map_mul]

@[expose] noncomputable def lowHom : Multiplicative F →* G where
  toFun c := rootLow φ (Multiplicative.toAdd c)
  map_one' := by simp only [toAdd_one, rootLow, lowerGL_zero, map_one]
  map_mul' c d := by simp only [toAdd_mul, rootLow, ← lowerGL_add, map_mul]

theorem upHom_apply (c : Multiplicative F) : upHom φ c = rootUp φ (Multiplicative.toAdd c) := rfl

theorem lowHom_apply (c : Multiplicative F) : lowHom φ c = rootLow φ (Multiplicative.toAdd c) := rfl

noncomputable abbrev rootX₁ : Subgroup G := (upHom φ).range

noncomputable abbrev rootX₂ : Subgroup G := (lowHom φ).range

theorem mem_rootX₁ {x : G} : x ∈ rootX₁ φ ↔ ∃ c : F, rootUp φ c = x :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem mem_rootX₂ {x : G} : x ∈ rootX₂ φ ↔ ∃ c : F, rootLow φ c = x :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

variable (Y : G)

@[expose] noncomputable def rootSub : Fin 3 → Fin 3 → Subgroup G :=
  ![![⊥, rootX₁ φ, (rootX₂ φ).map (conjHom (Y ^ 2)⁻¹)],
    ![rootX₂ φ, ⊥, (rootX₁ φ).map (conjHom Y⁻¹)],
    ![(rootX₁ φ).map (conjHom (Y ^ 2)⁻¹), (rootX₂ φ).map (conjHom Y⁻¹), ⊥]]

@[simp] theorem rootSub_01 : rootSub φ Y 0 1 = rootX₁ φ := rfl
@[simp] theorem rootSub_10 : rootSub φ Y 1 0 = rootX₂ φ := rfl
@[simp] theorem rootSub_12 : rootSub φ Y 1 2 = (rootX₁ φ).map (conjHom Y⁻¹) := rfl
@[simp] theorem rootSub_21 : rootSub φ Y 2 1 = (rootX₂ φ).map (conjHom Y⁻¹) := rfl
@[simp] theorem rootSub_20 : rootSub φ Y 2 0 = (rootX₁ φ).map (conjHom (Y ^ 2)⁻¹) := rfl
@[simp] theorem rootSub_02 : rootSub φ Y 0 2 = (rootX₂ φ).map (conjHom (Y ^ 2)⁻¹) := rfl


@[expose] def Commutes (H K : Subgroup G) : Prop := ∀ a ∈ H, ∀ b ∈ K, a * b = b * a

@[expose] def CommIn (H K L : Subgroup G) : Prop := ∀ a ∈ H, ∀ b ∈ K, ⁅a, b⁆ ∈ L

@[expose] def NonTriv (H K : Subgroup G) : Prop := ∃ a ∈ H, ∃ b ∈ K, ⁅a, b⁆ ≠ 1

omit [Z.Normal] in
theorem Commutes.symm {H K : Subgroup G} (h : Commutes H K) : Commutes K H :=
  fun a ha b hb => (h b hb a ha).symm

omit [Z.Normal] in
theorem CommIn.symm {H K L : Subgroup G} (h : CommIn H K L) : CommIn K H L := by
  intro a ha b hb
  have := L.inv_mem (h b hb a ha)
  rwa [commutatorElement_inv] at this

omit [Z.Normal] in
theorem NonTriv.symm {H K : Subgroup G} (h : NonTriv H K) : NonTriv K H := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨b, hb, a, ha, fun h' => hab ?_⟩
  rw [← commutatorElement_inv, h', inv_one]

omit [Z.Normal] in
theorem Commutes.map {H K : Subgroup G} (h : Commutes H K) (f : G →* G) :
    Commutes (H.map f) (K.map f) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, h a ha b hb, map_mul]

omit [Z.Normal] in
theorem CommIn.map {H K L : Subgroup G} (h : CommIn H K L) (f : G →* G) :
    CommIn (H.map f) (K.map f) (L.map f) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_commutatorElement]
  exact Subgroup.mem_map_of_mem f (h a ha b hb)

omit [Z.Normal] in
theorem NonTriv.map {H K : Subgroup G} (h : NonTriv H K) (g : G) :
    NonTriv (H.map (conjHom g)) (K.map (conjHom g)) := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨_, Subgroup.mem_map_of_mem _ ha, _, Subgroup.mem_map_of_mem _ hb, ?_⟩
  rw [← map_commutatorElement]
  intro h'
  apply hab
  have := congrArg (conjHom g⁻¹) h'
  rwa [map_one, ← MonoidHom.comp_apply, ← conjHom_mul, inv_mul_cancel, conjHom_apply, one_mul,
    inv_one, mul_one] at this

noncomputable abbrev invJ₁ : G := linearCentralizerHom φ (diagGL 1 (-1))

noncomputable abbrev invJ₂ : G := linearCentralizerHom φ (diagGL (-1) 1)

noncomputable abbrev swapW : G := linearCentralizerHom φ swapGL

@[expose] def IsTorus (g : G) : Prop := J * g = g * J ∧ invJ₁ φ * g = g * invJ₁ φ

theorem isTorus_diag (a b : Fˣ) : IsTorus φ (linearCentralizerHom φ (diagGL a b)) := by
  refine ⟨linearCentralizerHom_commute φ _, ?_⟩
  rw [invJ₁, ← map_mul, ← map_mul, diagGL_mul, diagGL_mul, mul_comm (1 : Fˣ), mul_comm (-1 : Fˣ)]

theorem IsTorus.mul {g h : G} (hg : IsTorus φ g) (hh : IsTorus φ h) : IsTorus φ (g * h) := by
  refine ⟨?_, ?_⟩
  · rw [← mul_assoc, hg.1, mul_assoc, hh.1, mul_assoc]
  · rw [← mul_assoc, hg.2, mul_assoc, hh.2, mul_assoc]

theorem IsTorus.inv {g : G} (hg : IsTorus φ g) : IsTorus φ g⁻¹ := by
  refine ⟨?_, ?_⟩
  · rw [mul_inv_eq_iff_eq_mul, mul_assoc, hg.1, ← mul_assoc, inv_mul_cancel, one_mul]
  · rw [mul_inv_eq_iff_eq_mul, mul_assoc, hg.2, ← mul_assoc, inv_mul_cancel, one_mul]

section Structure

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
  (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include hZ hZodd h2 in
theorem isTorus_iff (g : G) :
    IsTorus φ g ↔ ∃ a b : Fˣ, g = linearCentralizerHom φ (diagGL a b) := by
  constructor
  · rintro ⟨h1, h2'⟩
    exact exists_diag_of_commute φ hZ hZodd h2 h1 h2'
  · rintro ⟨a, b, rfl⟩
    exact isTorus_diag φ a b

include hZ hZodd h2 hJ in
theorem invJ₂_eq : invJ₂ φ = J * invJ₁ φ := by
  have h := linearCentralizerHom_neg_one φ hZ hZodd h2 hJ
  calc invJ₂ φ = linearCentralizerHom φ (-1) * invJ₁ φ := by
        rw [invJ₂, invJ₁, ← map_mul, neg_one_eq_diagGL, diagGL_mul]
        congr 2 <;> simp
    _ = J * invJ₁ φ := by rw [h]

include hJ in
theorem J_mul_self : J * J = 1 := by
  rw [← pow_two, ← hJ, pow_orderOf_eq_one]

theorem invJ₁_mul_self : invJ₁ φ * invJ₁ φ = 1 := by
  rw [invJ₁, ← map_mul, diagGL_mul]
  simp [diagGL_one_one]

theorem swapW_mul_self : swapW φ * swapW φ = 1 := by
  rw [swapW, ← map_mul, swapGL_mul_self, map_one]

theorem swapW_inv : (swapW φ)⁻¹ = swapW φ :=
  inv_eq_of_mul_eq_one_right (swapW_mul_self φ)

theorem swapW_conj_invJ₁ : swapW φ * invJ₁ φ * (swapW φ)⁻¹ = invJ₂ φ := by
  rw [swapW_inv, swapW, invJ₁, invJ₂, ← map_mul, ← map_mul, swapGL_mul_diagGL, mul_assoc,
    swapGL_mul_self, mul_one]

theorem swapW_conj_J : swapW φ * J * (swapW φ)⁻¹ = J := by
  rw [← linearCentralizerHom_commute φ swapGL, mul_assoc, mul_inv_cancel, mul_one]


theorem J_commute_invJ₁ : J * invJ₁ φ = invJ₁ φ * J := linearCentralizerHom_commute φ _

include hZ hZodd h2 hJ in
theorem invJ₂_mul_invJ₁ : invJ₂ φ * invJ₁ φ = J := by
  rw [invJ₂_eq φ hZ hZodd h2 hJ, mul_assoc, invJ₁_mul_self, mul_one]

include hZ hZodd h2 hJ in
theorem J_mul_invJ₂ : J * invJ₂ φ = invJ₁ φ := by
  rw [invJ₂_eq φ hZ hZodd h2 hJ, ← mul_assoc, J_mul_self hJ, one_mul]

variable {Y}
variable (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)

theorem conj_eq_of_inv_conj_eq {Y a b : G} (h : Y⁻¹ * a * Y = b) : Y * b * Y⁻¹ = a := by
  rw [← h]
  group

theorem commute_of_inv_conj_eq_self {x a : G} (h : x⁻¹ * a * x = a) : a * x = x * a := by
  calc a * x = x * (x⁻¹ * a * x) := by group
    _ = x * a := by rw [h]

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem conj_Y_invJ₂ : Y⁻¹ * invJ₂ φ * Y = J := by
  have hJ₂ := invJ₂_eq φ hZ hZodd h2 hJ
  calc Y⁻¹ * invJ₂ φ * Y = (Y⁻¹ * J * Y) * (Y⁻¹ * invJ₁ φ * Y) := by rw [hJ₂]; group
    _ = invJ₁ φ * invJ₂ φ := by rw [hY₁, hY₂]
    _ = invJ₁ φ * (J * invJ₁ φ) := by rw [hJ₂]
    _ = J := by rw [J_commute_invJ₁, ← mul_assoc, invJ₁_mul_self, one_mul]

theorem commute_conj {a g : G} (x : G) (h : a * g = g * a) :
    (x * a * x⁻¹) * (x * g * x⁻¹) = (x * g * x⁻¹) * (x * a * x⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc a, h, mul_assoc]

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem IsTorus.conj_inv_Y {g : G} (hg : IsTorus φ g) : IsTorus φ (Y⁻¹ * g * Y) := by
  have e1 := commute_conj Y⁻¹ hg.1
  have e2 := commute_conj Y⁻¹ hg.2
  rw [inv_inv, hY₁] at e1
  rw [inv_inv, hY₂] at e2
  refine ⟨?_, e1⟩
  rw [← invJ₂_mul_invJ₁ φ hZ hZodd h2 hJ, mul_assoc, e1, ← mul_assoc, e2, mul_assoc]

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem IsTorus.conj_Y {g : G} (hg : IsTorus φ g) : IsTorus φ (Y * g * Y⁻¹) := by
  have hJ₂ : Y * J * Y⁻¹ = invJ₂ φ := conj_eq_of_inv_conj_eq (conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂)
  have hJ' : Y * invJ₁ φ * Y⁻¹ = J := conj_eq_of_inv_conj_eq hY₁
  have e1 := commute_conj Y hg.1
  have e2 := commute_conj Y hg.2
  rw [hJ₂] at e1
  rw [hJ'] at e2
  refine ⟨e2, ?_⟩
  rw [← J_mul_invJ₂ φ hZ hZodd h2 hJ, mul_assoc, e1, ← mul_assoc, e2, mul_assoc]

include hZ hZodd h2 hJ in
theorem IsTorus.conj_W {g : G} (hg : IsTorus φ g) : IsTorus φ (swapW φ * g * (swapW φ)⁻¹) := by
  have e1 := commute_conj (swapW φ) hg.1
  have e2 := commute_conj (swapW φ) hg.2
  rw [swapW_conj_J] at e1
  rw [swapW_conj_invJ₁] at e2
  refine ⟨e1, ?_⟩
  rw [← J_mul_invJ₂ φ hZ hZodd h2 hJ, mul_assoc, e2, ← mul_assoc, e1, mul_assoc]

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem isTorus_Y_cube : IsTorus φ (Y ^ 3) := by
  have hY₃ := conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂
  have hJ3 : (Y ^ 3)⁻¹ * J * Y ^ 3 = J := by
    calc (Y ^ 3)⁻¹ * J * Y ^ 3 = Y⁻¹ * (Y⁻¹ * (Y⁻¹ * J * Y) * Y) * Y := by
          simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc]
      _ = J := by rw [hY₁, hY₂, hY₃]
  have hJ₁3 : (Y ^ 3)⁻¹ * invJ₁ φ * Y ^ 3 = invJ₁ φ := by
    calc (Y ^ 3)⁻¹ * invJ₁ φ * Y ^ 3 = Y⁻¹ * (Y⁻¹ * (Y⁻¹ * invJ₁ φ * Y) * Y) * Y := by
          simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc]
      _ = invJ₁ φ := by rw [hY₂, hY₃, hY₁]
  exact ⟨commute_of_inv_conj_eq_self hJ3, commute_of_inv_conj_eq_self hJ₁3⟩

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem isTorus_Y_sq_W : IsTorus φ (Y ^ 2 * swapW φ * Y⁻¹ * (swapW φ)⁻¹) := by
  have hY₃ := conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂
  have hY₁' : Y * invJ₁ φ * Y⁻¹ = J := conj_eq_of_inv_conj_eq hY₁
  have hY₂' : Y * invJ₂ φ * Y⁻¹ = invJ₁ φ := conj_eq_of_inv_conj_eq hY₂
  have hY₃' : Y * J * Y⁻¹ = invJ₂ φ := conj_eq_of_inv_conj_eq hY₃
  have hW1 : swapW φ * J * (swapW φ)⁻¹ = J := swapW_conj_J φ
  have hW1' : (swapW φ)⁻¹ * J * swapW φ = J := by
    have := hW1
    rw [swapW_inv] at this ⊢
    exact this
  have hW2 : swapW φ * invJ₁ φ * (swapW φ)⁻¹ = invJ₂ φ := swapW_conj_invJ₁ φ
  have hW2' : (swapW φ)⁻¹ * invJ₁ φ * swapW φ = invJ₂ φ := by
    have := hW2
    rw [swapW_inv] at this ⊢
    exact this
  set X := Y ^ 2 * swapW φ * Y⁻¹ * (swapW φ)⁻¹ with hX
  have hconjJ : X⁻¹ * J * X = J := by
    calc X⁻¹ * J * X = swapW φ * (Y * ((swapW φ)⁻¹ * ((Y ^ 2)⁻¹ * J * Y ^ 2) * swapW φ) * Y⁻¹) *
          (swapW φ)⁻¹ := by rw [hX]; group
      _ = J := by
        rw [show (Y ^ 2)⁻¹ * J * Y ^ 2 = Y⁻¹ * (Y⁻¹ * J * Y) * Y by
          simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc], hY₁, hY₂, ← hW2',
          show (swapW φ)⁻¹ * ((swapW φ)⁻¹ * invJ₁ φ * swapW φ) * swapW φ = invJ₁ φ by
            rw [swapW_inv]
            calc swapW φ * (swapW φ * invJ₁ φ * swapW φ) * swapW φ =
                (swapW φ * swapW φ) * invJ₁ φ * (swapW φ * swapW φ) := by group
              _ = invJ₁ φ := by rw [swapW_mul_self]; group,
          hY₁', hW1]
  have hconj₁ : X⁻¹ * invJ₁ φ * X = invJ₁ φ := by
    calc X⁻¹ * invJ₁ φ * X = swapW φ * (Y * ((swapW φ)⁻¹ * ((Y ^ 2)⁻¹ * invJ₁ φ * Y ^ 2) *
          swapW φ) * Y⁻¹) * (swapW φ)⁻¹ := by rw [hX]; group
      _ = invJ₁ φ := by
        rw [show (Y ^ 2)⁻¹ * invJ₁ φ * Y ^ 2 = Y⁻¹ * (Y⁻¹ * invJ₁ φ * Y) * Y by
          simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc], hY₂, hY₃,
          hW1', hY₃', ← hW2,
          show swapW φ * (swapW φ * invJ₁ φ * (swapW φ)⁻¹) * (swapW φ)⁻¹ = invJ₁ φ by
            rw [swapW_inv]
            calc swapW φ * (swapW φ * invJ₁ φ * swapW φ) * swapW φ =
                (swapW φ * swapW φ) * invJ₁ φ * (swapW φ * swapW φ) := by group
              _ = invJ₁ φ := by rw [swapW_mul_self]; group]
  exact ⟨commute_of_inv_conj_eq_self hconjJ, commute_of_inv_conj_eq_self hconj₁⟩

end Structure

end CFSG.DesarguesianPlanes
