module

public import CFSG.LieType.Chevalley.G2FieldFourCoverLifts
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public noncomputable section

namespace CFSG.LieType.Chevalley.G2FieldFour

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ExceptionalCover
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K : Type} [Field K] {E : Type*} [Group E] {η : E →* adjointGroup Tag.G2 K}

theorem conj_mem_sup {N H H' : Subgroup E} {x : E} (hH : ∀ h ∈ H, x * h * x⁻¹ ∈ N)
    (hH' : ∀ h ∈ H', x * h * x⁻¹ ∈ N) : ∀ h ∈ H ⊔ H', x * h * x⁻¹ ∈ N := by
  have hle : H ⊔ H' ≤ N.comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun h hh => by simpa using hH h hh) (fun h hh => by simpa using hH' h hh)
  intro h hh
  simpa using hle hh

namespace RootLifts

variable (L : RootLifts η)

theorem A_zero
    {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) : L.A d 0 = 1 := by
  have h := L.A_add d hd 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

@[expose] def liftHom
    {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) : Multiplicative K →* E where
  toFun c := L.A d c.toAdd
  map_one' := L.A_zero hd
  map_mul' c c' := L.A_add d hd c.toAdd c'.toAdd

@[expose] def liftGroup
    {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) : Subgroup E :=
  (L.liftHom hd).range

theorem mem_liftGroup
    {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) {e : E} :
    e ∈ L.liftGroup hd ↔ ∃ c, L.A d c = e := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.toAdd, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

theorem A_mem_liftGroup
    {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) (c : K) :
    L.A d c ∈ L.liftGroup hd :=
  (L.mem_liftGroup hd).2 ⟨c, rfl⟩

theorem card_liftGroup_le
    [Finite K] {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) :
    Nat.card (L.liftGroup hd) ≤ Nat.card K := by
  have h := Nat.card_le_card_of_surjective _ (L.liftHom hd).rangeRestrict_surjective
  rwa [Nat.card_congr Multiplicative.toAdd] at h

@[expose] def subM : Subgroup E :=
  L.liftGroup rootU_mem ⊔ (L.liftGroup rootV_mem ⊔ (L.liftGroup rootB_mem ⊔ L.liftGroup rootC_mem))

@[expose] def subN : Subgroup E :=
  L.liftGroup rootA_mem ⊔ L.subM

@[expose] def subP : Subgroup E :=
  L.liftGroup rootR_mem ⊔ L.subN

theorem le_subM_u
    : L.liftGroup rootU_mem ≤ L.subM := le_sup_left

theorem le_subM_v
    : L.liftGroup rootV_mem ≤ L.subM := le_sup_left.trans le_sup_right

theorem le_subM_b
    : L.liftGroup rootB_mem ≤ L.subM :=
  le_sup_left.trans (le_sup_right.trans le_sup_right)

theorem le_subM_c
    : L.liftGroup rootC_mem ≤ L.subM :=
  le_sup_right.trans (le_sup_right.trans le_sup_right)

theorem subM_le_subN
    : L.subM ≤ L.subN := le_sup_right

theorem le_subN_a
    : L.liftGroup rootA_mem ≤ L.subN := le_sup_left

theorem subN_le_subP
    : L.subN ≤ L.subP := le_sup_right

theorem le_subP_r
    : L.liftGroup rootR_mem ≤ L.subP := le_sup_left

end RootLifts

section Counting

variable
    [CharP K 2] {ω : Kˣ} (hω : orderOf ω = 3) (hη : Function.Surjective η)
  (hker : ∀ z, η z = 1 → z ∈ Subgroup.center E)
  (hab : ∀ d ∈ posRoots, ∀ (e e' : E) (c c' : K), η e = rootX d c → η e' = rootX d c' →
    e * e' = e' * e) (L : RootLifts η)
include hω hη hker hab

open RootLifts

theorem card_subM_le
    [Finite E] [Finite K] : Nat.card L.subM ≤ Nat.card K ^ 4 := by
  have hq := fun {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) => L.card_liftGroup_le hd
  have hbc : Nat.card (L.liftGroup rootB_mem ⊔ L.liftGroup rootC_mem : Subgroup E) ≤
      Nat.card K * Nat.card K := by
    refine (LinearCover.card_sup_le_of_conj_mem (hq rootB_mem) fun x hx h hh => ?_).trans
      (Nat.mul_le_mul_left _ (hq rootC_mem))
    obtain ⟨s, rfl⟩ := (L.mem_liftGroup rootB_mem).1 hx
    obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootC_mem).1 hh
    rw [conj_eq_of_commute (comm_bc hω hη hker hab (L.map_A _ rootB_mem s)
      (L.map_A _ rootC_mem t))]
    exact L.A_mem_liftGroup rootC_mem t
  have hvbc : Nat.card (L.liftGroup rootV_mem ⊔ (L.liftGroup rootB_mem ⊔
      L.liftGroup rootC_mem) : Subgroup E) ≤ Nat.card K * (Nat.card K * Nat.card K) := by
    refine (LinearCover.card_sup_le_of_conj_mem (hq rootV_mem) fun x hx => ?_).trans
      (Nat.mul_le_mul_left _ hbc)
    obtain ⟨s, rfl⟩ := (L.mem_liftGroup rootV_mem).1 hx
    refine conj_mem_sup (fun h hh => ?_) (fun h hh => ?_)
    · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootB_mem).1 hh
      rw [conj_eq_of_commute (comm_vb hω hη hker (L.map_A _ rootV_mem s)
        (L.map_A _ rootB_mem t))]
      exact Subgroup.mem_sup_left (L.A_mem_liftGroup rootB_mem t)
    · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootC_mem).1 hh
      rw [conj_eq_of_commute (comm_vc hω hη hker (L.map_A _ rootV_mem s)
        (L.map_A _ rootC_mem t))]
      exact Subgroup.mem_sup_right (L.A_mem_liftGroup rootC_mem t)
  have h := (LinearCover.card_sup_le_of_conj_mem (hq rootU_mem) fun x hx => ?_).trans
    (Nat.mul_le_mul_left _ hvbc)
  · calc Nat.card L.subM ≤ Nat.card K * (Nat.card K * (Nat.card K * Nat.card K)) := h
      _ = Nat.card K ^ 4 := by ring
  obtain ⟨s, rfl⟩ := (L.mem_liftGroup rootU_mem).1 hx
  refine conj_mem_sup (fun h hh => ?_) (conj_mem_sup (fun h hh => ?_) (fun h hh => ?_))
  · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootV_mem).1 hh
    rw [conj_eq_commutatorElement_mul', commutator_A_uv hω hη hker hab L]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_right
      (L.A_mem_liftGroup rootC_mem _))) (Subgroup.mem_sup_left (L.A_mem_liftGroup rootV_mem t))
  · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootB_mem).1 hh
    rw [conj_eq_of_commute (comm_ub hω hη hker (L.map_A _ rootU_mem s)
      (L.map_A _ rootB_mem t))]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (L.A_mem_liftGroup rootB_mem t))
  · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootC_mem).1 hh
    rw [conj_eq_of_commute (comm_uc hω hη hker (L.map_A _ rootU_mem s)
      (L.map_A _ rootC_mem t))]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (L.A_mem_liftGroup rootC_mem t))

theorem subM_injOn
    [Finite E] [Finite K] {m m' : E} (hm : m ∈ L.subM) (hm' : m' ∈ L.subM)
    (h : η m = η m') : m = m' := by
  let f : L.subM → L.subM.map η := fun m => ⟨η m, Subgroup.mem_map_of_mem η m.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  let α : Fin 4 → Fin Tag.G2.rank → ℤ := ![rootU, rootV, rootB, rootC]
  have hα : Function.Injective α := by decide +kernel
  have hpos : ∀ i, IsRoot .G2 (α i) ∧ 0 < height (α i) := by
    intro i
    fin_cases i
    exacts [mem_posRoots.1 rootU_mem, mem_posRoots.1 rootV_mem, mem_posRoots.1 rootB_mem,
      mem_posRoots.1 rootC_mem]
  have hprod := (positive_root_product_injectivity .G2 K α hα hpos).2
  have hmemW : ∀ c : Fin 4 → K, L.A rootU (c 0) * L.A rootV (c 1) * L.A rootB (c 2) *
      L.A rootC (c 3) ∈ L.subM := fun c =>
    mul_mem (mul_mem (mul_mem (L.le_subM_u (L.A_mem_liftGroup _ _))
      (L.le_subM_v (L.A_mem_liftGroup _ _))) (L.le_subM_b (L.A_mem_liftGroup _ _)))
      (L.le_subM_c (L.A_mem_liftGroup _ _))
  let g : (Fin 4 → K) → L.subM.map η := fun c => ⟨η (L.A rootU (c 0) * L.A rootV (c 1) *
    L.A rootB (c 2) * L.A rootC (c 3)), Subgroup.mem_map_of_mem η (hmemW c)⟩
  have hg : Function.Injective g := by
    intro c c' hcc'
    apply hprod
    have := congrArg (fun y : L.subM.map η => ((y : adjointGroup Tag.G2 K) : ModGL Tag.G2 K))
      hcc'
    simpa [g, α, L.map_A _ rootU_mem, L.map_A _ rootV_mem, L.map_A _ rootB_mem,
      L.map_A _ rootC_mem, coe_rootX, List.ofFn_succ, mul_assoc] using this
  have hcard : Nat.card L.subM ≤ Nat.card (L.subM.map η) :=
    calc Nat.card L.subM ≤ Nat.card K ^ 4 := card_subM_le hω hη hker hab L
      _ = Nat.card (Fin 4 → K) := by rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 4),
          Fintype.card_fin]
      _ ≤ Nat.card (L.subM.map η) := Nat.card_le_card_of_injective g hg
  have hinj := (hf.bijective_of_nat_card_le hcard).1
  exact congrArg Subtype.val (@hinj ⟨m, hm⟩ ⟨m', hm'⟩ (Subtype.ext h))

theorem conj_A_a_mem_subM
    (x : K) :
    ∀ m ∈ L.subM, L.A rootA x * m * (L.A rootA x)⁻¹ ∈ L.subM := by
  refine conj_mem_sup (fun h hh => ?_) (conj_mem_sup (fun h hh => ?_)
    (conj_mem_sup (fun h hh => ?_) (fun h hh => ?_)))
  · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootU_mem).1 hh
    rw [conj_eq_of_commute (comm_au hω hη hker (L.map_A _ rootA_mem x) (L.map_A _ rootU_mem t))]
    exact L.le_subM_u (L.A_mem_liftGroup _ t)
  · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootV_mem).1 hh
    rw [conj_eq_of_commute (comm_av hω hη hker (L.map_A _ rootA_mem x) (L.map_A _ rootV_mem t))]
    exact L.le_subM_v (L.A_mem_liftGroup _ t)
  · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootB_mem).1 hh
    rw [conj_eq_commutatorElement_mul', commutator_A_ab hω hη hker hab L]
    exact mul_mem (L.le_subM_c (L.A_mem_liftGroup _ _)) (L.le_subM_b (L.A_mem_liftGroup _ t))
  · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootC_mem).1 hh
    rw [conj_eq_of_commute (comm_ac hω hη hker hab (L.map_A _ rootA_mem x)
      (L.map_A _ rootC_mem t))]
    exact L.le_subM_c (L.A_mem_liftGroup _ t)

theorem commutator_A_ar
    [Finite E] [Finite K] (x s : K) :
    ⁅L.A rootA x, L.A rootR s⁆ = L.A rootU (x * s) * L.A rootV (x * s ^ 2) *
      L.A rootB (x * s ^ 3) * L.A rootC (x ^ 2 * s ^ 3) := by
  set W : K → E := fun x => L.A rootU (x * s) * L.A rootV (x * s ^ 2) *
    L.A rootB (x * s ^ 3) * L.A rootC (x ^ 2 * s ^ 3) with hWdef
  have hWM : ∀ x, W x ∈ L.subM := fun x =>
    mul_mem (mul_mem (mul_mem (L.le_subM_u (L.A_mem_liftGroup _ _))
      (L.le_subM_v (L.A_mem_liftGroup _ _))) (L.le_subM_b (L.A_mem_liftGroup _ _)))
      (L.le_subM_c (L.A_mem_liftGroup _ _))
  have hηW : ∀ x, η (W x) = ⁅rootX rootA x, rootX rootR s⁆ := fun x => by
    rw [commutator_rootX_ar, hWdef]
    simp only [map_mul, L.map_A _ rootU_mem, L.map_A _ rootV_mem, L.map_A _ rootB_mem,
      L.map_A _ rootC_mem]
  set κ : K → E := fun x => (W x)⁻¹ * ⁅L.A rootA x, L.A rootR s⁆ with hκdef
  have hκc : ∀ x, κ x ∈ Subgroup.center E := fun x => hker _ (by
    rw [hκdef]
    simp only []
    rw [map_mul, map_inv, hηW, map_commutatorElement, L.map_A _ rootA_mem, L.map_A _ rootR_mem,
      inv_mul_cancel])
  have hcomm_eq : ∀ x, ⁅L.A rootA x, L.A rootR s⁆ = W x * κ x := fun x => by
    rw [hκdef]
    simp only [mul_inv_cancel_left]
  have hWadd : ∀ x x', L.A rootA x * W x' * (L.A rootA x)⁻¹ * W x = W (x + x') := fun x x' => by
    refine subM_injOn hω hη hker hab L (mul_mem (conj_A_a_mem_subM hω hη hker hab L x _ (hWM x'))
      (hWM x)) (hWM _) ?_
    rw [map_mul, map_mul, map_mul, map_inv, hηW, hηW, hηW, L.map_A _ rootA_mem, rootX_add,
      commutatorElement_mul_left']
  have hκadd : ∀ x x', κ (x + x') = κ x * κ x' := fun x x' => by
    have hz : ∀ g : E, κ x' * g = g * κ x' := fun g => (Subgroup.mem_center_iff.1 (hκc x') g).symm
    have h1 : ⁅L.A rootA (x + x'), L.A rootR s⁆ = W (x + x') * (κ x' * κ x) := by
      rw [L.A_add _ rootA_mem, commutatorElement_mul_left', hcomm_eq x', hcomm_eq x, ← hWadd]
      calc L.A rootA x * (W x' * κ x') * (L.A rootA x)⁻¹ * (W x * κ x)
          = L.A rootA x * W x' * (κ x' * (L.A rootA x)⁻¹) * (W x * κ x) := by group
        _ = L.A rootA x * W x' * ((L.A rootA x)⁻¹ * κ x') * (W x * κ x) := by rw [hz]
        _ = L.A rootA x * W x' * (L.A rootA x)⁻¹ * (κ x' * W x) * κ x := by group
        _ = L.A rootA x * W x' * (L.A rootA x)⁻¹ * (W x * κ x') * κ x := by rw [hz]
        _ = L.A rootA x * W x' * (L.A rootA x)⁻¹ * W x * (κ x' * κ x) := by group
    have h2 : κ (x + x') = κ x' * κ x := by
      rw [hκdef]
      simp only []
      rw [h1, inv_mul_cancel_left]
    rw [h2, hz]
  obtain ⟨g, hg⟩ := hη (torusX (torusPow ω ![1, 2]))
  have ha : (rootChar K rootA (torusPow ω ![1, 2]) : K) ≠ 1 :=
    rootChar_torusPow_ne_one hω (by decide +kernel)
  have hr : rootChar K rootR (torusPow ω ![1, 2]) = 1 :=
    rootChar_torusPow_eq_one hω (by decide +kernel)
  have hu : rootChar K rootU (torusPow ω ![1, 2]) = rootChar K rootA (torusPow ω ![1, 2]) :=
    rootChar_torusPow_eq hω (by decide +kernel)
  have hv : rootChar K rootV (torusPow ω ![1, 2]) = rootChar K rootA (torusPow ω ![1, 2]) :=
    rootChar_torusPow_eq hω (by decide +kernel)
  have hb : rootChar K rootB (torusPow ω ![1, 2]) = rootChar K rootA (torusPow ω ![1, 2]) :=
    rootChar_torusPow_eq hω (by decide +kernel)
  have hc : (rootChar K rootC (torusPow ω ![1, 2]) : K) =
      (rootChar K rootA (torusPow ω ![1, 2]) : K) ^ 2 :=
    rootChar_torusPow_eq_sq hω (by decide +kernel)
  set ρ : K := (rootChar K rootA (torusPow ω ![1, 2]) : K) with hρ
  have hgW : ∀ x, g * W x * g⁻¹ = W (ρ * x) := fun x => by
    rw [hWdef]
    simp only []
    rw [show g * (L.A rootU (x * s) * L.A rootV (x * s ^ 2) * L.A rootB (x * s ^ 3) *
        L.A rootC (x ^ 2 * s ^ 3)) * g⁻¹ = g * L.A rootU (x * s) * g⁻¹ *
        (g * L.A rootV (x * s ^ 2) * g⁻¹) * (g * L.A rootB (x * s ^ 3) * g⁻¹) *
        (g * L.A rootC (x ^ 2 * s ^ 3) * g⁻¹) by group,
      L.A_conj _ rootU_mem _ g hg, L.A_conj _ rootV_mem _ g hg, L.A_conj _ rootB_mem _ g hg,
      L.A_conj _ rootC_mem _ g hg, hu, hv, hb, hc, ← hρ, mul_assoc ρ x s, mul_assoc ρ x (s ^ 2),
      mul_assoc ρ x (s ^ 3), mul_pow, mul_assoc (ρ ^ 2)]
  have hκinv : ∀ x, κ (ρ * x) = κ x := fun x => by
    have h1 : g * κ x * g⁻¹ = κ x := by
      rw [Subgroup.mem_center_iff.1 (hκc x) g, mul_inv_cancel_right]
    rw [← h1, hκdef]
    simp only []
    rw [show g * ((W x)⁻¹ * ⁅L.A rootA x, L.A rootR s⁆) * g⁻¹ =
        (g * W x * g⁻¹)⁻¹ * (g * ⁅L.A rootA x, L.A rootR s⁆ * g⁻¹) by group, hgW,
      LinearCover.conj_commutatorElement_eq, L.A_conj _ rootA_mem _ g hg,
      L.A_conj _ rootR_mem _ g hg, hr, Units.val_one, one_mul]
  have hκ1 := LinearCover.eq_one_of_map_add_of_map_mul hκadd ha hκinv x
  rw [hcomm_eq x, hκ1, mul_one]

theorem card_subN_le
    [Finite E] [Finite K] : Nat.card L.subN ≤ Nat.card K ^ 5 := by
  have h := LinearCover.card_sup_le_of_conj_mem (L.card_liftGroup_le rootA_mem)
    (H := L.subM) fun x hx => by
      obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootA_mem).1 hx
      exact conj_A_a_mem_subM hω hη hker hab L t
  calc Nat.card L.subN ≤ Nat.card K * Nat.card L.subM := h
    _ ≤ Nat.card K * Nat.card K ^ 4 := Nat.mul_le_mul_left _ (card_subM_le hω hη hker hab L)
    _ = Nat.card K ^ 5 := by ring

theorem conj_A_r_mem_subN
    [Finite E] [Finite K] (s : K) :
    ∀ n ∈ L.subN, L.A rootR s * n * (L.A rootR s)⁻¹ ∈ L.subN := by
  refine conj_mem_sup (fun h hh => ?_) fun h hh => L.subM_le_subN ?_
  · obtain ⟨x, rfl⟩ := (L.mem_liftGroup rootA_mem).1 hh
    rw [conj_eq_commutatorElement_mul', ← commutatorElement_inv,
      commutator_A_ar hω hη hker hab L]
    refine mul_mem (inv_mem (L.subM_le_subN ?_)) (L.le_subN_a (L.A_mem_liftGroup _ x))
    exact mul_mem (mul_mem (mul_mem (L.le_subM_u (L.A_mem_liftGroup _ _))
      (L.le_subM_v (L.A_mem_liftGroup _ _))) (L.le_subM_b (L.A_mem_liftGroup _ _)))
      (L.le_subM_c (L.A_mem_liftGroup _ _))
  · revert h hh
    refine conj_mem_sup (fun h hh => ?_) (conj_mem_sup (fun h hh => ?_)
      (conj_mem_sup (fun h hh => ?_) (fun h hh => ?_)))
    · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootU_mem).1 hh
      rw [conj_eq_commutatorElement_mul', commutator_A_ru hω hη hker hab L]
      exact mul_mem (mul_mem (L.le_subM_c (L.A_mem_liftGroup _ _))
        (L.le_subM_b (L.A_mem_liftGroup _ _))) (L.le_subM_u (L.A_mem_liftGroup _ t))
    · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootV_mem).1 hh
      rw [conj_eq_commutatorElement_mul', commutator_A_rv hω hη hker hab L]
      exact mul_mem (L.le_subM_b (L.A_mem_liftGroup _ _)) (L.le_subM_v (L.A_mem_liftGroup _ t))
    · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootB_mem).1 hh
      rw [conj_eq_of_commute (comm_rb hω hη hker (L.map_A _ rootR_mem s)
        (L.map_A _ rootB_mem t))]
      exact L.le_subM_b (L.A_mem_liftGroup _ t)
    · obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootC_mem).1 hh
      rw [conj_eq_of_commute (comm_rc hω hη hker (L.map_A _ rootR_mem s)
        (L.map_A _ rootC_mem t))]
      exact L.le_subM_c (L.A_mem_liftGroup _ t)

theorem card_subP_le
    [Finite E] [Finite K] : Nat.card L.subP ≤ Nat.card K ^ 6 := by
  have h := LinearCover.card_sup_le_of_conj_mem (L.card_liftGroup_le rootR_mem)
    (H := L.subN) fun x hx => by
      obtain ⟨t, rfl⟩ := (L.mem_liftGroup rootR_mem).1 hx
      exact conj_A_r_mem_subN hω hη hker hab L t
  calc Nat.card L.subP ≤ Nat.card K * Nat.card L.subN := h
    _ ≤ Nat.card K * Nat.card K ^ 5 := Nat.mul_le_mul_left _ (card_subN_le hω hη hker hab L)
    _ = Nat.card K ^ 6 := by ring

end Counting

omit [Group E] in
theorem mem_posRoots_cases {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots) :
    d = rootA ∨ d = rootR ∨ d = rootU ∨ d = rootV ∨ d = rootB ∨ d = rootC := by
  simpa only [posRoots, Finset.mem_insert, Finset.mem_singleton] using hd

theorem RootLifts.A_mem_subP
    (L : RootLifts η) {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ posRoots)
    (c : K) : L.A d c ∈ L.subP := by
  rcases mem_posRoots_cases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.subN_le_subP (L.le_subN_a (L.A_mem_liftGroup _ c))
  · exact L.le_subP_r (L.A_mem_liftGroup _ c)
  · exact L.subN_le_subP (L.subM_le_subN (L.le_subM_u (L.A_mem_liftGroup _ c)))
  · exact L.subN_le_subP (L.subM_le_subN (L.le_subM_v (L.A_mem_liftGroup _ c)))
  · exact L.subN_le_subP (L.subM_le_subN (L.le_subM_b (L.A_mem_liftGroup _ c)))
  · exact L.subN_le_subP (L.subM_le_subN (L.le_subM_c (L.A_mem_liftGroup _ c)))

theorem RootLifts.posUnipotent_le_map_subP
    (L : RootLifts η) :
    posUnipotent .G2 K ≤ (L.subP.map η).map (adjointGroup Tag.G2 K).subtype := by
  refine iSup₂_le fun d hd => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  have hd' : d ∈ posRoots := mem_posRoots.2 hd
  exact ⟨η (L.A d c), ⟨L.A d c, L.A_mem_subP hd' c, rfl⟩, by rw [L.map_A d hd' c]; rfl⟩

theorem G2_field_four_abelian_root_central_two_cover_trivial
    (K : Type) [Field K]
    (hK : Nat.card K = 4) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* adjointGroup Tag.G2 K) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hab : ∀ d : Fin Tag.G2.rank → ℤ, IsRoot .G2 d → 0 < height d →
      ∀ x ∈ ((rootSubgroup .G2 K d).subgroupOf (adjointGroup .G2 K)).comap η,
      ∀ y ∈ ((rootSubgroup .G2 K d).subgroupOf (adjointGroup .G2 K)).comap η, x * y = y * x) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2) (by norm_num) (by rw [hK]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ω, hω⟩ := exists_orderOf_eq (K := K)
  have hω3 : orderOf ω = 3 := by rw [hω, hK]
  have hker : ∀ z, η z = 1 → z ∈ Subgroup.center E := fun z hz => hC hz
  have hab' : ∀ d ∈ posRoots, ∀ (e e' : E) (c c' : K), η e = rootX d c → η e' = rootX d c' →
      e * e' = e' * e := by
    intro d hd e e' c c' he he'
    obtain ⟨hd1, hd2⟩ := mem_posRoots.1 hd
    refine hab d hd1 hd2 e ?_ e' ?_ <;> rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    · rw [he]
      exact Subgroup.subset_closure ⟨c, rfl⟩
    · rw [he']
      exact Subgroup.subset_closure ⟨c', rfl⟩
  obtain ⟨L⟩ := exists_rootLifts η hω3 hη hker hab'
  have hUcard : Nat.card (posUnipotent .G2 K) =
      Nat.card K ^ {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}.ncard :=
    card_posUnipotent
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := .G2) (K := K)) hUcard
  let S : Sylow 2 (adjointGroup Tag.G2 K) := hUp.toSylow hUi
  have hS : (S : Subgroup (adjointGroup Tag.G2 K)) ≤ L.subP.map η := by
    intro u hu
    rw [IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf] at hu
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 (L.posUnipotent_le_map_subP hu)
    rwa [show y = u from Subtype.ext hyu] at hy
  have hScard : Nat.card S = Nat.card K ^ 6 := by
    rw [IsPGroup.toSylow_coe, card_subgroupOf_of_le posUnipotent_le_adjointGroup, hUcard,
      ncard_posRoots]
  have hinj : ∀ z ∈ L.subP, η z = 1 → z = 1 := by
    let f : L.subP → L.subP.map η := fun m => ⟨η m, Subgroup.mem_map_of_mem η m.2⟩
    have hf : Function.Surjective f := by
      rintro ⟨y, m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    have hcard : Nat.card L.subP ≤ Nat.card (L.subP.map η) :=
      calc Nat.card L.subP ≤ Nat.card K ^ 6 := card_subP_le hω3 hη hker hab' L
        _ = Nat.card S := hScard.symm
        _ ≤ Nat.card (L.subP.map η) := Subgroup.card_le_of_le hS
    intro z hz hz1
    have h1 := (hf.bijective_of_nat_card_le hcard).1 (a₁ := ⟨z, hz⟩) (a₂ := ⟨1, one_mem _⟩)
      (Subtype.ext (show η z = η 1 by rw [hz1, map_one]))
    exact congrArg Subtype.val h1
  have hbot : η.ker = ⊥ :=
    LinearCover.ker_eq_bot_of_sylow_le_map η hη hC h2 S L.subP hS hinj
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).1 hbot, hη⟩

end CFSG.LieType.Chevalley.G2FieldFour
