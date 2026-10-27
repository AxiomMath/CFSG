module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveCommon

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

open BinarySymplecticTransvection
open scoped commutatorElement

theorem zmod2_mu_identity (k p₁ p₂ p₃ p₄ p₅ : ZMod 2) :
    p₁ + p₂ + k * p₅ + k * (p₃ + p₄ + p₅) = p₁ + k * p₃ + (p₂ + k * p₄) := by
  revert k p₁ p₂ p₃ p₄ p₅
  decide

variable {E : Type} [AddCommGroup E] {D : Type} [Group D] {B : Subgroup D}

@[expose] def bv (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2))
    (x : (E × ZMod 2) × ZMod 2) : D :=
  ((θ.symm (Multiplicative.ofAdd x) : B) : D)

open scoped Classical in
@[expose] def cB (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) (x : D) :
    (E × ZMod 2) × ZMod 2 :=
  if h : x ∈ B then Multiplicative.toAdd (θ ⟨x, h⟩) else 0

@[expose] def zz (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) : D :=
  bv θ (0, 1)

variable (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2))

theorem bv_mem (x : (E × ZMod 2) × ZMod 2) : bv θ x ∈ B :=
  (θ.symm _).2

theorem bv_add (x y : (E × ZMod 2) × ZMod 2) : bv θ (x + y) = bv θ x * bv θ y := by
  simp only [bv, ofAdd_add, map_mul, Subgroup.coe_mul]

theorem bv_zero : bv θ (0 : (E × ZMod 2) × ZMod 2) = 1 := by
  simp only [bv, ofAdd_zero, map_one, Subgroup.coe_one]

theorem bv_injective : Function.Injective (bv θ) := fun x y h => by
  have h' : θ.symm (Multiplicative.ofAdd x) = θ.symm (Multiplicative.ofAdd y) := Subtype.ext h
  exact Multiplicative.ofAdd.injective (θ.symm.injective h')

theorem cB_bv (x : (E × ZMod 2) × ZMod 2) : cB θ (bv θ x) = x := by
  have h : bv θ x ∈ B := bv_mem θ x
  simp only [cB, h, ↓reduceDIte]
  change Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd x))) = x
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem bv_cB {x : D} (hx : x ∈ B) : bv θ (cB θ x) = x := by
  simp only [cB, hx, ↓reduceDIte, bv, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem exists_bv_eq {x : D} (hx : x ∈ B) : ∃ y, bv θ y = x :=
  ⟨cB θ x, bv_cB θ hx⟩

theorem cB_mul {x y : D} (hx : x ∈ B) (hy : y ∈ B) : cB θ (x * y) = cB θ x + cB θ y := by
  obtain ⟨x', rfl⟩ := exists_bv_eq θ hx
  obtain ⟨y', rfl⟩ := exists_bv_eq θ hy
  rw [← bv_add, cB_bv, cB_bv, cB_bv]

include θ in
theorem B_comm {x y : D} (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x := by
  obtain ⟨x', rfl⟩ := exists_bv_eq θ hx
  obtain ⟨y', rfl⟩ := exists_bv_eq θ hy
  rw [← bv_add, ← bv_add, add_comm]

variable [Module (ZMod 2) E]

theorem bv_mul_self (x : (E × ZMod 2) × ZMod 2) : bv θ x * bv θ x = 1 := by
  rw [← bv_add, add_self_eq_zero_zmod_two, bv_zero]

theorem bv_inv (x : (E × ZMod 2) × ZMod 2) : (bv θ x)⁻¹ = bv θ x :=
  inv_eq_of_mul_eq_one_right (bv_mul_self θ x)

include θ in
theorem sq_eq_one_of_mem {x : D} (hx : x ∈ B) : x ^ 2 = 1 := by
  obtain ⟨x', rfl⟩ := exists_bv_eq θ hx
  rw [sq, bv_mul_self]

@[expose] def subA : Subgroup D where
  carrier := {d | ∃ v, bv θ (v, 0) = d}
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, by rw [← bv_add]; congr 1⟩
  one_mem' := ⟨0, bv_zero θ⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨v, (bv_inv θ _).symm⟩

@[expose] def subI : Subgroup D where
  carrier := {d | ∃ c : ZMod 2, bv θ (c • rV, 0) = d}
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', by rw [← bv_add]; congr 1; simp [add_smul]⟩
  one_mem' := ⟨0, by rw [zero_smul, Prod.mk_zero_zero, bv_zero]⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨c, (bv_inv θ _).symm⟩

theorem mem_subA {d : D} : d ∈ subA θ ↔ ∃ v, bv θ (v, 0) = d :=
  Iff.rfl

theorem subA_le : subA θ ≤ B := by
  rintro _ ⟨v, rfl⟩
  exact bv_mem θ _

theorem subI_le_subA : subI θ ≤ subA θ := by
  rintro _ ⟨c, rfl⟩
  exact ⟨_, rfl⟩

omit [Module (ZMod 2) E] in
theorem zz_mem : zz θ ∈ B :=
  bv_mem θ _

theorem zz_not_mem_subA : zz θ ∉ subA θ := by
  rintro ⟨v, hv⟩
  have h := congrArg Prod.snd (bv_injective θ hv)
  simp only at h
  exact absurd h (by decide)

theorem mem_subA_of_cB {x : D} (hx : x ∈ B) (h : (cB θ x).2 = 0) : x ∈ subA θ :=
  ⟨(cB θ x).1, by rw [← h, Prod.mk.eta, bv_cB θ hx]⟩

theorem mem_subA_or_mul_zz {x : D} (hx : x ∈ B) : x ∈ subA θ ∨ x * zz θ ∈ subA θ := by
  obtain ⟨⟨v, ε⟩, rfl⟩ := exists_bv_eq θ hx
  rcases zmod_two_cases ε with rfl | rfl
  · exact Or.inl ⟨v, rfl⟩
  · refine Or.inr ⟨v, ?_⟩
    rw [zz, ← bv_add, Prod.mk_add_mk, add_zero]
    rfl

variable (b : LinearMap.BilinForm (ZMod 2) E) (κ : ZMod 2)

structure Labels where
  lab : D → E × ZMod 2
  conj (d : D) (v : E × ZMod 2) :
    d⁻¹ * bv θ (v, 1) * d = bv θ (v + lab d + (κ * b (lab d).1 v.1) • rV, 1)

variable {θ b κ}

namespace Labels

variable (L : Labels θ b κ)

theorem conj_bv (d : D) (v : E × ZMod 2) (ε : ZMod 2) :
    d⁻¹ * bv θ (v, ε) * d = bv θ (v + (κ * b (L.lab d).1 v.1) • rV + ε • L.lab d, ε) := by
  rcases zmod_two_cases ε with rfl | rfl
  · have hsplit : bv θ ((v, 0) : (E × ZMod 2) × ZMod 2) = bv θ (v, 1) * bv θ (0, 1) := by
      rw [← bv_add, Prod.mk_add_mk, add_zero]
      rfl
    have hconj : d⁻¹ * (bv θ (v, 1) * bv θ (0, 1)) * d =
        (d⁻¹ * bv θ (v, 1) * d) * (d⁻¹ * bv θ (0, 1) * d) := by group
    rw [hsplit, hconj, L.conj, L.conj, ← bv_add, Prod.mk_add_mk]
    congr 1
    simp only [Prod.fst_zero, map_zero, mul_zero, zero_smul, add_zero, zero_add]
    refine Prod.ext ?_ (zmod2_add_self 1)
    rw [add_right_comm v, add_assoc, add_self_eq_zero_zmod_two, add_zero]
  · rw [L.conj, one_smul, add_right_comm]

theorem conj_zz (d : D) : d⁻¹ * zz θ * d = bv θ (L.lab d, 1) := by
  rw [zz, L.conj]
  simp only [Prod.fst_zero, map_zero, mul_zero, zero_smul, add_zero, zero_add]

theorem lab_one : L.lab 1 = 0 := by
  have h := L.conj_zz 1
  rw [inv_one, one_mul, mul_one, zz] at h
  exact (congrArg Prod.fst (bv_injective θ h)).symm

theorem lab_mul (hb : b.IsAlt) (d₁ d₂ : D) :
    L.lab (d₁ * d₂) = L.lab d₁ + L.lab d₂ + (κ * b (L.lab d₁).1 (L.lab d₂).1) • rV := by
  have h := L.conj_zz (d₁ * d₂)
  have h' : (d₁ * d₂)⁻¹ * zz θ * (d₁ * d₂) = d₂⁻¹ * (d₁⁻¹ * zz θ * d₁) * d₂ := by group
  rw [h', L.conj_zz, L.conj, symm_apply hb] at h
  exact (congrArg Prod.fst (bv_injective θ h)).symm

theorem lab_of_mem {d : D} (hd : d ∈ B) : L.lab d = 0 := by
  have h := L.conj_zz d
  rw [mul_assoc, B_comm θ (zz_mem θ) hd, ← mul_assoc, inv_mul_cancel, one_mul, zz] at h
  exact (congrArg Prod.fst (bv_injective θ h)).symm

theorem mem_of_lab_eq_zero
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) {d : D}
    (h : L.lab d = 0) : d ∈ B :=
  hfaith d fun v => by
    rw [L.conj, h]
    simp only [Prod.fst_zero, map_zero, LinearMap.zero_apply, mul_zero, zero_smul, add_zero]

theorem comm_bv (x : (E × ZMod 2) × ZMod 2) (d : D) :
    (bv θ x)⁻¹ * d⁻¹ * bv θ x * d =
      bv θ ((κ * b (L.lab d).1 x.1.1) • rV + x.2 • L.lab d, 0) := by
  have h : (bv θ x)⁻¹ * d⁻¹ * bv θ x * d = (bv θ x)⁻¹ * (d⁻¹ * bv θ (x.1, x.2) * d) := by
    simp only [Prod.mk.eta]
    group
  rw [h, L.conj_bv, bv_inv, ← bv_add]
  congr 1
  refine Prod.ext ?_ (zmod2_add_self _)
  change x.1 + (x.1 + _ + _) = _
  rw [← add_assoc, ← add_assoc, add_self_eq_zero_zmod_two, zero_add]

section Mu

variable {Q : QuadraticForm (ZMod 2) E}

@[expose] def mu (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b) :
    D →* Multiplicative (E × ZMod 2) where
  toFun d := Multiplicative.ofAdd ((L.lab d).1, (L.lab d).2 + κ * Q (L.lab d).1)
  map_one' := by
    rw [L.lab_one]
    simp
  map_mul' d₁ d₂ := by
    rw [L.lab_mul hb, ← ofAdd_add]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, rV, smul_zero,
      add_zero, smul_eq_mul, mul_one, Q_add hQ, Prod.mk_add_mk]
    congr 1
    exact zmod2_mu_identity _ _ _ _ _ _

theorem mu_apply (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b) (d : D) :
    L.mu hb hQ d = Multiplicative.ofAdd ((L.lab d).1, (L.lab d).2 + κ * Q (L.lab d).1) :=
  rfl

theorem mu_eq_one_iff (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b) (d : D) :
    L.mu hb hQ d = 1 ↔ L.lab d = 0 := by
  rw [mu_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
    rw [h1, QuadraticMap.map_zero, mul_zero, add_zero] at h2
    exact Prod.ext h1 h2
  · intro h
    rw [h]
    simp

theorem ker_mu (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) :
    (L.mu hb hQ).ker = B := by
  ext d
  rw [MonoidHom.mem_ker, mu_eq_one_iff]
  exact ⟨L.mem_of_lab_eq_zero hfaith, L.lab_of_mem⟩

theorem mu_surjective (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b)
    (hsurj : ∀ a, ∃ d, L.lab d = a) : Function.Surjective (L.mu hb hQ) := by
  intro w
  obtain ⟨d, hd⟩ := hsurj ((Multiplicative.toAdd w).1,
    (Multiplicative.toAdd w).2 + κ * Q (Multiplicative.toAdd w).1)
  refine ⟨d, ?_⟩
  rw [mu_apply, hd]
  simp only [add_assoc, zmod2_add_self, add_zero, Prod.mk.eta, ofAdd_toAdd]

theorem mu_fst (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b) (d : D) :
    (Multiplicative.toAdd (L.mu hb hQ d)).1 = (L.lab d).1 :=
  rfl

end Mu

include L in
theorem sq_mem (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d : D) :
    d ^ 2 ∈ B := by
  refine L.mem_of_lab_eq_zero hfaith ?_
  rw [sq, L.lab_mul hb, add_self_eq_zero_zmod_two, zero_add, hb.self_eq_zero, mul_zero, zero_smul]

include L in
theorem sq_mem_subA (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d : D) :
    d ^ 2 ∈ subA θ := by
  obtain ⟨y, hy⟩ := exists_bv_eq θ (L.sq_mem hb hfaith d)
  refine mem_subA_of_cB θ (L.sq_mem hb hfaith d) ?_
  rw [← hy, cB_bv]
  by_contra hy2
  have hy2' : y.2 = 1 := (zmod_two_cases y.2).resolve_left hy2
  have hfix : d⁻¹ * bv θ (y.1, y.2) * d = bv θ (y.1, y.2) := by
    rw [Prod.mk.eta, hy]
    group
  rw [L.conj_bv] at hfix
  have h1 := congrArg Prod.fst (bv_injective θ hfix)
  simp only at h1
  rw [hy2', one_smul, add_assoc, add_eq_left] at h1
  have hlab : L.lab d = (κ * b (L.lab d).1 y.1.1) • rV := (eq_of_add_eq_zero_zmod2 h1).symm
  have hlab1 : (L.lab d).1 = 0 := by
    rw [hlab]
    simp [rV]
  rw [hlab1, map_zero, LinearMap.zero_apply, mul_zero, zero_smul] at hlab
  have hdB := L.mem_of_lab_eq_zero hfaith hlab
  rw [sq_eq_one_of_mem θ hdB, ← bv_zero θ] at hy
  have := congrArg Prod.snd (bv_injective θ hy)
  rw [hy2', Prod.snd_zero] at this
  exact absurd this (by decide)

theorem comm_eq_sq_mul (d d' : D) :
    d⁻¹ * d'⁻¹ * d * d' = d⁻¹ ^ 2 * (d * d'⁻¹) ^ 2 * d' ^ 2 := by
  rw [sq, sq, sq]
  group

include L in
theorem comm_mem_subA (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d d' : D) :
    d⁻¹ * d'⁻¹ * d * d' ∈ subA θ := by
  rw [comm_eq_sq_mul]
  exact mul_mem (mul_mem (L.sq_mem_subA hb hfaith _) (L.sq_mem_subA hb hfaith _))
    (L.sq_mem_subA hb hfaith _)

end Labels

theorem commutator_le_closure_sq {G : Type*} [Group G] (H : Subgroup G) :
    ⁅H, H⁆ ≤ Subgroup.closure {x | ∃ y ∈ H, y ^ 2 = x} := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have e : ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * y⁻¹ ^ 2 := by
    rw [commutatorElement_def, sq, sq, sq]
    group
  rw [e]
  exact mul_mem (mul_mem (Subgroup.subset_closure ⟨x, hx, rfl⟩)
    (Subgroup.subset_closure ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy, rfl⟩))
    (Subgroup.subset_closure ⟨y⁻¹, inv_mem hy, rfl⟩)

namespace Labels

variable (L : Labels θ b κ)

theorem comm_zz (d : D) : (zz θ)⁻¹ * d⁻¹ * zz θ * d = bv θ (L.lab d, 0) := by
  rw [zz, L.comm_bv]
  simp

theorem commutator_eq (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) : commutator D = subA θ := by
  refine le_antisymm ?_ ?_
  · rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h := L.comm_mem_subA hb hfaith x⁻¹ y⁻¹
    rwa [inv_inv, inv_inv, ← commutatorElement_def] at h
  · rintro _ ⟨v, rfl⟩
    obtain ⟨d, hd⟩ := hsurj v
    have hz : (zz θ)⁻¹ = zz θ := bv_inv θ _
    have h : bv θ (v, 0) = ⁅zz θ, d⁻¹⁆ := by
      rw [commutatorElement_def, inv_inv]
      calc bv θ (v, 0) = (zz θ)⁻¹ * d⁻¹ * zz θ * d := by rw [L.comm_zz, hd]
        _ = zz θ * d⁻¹ * (zz θ)⁻¹ * d := by rw [hz]
    rw [h, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem closure_sq_eq (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) :
    Subgroup.closure {x : D | ∃ y : D, y ^ 2 = x} = subA θ := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨y, rfl⟩
    exact L.sq_mem_subA hb hfaith y
  · rw [← L.commutator_eq hb hfaith hsurj, commutator_def]
    refine (commutator_le_closure_sq ⊤).trans (Subgroup.closure_mono ?_)
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩

end Labels

@[expose] def sig (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) (d : D) : E :=
  (cB θ (d ^ 2)).1.1

@[expose] def om (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) (d d' : D) : E :=
  (cB θ (d⁻¹ * d'⁻¹ * d * d')).1.1

omit [Module (ZMod 2) E] in
theorem cB_one : cB θ (1 : D) = 0 := by
  rw [← bv_zero θ, cB_bv]

theorem cB_inv_of_mem {x : D} (hx : x ∈ B) : cB θ x⁻¹ = cB θ x := by
  obtain ⟨y, rfl⟩ := exists_bv_eq θ hx
  rw [bv_inv]

theorem sig_of_mem {x : D} (hx : x ∈ B) : sig θ x = 0 := by
  rw [sig, sq_eq_one_of_mem θ hx, cB_one]
  rfl

omit [Module (ZMod 2) E] in
theorem om_self (d : D) : om θ d d = 0 := by
  rw [om, show d⁻¹ * d⁻¹ * d * d = 1 by group, cB_one]
  rfl

namespace Labels

variable (L : Labels θ b κ)

include L in
theorem conj_mem_subA {x : D} (hx : x ∈ subA θ) (d : D) : d⁻¹ * x * d ∈ subA θ := by
  obtain ⟨v, rfl⟩ := hx
  rw [L.conj_bv, zero_smul, add_zero]
  exact ⟨_, rfl⟩

include L in
theorem fst_fst_cB_conj {x : D} (hx : x ∈ subA θ) (d : D) :
    (cB θ (d⁻¹ * x * d)).1.1 = (cB θ x).1.1 := by
  obtain ⟨v, rfl⟩ := hx
  rw [L.conj_bv, cB_bv, cB_bv]
  simp [rV]

theorem om_bv (x : (E × ZMod 2) × ZMod 2) (d : D) : om θ (bv θ x) d = x.2 • (L.lab d).1 := by
  rw [om, L.comm_bv, cB_bv]
  simp [rV]

theorem om_zz (d : D) : om θ (zz θ) d = (L.lab d).1 := by
  rw [zz, L.om_bv, one_smul]

include L in
theorem om_of_mem_subA {x : D} (hx : x ∈ subA θ) (d : D) : om θ x d = 0 := by
  obtain ⟨v, rfl⟩ := hx
  rw [L.om_bv, zero_smul]

include L in
theorem om_comm (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d d' : D) :
    om θ d' d = om θ d d' := by
  rw [om, om, show d'⁻¹ * d⁻¹ * d' * d = (d⁻¹ * d'⁻¹ * d * d')⁻¹ by group,
    cB_inv_of_mem (subA_le θ (L.comm_mem_subA hb hfaith d d'))]

include L in
theorem om_of_mem_subA_right (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) {x : D}
    (hx : x ∈ subA θ) (d : D) : om θ d x = 0 := by
  rw [L.om_comm hb hfaith, L.om_of_mem_subA hx]

include L in
theorem om_mul_left (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d₁ d₂ d' : D) :
    om θ (d₁ * d₂) d' = om θ d₁ d' + om θ d₂ d' := by
  have e : (d₁ * d₂)⁻¹ * d'⁻¹ * (d₁ * d₂) * d' =
      d₂⁻¹ * (d₁⁻¹ * d'⁻¹ * d₁ * d') * d₂ * (d₂⁻¹ * d'⁻¹ * d₂ * d') := by group
  have h₁ := L.comm_mem_subA hb hfaith d₁ d'
  have h₂ := L.comm_mem_subA hb hfaith d₂ d'
  rw [om, om, om, e, cB_mul θ (subA_le θ (L.conj_mem_subA h₁ d₂)) (subA_le θ h₂), Prod.fst_add,
    Prod.fst_add, L.fst_fst_cB_conj h₁]

include L in
theorem om_mul_right (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d d₁ d₂ : D) :
    om θ d (d₁ * d₂) = om θ d d₁ + om θ d d₂ := by
  rw [L.om_comm hb hfaith, L.om_mul_left hb hfaith, L.om_comm hb hfaith d₁,
    L.om_comm hb hfaith d₂]

include L in
theorem sig_mul (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d₁ d₂ : D) :
    sig θ (d₁ * d₂) = sig θ d₁ + sig θ d₂ + om θ d₂ d₁ := by
  have e : (d₁ * d₂) ^ 2 = d₁ ^ 2 * d₂ ^ 2 * (d₂⁻¹ * (d₂⁻¹ * d₁⁻¹ * d₂ * d₁) * d₂) := by
    rw [sq, sq, sq]
    group
  have hc := L.comm_mem_subA hb hfaith d₂ d₁
  rw [sig, sig, sig, om, e,
    cB_mul θ (mul_mem (L.sq_mem hb hfaith d₁) (L.sq_mem hb hfaith d₂))
      (subA_le θ (L.conj_mem_subA hc d₂)),
    cB_mul θ (L.sq_mem hb hfaith d₁) (L.sq_mem hb hfaith d₂), Prod.fst_add, Prod.fst_add,
    Prod.fst_add, Prod.fst_add, L.fst_fst_cB_conj hc]

include L in
theorem sig_mul_of_mem_subA (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d : D) {x : D}
    (hx : x ∈ subA θ) : sig θ (d * x) = sig θ d := by
  rw [L.sig_mul hb hfaith, sig_of_mem (subA_le θ hx), L.om_of_mem_subA hx, add_zero, add_zero]

theorem sig_mul_zz (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d : D) :
    sig θ (d * zz θ) = sig θ d + (L.lab d).1 := by
  rw [L.sig_mul hb hfaith, sig_of_mem (zz_mem θ), L.om_zz, add_zero]

include L in
theorem om_mul_of_mem_subA (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d d' : D) {x : D}
    (hx : x ∈ subA θ) : om θ (d * x) d' = om θ d d' := by
  rw [L.om_mul_left hb hfaith, L.om_of_mem_subA hx, add_zero]

theorem om_mul_zz (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (d d' : D) :
    om θ (d * zz θ) d' = om θ d d' + (L.lab d').1 := by
  rw [L.om_mul_left hb hfaith, L.om_zz]

end Labels

end CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
