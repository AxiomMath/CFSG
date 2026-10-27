module

public import CFSG.FeitThompson.Representations.IrreducibleCharactersOrthonormalBasis
public import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
public import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
public import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
public import CFSG.FeitThompson.Representations.OddCyclicFactorOrders
public import
  CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
public import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section IsMulCommutative

variable {A : Type*} [Group A] [IsMulCommutative A]

theorem mem_Irr_of_monoidHom (ψ : A →* ℂˣ) : (fun a => (ψ a : ℂ)) ∈ Irr A := by
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  have h := linearCharFun_mem_Irr (A := A) ψ
  rwa [show linearCharFun ψ = fun a => (ψ a : ℂ) from funext fun a => linearCharFun_apply ψ a] at h

theorem exists_monoidHom_coe_eq_of_mem_Irr {χ : A → ℂ} (hχ : χ ∈ Irr A) :
    ∃ ψ : A →* ℂˣ, (fun a => (ψ a : ℂ)) = χ := by
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨ψ, hψ⟩ := exists_linearCharFun_eq_of_mem_Irr (A := A) hχ
  exact ⟨ψ, by rw [← hψ]; exact funext fun a => (linearCharFun_apply ψ a).symm⟩

theorem apply_one_eq_one_of_mem_Irr {χ : A → ℂ} (hχ : χ ∈ Irr A) : χ 1 = 1 := by
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  exact Irr.apply_one_eq_one (A := A) hχ

theorem card_Irr_eq_card_of_isMulCommutative [Finite A] : Nat.card (Irr A) = Nat.card A := by
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  exact card_Irr_eq_card (A := A)

end IsMulCommutative

def principalIrr (X : Type*) [Group X] : Irr X := ⟨1, one_mem_Irr⟩

@[simp]
theorem coe_principalIrr (X : Type*) [Group X] : ((principalIrr X : Irr X) : X → ℂ) = 1 := (rfl)

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}

namespace IsCyclicTIPair

theorem isMulCommutative_coe (h : IsCyclicTIPair W W1 W2) : IsMulCommutative ↥W :=
  have := h.isCyclic
  IsCyclic.isMulCommutative

theorem isMulCommutative_left (h : IsCyclicTIPair W W1 W2) : IsMulCommutative ↥W1 :=
  have := h.isMulCommutative_coe
  isMulCommutative_iff_of_setLike.2 fun _ ha _ hb =>
    setLike_mul_comm (h.left_le ha) (h.left_le hb)

theorem isMulCommutative_right (h : IsCyclicTIPair W W1 W2) : IsMulCommutative ↥W2 :=
  have := h.isMulCommutative_coe
  isMulCommutative_iff_of_setLike.2 fun _ ha _ hb =>
    setLike_mul_comm (h.right_le ha) (h.right_le hb)

noncomputable def mulEquivProd (h : IsCyclicTIPair W W1 W2) : (↥W1 × ↥W2) ≃* ↥W :=
  mulEquivProdOfCoeEqMul h.mul_eq.symm h.inf_eq_bot fun _ hx _ hy => h.commute_of_mem hx hy

@[simp]
theorem coe_mulEquivProd_apply (h : IsCyclicTIPair W W1 W2) (p : ↥W1 × ↥W2) :
    ((h.mulEquivProd p : ↥W) : G) = (p.1 : G) * (p.2 : G) :=
  coe_mulEquivProdOfCoeEqMul_apply _ _ _ p

theorem symm_mulEquivProd_apply (h : IsCyclicTIPair W W1 W2) {x y : G} (hx : x ∈ W1)
    (hy : y ∈ W2) :
    h.mulEquivProd.symm ⟨x * y, mul_mem (h.left_le hx) (h.right_le hy)⟩ = (⟨x, hx⟩, ⟨y, hy⟩) := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (h.coe_mulEquivProd_apply (⟨x, hx⟩, ⟨y, hy⟩)).symm

theorem natCard_eq_mul (h : IsCyclicTIPair W W1 W2) :
    Nat.card ↥W = Nat.card ↥W1 * Nat.card ↥W2 := by
  rw [← Nat.card_congr h.mulEquivProd.toEquiv, Nat.card_prod]

noncomputable def prodChar (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) :
    ↥W → ℂ := fun z => lam (h.mulEquivProd.symm z).1 * mu (h.mulEquivProd.symm z).2

theorem prodChar_apply (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) (z : ↥W) :
    h.prodChar lam mu z = lam (h.mulEquivProd.symm z).1 * mu (h.mulEquivProd.symm z).2 := (rfl)

theorem prodChar_apply_mul (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ)
    {x y : G} (hx : x ∈ W1) (hy : y ∈ W2) :
    h.prodChar lam mu ⟨x * y, mul_mem (h.left_le hx) (h.right_le hy)⟩ =
      lam ⟨x, hx⟩ * mu ⟨y, hy⟩ := by
  rw [prodChar_apply, h.symm_mulEquivProd_apply hx hy]

theorem prodChar_apply_coe_left (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ)
    (x : ↥W1) : h.prodChar lam mu ⟨(x : G), h.left_le x.2⟩ = lam x * mu 1 := by
  have hx : (⟨(x : G), h.left_le x.2⟩ : ↥W) =
      ⟨(x : G) * (1 : G), mul_mem (h.left_le x.2) (h.right_le (one_mem W2))⟩ :=
    Subtype.ext (by simp)
  rw [hx, h.prodChar_apply_mul lam mu x.2 (one_mem W2)]
  rfl

theorem prodChar_apply_coe_right (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ)
    (y : ↥W2) : h.prodChar lam mu ⟨(y : G), h.right_le y.2⟩ = lam 1 * mu y := by
  have hy : (⟨(y : G), h.right_le y.2⟩ : ↥W) =
      ⟨(1 : G) * (y : G), mul_mem (h.left_le (one_mem W1)) (h.right_le y.2)⟩ :=
    Subtype.ext (by simp)
  rw [hy, h.prodChar_apply_mul lam mu (one_mem W1) y.2]
  rfl

theorem prodChar_one (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) :
    h.prodChar lam mu 1 = lam 1 * mu 1 := by
  have h1 : (1 : ↥W) = ⟨(1 : G) * (1 : G),
      mul_mem (h.left_le (one_mem W1)) (h.right_le (one_mem W2))⟩ := Subtype.ext (by simp)
  rw [h1, h.prodChar_apply_mul lam mu (one_mem W1) (one_mem W2)]
  rfl

@[simp]
theorem prodChar_one_one (h : IsCyclicTIPair W W1 W2) : h.prodChar 1 1 = 1 := by
  funext z
  simp [prodChar_apply]

theorem prodChar_mul_prodChar (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) :
    h.prodChar lam 1 * h.prodChar 1 mu = h.prodChar lam mu := by
  funext z
  simp [prodChar_apply]

noncomputable def prodCharHom (h : IsCyclicTIPair W W1 W2) (ψ₁ : ↥W1 →* ℂˣ) (ψ₂ : ↥W2 →* ℂˣ) :
    ↥W →* ℂˣ := (ψ₁.coprod ψ₂).comp h.mulEquivProd.symm.toMonoidHom

theorem prodChar_coe_coe (h : IsCyclicTIPair W W1 W2) (ψ₁ : ↥W1 →* ℂˣ) (ψ₂ : ↥W2 →* ℂˣ) :
    h.prodChar (fun a => (ψ₁ a : ℂ)) (fun b => (ψ₂ b : ℂ)) =
      fun z => ((h.prodCharHom ψ₁ ψ₂ z : ℂ)) := by
  funext z
  rw [prodChar_apply, prodCharHom]
  simp [MonoidHom.coprod_apply]

theorem prodChar_comp_inclusion (h : IsCyclicTIPair W W1 W2) (ψ : ↥W →* ℂˣ) :
    h.prodChar (fun a => (ψ (Subgroup.inclusion h.left_le a) : ℂ))
      (fun b => (ψ (Subgroup.inclusion h.right_le b) : ℂ)) = fun z => (ψ z : ℂ) := by
  funext z
  rw [prodChar_apply]
  have hz : Subgroup.inclusion h.left_le (h.mulEquivProd.symm z).1 *
      Subgroup.inclusion h.right_le (h.mulEquivProd.symm z).2 = z := by
    refine Subtype.ext ?_
    have hp := h.coe_mulEquivProd_apply (h.mulEquivProd.symm z)
    rw [MulEquiv.apply_symm_apply] at hp
    simpa using hp.symm
  rw [← Units.val_mul, ← ψ.map_mul, hz]

theorem prodChar_mem_Irr (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ} {mu : ↥W2 → ℂ}
    (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) : h.prodChar lam mu ∈ Irr ↥W := by
  have := h.isMulCommutative_left
  have := h.isMulCommutative_right
  have := h.isMulCommutative_coe
  obtain ⟨ψ₁, hψ₁⟩ := exists_monoidHom_coe_eq_of_mem_Irr hlam
  obtain ⟨ψ₂, hψ₂⟩ := exists_monoidHom_coe_eq_of_mem_Irr hmu
  rw [← hψ₁, ← hψ₂, h.prodChar_coe_coe ψ₁ ψ₂]
  exact mem_Irr_of_monoidHom _

theorem prodChar_one_eq_one (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ} {mu : ↥W2 → ℂ}
    (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) : h.prodChar lam mu 1 = 1 := by
  have := h.isMulCommutative_left
  have := h.isMulCommutative_right
  rw [h.prodChar_one, apply_one_eq_one_of_mem_Irr hlam, apply_one_eq_one_of_mem_Irr hmu, one_mul]

theorem prodChar_injective (h : IsCyclicTIPair W W1 W2) {lam lam' : ↥W1 → ℂ}
    {mu mu' : ↥W2 → ℂ} (hlam : lam ∈ Irr ↥W1) (hlam' : lam' ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2)
    (hmu' : mu' ∈ Irr ↥W2) (he : h.prodChar lam mu = h.prodChar lam' mu') :
    lam = lam' ∧ mu = mu' := by
  have := h.isMulCommutative_left
  have := h.isMulCommutative_right
  constructor
  · funext x
    have hx := congrFun he ⟨(x : G), h.left_le x.2⟩
    rwa [h.prodChar_apply_coe_left, h.prodChar_apply_coe_left,
      apply_one_eq_one_of_mem_Irr hmu, apply_one_eq_one_of_mem_Irr hmu', mul_one, mul_one] at hx
  · funext y
    have hy := congrFun he ⟨(y : G), h.right_le y.2⟩
    rwa [h.prodChar_apply_coe_right, h.prodChar_apply_coe_right,
      apply_one_eq_one_of_mem_Irr hlam, apply_one_eq_one_of_mem_Irr hlam', one_mul, one_mul] at hy

theorem exists_prodChar_eq_of_mem_Irr (h : IsCyclicTIPair W W1 W2) {χ : ↥W → ℂ}
    (hχ : χ ∈ Irr ↥W) : ∃ lam ∈ Irr ↥W1, ∃ mu ∈ Irr ↥W2, h.prodChar lam mu = χ := by
  have := h.isMulCommutative_left
  have := h.isMulCommutative_right
  have := h.isMulCommutative_coe
  obtain ⟨ψ, hψ⟩ := exists_monoidHom_coe_eq_of_mem_Irr hχ
  refine ⟨_, mem_Irr_of_monoidHom (ψ.comp (Subgroup.inclusion h.left_le)), _,
    mem_Irr_of_monoidHom (ψ.comp (Subgroup.inclusion h.right_le)), ?_⟩
  rw [← hψ]
  exact h.prodChar_comp_inclusion ψ

theorem Irr_eq_range_prodChar (h : IsCyclicTIPair W W1 W2) :
    Irr ↥W = Set.range (fun p : Irr ↥W1 × Irr ↥W2 =>
      h.prodChar (p.1 : ↥W1 → ℂ) (p.2 : ↥W2 → ℂ)) := by
  refine Set.eq_of_subset_of_subset (fun χ hχ => ?_) ?_
  · obtain ⟨lam, hlam, mu, hmu, he⟩ := h.exists_prodChar_eq_of_mem_Irr hχ
    exact ⟨(⟨lam, hlam⟩, ⟨mu, hmu⟩), he⟩
  · rintro χ ⟨p, rfl⟩
    exact h.prodChar_mem_Irr p.1.2 p.2.2

noncomputable def irrEquivProdIrr (h : IsCyclicTIPair W W1 W2) :
    (Irr ↥W1 × Irr ↥W2) ≃ Irr ↥W :=
  Equiv.ofBijective (fun p => ⟨h.prodChar (p.1 : ↥W1 → ℂ) (p.2 : ↥W2 → ℂ),
      h.prodChar_mem_Irr p.1.2 p.2.2⟩)
    ⟨fun p q hpq => by
      obtain ⟨h1, h2⟩ := h.prodChar_injective p.1.2 q.1.2 p.2.2 q.2.2 (congrArg Subtype.val hpq)
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2),
     fun χ => by
      obtain ⟨lam, hlam, mu, hmu, he⟩ := h.exists_prodChar_eq_of_mem_Irr χ.2
      exact ⟨(⟨lam, hlam⟩, ⟨mu, hmu⟩), Subtype.ext he⟩⟩

@[simp]
theorem coe_irrEquivProdIrr_apply (h : IsCyclicTIPair W W1 W2) (p : Irr ↥W1 × Irr ↥W2) :
    ((h.irrEquivProdIrr p : Irr ↥W) : ↥W → ℂ) =
      h.prodChar (p.1 : ↥W1 → ℂ) (p.2 : ↥W2 → ℂ) := (rfl)

theorem card_Irr_left (h : IsCyclicTIPair W W1 W2) : Nat.card (Irr ↥W1) = Nat.card ↥W1 := by
  have := h.isMulCommutative_left
  have := h.finite_left
  exact card_Irr_eq_card_of_isMulCommutative

theorem card_Irr_right (h : IsCyclicTIPair W W1 W2) : Nat.card (Irr ↥W2) = Nat.card ↥W2 := by
  have := h.isMulCommutative_right
  have := h.finite_right
  exact card_Irr_eq_card_of_isMulCommutative

theorem card_prod_Irr (h : IsCyclicTIPair W W1 W2) :
    Nat.card (Irr ↥W1 × Irr ↥W2) = Nat.card ↥W := by
  rw [Nat.card_prod, h.card_Irr_left, h.card_Irr_right, h.natCard_eq_mul]

open scoped Classical in
theorem cfInner_prodChar (h : IsCyclicTIPair W W1 W2) [Fintype ↥W] (i i' : Irr ↥W1)
    (j j' : Irr ↥W2) :
    cfInner (h.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodChar (i' : ↥W1 → ℂ) (j' : ↥W2 → ℂ)) =
      if (i, j) = (i', j') then 1 else 0 := by
  rw [cfInner_eq_ite_of_mem_Irr (h.prodChar_mem_Irr i.2 j.2) (h.prodChar_mem_Irr i'.2 j'.2)]
  by_cases hij : (i, j) = (i', j')
  · have hi : i = i' := congrArg Prod.fst hij
    have hj : j = j' := congrArg Prod.snd hij
    rw [if_pos (by rw [hi, hj]), if_pos hij]
  · rw [if_neg ?_, if_neg hij]
    intro he
    obtain ⟨h1, h2⟩ := h.prodChar_injective i.2 i'.2 j.2 j'.2 he
    exact hij (Prod.ext (Subtype.ext h1) (Subtype.ext h2))

open scoped Classical in
theorem cfInner_prodChar_eq_ite_and (h : IsCyclicTIPair W W1 W2) [Fintype ↥W] (i i' : Irr ↥W1)
    (j j' : Irr ↥W2) :
    cfInner (h.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodChar (i' : ↥W1 → ℂ) (j' : ↥W2 → ℂ)) =
      if i = i' ∧ j = j' then 1 else 0 := by
  rw [h.cfInner_prodChar]
  exact if_congr Prod.ext_iff rfl rfl

noncomputable def basisProdIrr (h : IsCyclicTIPair W W1 W2) :
    Module.Basis (Irr ↥W1 × Irr ↥W2) ℂ (classFun ↥W) :=
  have := h.finite_coe
  (classFun.basisIrr ↥W).reindex h.irrEquivProdIrr.symm

@[simp]
theorem coe_basisProdIrr_apply (h : IsCyclicTIPair W W1 W2) (p : Irr ↥W1 × Irr ↥W2) :
    ((h.basisProdIrr p : classFun ↥W) : ↥W → ℂ) =
      h.prodChar (p.1 : ↥W1 → ℂ) (p.2 : ↥W2 → ℂ) := by
  have := h.finite_coe
  rw [basisProdIrr, Module.Basis.reindex_apply, Equiv.symm_symm, classFun.basisIrr_apply,
    Irr.coe_toClassFun, coe_irrEquivProdIrr_apply]

open scoped Classical in
theorem cfInner_basisProdIrr (h : IsCyclicTIPair W W1 W2) [Fintype ↥W]
    (p q : Irr ↥W1 × Irr ↥W2) :
    cfInner ((h.basisProdIrr p : classFun ↥W) : ↥W → ℂ)
        ((h.basisProdIrr q : classFun ↥W) : ↥W → ℂ) = if p = q then 1 else 0 := by
  rw [coe_basisProdIrr_apply, coe_basisProdIrr_apply, h.cfInner_prodChar]

noncomputable def prodCharAlpha (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ)
    (mu : ↥W2 → ℂ) : ↥W → ℂ := 1 - h.prodChar lam 1 - h.prodChar 1 mu + h.prodChar lam mu

theorem prodCharAlpha_eq (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) :
    h.prodCharAlpha lam mu =
      1 - h.prodChar lam 1 - h.prodChar 1 mu + h.prodChar lam mu := (rfl)

theorem prodCharAlpha_eq_mul (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) :
    h.prodCharAlpha lam mu = (1 - h.prodChar lam 1) * (1 - h.prodChar 1 mu) := by
  rw [prodCharAlpha_eq, ← h.prodChar_mul_prodChar lam mu]
  ring

theorem prodCharAlpha_mem_virtualChars (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ}
    {mu : ↥W2 → ℂ} (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) :
    h.prodCharAlpha lam mu ∈ virtualChars ↥W := by
  rw [prodCharAlpha_eq]
  refine add_mem (sub_mem (sub_mem ?_ ?_) ?_) ?_
  · exact Irr_subset_virtualChars (one_mem_Irr (G := ↥W))
  · exact Irr_subset_virtualChars (h.prodChar_mem_Irr hlam one_mem_Irr)
  · exact Irr_subset_virtualChars (h.prodChar_mem_Irr one_mem_Irr hmu)
  · exact Irr_subset_virtualChars (h.prodChar_mem_Irr hlam hmu)

theorem prodCharAlpha_one (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ} {mu : ↥W2 → ℂ}
    (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) : h.prodCharAlpha lam mu 1 = 0 := by
  have h1 := h.prodChar_one_eq_one hlam (one_mem_Irr (G := ↥W2))
  have h2 := h.prodChar_one_eq_one (one_mem_Irr (G := ↥W1)) hmu
  have h3 := h.prodChar_one_eq_one hlam hmu
  simp only [prodCharAlpha_eq, Pi.add_apply, Pi.sub_apply, Pi.one_apply, h1, h2, h3]
  ring

end IsCyclicTIPair

end CFSG.FeitThompson
