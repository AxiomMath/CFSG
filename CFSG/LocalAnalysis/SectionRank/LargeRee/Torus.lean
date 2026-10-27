module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Weyl
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.RelativeWeylTwist

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity

section Char

variable {τ : Tag} {K : Type} [Field K] [Finite K]

@[expose] noncomputable def simpleChar (g : adjointGroup τ K) (i : Fin τ.rank) : K :=
  ((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single (.inr (simpleRoot τ i)) 1)
    (.inr (simpleRoot τ i))

theorem apply_single_simpleRoot_of_mem_H
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) :
    ((h : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single (.inr (simpleRoot τ i)) 1) =
      simpleChar h i • Finsupp.single (.inr (simpleRoot τ i)) 1 := by
  obtain ⟨μ, hμ⟩ := exists_apply_single_eq_smul_of_mem_H hh (.inr (simpleRoot τ i))
  have : simpleChar h i = μ := by simp [simpleChar, hμ]
  rw [this, hμ]

omit [Finite K] in
theorem yOp_rootVec_single'
    (i : Fin τ.rank) (c : K) :
    yOp τ K i c (rootVec τ K (Pi.single i 1)) =
      rootVec τ K (Pi.single i 1) + c • hVec τ K i + c ^ 2 • rootVec τ K (-Pi.single i 1) := by
  have hne : (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := fun h => by
    simpa using congrFun h i
  rw [rootVec_eq_single (isRoot_single τ i), yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right hne).trans (ite_eq_left rfl)

theorem simpleChar_mul_neg_eq_one
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) {μ' : K}
    (h₂ : ((h : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single (.inr (-simpleRoot τ i)) 1) =
        μ' • Finsupp.single (.inr (-simpleRoot τ i)) 1) : simpleChar h i * μ' = 1 :=
  mul_eq_one_of_mem_H_simple hh i (apply_single_simpleRoot_of_mem_H hh i) h₂

theorem simpleChar_ne_zero
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) : simpleChar h i ≠ 0 := by
  obtain ⟨μ', h₂⟩ := exists_apply_single_eq_smul_of_mem_H hh (.inr (-simpleRoot τ i))
  exact left_ne_zero_of_mul_eq_one (simpleChar_mul_neg_eq_one hh i h₂)

theorem conj_xElement_of_mem_H
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) (c : K) : h * xElement i c * h⁻¹ = xElement i (simpleChar h i * c) := by
  classical
  set F := nativeRootSubgroups τ K
  have hx : xElement i c ∈ F.X (simpleRoot τ i) := (F.mem_simple i _).2 ⟨c, rfl⟩
  obtain ⟨c', hc'⟩ := (F.mem_simple i _).1 (conj_mem_X_of_mem_H hh hx)
  have hc : ((h : ModGL τ K) : Module.End K (RootModule τ K)) * xOp τ K i c =
      xOp τ K i c' * ((h : ModGL τ K) : Module.End K (RootModule τ K)) := by
    have hc'' := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))) hc'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_xUnit, xElement] at hc''
    rw [← hc'', mul_assoc _ ((((h : ModGL τ K))⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have h₁ := apply_single_simpleRoot_of_mem_H hh i
  obtain ⟨μ', h₂⟩ := exists_apply_single_eq_smul_of_mem_H hh (.inr (-simpleRoot τ i))
  have hμ := simpleChar_mul_neg_eq_one hh i h₂
  have e₁ : rootVec τ K (Pi.single i 1) = Finsupp.single (.inr (simpleRoot τ i)) 1 :=
    rootVec_eq_single (isRoot_single τ i)
  have e₂ : rootVec τ K (-Pi.single i 1) = Finsupp.single (.inr (-simpleRoot τ i)) 1 :=
    rootVec_eq_single (isRoot_neg_single τ i)
  rw [← e₁] at h₁
  rw [← e₂] at h₂
  have key := congrArg (fun f : Module.End K (RootModule τ K) =>
    f (rootVec τ K (-Pi.single i 1))) hc
  simp only [Module.End.mul_apply] at key
  rw [xOp_rootVec_neg_single', h₂, map_smul, xOp_rootVec_neg_single', map_add, map_add,
    map_smul, map_smul, apply_hVec_of_mem_H hh i, h₁, h₂] at key
  have hne : (-simpleRoot τ i : Root τ) ≠ simpleRoot τ i := fun h => by
    have := congrArg (fun α : Root τ => α.1 i) h
    simp [simpleRoot] at this
  have hk₁ := congrArg (fun x : RootModule τ K => x (Sum.inl i)) key
  simp only [e₁, e₂, hVec_eq_single, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, reduceCtorEq, ite_false, ite_true, mul_zero, mul_one, zero_add,
    add_zero] at hk₁
  have hc'eq : c' = simpleChar h i * c := by
    calc c' = (simpleChar h i * μ') * c' := by rw [hμ, one_mul]
      _ = simpleChar h i * c := by rw [mul_assoc, ← hk₁]
  apply Subtype.ext
  rw [hc', hc'eq]
  rfl

theorem conj_yElement_of_mem_H
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) (c : K) :
    h * yElement i c * h⁻¹ = yElement i ((simpleChar h i)⁻¹ * c) := by
  classical
  set F := nativeRootSubgroups τ K
  have hy : yElement i c ∈ F.X (-simpleRoot τ i) := (F.mem_neg_simple i _).2 ⟨c, rfl⟩
  obtain ⟨c', hc'⟩ := (F.mem_neg_simple i _).1 (conj_mem_X_of_mem_H hh hy)
  have hc : ((h : ModGL τ K) : Module.End K (RootModule τ K)) * yOp τ K i c =
      yOp τ K i c' * ((h : ModGL τ K) : Module.End K (RootModule τ K)) := by
    have hc'' := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))) hc'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_yUnit, yElement] at hc''
    rw [← hc'', mul_assoc _ ((((h : ModGL τ K))⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have h₁ := apply_single_simpleRoot_of_mem_H hh i
  obtain ⟨μ', h₂⟩ := exists_apply_single_eq_smul_of_mem_H hh (.inr (-simpleRoot τ i))
  have hμ := simpleChar_mul_neg_eq_one hh i h₂
  have hμ0 := simpleChar_ne_zero hh i
  have e₁ : rootVec τ K (Pi.single i 1) = Finsupp.single (.inr (simpleRoot τ i)) 1 :=
    rootVec_eq_single (isRoot_single τ i)
  have e₂ : rootVec τ K (-Pi.single i 1) = Finsupp.single (.inr (-simpleRoot τ i)) 1 :=
    rootVec_eq_single (isRoot_neg_single τ i)
  rw [← e₁] at h₁
  rw [← e₂] at h₂
  have key := congrArg (fun f : Module.End K (RootModule τ K) =>
    f (rootVec τ K (Pi.single i 1))) hc
  simp only [Module.End.mul_apply] at key
  rw [yOp_rootVec_single', h₁, map_smul, yOp_rootVec_single', map_add, map_add,
    map_smul, map_smul, apply_hVec_of_mem_H hh i, h₁, h₂] at key
  have hk₁ := congrArg (fun x : RootModule τ K => x (Sum.inl i)) key
  simp only [e₁, e₂, hVec_eq_single, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, reduceCtorEq, ite_false, ite_true, mul_zero, mul_one, zero_add,
    add_zero] at hk₁
  have hc'eq : c' = (simpleChar h i)⁻¹ * c := by
    rw [hk₁, ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]
  apply Subtype.ext
  rw [hc', hc'eq]
  rfl

omit [Finite K] in
theorem xElement_injective
    (i : Fin τ.rank) : Function.Injective (xElement (τ := τ) (K := K) i) :=
  fun c d h => eltElement_injective (simpleRoot τ i) (by rwa [eltElement_simpleRoot,
    eltElement_simpleRoot])

theorem simpleChar_eq_of_conj
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    {i : Fin τ.rank} {μ : K} (hμ : h * xElement i 1 * h⁻¹ = xElement i μ) : simpleChar h i = μ := by
  rw [conj_xElement_of_mem_H hh, mul_one] at hμ
  exact xElement_injective i hμ

theorem simpleChar_mul
    {h h' : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (hh' : h' ∈ (nativeData τ K).H) (i : Fin τ.rank) :
    simpleChar (h * h') i = simpleChar h i * simpleChar h' i := by
  refine simpleChar_eq_of_conj (mul_mem hh hh') ?_
  calc h * h' * xElement i 1 * (h * h')⁻¹ = h * (h' * xElement i 1 * h'⁻¹) * h⁻¹ := by group
    _ = xElement i (simpleChar h i * simpleChar h' i) := by
      rw [conj_xElement_of_mem_H hh', conj_xElement_of_mem_H hh, mul_one]

theorem simpleChar_inv
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H) (i : Fin τ.rank) :
    simpleChar h⁻¹ i = (simpleChar h i)⁻¹ := by
  have h1 := simpleChar_mul hh (inv_mem hh) i
  rw [mul_inv_cancel] at h1
  have h0 : simpleChar (1 : adjointGroup τ K) i = 1 := by simp [simpleChar]
  rw [h0] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

theorem eq_one_of_simpleChar_eq_one
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (h1 : ∀ i, simpleChar h i = 1) : h = 1 := by
  have hcomm : ∀ g ∈ adjointGroup τ K, g * (h : ModGL τ K) = (h : ModGL τ K) * g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, c, hgc | hgc⟩ := hg
      · have hgx : g = ((xElement i c : adjointGroup τ K) : ModGL τ K) := Units.ext hgc
        have := conj_xElement_of_mem_H hh i c
        rw [h1, one_mul] at this
        have h' := congrArg (fun z : adjointGroup τ K => (z : ModGL τ K)) this
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
        rw [hgx]
        calc ((xElement i c : adjointGroup τ K) : ModGL τ K) * (h : ModGL τ K) =
            (h : ModGL τ K) * (xElement i c : adjointGroup τ K) * (h : ModGL τ K)⁻¹ *
              (h : ModGL τ K) := by rw [h']
          _ = (h : ModGL τ K) * (xElement i c : adjointGroup τ K) := by group
      · have hgy : g = ((yElement i c : adjointGroup τ K) : ModGL τ K) := Units.ext hgc
        have := conj_yElement_of_mem_H hh i c
        rw [h1, inv_one, one_mul] at this
        have h' := congrArg (fun z : adjointGroup τ K => (z : ModGL τ K)) this
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
        rw [hgy]
        calc ((yElement i c : adjointGroup τ K) : ModGL τ K) * (h : ModGL τ K) =
            (h : ModGL τ K) * (yElement i c : adjointGroup τ K) * (h : ModGL τ K)⁻¹ *
              (h : ModGL τ K) := by rw [h']
          _ = (h : ModGL τ K) * (yElement i c : adjointGroup τ K) := by group
    | one => rw [one_mul, mul_one]
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx =>
      calc x⁻¹ * (h : ModGL τ K) = x⁻¹ * ((h : ModGL τ K) * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * (h : ModGL τ K)) * x⁻¹ := by rw [hx]
        _ = (h : ModGL τ K) * x⁻¹ := by group
  have hz : h ∈ Subgroup.center (adjointGroup τ K) := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (hcomm g g.2)
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  exact hz

theorem eq_of_simpleChar_eq
    {h h' : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (hh' : h' ∈ (nativeData τ K).H) (heq : ∀ i, simpleChar h i = simpleChar h' i) : h = h' := by
  have := eq_one_of_simpleChar_eq_one (mul_mem hh (inv_mem hh')) fun i => by
    rw [simpleChar_mul hh (inv_mem hh'), simpleChar_inv hh', heq,
      mul_inv_cancel₀ (simpleChar_ne_zero hh' i)]
  exact mul_inv_eq_one.1 this

theorem simpleChar_torusElement
    (j k : Fin τ.rank) (t : Kˣ) :
    simpleChar (torusElement τ K j t) k = ((t ^ τ.cartan j k : Kˣ) : K) := by
  refine simpleChar_eq_of_conj (torusElement_mem_H (nativeRootSubgroups τ K) j t) ?_
  rw [torusElement_conj_xElement, mul_one]

theorem simpleChar_nrep_conj
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (w : WeylGroup τ) (k : Fin τ.rank) {χ : K}
    (hχ : ∀ c, h * (rootOperatorFamily τ).eltElement (w⁻¹ • simpleRoot τ k) c * h⁻¹ =
      (rootOperatorFamily τ).eltElement (w⁻¹ • simpleRoot τ k) (χ * c)) :
    simpleChar (nrep τ K w * h * (nrep τ K w)⁻¹) k = χ := by
  set n := nrep τ K w
  have hnH : n * h * n⁻¹ ∈ (nativeData τ K).H := by
    simpa using RootGroupData.conj_mem_H (D := nativeData τ K)
      ⟨n, nrep_mem_monomialGroup τ K w⟩ hh
  obtain ⟨ε, hε, hconj⟩ := exists_conj_nrep (K := K) w (w⁻¹ • simpleRoot τ k)
  have hw : w • (w⁻¹ • simpleRoot τ k) = simpleRoot τ k := smul_inv_smul w _
  rw [hw] at hconj
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  refine simpleChar_eq_of_conj hnH ?_
  have h1 : xElement k 1 = n * (rootOperatorFamily τ).eltElement (w⁻¹ • simpleRoot τ k) ε *
      n⁻¹ := by rw [hconj, hε2, eltElement_simpleRoot]
  have h2 : xElement k χ = n * (rootOperatorFamily τ).eltElement (w⁻¹ • simpleRoot τ k)
      (χ * ε) * n⁻¹ := by
    rw [hconj, ← mul_assoc, mul_comm ε χ, mul_assoc, hε2, mul_one, eltElement_simpleRoot]
  rw [h1, h2]
  calc n * h * n⁻¹ * (n * (rootOperatorFamily τ).eltElement (w⁻¹ • simpleRoot τ k) ε * n⁻¹) *
        (n * h * n⁻¹)⁻¹ =
      n * (h * (rootOperatorFamily τ).eltElement (w⁻¹ • simpleRoot τ k) ε * h⁻¹) * n⁻¹ := by
        group
    _ = _ := by rw [hχ]

end Char

section Ree

abbrev fi (i : Fin 4) : Fin ReeTag.F4.tag.rank :=
  Fin.cast rfl i

theorem perm_fi_zero : ReeTag.F4.perm (fi 0) = fi 3 := by decide

theorem perm_fi_one : ReeTag.F4.perm (fi 1) = fi 2 := by decide

theorem fi_zero_mem_longSet : fi 0 ∈ ReeTag.F4.longSet := by decide

theorem fi_one_mem_longSet : fi 1 ∈ ReeTag.F4.longSet := by decide

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ)

theorem simpleChar_perm_of_mem_reeFixed
    {h : adjointGroup ReeTag.F4.tag K}
    (hh : h ∈ (nativeData ReeTag.F4.tag K).H) (hF : h ∈ reeFixed ReeTag.F4 K a)
    (k : Fin ReeTag.F4.tag.rank) :
    simpleChar h (ReeTag.F4.perm k) = simpleChar h k ^ ReeTag.F4.relationExponent a k := by
  have hFh : ReeTag.F4.reeAut K a h = h := (mem_reeFixed ReeTag.F4 K a).1 hF
  refine simpleChar_eq_of_conj hh ?_
  have := congrArg (ReeTag.F4.reeAut K a) (conj_xElement_of_mem_H hh k 1)
  rw [map_mul, map_mul, map_inv, hFh, ReeTag.reeAut_xElement, ReeTag.reeAut_xElement, one_pow,
    mul_one] at this
  exact this

theorem eq_of_simpleChar_eq_of_mem_reeFixed
    {h h' : adjointGroup ReeTag.F4.tag K}
    (hh : h ∈ (nativeData ReeTag.F4.tag K).H) (hF : h ∈ reeFixed ReeTag.F4 K a)
    (hh' : h' ∈ (nativeData ReeTag.F4.tag K).H) (hF' : h' ∈ reeFixed ReeTag.F4 K a)
    (h0 : simpleChar h (fi 0) = simpleChar h' (fi 0))
    (h1 : simpleChar h (fi 1) = simpleChar h' (fi 1)) : h = h' := by
  refine eq_of_simpleChar_eq hh hh' fun i => ?_
  have h3 : simpleChar h (fi 3) = simpleChar h' (fi 3) := by
    rw [← perm_fi_zero, simpleChar_perm_of_mem_reeFixed a hh hF,
      simpleChar_perm_of_mem_reeFixed a hh' hF', h0]
  have h2 : simpleChar h (fi 2) = simpleChar h' (fi 2) := by
    rw [← perm_fi_one, simpleChar_perm_of_mem_reeFixed a hh hF,
      simpleChar_perm_of_mem_reeFixed a hh' hF', h1]
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3

@[expose] def reeExp (j : Fin ReeTag.F4.tag.rank) (β : Fin ReeTag.F4.tag.rank → ℤ) : ℤ :=
  ReeTag.F4.cartanPair j β + ((ReeTag.F4.prime ^ a : ℕ) : ℤ) * ReeTag.F4.cartanPair
    (ReeTag.F4.perm j) β

omit [CharP K ReeTag.F4.prime] in
theorem simpleChar_reeTorus
    (j k : Fin ReeTag.F4.tag.rank) (u : Kˣ) :
    simpleChar (ReeTag.F4.reeTorus a j u) k =
      ((u ^ reeExp a j (Pi.single k 1) : Kˣ) : K) := by
  refine simpleChar_eq_of_conj (ReeTag.F4.reeTorus_mem_H a j u) ?_
  have := ReeTag.F4.reeTorus_conj a j u (simpleRoot ReeTag.F4.tag k) 1
  rwa [eltElement_simpleRoot, eltElement_simpleRoot, mul_one] at this

omit [CharP K ReeTag.F4.prime] in
theorem simpleChar_nrep_conj_reeTorus
    (w : WeylGroup ReeTag.F4.tag)
    (j k : Fin ReeTag.F4.tag.rank) (u : Kˣ) :
    simpleChar (nrep ReeTag.F4.tag K w * ReeTag.F4.reeTorus a j u *
        (nrep ReeTag.F4.tag K w)⁻¹) k =
      ((u ^ reeExp a j (w⁻¹ • Pi.single k 1) : Kˣ) : K) :=
  simpleChar_nrep_conj (ReeTag.F4.reeTorus_mem_H a j u) w k fun c =>
    ReeTag.F4.reeTorus_conj a j u _ c

omit [CharP K ReeTag.F4.prime] in
theorem reeTorus_mul
    (j : Fin ReeTag.F4.tag.rank) (u v : Kˣ) :
    ReeTag.F4.reeTorus a j (u * v) = ReeTag.F4.reeTorus a j u * ReeTag.F4.reeTorus a j v := by
  refine eq_of_simpleChar_eq (ReeTag.F4.reeTorus_mem_H a j _)
    (mul_mem (ReeTag.F4.reeTorus_mem_H a j u) (ReeTag.F4.reeTorus_mem_H a j v)) fun k => ?_
  rw [simpleChar_mul (ReeTag.F4.reeTorus_mem_H a j u) (ReeTag.F4.reeTorus_mem_H a j v),
    simpleChar_reeTorus, simpleChar_reeTorus, simpleChar_reeTorus, mul_zpow, Units.val_mul]

omit [CharP K ReeTag.F4.prime] in
theorem reeTorus_one
    (j : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.reeTorus a j (1 : Kˣ) = 1 := by
  have h := reeTorus_mul (K := K) a j 1 1
  rw [mul_one] at h
  exact (mul_eq_left.1 h.symm)

variable {a}

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem units_pow_card_sub_one (u : Kˣ) : u ^ (Nat.card K - 1) = 1 := by
  rw [← Nat.card_units]
  exact pow_card_eq_one'

omit [CharP K ReeTag.F4.prime] in
theorem units_zpow_one_add_mul (u : Kˣ) (m : ℤ) :
    u ^ (1 + m * ((Nat.card K : ℤ) - 1)) = u := by
  have hq : ((Nat.card K - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) - 1 := by
    have := Nat.card_pos (α := K)
    omega
  rw [zpow_add, zpow_one, show m * ((Nat.card K : ℤ) - 1) = ((Nat.card K - 1 : ℕ) : ℤ) * m by
    rw [hq]; ring, zpow_mul, zpow_natCast, units_pow_card_sub_one, one_zpow, mul_one]

theorem two_pow_eq_two_mul_sq (a : ℕ) :
    ((ReeTag.F4.prime ^ (2 * a + 1) : ℕ) : ℤ) = 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ) ^ 2 := by
  push_cast
  change (2 : ℤ) ^ (2 * a + 1) = 2 * (2 ^ a) ^ 2
  ring

theorem zpow_mul_zpow_zpow {G : Type*} [CommGroup G] (x y : G) (p r s t m n : ℤ) :
    (x ^ p * y ^ r) ^ m * (x ^ s * y ^ t) ^ n = x ^ (p * m + s * n) * y ^ (r * m + t * n) := by
  rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm,
    ← zpow_add, ← zpow_add]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem cartanPair_single (j k : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.cartanPair j (Pi.single k 1) = ReeTag.F4.tag.cartan j k := by
  simp [ReeTag.cartanPair, Pi.single_apply]

theorem cartan_F4_values :
    ReeTag.F4.tag.cartan (fi 0) (fi 0) = 2 ∧ ReeTag.F4.tag.cartan (fi 3) (fi 0) = 0 ∧
      ReeTag.F4.tag.cartan (fi 0) (fi 1) = -1 ∧ ReeTag.F4.tag.cartan (fi 3) (fi 1) = 0 ∧
        ReeTag.F4.tag.cartan (fi 1) (fi 0) = -1 ∧ ReeTag.F4.tag.cartan (fi 2) (fi 0) = 0 ∧
          ReeTag.F4.tag.cartan (fi 1) (fi 1) = 2 ∧ ReeTag.F4.tag.cartan (fi 2) (fi 1) = -2 := by
  decide

theorem reeExp_zero_zero : reeExp a (fi 0) (Pi.single (fi 0) 1) = 2 := by
  rw [reeExp, cartanPair_single, cartanPair_single, perm_fi_zero, cartan_F4_values.1,
    cartan_F4_values.2.1]
  ring

theorem reeExp_zero_one : reeExp a (fi 0) (Pi.single (fi 1) 1) = -1 := by
  rw [reeExp, cartanPair_single, cartanPair_single, perm_fi_zero, cartan_F4_values.2.2.1,
    cartan_F4_values.2.2.2.1]
  ring

theorem reeExp_one_zero : reeExp a (fi 1) (Pi.single (fi 0) 1) = -1 := by
  rw [reeExp, cartanPair_single, cartanPair_single, perm_fi_one, cartan_F4_values.2.2.2.2.1,
    cartan_F4_values.2.2.2.2.2.1]
  ring

theorem reeExp_one_one :
    reeExp a (fi 1) (Pi.single (fi 1) 1) = 2 - 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ) := by
  rw [reeExp, cartanPair_single, cartanPair_single, perm_fi_one,
    cartan_F4_values.2.2.2.2.2.2.1, cartan_F4_values.2.2.2.2.2.2.2]
  ring

theorem exists_eq_reeTorus_mul
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    {h : adjointGroup ReeTag.F4.tag K} (hh : h ∈ (nativeData ReeTag.F4.tag K).H)
    (hF : h ∈ reeFixed ReeTag.F4 K a) :
    ∃ u v : Kˣ, h = ReeTag.F4.reeTorus a (fi 0) u * ReeTag.F4.reeTorus a (fi 1) v := by
  set e : ℤ := ((ReeTag.F4.prime ^ a : ℕ) : ℤ) with he
  have hq : (Nat.card K : ℤ) = 2 * e ^ 2 := by
    rw [hK]
    exact two_pow_eq_two_mul_sq a
  set s : Kˣ := Units.mk0 (simpleChar h (fi 0)) (simpleChar_ne_zero hh _)
  set t : Kˣ := Units.mk0 (simpleChar h (fi 1)) (simpleChar_ne_zero hh _)
  set u : Kˣ := s ^ ((4 * e + 3) * (2 - 2 * e)) * t ^ (4 * e + 3)
  set v : Kˣ := s ^ (4 * e + 3) * t ^ (2 * (4 * e + 3))
  have hexp : (4 * e + 3) * (3 - 4 * e) = 1 + (-8) * ((Nat.card K : ℤ) - 1) := by
    rw [hq]; ring
  refine ⟨u, v, eq_of_simpleChar_eq_of_mem_reeFixed a hh hF
    (mul_mem (ReeTag.F4.reeTorus_mem_H a _ u) (ReeTag.F4.reeTorus_mem_H a _ v))
    (mul_mem (ReeTag.F4.reeTorus_mem_reeFixed a hK fi_zero_mem_longSet u)
      (ReeTag.F4.reeTorus_mem_reeFixed a hK fi_one_mem_longSet v)) ?_ ?_⟩
  · rw [simpleChar_mul (ReeTag.F4.reeTorus_mem_H a _ u) (ReeTag.F4.reeTorus_mem_H a _ v),
      simpleChar_reeTorus, simpleChar_reeTorus, reeExp_zero_zero, reeExp_one_zero,
      ← Units.val_mul, zpow_mul_zpow_zpow]
    have e1 : (4 * e + 3) * (2 - 2 * e) * 2 + (4 * e + 3) * -1 = (4 * e + 3) * (3 - 4 * e) := by
      ring
    have e2 : (4 * e + 3) * 2 + 2 * (4 * e + 3) * -1 = 0 := by ring
    rw [e1, e2, zpow_zero, mul_one, hexp, units_zpow_one_add_mul]
    rfl
  · rw [simpleChar_mul (ReeTag.F4.reeTorus_mem_H a _ u) (ReeTag.F4.reeTorus_mem_H a _ v),
      simpleChar_reeTorus, simpleChar_reeTorus, reeExp_zero_one, reeExp_one_one,
      ← Units.val_mul, zpow_mul_zpow_zpow, ← he]
    have e1 : (4 * e + 3) * (2 - 2 * e) * -1 + (4 * e + 3) * (2 - 2 * e) = 0 := by ring
    have e2 : (4 * e + 3) * -1 + 2 * (4 * e + 3) * (2 - 2 * e) = (4 * e + 3) * (3 - 4 * e) := by
      ring
    rw [e1, e2, zpow_zero, one_mul, hexp, units_zpow_one_add_mul]
    rfl

variable (a) in
@[expose] noncomputable def reeTorusHom
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    {j : Fin ReeTag.F4.tag.rank} (hj : j ∈ ReeTag.F4.longSet) :
    Kˣ →* reeFixed ReeTag.F4 K a where
  toFun u := ⟨ReeTag.F4.reeTorus a j u, ReeTag.F4.reeTorus_mem_reeFixed a hK hj u⟩
  map_one' := Subtype.ext (reeTorus_one a j)
  map_mul' u v := Subtype.ext (reeTorus_mul a j u v)

@[simp] theorem coe_reeTorusHom
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    {j : Fin ReeTag.F4.tag.rank} (hj : j ∈ ReeTag.F4.longSet) (u : Kˣ) :
    ((reeTorusHom a hK hj u : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) =
      ReeTag.F4.reeTorus a j u :=
  rfl

variable (a) in
@[expose] noncomputable def reeTorusSub
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    {j : Fin ReeTag.F4.tag.rank} (hj : j ∈ ReeTag.F4.longSet) : Subgroup (reeFixed ReeTag.F4 K a) :=
  (reeTorusHom a hK hj).range

instance
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) {j : Fin ReeTag.F4.tag.rank}
    (hj : j ∈ ReeTag.F4.longSet) : IsCyclic (reeTorusSub a hK hj) :=
  isCyclic_of_surjective (reeTorusHom a hK hj).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

theorem reeTorusSub_le_reeTorusPart
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    {j : Fin ReeTag.F4.tag.rank} (hj : j ∈ ReeTag.F4.longSet) :
    reeTorusSub a hK hj ≤ reeTorusPart ReeTag.F4 K a := by
  rintro _ ⟨u, rfl⟩
  exact ReeTag.F4.reeTorus_mem_H a j u

theorem reeTorusSub_inf
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    reeTorusSub a hK fi_zero_mem_longSet ⊓ reeTorusSub a hK fi_one_mem_longSet = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
  rw [Subgroup.mem_bot]
  set e : ℤ := ((ReeTag.F4.prime ^ a : ℕ) : ℤ) with he
  have hq : (Nat.card K : ℤ) = 2 * e ^ 2 := by
    rw [hK]
    exact two_pow_eq_two_mul_sq a
  have hv' : ReeTag.F4.reeTorus a (fi 1) v = ReeTag.F4.reeTorus a (fi 0) u :=
    congrArg Subtype.val hv
  have c0 := congrArg (fun g => simpleChar g (fi 0)) hv'
  have c1 := congrArg (fun g => simpleChar g (fi 1)) hv'
  simp only [simpleChar_reeTorus, reeExp_zero_zero, reeExp_one_zero, reeExp_zero_one,
    reeExp_one_one] at c0 c1
  have c0' : v ^ (-1 : ℤ) = u ^ (2 : ℤ) := Units.ext c0
  have c1' : v ^ (2 - 2 * e) = u ^ (-1 : ℤ) := Units.ext c1
  have hv2 : v = u ^ (-2 : ℤ) := by
    calc v = (v ^ (-1 : ℤ))⁻¹ := by rw [zpow_neg_one, inv_inv]
      _ = (u ^ (2 : ℤ))⁻¹ := by rw [c0']
      _ = u ^ (-2 : ℤ) := by rw [← zpow_neg]
  rw [hv2, ← zpow_mul] at c1'
  have h3 : u ^ (4 * e - 3) = 1 := by
    calc u ^ (4 * e - 3) = u ^ (-2 * (2 - 2 * e)) * (u ^ (-1 : ℤ))⁻¹ := by
          rw [← zpow_neg, ← zpow_add]; ring_nf
      _ = 1 := by rw [c1', mul_inv_cancel]
  have hu : u = 1 := by
    have hexp : (4 * e - 3) * (-(4 * e + 3)) = 1 + (-8) * ((Nat.card K : ℤ) - 1) := by
      rw [hq]; ring
    rw [← units_zpow_one_add_mul u (-8), ← hexp, zpow_mul, h3, one_zpow]
  rw [hu, map_one]

theorem reeTorusPart_eq_sup
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    reeTorusPart ReeTag.F4 K a =
      reeTorusSub a hK fi_zero_mem_longSet ⊔ reeTorusSub a hK fi_one_mem_longSet := by
  refine le_antisymm (fun x hx => ?_) (sup_le (reeTorusSub_le_reeTorusPart hK _)
    (reeTorusSub_le_reeTorusPart hK _))
  obtain ⟨u, v, huv⟩ := exists_eq_reeTorus_mul hK hx x.2
  have : x = reeTorusHom a hK fi_zero_mem_longSet u * reeTorusHom a hK fi_one_mem_longSet v :=
    Subtype.ext huv
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨u, rfl⟩) (Subgroup.mem_sup_right ⟨v, rfl⟩)

theorem commute_of_mem_reeTorusPart
    {x y : reeFixed ReeTag.F4 K a}
    (hx : x ∈ reeTorusPart ReeTag.F4 K a) (hy : y ∈ reeTorusPart ReeTag.F4 K a) : Commute x y :=
  Subtype.ext (commute_of_mem_H hx hy)

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem blockElt_inv_smul
    (i : Fin ReeTag.F4.tag.rank) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    (ReeTag.F4.blockElt i)⁻¹ • v = (ReeTag.F4.reeOrbitWord i).foldr (reflect ReeTag.F4.tag) v := by
  rw [inv_eq_of_mul_eq_one_right (ReeTag.F4.blockElt_mul_self i), ReeTag.blockElt,
    CFSG.LieType.Chevalley.wordProd_smul]

theorem reeExp_eq (j : Fin ReeTag.F4.tag.rank) (v : Fin ReeTag.F4.tag.rank → ℤ) {c₀ c₁ : ℤ}
    (h₀ : ReeTag.F4.cartanPair j v = c₀) (h₁ : ReeTag.F4.cartanPair (ReeTag.F4.perm j) v = c₁) :
    reeExp a j v = c₀ + ((ReeTag.F4.prime ^ a : ℕ) : ℤ) * c₁ := by
  rw [reeExp, h₀, h₁]

theorem reeExp_reflections :
    reeExp a (fi 0) ((ReeTag.F4.blockElt (fi 0))⁻¹ • Pi.single (fi 0) 1) = -2 ∧
    reeExp a (fi 0) ((ReeTag.F4.blockElt (fi 0))⁻¹ • Pi.single (fi 1) 1) = 1 ∧
    reeExp a (fi 1) ((ReeTag.F4.blockElt (fi 0))⁻¹ • Pi.single (fi 0) 1) = 1 ∧
    reeExp a (fi 1) ((ReeTag.F4.blockElt (fi 0))⁻¹ • Pi.single (fi 1) 1) =
      1 - 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ) ∧
    reeExp a (fi 0) ((ReeTag.F4.blockElt (fi 1))⁻¹ • Pi.single (fi 0) 1) =
      -2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ) ∧
    reeExp a (fi 0) ((ReeTag.F4.blockElt (fi 1))⁻¹ • Pi.single (fi 1) 1) = 1 ∧
    reeExp a (fi 1) ((ReeTag.F4.blockElt (fi 1))⁻¹ • Pi.single (fi 0) 1) = 1 ∧
    reeExp a (fi 1) ((ReeTag.F4.blockElt (fi 1))⁻¹ • Pi.single (fi 1) 1) =
      2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ) - 2 := by
  simp only [blockElt_inv_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reeExp_eq _ _ (c₀ := -2) (c₁ := 0) (by decide +kernel) (by decide +kernel)]; ring
  · rw [reeExp_eq _ _ (c₀ := 1) (c₁ := 0) (by decide +kernel) (by decide +kernel)]; ring
  · rw [reeExp_eq _ _ (c₀ := 1) (c₁ := 0) (by decide +kernel) (by decide +kernel)]; ring
  · rw [reeExp_eq _ _ (c₀ := 1) (c₁ := -2) (by decide +kernel) (by decide +kernel)]; ring
  · rw [reeExp_eq _ _ (c₀ := 0) (c₁ := -2) (by decide +kernel) (by decide +kernel)]; ring
  · rw [reeExp_eq _ _ (c₀ := 1) (c₁ := 0) (by decide +kernel) (by decide +kernel)]; ring
  · rw [reeExp_eq _ _ (c₀ := 1) (c₁ := 0) (by decide +kernel) (by decide +kernel)]; ring
  · rw [reeExp_eq _ _ (c₀ := -2) (c₁ := 2) (by decide +kernel) (by decide +kernel)]; ring

theorem nrep_conj_reeTorus_eq
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    {w : WeylGroup ReeTag.F4.tag} (hw : w ∈ ReeTag.F4.relWeylRee) {j : Fin ReeTag.F4.tag.rank}
    (hj : j ∈ ReeTag.F4.longSet) (u : Kˣ) {g : adjointGroup ReeTag.F4.tag K}
    (hgH : g ∈ (nativeData ReeTag.F4.tag K).H) (hgF : g ∈ reeFixed ReeTag.F4 K a)
    (h0 : simpleChar g (fi 0) = ((u ^ reeExp a j (w⁻¹ • Pi.single (fi 0) 1) : Kˣ) : K))
    (h1 : simpleChar g (fi 1) = ((u ^ reeExp a j (w⁻¹ • Pi.single (fi 1) 1) : Kˣ) : K)) :
    nrep ReeTag.F4.tag K w * ReeTag.F4.reeTorus a j u * (nrep ReeTag.F4.tag K w)⁻¹ = g := by
  have hH : nrep ReeTag.F4.tag K w * ReeTag.F4.reeTorus a j u * (nrep ReeTag.F4.tag K w)⁻¹ ∈
      (nativeData ReeTag.F4.tag K).H := by
    simpa using RootGroupData.conj_mem_H (D := nativeData ReeTag.F4.tag K)
      ⟨nrep ReeTag.F4.tag K w, nrep_mem_monomialGroup _ K w⟩ (ReeTag.F4.reeTorus_mem_H a j u)
  have hF : nrep ReeTag.F4.tag K w * ReeTag.F4.reeTorus a j u * (nrep ReeTag.F4.tag K w)⁻¹ ∈
      reeFixed ReeTag.F4 K a :=
    mul_mem (mul_mem (nrep_mem_reeFixed ReeTag.F4 K a hw)
      (ReeTag.F4.reeTorus_mem_reeFixed a hK hj u)) (inv_mem (nrep_mem_reeFixed ReeTag.F4 K a hw))
  refine eq_of_simpleChar_eq_of_mem_reeFixed a hH hF hgH hgF ?_ ?_
  · rw [simpleChar_nrep_conj_reeTorus, h0]
  · rw [simpleChar_nrep_conj_reeTorus, h1]

theorem fi_zero_eq : fi 0 = (0 : Fin 4) := rfl

theorem fi_one_eq : fi 1 = (1 : Fin 4) := rfl

theorem torus_reflections
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (u : Kˣ) :
    nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 0)) * ReeTag.F4.reeTorus a (fi 0) u *
        (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 0)))⁻¹ = (ReeTag.F4.reeTorus a (fi 0) u)⁻¹ ∧
    nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 0)) * ReeTag.F4.reeTorus a (fi 1) u *
        (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 0)))⁻¹ =
      ReeTag.F4.reeTorus a (fi 1) u * ReeTag.F4.reeTorus a (fi 0) u ∧
    nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) * ReeTag.F4.reeTorus a (fi 1) u *
        (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)))⁻¹ = (ReeTag.F4.reeTorus a (fi 1) u)⁻¹ ∧
    nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) * ReeTag.F4.reeTorus a (fi 0) u *
        (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)))⁻¹ =
      ReeTag.F4.reeTorus a (fi 0) u *
        ReeTag.F4.reeTorus a (fi 1) (u ^ (2 + 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ))) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := reeExp_reflections (a := a)
  set e : ℤ := ((ReeTag.F4.prime ^ a : ℕ) : ℤ) with he
  have hq : (Nat.card K : ℤ) = 2 * e ^ 2 := by
    rw [hK]
    exact two_pow_eq_two_mul_sq a
  have hz0 := ReeTag.reeOrbitWord_mem ReeTag.F4 (fi 0)
  have hz1 := ReeTag.reeOrbitWord_mem ReeTag.F4 (fi 1)
  have H0 := ReeTag.F4.reeTorus_mem_H (K := K) a (fi 0)
  have H1 := ReeTag.F4.reeTorus_mem_H (K := K) a (fi 1)
  have F0 := ReeTag.F4.reeTorus_mem_reeFixed (K := K) a hK fi_zero_mem_longSet
  have F1 := ReeTag.F4.reeTorus_mem_reeFixed (K := K) a hK fi_one_mem_longSet
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine nrep_conj_reeTorus_eq hK hz0 fi_zero_mem_longSet u (inv_mem (H0 u)) (inv_mem (F0 u))
      ?_ ?_
    · rw [simpleChar_inv (H0 u), simpleChar_reeTorus, reeExp_zero_zero, r1,
        ← Units.val_inv_eq_inv_val, ← zpow_neg]
    · rw [simpleChar_inv (H0 u), simpleChar_reeTorus, reeExp_zero_one, r2,
        ← Units.val_inv_eq_inv_val, ← zpow_neg, neg_neg]
  · refine nrep_conj_reeTorus_eq hK hz0 fi_one_mem_longSet u (mul_mem (H1 u) (H0 u))
      (mul_mem (F1 u) (F0 u)) ?_ ?_
    · rw [simpleChar_mul (H1 u) (H0 u), simpleChar_reeTorus, simpleChar_reeTorus,
        reeExp_one_zero, reeExp_zero_zero, r3, ← Units.val_mul, ← zpow_add]
      norm_num
    · rw [simpleChar_mul (H1 u) (H0 u), simpleChar_reeTorus, simpleChar_reeTorus,
        reeExp_one_one, reeExp_zero_one, r4, ← Units.val_mul, ← zpow_add, ← he]
      congr 2
      ring
  · refine nrep_conj_reeTorus_eq hK hz1 fi_one_mem_longSet u (inv_mem (H1 u)) (inv_mem (F1 u))
      ?_ ?_
    · rw [simpleChar_inv (H1 u), simpleChar_reeTorus, reeExp_one_zero, r7,
        ← Units.val_inv_eq_inv_val, ← zpow_neg, neg_neg]
    · rw [simpleChar_inv (H1 u), simpleChar_reeTorus, reeExp_one_one, r8,
        ← Units.val_inv_eq_inv_val, ← zpow_neg, ← he]
      congr 2
      ring
  · refine nrep_conj_reeTorus_eq hK hz1 fi_zero_mem_longSet u (mul_mem (H0 u) (H1 _))
      (mul_mem (F0 u) (F1 _)) ?_ ?_
    · rw [simpleChar_mul (H0 u) (H1 _), simpleChar_reeTorus, simpleChar_reeTorus,
        reeExp_zero_zero, reeExp_one_zero, r5, ← zpow_mul, ← Units.val_mul, ← zpow_add]
      congr 2
      ring
    · rw [simpleChar_mul (H0 u) (H1 _), simpleChar_reeTorus, simpleChar_reeTorus,
        reeExp_zero_one, reeExp_one_one, r6, ← zpow_mul, ← Units.val_mul, ← zpow_add]
      have hexp : -1 + (2 + 2 * e) * (2 - 2 * e) = 1 + (-2) * ((Nat.card K : ℤ) - 1) := by
        rw [hq]; ring
      rw [hexp, units_zpow_one_add_mul, zpow_one]

theorem relNrepHom_inv_reeTorusSub
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    (∀ t ∈ reeTorusSub a hK fi_zero_mem_longSet,
      relNrepHom K a (blockGen 0) * t * (relNrepHom K a (blockGen 0))⁻¹ = t⁻¹) ∧
    ∀ t ∈ reeTorusSub a hK fi_one_mem_longSet,
      relNrepHom K a (blockGen 1) * t * (relNrepHom K a (blockGen 1))⁻¹ = t⁻¹ := by
  refine ⟨?_, ?_⟩ <;> rintro _ ⟨u, rfl⟩ <;> apply Subtype.ext
  · exact (torus_reflections hK u).1
  · exact (torus_reflections hK u).2.2.1

theorem relNrepHom_cross_reeTorusSub
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    (∀ t ∈ reeTorusSub a hK fi_one_mem_longSet,
      t⁻¹ * (relNrepHom K a (blockGen 0) * t * (relNrepHom K a (blockGen 0))⁻¹) ∈
        reeTorusSub a hK fi_zero_mem_longSet) ∧
    ∀ t ∈ reeTorusSub a hK fi_zero_mem_longSet,
      t⁻¹ * (relNrepHom K a (blockGen 1) * t * (relNrepHom K a (blockGen 1))⁻¹) ∈
        reeTorusSub a hK fi_one_mem_longSet := by
  refine ⟨?_, ?_⟩ <;> rintro _ ⟨u, rfl⟩
  · refine ⟨u, Subtype.ext ?_⟩
    change ReeTag.F4.reeTorus a (fi 0) u = (ReeTag.F4.reeTorus a (fi 1) u)⁻¹ *
      (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 0)) * ReeTag.F4.reeTorus a (fi 1) u *
        (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 0)))⁻¹)
    rw [(torus_reflections hK u).2.1, inv_mul_cancel_left]
  · refine ⟨u ^ (2 + 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ)), Subtype.ext ?_⟩
    change ReeTag.F4.reeTorus a (fi 1) _ = (ReeTag.F4.reeTorus a (fi 0) u)⁻¹ *
      (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) * ReeTag.F4.reeTorus a (fi 0) u *
        (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)))⁻¹)
    rw [(torus_reflections hK u).2.2.2, inv_mul_cancel_left]

end Ree

end CFSG.SectionRank.LargeRee
