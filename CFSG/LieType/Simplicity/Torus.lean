module

public import CFSG.LieType.Ree.ReeHolds
public import CFSG.LieType.Chevalley.TorusCentralizer

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk
  CFSG.LieType.Ree

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem exists_mul_xOp_eq_of_mem_H
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) : ∃ c : K, ((h : ModGL τ K) : Module.End K (RootModule τ K)) * xOp τ K i 1 =
      xOp τ K i c * ((h : ModGL τ K) : Module.End K (RootModule τ K)) := by
  set F := nativeRootSubgroups τ K
  obtain ⟨x, hx⟩ : ∃ x : adjointGroup τ K, (x : ModGL τ K) = xUnit τ K i 1 :=
    ⟨⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩, rfl⟩
  have hxX : x ∈ F.X (simpleRoot τ i) := (F.mem_simple i x).mpr ⟨1, hx⟩
  obtain ⟨c, hc⟩ := (F.mem_simple i _).mp (conj_mem_X_of_mem_H hh hxX)
  have hc' := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))) hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hx, coe_xUnit] at hc'
  refine ⟨c, ?_⟩
  rw [← hc', mul_assoc _ ((((h : ModGL τ K))⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)),
    ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

theorem exists_apply_single_eq_smul_of_mem_H
    {h : adjointGroup τ K}
    (hh : h ∈ (nativeData τ K).H) (b : Label τ) : ∃ μ : K,
      ((h : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) =
        μ • Finsupp.single b 1 := by
  rcases b with i | ⟨α, hα⟩
  · obtain ⟨c, hc⟩ := exists_mul_xOp_eq_of_mem_H hh i
    exact exists_apply_hVec_eq_smul (preservesWeights_of_mem_H hh) i hc
  · have := (preservesWeights_of_mem_H hh).apply_rootVec (K := K) hα
    rw [rootVec_eq_single hα] at this
    exact ⟨_, this⟩

theorem commute_of_mem_H
    {h h' : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (hh' : h' ∈ (nativeData τ K).H) : Commute h h' := by
  show h * h' = h' * h
  refine Subtype.ext (Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_))
  obtain ⟨μ, hμ⟩ := exists_apply_single_eq_smul_of_mem_H hh b
  obtain ⟨μ', hμ'⟩ := exists_apply_single_eq_smul_of_mem_H hh' b
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Subgroup.coe_mul, Units.val_mul,
    Module.End.mul_apply, hμ, hμ', map_smul, smul_smul, mul_comm]

theorem H_inf_U_eq_bot
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (nativeData τ K).H ⊓ (nativeData τ K).U = ⊥ := by
  have hU : IsPGroup p (nativeData τ K).U := (nativeRootSubgroups τ K).isPGroup_U p
  have hH : Nat.Coprime (Nat.card (nativeData τ K).H) p :=
    (nativeRootSubgroups τ K).coprime_card_H p
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hU
  refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hn]
  exact Nat.Coprime.pow_right n hH

theorem exists_mul_of_mem_B
    {b : adjointGroup τ K} (hb : b ∈ (nativeData τ K).B) :
    ∃ u ∈ (nativeData τ K).U, ∃ h ∈ (nativeData τ K).H, b = u * h := by
  obtain ⟨h, hh, u, hu, rfl⟩ := RootGroupData.exists_mul_of_mem_B hb
  refine ⟨h * u * h⁻¹, ?_, h, hh, by group⟩
  exact (Subgroup.mem_normalizer_iff.mp (RootGroupData.H_le_normalizer_U hh) u).mp hu

theorem isSolvable_B
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Group.IsSolvable (nativeData τ K).B := by
  set D := nativeData τ K
  set N : Subgroup D.B := D.U.subgroupOf D.B
  have : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer RootGroupData.U_le_B).2
      (nativeRootSubgroups τ K).B_le_normalizer_U
  have hN : IsPGroup p N :=
    ((nativeRootSubgroups τ K).isPGroup_U p).comap_of_injective _ Subtype.val_injective
  have : Group.IsSolvable N := by
    have := hN.isNilpotent
    infer_instance
  have hmod : ∀ x : D.B, ∃ h : D.B, (h : adjointGroup τ K) ∈ D.H ∧ (x : D.B ⧸ N) = h := by
    intro x
    obtain ⟨h, hh, u, hu, hx⟩ := RootGroupData.exists_mul_of_mem_B x.2
    refine ⟨⟨h, RootGroupData.H_le_B hh⟩, hh, QuotientGroup.eq.2 ?_⟩
    rw [Subgroup.mem_subgroupOf]
    have e : ((x⁻¹ * ⟨h, RootGroupData.H_le_B hh⟩ : D.B) : adjointGroup τ K) = u⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hx]
      group
    rw [e]
    exact inv_mem hu
  have : Group.IsSolvable (D.B ⧸ N) := by
    refine Group.isSolvable_of_comm fun x y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨h, hh, hx⟩ := hmod x
    obtain ⟨h', hh', hy⟩ := hmod y
    rw [hx, hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (commute_of_mem_H hh hh').eq)
  exact Group.isSolvable_of_subgroup_quotient N

variable (τ) in
@[expose] def hStepLin (i : Fin τ.rank) : Module.End ℤ (Fin τ.rank → ℤ) where
  toFun := hStep τ i
  map_add' c d := by
    simp only [hStep, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
    abel
  map_smul' z c := by
    have hs : ∑ j, ((τ.cartan j i).natAbs : ℤ) * (z • c) j =
        z * ∑ j, ((τ.cartan j i).natAbs : ℤ) * c j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]; ring
    simp only [hStep, hs, RingHom.id_apply, smul_sub, smul_smul]

variable (τ) in
@[expose] def hStepCheck : Bool :=
  (List.finRange τ.rank).all fun i => (List.finRange τ.rank).all fun j =>
    (List.finRange τ.rank).all fun k =>
      List.ofFn ((fun c => hStep τ i (hStep τ j c))^[braidLength (τ.cartan i j * τ.cartan j i)]
        (Pi.single k 1)) == List.ofFn (Pi.single k 1 : Fin τ.rank → ℤ)

theorem hStepCheck_eq_true : ∀ τ : Tag, hStepCheck τ = true
  | .G2 => by decide +kernel
  | .F4 => by decide +kernel
  | .D4 => by decide +kernel
  | .E6 => by decide +kernel
  | .E7 => by decide +kernel
  | .E8 => by decide +kernel

theorem iterate_hStep_single (i j k : Fin τ.rank) :
    (fun c => hStep τ i (hStep τ j c))^[braidLength (τ.cartan i j * τ.cartan j i)]
      (Pi.single k 1) = Pi.single k 1 := by
  have h := hStepCheck_eq_true τ
  simp only [hStepCheck, List.all_eq_true, List.mem_finRange, true_implies] at h
  exact List.ofFn_injective (eq_of_beq (h i j k))

theorem isLiftable_hStepLin :
    (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).IsLiftable (hStepLin τ) := by
  intro i j
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    coxeterOrder_eq_braidLength]
  refine LinearMap.pi_ext fun k x => ?_
  have h1 : ((hStepLin τ i * hStepLin τ j) ^ braidLength (τ.cartan i j * τ.cartan j i))
      (Pi.single k 1) = Pi.single k 1 := by
    rw [Module.End.pow_apply]
    exact iterate_hStep_single i j k
  rw [show (Pi.single k x : Fin τ.rank → ℤ) = x • Pi.single k 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, map_smul, h1, Module.End.one_apply]

variable (τ) in
@[expose] noncomputable def cartanAction
    : WeylGroup τ →* Module.End ℤ (Fin τ.rank → ℤ) :=
  (coxeterSystem τ).lift ⟨hStepLin τ, isLiftable_hStepLin⟩

theorem cartanAction_simple
    (i : Fin τ.rank) : cartanAction τ (simple τ i) = hStepLin τ i :=
  (coxeterSystem τ).lift_apply_simple isLiftable_hStepLin i

omit [Finite K] in
theorem torusElt_hVecSum
    (i : Fin τ.rank) (t : Kˣ) (c : Fin τ.rank → ℤ) :
    (torusElt τ K i t : Module.End K (RootModule τ K)) (hVecSum K c) = hVecSum K c := by
  simp only [hVecSum, map_sum, map_smul, torusElt_hVec]

theorem apply_hVecSum_of_mem_monomialGroup
    {m : adjointGroup τ K} (hm : m ∈ monomialGroup τ K)
    (c : Fin τ.rank → ℤ) :
    ((m : ModGL τ K) : Module.End K (RootModule τ K)) (hVecSum K c) =
      hVecSum K (cartanAction τ (weylHom τ K ⟨m, hm⟩) c) := by
  induction hm using Subgroup.closure_induction generalizing c with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨⟨i, t⟩, rfl⟩
    · rw [weylHom_weylElement, cartanAction_simple]
      exact weylElt_hVecSum i 1 c
    · rw [weylHom_torusElement, map_one, Module.End.one_apply]
      exact torusElt_hVecSum i t c
  | one =>
    have h1 : weylHom τ K ⟨1, one_mem _⟩ = 1 := map_one _
    rw [h1, map_one, Module.End.one_apply]
    rfl
  | mul x y hx hy ihx ihy =>
    have hxy : weylHom τ K ⟨x * y, mul_mem (show x ∈ monomialGroup τ K from hx)
        (show y ∈ monomialGroup τ K from hy)⟩ =
        weylHom τ K ⟨x, hx⟩ * weylHom τ K ⟨y, hy⟩ := by
      rw [← map_mul]
      rfl
    rw [hxy, map_mul, Module.End.mul_apply, ← ihx, ← ihy]
    rfl
  | inv x hx ihx =>
    have hinv : weylHom τ K ⟨x⁻¹, inv_mem (show x ∈ monomialGroup τ K from hx)⟩ =
        (weylHom τ K ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [hinv]
    have h := ihx (cartanAction τ (weylHom τ K ⟨x, hx⟩)⁻¹ c)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [← h, ← Module.End.mul_apply, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply]

theorem apply_hVec_of_mem_H
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) :
    ((h : ModGL τ K) : Module.End K (RootModule τ K)) (hVec τ K i) = hVec τ K i := by
  obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := (RootGroupData.mem_H_iff (D := nativeData τ K)).mp hh
  have hkN' : k ∈ monomialGroup τ K := hkN
  have hk' : weylHom τ K ⟨k, hkN'⟩ = 1 := hk
  rw [← hVecSum_single, apply_hVecSum_of_mem_monomialGroup hkN', hk', map_one,
    Module.End.one_apply]

theorem exists_apply_single_inr_eq_smul
    (m : monomialGroup τ K) (β : Root τ) :
    ∃ c : K, (((m : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single (.inr β) 1) = c • Finsupp.single (.inr (weylHom τ K m • β)) 1 := by
  classical
  refine ⟨(((m : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K))
    (Finsupp.single (.inr β) 1) (.inr (weylHom τ K m • β)), ?_⟩
  ext a
  rw [Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs with ha
  · subst ha
    simp
  · rw [smul_zero]
    by_contra hne
    have h1 := labelWt_eq_of_monomial m hne
    rcases a with k | γ
    · exact (IsRoot.smul β.2 (weylHom τ K m)).ne_zero h1.symm
    · exact ha (congrArg Sum.inr (Subtype.ext h1.symm))

theorem conj_apply_single_inr
    (m : monomialGroup τ K) (h : adjointGroup τ K) (β : Root τ)
    {μ : K} (hμ : ((h : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single (.inr (weylHom τ K m • β)) 1) =
        μ • Finsupp.single (.inr (weylHom τ K m • β)) 1) :
    ((((m : adjointGroup τ K)⁻¹ * h * m : adjointGroup τ K) : ModGL τ K) :
      Module.End K (RootModule τ K)) (Finsupp.single (.inr β) 1) =
        μ • Finsupp.single (.inr β) 1 := by
  obtain ⟨c, hc⟩ := exists_apply_single_inr_eq_smul m β
  have key : ((h : ModGL τ K) : Module.End K (RootModule τ K))
      ((((m : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K))
        (Finsupp.single (.inr β) 1)) =
      μ • (((m : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K))
        (Finsupp.single (.inr β) 1) := by
    rw [hc, map_smul, hμ, smul_comm]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Module.End.mul_apply, key,
    map_smul]
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem mul_eq_one_of_mem_H_simple
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) {μ μ' : K}
    (h₁ : ((h : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single (.inr (simpleRoot τ i)) 1) = μ • Finsupp.single (.inr (simpleRoot τ i)) 1)
    (h₂ : ((h : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single (.inr (-simpleRoot τ i)) 1) =
        μ' • Finsupp.single (.inr (-simpleRoot τ i)) 1) : μ * μ' = 1 := by
  classical
  have e₁ : rootVec τ K (Pi.single i 1) = Finsupp.single (.inr (simpleRoot τ i)) 1 :=
    rootVec_eq_single (isRoot_single τ i)
  have e₂ : rootVec τ K (-Pi.single i 1) = Finsupp.single (.inr (-simpleRoot τ i)) 1 :=
    rootVec_eq_single (isRoot_neg_single τ i)
  rw [← e₁] at h₁
  rw [← e₂] at h₂
  obtain ⟨c, hc⟩ := exists_mul_xOp_eq_of_mem_H hh i
  have key := congrArg (fun f : Module.End K (RootModule τ K) =>
    f (rootVec τ K (-Pi.single i 1))) hc
  simp only [Module.End.mul_apply] at key
  rw [xOp_rootVec_neg_single', h₂, map_smul, xOp_rootVec_neg_single', map_add, map_add,
    map_smul, map_smul, apply_hVec_of_mem_H hh i, h₁, h₂, one_smul, one_pow, one_smul] at key
  have hne : (-simpleRoot τ i : Root τ) ≠ simpleRoot τ i := fun h => by
    have := congrArg (fun α : Root τ => α.1 i) h
    simp [simpleRoot] at this
  have hk₁ := congrArg (fun x : RootModule τ K => x (Sum.inl i)) key
  have hk₂ := congrArg (fun x : RootModule τ K => x (Sum.inr (simpleRoot τ i))) key
  simp only [e₁, e₂, hVec_eq_single, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, reduceCtorEq, ite_false, ite_true, Sum.inr.injEq, hne, mul_zero,
    mul_one, zero_add, add_zero] at hk₁ hk₂
  linear_combination μ' * hk₂ - (μ' * c + 1) * hk₁

theorem mul_eq_one_of_mem_H
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H) (α : Root τ)
    {μ μ' : K}
    (h₁ : ((h : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single (.inr α) 1) =
      μ • Finsupp.single (.inr α) 1)
    (h₂ : ((h : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single (.inr (-α)) 1) =
      μ' • Finsupp.single (.inr (-α)) 1) : μ * μ' = 1 := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 α.2
  obtain ⟨m, rfl⟩ := weylHom_surjective (τ := τ) (K := K) w
  have hα : α = weylHom τ K m • simpleRoot τ j := Subtype.ext hwj.symm
  have hh' : (m : adjointGroup τ K)⁻¹ * h * m ∈ (nativeData τ K).H := by
    simpa using RootGroupData.conj_mem_H (D := nativeData τ K)
      ⟨(m : adjointGroup τ K)⁻¹, inv_mem m.2⟩ hh
  refine mul_eq_one_of_mem_H_simple hh' j (conj_apply_single_inr m h _ ?_)
    (conj_apply_single_inr m h _ ?_)
  · rw [← hα]
    exact h₁
  · rw [smul_neg_root, ← hα]
    exact h₂

theorem nrep_conj_of_mem_H
    {w₀ : WeylGroup τ} (hw₀ : ∀ α : Root τ, (w₀ • α).1 = -α.1)
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H) :
    nrep τ K w₀ * h * (nrep τ K w₀)⁻¹ = h⁻¹ := by
  obtain ⟨n, hn, hφ⟩ : ∃ n : monomialGroup τ K, (n : adjointGroup τ K) = nrep τ K w₀ ∧
      weylHom τ K n = w₀ := ⟨_, rfl, weylHom_nrep τ K w₀⟩
  rw [← hn]
  have hinv : ∀ α : Root τ, weylHom τ K n⁻¹ • α = -α := fun α => by
    rw [map_inv, hφ]
    apply Subtype.ext
    have := hw₀ (w₀⁻¹ • α)
    rw [smul_inv_smul] at this
    change (w₀⁻¹ • α).1 = -α.1
    rw [this, neg_neg]
  have hh' : (n : adjointGroup τ K) * h * (n : adjointGroup τ K)⁻¹ ∈ (nativeData τ K).H :=
    RootGroupData.conj_mem_H (D := nativeData τ K) n hh
  refine Subtype.ext (Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_))
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with i | α
  · rw [← hVec_eq_single, apply_hVec_of_mem_H hh' i, apply_hVec_of_mem_H (inv_mem hh) i]
  · obtain ⟨μ, hμ⟩ := exists_apply_single_eq_smul_of_mem_H hh (.inr α)
    obtain ⟨μ', hμ'⟩ := exists_apply_single_eq_smul_of_mem_H hh (.inr (-α))
    have h1 : μ * μ' = 1 := mul_eq_one_of_mem_H hh α hμ hμ'
    have hL := conj_apply_single_inr n⁻¹ h α (μ := μ') (by rw [hinv]; exact hμ')
    rw [Subgroup.coe_inv, inv_inv] at hL
    have hR : (((h⁻¹ : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K))
        (Finsupp.single (.inr α) 1) = μ' • Finsupp.single (.inr α) 1 := by
      have e : (Finsupp.single (.inr α) 1 : RootModule τ K) =
          ((h : ModGL τ K) : Module.End K (RootModule τ K)) (μ' • Finsupp.single (.inr α) 1) := by
        rw [map_smul, hμ, smul_smul, mul_comm, h1, one_smul]
      conv_lhs => rw [e]
      rw [← Module.End.mul_apply, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Module.End.one_apply]
    exact hL.trans hR.symm

section Ree

variable {t : ReeTag} [CharP K t.prime] (a : ℕ)

theorem exists_mul_of_mem_B_of_mem_reeFixed
    {b : adjointGroup t.tag K}
    (hb : b ∈ (nativeData t.tag K).B) (hF : b ∈ reeFixed t K a) :
    ∃ u ∈ (nativeData t.tag K).U, u ∈ reeFixed t K a ∧
      ∃ h ∈ (nativeData t.tag K).H, h ∈ reeFixed t K a ∧ b = u * h := by
  obtain ⟨u, hu, h, hh, rfl⟩ := exists_mul_of_mem_B hb
  have hFu := ReeTag.reeAut_mem_U a hu
  have hFh := ReeTag.reeAut_mem_H a hh
  have hF' : t.reeAut K a u * t.reeAut K a h = u * h := by
    rw [← map_mul]
    exact hF
  have e : u⁻¹ * t.reeAut K a u = h * (t.reeAut K a h)⁻¹ := by
    calc u⁻¹ * t.reeAut K a u
        = u⁻¹ * (t.reeAut K a u * t.reeAut K a h) * (t.reeAut K a h)⁻¹ := by group
      _ = u⁻¹ * (u * h) * (t.reeAut K a h)⁻¹ := by rw [hF']
      _ = h * (t.reeAut K a h)⁻¹ := by group
  have hmem : u⁻¹ * t.reeAut K a u ∈ (nativeData t.tag K).H ⊓ (nativeData t.tag K).U :=
    Subgroup.mem_inf.2 ⟨by rw [e]; exact mul_mem hh (inv_mem hFh), mul_mem (inv_mem hu) hFu⟩
  rw [H_inf_U_eq_bot t.prime, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hu' : t.reeAut K a u = u := hmem.symm
  rw [hu'] at hF'
  exact ⟨u, hu, hu', h, hh, mul_left_cancel hF', rfl⟩

end Ree

end CFSG.LieType.Simplicity
