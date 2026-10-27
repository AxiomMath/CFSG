module

public import CFSG.ClassicalInvolution.Q3.Q3ExcGroup
public import CFSG.ClassicalInvolution.Q3.Q3ExcRoots
public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels
public import CFSG.LieType.HighestRoot.CentChevalleyThree
public import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.HighestRoot CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups commutatorElement

variable {τ : Tag} {K : Type} [Field K] [Finite K]

section Structure

theorem exc3_pow_four_mem_rootSpan (hK3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {x : ModGL τ K}
    (hx : x ∈ toralCentralizer τ K a) : x ^ 4 ∈ rootSpan τ K (rootCharKernel a) := by
  have h := sq_mem_rootSpan_of_mem_toralRootGroup hK3 (sq_mem_toralRootGroup hK ha hx)
  rwa [← pow_mul] at h

omit [Finite K] in
theorem exc3_mem_torusGroup_of_centralizes (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {x : ModGL τ K} (hxS : x ∈ rootSpan τ K (rootCharKernel a))
    (hxc : ∀ y ∈ rootSpan τ K (rootCharKernel a), x * y = y * x) : x ∈ torusGroup τ K := by
  set χ := maskChar (signTupleBits a) with hχ
  rw [rootCharKernel_eq_kernelRoots hK ha, ← iSup_componentRootSpan K (χ := χ)] at hxS hxc
  have : Finite (KernelComponent χ) :=
    (root_character_kernel_orthogonal_central_product τ K χ).2.1
  have hcomm : ∀ i j : KernelComponent χ, i ≠ j → ∀ a ∈ componentRootSpan K χ i,
      ∀ b ∈ componentRootSpan K χ j, a * b = b * a := by
    intro i j hij u hu v hv
    have h := commutator_componentRootSpan_eq_bot K (χ := χ) hij
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact (Subgroup.mem_centralizer_iff.mp (h hu) v hv).symm
  have h := exc3_center_le_iSup (fun i : KernelComponent χ => componentRootSpan K χ i) hcomm hxS hxc
  have hle : (⨆ i : KernelComponent χ, (componentRootSpan K χ i ⊓
      Subgroup.centralizer (componentRootSpan K χ i : Set (ModGL τ K)))) ≤ torusGroup τ K := by
    refine iSup_le fun i y hy => ?_
    have hyc : (⟨y, hy.1⟩ : componentRootSpan K χ i) ∈
        Subgroup.center (componentRootSpan K χ i) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 g g.2)
    exact componentTorus_le_torusGroup K χ i (coe_mem_componentTorus_of_mem_center hyc)
  exact hle h

theorem exc3_sq_eq_one_of_mem_center (hK3 : Nat.card K = 3)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} {i : KernelComponent χ}
    {x : componentRootSpan K χ i} (hx : x ∈ Subgroup.center (componentRootSpan K χ i)) :
    (x : ModGL τ K) ^ 2 = 1 :=
  sq_eq_one_of_mem_torusGroup hK3
    (componentTorus_le_torusGroup K χ i (coe_mem_componentTorus_of_mem_center hx))

omit [Finite K] in
theorem exc3_small_class (hK : ringChar K ≠ 2) (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ)
    (i : KernelComponent χ) (hi : ¬ 2 < (componentRoots χ i).ncard) :
    ∃ (α : Fin τ.rank → ℤ) (hα : α ∈ kernelRoots χ), i = ⟦⟨α, hα⟩⟧ ∧
      componentRoots χ i = {α, -α} ∧
      componentRootSpan K χ i = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ∧
      Nonempty (SL2 K ≃* componentRootSpan K χ i) := by
  induction i using Quotient.inductionOn with
  | h a =>
  obtain ⟨α, hα⟩ := a
  have hΨ := isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots χ ⟦⟨α, hα⟩⟧ :=
    Set.insert_subset hαΨ (Set.singleton_subset_iff.2 (hΨ.neg_mem α hαΨ))
  have hfin : (componentRoots χ ⟦⟨α, hα⟩⟧).Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ
  have hne : α ≠ -α := ne_neg_of_isRoot (hΨ.isRoot α hαΨ)
  have hcard : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard = 2 := Set.ncard_pair hne
  have heq : componentRoots χ ⟦⟨α, hα⟩⟧ = {α, -α} :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; omega) hfin).symm
  have hS : componentRootSpan K χ ⟦⟨α, hα⟩⟧ = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
    change rootSpan τ K (componentRoots χ ⟦⟨α, hα⟩⟧) = _
    rw [heq, rootSpan_pair_eq]
  obtain ⟨-, ⟨eR⟩, -, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK (hΨ.isRoot α hαΨ)
  exact ⟨α, hα, rfl, heq, hS, ⟨eR.trans (MulEquiv.subgroupCongr hS.symm)⟩⟩

omit [Finite K] in
theorem exc3_nonempty_equiv_sl2Three (hK3 : Nat.card K = 3) {J : Type*} [Group J]
    (e : SL2 K ≃* J) : Nonempty (SL(2, ZMod 3) ≃* J) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK3]; norm_num)
  exact ⟨(slEquivSL23 hK3).symm.trans e⟩

theorem exc3_false_of_involution_mem_odd {G : Type*} [Group G] {M : Subgroup G}
    (hodd : Odd (Nat.card M)) {x : G} (hx : x ∈ M) (h2 : orderOf x = 2) : False := by
  have h := Subgroup.orderOf_dvd_natCard M hx
  rw [h2] at h
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem exc3_inf_class_eq_bot (hK3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ)
    {M : Subgroup (ModGL τ K)} (hodd : Odd (Nat.card M))
    (hMn : ∀ a ∈ componentRootSpan K χ i, ∀ m ∈ M, a * m * a⁻¹ ∈ M) :
    M ⊓ componentRootSpan K χ i = ⊥ := by
  set A := componentRootSpan K χ i with hA
  have hN : ((M ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnM, hnA⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa using hMn g g.2 n hnM
    · simpa using mul_mem (mul_mem g.2 hnA) (inv_mem g.2)
  have hodd' : ∀ y ∈ M, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard M hy)
  by_cases hbig : 2 < (componentRoots χ i).ncard
  · have hq : CFSG.IsQuasisimple A := (odd_sign_root_component_quasisimple τ K χ i).2.2 hK hbig
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hcen
    · exfalso
      obtain ⟨x, hx⟩ := exists_orderOf_eq_two_of_isQuasisimple (ModelFacts.open_isQuasisimple hq)
      have hxM : (x : ModGL τ K) ∈ M := by
        have : x ∈ (M ⊓ A).subgroupOf A := htop ▸ Subgroup.mem_top x
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).1
      exact exc3_false_of_involution_mem_odd hodd hxM
        (by rw [← hx, Subgroup.orderOf_coe])
    · refine eq_bot_iff.mpr fun y hy => ?_
      rw [Subgroup.mem_bot]
      have hyc : (⟨y, hy.2⟩ : A) ∈ Subgroup.center A := hcen (Subgroup.mem_subgroupOf.2 hy)
      exact exc3_eq_one_of_sq_eq_one_of_odd (exc3_sq_eq_one_of_mem_center hK3 hyc) (hodd' y hy.1)
  · obtain ⟨α, hα, -, -, hS, ⟨eR⟩⟩ := exc3_small_class (K := K) hK χ i hbig
    obtain ⟨e⟩ := exc3_nonempty_equiv_sl2Three hK3 eR
    refine eq_bot_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot]
    by_contra hy1
    have hcard : Nat.card A = 24 := by
      rw [← Nat.card_congr e.toEquiv, natCard_sl2Three]
    have hord : orderOf y ∣ 24 := by
      have := Subgroup.orderOf_dvd_natCard A hy.2
      rwa [hcard] at this
    have hy3 : y ^ 3 = 1 := by
      have h3 : orderOf y ∣ 3 := by
        have hc : Nat.Coprime (orderOf y) 8 := by
          have := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr (hodd' y hy.1))
          simpa using this
        have h24 : orderOf y ∣ 3 * 8 := by simpa using hord
        exact (Nat.Coprime.dvd_of_dvd_mul_right hc h24)
      exact orderOf_dvd_iff_pow_eq_one.mp h3
    have htop := eq_top_of_normal_of_pow_three (B := A) e
      (N := (M ⊓ A).subgroupOf A) (fun x hx g => hN.conj_mem x hx g) (x := ⟨y, hy.2⟩)
      (Subgroup.mem_subgroupOf.2 hy) (Subtype.ext hy3 : (⟨y, hy.2⟩ : A) ^ 3 = 1)
      (fun h => hy1 (congrArg Subtype.val h))
    have h1 : (e (-1) : ModGL τ K) ∈ M := by
      have : (e (-1)) ∈ (M ⊓ A).subgroupOf A := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).1
    refine exc3_false_of_involution_mem_odd hodd h1 ?_
    have h2 := orderOf_injective e.toMonoidHom e.injective (-1)
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [Subgroup.orderOf_coe, h2]
    exact orderOf_neg_one_SL23


theorem exc3_oddNormal_eq_bot (hK3 : Nat.card K = 3) {b : Fin τ.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) {N : Subgroup (ModGL τ K)}
    (hNX : N ≤ toralCentralizer τ K b)
    (hNn : ∀ x ∈ toralCentralizer τ K b, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hK : ringChar K ≠ 2 := ringChar_ne_two_of_card_eq_three hK3
  set χ := maskChar (signTupleBits b) with hχ
  have hker : rootCharKernel b = kernelRoots χ := rootCharKernel_eq_kernelRoots hK hb
  have hSX : rootSpan τ K (rootCharKernel b) ≤ toralCentralizer τ K b :=
    rootSpan_rootCharKernel_le_toralCentralizer b
  set S := rootSpan τ K (rootCharKernel b) with hS
  have hSker : S = rootSpan τ K (kernelRoots χ) := by rw [hS, hker]
  set M := N ⊓ S with hM
  have hModd : Odd (Nat.card M) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  have hMn : ∀ s ∈ S, ∀ m ∈ M, s * m * s⁻¹ ∈ M := fun s hs m hm =>
    ⟨hNn s (hSX hs) m hm.1, S.mul_mem (S.mul_mem hs hm.2) (S.inv_mem hs)⟩
  have hMbot : M = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Subgroup.mem_bot]
    have hmS : m ∈ S := hm.2
    have hcls : ∀ i : KernelComponent χ, ∀ s ∈ componentRootSpan K χ i, m * s = s * m := by
      intro i s hs
      have hsS : s ∈ S := hSker ▸ componentRootSpan_le K i hs
      have hnorm : S ≤ Subgroup.normalizer (componentRootSpan K χ i : Set (ModGL τ K)) :=
        hSker ▸ rootSpan_le_normalizer K i
      have h1 : s * m * s⁻¹ * m⁻¹ ∈ M := M.mul_mem (hMn s hsS m hm) (M.inv_mem hm)
      have h2 : s * m * s⁻¹ * m⁻¹ ∈ componentRootSpan K χ i := by
        have h3 : m * s⁻¹ * m⁻¹ ∈ componentRootSpan K χ i :=
          (Subgroup.mem_normalizer_iff.1 (hnorm hmS) s⁻¹).1 ((componentRootSpan K χ i).inv_mem hs)
        have e : s * m * s⁻¹ * m⁻¹ = s * (m * s⁻¹ * m⁻¹) := by group
        rw [e]
        exact (componentRootSpan K χ i).mul_mem hs h3
      have h4 := exc3_inf_class_eq_bot hK3 hK χ i hModd (fun a ha x hx => hMn a (hSker ▸
        componentRootSpan_le K i ha) x hx)
      have h5 : s * m * s⁻¹ * m⁻¹ ∈ M ⊓ componentRootSpan K χ i := ⟨h1, h2⟩
      rw [h4, Subgroup.mem_bot] at h5
      have h6 : s * m = m * s := by
        have := congrArg (· * (m * s)) h5
        simp only [one_mul] at this
        calc s * m = s * m * s⁻¹ * m⁻¹ * (m * s) := by group
          _ = m * s := this
      exact h6.symm
    have hmc : ∀ y ∈ S, m * y = y * m := by
      intro y hy
      have hle : (⨆ i : KernelComponent χ, componentRootSpan K χ i) ≤
          Subgroup.centralizer ({m} : Set (ModGL τ K)) := by
        refine iSup_le fun i s hs => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcls i s hs).symm
      rw [iSup_componentRootSpan K (χ := χ), ← hSker] at hle
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
    have hmT := exc3_mem_torusGroup_of_centralizes hK hb hm.2 hmc
    exact exc3_eq_one_of_sq_eq_one_of_odd (sq_eq_one_of_mem_torusGroup hK3 hmT)
      (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hm.1))
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have h4 : n ^ 4 ∈ M := ⟨N.pow_mem hn 4, exc3_pow_four_mem_rootSpan hK3 hK hb (hNX hn)⟩
  rw [hMbot, Subgroup.mem_bot] at h4
  have hord : Odd (orderOf n) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hn)
  have h1 : orderOf n ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hc : Nat.Coprime (orderOf n) 4 := by
    have := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hord)
    simpa using this
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc h1)


omit [Finite K] in
theorem exc3_class_commute {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    {i j : KernelComponent χ} (hij : i ≠ j) :
    ∀ a ∈ componentRootSpan K χ i, ∀ b ∈ componentRootSpan K χ j, a * b = b * a := by
  intro u hu v hv
  have h := commutator_componentRootSpan_eq_bot K (χ := χ) hij
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact (Subgroup.mem_centralizer_iff.mp (h hu) v hv).symm

omit [Finite K] in
theorem exc3_classCenter_le_torus {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    (i : KernelComponent χ) :
    componentRootSpan K χ i ⊓ Subgroup.centralizer (componentRootSpan K χ i : Set (ModGL τ K)) ≤
      torusGroup τ K := by
  intro y hy
  have hyc : (⟨y, hy.1⟩ : componentRootSpan K χ i) ∈
      Subgroup.center (componentRootSpan K χ i) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 g g.2)
  exact componentTorus_le_torusGroup K χ i (coe_mem_componentTorus_of_mem_center hyc)

theorem exc3_centralizes_big_class (hK : ringChar K ≠ 2)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} (i : KernelComponent χ)
    (hi : 2 < (componentRoots χ i).ncard) {L : Subgroup (ModGL τ K)}
    (hLS : L ≤ rootSpan τ K (kernelRoots χ)) (hsub : IsSubnormal L (rootSpan τ K (kernelRoots χ)))
    (hsolv : Group.IsSolvable L) :
    ∀ x ∈ L, ∀ s ∈ componentRootSpan K χ i, x * s = s * x := by
  have : Finite (ModGL τ K) := finite_modGL
  set S := rootSpan τ K (kernelRoots χ) with hS
  have hSi : componentRootSpan K χ i ≤ S := componentRootSpan_le K i
  have hq : CFSG.IsQuasisimple (componentRootSpan K χ i) :=
    (odd_sign_root_component_quasisimple τ K χ i).2.2 hK hi
  have hnormal : ((componentRootSpan K χ i).subgroupOf S).Normal :=
    ((root_character_kernel_orthogonal_central_product τ K χ).2.2.2.1 i).2
  have hcomp : CFSG.IsComponent ((componentRootSpan K χ i).subgroupOf S) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSi).symm hq,
      hnormal.isSubnormal⟩
  have hLsn : (L.subgroupOf S).IsSubnormal := by
    have := isSubnormal_subgroupOf hsub S
    rw [Subgroup.subgroupOf_self] at this
    exact (CFSG.Adapters.isSubnormal_top_iff _).1 this
  have hLsolv : Group.IsSolvable (L.subgroupOf S) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLS).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLS).injective
  have h := (CFSG.LocalCores.component_solvable_centralizer hLsolv hLsn).1 _ hcomp
  intro x hx s hs
  have hm := Subgroup.commutator_mem_commutator
    (H₁ := (componentRootSpan K χ i).subgroupOf S) (H₂ := L.subgroupOf S)
    (g₁ := (⟨s, hSi hs⟩ : S)) (g₂ := (⟨x, hLS hx⟩ : S)) hs hx
  rw [h, Subgroup.mem_bot] at hm
  have h2 := congrArg Subtype.val hm
  have h3 : ⁅s, x⁆ = 1 := by simpa [commutatorElement_def] using h2
  exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm


omit [Finite K] in
theorem exc3_small_unique (hK : ringChar K ≠ 2) {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    (hU : UniqIsolated τ χ) (i j : KernelComponent χ) (hi : ¬ 2 < (componentRoots χ i).ncard)
    (hj : ¬ 2 < (componentRoots χ j).ncard) : i = j := by
  obtain ⟨α, hα, rfl, hαr, -⟩ := exc3_small_class (K := K) hK χ i hi
  obtain ⟨β, hβ, rfl, hβr, -⟩ := exc3_small_class (K := K) hK χ j hj
  have hiso : ∀ {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ),
      componentRoots χ ⟦⟨α, hα⟩⟧ = {α, -α} →
      ∀ γ ∈ kernelRoots χ, γ = α ∨ γ = -α ∨ iform α γ = 0 := by
    intro α hα hr γ hγ
    by_cases hc : (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) = ⟦⟨α, hα⟩⟧
    · have : γ ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hγ, hc⟩
      rw [hr] at this
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (iform_eq_zero_of_mk_ne (α := ⟨α, hα⟩) (β := ⟨γ, hγ⟩) (Ne.symm hc)))
  rcases hU α β hα hβ (hiso hα hαr) (hiso hβ hβr) with h | h
  · subst h
    rfl
  · subst h
    exact mk_eq_of_iform_ne_zero (α := ⟨α, hα⟩) (β := ⟨-α, hβ⟩)
      (by rw [iform_comm]; exact iform_neg_self_ne_zero hα.1)


theorem exc3_exists_rankOne_of_member (hK3 : Nat.card K = 3) {b : Fin τ.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hU : ∀ i j : KernelComponent (maskChar (signTupleBits b)),
      ¬ 2 < (componentRoots (maskChar (signTupleBits b)) i).ncard →
      ¬ 2 < (componentRoots (maskChar (signTupleBits b)) j).ncard → i = j)
    {L : Subgroup (ModGL τ K)} (eL : SL(2, ZMod 3) ≃* L) (hLX : L ≤ toralCentralizer τ K b)
    (hsub : IsSubnormal L (toralCentralizer τ K b)) :
    ∃ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      L = componentRootSpan K (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ ∧
        componentRootSpan K (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
  have : Finite (ModGL τ K) := finite_modGL
  have hK : ringChar K ≠ 2 := ringChar_ne_two_of_card_eq_three hK3
  set χ := maskChar (signTupleBits b) with hχ
  have hker : rootCharKernel b = kernelRoots χ := rootCharKernel_eq_kernelRoots hK hb
  have hSX : rootSpan τ K (kernelRoots χ) ≤ toralCentralizer τ K b := by
    rw [← hker]
    exact rootSpan_rootCharKernel_le_toralCentralizer b
  set S := rootSpan τ K (kernelRoots χ) with hS
  have eL' : L ≃* SL2 K := eL.symm.trans (slEquivSL23 hK3).symm
  have hgen : Subgroup.closure {y : L | orderOf y = 3} = ⊤ :=
    closure_orderOf_three_eq_top_of_mulEquiv hK3 eL'
  have hLS : L ≤ S := by
    have := le_rootSpan_of_closure_eq_top hK3 hK hb hLX hgen
    rwa [hker] at this
  have hLsubS : IsSubnormal L S := by
    have := isSubnormal_inf hsub S
    rwa [inf_eq_left.mpr hLS, inf_eq_right.mpr hSX] at this
  have hLsolv : Group.IsSolvable L := isSolvable_of_mulEquiv hK3 eL'
  have hcent := fun i (hi : 2 < (componentRoots χ i).ncard) =>
    exc3_centralizes_big_class hK i hi hLS hLsubS hLsolv
  let Big := {i : KernelComponent χ // 2 < (componentRoots χ i).ncard}
  let Small := {i : KernelComponent χ // ¬ 2 < (componentRoots χ i).ncard}
  have : Finite (KernelComponent χ) := (root_character_kernel_orthogonal_central_product τ K χ).2.1
  set P : Subgroup (ModGL τ K) := ⨆ i : Big, componentRootSpan K χ i.1 with hP
  set Q : Subgroup (ModGL τ K) := ⨆ i : Small, componentRootSpan K χ i.1 with hQ
  have hSPQ : S = P ⊔ Q := by
    rw [hS, ← iSup_componentRootSpan K (χ := χ),
      iSup_split (fun i => componentRootSpan K χ i) (fun i => 2 < (componentRoots χ i).ncard),
      iSup_subtype', iSup_subtype']
  have hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := by
    intro p hp q hq
    have hle : P ≤ Subgroup.centralizer (Q : Set (ModGL τ K)) := by
      refine iSup_le fun i u hu => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hle2 : Q ≤ Subgroup.centralizer (componentRootSpan K χ i.1 : Set (ModGL τ K)) := by
        refine iSup_le fun j v hv => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hij : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
        exact exc3_class_commute hij w hw v hv
      exact (Subgroup.mem_centralizer_iff.mp (hle2 hv) u hu).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hp) q hq).symm
  have hLP : ∀ x ∈ L, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hle : P ≤ Subgroup.centralizer ({x} : Set (ModGL τ K)) := by
      refine iSup_le fun i u hu => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcent i.1 i.2 x hx u hu).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hord3 : ∀ x ∈ L, x ^ 3 = 1 → x ∈ Q := by
    intro x hx hx3
    have hxS : x ∈ P ⊔ Q := hSPQ ▸ hLS hx
    obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_commute hPQ).mp hxS
    have hpc : ∀ y ∈ P, p * y = y * p := by
      intro y hy
      have e1 := hLP (p * q) hx y hy
      have e2 := hPQ y hy q hq
      have e3 : p * y * q = y * p * q := by
        calc p * y * q = p * (y * q) := by group
          _ = p * (q * y) := by rw [e2]
          _ = p * q * y := by group
          _ = y * (p * q) := e1
          _ = y * p * q := by group
      exact mul_right_cancel e3
    have hcomm : ∀ i j : Big, i ≠ j → ∀ a ∈ componentRootSpan K χ i.1,
        ∀ b ∈ componentRootSpan K χ j.1, a * b = b * a :=
      fun i j hij a ha b hb => exc3_class_commute (fun h => hij (Subtype.ext h)) a ha b hb
    have hpT : p ∈ torusGroup τ K := by
      have hmem := exc3_center_le_iSup (fun i : Big => componentRootSpan K χ i.1) hcomm hp hpc
      have hle : (⨆ i : Big, (componentRootSpan K χ i.1 ⊓
          Subgroup.centralizer (componentRootSpan K χ i.1 : Set (ModGL τ K)))) ≤
          torusGroup τ K := iSup_le fun i => exc3_classCenter_le_torus (K := K) i.1
      exact hle hmem
    have hp2 : p ^ 2 = 1 := sq_eq_one_of_mem_torusGroup hK3 hpT
    have hpq : Commute p q := hPQ p hp q hq
    have h1 : (p * q) ^ 3 = p * q ^ 3 := by
      rw [hpq.mul_pow, show p ^ 3 = p by rw [pow_succ, hp2, one_mul]]
    have h2 : p * q ^ 3 = 1 := by rw [← h1]; exact hx3
    have h3 : p = (q ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [h3]
    exact Q.mul_mem (Q.inv_mem (Q.pow_mem hq 3)) hq
  have hLQ : L ≤ Q := by
    intro x hx
    have hle : Subgroup.closure {y : L | orderOf y = 3} ≤ Q.subgroupOf L :=
      (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2
        (hord3 y.1 y.2 (by
          have : orderOf (y : ModGL τ K) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
          rw [← this]
          exact pow_orderOf_eq_one _))
    exact Subgroup.mem_subgroupOf.1 (hle (hgen ▸ Subgroup.mem_top (⟨x, hx⟩ : L)))
  by_cases hSm : Nonempty Small
  · obtain ⟨i₀⟩ := hSm
    have hsub1 : Subsingleton Small := ⟨fun i j => Subtype.ext (hU i.1 j.1 i.2 j.2)⟩
    have hQeq : Q = componentRootSpan K χ i₀.1 :=
      le_antisymm (iSup_le fun i => by rw [Subsingleton.elim i i₀])
        (le_iSup (fun i : Small => componentRootSpan K χ i.1) i₀)
    obtain ⟨γ, hγ, hi₀, -, hSγ, ⟨eR⟩⟩ := exc3_small_class (K := K) hK χ i₀.1 i₀.2
    obtain ⟨e⟩ := exc3_nonempty_equiv_sl2Three hK3 eR
    have hcard : Nat.card (componentRootSpan K χ i₀.1) ≤ 24 := by
      rw [← Nat.card_congr e.toEquiv, natCard_sl2Three]
    have hLeq : L = componentRootSpan K χ i₀.1 :=
      eq_of_le_of_natCard_le eL (hQeq ▸ hLQ) hcard
    refine ⟨γ, hγ, ?_, ?_⟩
    · rw [hLeq, hi₀]
    · rw [← hi₀]
      exact hSγ
  · exfalso
    rw [not_nonempty_iff] at hSm
    have hQbot : Q = ⊥ := by
      rw [hQ]
      exact iSup_of_empty _
    have hL1 : L = ⊥ := le_bot_iff.mp (hQbot ▸ hLQ)
    have hnt : Nontrivial (SL(2, ZMod 3)) := ⟨⟨-1, 1, by decide +kernel⟩⟩
    obtain ⟨a, ha⟩ := exists_ne (1 : SL(2, ZMod 3))
    have := eL.injective (a₁ := a) (a₂ := 1) (by
      apply Subtype.ext
      have h1 : (eL a : ModGL τ K) ∈ (⊥ : Subgroup (ModGL τ K)) := hL1 ▸ (eL a).2
      rw [Subgroup.mem_bot] at h1
      simpa using h1)
    exact ha this


end Structure

end CFSG.ClassicalInvolution.Q3
