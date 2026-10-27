module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentClasses
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentSU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Model8Torus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourIn
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp TwE6UniqAbs
open scoped MatrixGroups Matrix commutatorElement

section Comp

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem pow_three_of_orderOf_three {ω : Lˣ} (hω : orderOf ω = 3) : ω ^ 3 = 1 := by
  have := pow_orderOf_eq_one ω
  rwa [hω] at this

theorem Std8.a0_mem_torus (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) :
    rootDiagUnit Tag.E6 (a0 ω) ∈ D.S.D.torus := by
  rw [← dV_x0_eq]
  exact D.dV_mem_torus (pow_three_of_orderOf_three hω) x0

theorem a0_pow_three {ω : Lˣ} (hω : orderOf ω = 3) (j : Fin Tag.E6.rank) : a0 ω j ^ 3 = 1 := by
  by_cases hj : j = 3
  · subst hj
    simpa [a0] using pow_three_of_orderOf_three hω
  · simp [a0, Pi.mulSingle_apply, hj]

theorem a0_ne_one {ω : Lˣ} (hω : orderOf ω = 3) : rootDiagUnit Tag.E6 (a0 ω) ≠ 1 := by
  intro h
  rw [← dV_x0_eq, ← dV_zero (τ := Tag.E6) ω] at h
  have := dV_injective hω h
  have h3 := congrFun this 3
  simp [x0] at h3

theorem Std8.hTame
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) :
    ∀ i : KernelComponent (rootCharHom (a0 ω)),
      CFSG.IsQuasisimple ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i) ∨
        Group.IsSolvable ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i) :=
  langSetup_hTame_of_prime D.S Nat.prime_three TwE6InnerAbs.natCast_three_ne_zero_of_charTwo
    (fun h => absurd h (by decide)) (D.a0_mem_torus hω) (a0_pow_three hω) (a0_ne_one hω)

theorem Std8.orbitLength_eq_one (D : Std8 L) {ω : Lˣ}
    (i : KernelComponent (rootCharHom (a0 ω))) :
    componentOrbitLength D.S.ρ (componentRoots (rootCharHom (a0 ω)) i) = 1 := by
  have hfin : (componentRoots (rootCharHom (a0 ω)) i).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have hstab : ∀ γ ∈ componentRoots (rootCharHom (a0 ω)) i,
      D.S.ρ γ ∈ componentRoots (rootCharHom (a0 ω)) i := fun γ hγ => by
    rw [D.hρ]
    exact (isRootComponent_componentRoots i).neg_mem γ hγ
  exact componentOrbitLength_eq_one hfin hstab

theorem Std8.rationalComponent_quasisimple_lie
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3)
    (i : KernelComponent (rootCharHom (a0 ω))) :
    CFSG.IsQuasisimple ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i) ∧
      IsLieQuot ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i)
        OuterFourInAux.IsU3EightIndex := by
  obtain ⟨ψ, σ, hψ, -, hΨ⟩ := exists_frames_a0 hω i
  have hs1 := D.orbitLength_eq_one i
  have hπ : ∀ a' b : Fin 3, a' ≠ b → (D.S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength
      D.S.ρ (componentRoots (rootCharHom (a0 ω)) i)] (σ a' b) =
        σ ((Equiv.refl (Fin 3)) b) ((Equiv.refl (Fin 3)) a') := by
    intro a' b _
    rw [hs1, Function.iterate_one, D.hρ]
    exact (hψ.neg a' b).symm
  have hq8 : D.S.D.q = 2 ^ 3 := D.hq.trans (by norm_num)
  have hνQ : (3, 2 ^ (3 * componentOrbitLength D.S.ρ (componentRoots (rootCharHom (a0 ω)) i))) ≠
      (3, 2) := by
    rw [hs1]
    decide
  refine ⟨rationalComponent_suN_quasisimple D.S (D.a0_mem_torus hω) i (by norm_num : 3 ≤ 3) hψ hΨ
    (Equiv.refl _) hπ Nat.prime_two inferInstance (by norm_num : 0 < 3) hq8 hνQ, ?_⟩
  have hmodel := KSExact.rationalComponent_suN_model D.S (D.a0_mem_torus hω) i
    (by norm_num : 3 ≤ 3) hψ hΨ (Equiv.refl _) hπ Nat.prime_two inferInstance
    (by norm_num : 0 < 3) hq8 hνQ
  rw [hs1, Nat.mul_one] at hmodel
  exact KSExact.isLieQuot_of_twistedA_model hmodel _ fun q hp hf => ⟨rfl, hp, hf⟩

theorem Std8.mem_component_of_rho (D : Std8 L) {ω : Lˣ} (i : KernelComponent (rootCharHom (a0 ω)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom (a0 ω)) i) :
    D.S.ρ γ ∈ componentRoots (rootCharHom (a0 ω)) i := by
  rw [D.hρ]
  exact (isRootComponent_componentRoots i).neg_mem γ hγ

theorem Std8.rationalRoots_eq (D : Std8 L) {ω : Lˣ} (i : KernelComponent (rootCharHom (a0 ω))) :
    rationalRoots D.S.ρ (rootCharHom (a0 ω)) i = componentRoots (rootCharHom (a0 ω)) i := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => exact hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact D.mem_component_of_rho i ih
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

theorem Std8.rationalComponent_le_rootSpan (D : Std8 L) {ω : Lˣ}
    (i : KernelComponent (rootCharHom (a0 ω))) :
    rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i ≤
      rootSpan Tag.E6 L (componentRoots (rootCharHom (a0 ω)) i) := by
  have h1 : rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i ≤
      rationalSpan D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i :=
    commutator_le_self_of_subgroup _
  refine h1.trans (inf_le_left.trans ?_)
  rw [D.rationalRoots_eq]

theorem Std8.rationalComponent_commute (D : Std8 L) {ω : Lˣ}
    {i j : KernelComponent (rootCharHom (a0 ω))} (hij : i ≠ j) {u v : ModGL Tag.E6 L}
    (hu : u ∈ rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i)
    (hv : v ∈ rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) j) : Commute u v := by
  have h := (root_character_kernel_orthogonal_central_product Tag.E6 L (rootCharHom (a0 ω))).2.2.1
    i j hij
  have hc : ⁅u, v⁆ ∈ ⁅componentRootSpan L (rootCharHom (a0 ω)) i,
      componentRootSpan L (rootCharHom (a0 ω)) j⁆ :=
    Subgroup.commutator_mem_commutator (D.rationalComponent_le_rootSpan i hu)
      (D.rationalComponent_le_rootSpan j hv)
  rw [h, Subgroup.mem_bot] at hc
  exact commutatorElement_eq_one_iff_mul_comm.1 hc

theorem Std8.mem_rationalSpan_iff (D : Std8 L) {ω : Lˣ} (i : KernelComponent (rootCharHom (a0 ω)))
    {x : ModGL Tag.E6 L} : x ∈ rationalSpan D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i ↔
      x ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom (a0 ω)) i) ∧ x ∈ D.S.Γ := by
  unfold rationalSpan
  rw [D.rationalRoots_eq i]
  exact Subgroup.mem_inf

theorem Std8.rootSL2_HSL_mem_rationalComponent (D : Std8 L) {ω : Lˣ}
    {i : KernelComponent (rootCharHom (a0 ω))} {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ componentRoots (rootCharHom (a0 ω)) i) {c : Lˣ} (hc : c ^ 9 = 1) :
    rootSL2 Tag.E6 L β (HSL c) ∈ rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i := by
  have hroot : IsRoot Tag.E6 β := hβ.1.1
  obtain ⟨c0, hc0⟩ := D.exists_antidiag_mem_Γ hroot
  have hc5 : (c ^ 5) ^ 9 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc, one_pow]
  have hspan : ∀ A : SL2 L, rootSL2 Tag.E6 L β A ∈
      rootSpan Tag.E6 L (componentRoots (rootCharHom (a0 ω)) i) := fun A =>
    rootSpan_mono (fun γ hγ => by
      rcases hγ with rfl | rfl
      · exact hβ
      · exact (isRootComponent_componentRoots i).neg_mem β hβ)
      (rootSL2_mem_rootSpan_pair hroot A)
  have hmem1 : rootSL2 Tag.E6 L β (HSL (c ^ 5)) ∈
      rationalSpan D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i :=
    (D.mem_rationalSpan_iff i).2 ⟨hspan _, D.rootSL2_HSL_mem_Γ hroot hc5⟩
  have hmem2 : rootSL2 Tag.E6 L β (nSL c0) ∈
      rationalSpan D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i :=
    (D.mem_rationalSpan_iff i).2 ⟨hspan _, hc0⟩
  have h1 := Subgroup.commutator_mem_commutator hmem1 hmem2
  have hn0 : ((nSL c0 : SL2 L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := rfl
  have hn1 : ((nSL c0 : SL2 L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := rfl
  have h4 : (c ^ 5) ^ 2 = c := by
    rw [← pow_mul, show 5 * 2 = 9 + 1 by rfl, pow_succ, hc, one_mul]
  rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    HSL_conj_antidiag (c ^ 5) hn0 hn1, h4] at h1
  exact h1

theorem b3_mem_R6 : ∀ b : Fin 6, b3 b ∈ R6 ∧ 3 ∣ b3 b 3 := by decide +kernel

theorem b3_isRoot (b : Fin 6) : IsRoot Tag.E6 (b3 b) := isRoot_of_mem_R6 (b3_mem_R6 b).1

theorem rootSL2_HSL_eq_rootDiagUnit' {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (u : Lˣ) :
    rootSL2 Tag.E6 L β (HSL u) =
      rootDiagUnit Tag.E6 (fun j => u ^ iform β (Pi.single j 1)) :=
  (Hel_root_eq_rootSL2 (Or.inr (Or.inl rfl)) hβ u).symm

theorem Std8.dV_mem_iSup_rationalComponent (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3)
    (x : Fin Tag.E6.rank → ZMod 3) :
    dV ω x ∈ ⨆ i : KernelComponent (rootCharHom (a0 ω)),
      rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i := by
  obtain ⟨e, he⟩ := exists_classEquiv hω
  have hω3 := pow_three_of_orderOf_three hω
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ω : L) (n := 3) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact Units.ne_zero ω hz.symm
  set ζ : Lˣ := Units.mk0 z hz0 with hζ
  have hζ3 : ζ ^ 3 = ω := Units.ext (by simpa [hζ] using hz)
  have hζ9 : ζ ^ 9 = 1 := by rw [show 9 = 3 * 3 by rfl, pow_mul, hζ3, hω3]
  set k : Fin 6 → ℤ := fun b => ∑ j, B3inv b j * ((x j).val : ℤ) with hk
  set u : Fin 6 → Lˣ := fun b => ζ ^ k b with hu
  have hu9 : ∀ b, u b ^ 9 = 1 := fun b => by
    rw [hu]
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ9, one_zpow]
  have hfac : ∀ b : Fin 6, rootSL2 Tag.E6 L (b3 b) (HSL (u b)) ∈
      ⨆ i : KernelComponent (rootCharHom (a0 ω)),
        rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i := fun b => by
    have hmem : b3 b ∈ componentRoots (rootCharHom (a0 ω)) (e.symm (cls (b3 b))) := by
      rw [he]
      exact ⟨b3_isRoot b, (b3_mem_R6 b).2, by simp⟩
    exact Subgroup.mem_iSup_of_mem _ (D.rootSL2_HSL_mem_rationalComponent hmem (hu9 b))
  have hprod : ((List.finRange 6).map fun b => rootSL2 Tag.E6 L (b3 b) (HSL (u b))).prod ∈
      ⨆ i : KernelComponent (rootCharHom (a0 ω)),
        rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i :=
    Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
      exact hfac b
  convert hprod using 1
  have hfac' : ∀ b : Fin 6, rootSL2 Tag.E6 L (b3 b) (HSL (u b)) =
      rootDiagUnit Tag.E6 (fun j => u b ^ iform (b3 b) (Pi.single j 1)) := fun b =>
    rootSL2_HSL_eq_rootDiagUnit' (b3_isRoot b) (u b)
  rw [List.map_congr_left (fun b _ => hfac' b)]
  have h2 := map_list_prod (rootDiagUnitHom Tag.E6 L)
    ((List.finRange 6).map fun b => (fun j => u b ^ iform (b3 b) (Pi.single j 1)))
  simp only [List.map_map] at h2
  have h3 : ((List.finRange 6).map fun b : Fin 6 =>
      (fun j : Fin Tag.E6.rank => u b ^ iform (b3 b) (Pi.single j 1))).prod =
        fun j => ∏ b : Fin 6, u b ^ iform (b3 b) (Pi.single j 1) := by
    funext j
    rw [Pi.list_prod_apply, List.map_map, Fin.prod_univ_def]
    rfl
  have h4 : ∀ j, ∑ b, k b * iform (b3 b) (Pi.single j 1) = 3 * ((x j).val : ℤ) := by
    intro j
    have h5 : ∀ j' : Fin Tag.E6.rank, ∑ b, B3inv b j' * ((x j').val : ℤ) *
        iform (b3 b) (Pi.single j 1) = ((x j').val : ℤ) * (if j = j' then 3 else 0) := by
      intro j'
      have h := b3_mul_B3inv j j'
      calc ∑ b, B3inv b j' * ((x j').val : ℤ) * iform (b3 b) (Pi.single j 1) =
          ((x j').val : ℤ) * ∑ b, iform (Pi.single j 1) (b3 b) * B3inv b j' := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [iform_comm (b3 b) (Pi.single j 1)]
            ring
        _ = ((x j').val : ℤ) * (if j = j' then 3 else 0) :=
            congrArg (fun t => ((x j').val : ℤ) * t) h
    calc ∑ b, k b * iform (b3 b) (Pi.single j 1) =
        ∑ b, ∑ j' : Fin Tag.E6.rank, B3inv b j' * ((x j').val : ℤ) *
          iform (b3 b) (Pi.single j 1) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_mul _ _ _
      _ = ∑ j' : Fin Tag.E6.rank, ∑ b, B3inv b j' * ((x j').val : ℤ) *
          iform (b3 b) (Pi.single j 1) := Finset.sum_comm
      _ = ∑ j' : Fin Tag.E6.rank, ((x j').val : ℤ) * (if j = j' then 3 else 0) :=
          Finset.sum_congr rfl fun j' _ => h5 j'
      _ = 3 * ((x j).val : ℤ) := by
          rw [Finset.sum_eq_single j]
          · rw [if_pos rfl]
            ring
          · intro j' _ hj'
            rw [if_neg (Ne.symm hj'), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ j) h
  have h5 : dV ω x =
      rootDiagUnit Tag.E6 (fun j => ∏ b : Fin 6, u b ^ iform (b3 b) (Pi.single j 1)) := by
    unfold dV
    congr 1
    funext j
    have h6 : ∏ b : Fin 6, u b ^ iform (b3 b) (Pi.single j 1) =
        ζ ^ (∑ b, k b * iform (b3 b) (Pi.single j 1)) := by
      rw [← SmallQ3.prod_zpow_eq_zpow_sum]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hu]
      simp only
      rw [← zpow_mul]
    rw [h6, h4 j, zpow_mul, zpow_ofNat, hζ3, zpow_natCast]
    rfl
  rw [h5, ← h3]
  exact h2

@[expose] noncomputable def Std8.Rc (D : Std8 L) (ω : Lˣ)
    (i : KernelComponent (rootCharHom (a0 ω))) : Subgroup ↥D.S.Γ :=
  (rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i).comap D.S.Γ.subtype

theorem Std8.rationalComponent_le_Γ (D : Std8 L) {ω : Lˣ}
    (i : KernelComponent (rootCharHom (a0 ω))) :
    rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i ≤ D.S.Γ := fun _ hx =>
  ((D.mem_rationalSpan_iff i).1 (commutator_le_self_of_subgroup _ hx)).2

theorem Std8.map_Rc (D : Std8 L) {ω : Lˣ} (i : KernelComponent (rootCharHom (a0 ω))) :
    (D.Rc ω i).map D.S.Γ.subtype =
      rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i := by
  unfold Std8.Rc
  exact Subgroup.map_comap_eq_self (by
    rw [Subgroup.range_subtype]
    exact D.rationalComponent_le_Γ i)

noncomputable def Std8.RcEquiv (D : Std8 L) (ω : Lˣ)
    (i : KernelComponent (rootCharHom (a0 ω))) :
    ↥(D.Rc ω i) ≃* ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i) :=
  ((D.Rc ω i).equivMapOfInjective D.S.Γ.subtype D.S.Γ.subtype_injective).trans
    (MulEquiv.subgroupCongr (D.map_Rc i))

theorem isLieQuot_of_mulEquiv_e6 {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    {P : TauCeti.LieTypeIndex → Prop} (h : IsLieQuot Y P) : IsLieQuot Z P := by
  obtain ⟨d, hd, ⟨φ⟩⟩ := h
  exact ⟨d, hd, ⟨(QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Z) e
    (Subgroup.map_center_eq e)).symm.trans φ⟩⟩

theorem Std8.Rc_quasisimple_lie
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) (i : KernelComponent (rootCharHom (a0 ω))) :
    CFSG.Open.IsQuasisimple ↥(D.Rc ω i) ∧
      IsLieQuot ↥(D.Rc ω i) OuterFourInAux.IsU3EightIndex := by
  obtain ⟨hq, hl⟩ := D.rationalComponent_quasisimple_lie hω i
  exact ⟨CFSG.Open.IsQuasisimple.of_mulEquiv (D.RcEquiv ω i) (open_isQuasisimple hq),
    isLieQuot_of_mulEquiv_e6 (D.RcEquiv ω i).symm hl⟩

theorem Std8.Rc_commute (D : Std8 L) {ω : Lˣ} {i j : KernelComponent (rootCharHom (a0 ω))}
    (hij : i ≠ j) {u v : ↥D.S.Γ} (hu : u ∈ D.Rc ω i) (hv : v ∈ D.Rc ω j) : Commute u v :=
  Subtype.ext (D.rationalComponent_commute hij hu hv).eq

@[expose] noncomputable def Std8.z0 (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) : ↥D.S.Γ :=
  ⟨dV ω x0, D.dV_mem_Γ (pow_three_of_orderOf_three hω) x0⟩

theorem Std8.coe_z0 (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) :
    (D.z0 hω : ModGL Tag.E6 L) = rootDiagUnit Tag.E6 (a0 ω) :=
  (dV_x0_eq ω).symm ▸ rfl

end Comp

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
