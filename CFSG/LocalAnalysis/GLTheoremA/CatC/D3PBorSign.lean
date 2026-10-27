module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IBound
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PLayer2

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]



section Basic

@[expose] def LayerAct.one' : LayerAct Tag.D4 (1 : MulAut ↥(adjointGroup Tag.D4 K)) (1 : K ≃+* K) where
  r _ δ := δ
  f _ _ := 1
  stable _ _ hx := hx
  coord k δ x _ := by
    simp [MulAut.one_apply]

@[expose] def LayerAct.castAut {α α' : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K} (h : α = α')
    (la : LayerAct Tag.D4 α σ) : LayerAct Tag.D4 α' σ where
  r := la.r
  f := la.f
  stable := by subst h; exact la.stable
  coord := by subst h; exact la.coord

@[expose] def LayerAct.castSigma {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ σ' : K ≃+* K} (h : σ = σ')
    (la : LayerAct Tag.D4 α σ) : LayerAct Tag.D4 α σ' where
  r := la.r
  f := la.f
  stable := la.stable
  coord := by subst h; exact la.coord

open scoped Classical in
theorem LayerAct.unique_eq {α α' : MulAut ↥(adjointGroup Tag.D4 K)} {σ σ' : K ≃+* K} (h : α = α')
    (la : LayerAct Tag.D4 α σ) (la' : LayerAct Tag.D4 α' σ') :
    (∀ k δ, la.r k δ = la'.r k δ) ∧ σ = σ' ∧ ∀ k δ, la.f k δ = la'.f k δ := by
  subst h
  obtain ⟨hr, hσ⟩ := LayerAct.unique' la la'
  refine ⟨hr, hσ, fun k δ => ?_⟩
  subst hσ
  have hx : rootElt (la.r k δ).1 1 ∈ unitN Tag.D4 K k := rootElt_mem_unitN' _ 1
  have h1 := la.coord k δ _ hx
  have h2 := la'.coord k δ _ hx
  rw [rootCoord_rootElt, if_pos rfl, map_one, mul_one] at h1
  rw [rootCoord_rootElt, if_pos (hr k δ), map_one, mul_one] at h2
  exact h1.symm.trans h2

end Basic

section Involution

theorem eq_one_of_mul_self_cube {G : Type*} [Group G] {x : G} (h2 : x * x = 1) (h3 : x ^ 3 = 1) :
    x = 1 := by
  calc x = x * (x * x) := by rw [h2, mul_one]
    _ = x ^ 3 := (pow_three x).symm
    _ = 1 := h3

theorem commute_ringEquiv (a b : K ≃+* K) : a * b = b * a := by
  haveI := isCyclic_ringEquiv' (K := K)
  exact (IsCyclic.commGroup (α := K ≃+* K)).mul_comm a b

theorem exists_layerAct_involution (α t : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (ht2 : t * t = 1) (hb3 : (t * α) ^ 3 = 1)
    (hUα : (unitU K).map α.toMonoidHom = unitU K) (hUt : (unitU K).map t.toMonoidHom = unitU K) :
    ∃ la : LayerAct Tag.D4 t (1 : K ≃+* K), (∀ k δ, la.r k δ = δ) ∧
      ∀ k δ, la.f k δ * la.f k δ = 1 := by
  classical
  have hUb : (unitU K).map (t * α).toMonoidHom = unitU K := by
    rw [map_toMonoidHom_mul_mulAut, hUα, hUt]
  obtain ⟨σ, ε, la, hσ3, hε3, -, hr⟩ := exists_layerAct_of_stable α hα3 (unitU K) rfl hUα
  obtain ⟨σ', ε', la', hσ'3, hε'3, -, hr'⟩ :=
    exists_layerAct_of_stable (t * α) hb3 (unitU K) rfl hUb
  have hα3' : α * α * α = 1 := by rw [← pow_three']; exact hα3
  have hteq : t * α * α * α = t := by
    calc t * α * α * α = t * (α * α * α) := by group
      _ = t := by rw [hα3', mul_one]
  set la1 := LayerAct.comp' (LayerAct.comp' la' la) la with hla1
  set m : ℕ := 2 * ε + (2 * ε + 2 * ε') with hm
  have hr1 : ∀ k δ, (la1.r k δ).1 = permLattice (d4Rho ^ m) δ.1 := by
    intro k δ
    show (la.r k (la.r k (la'.r k δ))).1 = _
    rw [hr, hr, hr', hm, pow_add, pow_add]
    simp only [permLattice_mul']
  have ht2' : (t * α * α * α) * (t * α * α * α) = 1 := by rw [hteq]; exact ht2
  obtain ⟨hrr, hσσ, hff⟩ := LayerAct.unique_eq ht2' (LayerAct.comp' la1 la1) (LayerAct.one' (K := K))
  have hρ2 : d4Rho ^ m * d4Rho ^ m = 1 := by
    refine Equiv.ext fun i => ?_
    let δi : UnitRoots Tag.D4 0 := ⟨rA i, rA_isRoot i, by rw [height_rA]; rfl⟩
    have h1 := congrArg Subtype.val (hrr 0 δi)
    change (la1.r 0 (la1.r 0 δi)).1 = δi.1 at h1
    have e1 : ∀ (p : Equiv.Perm D4Idx) (j : D4Idx), permLattice p (rA j) = rA (p j) :=
      fun p j => permLattice_single p j
    rw [hr1, hr1, show δi.1 = rA i from rfl, e1, e1] at h1
    exact (rA_inj _ _).1 h1
  have hρ3 : (d4Rho ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, d4Rho_pow_three, one_pow]
  have hρ1 : d4Rho ^ m = 1 := eq_one_of_mul_self_cube hρ2 hρ3
  have hrid : ∀ k δ, la1.r k δ = δ := fun k δ =>
    Subtype.ext (by rw [hr1, hρ1, permLattice_one'])
  have hσ1 : σ' * σ * σ = 1 := by
    have h3 : (σ' * σ * σ) ^ 3 = 1 := by
      have hc1 : Commute (σ' * σ) σ := commute_ringEquiv _ _
      have hc2 : Commute σ' σ := commute_ringEquiv _ _
      rw [hc1.mul_pow, hc2.mul_pow, hσ'3, hσ3, one_mul, one_mul]
    exact eq_one_of_mul_self_cube hσσ h3
  have hf2 : ∀ k δ, la1.f k δ * la1.f k δ = 1 := by
    intro k δ
    have h := hff k δ
    change la1.f k δ * (σ' * σ * σ) (la1.f k (la1.r k δ)) = 1 at h
    have hσ1' : ∀ y : K, (σ' * σ * σ) y = y := fun y => by rw [hσ1]; rfl
    rw [hσ1', hrid k δ] at h
    exact h
  exact ⟨LayerAct.castSigma hσ1 (LayerAct.castAut hteq la1), hrid, hf2⟩

end Involution

section Sign

open scoped Classical in
@[expose] def layerScalar {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) (v : D4Vec) : K :=
  if h : IsRoot Tag.D4 v ∧ 0 < height v then
    la.f ((height v).toNat - 1) ⟨v, h.1, by have := h.2; omega⟩
  else 1

theorem layerScalar_eq {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) {k : ℕ} (δ : UnitRoots Tag.D4 k) :
    layerScalar la δ.1 = la.f k δ := by
  classical
  have hh : height δ.1 = ((k + 1 : ℕ) : ℤ) := δ.2.2
  have hk : (height δ.1).toNat - 1 = k := by rw [hh]; simp
  unfold layerScalar
  rw [dif_pos (UnitRoots.pos Tag.D4 δ)]
  have key : ∀ (k' : ℕ) (hk' : k' = k) (δ' : UnitRoots Tag.D4 k'), δ'.1 = δ.1 →
      la.f k' δ' = la.f k δ := by
    intro k' hk' δ' h
    subst hk'
    congr 1
    exact Subtype.ext h
  exact key _ hk _ rfl

theorem layerAct_coord_triv {t : MulAut ↥(adjointGroup Tag.D4 K)}
    (la : LayerAct Tag.D4 t (1 : K ≃+* K)) (hr : ∀ k δ, la.r k δ = δ) (k : ℕ)
    (δ : UnitRoots Tag.D4 k) (x : ↥(adjointGroup Tag.D4 K)) (hx : x ∈ unitN Tag.D4 K k) :
    rootCoord (UnitRoots.pos Tag.D4 δ) ((t x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      la.f k δ * rootCoord (UnitRoots.pos Tag.D4 δ) (x : ModGL Tag.D4 K) := by
  have h := la.coord k δ x hx
  rw [hr k δ] at h
  exact h

open scoped Classical in
theorem pc_layerAct_rootElt {t : MulAut ↥(adjointGroup Tag.D4 K)}
    (la : LayerAct Tag.D4 t (1 : K ≃+* K)) (hr : ∀ k δ, la.r k δ = δ) {γ γ' : D4Vec}
    (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ) (hγ' : γ' ∈ d4RootsAt (height γ)) :
    pc γ' ((t (rootElt γ 1) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      if γ' = γ then layerScalar la γ else 0 := by
  obtain ⟨h1, h2⟩ := mem_d4RootsAt.1 hγ'
  have hpos' : IsRoot Tag.D4 γ' ∧ 0 < height γ' := ⟨h1, by rw [h2]; exact hγ.2⟩
  set k := (height γ).toNat - 1 with hkdef
  have hhk : height γ = ((k + 1 : ℕ) : ℤ) := by have := hγ.2; omega
  let g₁ : UnitRoots Tag.D4 k := ⟨γ, hγ.1, hhk⟩
  let g₂ : UnitRoots Tag.D4 k := ⟨γ', h1, by rw [h2]; exact hhk⟩
  have hx : rootElt γ 1 ∈ unitN Tag.D4 K k := rootElt_mem_unitN ⟨hγ.1, hhk⟩ 1
  have e := layerAct_coord_triv la hr k g₂ (rootElt γ 1) hx
  have hroot := rootCoord_rootElt (K := K) g₂ g₁ 1
  rw [pc_of_pos hpos']
  change rootCoord (UnitRoots.pos Tag.D4 g₂) _ = _
  rw [e, hroot]
  have hs : layerScalar la γ = la.f k g₁ := layerScalar_eq la g₁
  by_cases hc : γ' = γ
  · have hg : g₁ = g₂ := Subtype.ext hc.symm
    rw [if_pos hc, if_pos hg, hs, hg, mul_one]
  · have hg : ¬ g₁ = g₂ := fun h => hc (congrArg Subtype.val h).symm
    rw [if_neg hc, if_neg hg, mul_zero]

open scoped commutatorElement

theorem layerScalar_add {t : MulAut ↥(adjointGroup Tag.D4 K)}
    (la : LayerAct Tag.D4 t (1 : K ≃+* K)) (hr : ∀ k δ, la.r k δ = δ) {γ δ : D4Vec}
    (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ) (hδ : IsRoot Tag.D4 δ ∧ 0 < height δ)
    (hβ : IsRoot Tag.D4 (γ + δ)) :
    layerScalar la (γ + δ) = layerScalar la γ * layerScalar la δ := by
  classical
  have hβ' : IsRoot Tag.D4 (γ + δ) ∧ 0 < height (γ + δ) :=
    ⟨hβ, by rw [d4_height_add]; have := hγ.2; have := hδ.2; omega⟩
  have hτ : Tag.D4 = .D4 ∨ Tag.D4 = .E6 ∨ Tag.D4 = .E7 ∨ Tag.D4 = .E8 := Or.inl rfl
  have hne : γ ≠ δ := fun h => by
    subst h
    exact d4_not_isRoot_double hγ.1 hβ
  have hneg : γ ≠ -δ := fun h => by
    have h1 := hγ.2
    have h2 := hδ.2
    rw [h, height_neg] at h1
    omega
  obtain ⟨h1, -⟩ := simply_laced_root_commutator_unit.{0} Tag.D4 hτ hγ.1 hδ.1 hne hneg
  obtain ⟨hC, -⟩ := h1 hβ
  have hCne : (commConst Tag.D4 γ δ (1, 1) : K) ≠ 0 := by
    rcases hC with h | h <;> rw [h] <;> simp
  set kγ := (height γ).toNat - 1 with hkγ
  set kδ := (height δ).toNat - 1 with hkδ
  set kβ := (height (γ + δ)).toNat - 1 with hkβ
  have hhγ : height γ = ((kγ + 1 : ℕ) : ℤ) := by have := hγ.2; omega
  have hhδ : height δ = ((kδ + 1 : ℕ) : ℤ) := by have := hδ.2; omega
  have hhβ : height (γ + δ) = ((kβ + 1 : ℕ) : ℤ) := by have := hβ'.2; omega
  let g₃ : UnitRoots Tag.D4 kβ := ⟨γ + δ, hβ, hhβ⟩
  set X : ↥(adjointGroup Tag.D4 K) := rootElt γ 1 with hX
  set Y : ↥(adjointGroup Tag.D4 K) := rootElt δ 1 with hY
  have hXN : X ∈ unitN Tag.D4 K kγ := rootElt_mem_unitN ⟨hγ.1, hhγ⟩ 1
  have hYN : Y ∈ unitN Tag.D4 K kδ := rootElt_mem_unitN ⟨hδ.1, hhδ⟩ 1
  have hXm : (X : ModGL Tag.D4 K) ∈ heightSeries Tag.D4 K (height γ) := by rw [hhγ]; exact hXN
  have hYm : (Y : ModGL Tag.D4 K) ∈ heightSeries Tag.D4 K (height δ) := by rw [hhδ]; exact hYN
  have hcommm : ⁅(X : ModGL Tag.D4 K), (Y : ModGL Tag.D4 K)⁆ ∈
      heightSeries Tag.D4 K (height (γ + δ)) := by
    rw [d4_height_add]
    exact commutator_heightSeries_le K _ _ (Subgroup.commutator_mem_commutator hXm hYm)
  set Z : ↥(adjointGroup Tag.D4 K) := ⁅X, Y⁆ with hZ
  have hZm : ((Z : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      ⁅(X : ModGL Tag.D4 K), (Y : ModGL Tag.D4 K)⁆ := rfl
  have hZN : Z ∈ unitN Tag.D4 K kβ := by
    rw [mem_unitN, hZm, ← hhβ]
    exact hcommm
  have hcoordZ : rootCoord hβ' (Z : ModGL Tag.D4 K) = (commConst Tag.D4 γ δ (1, 1) : K) := by
    rw [hZm]
    have hXe : (X : ModGL Tag.D4 K) = pinnedX Tag.D4 K γ 1 := rfl
    have hYe : (Y : ModGL Tag.D4 K) = pinnedX Tag.D4 K δ 1 := rfl
    rw [hXe, hYe]
    have := rootCoord_commutator_pinnedX_d4 hγ hδ hβ' (by rw [d4_height_add]) (1 : K) 1
    rw [if_pos rfl] at this
    simpa using this
  have e1 := layerAct_coord_triv la hr kβ g₃ Z hZN
  change rootCoord hβ' ((t Z : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = la.f kβ g₃ * rootCoord hβ' (Z : ModGL Tag.D4 K) at e1
  rw [hcoordZ] at e1
  have htZ : ((t Z : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      ⁅((t X : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K),
        ((t Y : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁆ := by
    rw [hZ, map_commutatorElement]
    rfl
  have hzm : ((t X : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      heightSeries Tag.D4 K (height γ) := by
    rw [hhγ]; exact la.stable kγ X hXN
  have hwm : ((t Y : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      heightSeries Tag.D4 K (height δ) := by
    rw [hhδ]; exact la.stable kδ Y hYN
  have hpair := rootCoord_commutator_pair (K := K) hγ.2 hδ.2 hzm hwm hβ' (d4_height_add γ δ)
  rw [← htZ, e1] at hpair
  have hγm : γ ∈ d4RootsAt (height γ) := mem_d4RootsAt.2 ⟨hγ.1, rfl⟩
  have hδm : δ ∈ d4RootsAt (height δ) := mem_d4RootsAt.2 ⟨hδ.1, rfl⟩
  rw [Finset.sum_eq_single γ (fun γ' hγ' hne' => by
      refine Finset.sum_eq_zero fun δ' _ => ?_
      rw [pc_layerAct_rootElt la hr hγ hγ', if_neg hne']
      simp) (fun h => absurd hγm h),
    Finset.sum_eq_single δ (fun δ' hδ' hne' => by
      rw [pc_layerAct_rootElt la hr hδ hδ', if_neg hne']
      simp) (fun h => absurd hδm h),
    pc_layerAct_rootElt la hr hγ hγm, pc_layerAct_rootElt la hr hδ hδm] at hpair
  simp only [if_true] at hpair
  have hsγ : layerScalar la γ = layerScalar la γ := rfl
  have hsβ : la.f kβ g₃ = layerScalar la (γ + δ) := (layerScalar_eq la g₃).symm
  rw [hsβ] at hpair
  have : (commConst Tag.D4 γ δ (1, 1) : K) *
      (layerScalar la (γ + δ) - layerScalar la γ * layerScalar la δ) = 0 := by
    linear_combination hpair
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hCne)

theorem exists_sign_of_involution [CharP K 3] (α t : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (ht2 : t * t = 1) (hb3 : (t * α) ^ 3 = 1)
    (hUα : (unitU K).map α.toMonoidHom = unitU K) (hUt : (unitU K).map t.toMonoidHom = unitU K) :
    ∃ (la : LayerAct Tag.D4 t (1 : K ≃+* K)) (b : D4Idx → Bool), (∀ k δ, la.r k δ = δ) ∧
      ∀ k (δ : UnitRoots Tag.D4 k), la.f k δ = if sgnB b δ.1 then -1 else 1 := by
  classical
  obtain ⟨la, hr, hf2⟩ := exists_layerAct_involution α t hα3 ht2 hb3 hUα hUt
  have hmem : ∀ k (δ : UnitRoots Tag.D4 k), δ.1 ∈ d4RootsFrom 1 := fun k δ =>
    mem_d4RootsFrom.2 ⟨δ.2.1, (UnitRoots.pos Tag.D4 δ).2, by
      rw [δ.2.2]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)⟩
  have hroot : ∀ v ∈ d4RootsFrom 1, IsRoot Tag.D4 v ∧ 0 < height v := fun v hv => by
    obtain ⟨h1, h2, -⟩ := mem_d4RootsFrom.1 hv
    exact ⟨h1, h2⟩
  have hsd : SignData (layerScalar la) := by
    refine ⟨fun v hv => ?_, fun γ hγ δ hδ hβ => ?_⟩
    · have hv' := hroot v hv
      have hhk : height v = ((((height v).toNat - 1) + 1 : ℕ) : ℤ) := by have := hv'.2; omega
      let d : UnitRoots Tag.D4 ((height v).toNat - 1) := ⟨v, hv'.1, hhk⟩
      have := layerScalar_eq la d
      change layerScalar la v = la.f _ d at this
      rw [this]
      exact hf2 _ d
    · exact layerScalar_add la hr (hroot γ hγ) (hroot δ hδ) (mem_d4RootsFrom.1 hβ).1
  obtain ⟨b, hb⟩ := signData_table (neg_one_ne_one_of_charThree (K := K)) hsd
  refine ⟨la, b, hr, fun k δ => ?_⟩
  rw [← layerScalar_eq la δ]
  exact hb δ.1 (hmem k δ)

end Sign

end CFSG.LocalAnalysis.GLTheoremA
