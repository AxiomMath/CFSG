module

public import CFSG.HardMathSupport.Foote.Proving.RootStringOne
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryBasic
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighPin
public import CFSG.RankThree.Lattice.SteinbergBIGenCells

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

set_option linter.unusedSectionVars false


variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M] (D : GenFixedRootDatum τ p₀ k M)

theorem orbitMap_of_orbitCard_one {O : Set (Fin τ.rank → ℤ)}
    (h1 : GenFixedRootDatum.orbitCard O = 1) (A : SL2 (D.orbitField O)) :
    D.orbitMap O A = rootSL2 τ k (GenFixedRootDatum.orbitRoot O)
      (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A) := by
  rw [D.orbitMap_eq_prod, h1, show List.range 1 = [0] from rfl, List.map_singleton,
    List.prod_singleton, D.orbitFactor_apply, D.orbitVec_zero, mul_zero, iterateFrobenius_zero]
  congr 1

theorem orbitX_of_orbitCard_one {O : Set (Fin τ.rank → ℤ)}
    (h1 : GenFixedRootDatum.orbitCard O = 1) (c : D.orbitField O) :
    D.orbitX O c = rootSL2 τ k (GenFixedRootDatum.orbitRoot O) (uSL (c : k)) := by
  rw [GenFixedRootDatum.orbitX, orbitMap_of_orbitCard_one D h1, map_uSL]
  rfl

theorem orbitN_of_orbitCard_one {O : Set (Fin τ.rank → ℤ)}
    (h1 : GenFixedRootDatum.orbitCard O = 1) :
    D.orbitN O = rootSL2 τ k (GenFixedRootDatum.orbitRoot O) WSL := by
  rw [GenFixedRootDatum.orbitN, orbitMap_of_orbitCard_one D h1, map_WSL]

theorem theta_orbitRoot_of_orbitCard_one {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h1 : GenFixedRootDatum.orbitCard O = 1) :
    D.θ (toReal (GenFixedRootDatum.orbitRoot O)) = toReal (GenFixedRootDatum.orbitRoot O) := by
  obtain ⟨b, hb⟩ := Set.ncard_eq_one.1 h1
  have h0 : GenFixedRootDatum.orbitRoot O = b :=
    Set.mem_singleton_iff.1 ((Set.ext_iff.1 hb _).1 (D.orbitRoot_mem hO))
  have h1' : D.orbitVec O 1 = b :=
    Set.mem_singleton_iff.1 ((Set.ext_iff.1 hb _).1 (D.orbitVec_mem hO 1))
  have h := D.toReal_orbitVec hO 1
  rw [pow_one, h1', ← h0] at h
  exact h.symm

theorem F_eq_self_of_mem_orbitGroup {g : ModGL τ k} (hg : g ∈ D.orbitGroup) :
    D.F ⟨g, D.orbitGroup_le_adjointGroup hg⟩ = ⟨g, D.orbitGroup_le_adjointGroup hg⟩ :=
  (D.mem_fixedGroup.1 (D.orbitGroupC_le_fixedGroup (Subgroup.mem_subgroupOf.2 hg))).2

theorem conj_mem_commutator_of_mem_self {G : Type*} [Group G] {H : Subgroup G} {g x : G}
    (hg : g ∈ H) (hx : x ∈ ⁅H, H⁆) : g * x * g⁻¹ ∈ ⁅H, H⁆ := by
  have hxH : x ∈ H := Subgroup.commutator_le_self H hx
  have h1 : ⁅g, x⁆ ∈ ⁅H, H⁆ := Subgroup.commutator_mem_commutator hg hxH
  have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem h1 hx

theorem not_isRoot_of_iform_eq_neg_one {β β' : Fin τ.rank → ℤ}
    (hsl : ∀ γ, IsRoot τ γ → iform γ γ = 2) (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (h : iform β β' = -1) :
    ∀ q ∈ CFSG.LieType.Chevalley.commCandidates, q ≠ (1, 1) →
      ¬ IsRoot τ (q.1 • β + q.2 • β') := by
  intro q hq hne hroot
  have e := hsl _ hroot
  rw [iform_nsmul_add_nsmul, hsl β hβ, hsl β' hβ', h] at e
  simp only [CFSG.LieType.Chevalley.commCandidates, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hne rfl
  all_goals norm_num at e

theorem orbitXY_mem_commutator_of_adjacent_root {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hP : P ∈ D.orbits) (h1O : GenFixedRootDatum.orbitCard O = 1)
    (h1P : GenFixedRootDatum.orbitCard P = 1)
    (hOP : iform (GenFixedRootDatum.orbitRoot O) (GenFixedRootDatum.orbitRoot P) = -1)
    (c : D.orbitField P) :
    D.orbitX P c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ ∧ D.orbitY P c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  classical
  set β := GenFixedRootDatum.orbitRoot O with hβdef
  set β' := GenFixedRootDatum.orbitRoot P with hβ'def
  have hβ : IsRoot τ β := (D.orbitRoot_mem_kernelRoots hO).1
  have hβ' : IsRoot τ β' := (D.orbitRoot_mem_kernelRoots hP).1
  have hsl : ∀ γ, IsRoot τ γ → iform γ γ = 2 := fun γ hγ => D.iform_self_eq_two hγ
  have hne : β ≠ β' := by
    intro h
    rw [h, hsl β' hβ'] at hOP
    omega
  have hneg : ∀ x y : Fin τ.rank → ℤ, iform x (-y) = -iform x y := fun x y => by
    rw [← neg_one_smul ℤ y, iform_smul_right]
    ring
  have hne' : β ≠ -β' := by
    intro h
    have h2 : iform β β' = -2 := by
      rw [h, iform_comm, hneg, hsl β' hβ']
    omega
  have hsum : IsRoot τ (β + β') := by
    have h' : 0 < iform β (-β') := by rw [hneg, hOP]; norm_num
    have := isRoot_sub_of_iform_pos hβ (IsRoot.neg hβ') hne' h'
    rwa [sub_neg_eq_add] at this
  obtain ⟨C, ⟨hC1, hC2⟩, hcomm⟩ := CFSG.HardMathSupport.Foote.Proving.commutator_pinnedX_string_one
    hβ hβ' hne hne' hsum (not_isRoot_of_iform_eq_neg_one hsl hβ hβ' hOP)
  have hbound : CFSG.LieType.Chevalley.RootOps.commConstBound τ = 1 := by
    rcases D.simplyLaced with h | h | h | h <;> subst h <;> rfl
  rw [hbound] at hC2
  have hCu : (C : k) * C = 1 := by
    have : C = 1 ∨ C = -1 := by
      rcases abs_eq (zero_le_one' ℤ) |>.1 (le_antisymm (by exact_mod_cast hC2) hC1) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases this with rfl | rfl <;> simp
  set n : ModGL τ k := rootSL2 τ k β WSL with hn
  have hnC : n ∈ D.orbitGroup := by
    rw [hn, ← orbitN_of_orbitCard_one D h1O]
    exact D.orbitMap_mem_orbitGroup hO WSL
  have hγ : β + β' - (2 * iform β (β + β') / iform β β) • β = β' := by
    rw [iform_add_right, hsl β hβ, hOP]
    norm_num
  obtain ⟨μ, hμ⟩ := CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_conj_pinnedX (K := k)
    hβ hsum
  rw [hγ] at hμ
  set ε : k := (((pinnedData τ β).2.2 : ℤ) : k) with hε
  set ε' : k := (((pinnedData τ β').2.2 : ℤ) : k) with hε'
  have hεε : ε * ε = 1 := pinnedSign_mul_self β
  have hεε' : ε' * ε' = 1 := pinnedSign_mul_self β'
  have huβ : ∀ s : k, rootSL2 τ k β (uSL s) = pinnedX τ k β (ε * s) := fun s => by
    rw [rootSL2_uSL_eq, zsmul_eq_mul]
  have huβ' : ∀ s : k, rootSL2 τ k β' (uSL s) = pinnedX τ k β' (ε' * s) := fun s => by
    rw [rootSL2_uSL_eq, zsmul_eq_mul]
  set lam : k := (μ : k) * C * ε with hlam
  have hconj : ∀ t : k, n * ⁅rootSL2 τ k β (uSL 1), rootSL2 τ k β' (uSL t)⁆ * n⁻¹ =
      rootSL2 τ k β' (uSL (lam * t)) := by
    intro t
    rw [huβ, huβ', commutatorElement_def, pinnedX_neg, pinnedX_neg]
    rw [hcomm k (ε * 1) (ε' * t), hμ, huβ']
    congr 1
    ring
  have hmemX : ∀ t : D.orbitField P, n * ⁅D.orbitX O 1, D.orbitX P t⁆ * n⁻¹ ∈
      ⁅D.orbitGroup, D.orbitGroup⁆ := fun t =>
    conj_mem_commutator_of_mem_self hnC (Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure ⟨O, hO, 1, Or.inl rfl⟩)
      (Subgroup.subset_closure ⟨P, hP, t, Or.inl rfl⟩))
  have hconjX : ∀ t : D.orbitField P, n * ⁅D.orbitX O 1, D.orbitX P t⁆ * n⁻¹ =
      rootSL2 τ k β' (uSL (lam * (t : k))) := by
    intro t
    rw [orbitX_of_orbitCard_one D h1O, orbitX_of_orbitCard_one D h1P, OneMemClass.coe_one]
    exact hconj t
  have hlamC : n * ⁅D.orbitX O 1, D.orbitX P 1⁆ * n⁻¹ ∈ D.orbitGroup :=
    Subgroup.commutator_le_self _ (hmemX 1)
  have hX1 : n * ⁅D.orbitX O 1, D.orbitX P 1⁆ * n⁻¹ = rootSL2 τ k β' (uSL lam) := by
    rw [hconjX, OneMemClass.coe_one, mul_one]
  have hfix := F_eq_self_of_mem_orbitGroup D hlamC
  have hθβ' := theta_orbitRoot_of_orbitCard_one D hP h1P
  have hβ'Δ : β' ∈ unionSimpleRoots D.χ Set.univ := by
    obtain ⟨i, -, hi⟩ := D.mem_unionSimpleRoots_of_mem_orbits hP (D.orbitRoot_mem hP)
    exact ⟨i, Set.mem_univ i, hi⟩
  have hF := D.map_rootSL2 β' hβ'Δ β' hθβ' (uSL lam) ⟨_, D.orbitGroup_le_adjointGroup hlamC⟩ hX1
  rw [hfix] at hF
  change n * ⁅D.orbitX O 1, D.orbitX P 1⁆ * n⁻¹ = _ at hF
  rw [hX1, map_uSL] at hF
  have hlamq : lam ^ D.q = lam := by
    have h1 := CFSG.RankThree.PartTwo.Census.Exceptional.rootSL2_injective hβ' hF
    have h2 := congrArg (fun A : SL2 k => (A : Matrix (Fin 2) (Fin 2) k) 0 1) h1
    simp only [coe_uSL] at h2
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h2
    rw [iterateFrobenius_def] at h2
    exact h2.symm
  have hlamK : lam ∈ D.orbitField P := by
    rw [GenFixedRootDatum.mem_orbitField, h1P, pow_one]
    exact hlamq
  have hlam0 : lam ≠ 0 := by
    have hC0 : (C : k) ≠ 0 := fun h => by rw [h, zero_mul] at hCu; exact zero_ne_one hCu
    have hε0 : ε ≠ 0 := fun h => by rw [h, zero_mul] at hεε; exact zero_ne_one hεε
    exact mul_ne_zero (mul_ne_zero μ.ne_zero hC0) hε0
  have hX : ∀ c : D.orbitField P, D.orbitX P c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
    intro c
    have hmem : lam⁻¹ * (c : k) ∈ D.orbitField P := mul_mem (inv_mem hlamK) c.2
    have e : D.orbitX P c = n * ⁅D.orbitX O 1, D.orbitX P ⟨_, hmem⟩⁆ * n⁻¹ := by
      rw [hconjX, orbitX_of_orbitCard_one D h1P]
      simp only
      rw [← mul_assoc, mul_inv_cancel₀ hlam0, one_mul]
    rw [e]
    exact hmemX _
  refine ⟨hX c, ?_⟩
  have hY : D.orbitY P c = D.orbitN P * D.orbitX P (-c) * (D.orbitN P)⁻¹ := by
    rw [GenFixedRootDatum.orbitY, GenFixedRootDatum.orbitN, GenFixedRootDatum.orbitX,
      ← D.orbitMapHom_apply hP, ← D.orbitMapHom_apply hP, ← D.orbitMapHom_apply hP, ← map_inv,
      ← map_mul, ← map_mul]
    congr 1
    have h := WSL_mul_uSL (-c)
    rw [neg_neg] at h
    rw [h, mul_inv_cancel_right]
  rw [hY]
  exact conj_mem_commutator_of_mem_self (D.orbitMap_mem_orbitGroup hP WSL) (hX (-c))

end CFSG.HardMathSupport.Timmesfeld.LangTorus
