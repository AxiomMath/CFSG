module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerShape
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalRootGrading

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Tuple

variable (τ : Tag) (K : Type) [Field K]

@[expose] def zTuple (k : Fin τ.rank) : Fin τ.rank → Kˣ :=
  fun j => (-1 : Kˣ) ^ τ.cartan k j

variable {τ K}

theorem zTuple_mem (k : Fin τ.rank) (i : Fin τ.rank) :
    zTuple τ K k i = 1 ∨ zTuple τ K k i = -1 := by
  rcases Int.even_or_odd (τ.cartan k i) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem neg_one_zpow_eq_neg_one_iff (hK : ringChar K ≠ 2) (n : ℤ) :
    (-1 : Kˣ) ^ n = -1 ↔ ¬ Even n := by
  have h1 : (1 : Kˣ) ≠ -1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK (congrArg Units.val h).symm
  rcases Int.even_or_odd n with h | h
  · rw [h.neg_one_zpow]
    exact ⟨fun h' => absurd h' h1, fun h' => absurd h h'⟩
  · rw [h.neg_one_zpow]
    exact ⟨fun _ => Int.not_even_iff_odd.mpr h, fun _ => rfl⟩

theorem signTupleBits_zTuple (hK : ringChar K ≠ 2) (k : Fin τ.rank) :
    signTupleBits (zTuple τ K k) = zMask τ k := by
  classical
  funext j
  rw [Bool.eq_iff_iff]
  simp only [signTupleBits, zMask, decide_eq_true_eq]
  exact neg_one_zpow_eq_neg_one_iff hK _

end Tuple

section Main

variable {τ : Tag} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem subgroupOf_rootSubgroup_eq_rootGroup (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    (rootSubgroup τ K γ).subgroupOf (adjointGroup τ K) = rootGroup F K γ := by
  rw [rootGroup_of_isRoot hγ]
  exact F.subgroupOf_rootSubgroup_eq K ⟨γ, hγ⟩

theorem stdLayer_adjoint (hK : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K) (k : Fin τ.rank)
    {δ₂ δ₃ : Fin τ.rank → ℤ} (hS : LayerShape (zChar τ k) (Pi.single k 1) δ₂ δ₃) :
    StdLayer (rootGroup (rootOperatorFamily τ) K (Pi.single k 1) ⊔
        rootGroup (rootOperatorFamily τ) K (-Pi.single k 1))
      (rootGroup (rootOperatorFamily τ) K δ₂ ⊔ rootGroup (rootOperatorFamily τ) K (-δ₂)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set F := rootOperatorFamily τ with hF
  set χ := zChar τ k with hχ
  set e : Fin τ.rank → ℤ := Pi.single k 1 with he
  set i₁ : KernelComponent χ := Quotient.mk _ ⟨e, hS.mem_e⟩ with hi₁
  set i₂ : KernelComponent χ := Quotient.mk _ ⟨δ₂, hS.mem₂⟩ with hi₂
  have hi12 : i₁ ≠ i₂ := hS.mk_e_ne
  have hi21 : i₂ ≠ i₁ := fun h => hi12 h.symm
  set S₁ := componentRootSpan K χ i₁ with hS₁def
  set S₂ := componentRootSpan K χ i₂ with hS₂def
  have hS₁le : S₁ ≤ adjointGroup τ K :=
    (componentRootSpan_le K i₁).trans (rootSpan_le_adjointGroup K _)
  have hS₂le : S₂ ≤ adjointGroup τ K :=
    (componentRootSpan_le K i₂).trans (rootSpan_le_adjointGroup K _)
  have hS₁ : S₁ = rootSubgroup τ K e ⊔ rootSubgroup τ K (-e) := by
    have hset : {α | ∃ h : α ∈ kernelRoots χ,
        (Quotient.mk (kernelRootSetoid χ) ⟨α, h⟩ : KernelComponent χ) = i₁} = {e, -e} := by
      ext α
      constructor
      · rintro ⟨h, hα⟩
        exact (hS.mk_eq_e_iff α h).1 hα
      · rintro (rfl | rfl)
        · exact ⟨hS.mem_e, rfl⟩
        · exact ⟨neg_mem_kernelRoots hS.mem_e, (hS.mk_eq_e_iff _ _).2 (Or.inr rfl)⟩
    change rootSpan τ K _ = _
    rw [hset, CFSG.LieType.Chevalley.OddToralFixed.rootSpan_pair]
  set G := ↥(adjointGroup τ K) with hG
  set Rstd : Subgroup G := rootGroup F K e ⊔ rootGroup F K (-e) with hRstd
  have hRstd' : Rstd = S₁.subgroupOf (adjointGroup τ K) := by
    rw [hS₁, hRstd]
    exact (subgroupOf_rootSubgroup_sup_eq F hS.mem_e.1).symm
  have mem_Rstd : ∀ y : G, y ∈ Rstd ↔ (y : ModGL τ K) ∈ S₁ := fun y => by
    rw [hRstd', Subgroup.mem_subgroupOf]
  set L : Subgroup G := S₂.subgroupOf (adjointGroup τ K) with hL
  have mem_L : ∀ y : G, y ∈ L ↔ (y : ModGL τ K) ∈ S₂ := fun y => Subgroup.mem_subgroupOf
  have hG4 : ∀ δ (h : δ ∈ kernelRoots χ), δ ≠ e → δ ≠ -e → rootGroup F K δ ≤ L := by
    intro δ h hne hne'
    have hle : rootSubgroup τ K δ ≤ S₂ := by
      have := rootSubgroup_le_componentRootSpan K (χ := χ) ⟨δ, h⟩
      rwa [hS.conn δ h hne hne'] at this
    rw [← subgroupOf_rootSubgroup_eq_rootGroup F h.1]
    exact fun x hx => hle hx
  refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hq : CFSG.IsQuasisimple ↥S₂ := isQuasisimple_componentRootSpan_of_five_le hK h5 χ i₂
    exact (open_isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hS₂le)).2 (open_isQuasisimple hq)
  ·
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : (x : ModGL τ K) ∈ Subgroup.centralizer (S₁ : Set (ModGL τ K)) :=
      componentRootSpan_le_centralizer K hi21 ((mem_L x).1 hx)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 _ ((mem_Rstd y).1 hy))
  ·
    intro P hPC hPperf
    set z₀ : G := torusHom K k (-1) with hz₀
    have hz₀R : z₀ ∈ Rstd := torus_le_rankOne k ⟨-1, rfl⟩
    have hz₀val : (z₀ : ModGL τ K) = rootDiagUnit τ (zTuple τ K k) :=
      torusElt_eq_rootDiagUnit k (-1)
    have hb := zTuple_mem (τ := τ) (K := K) k
    have hCz := centralizer_eq_subgroupOf_toralCentralizer (zTuple τ K k) z₀ hz₀val
    have hPz : P ≤ Subgroup.centralizer ({z₀} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp (hPC hx) _ hz₀R
    rw [hCz] at hPz
    set P' : Subgroup (ModGL τ K) := P.map (adjointGroup τ K).subtype with hP'
    have hP'X : P' ≤ toralCentralizer τ K (zTuple τ K k) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hPz hx
    have hP'perf : P' ≤ ⁅P', P'⁆ := by
      rw [hP', ← Subgroup.map_commutator]
      exact Subgroup.map_mono hPperf
    obtain ⟨-, -, -, hD, -⟩ :=
      odd_toral_involution_centralizer_p_component_root_reduction τ K hK (zTuple τ K k) hb
    have hP'S : P' ≤ rootSpan τ K (rootCharKernel (zTuple τ K k)) :=
      le_of_perfect_of_derivedSeries_two' hD hP'X hP'perf
    have hker : rootCharKernel (zTuple τ K k) = kernelRoots χ := by
      rw [rootCharKernel_eq_kernelRoots hK hb, signTupleBits_zTuple hK]
      rfl
    rw [hker] at hP'S
    have hSsup : rootSpan τ K (kernelRoots χ) = S₁ ⊔ S₂ := by
      rw [← iSup_componentRootSpan K]
      refine le_antisymm (iSup_le fun i => ?_)
        (sup_le (le_iSup (fun i => componentRootSpan K χ i) i₁)
          (le_iSup (fun i => componentRootSpan K χ i) i₂))
      rcases hS.exists_eq i with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    rw [hSsup] at hP'S
    have hP'C : P' ≤ Subgroup.centralizer (S₁ : Set (ModGL τ K)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hy : (⟨s, hS₁le hs⟩ : G) ∈ Rstd := (mem_Rstd _).2 hs
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hPC hx) _ hy)
    have hP'S₂ : P' ≤ S₂ :=
      le_of_perfect_of_le_sup_of_commutes (componentRootSpan_le_centralizer K hi12) hP'S hP'perf
        hP'C
    intro x hx
    exact (mem_L x).2 (hP'S₂ ⟨x, hx, rfl⟩)
  ·
    refine sup_le (hG4 δ₂ hS.mem₂ hS.ne₂ hS.ne₂') (hG4 (-δ₂) (neg_mem_kernelRoots hS.mem₂) ?_ ?_)
    · intro h
      exact hS.ne₂' (neg_eq_iff_eq_neg.mp h)
    · intro h
      exact hS.ne₂ (neg_inj.mp h)
  ·
    intro heq
    have h3 : rootGroup F K δ₃ ≤ L := hG4 δ₃ hS.mem₃ hS.ne₃ hS.ne₃'
    rw [← heq] at h3
    apply not_rootSubgroup_le_rootSubgroup_sup (K := K) hS.mem₂.1 hS.mem₃.1 hS.ne₃₂ hS.ne₃₂'
    have hR₂ : (rootSubgroup τ K δ₂ ⊔ rootSubgroup τ K (-δ₂)).subgroupOf (adjointGroup τ K) =
        rootGroup F K δ₂ ⊔ rootGroup F K (-δ₂) := subgroupOf_rootSubgroup_sup_eq F hS.mem₂.1
    intro y hy
    have hy' : (⟨y, rootSubgroup_le_adjointGroup δ₃ hy⟩ : G) ∈ rootGroup F K δ₃ := by
      rw [← subgroupOf_rootSubgroup_eq_rootGroup F hS.mem₃.1]
      exact hy
    have := h3 hy'
    rw [← hR₂] at this
    exact this

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic
