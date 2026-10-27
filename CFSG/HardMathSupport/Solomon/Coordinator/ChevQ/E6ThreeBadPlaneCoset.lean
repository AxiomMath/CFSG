module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompFix

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

section Coset

variable
  {K : Type} [Field K]

private def e6CosetFix (G : Subgroup (ModGL Tag.E6 K)) : Submodule K (RootModule Tag.E6 K) where
  carrier := {v | ∀ g ∈ G, (g : Module.End K (RootModule Tag.E6 K)) v = v}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    intro g hg
    rw [map_add, ha g hg, hb g hg]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro g _
    exact map_zero _
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    intro g hg
    rw [map_smul, hv g hg]

private theorem mem_e6CosetFix {G : Subgroup (ModGL Tag.E6 K)} {v : RootModule Tag.E6 K} :
    v ∈ e6CosetFix G ↔ ∀ g ∈ G, (g : Module.End K (RootModule Tag.E6 K)) v = v :=
  Iff.rfl

private def e6CosetW (ω : Kˣ) (i : Fin 3) : Submodule K (RootModule Tag.E6 K) :=
  LinearMap.ker ((rootDiagUnit .E6 (e6LineChar ω) : Module.End K (RootModule .E6 K)) - 1) ⊓
    (e6CosetFix (e6LineFactor K (i + 1)) ⊓ e6CosetFix (e6LineFactor K (i + 2)))

private theorem mem_e6CosetW {ω : Kˣ} {i : Fin 3} {v : RootModule Tag.E6 K} :
    v ∈ e6CosetW ω i ↔
      (rootDiagUnit .E6 (e6LineChar ω) : Module.End K (RootModule .E6 K)) v = v ∧
        v ∈ e6CosetFix (e6LineFactor K (i + 1)) ∧ v ∈ e6CosetFix (e6LineFactor K (i + 2)) := by
  rw [e6CosetW, Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

private theorem e6CosetW_le {ω : Kˣ} (i : Fin 3) :
    e6CosetW ω i ≤
      LinearMap.ker ((rootDiagUnit .E6 (e6LineChar ω) : Module.End K (RootModule .E6 K)) - 1) := by
  rw [e6CosetW]
  exact inf_le_left

private theorem e6Coset_comm {ω : Kˣ} {g : ModGL Tag.E6 K}
    (hg : g ∈ toralCentralizer .E6 K (e6LineChar ω)) :
    g * rootDiagUnit .E6 (e6LineChar ω) = rootDiagUnit .E6 (e6LineChar ω) * g :=
  (mul_inv_eq_iff_eq_mul.1 (mem_toralCentralizer.1 hg).2).symm

private theorem mem_e6CosetFix_of_map {G H : Subgroup (ModGL Tag.E6 K)} {g : ModGL Tag.E6 K}
    (hGH : G.map (MulAut.conj g).toMonoidHom = H) {v : RootModule Tag.E6 K}
    (hv : v ∈ e6CosetFix G) : (g : Module.End K (RootModule Tag.E6 K)) v ∈ e6CosetFix H := by
  rw [mem_e6CosetFix]
  intro x hx
  rw [← hGH] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  change ((g * y * g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      ((g : Module.End K (RootModule Tag.E6 K)) v) = (g : Module.End K (RootModule Tag.E6 K)) v
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul,
    Module.End.mul_apply, (mem_e6CosetFix.1 hv) y hy]

private theorem mem_e6CosetW_of_conj {ω : Kˣ} {g : ModGL Tag.E6 K} {s : Fin 3}
    (hg : g * rootDiagUnit .E6 (e6LineChar ω) = rootDiagUnit .E6 (e6LineChar ω) * g)
    (hU : ∀ i, (e6LineFactor K i).map (MulAut.conj g).toMonoidHom = e6LineFactor K (i + s))
    {i : Fin 3} {v : RootModule Tag.E6 K} (hv : v ∈ e6CosetW ω i) :
    (g : Module.End K (RootModule Tag.E6 K)) v ∈ e6CosetW ω (i + s) := by
  obtain ⟨h0, h1, h2⟩ := mem_e6CosetW.1 hv
  refine mem_e6CosetW.2 ⟨?_, ?_, ?_⟩
  · rw [← Module.End.mul_apply, ← Units.val_mul, ← hg, Units.val_mul, Module.End.mul_apply, h0]
  · have h := mem_e6CosetFix_of_map (hU (i + 1)) h1
    rwa [add_right_comm i 1 s] at h
  · have h := mem_e6CosetFix_of_map (hU (i + 2)) h2
    rwa [add_right_comm i 2 s] at h

private theorem e6Coset_xUnit_mem {i : Fin 3} {k : Fin Tag.E6.rank}
    (hk : (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots i) (c : K) :
    xUnit Tag.E6 K k c ∈ e6LineFactor K i := by
  rw [← pinnedX_single]
  exact pinnedX_mem_rootSpan (S := (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) hk c

private theorem e6Coset_torusElt_mem {i : Fin 3} {k : Fin Tag.E6.rank}
    (h1 : (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots i)
    (h2 : (-Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots i) (t : Kˣ) :
    torusElt .E6 K k t ∈ e6LineFactor K i := by
  have hy : ∀ c, yUnit .E6 K k c ∈ e6LineFactor K i := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan (S := (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) h2 c
  have hw : ∀ s : Kˣ, weylElt .E6 K k s ∈ e6LineFactor K i := fun s => by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (e6Coset_xUnit_mem h1 _) (hy _)) (e6Coset_xUnit_mem h1 _)
  exact mul_mem (hw t) (hw (-1))

private theorem e6Coset_hVec_fix (i : Fin Tag.E6.rank) {u : ModGL Tag.E6 K}
    (hc : u * xUnit Tag.E6 K i 1 = xUnit Tag.E6 K i 1 * u)
    (hp : (u : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (Pi.single i 1)) =
      rootVec Tag.E6 K (Pi.single i 1))
    (hn : (u : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (-Pi.single i 1)) =
      rootVec Tag.E6 K (-Pi.single i 1)) :
    (u : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K i) = hVec Tag.E6 K i := by
  have h := congrArg (fun g : ModGL Tag.E6 K =>
    (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (-Pi.single i 1))) hc
  simp only [Units.val_mul, Module.End.mul_apply, coe_xUnit, hn,
    CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single, map_add, map_smul, hp, one_smul,
    one_pow] at h
  exact add_left_cancel (add_right_cancel h)

private theorem e6Coset_eight_le_finrank (W : Submodule K (RootModule Tag.E6 K))
    (h0 : hVec Tag.E6 K 0 ∈ W) (h2 : hVec Tag.E6 K 2 ∈ W)
    (hμ : ∀ μ ∈ e6LineRoots 0, rootVec Tag.E6 K μ ∈ W) : 8 ≤ Module.finrank K W := by
  classical
  let g : Fin 2 ⊕ ↥(e6LineRoots 0) → Label Tag.E6 :=
    Sum.elim (fun j => Sum.inl (![0, 2] j))
      (fun μ => Sum.inr ⟨μ.1, isRoot_of_mem_e6LineRoots μ.2⟩)
  have h02 : Function.Injective (![0, 2] : Fin 2 → Fin Tag.E6.rank) := by decide
  have hg : Function.Injective g := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (h02 (Sum.inl.inj h))
    · cases h
    · cases h
    · have h' : (⟨a.1, isRoot_of_mem_e6LineRoots a.2⟩ : {v : Fin Tag.E6.rank → ℤ // IsRoot .E6 v}) =
          ⟨b.1, isRoot_of_mem_e6LineRoots b.2⟩ := Sum.inr.inj h
      exact congrArg Sum.inr (Subtype.ext (Subtype.mk.inj h'))
  have hmem : ∀ k, Finsupp.single (g k) (1 : K) ∈ W := by
    rintro (j | μ)
    · fin_cases j
      · exact h0
      · exact h2
    · have e : Finsupp.single (g (Sum.inr μ)) (1 : K) = rootVec Tag.E6 K μ.1 :=
        (rootVec_eq_single_of_isRoot (isRoot_of_mem_e6LineRoots μ.2)).symm
      rw [e]
      exact hμ μ.1 μ.2
  have hli : LinearIndependent K (fun k => (⟨_, hmem k⟩ : W)) :=
    LinearIndependent.of_comp W.subtype
      ((Finsupp.linearIndependent_single_one K (Label Tag.E6)).comp g hg)
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, card_e6LineRoots] at hcard
  exact hcard

private theorem e6Coset_eight_le_W0 {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) :
    8 ≤ Module.finrank K (e6CosetW ω 0) := by
  have hFM : e6LineFactor K 0 ≤ toralRootGroup .E6 K (e6LineChar ω) := by
    show _ ≤ torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω))
    rw [e6Line_kernel hw3 hw1, rootSpan_eq_iSup_e6LineFactor]
    exact (le_iSup (fun i => e6LineFactor K i) 0).trans le_sup_right
  have hh₀M : rootDiagUnit .E6 (e6LineChar ω) ∈ toralRootGroup .E6 K (e6LineChar ω) :=
    Subgroup.mem_sup_left (e6Line_diag_mem_torusGroup ω)
  have hFV₀ := fix_of_commute_e6LineFactor_zero hw3 hw1 hh₀M fun g hg =>
    (e6Coset_comm (toralRootGroup_le _ (hFM hg))).symm
  have hfixR : ∀ j : Fin 3, j ≠ 0 → ∀ μ ∈ e6LineRoots 0,
      rootVec Tag.E6 K μ ∈ e6CosetFix (e6LineFactor K j) := fun j hj μ hμ =>
    mem_e6CosetFix.2 fun g hg => e6LineFactor_fix_rootVec (Ne.symm hj) hμ hg
  have hfixH : ∀ j : Fin 3, j ≠ 0 → ∀ k : Fin Tag.E6.rank,
      (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots 0 →
      (-Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots 0 →
      hVec Tag.E6 K k ∈ e6CosetFix (e6LineFactor K j) := fun j hj k hk hk' =>
    mem_e6CosetFix.2 fun g hg => e6Coset_hVec_fix k
      (e6LineFactor_commute hj hg (e6Coset_xUnit_mem hk 1))
      (e6LineFactor_fix_rootVec (Ne.symm hj) hk hg) (e6LineFactor_fix_rootVec (Ne.symm hj) hk' hg)
  refine e6Coset_eight_le_finrank _ (mem_e6CosetW.2 ⟨hFV₀.2.1, ?_, ?_⟩)
    (mem_e6CosetW.2 ⟨hFV₀.2.2, ?_, ?_⟩)
    fun μ hμ => mem_e6CosetW.2 ⟨hFV₀.1 μ hμ, hfixR 1 (by decide) μ hμ, hfixR 2 (by decide) μ hμ⟩
  · exact hfixH 1 (by decide) 0 (by decide) (by decide)
  · exact hfixH 2 (by decide) 0 (by decide) (by decide)
  · exact hfixH 1 (by decide) 2 (by decide) (by decide)
  · exact hfixH 2 (by decide) 2 (by decide) (by decide)

private theorem e6Coset_units_injective (g : ModGL Tag.E6 K) :
    Function.Injective (g : Module.End K (RootModule Tag.E6 K)) := by
  intro x y h
  have hx : ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      ((g : Module.End K (RootModule Tag.E6 K)) x) = x := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hy : ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      ((g : Module.End K (RootModule Tag.E6 K)) y) = y := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  rw [← hx, h, hy]

private theorem e6Coset_finrank_le {P Q : Submodule K (RootModule Tag.E6 K)}
    (g : ModGL Tag.E6 K) (h : ∀ v ∈ P, (g : Module.End K (RootModule Tag.E6 K)) v ∈ Q) :
    Module.finrank K P ≤ Module.finrank K Q := by
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (g : Module.End K (RootModule Tag.E6 K)).restrict h) fun x y hxy => Subtype.ext ?_
  have e : (g : Module.End K (RootModule Tag.E6 K)) x =
      (g : Module.End K (RootModule Tag.E6 K)) y := congrArg Subtype.val hxy
  exact e6Coset_units_injective g e

private theorem e6Coset_ker_inf_eq_bot {P Q R : Submodule K (RootModule Tag.E6 K)}
    (g : ModGL Tag.E6 K) (hPQ : P ⊓ Q = ⊥) (hR : R ⊓ (P ⊔ Q) = ⊥)
    (hgP : ∀ v ∈ P, (g : Module.End K (RootModule Tag.E6 K)) v ∈ Q)
    (hgQ : ∀ v ∈ Q, (g : Module.End K (RootModule Tag.E6 K)) v ∈ R) :
    LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ (P ⊔ Q) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv'
  obtain ⟨hv, hvPQ⟩ := Submodule.mem_inf.1 hv'
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hvPQ
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, map_add] at hv
  have hgq : (g : Module.End K (RootModule Tag.E6 K)) q ∈ R ⊓ (P ⊔ Q) := by
    refine Submodule.mem_inf.2 ⟨hgQ q hq, ?_⟩
    have e : (g : Module.End K (RootModule Tag.E6 K)) q =
        p + q - (g : Module.End K (RootModule Tag.E6 K)) p := by
      rw [← hv]
      abel
    rw [e]
    exact sub_mem (add_mem (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hq))
      (Submodule.mem_sup_right (hgP p hp))
  rw [hR, Submodule.mem_bot] at hgq
  have hq0 : q = 0 := e6Coset_units_injective g (by rw [hgq, map_zero])
  subst hq0
  rw [map_zero, add_zero, add_zero] at hv
  have hpPQ : p ∈ P ⊓ Q := Submodule.mem_inf.2 ⟨hp, hv ▸ hgP p hp⟩
  rw [hPQ, Submodule.mem_bot] at hpPQ
  rw [hpPQ, add_zero]
  exact Submodule.zero_mem _

private theorem e6Coset_count {F P Q R : Submodule K (RootModule Tag.E6 K)} {g : ModGL Tag.E6 K}
    (hF : Module.finrank K F = 24) (hP : P ≤ F) (hQ : Q ≤ F) (hPQ : P ⊓ Q = ⊥)
    (hR : R ⊓ (P ⊔ Q) = ⊥) (h8P : 8 ≤ Module.finrank K P) (h8Q : 8 ≤ Module.finrank K Q)
    (hgP : ∀ v ∈ P, (g : Module.End K (RootModule Tag.E6 K)) v ∈ Q)
    (hgQ : ∀ v ∈ Q, (g : Module.End K (RootModule Tag.E6 K)) v ∈ R) :
    Module.finrank K ↥(LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ F) ≤ 8 := by
  have hker := e6Coset_ker_inf_eq_bot g hPQ hR hgP hgQ
  have hX : LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ F ⊓ (P ⊔ Q) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_right _ inf_le_left).trans hker.le)
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ F) (P ⊔ Q)
  rw [hPQ, finrank_bot] at e1
  rw [hX, finrank_bot] at e2
  have hle : Module.finrank K ↥(LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ F ⊔
      (P ⊔ Q)) ≤ Module.finrank K F :=
    Submodule.finrank_mono (sup_le inf_le_right (sup_le hP hQ))
  omega

private theorem e6Coset_map_sum_smul {M : Type*} [AddCommGroup M] [Module K M] (f : M →ₗ[K] M)
    {y : Fin Tag.E6.rank → M} {lam : Fin Tag.E6.rank → K} {v : M}
    (hy : ∀ j, f (y j) = y j + lam j • v) (c : Fin Tag.E6.rank → K) :
    f (∑ j, c j • y j) = ∑ j, c j • y j + (∑ j, c j * lam j) • v := by
  simp only [map_sum, map_smul, hy, smul_add, Finset.sum_add_distrib, smul_smul, Finset.sum_smul]

private theorem e6Coset_sum_mul_eq_zero {M : Type*} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) {y : Fin Tag.E6.rank → M} {lam : Fin Tag.E6.rank → K} {v : M}
    (hy : ∀ j, f (y j) = y j + lam j • v) (hv : v ≠ 0) {c : Fin Tag.E6.rank → K}
    (h : f (∑ j, c j • y j) = ∑ j, c j • y j) : ∑ j, c j * lam j = 0 := by
  rw [e6Coset_map_sum_smul f hy c, add_eq_left] at h
  exact (smul_eq_zero.1 h).resolve_right hv

private theorem e6Coset_xOp_hVec (k j : Fin Tag.E6.rank) :
    xOp Tag.E6 K k 1 (hVec Tag.E6 K j) =
      hVec Tag.E6 K j + ((Tag.E6.cartan j k).natAbs : K) • rootVec Tag.E6 K (Pi.single k 1) := by
  rw [CFSG.Blueprint.Chevalley.xOp_apply_hVec, mul_one]

private theorem e6Coset_sum_six {M : Type*} [AddCommMonoid M] (f : Fin Tag.E6.rank → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 :=
  Fin.sum_univ_six f

private theorem e6Coset_cartan_sums (c : Fin Tag.E6.rank → K) :
    ∑ j, c j * ((Tag.E6.cartan j 0).natAbs : K) = 2 * c 0 + c 2 ∧
      ∑ j, c j * ((Tag.E6.cartan j 2).natAbs : K) = c 0 + 2 * c 2 + c 3 ∧
      ∑ j, c j * ((Tag.E6.cartan j 4).natAbs : K) = c 3 + 2 * c 4 + c 5 ∧
      ∑ j, c j * ((Tag.E6.cartan j 5).natAbs : K) = c 4 + 2 * c 5 ∧
      ∑ j, c j * ((Tag.E6.cartan j 1).natAbs : K) = 2 * c 1 + c 3 := by
  have key : ∀ c : Fin 6 → K,
      ∑ j, c j * ((Tag.cartanE 6 j 0).natAbs : K) = 2 * c 0 + c 2 ∧
        ∑ j, c j * ((Tag.cartanE 6 j 2).natAbs : K) = c 0 + 2 * c 2 + c 3 ∧
        ∑ j, c j * ((Tag.cartanE 6 j 4).natAbs : K) = c 3 + 2 * c 4 + c 5 ∧
        ∑ j, c j * ((Tag.cartanE 6 j 5).natAbs : K) = c 4 + 2 * c 5 ∧
        ∑ j, c j * ((Tag.cartanE 6 j 1).natAbs : K) = 2 * c 1 + c 3 := by
    intro c
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_six, Tag.cartanE] <;> ring
  exact key c

private def e6CosetLam (j : Fin Tag.E6.rank) : ℤ :=
  ∑ l, e6LineWord.foldr (RootWalk.hStep Tag.E6) (Pi.single j 1) l *
    ((Tag.E6.cartan l 2).natAbs : ℤ)

private theorem e6CosetLam_eq : e6CosetLam 0 = 0 ∧ e6CosetLam 1 = -1 ∧ e6CosetLam 2 = 0 ∧
    e6CosetLam 3 = -1 ∧ e6CosetLam 4 = 0 ∧ e6CosetLam 5 = 0 := by
  decide +kernel

private theorem e6Coset_lam_sum (c : Fin Tag.E6.rank → K) :
    ∑ j, c j * ((e6CosetLam j : ℤ) : K) = -c 1 - c 3 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := e6CosetLam_eq
  rw [e6Coset_sum_six, h0, h1, h2, h3, h4, h5]
  push_cast
  ring

private theorem e6Coset_reduced : (coxeterSystem Tag.E6).IsReduced e6LineWord :=
  isReduced_of_reducedCheck (by decide +kernel)

private theorem e6Coset_canonicalRep_hVec (j : Fin Tag.E6.rank) :
    (canonicalRep (coxeterSystem .E6) K e6LineWeyl : Module.End K (RootModule Tag.E6 K))
        (hVec Tag.E6 K j) =
      ∑ l, ((e6LineWord.foldr (RootWalk.hStep Tag.E6) (Pi.single j 1) l : ℤ) : K) •
        hVec Tag.E6 K l := by
  rw [← RootWalk.hVecSum_single (R := K) j,
    show e6LineWeyl = (coxeterSystem Tag.E6).wordProd e6LineWord from rfl,
    canonicalRep_wordProd e6Coset_reduced]
  exact RootWalk.prod_weylElt_hVecSum (τ := Tag.E6) K e6LineWord (Pi.single j 1)

private theorem e6Coset_xOp_canonicalRep_hVec (j : Fin Tag.E6.rank) :
    xOp Tag.E6 K 2 1 ((canonicalRep (coxeterSystem .E6) K e6LineWeyl :
        Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K j)) =
      (canonicalRep (coxeterSystem .E6) K e6LineWeyl : Module.End K (RootModule Tag.E6 K))
          (hVec Tag.E6 K j) + ((e6CosetLam j : ℤ) : K) • rootVec Tag.E6 K (Pi.single 2 1) := by
  rw [e6Coset_canonicalRep_hVec, e6Coset_map_sum_smul (xOp Tag.E6 K 2 1) (e6Coset_xOp_hVec 2),
    e6CosetLam, Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_natCast]

private theorem e6Coset_key : ∀ β ∈ rootFinset .E6, (3 : ℤ) ∣ β e6KacNode →
    (3 : ℤ) ∣ ∑ j, Tag.E6.cartan 0 j * β j → (3 : ℤ) ∣ ∑ j, Tag.E6.cartan 4 j * β j →
      (3 : ℤ) ∣ ∑ j, Tag.E6.cartan 1 j * β j → False := by
  decide +kernel

private theorem e6Coset_three_ne_zero {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) : (3 : K) ≠ 0 := by
  intro h
  have hω : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have h2 : ((ω : K) - 1) ^ 3 = 0 := by
    calc ((ω : K) - 1) ^ 3 = (ω : K) ^ 3 - 3 * (ω : K) ^ 2 + 3 * (ω : K) - 1 := by ring
      _ = 0 := by rw [hω, h]; ring
  exact h1 (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)))

private theorem e6Coset_eq_zero {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    {z : RootModule Tag.E6 K}
    (hF : (rootDiagUnit .E6 (e6LineChar ω) : Module.End K (RootModule .E6 K)) z = z)
    (h0 : z ∈ e6CosetFix (e6LineFactor K 0)) (h1 : z ∈ e6CosetFix (e6LineFactor K 1))
    (h2 : z ∈ e6CosetFix (e6LineFactor K 2)) : z = 0 := by
  have hroot : ∀ β : {v : Fin Tag.E6.rank → ℤ // IsRoot .E6 v}, z (Sum.inr β) = 0 := by
    intro β
    by_contra hz
    have hF' : z ∈ LinearMap.ker (rootDiag (e6LineChar ω) - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hF
    rw [ker_rootDiag_sub_one, Finsupp.mem_supported] at hF'
    have hb : rootChar (e6LineChar ω) β.1 = 1 := hF' (Finsupp.mem_support_iff.2 hz)
    rw [rootChar_e6LineChar, e6Line_zpow_eq_one_iff_three_dvd hw3 hw1] at hb
    have htor : ∀ (i : Fin 3) (k : Fin Tag.E6.rank),
        (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots i →
        (-Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots i →
        z ∈ e6CosetFix (e6LineFactor K i) → (3 : ℤ) ∣ ∑ j, Tag.E6.cartan k j * β.1 j := by
      intro i k hk hk' hzi
      have hc := DFunLike.congr_fun ((mem_e6CosetFix.1 hzi) _ (e6Coset_torusElt_mem hk hk' ω))
        (Sum.inr β)
      rw [torusElt_apply_eq] at hc
      have hc' : (((ω ^ (∑ j, Tag.E6.cartan k j * β.1 j) : Kˣ) : K) - 1) * z (Sum.inr β) = 0 := by
        rw [sub_mul, one_mul, sub_eq_zero]
        exact hc
      rw [← e6Line_zpow_eq_one_iff_three_dvd hw3 hw1]
      exact Units.val_eq_one.1 (sub_eq_zero.1 ((mul_eq_zero.1 hc').resolve_right hz))
    exact e6Coset_key β.1 (mem_rootFinset.2 β.2) hb (htor 0 0 (by decide) (by decide) h0)
      (htor 1 4 (by decide) (by decide) h1) (htor 2 1 (by decide) (by decide) h2)
  obtain ⟨c, rfl⟩ : ∃ c : Fin Tag.E6.rank → K, z = ∑ j, c j • hVec Tag.E6 K j := by
    refine ⟨fun j => z (Sum.inl j), ?_⟩
    ext b
    rcases b with j | β
    · simp [hVec, Finsupp.single_apply]
    · simp [hVec, Finsupp.single_apply, hroot β]
  have hE : ∀ (i : Fin 3) (k : Fin Tag.E6.rank),
      (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots i →
      (∑ j, c j • hVec Tag.E6 K j) ∈ e6CosetFix (e6LineFactor K i) →
        ∑ j, c j * ((Tag.E6.cartan j k).natAbs : K) = 0 := fun i k hk hzi =>
    e6Coset_sum_mul_eq_zero (xOp Tag.E6 K k 1) (e6Coset_xOp_hVec k)
      (rootVec_ne_zero (isRoot_single _ k)) ((mem_e6CosetFix.1 hzi) _ (e6Coset_xUnit_mem hk 1))
  obtain ⟨s0, s2, s4, s5, s1⟩ := e6Coset_cartan_sums c
  have e0 := hE 0 0 (by decide) h0
  have e2 := hE 0 2 (by decide) h0
  have e4 := hE 1 4 (by decide) h1
  have e5 := hE 1 5 (by decide) h1
  have e1 := hE 2 1 (by decide) h2
  rw [s0] at e0
  rw [s2] at e2
  rw [s4] at e4
  rw [s5] at e5
  rw [s1] at e1
  have hnz := mem_e6CosetFix_of_map (e6LineFactor_conj 2) h2
  rw [show (2 : Fin 3) + 1 = 0 from rfl] at hnz
  have hx := (mem_e6CosetFix.1 hnz) _ (e6Coset_xUnit_mem (i := 0) (k := 2) (by decide) 1)
  have e : (canonicalRep (coxeterSystem .E6) K e6LineWeyl : Module.End K (RootModule Tag.E6 K))
      (∑ j, c j • hVec Tag.E6 K j) =
        ∑ j, c j • (canonicalRep (coxeterSystem .E6) K e6LineWeyl :
          Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K j) := by
    simp only [map_sum, map_smul]
  rw [e] at hx
  have eN := e6Coset_sum_mul_eq_zero (xOp Tag.E6 K 2 1) e6Coset_xOp_canonicalRep_hVec
    (rootVec_ne_zero (isRoot_single _ 2)) hx
  rw [e6Coset_lam_sum] at eN
  have hK3 := e6Coset_three_ne_zero hw3 hw1
  have c1 : c 1 = 0 := by linear_combination e1 + eN
  have c3 : c 3 = 0 := by linear_combination -eN - c1
  have c0 : c 0 = 0 := by
    have h : 3 * c 0 = 0 := by linear_combination 2 * e0 - e2 + c3
    exact (mul_eq_zero.1 h).resolve_left hK3
  have c2 : c 2 = 0 := by linear_combination e0 - 2 * c0
  have c5 : c 5 = 0 := by
    have h : 3 * c 5 = 0 := by linear_combination 2 * e5 - e4 + c3
    exact (mul_eq_zero.1 h).resolve_left hK3
  have c4 : c 4 = 0 := by linear_combination e5 - 2 * c5
  rw [e6Coset_sum_six, c0, c1, c2, c3, c4, c5]
  simp only [zero_smul, add_zero]

theorem e6PlaneCoset_proved : E6PlaneCosetStmt := by
  intro K _ _ ω hw3 hw1 u hu huM
  obtain ⟨m, hm, j, hj, rfl⟩ := e6Line_centralizer_mul hw3 hw1 hu
  have hnW : ∀ i : Fin 3, ∀ v ∈ e6CosetW ω i,
      (canonicalRep (coxeterSystem .E6) K e6LineWeyl : Module.End K (RootModule Tag.E6 K)) v ∈
        e6CosetW ω (i + 1) := fun i v hv =>
    mem_e6CosetW_of_conj (e6Coset_comm (canonicalRep_mem_toralCentralizer
      (e6LineWeyl_mem_stabilizer hw3 hw1))) (fun k => e6LineFactor_conj k) hv
  have hn01 : ∀ v ∈ e6CosetW ω 0,
      (canonicalRep (coxeterSystem .E6) K e6LineWeyl : Module.End K (RootModule Tag.E6 K)) v ∈
        e6CosetW ω 1 := fun v hv => by
    have h := hnW 0 v hv
    rwa [show (0 : Fin 3) + 1 = 1 from rfl] at h
  have hn12 : ∀ v ∈ e6CosetW ω 1,
      (canonicalRep (coxeterSystem .E6) K e6LineWeyl : Module.End K (RootModule Tag.E6 K)) v ∈
        e6CosetW ω 2 := fun v hv => by
    have h := hnW 1 v hv
    rwa [show (1 : Fin 3) + 1 = 2 from rfl] at h
  have hn20 : ∀ v ∈ e6CosetW ω 2,
      (canonicalRep (coxeterSystem .E6) K e6LineWeyl : Module.End K (RootModule Tag.E6 K)) v ∈
        e6CosetW ω 0 := fun v hv => by
    have h := hnW 2 v hv
    rwa [show (2 : Fin 3) + 1 = 0 from rfl] at h
  have hmW : ∀ i : Fin 3, ∀ v ∈ e6CosetW ω i,
      (m : Module.End K (RootModule Tag.E6 K)) v ∈ e6CosetW ω i := fun i v hv => by
    have h := mem_e6CosetW_of_conj (s := 0) (e6Coset_comm (toralRootGroup_le _ hm))
      (fun k => by
        rw [add_zero]
        exact map_conj_eq_of_mem_normalizer_aux (e6LineFactor_normalizer hw3 hw1 k hm)) hv
    rwa [add_zero] at h
  have h8₁ : 8 ≤ Module.finrank K (e6CosetW ω 1) :=
    (e6Coset_eight_le_W0 hw3 hw1).trans (e6Coset_finrank_le _ hn01)
  have h8₂ : 8 ≤ Module.finrank K (e6CosetW ω 2) := h8₁.trans (e6Coset_finrank_le _ hn12)
  have h12 : e6CosetW ω 1 ⊓ e6CosetW ω 2 = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨hF, h12', h10⟩ := mem_e6CosetW.1 hv1
    obtain ⟨-, -, h21⟩ := mem_e6CosetW.1 hv2
    rw [show (1 : Fin 3) + 1 = 2 from rfl] at h12'
    rw [show (1 : Fin 3) + 2 = 0 from rfl] at h10
    rw [show (2 : Fin 3) + 2 = 1 from rfl] at h21
    exact (Submodule.mem_bot K).2 (e6Coset_eq_zero hw3 hw1 hF h10 h21 h12')
  have hsup : e6CosetW ω 1 ⊔ e6CosetW ω 2 ≤ e6CosetFix (e6LineFactor K 0) := by
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · have h := (mem_e6CosetW.1 hv).2.2
      rwa [show (1 : Fin 3) + 2 = 0 from rfl] at h
    · have h := (mem_e6CosetW.1 hv).2.1
      rwa [show (2 : Fin 3) + 1 = 0 from rfl] at h
  have h0_12 : e6CosetW ω 0 ⊓ (e6CosetW ω 1 ⊔ e6CosetW ω 2) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv0, hv12⟩ := Submodule.mem_inf.1 hv
    obtain ⟨hF, h01, h02⟩ := mem_e6CosetW.1 hv0
    rw [show (0 : Fin 3) + 1 = 1 from rfl] at h01
    rw [show (0 : Fin 3) + 2 = 2 from rfl] at h02
    exact (Submodule.mem_bot K).2 (e6Coset_eq_zero hw3 hw1 hF (hsup hv12) h01 h02)
  interval_cases j
  · exact absurd (by rw [pow_zero, mul_one]; exact hm) huM
  · refine e6Coset_count (e6Line_finrank_fixed_aux hw3 hw1) (e6CosetW_le 1) (e6CosetW_le 2) h12
      h0_12 h8₁ h8₂ (fun v hv => ?_) (fun v hv => ?_)
    · rw [pow_one, Units.val_mul, Module.End.mul_apply]
      exact hmW 2 _ (hn12 v hv)
    · rw [pow_one, Units.val_mul, Module.End.mul_apply]
      exact hmW 0 _ (hn20 v hv)
  · refine e6Coset_count (e6Line_finrank_fixed_aux hw3 hw1) (e6CosetW_le 2) (e6CosetW_le 1)
      (by rw [inf_comm]; exact h12) (by rw [sup_comm]; exact h0_12) h8₂ h8₁
      (fun v hv => ?_) (fun v hv => ?_)
    · rw [pow_two, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact hmW 1 _ (hn01 _ (hn20 v hv))
    · rw [pow_two, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact hmW 0 _ (hn20 _ (hn12 v hv))

end Coset

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
