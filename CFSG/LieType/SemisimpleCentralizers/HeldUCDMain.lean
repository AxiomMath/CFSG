module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDCent
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDFactors
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDIso
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

theorem finite_linear_endo (K : Type) [Ring K] (V : Type) [AddCommGroup V] [Module K V]
    [Finite V] : Finite (V →ₗ[K] V) :=
  Finite.of_injective (fun g : V →ₗ[K] V => (g : V → V)) DFunLike.coe_injective

theorem unitaryOrLinear_top (Q : ℕ) (K V : Type) [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (e : ℕ) (hcard : Nat.card K = Q ^ (2 * e)) :
    Held.UnitaryOrLinearBlock Q ↥(⊤ : Subgroup (LinearMap.GeneralLinearGroup K V)) := by
  right
  refine ⟨Module.finrank K V, e, K, inferInstance, inferInstance, hcard, ⟨?_⟩⟩
  exact Subgroup.topEquiv.trans (Matrix.GeneralLinearGroup.toLin' (Module.finBasis K V)).symm

section Blocks

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}
  [hK : ∀ f : ↥(Fset s b F), Fact (∀ x ∈ Vf s b F f.1, aeval s f.1 *ᵥ x = 0)]

theorem finite_Bl [Finite L] (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) :
    Finite ↥(Bl H f) := by
  haveI := finite_linear_endo (AdjoinRoot f.1) (Vf s b F f.1)
  exact Subtype.finite

theorem block_top_unitaryOrLinear [Finite L] (H : PrimaryHyp τ s m F a b) (Q : ℕ)
    (hQ : Nat.card L = Q ^ 2) (f : ↥(Fset s b F)) :
    Held.UnitaryOrLinearBlock Q
      ↥(⊤ : Subgroup (LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1))) := by
  haveI : Fact (Irreducible f.1) := ⟨H.hirr f.1 (mem_Fset.mp f.2).1⟩
  have hf0 : f.1 ≠ 0 := (H.hirr f.1 (mem_Fset.mp f.2).1).ne_zero
  let pb := AdjoinRoot.powerBasis (K := L) hf0
  haveI : Finite (AdjoinRoot f.1) := Finite.of_equiv _ pb.basis.equivFun.toEquiv.symm
  haveI : Module.Finite (AdjoinRoot f.1) (Vf s b F f.1) :=
    Module.Finite.of_restrictScalars_finite L (AdjoinRoot f.1) (Vf s b F f.1)
  have hdim : pb.dim = f.1.natDegree := AdjoinRoot.powerBasis_dim hf0
  have hfin : Nat.card (Fin pb.dim) = pb.dim := by simp
  apply unitaryOrLinear_top Q (AdjoinRoot f.1) (Vf s b F f.1) f.1.natDegree
  rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, hfin, hdim, hQ, ← pow_mul]

theorem block_selfDual_unitaryOrLinear [Finite L] (H : PrimaryHyp τ s m F a b) (Q : ℕ)
    (hQ : Nat.card L = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q) (f : ↥(Fset s b F))
    (hself : piI H f = f) : Held.UnitaryOrLinearBlock Q ↥(Bl H f) := by
  rw [Bl_of_selfDual H hself]
  haveI : Fact (Irreducible f.1) := ⟨H.hirr f.1 (mem_Fset.mp f.2).1⟩
  have hsa : adjM τ (Pmat s b F f.1) = Pmat s b F f.1 := by
    rw [adjM_piI H f, hself]
  exact selfDual_unitaryOrLinear H (mem_Fset.mp f.2).1 (mem_Fset.mp f.2).2 hsa Q hQ hτQ

theorem block_unitaryOrLinear [Finite L] (H : PrimaryHyp τ s m F a b) (Q : ℕ)
    (hQ : Nat.card L = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q) (f : Activ H) :
    Held.UnitaryOrLinearBlock Q ↥(Bl H f.1) := by
  by_cases hself : piI H f.1 = f.1
  · exact block_selfDual_unitaryOrLinear H Q hQ hτQ f.1 hself
  · rw [Bl_of_isRep H (f.2.resolve_left hself)]
    exact block_top_unitaryOrLinear H Q hQ f.1

noncomputable def reindexBlocks (H : PrimaryHyp τ s m F a b) {r : ℕ} (e : Activ H ≃ Fin r) :
    ((f : Activ H) → ↥(Bl H f.1)) ≃* ((k : Fin r) → ↥(Bl H (e.symm k).1)) :=
  { toEquiv := Equiv.piCongrLeft' (fun f : Activ H => ↥(Bl H f.1)) e
    map_mul' := fun _ _ => rfl }

end Blocks

theorem centralizer_decomposition [Finite L] {Q : ℕ} {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x)
    (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2) (s : GL (Fin n) L)
    (hs : s ∈ Held.heldSU n L τ hτ) (hord : (orderOf s : L) ≠ 0) :
    ∃ (r : ℕ) (H : Fin r → Type) (_ : ∀ k, Group (H k)) (_ : ∀ k, Finite (H k)),
      (∀ k, Held.UnitaryOrLinearBlock Q (H k)) ∧
        Nonempty (↥(Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ Held.heldGU n L τ hτ) ≃*
          ∀ k, H k) := by
  have hm0 : 0 < orderOf s := orderOf_pos s
  have hsm : (s : Matrix (Fin n) (Fin n) L) ^ orderOf s = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hs' : adjM τ (s : Matrix (Fin n) (Fin n) L) * (s : Matrix (Fin n) (Fin n) L) = 1 :=
    Held.mem_heldGU.mp (Subgroup.mem_inf.mp hs).1
  set F : Finset L[X] := factorsOf (L := L) (orderOf s) with hF
  have hirr : ∀ f ∈ F, Irreducible f := fun f hf => factorsOf_irreducible hf
  have hmon : ∀ f ∈ F, Monic f := fun f hf => factorsOf_monic hf
  have hprod : ∏ f ∈ F, f = X ^ orderOf s - 1 := prod_factorsOf hord hm0
  have hcop : ∀ f ∈ F, ∃ u v : L[X], u * f + v * gcF F f = 1 :=
    fun f hf => isCoprime_gcF hirr hmon hf
  choose! a b hab using hcop
  let H : PrimaryHyp τ (s : Matrix (Fin n) (Fin n) L) (orderOf s) F a b :=
    ⟨hτ, hm0, hirr, hmon, hprod, hsm, hs', hab⟩
  haveI hK : ∀ f : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F),
      Fact (∀ x ∈ Vf (s : Matrix (Fin n) (Fin n) L) b F f.1,
        aeval (s : Matrix (Fin n) (Fin n) L) f.1 *ᵥ x = 0) :=
    fun f => ⟨fun x hx => aeval_factor_mulVec_eq_zero H (mem_Fset.mp f.2).1 hx⟩
  letI : Fintype (Activ H) := Fintype.ofFinite (Activ H)
  let e : Activ H ≃ Fin (Fintype.card (Activ H)) := Fintype.equivFin (Activ H)
  refine ⟨Fintype.card (Activ H), fun k => ↥(Bl H (e.symm k).1), fun k => inferInstance,
    fun k => finite_Bl H (e.symm k).1, fun k => block_unitaryOrLinear H Q hL hτQ (e.symm k),
    ⟨(centralizerEquivGlin hτ s).trans ((glinEquivBlocks H).trans (reindexBlocks H e))⟩⟩

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI Matrix

theorem unitaryCentralizerDecomposition_holds : UnitaryCentralizerDecomposition := by
  intro Q n L _ _ τ hτ s hL hτQ hs hord
  exact HeldUCD.centralizer_decomposition hτ hτQ hL s hs hord

end CFSG.LieType.SemisimpleCentralizers.Held

end
