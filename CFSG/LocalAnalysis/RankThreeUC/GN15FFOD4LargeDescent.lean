module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4TensorModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Spin CFSG.QuasithinUnique.Setup
open scoped Matrix


private lemma frobEquiv_symm_frobHom {K k : Type} [Field K] [Field k] [Algebra K k]
    [Finite k] [CharP k 2] (b : ℕ) (c : K) :
    (iterateFrobeniusEquiv k 2 b).symm (frobHom (K := K) k b c) = algebraMap K k c := by
  change (iterateFrobeniusEquiv k 2 b).symm
    (iterateFrobenius k 2 b (algebraMap K k c)) = algebraMap K k c
  rw [← iterateFrobeniusEquiv_apply]
  exact (iterateFrobeniusEquiv k 2 b).symm_apply_apply (algebraMap K k c)

private lemma frobEquiv_symm_mulVec {K k ι : Type} [Field K] [Field k] [Algebra K k]
    [Finite k] [CharP k 2] [Fintype ι] [DecidableEq ι] (b : ℕ)
    (M : Matrix ι ι K) (v : ι → k) :
    (fun a => (iterateFrobeniusEquiv k 2 b).symm
      ((((frobHom (K := K) k b).mapMatrix M) *ᵥ v) a)) =
    M.map (algebraMap K k) *ᵥ (fun a => (iterateFrobeniusEquiv k 2 b).symm (v a)) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.mapMatrix_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul]
  congr 1
  exact frobEquiv_symm_frobHom (K := K) b (M a j)


theorem exists_natural_of_frobNat {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {L : Subgroup (MulAut V)} (θ : L ≃* orthElementaryGroup (quadPlus 4 K))
    (hirr : X1.IsIrrOn L) {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    (ρ : Representation k (adjointGroup .D4 K) (Fin m → k))
    (ν : Additive V →+ (Fin m → k)) (hν : Function.Injective ν)
    (hνeq : ∀ (g : adjointGroup .D4 K) (v : V),
      ν (Additive.ofMul (((θ.symm (eta K g) : L) : MulAut V) v)) = ρ g (ν (Additive.ofMul v)))
    (b : ℕ) (σ : adjointGroup .D4 K ≃* adjointGroup .D4 K)
    (β : (Fin m → k) ≃ₗ[k] (Fin 4 ⊕ Fin 4 → k))
    (hβ : ∀ (g : adjointGroup .D4 K) (w : Fin m → k),
      β (ρ g w) = frobNatRep (K := K) k b (σ g) (β w))
    (hcard : Nat.card K ^ 8 ≤ Nat.card V) :
    ∃ (ψ : L ≃* orthElementaryGroup (quadPlus 4 K)) (φ : Additive V ≃+ (Fin 4 ⊕ Fin 4 → K)),
      ∀ (l : L) (v : V), φ (Additive.ofMul ((l : MulAut V) v)) =
        (ψ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (Additive.ofMul v)) := by
  classical
  have _hV := hV
  let F : k ≃+* k := iterateFrobeniusEquiv k 2 b
  let u : Additive V →+ (Fin 4 ⊕ Fin 4 → k) :=
    { toFun := fun x a => F.symm (β (ν x) a)
      map_zero' := by
        funext a
        simp
      map_add' := by
        intro x y
        funext a
        simp [map_add] }
  have hu_apply : ∀ (x : Additive V) (a : Fin 4 ⊕ Fin 4), u x a = F.symm (β (ν x) a) :=
    fun _ _ => rfl
  have hu_eq : ∀ (g : adjointGroup .D4 K) (v : V),
      u (Additive.ofMul (((θ.symm (eta K g) : L) : MulAut V) v)) =
        (natMat K (σ g)).map (algebraMap K k) *ᵥ u (Additive.ofMul v) := by
    intro g v
    funext a
    rw [hu_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    simp only [hu_apply]
    rw [hνeq g v, hβ g (ν (Additive.ofMul v))]
    change F.symm
      ((((frobHom (K := K) k b).mapMatrix (natMat K (σ g))) *ᵥ
        β (ν (Additive.ofMul v))) a) =
      ∑ j, algebraMap K k (natMat K (σ g) a j) * F.symm (β (ν (Additive.ofMul v)) j)
    exact congrFun (frobEquiv_symm_mulVec (K := K) (k := k) b (natMat K (σ g))
      (β (ν (Additive.ofMul v)))) a
  obtain ⟨v₀, hv₀⟩ := @exists_ne V hirr.1 (1 : V)
  have hνv : ν (Additive.ofMul v₀) ≠ 0 := by
    intro h
    apply hv₀
    have h' : Additive.ofMul v₀ = 0 := hν (by simpa using h)
    simpa using congrArg Additive.toMul h'
  have hβv : β (ν (Additive.ofMul v₀)) ≠ 0 := by
    intro h
    apply hνv
    exact β.injective (by simpa using h)
  obtain ⟨a₀, ha₀⟩ : ∃ a : Fin 4 ⊕ Fin 4, β (ν (Additive.ofMul v₀)) a ≠ 0 := by
    by_contra h
    push Not at h
    exact hβv (funext h)
  have hu₀ : F.symm (β (ν (Additive.ofMul v₀)) a₀) ≠ 0 := by
    intro h
    apply ha₀
    have h' := congrArg F h
    simpa [F] using h'
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one K
    (x := F.symm (β (ν (Additive.ofMul v₀)) a₀)) hu₀
  let f : Additive V →+ (Fin 4 ⊕ Fin 4 → K) :=
    { toFun := fun x a => ell (u x a)
      map_zero' := by
        funext a
        simp
      map_add' := by
        intro x y
        funext a
        simp [map_add] }
  have hf_apply : ∀ (x : Additive V) (a : Fin 4 ⊕ Fin 4), f x a = ell (u x a) := fun _ _ => rfl
  have hf_eq : ∀ (g : adjointGroup .D4 K) (v : V),
      f (Additive.ofMul (((θ.symm (eta K g) : L) : MulAut V) v)) =
        (natMat K (σ g)) *ᵥ f (Additive.ofMul v) := by
    intro g v
    funext a
    rw [hf_apply]
    simp only [Matrix.mulVec, dotProduct]
    simp only [hf_apply]
    rw [hu_eq g v]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hf_eta : ∀ (g : adjointGroup .D4 K) (v : V),
      f (Additive.ofMul (((θ.symm (eta K g) : L) : MulAut V) v)) =
        ((eta K (σ g) : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (f (Additive.ofMul v)) := by
    intro g v
    rw [hf_eq g v]
    exact LinearMap.toMatrix'_mulVec _ _
  have hfne : f (Additive.ofMul v₀) ≠ 0 := by
    intro h
    have h1 : f (Additive.ofMul v₀) a₀ = 0 := by rw [h]; rfl
    rw [hf_apply] at h1
    rw [hu_apply, hell] at h1
    exact one_ne_zero h1
  let Ksub : Subgroup V := AddSubgroup.toSubgroup' f.ker
  have hKinv : ∀ g ∈ L, ∀ w ∈ Ksub, g w ∈ Ksub := by
    intro l hl w hw
    rw [AddSubgroup.mem_toSubgroup'] at hw ⊢
    rw [AddMonoidHom.mem_ker] at hw ⊢
    let g : adjointGroup .D4 K := (eta K).symm (θ ⟨l, hl⟩)
    have hlg : (θ.symm (eta K g) : L) = ⟨l, hl⟩ := by
      simp [g]
    have h1 : f (Additive.ofMul (((θ.symm (eta K g) : L) : MulAut V) w)) = 0 := by
      rw [hf_eq g w, hw]
      simp
    simpa [hlg] using h1
  have hinj : Function.Injective f := by
    rcases hirr.2 Ksub hKinv with hbot | htop
    · rw [← AddSubgroup.toSubgroup'.map_bot] at hbot
      have hker : f.ker = ⊥ := AddSubgroup.toSubgroup'.injective hbot
      exact (AddMonoidHom.ker_eq_bot_iff f).1 hker
    · exfalso
      have hmemKer : Additive.ofMul v₀ ∈ f.ker := by
        have hKtop : v₀ ∈ Ksub := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (AddSubgroup.mem_toSubgroup' f.ker v₀).mp hKtop
      exact hfne (AddMonoidHom.mem_ker.mp hmemKer)
  have hcardAdd : Nat.card (Additive V) = Nat.card V :=
    Nat.card_congr Additive.toMul
  have hcardTarget : Nat.card (Fin 4 ⊕ Fin 4 → K) = Nat.card K ^ 8 := by
    rw [Nat.card_pi]
    simp [Fintype.card_sum]
  have hbij : Function.Bijective f :=
    Function.Injective.bijective_of_nat_card_le hinj (by
      rw [hcardTarget, hcardAdd]
      exact hcard)
  let ψ : L ≃* orthElementaryGroup (quadPlus 4 K) :=
    θ.trans ((eta K).symm.trans (σ.trans (eta K)))
  refine ⟨ψ, AddEquiv.ofBijective f hbij, ?_⟩
  intro l v
  change f (Additive.ofMul ((l : MulAut V) v)) =
    (ψ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (f (Additive.ofMul v))
  let g : adjointGroup .D4 K := (eta K).symm (θ l)
  have hψ : ψ l = eta K (σ g) := by
    simp [ψ, g, MulEquiv.trans_apply]
  have hlg : (θ.symm (eta K g) : L) = l := by simp [g]
  rw [hψ, ← hlg]
  exact hf_eta g v


end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
