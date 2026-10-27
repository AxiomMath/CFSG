module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import Mathlib

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.AbelianFixedPointFreeLift

open CFSG

theorem exists_invariant_fpf_noncyclic_map_quotient_of_abelian
    {P : Type*} [Group P] [Finite P] {q r : ℕ} [Fact q.Prime]
    (hPcomm : IsMulCommutative P) (hP : IsPGroup q P)
    (K : Subgroup P) (θ : MulAut P) (hr : orderOf θ = r) (hrp : r.Prime)
    (hqr : q ≠ r) (hfix_le : ∀ x : P, θ x = x → x ∈ K)
    (hquot : ¬ IsCyclic (P ⧸ K)) :
    ∃ B : Subgroup P, B.map θ.toMonoidHom = B ∧ IsPGroup q B ∧ ¬ IsCyclic B ∧
      B.map (QuotientGroup.mk' K) = ⊤ ∧
      ∃ κ : B →* B, (∀ b : B, κ b = b → b = 1) ∧
        ∀ b : B, θ (b : P) = (κ b : P) := by
  classical
  let : CommGroup P := IsMulCommutative.instCommGroup
  let A := Subgroup.zpowers θ
  let φ : A →* MulAut P := A.subtype
  have hsolv : Group.IsSolvable P := Group.isSolvable_of_comm fun a b => mul_comm a b
  have hcoprime : Nat.Coprime (Nat.card A) (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [show Nat.card A = r by simp [A, Nat.card_zpowers, hr], hn]
    exact Nat.Coprime.pow_right n
      ((Nat.coprime_primes hrp (Fact.out : q.Prime)).2 (Ne.symm hqr))
  have hC_le_K : fixedPointSubgroup A P ≤ K := by
    intro x hx
    exact hfix_le x (hx ⟨θ, Subgroup.mem_zpowers θ⟩)
  have hcompl0 : IsCompl (fixedPointSubgroup A P) (CFSG.commutatorAction (A := A) (G := P)) :=
    CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := P) (A := A) hsolv hcoprime hPcomm
  let B : Subgroup P := CFSG.commutatorAction (A := A) (G := P)
  have hBinv : IsInvariant A P B := CFSG.commutatorAction_isInvariant
  have hBmap : B.map θ.toMonoidHom = B := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h := (hBinv.invariant (A := A) (G := P) (H := B)
        (⟨θ, Subgroup.mem_zpowers θ⟩ : A) y).1 hy
      change (θ : MulAut P) y ∈ B at h
      exact h
    · intro x hx
      refine ⟨θ⁻¹ x, ?_, by simp⟩
      have h := (hBinv.invariant (A := A) (G := P) (H := B)
        (⟨θ⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers θ)⟩ : A) x).1 hx
      change ((θ⁻¹ : MulAut P) x) ∈ B at h
      exact h
  have hBq : IsPGroup q B := hP.of_injective B.subtype B.subtype_injective
  have hBmapQuot : B.map (QuotientGroup.mk' K) = ⊤ := by
    refine le_antisymm le_top ?_
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    have hx : x ∈ fixedPointSubgroup A P ⊔ B := by
      rw [hcompl0.sup_eq_top]
      exact Subgroup.mem_top x
    obtain ⟨c, hc, b, hb, rfl⟩ := Subgroup.mem_sup.1 hx
    refine ⟨b, hb, ?_⟩
    have hcK : c ∈ K := hC_le_K hc
    have hc1 : QuotientGroup.mk' K c = 1 := (QuotientGroup.eq_one_iff c).2 hcK
    rw [map_mul, hc1, one_mul]
  have hBnoncyc : ¬ IsCyclic B := by
    intro hBcyc
    let f : B →* P ⧸ K := (QuotientGroup.mk' K).comp B.subtype
    have hf : Function.Surjective f := by
      intro y
      have hy : y ∈ B.map (QuotientGroup.mk' K) := by
        rw [hBmapQuot]
        exact Subgroup.mem_top y
      obtain ⟨b, hb, hby⟩ := hy
      exact ⟨⟨b, hb⟩, hby⟩
    exact hquot (isCyclic_of_surjective f hf)
  let κ : B →* B :=
    { toFun := fun b => ⟨θ (b : P), by
        have h : θ (b : P) ∈ B.map θ.toMonoidHom := ⟨b, b.2, rfl⟩
        rwa [hBmap] at h⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hrel : ∀ b : B, θ (b : P) = (κ b : P) := fun b => rfl
  have hκfpf : ∀ b : B, κ b = b → b = 1 := by
    intro b hb
    have hθb : θ (b : P) = (b : P) := by
      rw [hrel b]
      exact congrArg Subtype.val hb
    have hbC : (b : P) ∈ fixedPointSubgroup A P := by
      have hle : A ≤ fixingSubgroup (MulAut P) ({(b : P)} : Set P) := by
        rw [Subgroup.zpowers_le]
        exact (mem_fixingSubgroup_iff (MulAut P)).2 (fun x hx => by
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact hθb)
      intro a
      exact (mem_fixingSubgroup_iff (MulAut P)).1 (hle a.2) (b : P) (Set.mem_singleton _)
    exact Subtype.ext (Subgroup.disjoint_def.mp hcompl0.disjoint hbC b.2)
  exact ⟨B, hBmap, hBq, hBnoncyc, hBmapQuot, κ, hκfpf, hrel⟩

end CFSG.GroupTheory.CoprimeActionSupport.AbelianFixedPointFreeLift
