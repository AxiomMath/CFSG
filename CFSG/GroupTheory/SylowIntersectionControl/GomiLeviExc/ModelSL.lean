module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Model
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift

public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Universal
  CFSG.LieType.Steinberg

theorem SLModel.isCharTwoSteinberg (k : Type) [Field k] [CharP k 2] (m : ℕ) :
    IsCharTwoSteinberg (SpecialLinear.rootDatum m k).roots (SL.x m k) := by
  classical
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (A := CartanMatrix.A m) (SpecialLinear.isFiniteType_A m)
    (Dv := ∅) rfl
  refine ⟨?_, ?_⟩
  · intro γ hγ c d
    exact (SL.isParametrization (m := m) (F := k) γ hγ).2.1 c d
  · intro α hα β hβ hαβ c d
    have hcomm := SL.commutatorFormula (m := m) (F := k) O α hα β hβ hαβ c d
    rw [hcomm]
    by_cases h : α + β ∈ (SpecialLinear.rootDatum m k).roots
    · rw [if_pos h]
      have hmem : (1, 1) ∈ expPairs (SL.Φ (m := m) (F := k)) α β := by
        refine ⟨one_pos, one_pos, ?_⟩
        erw [RootSystem.ofCartan_roots, one_smul, one_smul]
        exact h
      have hp1 : (1, 1) ∈ O.list α β := (O.mem_iff α hα β hβ hαβ (1, 1)).2 hmem
      have hall : ∀ p ∈ O.list α β, p = (1, 1) := by
        intro p hp
        exact ((SL.mem_expPairs_iff (F := k) hα hβ hαβ p).1 ((O.mem_iff α hα β hβ hαβ p).1 hp)).1
      have hlist : O.list α β = [(1, 1)] := by
        refine List.perm_singleton.1 ((List.perm_ext_iff_of_nodup (O.nodup α β)
          (List.nodup_singleton _)).2 ?_)
        intro p
        constructor
        · intro hp; simpa [List.mem_singleton] using hall p hp
        · intro hp; rw [List.mem_singleton] at hp; rw [hp]; exact hp1
      rw [hlist, List.map_singleton, List.prod_singleton]; simp only [pow_one]
      have hcast : ((SL.commC α β (1, 1) : ℤ) : k) = 1 := by
        unfold SL.commC
        split_ifs
        · simp
        · rw [Int.cast_neg, Int.cast_one]
          exact CharTwo.neg_eq 1
      erw [hcast, one_smul, one_smul, one_mul]
      rfl
    · rw [if_neg h]
      have hnil : O.list α β = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro p hp
        have hp' := (O.mem_iff α hα β hβ hαβ p).1 hp
        have hp_eq := ((SL.mem_expPairs_iff (F := k) hα hβ hαβ p).1 hp').1
        subst hp_eq
        have hp'' : α + β ∈ (SpecialLinear.rootDatum m k).roots := by
          have h1 : (1, 1).1 • α + (1, 1).2 • β ∈ (SpecialLinear.rootDatum m k).roots := hp'.2.2
          simpa only [Prod.fst, Prod.snd, one_smul] using h1
        exact h hp''
      rw [hnil, List.map_nil, List.prod_nil]

variable (k : Type) [Field k] [Finite k] [CharP k 2] {m : ℕ}

theorem isCharTwoModel_sl (hm : 2 ≤ m)
    (hC : IsChevTwo (SpecialLinearGroup (Fin (m + 1)) k ⧸
      center (SpecialLinearGroup (Fin (m + 1)) k))) :
    IsCharTwoModel (SpecialLinear.rootDatum m k) k (SL.x m k) where
  conclusionB :=
    conclusionB_of rfl (SpecialLinear.isCTGroupDatum m k) (SpecialLinear.steinbergExtras m k)
      SL.isParametrization
      (fun O => ⟨SL.commC (m := m), fun α _ β _ p _ => by
        simp only [Set.mem_insert_iff]
        exact Or.inl (SL.commC_natAbs (m := m) α β p), SL.commutatorFormula O⟩)
      (fun O C hOC => SL.chevalleyExtras hm O C hOC)
  divisible := rfl
  isSymm := CartanMatrix.A_isSymm m
  steinberg := SLModel.isCharTwoSteinberg k m
  isQuasisimple := CFSG.LieType.Universal.SpecialLinear.isQuasisimple m k hm
  odd_card_center := Nat.not_even_iff_odd.mp fun h =>
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.not_dvd_card_center_specialLinearGroup
      (p := 2) (even_iff_two_dvd.mp h)
  isChevTwo := hC

theorem hasCharTwoModel_A (hm : 2 ≤ m)
    (hC : IsChevTwo (SpecialLinearGroup (Fin (m + 1)) k ⧸
      center (SpecialLinearGroup (Fin (m + 1)) k))) :
    HasCharTwoModel k (CartanMatrix.A m) :=
  ⟨_, _, SpecialLinear.rootDatum m k, SL.x m k, Equiv.refl _, fun _ _ => rfl,
    isCharTwoModel_sl k hm hC⟩

end CFSG.GroupTheory.GomiLeviExc
