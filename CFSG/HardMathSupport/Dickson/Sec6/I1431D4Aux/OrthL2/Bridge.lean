module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Levi
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Steinberg.Minuscule
  CFSG.TauCetiBridge.Minuscule CFSG.LieType.Universal.Spin CFSG.TauCetiBridge.Twisted

variable (K : Type) [Field K]

@[expose] def node0 : Fin Tag.D4.rank := ⟨0, by decide⟩

theorem root_zero : Tag.D4.rootCertificate.root 0 = Pi.single node0 1 := by
  decide +kernel

theorem root_four : Tag.D4.rootCertificate.root 4 = -Pi.single node0 1 := by
  decide +kernel

section Theta


theorem theta_x (c : K) :
    theta K ⟨eichler (quadPlus 4 K) (Pi.single (Sum.inl 0) 1) (c • Pi.single (Sum.inr 1) 1),
      eichler_mem_elementaryGroup _ _ _⟩ = adjX Tag.D4 K node0 (-c) := by
  have h := blockRep_xm (F := K) 0 (-c)
  have hU : rU 0 = Sum.inl 0 := rfl
  have hW : rW 0 = Sum.inr 1 := rfl
  have hS : rS 0 = -1 := rfl
  rw [hU, hW, hS] at h
  have hroot : Tag.D4.rootCertificate.root ((0 : Fin 24) : ℕ) = Pi.single node0 1 := root_zero
  rw [hroot] at h
  have h1 : (((-1 : ℤ) : K) * -c) = c := by simp
  rw [h1] at h
  have hE : (⟨eichler (quadPlus 4 K) (Pi.single (Sum.inl 0) 1) (c • Pi.single (Sum.inr 1) 1),
      eichler_mem_elementaryGroup _ _ _⟩ : elementaryGroup (quadPlus 4 K)) =
      blockRepE K (d4tData_valid.xm K (Pi.single node0 1) (-c)) :=
    Subtype.ext (by rw [coe_blockRepE]; exact h.symm)
  rw [hE, theta_blockRepE]
  exact Subtype.ext (adMin_xm_single (hV := d4tData_valid) (hpd := posDef_cartan_D4)
    (hS := d4tSigns_check) (K := K) node0 (-c))

theorem theta_y (c : K) :
    theta K ⟨eichler (quadPlus 4 K) (Pi.single (Sum.inl 1) 1) (c • Pi.single (Sum.inr 0) 1),
      eichler_mem_elementaryGroup _ _ _⟩ = adjY Tag.D4 K node0 (-c) := by
  have h := blockRep_xm (F := K) 4 (-c)
  have hU : rU 4 = Sum.inl 1 := rfl
  have hW : rW 4 = Sum.inr 0 := rfl
  have hS : rS 4 = -1 := rfl
  rw [hU, hW, hS] at h
  have hroot : Tag.D4.rootCertificate.root ((4 : Fin 24) : ℕ) = -Pi.single node0 1 := root_four
  rw [hroot] at h
  have h1 : (((-1 : ℤ) : K) * -c) = c := by simp
  rw [h1] at h
  have hE : (⟨eichler (quadPlus 4 K) (Pi.single (Sum.inl 1) 1) (c • Pi.single (Sum.inr 0) 1),
      eichler_mem_elementaryGroup _ _ _⟩ : elementaryGroup (quadPlus 4 K)) =
      blockRepE K (d4tData_valid.xm K (-Pi.single node0 1) (-c)) :=
    Subtype.ext (by rw [coe_blockRepE]; exact h.symm)
  rw [hE, theta_blockRepE]
  exact Subtype.ext (adMin_xm_neg_single (hV := d4tData_valid) (hpd := posDef_cartan_D4)
    (hS := d4tSigns_check) (K := K) node0 (-c))

@[expose] def leviE {K : Type} [Field K] (Q : QuadraticForm K (Coord → K)) (a b a' b' : Coord → K) :
    Subgroup (elementaryGroup Q) :=
  Subgroup.closure
    ((Set.range fun c : K => (⟨eichler Q a (c • b'), eichler_mem_elementaryGroup Q _ _⟩ :
        elementaryGroup Q)) ∪
      Set.range fun c : K => (⟨eichler Q b (c • a'), eichler_mem_elementaryGroup Q _ _⟩ :
        elementaryGroup Q))

theorem leviE_map_subtype {K : Type} [Field K] (Q : QuadraticForm K (Coord → K)) (a b a' b' : Coord → K) :
    (leviE Q a b a' b').map (elementaryGroup Q).subtype = leviV Q a b a' b' := by
  rw [leviE, leviV, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_union, Set.mem_range, Set.mem_setOf_eq,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, Or.inl ⟨c, rfl⟩, rfl⟩
    · exact ⟨_, Or.inr ⟨c, rfl⟩, rfl⟩

theorem theta_leviE_node0 :
    (leviE (quadPlus 4 K) (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inl 1) 1)
      (Pi.single (Sum.inr 0) 1) (Pi.single (Sum.inr 1) 1)).map (theta K) =
      simplePosSubgroup Tag.D4 K node0 ⊔ simpleNegSubgroup Tag.D4 K node0 := by
  rw [leviE, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
    · exact Subgroup.mem_sup_left ⟨-c, by rw [theta_x]; rfl⟩
    · exact Subgroup.mem_sup_right ⟨-c, by rw [theta_y]; rfl⟩
  · refine sup_le ?_ ?_
    · rintro g ⟨c, hc⟩
      refine Subgroup.subset_closure ⟨_, Or.inl ⟨-c, rfl⟩, ?_⟩
      rw [theta_x, neg_neg]
      exact Subtype.ext hc.symm
    · rintro g ⟨c, hc⟩
      refine Subgroup.subset_closure ⟨_, Or.inr ⟨-c, rfl⟩, ?_⟩
      rw [theta_y, neg_neg]
      exact Subtype.ext hc.symm

end Theta

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
