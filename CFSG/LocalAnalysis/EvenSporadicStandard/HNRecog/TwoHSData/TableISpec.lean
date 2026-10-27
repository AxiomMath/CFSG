
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClassesBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeGlue

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem elemW_append (w w' : List ℕ) : elemW (w ++ w') = elemW w * elemW w' := by
  simp only [elemW, TwoHS.wordVal, List.map_append, List.prod_append]

theorem pair4_size (t0 ta tb tab : Table) : (pair4 t0 ta tb tab).size = 4 := rfl
theorem pair4_get0 (t0 ta tb tab : Table) : (pair4 t0 ta tb tab)[0]! = t0 := rfl
theorem pair4_get1 (t0 ta tb tab : Table) : (pair4 t0 ta tb tab)[1]! = ta := rfl
theorem pair4_get2 (t0 ta tb tab : Table) : (pair4 t0 ta tb tab)[2]! = tb := rfl
theorem pair4_get3 (t0 ta tb tab : Table) : (pair4 t0 ta tb tab)[3]! = tab := rfl

theorem isEnumSet_pair {a b : Equiv.Perm (Fin 1408)} {ta tb tab : Table}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hta : Rep 1408 ta a) (htb : Rep 1408 tb b) (htab : Rep 1408 tab (a * b)) :
    IsEnumSet 1408 (pair4 (idT 1408) ta tb tab)
      (closure ({a, b} : Set (Equiv.Perm (Fin 1408))) : Set (Equiv.Perm (Fin 1408))) := by
  constructor
  · intro k hk
    rw [pair4_size] at hk
    interval_cases k
    · exact ⟨1, one_mem _, by rw [pair4_get0]; exact Rep.idT (by norm_num)⟩
    · exact ⟨a, subset_closure (by simp), by rw [pair4_get1]; exact hta⟩
    · exact ⟨b, subset_closure (by simp), by rw [pair4_get2]; exact htb⟩
    · exact ⟨a * b, mul_mem (subset_closure (by simp)) (subset_closure (by simp)),
        by rw [pair4_get3]; exact htab⟩
  · intro g hg
    rcases (TwoHSData.mem_closure_pair_iff ha hb hab).1 hg with h | h | h | h
    · exact ⟨0, by rw [pair4_size]; omega, by rw [pair4_get0, h]; exact Rep.idT (by norm_num)⟩
    · exact ⟨1, by rw [pair4_size]; omega, by rw [pair4_get1, h]; exact hta⟩
    · exact ⟨2, by rw [pair4_size]; omega, by rw [pair4_get2, h]; exact htb⟩
    · exact ⟨3, by rw [pair4_size]; omega, by rw [pair4_get3, h]; exact htab⟩

section Cert

theorem elemA_mul_self : elemA * elemA = 1 :=
  mul_self_eq_one_of_orderOf_eq_two twoHSBasic_spec.1

theorem elemA_comm {g : Equiv.Perm (Fin 1408)} (hg : g ∈ P1408) : elemA * g = g * elemA :=
  twoHSBasic_spec.2.2.2.2.1 g hg

theorem pair_le_centralizer {y : Equiv.Perm (Fin 1408)} (hy : y ∈ P1408) :
    closure ({elemA, y} : Set (Equiv.Perm (Fin 1408))) ≤
      P1408 ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 1408))) := by
  rw [closure_le]
  intro v hv
  rcases hv with rfl | hv
  · refine Subgroup.mem_inf.2 ⟨elemA_mem, mem_centralizer_iff.2 ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (elemA_comm hy).symm
  · rw [Set.mem_singleton_iff] at hv
    subst hv
    refine Subgroup.mem_inf.2 ⟨hy, mem_centralizer_iff.2 ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]

theorem pair_central {y x : Equiv.Perm (Fin 1408)}
    (hx : x ∈ P1408 ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 1408)))) :
    ∀ v ∈ closure ({elemA, y} : Set (Equiv.Perm (Fin 1408))), x * v = v * x := by
  have hxP : x ∈ P1408 := (Subgroup.mem_inf.1 hx).1
  have hxC : x ∈ centralizer ({y} : Set (Equiv.Perm (Fin 1408))) := (Subgroup.mem_inf.1 hx).2
  have hle : closure ({elemA, y} : Set (Equiv.Perm (Fin 1408))) ≤
      centralizer ({x} : Set (Equiv.Perm (Fin 1408))) := by
    rw [closure_le]
    intro v hv
    refine mem_centralizer_iff.2 ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    rcases hv with rfl | hv
    · exact (elemA_comm hxP).symm
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact (mem_centralizer_iff.1 hxC v rfl).symm
  intro v hv
  exact mem_centralizer_iff.1 (hle hv) x rfl

end Cert

theorem map_subtype_centralizer {M : Type*} [Group M] (P : Subgroup M) (t : ↥P) :
    (centralizer ({t} : Set ↥P)).map P.subtype =
      P ⊓ centralizer ({(t : M)} : Set M) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val hx
    simpa using this
  · rintro ⟨hgP, hg⟩
    exact ⟨⟨g, hgP⟩, Subtype.ext (by simpa using hg), rfl⟩

@[expose] noncomputable def centralizerSubtypeEquiv {M : Type*} [Group M] (P : Subgroup M)
    (t : ↥P) :
    ↥(centralizer ({t} : Set ↥P)) ≃* ↥(P ⊓ centralizer ({(t : M)} : Set M)) :=
  (centralizer ({t} : Set ↥P)).equivMapOfInjective P.subtype P.subtype_injective |>.trans
    (MulEquiv.subgroupCongr (map_subtype_centralizer P t))

end CFSG.EvenSporadicStandard.HNRecog
