module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.RankThree.GroupTheory.PerfectSubnormalModNormal

public section

namespace CFSG.CGT.Foote82

@[expose] def layerClosure {Y : Type*} [Group Y] (A : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {x | ∃ b ∈ CFSG.pLayer Y 2, ∃ a ∈ A, x = b * a * b⁻¹}

section ConjClosure

variable {G : Type*} [Group G]

private lemma le_closure_conj (M A : Subgroup G) :
    A ≤ Subgroup.closure {x | ∃ b ∈ M, ∃ a ∈ A, x = b * a * b⁻¹} := fun a ha =>
  Subgroup.subset_closure ⟨1, one_mem _, a, ha, by simp⟩

private lemma closure_conj_le {M A K : Subgroup G} (hM : M ≤ K) (hA : A ≤ K) :
    Subgroup.closure {x | ∃ b ∈ M, ∃ a ∈ A, x = b * a * b⁻¹} ≤ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨b, hb, a, ha, rfl⟩
  exact mul_mem (mul_mem (hM hb) (hA ha)) (inv_mem (hM hb))

private lemma le_normalizer_closure_conj (M A : Subgroup G) :
    M ≤ Subgroup.normalizer
      (Subgroup.closure {x | ∃ b ∈ M, ∃ a ∈ A, x = b * a * b⁻¹} : Set G) := by
  refine Subgroup.le_normalizer_closure_iff.2 ?_
  rintro c hc _ ⟨b, hb, a, ha, rfl⟩
  exact Subgroup.subset_closure ⟨c * b, mul_mem hc hb, a, ha, by group⟩

end ConjClosure

variable {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}

theorem le_layerClosure : A ≤ layerClosure A :=
  le_closure_conj _ A

theorem layerClosure_le (hA : A ≤ CFSG.pLayer Y 2) : layerClosure A ≤ CFSG.pLayer Y 2 :=
  closure_conj_le le_rfl hA

theorem pLayer_le_normalizer_layerClosure :
    CFSG.pLayer Y 2 ≤ Subgroup.normalizer (layerClosure A : Set Y) :=
  le_normalizer_closure_conj _ A

theorem isSubnormal_layerClosure (hA : A ≤ CFSG.pLayer Y 2) : (layerClosure A).IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic (G := Y) (p := 2)
  exact Subgroup.IsSubnormal.step _ _ (layerClosure_le hA)
    (inferInstance : (CFSG.pLayer Y 2).Normal).isSubnormal
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (layerClosure_le hA)).2
      pLayer_le_normalizer_layerClosure)

private lemma map_pLayer_le_normalizer_map {S : Subgroup Y} (hS : S.IsSubnormal) :
    (CFSG.pLayer Y 2).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 Y)) ≤ Subgroup.normalizer
      (S.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 Y)) : Set (Y ⧸ CFSG.pPrimeCore 2 Y)) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  rw [hLK]
  rcases CFSG.LocalCores.component_subnormal_subgroup hK
      (hS.map (QuotientGroup.mk'_surjective _)) with h | h
  · exact h.trans Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h).trans
      (Subgroup.centralizer_le_normalizer _)

theorem closure_conj_layerClosure (hA : A ≤ CFSG.pLayer Y 2) (hperf : ⁅A, A⁆ = A) :
    Subgroup.closure {x | ∃ b ∈ layerClosure A, ∃ a ∈ A, x = b * a * b⁻¹} = layerClosure A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := layerClosure A
  set W := Subgroup.closure {x | ∃ b ∈ X, ∃ a ∈ A, x = b * a * b⁻¹}
  have hWX : W ≤ X := closure_conj_le le_rfl le_layerClosure
  have hXn : X ≤ Subgroup.normalizer (W : Set Y) := le_normalizer_closure_conj X A
  have hWsub : W.IsSubnormal :=
    Subgroup.IsSubnormal.step W X hWX (isSubnormal_layerClosure hA)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hWX).2 hXn)
  have hXπ : X.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 Y)) ≤
      W.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 Y)) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1
      (map_pLayer_le_normalizer_map hWsub (Subgroup.mem_map_of_mem _ hb)) _).1
      (Subgroup.mem_map_of_mem _ (le_closure_conj X A ha))
  have hXperf : ⁅X, X⁆ = X := by
    refine le_antisymm (Subgroup.commutator_le_self _) ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨b, hb, a, ha, rfl⟩
    set P := A.map (MulAut.conj b).toMonoidHom with hP
    have hPX : P ≤ X := by
      rintro _ ⟨a', ha', rfl⟩
      exact Subgroup.subset_closure ⟨b, hb, a', ha', rfl⟩
    have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hperf]
    exact Subgroup.commutator_mono hPX hPX (hPperf.ge ⟨a, ha, rfl⟩)
  have hsolO : Group.IsSolvable (CFSG.pPrimeCore 2 Y) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
  have hsol : Group.IsSolvable (X ⊓ CFSG.pPrimeCore 2 Y : Subgroup Y) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_right : X ⊓ CFSG.pPrimeCore 2 Y ≤ CFSG.pPrimeCore 2 Y))
      (Subgroup.inclusion_injective _)
  have hdecomp : ∀ s ∈ X, ∃ m ∈ W, ∃ r ∈ X ⊓ CFSG.pPrimeCore 2 Y, m * r = s := by
    intro s hs
    obtain ⟨w, hw, hws⟩ := Subgroup.mem_map.1 (hXπ (Subgroup.mem_map_of_mem _ hs))
    have hr : w⁻¹ * s ∈ CFSG.pPrimeCore 2 Y := by
      refine (QuotientGroup.ker_mk' (CFSG.pPrimeCore 2 Y)).le (MonoidHom.mem_ker.2 ?_)
      rw [map_mul, map_inv, hws, inv_mul_cancel]
    exact ⟨w, hw, w⁻¹ * s, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hWX hw)) hs, hr⟩, by simp⟩
  exact le_antisymm hWX (CFSG.RankThree.GroupTheory.le_of_perfect_of_eq_mul_solvable
    (Subgroup.isPerfect_iff.2 hXperf) hWX hXn hsol hdecomp)

end CFSG.CGT.Foote82
