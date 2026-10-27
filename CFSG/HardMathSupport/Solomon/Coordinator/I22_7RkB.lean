module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7RkA
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Subgroup
open scoped commutatorElement

theorem i227rk_centralizes_of_rank_le_two {K : Type*} [Group K] [Finite K]
    (hK : commutator K = ⊤) (V : Subgroup K) [V.Normal] (hV : IsPGroup 3 V)
    (hr : ∀ E : Subgroup K, E ≤ V → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9) :
    ∀ k : K, ∀ v ∈ V, k * v = v * k := by
  by_cases hVb : V = ⊥
  · intro k v hv
    rw [hVb, Subgroup.mem_bot] at hv
    subst hv
    simp
  have hnt : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVb
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := 3) (by norm_num) hV
  have := hDchar
  let φ : K →* MulAut V := MulAut.conjNormal
  let ρ : K →* MulAut D :=
    (CFSG.FiveTransitive.CharacteristicAutomorphism.restrict D).comp φ
  have hsolv : Group.IsSolvable (MulAut D) := by
    refine i227rk_mulAut_solvable (G := D) ?_ ?_ ?_
    · intro x
      exact Subtype.ext (by simpa using hDexp x x.2)
    · intro x y
      rw [Subgroup.mem_center_iff]
      intro g
      have hmem := hDcomm (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top y.1))
      have hg := (Subgroup.mem_centralizer_iff.mp hmem.2) g.1 g.2
      apply Subtype.ext
      simpa [commutatorElement_def] using hg
    · intro B hB
      let f : D →* K := V.subtype.comp D.subtype
      have hf : Function.Injective f := V.subtype_injective.comp D.subtype_injective
      have hE : CFSG.Open.IsElemAbelian 3 (B.map f) := by
        refine ⟨?_, ?_⟩
        · refine IsMulCommutative.of_comm ?_
          rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
          apply Subtype.ext
          have : (⟨a, ha⟩ : B) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
            hB.is_comm.comm _ _
          have h2 := congrArg (fun z : B => f z.1) this
          simpa using h2
        · rintro _ ⟨a, ha, rfl⟩
          rw [← map_pow]
          have : a ^ 3 = 1 := Subtype.ext (by simpa using hDexp a a.2)
          rw [this, map_one]
      have hle : B.map f ≤ V := by
        rintro _ ⟨a, ha, rfl⟩
        exact (a : V).2
      have := hr _ hle hE
      rwa [← Nat.card_congr (Subgroup.equivMapOfInjective B f hf).toEquiv] at this
  have hρ : ∀ k : K, ρ k = 1 := i227rk_hom_eq_one_of_solvable hK ρ
  have hfix : ∀ k : K, φ k ∈ fixingSubgroup (MulAut V) (D : Set V) := by
    intro k
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have := congrArg (fun a : MulAut D => ((a ⟨y, hy⟩ : D) : V)) (hρ k)
    simpa [ρ] using this
  let ψ : K →* fixingSubgroup (MulAut V) (D : Set V) := φ.codRestrict _ hfix
  have : Finite (fixingSubgroup (MulAut V) (D : Set V)) := inferInstance
  have hnil : Group.IsNilpotent (fixingSubgroup (MulAut V) (D : Set V)) := hDfix.isNilpotent
  have hψ : ∀ k : K, ψ k = 1 := i227rk_hom_eq_one_of_solvable hK ψ
  intro k v hv
  have h1 : φ k = 1 := congrArg Subtype.val (hψ k)
  have h2 := congrArg (fun a : MulAut V => ((a ⟨v, hv⟩ : V) : K)) h1
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc k * v = k * v * k⁻¹ * k := by group
    _ = v * k := by rw [h2]

end CFSG.HardMathSupport.Solomon.Coordinator
