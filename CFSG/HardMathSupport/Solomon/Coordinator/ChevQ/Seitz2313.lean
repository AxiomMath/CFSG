module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GH74.GLS.Basic
public import CFSG.LieType.Seitz.Defs
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LieType.Seitz

namespace Seitz2313Aux

variable {S : Type*} [Group S]

def actOn (E : Subgroup (MulAut S)) (Q : Subgroup S) (hinv : ∀ φ ∈ E, ∀ u ∈ Q, φ u ∈ Q) :
    E →* MulAut Q where
  toFun φ :=
    { toFun := fun u => ⟨(φ : MulAut S) u, hinv φ φ.2 u u.2⟩
      invFun := fun u => ⟨(φ : MulAut S)⁻¹ u, by
        have := hinv (φ : MulAut S)⁻¹ (E.inv_mem φ.2) u u.2
        simpa using this⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  map_one' := MulEquiv.ext fun u => Subtype.ext rfl
  map_mul' := fun a b => MulEquiv.ext fun u => Subtype.ext rfl

theorem hyperplane_generation_of_invariant [Finite S] {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E) (hE0 : E ≠ ⊥)
    {Q : Subgroup S} (hQ : IsPGroup r ↥Q) (hinv : ∀ φ ∈ E, ∀ u ∈ Q, φ u ∈ Q) :
    Q ≤ ⨆ (F : Subgroup (MulAut S)) (_ : F ≤ E ∧ F.relIndex E = p),
      CFSG.GH74.GLS.oPrimeResidualOf r (fixedPoints F) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Finite E := inferInstance
  haveI : IsElementaryAbelian p E := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
  haveI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hE0
  letI : MulDistribMulAction E Q := MulDistribMulAction.compHom Q (actOn E Q hinv)
  have hnd : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
    rw [hk]
    intro h
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h))
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := E) (H := Q) hnd
  intro u hu
  have hu' : (⟨u, hu⟩ : Q) ∈ ⨆ (B : Subgroup E) (_ : B.index = p), CFSG.fixedPointSubgroup B Q := by
    rw [hgen]; exact Subgroup.mem_top _
  have hle : (⨆ (B : Subgroup E) (_ : B.index = p), CFSG.fixedPointSubgroup B Q) ≤
      (⨆ (F : Subgroup (MulAut S)) (_ : F ≤ E ∧ F.relIndex E = p),
        CFSG.GH74.GLS.oPrimeResidualOf r (fixedPoints F)).comap Q.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    set F : Subgroup (MulAut S) := B.map E.subtype with hF
    have hFE : F ≤ E := Subgroup.map_subtype_le B
    have hrel : F.relIndex E = p := by
      have h3 : (⊤ : Subgroup ↥E).map E.subtype = E := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      calc F.relIndex E = F.relIndex ((⊤ : Subgroup ↥E).map E.subtype) := by rw [h3]
        _ = B.relIndex ⊤ := Subgroup.relIndex_map_map_of_injective _ _ E.subtype_injective
        _ = p := by rw [Subgroup.relIndex_top_right]; exact hB
    have hxfix : ((x : Q) : S) ∈ fixedPoints F := by
      rintro _ ⟨b, hb, rfl⟩
      have := ((FixedPoints.mem_subgroup _ _ _).1 hx) ⟨b, hb⟩
      exact congrArg Subtype.val this
    refine Subgroup.mem_iSup_of_mem F (Subgroup.mem_iSup_of_mem ⟨hFE, hrel⟩ ?_)
    have hord : ∃ k : ℕ, ((x : Q) : S) ^ (r ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hQ x
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    refine ⟨⟨(x : S), hxfix⟩, Subgroup.subset_closure ?_, rfl⟩
    obtain ⟨k, hk⟩ := hord
    exact ⟨k, Subtype.ext hk⟩
  exact hle hu'

end Seitz2313Aux

