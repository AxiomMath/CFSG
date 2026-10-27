module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.CoverIsoSU
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.SU3Closure
public import CFSG.LieType.SeitzGeneration.UnitaryHyperEx

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

open CFSG.LieType.SeitzGeneration CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

theorem coverThree_gen_toral_unitary
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (h9 : 9 ∣ q.card + 1)
    (e : K ⧸ Subgroup.center K ≃* Cat ⟨.twistedA 2 q, hv⟩)
    (hz : 3 ∣ Nat.card (Subgroup.center K))
    (P : Subgroup K) (hPc : IsMulCommutative P) (hP : Nat.card P = 3 ^ 3)
    (hPZ : Nat.card (P ⊓ Subgroup.center K : Subgroup K) = 3)
    (hP3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center K) :
    Subgroup.closure {k : K | ∃ x ∈ P, x ∉ Subgroup.center K ∧ k * x = x * k} = ⊤ := by
  classical
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ with hfdef
  have hf : 1 ≤ f := TauCeti.ValidLieTypeIndex.fieldExponent_pos _
  have hℓp : ℓ.Prime := by
    rw [hℓ]
    exact Fact.out
  have : Fact ℓ.Prime := ⟨hℓp⟩
  set F := GaloisField ℓ (2 * f)
  have hU : UnitaryFieldData ℓ f F :=
    CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f hf
  have := hU.finite
  have := hU.charP
  have hqc : ℓ ^ f = q.card := card_twistedA 2 q hv
  have h9' : 9 ∣ ℓ ^ f + 1 := by rw [hqc]; exact h9
  have h5 : 5 ≤ ℓ ^ f := by
    have := Nat.le_of_dvd (by positivity) h9'
    omega
  let eU := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv
  let ρ : K →* StatedProj (StatedSU (2 + 1) (ℓ ^ f) F) :=
    (eU.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ :=
    (eU.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center K := by
    ext x
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨ψ⟩ := exists_mulEquiv_su3_of_cover
    hGA hℓp h5 hU.card_eq_sq h9' ρ hρs hker hz
  have hq2 : ℓ ^ f ≠ 2 := by omega
  set P' : Subgroup (unitarySU ℓ f F 3) := P.map ψ.symm.toMonoidHom with hP'
  have hP'comm : IsMulCommutative P' := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change (a : unitarySU ℓ f F 3) * b = b * a
    rw [← hxa, ← hyb]
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hPc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hP'card : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective ψ.symm.injective, hP]
    norm_num
  have hP'Z : Nat.card (P' ⊓ Subgroup.center (unitarySU ℓ f F 3) :
      Subgroup (unitarySU ℓ f F 3)) = 3 := by
    rw [hP', map_inf_center, Subgroup.card_map_of_injective ψ.symm.injective]
    exact hPZ
  have hP'3 : ∀ x ∈ P', x ^ 3 ∈ Subgroup.center (unitarySU ℓ f F 3) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow]
    exact (mem_center_map_iff ψ.symm _).2 (hP3 x hx)
  have htop := su3_closure_centralizers hU hq2 h9' P' hP'comm hP'card hP'Z hP'3
  have hmap : P'.map ψ.toMonoidHom = P := by
    rw [hP', Subgroup.map_map]
    ext x
    simp
  have h1 := closure_centralizers_map ψ P'
  rw [hmap, htop, Subgroup.map_top_of_surjective _ ψ.surjective] at h1
  exact h1

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
