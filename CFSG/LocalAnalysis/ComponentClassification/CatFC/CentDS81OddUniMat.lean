module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddUni
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddFam
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem solvableOrComponent_gramSU {n p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (A : gramSU h (idGram K n))
    (hA2 : A * A ∈ normOneScalars h (gramSU h (idGram K n)) n)
    (hAne : A ∉ normOneScalars h (gramSU h (idGram K n)) n) :
    SolvableOrComponent (gramSU h (idGram K n)) A := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  obtain ⟨c, hcN, -, hc⟩ := hA2
  have hAA : (A : GL (Fin n) K) * A = GeneralLinearGroup.scalar (Fin n) c := by
    rw [← Subgroup.coe_mul]
    exact hc
  set B := idForm h n with hBdef
  let T : sesqUnitaryGroup B :=
    ⟨Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K),
      (toLin_mem_sesqUnitaryGroup_iff _).mpr ((mem_gramSU_iff_unitary h).mp A.2).1⟩
  have hTcoe : ((T : LinearMap.GeneralLinearGroup K (Fin n → K))) =
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) := rfl
  have hTT : T * T ∈ sesqNormOneScalars h B := by
    refine ⟨(c : K), hcN, ?_⟩
    have e1 : ((T * T : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K (Fin n → K)) =
        Matrix.GeneralLinearGroup.toLin (GeneralLinearGroup.scalar (Fin n) c) := by
      rw [← hAA, map_mul]
      rfl
    rw [e1, CatLeafProof.OddInner.toLin_scalar]
  have hTne : (QuotientGroup.mk T : sesqProjUnitary h B) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c', hc'N, hc'⟩ := h1
    apply hAne
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      simp [UnitaryFieldData.norm] at hc'N
    let u : Kˣ := Units.mk0 c' hc'0
    have hAu : (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) u := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      apply Units.ext
      rw [CatLeafProof.OddInner.toLin_scalar]
      exact hc'
    refine ⟨u, hc'N, ?_, hAu⟩
    have hdet := A.2.2
    rw [hAu, GeneralLinearGroup.coe_scalar] at hdet
    have hdet' : ((u : Kˣ) : K) ^ n = 1 := by
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet')
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2 := by
    refine orderOf_eq_prime ?_ hTne
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hTT
  have hcen := hasCompOrSolv_sesqCentralizer h hp2 (by rw [Module.finrank_fin_fun]; omega)
    (idForm_isSymm h n) (idForm_separatingLeft h n) hT
  let φS : gramSU h (idGram K n) →* sesqUnitaryGroup B :=
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
      LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp
        (gramSU h (idGram K n)).subtype).codRestrict _ fun g =>
      (toLin_mem_sesqUnitaryGroup_iff _).mpr ((mem_gramSU_iff_unitary h).mp g.2).1
  have hφS : Function.Injective φS := fun x y hxy =>
    Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective (congrArg Subtype.val hxy))
  have hrange : φS.range = CatalogueBUnitaryB.unitarySpecial B := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) x).mpr x.2
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      set g := Matrix.GeneralLinearGroup.toLin.symm (y : LinearMap.GeneralLinearGroup K
        (Fin n → K)) with hgdef
      have hgy : Matrix.GeneralLinearGroup.toLin g = (y : LinearMap.GeneralLinearGroup K
          (Fin n → K)) := MulEquiv.apply_symm_apply _ _
      have hg : g ∈ gramSU h (idGram K n) := by
        rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, hgy]
        exact hy
      exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩
  have hnorm : φS.range.Normal := by
    rw [hrange]
    exact CatalogueBUnitaryB.unitarySpecial_normal B
  have hcomm : commutator (sesqUnitaryGroup B) ≤ φS.range := by
    rw [hrange]
    intro x hx
    rw [CatalogueBUnitaryB.mem_unitarySpecial]
    have h1 := Abelianization.commutator_subset_ker
      ((Units.map (LinearMap.det : ((Fin n → K) →ₗ[K] (Fin n → K)) →* K)).comp
        (sesqUnitaryGroup B).subtype) hx
    rw [MonoidHom.mem_ker] at h1
    have h2 := congrArg Units.val h1
    simpa [MonoidHom.comp_apply, Units.coe_map] using h2
  exact solvableOrComponent_of_inj φS hφS hnorm hcomm A hcen

theorem oddDichotomyFamily_PSU : OddDichotomyFamily .PSU := by
  intro X _ _ n p f hp hp2 hadm hm τ hτ
  have hn : 3 ≤ n := hadm.2.2.1
  obtain ⟨K, _, h, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  refine solvableOrComponent_of_mulEquiv e τ ?_
  have : Finite K := h.finite
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e τ)
  have hτ2 : (e τ) ^ 2 = 1 := by
    rw [← map_pow, ← hτ, pow_orderOf_eq_one, map_one]
  have hτ1 : e τ ≠ 1 := by
    intro h1
    have := orderOf_eq_one_iff.2 (e.injective (h1.trans (map_one e).symm))
    rw [hτ] at this
    exact absurd this (by norm_num)
  have hK' : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).ker ≤
      center (gramSU h (idGram K n)) := by
    rw [QuotientGroup.ker_mk']
    rintro z ⟨c', -, -, hz⟩
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact (commute_scalar c' _).eq
  have hA2 : g * g ∈ normOneScalars h (gramSU h (idGram K n)) n := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hg, ← pow_two]
    exact hτ2
  have hAne : g ∉ normOneScalars h (gramSU h (idGram K n)) n := by
    intro hmem
    exact hτ1 (hg ▸ (QuotientGroup.eq_one_iff g).2 hmem)
  have := solvableOrComponent_of_cover (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))
    (QuotientGroup.mk'_surjective _) hK' g (solvableOrComponent_gramSU h hp2 hn g hA2 hAne)
  have hg' : QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) g = e τ := hg
  rw [hg'] at this
  exact this

end CFSG.ComponentClassification.CatFC.DS81
