module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBBlocks
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealEigen
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealKey
import CFSG.HardMathSupport.Dickson.Bal207.CompShape

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

namespace U6Comps

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

open Polynomial CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks

section Lift

variable {X : Type} [Group X] [Finite X]

theorem glaPComponent_image {K : Subgroup X} {a : X} (ha : a ∈ Subgroup.normalizer (K : Set X))
    {J : Subgroup X} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    GLAPComponent 3 (fixSubgroup (actHom K ⟨a, ha⟩))
      ((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) := by
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hαβ : ∀ k : ↥K, π (K.normalizerMonoidHom ⟨a, ha⟩ k) =
      actHom K ⟨a, ha⟩ (π k) := fun k => (actHom_mk K ⟨a, ha⟩ k).symm
  have hJ' := glaPComponent_fixSubgroup Nat.prime_three ha hJ
  exact glaPComponent_map_fixSubgroup π hker (K.normalizerMonoidHom ⟨a, ha⟩)
    (actHom K ⟨a, ha⟩) hαβ hπ Nat.prime_three hJ'

theorem glaPComponent_eq_of_image_eq {K : Subgroup X} {a : X}
    {J₁ J₂ : Subgroup X} (h₁ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₁)
    (h₂ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₂)
    (ha : a ∈ Subgroup.normalizer (K : Set X))
    (h : (J₁.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) =
      (J₂.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) : J₁ = J₂ := by
  have hker : (QuotientGroup.mk' (Subgroup.center ↥K)).ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have h₁K : J₁ ≤ K := fun y hy => (Subgroup.mem_inf.1 (h₁.1 hy)).1
  have h₂K : J₂ ≤ K := fun y hy => (Subgroup.mem_inf.1 (h₂.1 hy)).1
  have h₁' := glaPComponent_fixSubgroup Nat.prime_three ha h₁
  have h₂' := glaPComponent_fixSubgroup Nat.prime_three ha h₂
  have h3 : J₁.subgroupOf K = J₂.subgroupOf K :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq_of_ker_le_center _ hker h₁' h₂' h
  calc J₁ = (J₁.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le h₁K).symm
    _ = (J₂.subgroupOf K).map K.subtype := by rw [h3]
    _ = J₂ := Subgroup.map_subgroupOf_eq_of_le h₂K

theorem isQuasisimple_of_image {K : Subgroup X} {a : X} (ha : a ∈ Subgroup.normalizer (K : Set X))
    {J : Subgroup X} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hq : CFSG.Open.IsQuasisimple
      ↥((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)))) :
    CFSG.Open.IsQuasisimple ↥J ∧ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
      (↥((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) ⧸
        Subgroup.center ↥((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))))) := by
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hJK : J ≤ K := fun y hy => (Subgroup.mem_inf.1 (hJ.1 hy)).1
  have hJ₁ : GLAPComponent 3 (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩)) (J.subgroupOf K) :=
    glaPComponent_fixSubgroup Nat.prime_three ha hJ
  have hcov : (π.subgroupMap (J.subgroupOf K)).ker ≤ Subgroup.center ↥(J.subgroupOf K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ker_subgroupMap_le_center π hker _
  have hperf₁ : ⁅J.subgroupOf K, J.subgroupOf K⁆ = J.subgroupOf K := glaPComponent_perfect hJ₁
  have hperf : Group.IsPerfect ↥(J.subgroupOf K) := Subgroup.isPerfect_iff.2 hperf₁
  have hQ₁ : CFSG.IsQuasisimple ↥(J.subgroupOf K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_central_cover
      (π.subgroupMap (J.subgroupOf K)) (MonoidHom.subgroupMap_surjective π _) hperf hcov
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hq)
  have hQ₁' : CFSG.Open.IsQuasisimple ↥(J.subgroupOf K) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQ₁
  let e₂ : ↥(J.subgroupOf K) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJK
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂ hQ₁', ?_⟩
  obtain ⟨e₃⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hQ₁'.1 (π.subgroupMap (J.subgroupOf K)) (MonoidHom.subgroupMap_surjective π _) hcov
  exact ⟨(QuotientGroup.congr _ _ e₂.symm (Subgroup.map_center_eq e₂.symm)).trans e₃⟩


theorem isComponentOf_image {K : Subgroup X} {a : X} (ha : a ∈ Subgroup.normalizer (K : Set X))
    (hlayer : PerfectInLayer (actHom K ⟨a, ha⟩)) {J : Subgroup X}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    CFSG.Open.IsComponentOf ((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)))
      (fixSubgroup (actHom K ⟨a, ha⟩)) := by
  have hJβ := glaPComponent_image ha hJ
  have hlay := hlayer _ hJβ.1 (glaPComponent_perfect hJβ)
  exact (glaPComponent_isComponent_of_le_layer hJβ hlay).1

theorem threeComp_type {P : TauCeti.LieTypeIndex → Prop} {K : Subgroup X} {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X))
    (hlayer : PerfectInLayer (actHom K ⟨a, ha⟩))
    (htype : ∀ L : Subgroup (↥K ⧸ Subgroup.center ↥K),
      CFSG.Open.IsComponentOf L (fixSubgroup (actHom K ⟨a, ha⟩)) → IsLieQuot ↥L P) {J : Subgroup X}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    CFSG.Open.IsQuasisimple ↥J ∧ IsLieQuot ↥J P := by
  have hc := isComponentOf_image ha hlayer hJ
  obtain ⟨hq, ⟨e⟩⟩ := isQuasisimple_of_image ha hJ hc.2.2
  refine ⟨hq, ?_⟩
  obtain ⟨d, hd, ⟨φ⟩⟩ := htype _ hc
  exact ⟨d, hd, ⟨e.trans φ⟩⟩

end Lift

section Congr

variable {S G : Type} [Group S] [Group G]

theorem shapeData_of_congr {P : TauCeti.LieTypeIndex → Prop} (ε : S ≃* G) (β : MulAut S)
    (hlayer : PerfectInLayer (MulAut.congr ε β))
    (htype : ∀ L : Subgroup G, CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.congr ε β)) →
      IsLieQuot ↥L P) :
    PerfectInLayer β ∧
      ∀ L : Subgroup S, CFSG.Open.IsComponentOf L (fixSubgroup β) → IsLieQuot ↥L P := by
  refine ⟨LieSemisimple.perfectInLayer_of_congr ε β hlayer, fun L hL => ?_⟩
  have hmap : CFSG.Open.IsComponentOf (L.map (ε : S →* G)) (fixSubgroup (MulAut.congr ε β)) := by
    rw [CFSG.HardMathSupport.Dickson.Bal207.fixSubgroup_mulAutCongr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ε hL
  exact Bal209F4Aux.isLieQuot_mulEquiv (L.equivMapOfInjective (ε : S →* G) ε.injective).symm
    (htype _ hmap)

theorem three_comp_of_congr (ε : S ≃* G) (β : MulAut S)
    (h3 : ∀ L₁ L₂ L₃ : Subgroup G, CFSG.Open.IsComponentOf L₁ (fixSubgroup (MulAut.congr ε β)) →
      CFSG.Open.IsComponentOf L₂ (fixSubgroup (MulAut.congr ε β)) →
      CFSG.Open.IsComponentOf L₃ (fixSubgroup (MulAut.congr ε β)) → L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃) :
    ∀ L₁ L₂ L₃ : Subgroup S, CFSG.Open.IsComponentOf L₁ (fixSubgroup β) →
      CFSG.Open.IsComponentOf L₂ (fixSubgroup β) → CFSG.Open.IsComponentOf L₃ (fixSubgroup β) →
        L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃ := by
  have hmap : ∀ {L : Subgroup S}, CFSG.Open.IsComponentOf L (fixSubgroup β) →
      CFSG.Open.IsComponentOf (L.map (ε : S →* G)) (fixSubgroup (MulAut.congr ε β)) := fun hL => by
    rw [CFSG.HardMathSupport.Dickson.Bal207.fixSubgroup_mulAutCongr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ε hL
  intro L₁ L₂ L₃ h₁ h₂ h₃
  have inj := Subgroup.map_injective (f := (ε : S →* G)) ε.injective
  rcases h3 _ _ _ (hmap h₁) (hmap h₂) (hmap h₃) with h | h | h
  · exact Or.inl (inj h)
  · exact Or.inr (Or.inl (inj h))
  · exact Or.inr (Or.inr (inj h))

end Congr

section Shape

variable {X : Type} [Group X] [Finite X]

theorem shape_of_model {P : TauCeti.LieTypeIndex → Prop} {G : Type} [Group G] {K : Subgroup X}
    {a : X} (ha : a ∈ Subgroup.normalizer (K : Set X)) (ε : (↥K ⧸ Subgroup.center ↥K) ≃* G)
    (hlayer : PerfectInLayer (MulAut.congr ε (actHom K ⟨a, ha⟩)))
    (htype : ∀ L : Subgroup G,
      CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.congr ε (actHom K ⟨a, ha⟩))) → IsLieQuot ↥L P)
    (h3 : ∀ L₁ L₂ L₃ : Subgroup G,
      CFSG.Open.IsComponentOf L₁ (fixSubgroup (MulAut.congr ε (actHom K ⟨a, ha⟩))) →
      CFSG.Open.IsComponentOf L₂ (fixSubgroup (MulAut.congr ε (actHom K ⟨a, ha⟩))) →
      CFSG.Open.IsComponentOf L₃ (fixSubgroup (MulAut.congr ε (actHom K ⟨a, ha⟩))) →
        L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃) :
    (∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      CFSG.Open.IsQuasisimple ↥J ∧ IsLieQuot ↥J P) ∧
    (∀ J₁ J₂ J₃ : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₁ →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₂ →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₃ →
        J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) := by
  obtain ⟨hlayer', htype'⟩ := shapeData_of_congr ε _ hlayer htype
  have h3' := three_comp_of_congr ε _ h3
  refine ⟨fun J hJ => threeComp_type ha hlayer' htype' hJ, fun J₁ J₂ J₃ h₁ h₂ h₃ => ?_⟩
  rcases h3' _ _ _ (isComponentOf_image ha hlayer' h₁) (isComponentOf_image ha hlayer' h₂)
    (isComponentOf_image ha hlayer' h₃) with h | h | h
  · exact Or.inl (glaPComponent_eq_of_image_eq h₁ h₂ ha h)
  · exact Or.inr (Or.inl (glaPComponent_eq_of_image_eq h₁ h₃ ha h))
  · exact Or.inr (Or.inr (glaPComponent_eq_of_image_eq h₂ h₃ ha h))

end Shape

section Eigen

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem primaryComponent_X_sub_C_eq_eigenspace (x : Module.End K V) (d : K) :
    primaryComponent x (X - C d) = x.eigenspace d := by
  ext v
  rw [mem_primaryComponent_X_sub_C, Module.End.mem_eigenspace_iff]

theorem sum_finrank_eigenspace_le (f : Module.End K V) (S : Finset K) :
    ∑ d ∈ S, Module.finrank K (f.eigenspace d) ≤ Module.finrank K V := by
  classical
  have hind : iSupIndep f.eigenspace := f.eigenspaces_iSupIndep
  have key : ∀ S : Finset K, Module.finrank K (⨆ d ∈ S, f.eigenspace d : Submodule K V) =
      ∑ d ∈ S, Module.finrank K (f.eigenspace d) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert d S hd ih =>
      rw [Finset.sum_insert hd, ← ih]
      have hdis : Disjoint (f.eigenspace d) (⨆ c ∈ S, f.eigenspace c) :=
        hind.disjoint_biSup hd
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (f.eigenspace d)
        (⨆ c ∈ S, f.eigenspace c)
      rw [hdis.eq_bot, finrank_bot, add_zero] at h1
      rw [Finset.iSup_insert, h1]
  rw [← key S]
  exact Submodule.finrank_le _

end Eigen

section Rescale

open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {K0 : Type} [Field K0]

theorem exists_cube_root_units (h : UnitaryFieldData 2 3 K0) {c : K0ˣ} (hc : c ^ 3 = 1) :
    ∃ ν : K0ˣ, ν ^ 3 = c := by
  classical
  haveI := h.finite
  haveI : Fintype K0 := Fintype.ofFinite K0
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := K0ˣ)
  have hcard : Nat.card K0ˣ = 63 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, h.card]
    norm_num
  have hord : orderOf γ = 63 := (orderOf_eq_card_of_forall_mem_zpowers hγ).trans hcard
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hγ c))
  have h1 : γ ^ (k * 3) = 1 := by rw [pow_mul, hk, hc]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h2
  obtain ⟨j, hj⟩ : 21 ∣ k := by omega
  refine ⟨γ ^ (7 * j), ?_⟩
  rw [← pow_mul, ← hk, hj]
  congr 1
  ring

theorem exists_scalar_cube (h : UnitaryFieldData 2 3 K0) {g : StatedSU 6 (2 ^ 3) K0}
    (hg : primeFormConjHom h (idGram K0 6) ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ ^ 3 = 1) :
    ∃ μ : K0ˣ, μ ^ 3 = 1 ∧
      (g : GL (Fin 6) K0) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) μ := by
  obtain ⟨μ, hμ9, hpow⟩ := u6r_cube_scalar (h := h) (n := 6) (by norm_num)
    ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ hg
  have hpow' : (g : GL (Fin 6) K0) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) μ := hpow
  refine ⟨μ, ?_, hpow'⟩
  have hgG : (g : GL (Fin 6) K0) ∈ gramSU h ((1 : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) := by
    rw [← statedSU_eq_gramSU h]; exact g.2
  have hdet : ((g : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0).det = 1 := hgG.2
  have h9 : (μ : K0) ^ 9 = 1 := by
    have h9' : μ ^ (2 ^ 3 + 1) = 1 := hμ9
    have := congrArg (fun z : K0ˣ => (z : K0)) h9'
    simpa using this
  have h6 : (μ : K0) ^ 6 = 1 := by
    have e1 : ((Matrix.GeneralLinearGroup.scalar (Fin 6) μ : GL (Fin 6) K0) :
        Matrix (Fin 6) (Fin 6) K0).det = (μ : K0) ^ 6 := by
      simp [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]
    have e2 : (((g : GL (Fin 6) K0) ^ 3 : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0).det = 1 := by
      rw [Units.val_pow_eq_pow_val, Matrix.det_pow, hdet, one_pow]
    rw [hpow'] at e2
    rw [← e1]
    exact e2
  have h3 : (μ : K0) ^ 3 = 1 := by
    have : (μ : K0) ^ 3 * (μ : K0) ^ 6 = (μ : K0) ^ 6 := by
      rw [← pow_add]; simpa using h9.trans h6.symm
    have h6' : (μ : K0) ^ 6 ≠ 0 := pow_ne_zero 6 μ.ne_zero
    exact mul_right_cancel₀ h6' (this.trans (by rw [one_mul]))
  exact Units.ext (by simpa using h3)

theorem exists_rescale (h : UnitaryFieldData 2 3 K0) {g : StatedSU 6 (2 ^ 3) K0}
    (hg : primeFormConjHom h (idGram K0 6) ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ ^ 3 = 1) :
    ∃ (A : primeFormUnitary h (idGram K0 6)) (ν : K0ˣ), (A : GL (Fin 6) K0) ^ 3 = 1 ∧
      (g : GL (Fin 6) K0) = Matrix.GeneralLinearGroup.scalar (Fin 6) ν * (A : GL (Fin 6) K0) ∧
      primeFormConjHom h (idGram K0 6) A =
        primeFormConjHom h (idGram K0 6) ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ := by
  obtain ⟨μ, hμ3, hpow⟩ := exists_scalar_cube h hg
  obtain ⟨ν, hν⟩ := exists_cube_root_units h hμ3
  have hν9 : ν ^ (2 ^ 3 + 1) = 1 := by
    have : ν ^ 9 = (ν ^ 3) ^ 3 := by rw [← pow_mul]
    rw [show 2 ^ 3 + 1 = 9 by norm_num, this, hν, hμ3]
  obtain ⟨A, hA, hAconj⟩ := u6r_rescale (h := h) (n := 6)
    ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ hν9
  have hA' : (A : GL (Fin 6) K0) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) ν⁻¹ * (g : GL (Fin 6) K0) := hA
  refine ⟨A, ν, ?_, ?_, hAconj⟩
  · rw [hA', (commute_scalar ν⁻¹ (g : GL (Fin 6) K0)).symm.mul_pow, hpow, ← map_pow, ← map_mul,
      inv_pow, hν, inv_mul_cancel, map_one]
  · rw [hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

end Rescale

section TypeL2

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem isLieQuot_A1_of_isTypeL2 {Y : Type} [Group Y] (hY : IsTypeL2 8 Y) :
    IsLieQuot Y (fun e => ∃ q : TauCeti.PrimePower, IsTwoPow q 3 ∧ e = .A 1 q) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := hY
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  have hF8 : Nat.card F = 2 ^ 3 := by rw [hcard]; norm_num
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 3 (by norm_num) hF8
  let eP := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  exact ⟨⟨.A 1 q, hv⟩, ⟨q, ⟨rfl, rfl⟩, rfl⟩,
    ⟨e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      (eP.trans eC.symm))⟩⟩

end TypeL2

section BlockType

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

variable {K0 : Type} [Field K0]

theorem specialBlock_equiv_statedSU (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6))
    (H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A))
    (a : primaryFactors ((t6psub_toLin A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
      Module.End K0 (Fin 6 → K0)))
    (hself : dualPoly h.bar (a : K0[X]) = a) (hdeg : (a : K0[X]).natDegree = 1) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ 3) ^ 2 ∧
      Nonempty (↥(specialBlock (idForm h 6) (t6psub_toLin A) (a : K0[X])) ≃*
        ↥(CFSG.Open.StatedSU (primaryMultiplicity ((t6psub_toLin A :
          LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) : Module.End K0 (Fin 6 → K0))
            (a : K0[X])) (2 ^ 3) E)) := by
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
    nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
  obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
  obtain ⟨e3⟩ :=
    CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K0[X]))
        (primaryComponent ((t6psub_toLin A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
          Module.End K0 (Fin 6 → K0)) (a : K0[X]))))
        (Fin (Module.finrank (AdjoinRoot (a : K0[X]))
        (primaryComponent ((t6psub_toLin A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
          Module.End K0 (Fin 6 → K0)) (a : K0[X])))) (AdjoinRoot (a : K0[X]))))
      (fun i j => by rw [hb i j, Matrix.one_apply])
  let e4 := (e.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
  have hcard := hE.card_eq_sq
  rw [hdeg, mul_one] at hcard
  rw [hdeg, mul_one] at e4
  exact ⟨AdjoinRoot (a : K0[X]), inferInstance, hE.finite, hcard, ⟨e4⟩⟩

@[expose] noncomputable def blockImage (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) (d : K0) : Subgroup (primeFormP h (idGram K0 6)) :=
  ((specialBlock (idForm h 6) (t6psub_toLin A) (X - C d)).comap
      (LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.toLinSU h 6)).map
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K0 6)) 6))

theorem blockImage_equiv_statedProj (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6))
    (H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A)) (i : t6psub_Idx h 6 A)
    (hself : dualPoly h.bar (i.1 : K0[X]) = i.1) (hdeg : (i.1 : K0[X]).natDegree = 1)
    (hm : 3 ≤ primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
      Module.End K0 (Fin 6 → K0)) (i.1 : K0[X])) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ 3) ^ 2 ∧
      Nonempty ((↥((t6psub_block A i).map (QuotientGroup.mk' (normOneScalars h
        (gramSU h (idGram K0 6)) 6))) ⧸ Subgroup.center ↥((t6psub_block A i).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K0 6)) 6)))) ≃*
        StatedProj (StatedSU (primaryMultiplicity ((t6psub_toLin A :
          LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) : Module.End K0 (Fin 6 → K0))
            (i.1 : K0[X])) (2 ^ 3) E)) := by
  obtain ⟨E, hEf, hEfin, hEcard, ⟨e4⟩⟩ := specialBlock_equiv_statedSU h A H i.1 hself hdeg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : (primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
      Module.End K0 (Fin 6 → K0)) (i.1 : K0[X]), 2 ^ 3) ≠ (3, 2) := by
    intro h0
    simp only [Prod.mk.injEq] at h0
    omega
  obtain ⟨hq, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := E)
    (p := 2) (f := 3) hEcard hm hnq
  refine ⟨E, hEf, hEfin, hEcard, ?_⟩
  have e5 : ↥(t6psub_block A i) ≃* ↥(specialBlock (idForm h 6) (t6psub_toLin A) (i.1 : K0[X])) :=
    (Subgroup.equivMapOfInjective (t6psub_block A i) (t6psuh_toLinSU h 6)
      t6psuh_toLinSU_injective).trans (MulEquiv.subgroupCongr (t6psub_map_block A H i))
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K0) :=
    Finite.of_injective (fun g : GL (Fin 6) K0 => (g : Matrix (Fin 6) (Fin 6) K0))
      Units.val_injective
  have hperf : commutator ↥(t6psub_block A i) = ⊤ :=
    (t6psub_isQuasisimple_block A H i).1.commutator_eq_top
  have hker : ((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K0 6)) 6)).subgroupMap
      (t6psub_block A i)).ker ≤ Subgroup.center ↥(t6psub_block A i) :=
    ker_subgroupMap_le_center _ u6r_ker_le_center _
  obtain ⟨e6⟩ := nonempty_centralQuotient_mulEquiv hperf
    ((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K0 6)) 6)).subgroupMap
      (t6psub_block A i)) (MonoidHom.subgroupMap_surjective _ _) hker
  exact ⟨e6.symm.trans ((QuotientGroup.congr _ _ (e5.trans e4)
    (Subgroup.map_center_eq (e5.trans e4))).trans (QuotientGroup.quotientMulEquivOfEq hZ))⟩

noncomputable abbrev xlin (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) : Module.End K0 (Fin 6 → K0) :=
  ((t6psub_toLin A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) : Module.End K0 (Fin 6 → K0))

theorem eigMult_eq_finrank (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (d : K0) :
    eigMult (A : GL (Fin 6) K0) d = Module.finrank K0 (primaryComponent (xlin h A) (X - C d)) := by
  have hker : LinearMap.ker (Matrix.toLin' ((A : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) -
      d • (LinearMap.id : (Fin 6 → K0) →ₗ[K0] (Fin 6 → K0))) =
      primaryComponent (xlin h A) (X - C d) := by
    ext v
    rw [u6r_mem_primaryComponent_iff, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  unfold eigMult
  rw [hker]

theorem exists_goodIdx (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0}
    (hd : 2 ≤ eigMult (A : GL (Fin 6) K0) d) :
    d ^ 3 = 1 ∧ ∃ i : t6psub_Idx h 6 A, (i.1 : K0[X]) = X - C d := by
  rw [eigMult_eq_finrank] at hd
  have hpos : 0 < Module.finrank K0 (primaryComponent (xlin h A) (X - C d)) := by omega
  obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hmem : X - C d ∈ primaryFactors (xlin h A) :=
    u6r_mem_primaryFactors A hv (fun h0 => hv0 (Subtype.ext h0))
  obtain ⟨c, hc3, hcd⟩ := u6r_primaryFactor_eq A hA3 hmem
  have hcd' : d = c := by
    have := congrArg (fun p : K0[X] => p.coeff 0) hcd
    simpa using this
  subst hcd'
  refine ⟨hc3, ⟨⟨X - C d, hmem⟩, ?_⟩, rfl⟩
  exact isGoodBlock_X_sub_C (hK := h) hmem hd (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    omega)

theorem primaryMultiplicity_eq_eigMult (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) (d : K0) :
    primaryMultiplicity (xlin h A) (X - C d) = eigMult (A : GL (Fin 6) K0) d := by
  rw [primaryMultiplicity_X_sub_C, eigMult_eq_finrank]

theorem comp_eq_blockImage (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {L : Subgroup (primeFormP h (idGram K0 6))}
    (hL : CFSG.Open.IsComponentOf L (fixSubgroup (primeFormConjHom h (idGram K0 6) A))) :
    ∃ d : K0, 2 ≤ eigMult (A : GL (Fin 6) K0) d ∧ L = blockImage h A d := by
  have H := primaryData_toLin' h A.2 Nat.prime_three (by norm_num : 3 ≠ 2) (c := 1)
    (by rw [hA3, map_one])
  obtain ⟨a, ha⟩ := exists_good_block_of_component (by norm_num : 2 ≤ 2 ^ 3) A rfl H L hL
  obtain ⟨d, hd3, hform⟩ := u6r_primaryFactor_eq A hA3 a.1.2
  refine ⟨d, ?_, ?_⟩
  · have h2 := a.2.1
    rw [hform] at h2
    have h2' : 2 ≤ primaryMultiplicity (xlin h A) (X - C d) := h2
    rw [primaryMultiplicity_eq_eigMult] at h2'
    exact h2'
  · rw [ha, blockImage, ← hform]
    rfl

theorem isLieQuot_blockImage_two (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0}
    (hd : eigMult (A : GL (Fin 6) K0) d = 2) :
    IsLieQuot ↥(blockImage h A d)
      (fun e => ∃ q : TauCeti.PrimePower, IsTwoPow q 3 ∧ e = .A 1 q) := by
  obtain ⟨hd3, i, hi⟩ := exists_goodIdx h A hA3 (d := d) (by omega)
  have H := primaryData_toLin' h A.2 Nat.prime_three (by norm_num : 3 ≠ 2) (c := 1)
    (by rw [hA3, map_one])
  have hself : dualPoly h.bar (i.1 : K0[X]) = i.1 := by
    rw [hi]; exact u6r_dualPoly h (by decide) hd3
  have hm2 : primaryMultiplicity (xlin h A) (i.1 : K0[X]) = 2 := by
    rw [hi, primaryMultiplicity_eq_eigMult, hd]
  have hT := u6r_isTypeL2_block A H i hself hm2
  have hdeg : (i.1 : K0[X]).natDegree = 1 := by rw [hi]; exact natDegree_X_sub_C d
  rw [hdeg] at hT
  have hB : blockImage h A d = (t6psub_block A i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K0 6)) 6)) := by
    unfold blockImage t6psub_block
    rw [hi]
    rfl
  rw [hB]
  exact isLieQuot_A1_of_isTypeL2 (by simpa using hT)

theorem isLieQuot_blockImage_twistedA (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0} {r : ℕ}
    (hr : 2 ≤ r) (hd : eigMult (A : GL (Fin 6) K0) d = r + 1) :
    IsLieQuot ↥(blockImage h A d)
      (fun e => ∃ q : TauCeti.PrimePower, IsTwoPow q 3 ∧ e = .twistedA r q) := by
  obtain ⟨hd3, i, hi⟩ := exists_goodIdx h A hA3 (d := d) (by omega)
  have H := primaryData_toLin' h A.2 Nat.prime_three (by norm_num : 3 ≠ 2) (c := 1)
    (by rw [hA3, map_one])
  have hself : dualPoly h.bar (i.1 : K0[X]) = i.1 := by
    rw [hi]; exact u6r_dualPoly h (by decide) hd3
  have hmi : primaryMultiplicity (xlin h A) (i.1 : K0[X]) = r + 1 := by
    rw [hi, primaryMultiplicity_eq_eigMult, hd]
  have hdeg : (i.1 : K0[X]).natDegree = 1 := by rw [hi]; exact natDegree_X_sub_C d
  have hm3 : 3 ≤ primaryMultiplicity (xlin h A) (i.1 : K0[X]) := by omega
  obtain ⟨E, hEf, hEfin, hEcard, ⟨e⟩⟩ := blockImage_equiv_statedProj h A H i hself hdeg hm3
  rw [show primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
    Module.End K0 (Fin 6 → K0)) (i.1 : K0[X]) = r + 1 from hmi] at e
  have hB : blockImage h A d = (t6psub_block A i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K0 6)) 6)) := by
    unfold blockImage t6psub_block
    rw [hi]
    rfl
  rw [hB]
  refine KSExact.isLieQuot_of_twistedA_model (m := r) (p := 2) (f := 3) ?_ _
    (fun q hq1 hq2 => ⟨q, ⟨hq1, hq2⟩, rfl⟩)
  refine ⟨⟨Nat.prime_two, by norm_num, by omega, ?_⟩, E, hEf, hEfin, hEcard, ⟨e⟩⟩
  intro h0
  simp only [Prod.mk.injEq] at h0
  omega

theorem sum_eigMult_le (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (S : Finset K0) : ∑ d ∈ S, eigMult (A : GL (Fin 6) K0) d ≤ 6 := by
  have e : ∀ d, eigMult (A : GL (Fin 6) K0) d =
      Module.finrank K0 ((xlin h A).eigenspace d) := fun d => by
    rw [eigMult_eq_finrank, primaryComponent_X_sub_C_eq_eigenspace]
  simp only [e]
  have := sum_finrank_eigenspace_le (xlin h A) S
  rwa [Module.finrank_fin_fun] at this

theorem eigMult_three_le (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    {a b c : K0} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    eigMult (A : GL (Fin 6) K0) a + eigMult (A : GL (Fin 6) K0) b +
      eigMult (A : GL (Fin 6) K0) c ≤ 6 := by
  classical
  have := sum_eigMult_le h A {a, b, c}
  rwa [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, ← add_assoc] at this

theorem eigMult_four_le (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    {a b c d : K0} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    eigMult (A : GL (Fin 6) K0) a + eigMult (A : GL (Fin 6) K0) b +
      eigMult (A : GL (Fin 6) K0) c + eigMult (A : GL (Fin 6) K0) d ≤ 6 := by
  classical
  have := sum_eigMult_le h A {a, b, c, d}
  rwa [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_insert (by simp [hcd]), Finset.sum_singleton, ← add_assoc, ← add_assoc] at this

theorem isLieQuot_mono {Y : Type*} [Group Y] {P Q : TauCeti.LieTypeIndex → Prop}
    (hPQ : ∀ e, P e → Q e) (hY : IsLieQuot Y P) : IsLieQuot Y Q := by
  obtain ⟨d, hd, hφ⟩ := hY
  exact ⟨d, hPQ d.1 hd, hφ⟩

theorem comps_count (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1)
    (hno : ¬ ∃ d₁ d₂ d₃ : K0, d₁ ≠ d₂ ∧ d₁ ≠ d₃ ∧ d₂ ≠ d₃ ∧
      2 ≤ eigMult (A : GL (Fin 6) K0) d₁ ∧ 2 ≤ eigMult (A : GL (Fin 6) K0) d₂ ∧
      2 ≤ eigMult (A : GL (Fin 6) K0) d₃)
    (L₁ L₂ L₃ : Subgroup (primeFormP h (idGram K0 6)))
    (h₁ : CFSG.Open.IsComponentOf L₁ (fixSubgroup (primeFormConjHom h (idGram K0 6) A)))
    (h₂ : CFSG.Open.IsComponentOf L₂ (fixSubgroup (primeFormConjHom h (idGram K0 6) A)))
    (h₃ : CFSG.Open.IsComponentOf L₃ (fixSubgroup (primeFormConjHom h (idGram K0 6) A))) :
    L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃ := by
  obtain ⟨d₁, m₁, rfl⟩ := comp_eq_blockImage h A hA3 h₁
  obtain ⟨d₂, m₂, rfl⟩ := comp_eq_blockImage h A hA3 h₂
  obtain ⟨d₃, m₃, rfl⟩ := comp_eq_blockImage h A hA3 h₃
  by_cases e12 : d₁ = d₂
  · exact Or.inl (by rw [e12])
  by_cases e13 : d₁ = d₃
  · exact Or.inr (Or.inl (by rw [e13]))
  by_cases e23 : d₂ = d₃
  · exact Or.inr (Or.inr (by rw [e23]))
  exact absurd ⟨d₁, d₂, d₃, e12, e13, e23, m₁, m₂, m₃⟩ hno

theorem eigMult_two_le (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    {a b : K0} (hab : a ≠ b) :
    eigMult (A : GL (Fin 6) K0) a + eigMult (A : GL (Fin 6) K0) b ≤ 6 := by
  classical
  have := sum_eigMult_le h A {a, b}
  rwa [Finset.sum_insert (by simp [hab]), Finset.sum_singleton] at this

theorem fixedComps_big (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1)
    (hbig : ∃ c : K0, 4 ≤ eigMult (A : GL (Fin 6) K0) c)
    (hns : ∀ d : K0, eigMult (A : GL (Fin 6) K0) d ≠ 6) :
    (∀ L : Subgroup (primeFormP h (idGram K0 6)),
      CFSG.Open.IsComponentOf L (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) →
        IsLieQuot ↥L IsU6BigCompIndex) ∧
    (∀ L₁ L₂ L₃ : Subgroup (primeFormP h (idGram K0 6)),
      CFSG.Open.IsComponentOf L₁ (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) →
      CFSG.Open.IsComponentOf L₂ (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) →
      CFSG.Open.IsComponentOf L₃ (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) →
        L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃) := by
  obtain ⟨c, hc⟩ := hbig
  refine ⟨fun L hL => ?_, comps_count h A hA3 ?_⟩
  · obtain ⟨d, hd2, rfl⟩ := comp_eq_blockImage h A hA3 hL
    have hd6 := hns d
    have hd3 : eigMult (A : GL (Fin 6) K0) d ≠ 3 := by
      intro h3
      have hcd : c ≠ d := by
        rintro rfl
        omega
      have := eigMult_two_le h A hcd
      omega
    have hle6 : eigMult (A : GL (Fin 6) K0) d ≤ 6 := by
      classical
      have := sum_eigMult_le h A {d}
      simpa using this
    have hcases : eigMult (A : GL (Fin 6) K0) d = 2 ∨ eigMult (A : GL (Fin 6) K0) d = 4 ∨
        eigMult (A : GL (Fin 6) K0) d = 5 := by omega
    rcases hcases with h2 | h4 | h5
    · exact isLieQuot_mono (fun e ⟨q, hq, he⟩ => ⟨q, hq, Or.inl he⟩)
        (isLieQuot_blockImage_two h A hA3 h2)
    · exact isLieQuot_mono (fun e ⟨q, hq, he⟩ => ⟨q, hq, Or.inr (Or.inl he)⟩)
        (isLieQuot_blockImage_twistedA h A hA3 (r := 3) (by norm_num) (by omega))
    · exact isLieQuot_mono (fun e ⟨q, hq, he⟩ => ⟨q, hq, Or.inr (Or.inr he)⟩)
        (isLieQuot_blockImage_twistedA h A hA3 (r := 4) (by norm_num) (by omega))
  · rintro ⟨d₁, d₂, d₃, e12, e13, e23, m₁, m₂, m₃⟩
    classical
    by_cases c1 : c = d₁
    · subst c1
      have := eigMult_three_le h A e12 e13 e23
      omega
    by_cases c2 : c = d₂
    · subst c2
      have := eigMult_three_le h A e12 e13 e23
      omega
    by_cases c3 : c = d₃
    · subst c3
      have := eigMult_three_le h A e12 e13 e23
      omega
    have := eigMult_four_le h A c1 c2 c3 e12 e13 e23
    omega

theorem fixedComps_three (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1)
    (hdiv : ∀ c : K0, 3 ∣ eigMult (A : GL (Fin 6) K0) c)
    (hns : ∀ d : K0, eigMult (A : GL (Fin 6) K0) d ≠ 6) :
    (∀ L : Subgroup (primeFormP h (idGram K0 6)),
      CFSG.Open.IsComponentOf L (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) →
        IsLieQuot ↥L KSF4SU3.IsU3EightIndexTwo) ∧
    (∀ L₁ L₂ L₃ : Subgroup (primeFormP h (idGram K0 6)),
      CFSG.Open.IsComponentOf L₁ (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) →
      CFSG.Open.IsComponentOf L₂ (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) →
      CFSG.Open.IsComponentOf L₃ (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) →
        L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃) := by
  refine ⟨fun L hL => ?_, comps_count h A hA3 ?_⟩
  · obtain ⟨d, hd2, rfl⟩ := comp_eq_blockImage h A hA3 hL
    have hd6 := hns d
    have hle6 : eigMult (A : GL (Fin 6) K0) d ≤ 6 := by
      classical
      have := sum_eigMult_le h A {d}
      simpa using this
    have hd3 := hdiv d
    have h3 : eigMult (A : GL (Fin 6) K0) d = 3 := by omega
    exact isLieQuot_blockImage_twistedA h A hA3 (r := 2) le_rfl (by omega)
  · rintro ⟨d₁, d₂, d₃, e12, e13, e23, m₁, m₂, m₃⟩
    have := eigMult_three_le h A e12 e13 e23
    have a1 := hdiv d₁
    have a2 := hdiv d₂
    have a3 := hdiv d₃
    omega

theorem eigMult_scalar_mul (ν : K0ˣ) (A : GL (Fin 6) K0) (c : K0) :
    eigMult (Matrix.GeneralLinearGroup.scalar (Fin 6) ν * A) c =
      eigMult A (((ν⁻¹ : K0ˣ) : K0) * c) := by
  have key : ∀ v : Fin 6 → K0,
      Matrix.toLin' (((Matrix.GeneralLinearGroup.scalar (Fin 6) ν * A : GL (Fin 6) K0)) :
        Matrix (Fin 6) (Fin 6) K0) v =
        (ν : K0) • Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) K0) v := fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  have hker : LinearMap.ker (Matrix.toLin' (((Matrix.GeneralLinearGroup.scalar (Fin 6) ν * A :
      GL (Fin 6) K0)) : Matrix (Fin 6) (Fin 6) K0) -
      c • (LinearMap.id : (Fin 6 → K0) →ₗ[K0] (Fin 6 → K0))) =
      LinearMap.ker (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) K0) -
      (((ν⁻¹ : K0ˣ) : K0) * c) • (LinearMap.id : (Fin 6 → K0) →ₗ[K0] (Fin 6 → K0))) := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      key, sub_eq_zero]
    constructor
    · intro hv
      have : (((ν⁻¹ : K0ˣ) : K0) * (ν : K0)) • Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) K0) v =
          (((ν⁻¹ : K0ˣ) : K0) * c) • v := by
        rw [mul_smul, hv, mul_smul]
      rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at this
    · intro hv
      rw [hv, smul_smul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  unfold eigMult
  rw [hker]

theorem eigMult_ne_six_of_not_scalar (A : GL (Fin 6) K0) (ν : K0ˣ)
    (hnot : ¬ ∃ c : K0ˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) ν * A =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c) (d : K0) : eigMult A d ≠ 6 := by
  intro h6
  have hfin : Module.finrank K0 (LinearMap.ker (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) K0) -
      d • (LinearMap.id : (Fin 6 → K0) →ₗ[K0] (Fin 6 → K0)))) =
      Module.finrank K0 (Fin 6 → K0) := by
    rw [Module.finrank_fin_fun]; exact h6
  have htop := Submodule.eq_top_of_finrank_eq hfin
  have hAv : ∀ v : Fin 6 → K0, Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) K0) v = d • v := by
    intro v
    have hv : v ∈ LinearMap.ker (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) K0) -
      d • (LinearMap.id : (Fin 6 → K0) →ₗ[K0] (Fin 6 → K0))) := by rw [htop]; trivial
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hv
    exact hv
  have hAmat : (A : Matrix (Fin 6) (Fin 6) K0) = Matrix.scalar (Fin 6) d := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [hAv, Matrix.toLin'_apply, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  have hd0 : d ≠ 0 := by
    intro hd
    have h1 := congrArg (fun z : GL (Fin 6) K0 => (z : Matrix (Fin 6) (Fin 6) K0))
      (mul_inv_cancel A)
    simp only [Units.val_mul, Units.val_one, hAmat, hd, map_zero, zero_mul] at h1
    exact zero_ne_one h1
  apply hnot
  refine ⟨ν * Units.mk0 d hd0, ?_⟩
  rw [map_mul]
  congr 1
  apply Units.ext
  rw [hAmat]
  simp [Matrix.GeneralLinearGroup.coe_scalar]

end BlockType

section Targets

open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj

variable {K0 : Type} [Field K0]

theorem conj_projH_eq_uConjAut (h : UnitaryFieldData 2 3 K0) (g : StatedSU 6 (2 ^ 3) K0) :
    MulAut.conj (projH _ g) =
      uConjAut h (by norm_num) ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective z
  have e1 := uConjAut_proj h (by norm_num : 1 ≤ 6)
    ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ t
  refine Eq.trans ?_ e1.symm
  rw [MulAut.conj_apply]
  rfl

theorem congr_actHom_eq {X : Type} [Group X] {K : Subgroup X} (h : UnitaryFieldData 2 3 K0)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSU 6 (2 ^ 3) K0)) {y : X}
    {g : StatedSU 6 (2 ^ 3) K0} (hact : ActsAs K e y g) :
    ∃ hy : y ∈ Subgroup.normalizer (K : Set X),
      MulAut.congr (e.trans (uTransport h (by norm_num : 1 ≤ 6))) (actHom K ⟨y, hy⟩) =
        primeFormConjHom h (idGram K0 6) ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ := by
  obtain ⟨hy, hconj⟩ := hact
  refine ⟨hy, ?_⟩
  have h1 : MulAut.congr (e.trans (uTransport h (by norm_num : 1 ≤ 6))) (actHom K ⟨y, hy⟩) =
      MulAut.congr (uTransport h (by norm_num : 1 ≤ 6))
        (MulAut.congr e (actHom K ⟨y, hy⟩)) := MulEquiv.ext fun _ => rfl
  rw [h1, hconj, conj_projH_eq_uConjAut h g]
  exact MulEquiv.apply_symm_apply (MulAut.congr (uTransport h (by norm_num : 1 ≤ 6))) _

theorem conj_pow_three (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) :
    primeFormConjHom h (idGram K0 6) A ^ 3 = 1 := by
  rw [← map_pow]
  have : A ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hA3]; rfl)
  rw [this, map_one]

theorem exists_model_of_actsAs {X : Type} [Group X] {K : Subgroup X} (h : UnitaryFieldData 2 3 K0)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSU 6 (2 ^ 3) K0)) {y : X}
    {g : StatedSU 6 (2 ^ 3) K0} (hact : ActsAs K e y g) (hy3 : y ^ 3 = 1) :
    ∃ (hy : y ∈ Subgroup.normalizer (K : Set X)) (A : primeFormUnitary h (idGram K0 6)) (ν : K0ˣ),
      (A : GL (Fin 6) K0) ^ 3 = 1 ∧
      (g : GL (Fin 6) K0) = Matrix.GeneralLinearGroup.scalar (Fin 6) ν * (A : GL (Fin 6) K0) ∧
      MulAut.congr (e.trans (uTransport h (by norm_num : 1 ≤ 6))) (actHom K ⟨y, hy⟩) =
        primeFormConjHom h (idGram K0 6) A := by
  obtain ⟨hy, hcongr⟩ := congr_actHom_eq h e hact
  have hcube : primeFormConjHom h (idGram K0 6)
      ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩ ^ 3 = 1 := by
    rw [← hcongr, ← map_pow, ← map_pow]
    have : (⟨y, hy⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one, map_one]
  obtain ⟨A, ν, hA3, hgA, hAconj⟩ := exists_rescale h hcube
  exact ⟨hy, A, ν, hA3, hgA, by rw [hcongr, hAconj]⟩

end Targets

end U6Comps

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
