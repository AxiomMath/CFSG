module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Dickson.I271.Support.Action
public import CFSG.RankThree.PartOne.CTP.SeitzField
import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

theorem fixedSubgroup_eq_fixSubgroup {G : Type} [Group G] (α : MulAut G) :
    CFSG.RankThree.PartOne.CTP.fixedSubgroup α = fixSubgroup α :=
  Subgroup.ext fun _ => Iff.rfl

theorem liftComp_quasisimple_iso {X : Type} [Group X] [Finite X] {K : Subgroup X} {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) {J₁ : Subgroup ↥K}
    {T : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hJ₁ : GLAPComponent 3 (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩)) J₁)
    (hmap : J₁.map (QuotientGroup.mk' (Subgroup.center ↥K)) = T)
    (hTq : CFSG.Open.IsQuasisimple ↥T) :
    CFSG.Open.IsQuasisimple ↥(J₁.map K.subtype) ∧
      Nonempty ((↥(J₁.map K.subtype) ⧸ Subgroup.center ↥(J₁.map K.subtype)) ≃*
        (↥T ⧸ Subgroup.center ↥T)) := by
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  subst hmap
  have hcov : (π.subgroupMap J₁).ker ≤ Subgroup.center ↥J₁ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ker_subgroupMap_le_center π hker J₁
  have hperf₁ : ⁅J₁, J₁⁆ = J₁ := glaPComponent_perfect hJ₁
  have hperf : Group.IsPerfect ↥J₁ := Subgroup.isPerfect_iff.2 hperf₁
  have hQ₁ : CFSG.IsQuasisimple ↥J₁ :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_central_cover
      (π.subgroupMap J₁) (MonoidHom.subgroupMap_surjective π J₁) hperf hcov
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hTq)
  have hQ₁' : CFSG.Open.IsQuasisimple ↥J₁ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQ₁
  let e₂ : ↥J₁ ≃* ↥(J₁.map K.subtype) := J₁.equivMapOfInjective K.subtype K.subtype_injective
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂ hQ₁', ?_⟩
  obtain ⟨e₃⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hQ₁'.1 (π.subgroupMap J₁) (MonoidHom.subgroupMap_surjective π J₁) hcov
  exact ⟨(QuotientGroup.congr _ _ e₂.symm (Subgroup.map_center_eq e₂.symm)).trans e₃⟩

theorem threeComponents_lift {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) {y : X} (hy : y ∈ Subgroup.normalizer (K : Set X))
    {n : ℕ} {T : Fin n → Subgroup (↥K ⧸ Subgroup.center ↥K)} (hT : Function.Injective T)
    (hTc : ∀ L : Subgroup (↥K ⧸ Subgroup.center ↥K),
      GLAPComponent 3 (CFSG.RankThree.PartOne.CTP.fixedSubgroup (actHom K ⟨y, hy⟩)) L ↔
        ∃ i, L = T i)
    (hTq : ∀ i, CFSG.Open.IsQuasisimple ↥(T i)) :
    ∃ J : Fin n → Subgroup X, Function.Injective J ∧
      (∀ L : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) L ↔
        ∃ i, L = J i) ∧
      ∀ i, CFSG.Open.IsQuasisimple ↥(J i) ∧
        Nonempty ((↥(J i) ⧸ Subgroup.center ↥(J i)) ≃* (↥(T i) ⧸ Subgroup.center ↥(T i))) := by
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hαβ : ∀ k : ↥K, π (K.normalizerMonoidHom ⟨y, hy⟩ k) =
      actHom K ⟨y, hy⟩ (π k) := fun k => (actHom_mk K ⟨y, hy⟩ k).symm
  have hTc' : ∀ L : Subgroup (↥K ⧸ Subgroup.center ↥K),
      GLAPComponent 3 (fixSubgroup (actHom K ⟨y, hy⟩)) L ↔ ∃ i, L = T i := by
    intro L
    rw [← fixedSubgroup_eq_fixSubgroup]
    exact hTc L
  choose J₁ hJ₁ hJ₁map using fun i : Fin n =>
    exists_glaPComponent_map_fixSubgroup π hker (K.normalizerMonoidHom ⟨y, hy⟩)
      (actHom K ⟨y, hy⟩) hαβ hπ Nat.prime_three ((hTc' (T i)).2 ⟨i, rfl⟩)
  have hC : fixSubgroup (K.normalizerMonoidHom ⟨y, hy⟩) =
      (K ⊓ Subgroup.centralizer ({y} : Set X)).subgroupOf K :=
    fixSubgroup_normalizerMonoidHom hy
  have hJ₁' : ∀ i,
      GLAPComponent 3 ((K ⊓ Subgroup.centralizer ({y} : Set X)).subgroupOf K) (J₁ i) := by
    intro i
    rw [← hC]
    exact hJ₁ i
  have hJ₀ : ∀ i, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X))
      ((J₁ i).map K.subtype) := by
    intro i
    have hc : ∀ z ∈ ((K ⊓ Subgroup.centralizer ({y} : Set X)).subgroupOf K) ⊓ K.subtype.ker,
        ∀ w ∈ (K ⊓ Subgroup.centralizer ({y} : Set X)).subgroupOf K, w * z = z * w := by
      intro z hz w _
      have : z = 1 := Subtype.ext (MonoidHom.mem_ker.1 hz.2)
      rw [this, mul_one, one_mul]
    have h := glaPComponent_map_central Nat.prime_three K.subtype hc (hJ₁' i)
    have hCK : K ⊓ Subgroup.centralizer ({y} : Set X) ≤ K := inf_le_left
    rwa [Subgroup.map_subgroupOf_eq_of_le hCK] at h
  have hJinj : Function.Injective (fun i => (J₁ i).map K.subtype) := by
    intro i j hij
    have h1 : J₁ i = J₁ j := Subgroup.map_injective K.subtype_injective hij
    apply hT
    rw [← hJ₁map i, ← hJ₁map j, h1]
  have hiff : ∀ L : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) L ↔
      ∃ i, L = (J₁ i).map K.subtype := by
    intro L
    constructor
    · intro hL
      have hLK : L ≤ K := fun z hz => (Subgroup.mem_inf.1 (hL.1 hz)).1
      have hL' : GLAPComponent 3 (fixSubgroup (K.normalizerMonoidHom ⟨y, hy⟩)) (L.subgroupOf K) :=
        glaPComponent_fixSubgroup Nat.prime_three hy hL
      obtain ⟨i, hi⟩ := (hTc' _).1 (glaPComponent_map_fixSubgroup π hker
        (K.normalizerMonoidHom ⟨y, hy⟩) (actHom K ⟨y, hy⟩) hαβ hπ Nat.prime_three hL')
      have h2 : L.subgroupOf K = J₁ i :=
        CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq_of_ker_le_center π hker hL'
          (hJ₁ i) (hi.trans (hJ₁map i).symm)
      refine ⟨i, ?_⟩
      calc L = (L.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hLK).symm
        _ = (J₁ i).map K.subtype := by rw [h2]
    · rintro ⟨i, rfl⟩
      exact hJ₀ i
  exact ⟨fun i => (J₁ i).map K.subtype, hJinj, hiff,
    fun i => liftComp_quasisimple_iso hy (hJ₁ i) (hJ₁map i) (hTq i)⟩

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
