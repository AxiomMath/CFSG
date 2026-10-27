module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Bg.Pu5.Assembly
public import CFSG.GH74.GLS.Bg.Pu5.L299T
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cSec_cmap_eq (K : Subgroup G) (c : G) : cSec (cmap c K) = cmap c (cSec K) := by
  apply le_antisymm
  · intro x hx
    rw [mem_cmap]
    have h := conj_mem_cSec_cmap hx c⁻¹
    rw [cmap_inv_cancel] at h
    simpa using h
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact conj_mem_cSec_cmap hy c

theorem isSylowOf_cmap {P K : Subgroup G} (h : IsSylowOf 2 P K) (c : G) :
    IsSylowOf 2 (cmap c P) (cmap c K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hp, hidx⟩ := h
  refine ⟨Subgroup.map_mono hle, ?_, ?_⟩
  · exact hp.of_equiv
      (Subgroup.equivMapOfInjective P (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)
  · have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj c).toMonoidHom) P K
      (MulAut.conj c).injective
    show ¬ 2 ∣ (P.map (MulAut.conj c).toMonoidHom).relIndex (K.map (MulAut.conj c).toMonoidHom)
    rw [this]
    exact hidx

theorem exists_mulEquiv_of_isSylowOf_two {Y P Q : Subgroup G} (hP : IsSylowOf 2 P Y)
    (hQ : IsSylowOf 2 Q Y) : Nonempty (↥P ≃* ↥Q) := by
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨e⟩ := exists_mulEquiv_of_isSylowOf hQ P'
  exact ⟨(Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).symm.trans e⟩

theorem isRigidRankOneComp_conj {z : G} {K : Subgroup G} (h : IsRigidRankOneComp z K) (c : G) :
    IsRigidRankOneComp (c * z * c⁻¹) (cmap c K) :=
  ⟨isPRigid_cmap h.1 c, by rw [pRank_cmap]; exact h.2⟩

theorem cfg_swap_data (h44 : II4_44) (hquat : II4_4_quat) (h293 : L293) {z t : G} {S : Subgroup G}
    (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1) :
    ∃ S' : Subgroup G, Cfg G t z S' ∧
      Set.ncard {K : Subgroup G | IsRigidRankOneComp t K} = 1 ∧
      ∀ K : Subgroup G, IsRigidRankOneComp z K → ∀ K' : Subgroup G, IsRigidRankOneComp t K' →
        Nonempty (↥(S ⊓ cSec K) ≃* ↥(S' ⊓ cSec K')) := by
  obtain ⟨S', hC'⟩ := cfg_swap h44 hquat h293 hC
  obtain ⟨c, hc⟩ := isConj_iff.1 hC.conj
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hcard
  have haK : IsRigidRankOneComp z a := by
    have : a ∈ {K : Subgroup G | IsRigidRankOneComp z K} := by rw [ha]; rfl
    exact this
  have hunique : ∀ K, IsRigidRankOneComp z K → K = a := by
    intro K hK
    have : K ∈ {K : Subgroup G | IsRigidRankOneComp z K} := hK
    rw [ha] at this
    exact this
  have hcaK : IsRigidRankOneComp t (cmap c a) := by
    have := isRigidRankOneComp_conj haK c
    rwa [hc] at this
  have hset : {K' : Subgroup G | IsRigidRankOneComp t K'} = {cmap c a} := by
    ext K'
    constructor
    · intro hK'
      have h1 := isRigidRankOneComp_conj hK' c⁻¹
      have e1 : c⁻¹ * t * c⁻¹⁻¹ = z := by rw [← hc]; group
      rw [e1] at h1
      have h2 := hunique _ h1
      show K' = cmap c a
      rw [← h2, cmap_cancel]
    · intro hK'
      rw [Set.mem_singleton_iff.1 hK']
      exact hcaK
  refine ⟨S', hC', ?_, ?_⟩
  · rw [hset]
    exact Set.ncard_singleton _
  · intro K hK K' hK'
    have hKa : K = a := hunique K hK
    have hK'a : K' = cmap c a := by
      have : K' ∈ {K' : Subgroup G | IsRigidRankOneComp t K'} := hK'
      rw [hset] at this
      exact this
    have hcard' : Set.ncard {K : Subgroup G | IsRigidRankOneComp t K} = 1 := by
      rw [hset]
      exact Set.ncard_singleton _
    have hQ := isSylowOf_inf_cSec hC hcard hK
    have hQ' := isSylowOf_inf_cSec hC' hcard' hK'
    subst hKa
    have hQc := isSylowOf_cmap hQ c
    rw [← cSec_cmap_eq, ← hK'a] at hQc
    obtain ⟨e1⟩ := exists_mulEquiv_of_isSylowOf_two hQc hQ'
    exact ⟨(Subgroup.equivMapOfInjective (S ⊓ cSec K) (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).trans e1⟩

end CFSG.GH74.GLS.Bg.Pu5
