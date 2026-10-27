module

public import CFSG.GH74.GLS.IVK.Lifted.OddFrattini
public import CFSG.GH74.GLS.Bg.Pu5.Statements
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z t : G} {S : Subgroup G}

omit [Finite G] in
theorem rigidProduct_eq_of_ncard_one {K : Subgroup G}
    (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1) (hK : IsRigidRankOneComp z K) :
    rigidProduct z = K := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hcard
  have hKa : K = a := by
    have : K ∈ {K : Subgroup G | IsRigidRankOneComp z K} := hK
    rw [ha] at this
    exact this
  unfold rigidProduct
  rw [ha, sSup_singleton, hKa]

theorem mem_normalizer_of_ncard_one {c : G} {K : Subgroup G}
    (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1) (hK : IsRigidRankOneComp z K)
    (hc : c ∈ centralizer ({z} : Set G)) : c ∈ normalizer (K : Set G) := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hcard
  have hKa : K = a := by
    have : K ∈ {K : Subgroup G | IsRigidRankOneComp z K} := hK
    rw [ha] at this
    exact this
  have h1 : cmap c K ∈ {K : Subgroup G | IsRigidRankOneComp z K} := isRigidRankOneComp_cmap hK hc
  rw [ha] at h1
  have h2 : cmap c K = K := (Set.mem_singleton_iff.1 h1).trans hKa.symm
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

theorem isSylowOf_inf_cSec (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K) : IsSylowOf 2 (S ⊓ cSec K) (cSec K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hC.hz, sq] at this
  have hz1 : z ≠ 1 := fun h => by
    have := hC.hz
    rw [h, orderOf_one] at this
    omega
  have hzK : z ∈ K := by
    have := hC.hzK
    rwa [rigidProduct_eq_of_ncard_one hcard hK] at this
  set C := centralizer ({z} : Set G) with hCdef
  set Y := cSec K with hY
  set Y₀ := Y ⊓ C with hY₀
  have hSC : S ≤ C := hC.sylow.le
  have hCY : C ≤ normalizer (Y₀ : Set G) := by
    intro c hc
    have hcK : c ∈ normalizer (K : Set G) := mem_normalizer_of_ncard_one hcard hK hc
    have hcY : c ∈ normalizer (Y : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact cSec_conj K hcK hy
      · intro hy
        have := cSec_conj K ((normalizer (K : Set G)).inv_mem hcK) hy
        simpa [mul_assoc] using this
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcY, Subgroup.le_normalizer hc⟩
  have hsylY₀ : IsSylowOf 2 (S ⊓ Y₀) Y₀ := hC.sylow.inf_of_le_normalizer inf_le_right hCY
  have hQeq : S ⊓ Y₀ = S ⊓ Y := by
    ext x
    constructor
    · rintro ⟨hxS, hxY, -⟩
      exact ⟨hxS, hxY⟩
    · rintro ⟨hxS, hxY⟩
      exact ⟨hxS, hxY, hSC hxS⟩
  rw [hQeq] at hsylY₀
  rw [isSylowOf_iff]
  refine ⟨inf_le_right, hC.sylow.isPGroup.to_le inf_le_left, ?_⟩
  have h1 : ¬ 2 ∣ (S ⊓ Y).relIndex Y₀ := (isSylowOf_iff.1 hsylY₀).2.2
  have h2 : Odd (Y₀.relIndex Y) := relIndex_centralizer_odd K hz2 hz1 hzK
  have hQY₀ : S ⊓ Y ≤ Y₀ := by
    rw [← hQeq]
    exact inf_le_right
  have h3 : (S ⊓ Y).relIndex Y = (S ⊓ Y).relIndex Y₀ * Y₀.relIndex Y :=
    (Subgroup.relIndex_mul_relIndex (S ⊓ Y) Y₀ Y hQY₀ inf_le_left).symm
  rw [h3]
  have hodd1 : Odd ((S ⊓ Y).relIndex Y₀) := Nat.odd_iff.2 (by omega)
  exact fun hdvd => (Nat.not_even_iff_odd.2 (hodd1.mul h2)) (even_iff_two_dvd.2 hdvd)

theorem exists_mulEquiv_of_isSylowOf {Y Q : Subgroup G} (hQ : IsSylowOf 2 Q Y) (P : Sylow 2 ↥Y) :
    Nonempty (↥P.toSubgroup ≃* ↥Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q', rfl⟩ := hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P Q'
  have h2 : MulAut.conj g • P.toSubgroup = Q'.toSubgroup := by
    rw [← Sylow.coe_subgroup_smul, hg]
  exact ⟨((Subgroup.equivSMul (MulAut.conj g) P.toSubgroup).trans (MulEquiv.subgroupCongr h2)).trans
    (Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective)⟩

theorem l299t_of :
    ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
      Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1 →
        ∀ K : Subgroup G, IsRigidRankOneComp z K →
          ∀ P : Sylow 2 ↥(rigidSectionCentralizer z), Nonempty (↥P.toSubgroup ≃* ↥(S ⊓ cSec K)) := by
  intro G _ _ z t S hC hcard K hK P
  have hY : rigidSectionCentralizer z = cSec K := by
    unfold rigidSectionCentralizer
    rw [rigidProduct_eq_of_ncard_one hcard hK]
    rfl
  have hQ : IsSylowOf 2 (S ⊓ cSec K) (rigidSectionCentralizer z) := by
    rw [hY]
    exact isSylowOf_inf_cSec hC hcard hK
  exact exists_mulEquiv_of_isSylowOf hQ P

end CFSG.GH74.GLS.Bg.Pu5
