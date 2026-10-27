module

public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

variable {G : Type} [Group G]

structure ClassicalClause (Ω : Set (Subgroup G)) : Prop where
  subnormal : ∀ K ∈ Ω, ∃ z : G, z ∈ K ∧ orderOf z = 2 ∧
    IsSubnormal K (Subgroup.centralizer ({z} : Set G))
  commOdd : ∀ J ∈ Ω, ∀ u a b : G, u ∈ J → IsPGroup 2 (Subgroup.zpowers u) → u * u ≠ 1 →
    a ∈ J → b ∈ J → a * u = u * a → b * u = u * b → a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf J

structure PartIHypG (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  cls : ClassicalClause Ω
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J

variable [Finite G]

theorem commutator_mem_oddCoreOf_of_chart {F : Type} [Field F] {J : Subgroup G}
    (φ : ↥J →* SL(2, F)) (hφk : ∀ x : ↥J, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥J)
    {u a b : G} (hu : u ∈ J) (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (huu : u * u ≠ 1)
    (ha : a ∈ J) (hb : b ∈ J) (hau : a * u = u * a) (hbu : b * u = u * b) :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf J := by
  have hx : φ ⟨u, hu⟩ * φ ⟨u, hu⟩ ≠ 1 := by
    intro h
    rw [← map_mul, hφk] at h
    apply huu
    have h2 : IsPGroup 2 (Subgroup.zpowers (u * u)) :=
      hu2.to_le (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_zpowers u)
        (Subgroup.mem_zpowers u)))
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J)
      (mem_oddCoreOf_iff.mpr ⟨J.mul_mem hu hu, h⟩) h2
  have hya : φ ⟨a, ha⟩ * φ ⟨u, hu⟩ = φ ⟨u, hu⟩ * φ ⟨a, ha⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hau)
  have hyb : φ ⟨b, hb⟩ * φ ⟨u, hu⟩ = φ ⟨u, hu⟩ * φ ⟨b, hb⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hbu)
  have hc := Sec7.sl2_commute_of_commute hx hya hyb
  have hc' : φ (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥J)⁻¹ * (⟨b, hb⟩ : ↥J)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  exact mem_oddCoreOf_iff.mpr ⟨_, (hφk _).mp hc'⟩

theorem classicalClause_of_modU {p f : ℕ} {Ω : Set (Subgroup G)}
    (h : HypOmegaModU (.sl2 p f) Ω) : ClassicalClause Ω where
  subnormal K hK := by
    obtain ⟨z, hz⟩ := h.classical K hK
    exact ⟨z, hz.mem, hz.orderOf_eq_two, hz.subnormal⟩
  commOdd J hJ u a b hu hu2 huu ha hb hau hbu := by
    obtain ⟨z, hz⟩ := h.classical J hJ
    obtain ⟨hp, ⟨e⟩⟩ := hz.witness
    refine commutator_mem_oddCoreOf_of_chart (e.toMonoidHom.comp (QuotientGroup.mk' _))
      (fun x => ?_) hu hu2 huu ha hb hau hbu
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e, e.injective.eq_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem partIHypG_of_modU {p f : ℕ} {Ω : Set (Subgroup G)} (h : HypOmegaModU (.sl2 p f) Ω)
    (hA : ∀ J ∈ Ω, AEmpty Ω J) : PartIHypG Ω :=
  ⟨hypOmegaGenU_of_modU (MemberType.cert_sl2 p f) h, classicalClause_of_modU h, hA⟩

omit [Finite G] in
theorem ClassicalClause.isSubnormal_of_uniqueInvolution {Ω : Set (Subgroup G)}
    (hcl : ClassicalClause Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨z', hz'K, hz'o, hz'⟩ := hcl.subnormal K hK
  have hz'z : z' = z := by
    have hsq : z' * z' = 1 := by
      have := pow_orderOf_eq_one z'
      rwa [hz'o, pow_two] at this
    rcases hz.unique z' hz'K hsq with h | h
    · exfalso
      rw [h, orderOf_one] at hz'o
      omega
    · exact h
  rw [hz'z] at hz'
  exact hz'

end CFSG.ClassicalInvolution.Q3.Q3CL
