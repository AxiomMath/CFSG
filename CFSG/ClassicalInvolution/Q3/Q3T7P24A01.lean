module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A00
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubStab
public import CFSG.ClassicalInvolution.AschTight.Sec71Cases
public import CFSG.ClassicalInvolution.AschTight.Sec71Cap2
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A01
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Disconnected.AschTight.Sec71.DData :=
  @CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71.DData

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G]
section Conversions
variable [Finite G] {Ω : Set (Subgroup G)} {K K' J W : Subgroup G}
  {z u t : G}
end Conversions
section Twins
variable {Ω : Set (Subgroup G)} {K L : Subgroup G} {z : G}
end Twins
section Transport
variable [Finite G] {Ω : Set (Subgroup G)} {K L : Subgroup G}

theorem AscStand.of_mem (h : AscStand Ω K) (hL : L ∈ Ω) : AscStand Ω L where
  modU := h.modU
  hyp := h.hyp
  cls := h.cls
  rank := h.rank
  notFour := h.notFour
  below := h.below
  ih := h.ih
  aEmpty := h.aEmpty
  mem := hL
  trans := by
    obtain ⟨g₀, hg₀⟩ := h.trans L hL
    intro J hJ
    obtain ⟨g, hg⟩ := h.trans J hJ
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [conjSub_mul, ← hg₀, conjSub_inv_conjSub, hg]
  gen := h.gen
end Transport
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

@[expose] def L7_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod Ω → Q3CL.ClassicalClause Ω →
      (∀ J ∈ Ω, AEmpty Ω J) →
        ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ u r v t : G,
          Subgroup.zpowers u = R ⊓ W → R = Subgroup.closure {u, r} →
          Subgroup.zpowers v = T ⊓ W → T = Subgroup.closure {v, t} →
            (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} ∧
            ((∃ J ∈ Ω, R ≤ J ∧ T ≤ J) ∨
              (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaNbr Ω J ∧
                ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W) ∨
              (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaStarNbr Ω J ∧
                J' ∉ omegaNbr Ω J ∧
                ∃ v' : G, Subgroup.zpowers v' = Subgroup.zpowers v ∧
                  t⁻¹ * u * t * (u * v')⁻¹ ∈ OCW W ∧ r⁻¹ * v' * r * (v' * u)⁻¹ ∈ OCW W))
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

structure Hyp24 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Prop where
  std : Hyp23 Ω K K' z
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hS4 : MuIsoS4 Ω W
  hZ : W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥
  hWS : W ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hu : u ∈ K ⊔ K' ∧ u ∈ W ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z

@[expose] def C24_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 Ω K K' W S R R' z u → Nat.card ↥R = 8 →
      ¬ (S : Subgroup G) ≤ MGrp Ω W ∨ ConcOrTF4 G
end Asc77

end

section

namespace Disconnected.AschTight.Sec7
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G]
variable {Ω : Set (Subgroup G)}

theorem natCard_eq_two_mul_of_mem_USet [Finite G] (hΩ : Asc77.HypOmegaMod Ω)
    {U K R : Subgroup G} (hU : U ∈ USet Ω) (hK : K ∈ Ω) (hR : IsSylow2In R K) :
    Nat.card R = 2 * Nat.card U := by
  obtain ⟨R', -, J, hJ, hR'J, -, -, hcard, -⟩ := hΩ.exists_data_of_mem_USet hU
  rw [← hcard]
  exact CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq hΩ hK hJ hR
      hR'J
end Disconnected.AschTight.Sec7

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}
section Generators
variable [Finite G]

theorem eq_closure_pair {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod Ω) {W : Subgroup G} (hW : W ∈ WSet
    Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) {u r : G} (hu : Subgroup.zpowers u = R ⊓ W) (hr : r ∈ R) (hrW : r ∉ W) :
    R = Subgroup.closure {u, r} := by
  have hu' : u ∈ R ⊓ W := hu ▸ Subgroup.mem_zpowers u
  apply le_antisymm
  · intro x hx
    by_cases hxW : x ∈ W
    · have : x ∈ Subgroup.zpowers u := hu ▸ ⟨hx, hxW⟩
      exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _))) this
    · have h1 : r⁻¹ * x ∈ Subgroup.zpowers u :=
        hu ▸ ⟨R.mul_mem (R.inv_mem hr) hx, Q3CL.Thompson.D_inv_mul_mem hΩ hW hR hr hx hrW hxW⟩
      have h2 : x = r * (r⁻¹ * x) := by group
      rw [h2]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton r)))
        ((Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _))) h1)
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hu'.1
    · exact hr
end Generators
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77.T7A

theorem not_mem_inf_of_orderOf_four (hΩ : HypOmegaMod Ω) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) {u : G} (hu4 : orderOf u = 4) (huK : u ∈ K)
    (huK' : u ∈ K') : False := by
  have := hΩ.eq_of_le_of_le hK hK' (Asc77.T7A.isPGroup_zpowers_of_orderOf_four hu4)
    (by rw [Nat.card_zpowers, hu4]) (Subgroup.zpowers_le.mpr huK) (Subgroup.zpowers_le.mpr huK')
  exact hne this.symm
end T7A
end Asc77

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G]
namespace DData
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71.DData
variable {Ω : Set (Subgroup G)} {W R K : Subgroup G} {u r z : G}
end DData
variable {Ω : Set (Subgroup G)}

theorem exists_dData [Finite G] (hΩ : Asc77.HypOmegaMod Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {u r : G}
    (hu : Subgroup.zpowers u = R ⊓ W) (hRur : R = Subgroup.closure {u, r}) :
    ∃ K : Subgroup G, ∃ z : G, DData Ω W R K u r z := by
  have habel : Sec7.EtaAbelian Ω := fun η ⟨S, hS, hinv⟩ =>
    ((Asc77.l6_9_proved G Ω hΩ S).2 η hS hinv).1
  have h611 : Sec7.EtaMeets Ω := Asc77.l6_11_proved G Ω hΩ
  obtain ⟨K, hK, hRsyl⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hRK := hRsyl.1
  have hWK := Q3CL.Sec7.le_normalizer_of_mem_DSet hΩ habel h611 hW hR hK hRK
  have hW2 := Sec7.isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, hWη⟩ := id hW
  obtain ⟨S₁, hS₁⟩ := (IsPGroup.to_sup_of_normal_right' (Sec7.isPGroup_of_mem_RSet hR.1) hW2
    hR.2).exists_le_sylow
  have h8 := hΩ.eight_le_of_mem_RSet hR.1
  have hKS₁ : 2 < Nat.card ↥(K ⊓ (S₁ : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hRK (le_sup_left.trans hS₁))
    omega
  have hKWη : K ⊓ W ∈ η := by
    have := h611 S₁ η hη (fun V hV => (hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) V hV
      le_rfl : V ≤ W).trans (le_sup_right.trans hS₁)) K hK hKS₁
    rwa [← hWη] at this
  have hKWU := Sec7.mem_USet_of_mem_etaG hη hKWη
  have hKW2 : IsPGroup 2 ↥(K ⊓ W) := hW2.to_le inf_le_right
  have hRN : R ≤ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) := fun x hx =>
    Sec7.mem_normalizer_inf (Subgroup.le_normalizer (hRK hx)) (hR.2 hx)
  have hKWR : K ⊓ W ≤ R := by
    have := hRsyl.2.2 (R ⊔ (K ⊓ W)) (sup_le hRK inf_le_left)
      (IsPGroup.to_sup_of_normal_right' hRsyl.2.1 hKW2 hRN) le_sup_left
    rw [← this]
    exact le_sup_right
  have hKWeq : K ⊓ W = Subgroup.zpowers u := by
    rw [hu]
    exact le_antisymm (le_inf hKWR inf_le_right) (inf_le_inf_right W hRK)
  have hUU : Subgroup.zpowers u ∈ USet Ω := hKWeq ▸ hKWU
  have hcardU : Nat.card R = 2 * Nat.card ↥(Subgroup.zpowers u) :=
    Sec7.natCard_eq_two_mul_of_mem_USet hΩ hUU hK hRsyl
  have hcard : Nat.card R = 2 * orderOf u := by rw [hcardU, Nat.card_zpowers]
  have hU2 : IsPGroup 2 ↥(Subgroup.zpowers u) := hKWeq ▸ hKW2
  obtain ⟨n, hn⟩ := hU2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have h4 : 4 ≤ orderOf u := by omega
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  have huK : u ∈ K := (show u ∈ K ⊓ W by rw [hKWeq]; exact Subgroup.mem_zpowers u).1
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hn
      omega
    · exact h0
  have hhalf : orderOf u / 2 * 2 = orderOf u := by
    rw [hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ two_pos]
  have hzeq : u ^ (orderOf u / 2) = z := by
    have hsq : u ^ (orderOf u / 2) * u ^ (orderOf u / 2) = 1 := by
      rw [← pow_add, ← two_mul, mul_comm, hhalf, pow_orderOf_eq_one]
    have hne : u ^ (orderOf u / 2) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by omega) (by omega)
    exact (hz.unique _ (K.pow_mem huK _) hsq).resolve_left hne
  have hUR : Subgroup.zpowers u ≤ R := hKWeq ▸ hKWR
  have hzR : IsUniqueInvolution R z :=
    AscL62.isUniqueInvolution_of_le hz hRK (hUR (hzeq ▸ Subgroup.npow_mem_zpowers u _))
  have hQ := hΩ.isQuatSub_of_mem_RSet hR.1
  have hrR : r ∈ R := hRur ▸ Subgroup.subset_closure (by simp)
  have hUc : IsCyclic ↥(Subgroup.zpowers u) := inferInstance
  have hrU : r ∉ Subgroup.zpowers u := by
    intro hr
    have hle : R ≤ Subgroup.zpowers u := by
      rw [hRur, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · exact hr
    obtain ⟨x, hx, y, hy, hxy⟩ := hQ.exists_not_commute
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hx)
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hy)
    exact hxy (Commute.zpow_zpow_self u a b).eq
  have hconj : ∀ c ∈ Subgroup.zpowers u, r * c * r⁻¹ = c⁻¹ := fun c hc =>
    AscL62.conj_eq_inv_of_not_mem hQ hzR hUR hUc hcardU hrR hrU hc
  refine ⟨K, z, ⟨hK, hRsyl, hR, hKWeq, hUR, hUU, hWK, hcard, ⟨n, hn⟩, h4, hz, hzeq, hrR, hrU,
    hconj u (Subgroup.mem_zpowers u), AscL62.sq_eq_of_not_mem hQ hzR hUR hUc hcardU hrR hrU,
    fun x hx => ?_⟩⟩
  by_cases hxU : x ∈ Subgroup.zpowers u
  · exact Or.inl hxU
  · refine Or.inr ⟨(r⁻¹ * x)⁻¹, Subgroup.inv_mem _
      (AscL62.inv_mul_mem_of_index_two hUR hcardU hrR hx hrU hxU), ?_⟩
    have := hconj _ (AscL62.inv_mul_mem_of_index_two hUR hcardU hrR hx hrU hxU)
    calc x = (r * (r⁻¹ * x) * r⁻¹) * r := by group
      _ = (r⁻¹ * x)⁻¹ * r := by rw [this]
namespace DData
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71.DData
variable {W R K : Subgroup G} {u r z : G}

theorem inf_normalizer_le [hcl : Fact (Q3CL.ClassicalClause Ω)] [Finite G] (_hΩ : Asc77.HypOmegaMod
    Ω) (hd : DData Ω W R K u r z) :
    K ⊓ Subgroup.normalizer (W : Set G) ≤ R ⊔ OCW W := by
  have hU2 : IsPGroup 2 ↥(K ⊓ W) := by
    obtain ⟨n, hn⟩ := hd.orderOf_eq
    rw [hd.inf_eq]
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hUc : IsCyclic ↥(K ⊓ W) := by rw [hd.inf_eq]; infer_instance
  have hOH : oddCoreOf (K ⊓ Subgroup.centralizer (W : Set G)) ≤
      K ⊓ Subgroup.normalizer (W : Set G) :=
    (oddCoreOf_le_self _).trans
      (inf_le_inf_left K (Subgroup.centralizer_le_normalizer (W : Set G)))
  have hHO : K ⊓ Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (oddCoreOf (K ⊓ Subgroup.centralizer (W : Set G)) : Set G) :=
    fun h hh => Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer
      (Sec7.mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_inf.mp hh).1)
        (Sec7.normalizer_le_normalizer_centralizer W (Subgroup.mem_inf.mp hh).2))
  have hRH : IsSylow2In R (K ⊓ Subgroup.normalizer (W : Set G)) :=
    ⟨le_inf hd.le hd.memD.2, hd.sylow.2.1, fun V' hV'H hV'2 hRV' =>
      hd.sylow.2.2 V' (hV'H.trans inf_le_left) hV'2 hRV'⟩
  have hle := Sec7.le_sup_of_pow_mem hOH hHO hRH fun h hh =>
    Q3CL.Sec7.exists_pow_two_pow_mem hcl.out hd.memK hd.le_normalizer hUc hU2 hd.u_mem hd.u_sq_ne
      (Subgroup.mem_inf.mp hh).1 (Subgroup.mem_inf.mp hh).2
  exact hle.trans (sup_le_sup_left
    (Q3CL.Sec7.oddCoreOf_inf_centralizer_le_OCW hcl.out hd.memK hd.uinv hd.z_memW) R)

theorem mem_OCW_of_odd [hcl : Fact (Q3CL.ClassicalClause Ω)] [Finite G] (_hΩ : Asc77.HypOmegaMod Ω)
    (hd : DData Ω W R K u r z) {x : G}
    (hxK : x ∈ K) (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ OCW W := by
  have hU2 : IsPGroup 2 ↥(K ⊓ W) := by
    obtain ⟨n, hn⟩ := hd.orderOf_eq
    rw [hd.inf_eq]
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hUc : IsCyclic ↥(K ⊓ W) := by rw [hd.inf_eq]; infer_instance
  have hC := Sec7.mem_centralizer_of_odd hd.le_normalizer hUc hU2 hxK hxW hodd
  have hu2 : IsPGroup 2 ↥(Subgroup.zpowers u) := hU2.to_le (Subgroup.zpowers_le.mpr hd.u_mem)
  exact Q3CL.Sec7.oddCoreOf_inf_centralizer_le_OCW hcl.out hd.memK hd.uinv hd.z_memW
    (Q3CL.Sec7.mem_oddCoreOf_of_odd hcl.out hd.memK hd.u_memK hd.u_memW hu2 hd.u_sq_ne ⟨hxK, hC⟩
        hodd)
end DData
end Disconnected.AschTight.Sec71

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
section Conj
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Conj
section Existence
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7P24.exists_conj_mem_DSet (hΩ : HypOmegaMod Ω)
    (hW : W ∈ WSet Ω) (S : Sylow 2 G) :
    ∃ g : G, ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → conjSub g R ∈ DSet Ω W := by
  obtain ⟨S', hWS'⟩ := exists_sylow_ge_of_mem_WSet hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S S'
  refine ⟨g, fun R hR hRS => ?_⟩
  refine Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS' (RSet.conj hΩ.conjInvariant hR g) ?_
  rw [← hg]
  exact conjSub_mono hRS
end Existence
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.mem_muStab_iff {e : G} (he : e ∈ W) {R
    : Subgroup G} (hR : R ∈ DSet Ω W) {r : G}
    (hr : r ∈ R) {q : ↥(muGroup Ω W)} (hq : (q : NQuot (W ⊔ OCW W)) = piG W r) :
    q ∈ muStab Ω W e ↔ r * e * r⁻¹ = e := by
  constructor
  · rintro ⟨n, hn, hqn, hne⟩
    have h : piG W r = piG W n := hq.symm.trans hqn
    rw [← Q3CL.Thompson.conj_eq_of_piG_eq c.hΩ c.hW (hR.2 hr) hn h he]
    exact hne
  · intro h
    exact ⟨r, hR.2 hr, hq, h⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.comm_sq (ρ σ : Rep Ω W) (hne : ρ.K ≠
    σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ.K) {y z j : G}
    (hy : y ∈ σ.K ⊓ W) (hz : IsUniqueInvolution ρ.K z) (hj : IsUniqueInvolution σ.K j)
    (hy2 : y * y = j) :
    (ρ.r * y * ρ.r⁻¹ * y⁻¹) * (ρ.r * y * ρ.r⁻¹ * y⁻¹) = z := by
  have hc := c.comm_mem ρ σ hne hy
  set cc := ρ.r * y * ρ.r⁻¹ * y⁻¹ with hcc
  have hconj : ρ.r * y * ρ.r⁻¹ = cc * y := by rw [hcc]; group
  have h1 : (ρ.r * y * ρ.r⁻¹) * (ρ.r * y * ρ.r⁻¹) = z * j := by
    calc (ρ.r * y * ρ.r⁻¹) * (ρ.r * y * ρ.r⁻¹) = ρ.r * (y * y) * ρ.r⁻¹ := by group
      _ = ρ.r * j * ρ.r⁻¹ := by rw [hy2]
      _ = z * j := c.conj_involution ρ σ hne hnot hz hj
  have hab : cc * y = y * cc := c.comm_W cc hc.2 y hy.2
  have h2 : (cc * y) * (cc * y) = cc * cc * (y * y) := by
    calc (cc * y) * (cc * y) = cc * (y * cc) * y := by simp only [mul_assoc]
      _ = cc * (cc * y) * y := by rw [← hab]
      _ = cc * cc * (y * y) := by simp only [mul_assoc]
  rw [hconj, h2, hy2] at h1
  exact mul_right_cancel h1

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.stab_dichotomy (ρ ρ₁ ρ₂ : Rep Ω W) {w
    v z z₁ z₂ : G} (hne₁ : ρ.K ≠ ρ₁.K)
    (hne₂ : ρ.K ≠ ρ₂.K) (hnot₁ : ρ₁.K ∉ omegaNbr Ω ρ.K) (hnot₂ : ρ₂.K ∉ omegaNbr Ω ρ.K)
    (hw : w ∈ ρ₁.K ⊓ W) (hv : v ∈ ρ₂.K ⊓ W) (hz : IsUniqueInvolution ρ.K z)
    (hz₁ : IsUniqueInvolution ρ₁.K z₁) (hz₂ : IsUniqueInvolution ρ₂.K z₂) (hw2 : w * w = z₁)
    (hv2 : v * v = z₂) :
    ρ.r * (w * v) * ρ.r⁻¹ = w * v ∨ ρ.r * (w⁻¹ * v) * ρ.r⁻¹ = w⁻¹ * v := by
  have hcw := c.comm_mem ρ ρ₁ hne₁ hw
  have hcv := c.comm_mem ρ ρ₂ hne₂ hv
  have hsw := c.comm_sq ρ ρ₁ hne₁ hnot₁ hw hz hz₁ hw2
  have hsv := c.comm_sq ρ ρ₂ hne₂ hnot₂ hv hz hz₂ hv2
  have ew : ρ.r * w * ρ.r⁻¹ = (ρ.r * w * ρ.r⁻¹ * w⁻¹) * w := by group
  have ev : ρ.r * v * ρ.r⁻¹ = (ρ.r * v * ρ.r⁻¹ * v⁻¹) * v := by group
  have hrw : ρ.r * (w * v) * ρ.r⁻¹ = (ρ.r * w * ρ.r⁻¹) * (ρ.r * v * ρ.r⁻¹) := by group
  have hrw' : ρ.r * (w⁻¹ * v) * ρ.r⁻¹ = (ρ.r * w * ρ.r⁻¹)⁻¹ * (ρ.r * v * ρ.r⁻¹) := by group
  generalize ρ.r * w * ρ.r⁻¹ * w⁻¹ = cw at hcw hsw ew
  generalize ρ.r * v * ρ.r⁻¹ * v⁻¹ = cv at hcv hsv ev
  rw [ew, ev] at hrw hrw'
  rw [hrw, hrw']
  have hab := c.comm_W
  have h1 : cv * cw⁻¹ ∈ ρ.K := ρ.K.mul_mem hcv.1 (ρ.K.inv_mem hcw.1)
  have hcvw : cv * cw = cw * cv := hab cv hcv.2 cw hcw.2
  have hcc : cw⁻¹ * cv = cv * cw⁻¹ := (Commute.inv_left (show Commute cw cv from hcvw.symm)).eq
  have h2 : (cv * cw⁻¹) * (cv * cw⁻¹) = 1 := by
    calc (cv * cw⁻¹) * (cv * cw⁻¹) = cv * (cw⁻¹ * cv) * cw⁻¹ := by simp only [mul_assoc]
      _ = cv * (cv * cw⁻¹) * cw⁻¹ := by rw [hcc]
      _ = (cv * cv) * (cw * cw)⁻¹ := by rw [mul_inv_rev]; simp only [mul_assoc]
      _ = 1 := by rw [hsv, hsw, mul_inv_cancel]
  rcases hz.unique _ h1 h2 with h3 | h3
  ·
    right
    have hcc' : cv = cw := mul_inv_eq_one.mp h3
    rw [hcc']
    calc (cw * w)⁻¹ * (cw * v) = w⁻¹ * cw⁻¹ * (cw * v) := by rw [mul_inv_rev]
      _ = w⁻¹ * v := by group
  ·
    left
    have hcc' : cv * cw = 1 := by
      have e1 : cv = z * cw := by rw [← h3]; group
      rw [e1]
      calc z * cw * cw = z * (cw * cw) := by simp only [mul_assoc]
        _ = z * z := by rw [hsw]
        _ = 1 := hz.sq
    have hwv : w * (cv * v) = cv * (w * v) := by
      have := hab w hw.2 cv hcv.2
      calc w * (cv * v) = (w * cv) * v := by simp only [mul_assoc]
        _ = (cv * w) * v := by rw [this]
        _ = cv * (w * v) := by simp only [mul_assoc]
    calc cw * w * (cv * v) = cw * (w * (cv * v)) := by simp only [mul_assoc]
      _ = cw * (cv * (w * v)) := by rw [hwv]
      _ = (cw * cv) * (w * v) := by simp only [mul_assoc]
      _ = w * v := by rw [← hcvw, hcc', one_mul]
end Ctx
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem conj_mem_MGrp [Finite G] (hΩ : HypOmegaMod Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {x : G} (hx : x ∈ MGrp Ω W) :
    g * x * g⁻¹ ∈ MGrp Ω W := by
  refine Subgroup.iSup_induction (C := fun x => g * x * g⁻¹ ∈ MGrp Ω W)
    (fun R : Subgroup G => ⨆ (_ : R ∈ DSet Ω W), R) hx ?_ (by simp) ?_
  · intro R y hy
    refine Subgroup.iSup_induction (C := fun x => g * x * g⁻¹ ∈ MGrp Ω W)
      (fun _ : R ∈ DSet Ω W => R) hy ?_ (by simp) ?_
    · intro hR z hz
      exact le_MGrp_of_mem_D (Q3CL.Thompson.conjSub_mem_D hΩ hR hg) (conj_mem_conjSub hz)
    · intro x y hx hy
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
  · intro x y hx hy
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy

theorem conj_mem_MGrp_sup [Finite G] (hΩ : HypOmegaMod Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {x : G} (hx : x ∈ MGrp Ω W ⊔ OCW W) :
    g * x * g⁻¹ ∈ MGrp Ω W ⊔ OCW W := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Subgroup.mem_sup_left (conj_mem_MGrp hΩ hg hx)
    · exact Subgroup.mem_sup_right (conj_mem_OCW hg hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

@[expose] noncomputable def conjQ [Finite G] (hΩ : HypOmegaMod Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) : ↥(muGroup Ω W) ≃* ↥(muGroup Ω W) where
  toFun q := ⟨piG W g * q.1 * (piG W g)⁻¹, by
    obtain ⟨m, hm, hqm⟩ := mem_muGroup_iff.mp q.2
    have hmN := MGrp_sup_le_normalizer Ω W hm
    rw [hqm, ← piG_inv hg, ← piG_mul hg hmN, ← piG_mul (Subgroup.mul_mem _ hg hmN)
      (Subgroup.inv_mem _ hg)]
    exact piG_mem_muGroup (conj_mem_MGrp_sup hΩ hg hm)⟩
  invFun q := ⟨(piG W g)⁻¹ * q.1 * piG W g, by
    obtain ⟨m, hm, hqm⟩ := mem_muGroup_iff.mp q.2
    have hmN := MGrp_sup_le_normalizer Ω W hm
    have hg' : g⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hg
    have := piG_mem_muGroup (conj_mem_MGrp_sup hΩ hg' hm)
    rw [piG_mul (Subgroup.mul_mem _ hg' hmN) (Subgroup.inv_mem _ hg'), piG_mul hg' hmN,
      piG_inv hg', piG_inv hg, inv_inv] at this
    rw [hqm]
    exact this⟩
  left_inv q := Subtype.ext (by
    show (piG W g)⁻¹ * (piG W g * q.1 * (piG W g)⁻¹) * piG W g = q.1
    group)
  right_inv q := Subtype.ext (by
    show piG W g * ((piG W g)⁻¹ * q.1 * piG W g) * (piG W g)⁻¹ = q.1
    group)
  map_mul' x y := Subtype.ext (by
    show piG W g * (x.1 * y.1) * (piG W g)⁻¹ = (piG W g * x.1 * (piG W g)⁻¹) *
      (piG W g * y.1 * (piG W g)⁻¹)
    group)

theorem conjQ_apply [Finite G] (hΩ : HypOmegaMod Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (q : ↥(muGroup Ω W)) :
    ((conjQ hΩ hg q : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) = piG W g * q.1 * (piG W g)⁻¹ := rfl
section Fixed
variable [Finite G]
omit [Finite G] in

theorem conjQ_val [Finite G] (hΩ : HypOmegaMod Ω) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    {q : ↥(muGroup Ω W)} {t : G} (ht : t ∈ Subgroup.normalizer (W : Set G))
    (hq : (q : NQuot (W ⊔ OCW W)) = piG W t) :
    (conjQ hΩ hg q : NQuot (W ⊔ OCW W)) = piG W (g * t * g⁻¹) := by
  rw [conjQ_apply, hq, piG_mul (Subgroup.mul_mem _ hg ht) (Subgroup.inv_mem _ hg), piG_mul hg ht,
    piG_inv hg]
omit [Finite G] in

theorem conjQ_mem_muDeltaOf [Finite G] (hΩ : HypOmegaMod Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {C : Set (Subgroup G)}
    (hC : ∀ T ∈ C, conjSub g T ∈ C) (hCD : ∀ T ∈ C, T ∈ DSet Ω W) {q : ↥(muGroup Ω W)}
    (hq : q ∈ muDeltaOf Ω W C) : conjQ hΩ hg q ∈ muDeltaOf Ω W C := by
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := hq
  refine ⟨conjSub g R, hC R hR, g * r * g⁻¹, conj_mem_conjSub hr, ?_, ?_⟩
  · rw [mem_normalizer_iff_of_mem hg]
    exact hrW
  · exact conjQ_val hΩ hg ((hCD R hR).2 hr) hra
omit [Finite G] in

theorem conjQ_mem_muDelta [Finite G] (hΩ : HypOmegaMod Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {q : ↥(muGroup Ω W)}
    (hq : q ∈ muDelta Ω W) : conjQ hΩ hg q ∈ muDelta Ω W :=
  conjQ_mem_muDeltaOf hΩ hg (fun _ hT => Q3CL.Thompson.conjSub_mem_D hΩ hT hg) (fun _ hT => hT) hq
end Fixed
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77.T7A

theorem isSylow2In_sup_of_twin (hΩ : HypOmegaMod Ω) {K K' R R' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hc : Commutes R R') : IsSylow2In (R ⊔ R') (K ⊔ K') := by
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have hprod := card_sup_mul_card_inf hKN
  rw [sup_comm] at hprod
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK' hR'
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hRset
  have h8' : 8 ≤ Nat.card R' := hΩ.eight_le_of_mem_RSet hR'set
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hR.1 hR.2.1 (by omega)
  have hzR' : z ∈ R' := mem_of_isUniqueInvolution_of_isPGroup hz' hR'.1 hR'.2.1 (by omega)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hN0 : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
  have hinfK : (Nat.card ↥(K ⊓ K')).factorization 2 = 1 := by
    have hdvd : 2 ∣ Nat.card ↥(K ⊓ K') := by
      have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (x := z) ⟨hz.mem, hz'.mem⟩
      rwa [hz2] at this
    have h1 : 1 ≤ (Nat.card ↥(K ⊓ K')).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hN0).mp hdvd
    have h2 : padicValNat 2 (Nat.card ↥(K ⊓ K')) ≤ 1 :=
      (hΩ.omega4 K hK K' hK' hne.symm).1
    rw [Nat.factorization_def _ Nat.prime_two] at h1 ⊢
    omega
  have hinfR : Nat.card ↥(R ⊓ R') = 2 := by
    refine le_antisymm ?_ ?_
    · exact hΩ.card_le_two_of_le_inf hK hK' hne.symm (hR.2.1.to_le inf_le_left)
        (inf_le_left.trans hR.1) (inf_le_right.trans hR'.1)
    · have h1 : Subgroup.zpowers z ≤ R ⊓ R' := Subgroup.zpowers_le.mpr ⟨hzR, hzR'⟩
      have := Subgroup.card_le_of_le h1
      rwa [Nat.card_zpowers, hz2] at this
  have hRN : R' ≤ Subgroup.normalizer (R : Set G) := le_normalizer_of_commutes hc
  have hprodR := card_sup_mul_card_inf hRN
  rw [hinfR] at hprodR
  have ha := natCard_eq_pow_of_isSylow2In hR
  have hb := natCard_eq_pow_of_isSylow2In hR'
  have hQ0 : Nat.card ↥(K ⊔ K') ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have hK'0 : Nat.card ↥K' ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥(K ⊔ K')).factorization 2 + 1 =
      (Nat.card ↥K).factorization 2 + (Nat.card ↥K').factorization 2 := by
    have := congrArg (fun n => n.factorization 2) hprod
    simp only [Nat.factorization_mul hQ0 hN0, Nat.factorization_mul hK0 hK'0, Finsupp.add_apply,
      hinfK] at this
    exact this
  have hRR : Nat.card ↥(R ⊔ R') = 2 ^ (Nat.card ↥(K ⊔ K')).factorization 2 := by
    have h1 : Nat.card ↥(R' ⊔ R) = Nat.card ↥(R ⊔ R') := by rw [sup_comm]
    rw [h1, ha, hb] at hprodR
    have h2 : 2 ^ ((Nat.card ↥(K ⊔ K')).factorization 2 + 1) =
        2 ^ (Nat.card ↥K).factorization 2 * 2 ^ (Nat.card ↥K').factorization 2 := by
      rw [hfac, pow_add]
    rw [pow_succ] at h2
    have := hprodR.trans h2.symm
    have h3 : 0 < 2 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right h3 (by linarith)
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hR.2.1.to_sup_of_normal_right' hR'.2.1
    (le_normalizer_of_commutes hc.symm)
  refine ⟨sup_le_sup hR.1 hR'.1, hP2, fun V hVQ hV2 hle => ?_⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hdvd : Nat.card ↥V ∣ Nat.card ↥(K ⊔ K') := Subgroup.card_dvd_of_le hVQ
  rw [hn] at hdvd
  have hnle : n ≤ (Nat.card ↥(K ⊔ K')).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hQ0).mp hdvd
  have hcard : Nat.card ↥V ≤ Nat.card ↥(R ⊔ R') := by
    rw [hn, hRR]
    exact Nat.pow_le_pow_right (by norm_num) hnle
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
end T7A
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem inf_mem_USet_of_le_sylow (hΩ : HypOmegaMod Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) :
    L ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, rfl⟩ := hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans hWS
  have hR8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hL hR)
  have hcard : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) ((Subgroup.card_le_of_le (le_inf hR.1 hRS)).trans' hR8)
  have h611 := l6_11_proved G Ω hΩ S η hη hηS L hL hcard
  obtain ⟨S₀, hηS₀, -⟩ := hη
  exact (hηS₀.1 h611).1

theorem inf_data_of_le_sylow (hΩ : HypOmegaMod Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) :
    IsPGroup 2 ↥(L ⊓ W) ∧ IsCyclic ↥(L ⊓ W) ∧ 4 ≤ Nat.card ↥(L ⊓ W) := by
  have hU := inf_mem_USet_of_le_sylow hΩ hW hWS hL hR hRS
  obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
  exact ⟨hΩ.isPGroup_of_mem_USet hU, hcyc, h4⟩

theorem exists_orderOf_four_mem_inf (hΩ : HypOmegaMod Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) {z : G}
    (hz : IsUniqueInvolution L z) : ∃ x ∈ L ⊓ W, orderOf x = 4 := by
  obtain ⟨h2, -, h4⟩ := inf_data_of_le_sylow hΩ hW hWS hL hR hRS
  exact AscP1Nine3.exists_orderOf_four_of_four_le hz inf_le_left h2 h4
end T7C
end Asc77

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem orderOf_eq_orderOf [Finite G] (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) : orderOf u = orderOf v := by
  have h1 := hd.card
  have h2 := hd'.card
  have h3 := CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq hΩ
      hd.memK hd'.memK hd.sylow hd'.sylow
  omega

theorem DData.j_eq [Finite G] (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) : v ^ (orderOf u / 2) = j := by
  rw [orderOf_eq_orderOf hΩ hd hd']
  exact hd'.z_eq

theorem not_isCyclic_of_mem_RSet [Finite G] (hΩ : Asc77.HypOmegaMod Ω)
    {R : Subgroup G} (hR : R ∈ RSet Ω) : ¬ IsCyclic ↥R := by
  intro hc
  obtain ⟨x, hx, y, hy, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hR).exists_not_commute
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have h1 : (⟨x, hx⟩ : ↥R) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    rw [← ha, ← hb]
    exact (Commute.zpow_zpow_self g a b).eq
  exact hxy (congrArg Subtype.val h1)

theorem comm_le_oddCore_of_centralizes [Finite G] (hΩ : Asc77.HypOmegaMod Ω) {K J T : Subgroup G}
    {z j : G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (hzj : z ≠ j)
    (hT : IsSylow2In T J) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (hT8 : 8 ≤ Nat.card T) (hTc : ¬ IsCyclic ↥T) : ⁅T, K⁆ ≤ oddCoreOf K := by
  have hJt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hz', hj'⟩
    exact hzj ((hz.eq hz').trans (hj'.eq hj))
  have hTs : IsSylow2In T (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hT.1 hTz, hT.2.1, fun V hV hV2 hTV => hT.2.2 V (hV.trans inf_le_left) hV2 hTV⟩
  have hjT : j ∈ T := hj.mem_of_le hT.1 hT.2.1 (by omega)
  have hj2 : Nat.card ↥(Subgroup.zpowers j) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hj.sq) hj.ne_one
  rcases Asc77.l6_2 G Ω hΩ K hK z hz J hJ hJt j hj T hTs hjT with h | h | h | h
  · rw [h.1] at hT8
    omega
  · rw [h.1] at hT8
    omega
  · obtain ⟨-, -, -, hc, -⟩ := h.1
    exact absurd hc hTc
  · exact h.2
end Disconnected.AschTight.Sec71

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77.T7A

theorem exists_commuting_sylow_twin (hΩ : HypOmegaMod Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  obtain ⟨R', hR', hfix⟩ := exists_sylow_normalized hR.2.1 (hR.1.trans hKN)
  have hRn : R ≤ Subgroup.normalizer (R' : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix r hr)
  have h2 : IsPGroup 2 ↥(R ⊔ R') := hR.2.1.to_sup_of_normal_right' hR'.2.1 hRn
  exact ⟨R, R', hR, hR', hΩ.commutes_of_twin_of_isPGroup hK hK' hne.symm hz hz' hR.1 hR'.1 h2⟩

theorem exists_sylow_pair_of_mem (hΩ : HypOmegaMod Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧ u ∈ R ⊔ R' := by
  obtain ⟨R₀, R₀', hR₀, hR₀', hc₀⟩ := exists_commuting_sylow_twin hΩ hK hK' hne hz hz'
  have hQ₀ := isSylow2In_sup_of_twin hΩ hK hK' hne hz hz' hR₀ hR₀' hc₀
  obtain ⟨P, hP, huP⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_mul_self_eq_one hu2 hu1)
    (Subgroup.zpowers_le.mpr hu)
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hP
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have hK'N : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgK' : conjSub g K' = K' :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hK'N Subgroup.le_normalizer) hgQ)
  refine ⟨conjSub g R₀, conjSub g R₀', ?_, ?_, hc₀.conjSub g, ?_⟩
  · have := hR₀.conj g
    rwa [hgK] at this
  · have := hR₀'.conj g
    rwa [hgK'] at this
  · rw [← conjSub_sup_eq, hg]
    exact huP (Subgroup.mem_zpowers u)
end T7A
end Asc77

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem conj_z_eq (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) : t * z * t⁻¹ = z * j ^ k := by
  have := conj_pow_eq (hWc v hd'.u_memW u hd.u_memW) hk (orderOf u / 2)
  rwa [hd.z_eq, hd.j_eq hΩ hd'] at this

theorem comm_z_t (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) : ⁅z, t⁆ = (j ^ k)⁻¹ :=
  comm_eq_of_conj (hWc z hd.z_memW j hd'.z_memW) (conj_z_eq hΩ hd hd' hWc hk)

theorem even_of_comm_mem (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) (hmem : ⁅z, t⁆ ∈ oddCoreOf J) : Even k := by
  rw [comm_z_t hΩ hd hd' hWc hk] at hmem
  by_contra hke
  rw [zpow_eq_self_of_odd hd'.uinv.sq (Int.not_even_iff_odd.mp hke),
    inv_eq_of_mul_eq_one_right hd'.uinv.sq] at hmem
  exact hd'.uinv.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) hmem
    (isPGroup_zpowers_of_mul_self_eq_one hd'.uinv.sq hd'.uinv.ne_one))

theorem even_of_even (hΩ : Asc77.HypOmegaMod Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hie : Even i) : Even k := by
  have hrj : r * j * r⁻¹ = j := by
    have := conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [hd.j_eq hΩ hd', hd.z_eq, zpow_eq_one_of_even hd.uinv.sq hie, mul_one] at this
  have hRj := hd.le_centralizer hWc hd'.z_memW hrj
  have hRJ := comm_le_oddCore_of_centralizes hΩ hd'.memK hd.memK hd'.uinv hd.uinv
    (Ne.symm hzj) hd.sylow hRj (hΩ.eight_le_of_mem_RSet hd.memD.1)
    (not_isCyclic_of_mem_RSet hΩ hd.memD.1)
  have hzR : z ∈ R := hd.uinv.mem_of_le hd.le hd.sylow.2.1
    (by have := hΩ.eight_le_of_mem_RSet hd.memD.1; omega)
  exact even_of_comm_mem hΩ hd hd' hWc hk
    (hRJ (Subgroup.commutator_mem_commutator hzR hd'.r_memK))

theorem case_two_of_twin [hcl : Fact (Q3CL.ClassicalClause Ω)] (hΩ : Asc77.HypOmegaMod Ω) (hd :
    DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hKJ : K ≠ J) (hzj : z = j) :
    J ∈ omegaNbr Ω K ∧ ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W := by
  subst hzj
  have hJK := hΩ.le_normalizer_of_twin hd'.memK hd.memK (Ne.symm hKJ) hd'.uinv hd.uinv
  have hc := hΩ.comm_le_oddCore_of_twin hd.memK hd'.memK hKJ hd.uinv hd'.uinv
  refine ⟨⟨hd'.memK, Ne.symm hKJ, T, hd'.memD.1, hd'.le, hd'.le.trans hJK⟩, fun a ha b hb => ?_⟩
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf J := by
    have := (hc (Subgroup.commutator_mem_commutator (hd.le ha) (hd'.le hb))).2
    rwa [commutatorElement_def] at this
  exact hd'.mem_OCW_of_odd hΩ (oddCoreOf_le_self J hmem) (comm_mem_normalizer hd hd' ha hb)
    (odd_orderOf_of_mem (oddCoreOf_odd_natCard J) hmem)

theorem case_two_of_even [hcl : Fact (Q3CL.ClassicalClause Ω)] (hΩ : Asc77.HypOmegaMod Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hKJ : K ≠ J) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hie : Even i)
    (hke : Even k) : J ∈ omegaNbr Ω K ∧ ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W := by
  have hrj : r * j * r⁻¹ = j := by
    have := conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [hd.j_eq hΩ hd', hd.z_eq, zpow_eq_one_of_even hd.uinv.sq hie, mul_one] at this
  have htz : t * z * t⁻¹ = z := by
    rw [conj_z_eq hΩ hd hd' hWc hk, zpow_eq_one_of_even hd'.uinv.sq hke, mul_one]
  have h8 := hΩ.eight_le_of_mem_RSet hd.memD.1
  have h8' := hΩ.eight_le_of_mem_RSet hd'.memD.1
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hd'.memK hd.memK (Ne.symm hKJ) hd'.uinv hd.le
      hd.sylow.2.1 (by omega) (hd.le_centralizer hWc hd'.z_memW hrj)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hd.memK hd'.memK hKJ hd.uinv hd'.le
      hd'.sylow.2.1 (by omega) (hd'.le_centralizer hWc hd.z_memW htz)
  refine ⟨⟨hd'.memK, Ne.symm hKJ, T, hd'.memD.1, hd'.le, hTK⟩, fun a ha b hb => ?_⟩
  have hK' : a * b * a⁻¹ * b⁻¹ ∈ K := by
    have h1 : b * a⁻¹ * b⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK hb) a⁻¹).mp (K.inv_mem (hd.le ha))
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact K.mul_mem (hd.le ha) h1
  have hJ' : a * b * a⁻¹ * b⁻¹ ∈ J := by
    have h1 : a * b * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hRJ ha) b).mp (hd'.le hb)
    exact J.mul_mem h1 (J.inv_mem (hd'.le hb))
  exact hd.mem_OCW_of_odd hΩ hK' (comm_mem_normalizer hd hd' ha hb)
    (odd_orderOf_of_mem (Disconnected.AschTight.Sec71.odd_natCard_inf hd hd' hzj) ⟨hK', hJ'⟩)

theorem case_three_of_odd (hΩ : Asc77.HypOmegaMod Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hKJ : K ≠ J) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) (hko : Odd k) :
    J ∈ omegaStarNbr Ω K ∧ J ∉ omegaNbr Ω K := by
  refine ⟨⟨hd'.memK, Ne.symm hKJ, Subgroup.zpowers v, hd'.memU, hd'.U_le_K,
    hd'.U_le_W.trans hd.le_normalizer⟩, ?_⟩
  rintro ⟨-, -, T', hT', hT'J, hT'K⟩
  have hT'syl := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hT' hd'.memK hT'J
  have hcz : ∀ x ∈ T', x * z = z * x := fun x hx => by
    have h1 : x * z * x⁻¹ = z :=
      hd.uinv.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hT'K hx))
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [h1]
  have hmem := Q3T7P24.lemma33_involution hΩ hd'.memK hT'syl hd.uinv.sq
    (hd'.le_normalizer hd.z_memW) hcz t hd'.r_memK
  exact (Int.not_even_iff_odd.mpr hko) (even_of_comm_mem hΩ hd hd' hWc hk hmem)
end Disconnected.AschTight.Sec71

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement MatrixGroups
namespace T7B
open CFSG.ClassicalInvolution.Asc77.T7B
section SL2
open Matrix
variable {F : Type*} [Field F]
end SL2
section Lift
variable {G : Type} [Group G]
end Lift
section Member
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_centralizing_conj (hΩ : HypOmegaMod Ω) {L L' : Subgroup G} (hL : L ∈ Ω)
    (hL' : L' ∈ Ω) (hne : L' ≠ L) {z : G} (hzL : IsUniqueInvolution L z)
    (hzL' : IsUniqueInvolution L' z) {x b y ℓ : G} (hx : x ∈ L)
    (hx2 : IsPGroup 2 ↥(Subgroup.zpowers x)) (hℓ : ℓ ∈ L') (hxb : x * b = b * x)
    (hxy : x * y = y * x) (hℓb : ℓ * b * ℓ⁻¹ = y) :
    ∃ ℓ' ∈ L', ℓ' * b * ℓ'⁻¹ = y ∧ ℓ' * x = x * ℓ' := by
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    hΩ.le_normalizer_of_twin hL hL' hne.symm hzL hzL'
  have hcomm := hΩ.comm_le_oddCore_of_twin hL hL' hne.symm hzL hzL'
  set S : Subgroup G := oddCoreOf L' ⊓ Subgroup.centralizer ({b} : Set G) with hS
  set C : Set G := (fun n => ℓ * n) '' (S : Set G) with hC
  have hSodd : Odd (Nat.card ↥S) :=
    (oddCoreOf_odd_natCard L').of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hCodd : Odd (Nat.card ↥C) := by
    have : Nat.card ↥C = Nat.card ↥(S : Set G) :=
      Nat.card_image_of_injective (mul_right_injective ℓ) (S : Set G)
    rw [this]
    exact hSodd
  have hCmem : ∀ c ∈ C, c ∈ L' ∧ c * b * c⁻¹ = y ∧ ℓ⁻¹ * c ∈ oddCoreOf L' := by
    rintro _ ⟨n, hn, rfl⟩
    have hnO : n ∈ oddCoreOf L' := hn.1
    have hnb : n * b = b * n := Subgroup.mem_centralizer_singleton_iff.mp hn.2
    refine ⟨L'.mul_mem hℓ (oddCoreOf_le_self L' hnO), ?_, ?_⟩
    · calc ℓ * n * b * (ℓ * n)⁻¹ = ℓ * (n * b * n⁻¹) * ℓ⁻¹ := by group
        _ = y := by rw [hnb]; simpa using hℓb
    · simpa using hnO
  have hinv : ∀ v ∈ Subgroup.zpowers x, ∀ c ∈ C, v * c * v⁻¹ ∈ C := by
    intro v hv c hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hvL : x ^ j ∈ L := L.zpow_mem hx j
    have hvb : x ^ j * b = b * x ^ j := (Commute.zpow_left (show Commute x b from hxb) j).eq
    have hvy : x ^ j * y = y * x ^ j := (Commute.zpow_left (show Commute x y from hxy) j).eq
    obtain ⟨hcL', hcb, hcO⟩ := hCmem c hc
    set c' := x ^ j * c * (x ^ j)⁻¹ with hc'
    have hc'b : c' * b * c'⁻¹ = y := by
      calc c' * b * c'⁻¹ = x ^ j * (c * ((x ^ j)⁻¹ * b * x ^ j) * c⁻¹) * (x ^ j)⁻¹ := by
            rw [hc']; group
        _ = x ^ j * (c * b * c⁻¹) * (x ^ j)⁻¹ := by
            rw [show (x ^ j)⁻¹ * b * x ^ j = b by rw [mul_assoc, ← hvb]; group]
        _ = y := by rw [hcb, hvy]; group
    have hc'L' : ℓ⁻¹ * c' ∈ oddCoreOf L' := by
      have hvN : x ^ j ∈ Subgroup.normalizer (L' : Set G) := hLN hvL
      have hℓN : ℓ ∈ Subgroup.normalizer (L' : Set G) := Subgroup.le_normalizer hℓ
      have hcomm' : ⁅x ^ j, ℓ⁆ ∈ oddCoreOf L' :=
        (hcomm (Subgroup.commutator_mem_commutator hvL hℓ)).2
      have h1 : ℓ⁻¹ * ⁅x ^ j, ℓ⁆ * ℓ ∈ oddCoreOf L' := by
        have := conj_mem_oddCoreOf_of_mem_normalizer (Subgroup.inv_mem _ hℓN) hcomm'
        simpa using this
      have h2 : x ^ j * (ℓ⁻¹ * c) * (x ^ j)⁻¹ ∈ oddCoreOf L' :=
        conj_mem_oddCoreOf_of_mem_normalizer hvN hcO
      have e : ℓ⁻¹ * c' = (ℓ⁻¹ * ⁅x ^ j, ℓ⁆ * ℓ) * (x ^ j * (ℓ⁻¹ * c) * (x ^ j)⁻¹) := by
        rw [hc']
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (oddCoreOf L').mul_mem h1 h2
    refine ⟨ℓ⁻¹ * c', ⟨hc'L', ?_⟩, by simp⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have : (ℓ⁻¹ * c') * b * (ℓ⁻¹ * c')⁻¹ = b := by
      calc (ℓ⁻¹ * c') * b * (ℓ⁻¹ * c')⁻¹ = ℓ⁻¹ * (c' * b * c'⁻¹) * ℓ := by group
        _ = ℓ⁻¹ * y * ℓ := by rw [hc'b]
        _ = b := by rw [← hℓb]; group
    exact mul_inv_eq_iff_eq_mul.mp this
  obtain ⟨c, hcC, hfix⟩ := Thompson.exists_fixed_mem_of_odd hx2 hinv hCodd
  obtain ⟨hcL', hcb, -⟩ := hCmem c hcC
  refine ⟨c, hcL', hcb, ?_⟩
  exact (mul_inv_eq_iff_eq_mul.mp (hfix x (Subgroup.mem_zpowers x))).symm
end Member
end T7B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7B
open CFSG.ClassicalInvolution.Asc77.T7B
end T7B

@[expose] def C23_1_clique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting Ω K K' z → ∀ W ∈ WSet Ω,
      (Thompson.muDelta Ω W).Nonempty ∧ ∀ d ∈ Thompson.muDelta Ω W,
        (Star3T.cent (Thompson.muDelta Ω W) d).ncard = 2
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Conversions
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z u t u₁ u₂ : G}

theorem Hyp24.data (h : Hyp24 Ω K K' W S R R' z u) : Hyp24Data Ω K K' W S R R' z u where
  hW := h.hW
  hzW := h.hzW
  hS4 := h.hS4
  hZ := h.hZ
  hWS := h.hWS
  hR := h.hR
  hR' := h.hR'
  hu := h.hu
end Conversions
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end T7C
end Asc77

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem cap_case_one [hcl : Fact (Q3CL.ClassicalClause Ω)] (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω
    W R K u r z)
    (hd' : DData Ω W T K v t j) (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} := by
  have hVU : Subgroup.zpowers v = Subgroup.zpowers u := hd'.inf_eq.symm.trans hd.inf_eq
  have hrN : r ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W : Subgroup G) : Set G) := by
    refine mem_normalizer_Y₀ hd.r_normW (mem_normalizer_UV ?_ ?_)
    · rw [hd.conj_u]
      exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
    · have hv : v ∈ Subgroup.zpowers u := hVU ▸ Subgroup.mem_zpowers v
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      rw [← conj_zpow, hd.conj_u]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.inv_mem _
        (Subgroup.mem_zpowers u)) a)
  set F : Set G := {1, r} with hF
  have hFN : ∀ x ∈ F, x ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W : Subgroup G) : Set G) := by
    rintro x (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact hrN
  have hr : ∀ x ∈ F, ∃ y ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W, ∃ x' ∈ F,
      x * r = y * x' := by
    rintro x (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, r, by simp [hF], by group⟩
    · exact ⟨z, U_le_Y₀ u v W hd.z_mem, 1, by simp [hF], by rw [hd.sq_r, mul_one]⟩
  have hRstep := step_of_table (R := R) (T := R) (t := r) (v := u) le_sup_right
    (U_le_Y₀ u v W) (U_le_Y₀ u v W) hFN hd.cover hd.cover hr hr
  have hRX : R ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
    fun x hx => Sec7.normalizer_le_normalizer_OCW W (hd.memD.2 hx)
  refine inf_eq_of_table (F := F) hW2 hWc hd.u_memW hd'.u_memW (hd.U_le_R (Subgroup.mem_zpowers u))
    (hd'.U_le_R (Subgroup.mem_zpowers v)) (by simp [hF]) ?_ ?_
  · intro x hx s hs
    rcases hs with (hsR | hsT) | hsX
    · exact hRstep x hx s (Or.inl (Or.inl hsR))
    · have hsK : s ∈ K ⊓ Subgroup.normalizer (W : Set G) := ⟨hd'.le hsT, hd'.memD.2 hsT⟩
      obtain ⟨ρ, hρ, c, hc, rfl⟩ := exists_mul_of_mem_sup hRX (hd.inf_normalizer_le hΩ hsK)
      obtain ⟨y, hy, x', hx', he⟩ := hRstep x hx ρ (Or.inl (Or.inl hρ))
      refine ⟨y * (x' * c * x'⁻¹), Subgroup.mul_mem _ hy
        (conj_mem_of_mem_normalizer (hFN x' hx') (Subgroup.mem_sup_right hc)), x', hx', ?_⟩
      calc x * (ρ * c) = (x * ρ) * c := by group
        _ = y * x' * c := by rw [he]
        _ = y * (x' * c * x'⁻¹) * x' := by group
    · exact hRstep x hx s (Or.inr hsX)
  · rintro x (rfl | rfl) hu _
    · rfl
    · exact absurd hu (not_comm_of_inv hd.conj_u hd.u_sq_ne)
end Disconnected.AschTight.Sec71

end

end CFSG.ClassicalInvolution.Q3.Q3T8
