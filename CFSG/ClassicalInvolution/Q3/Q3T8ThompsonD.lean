module

public import CFSG.ClassicalInvolution.Q3.Q3T7M04
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
section Conj
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Conj
section Existence
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_conj_mem_DSet_gen (hΩ : HypOmegaMod Ω)
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
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}
section Fixed
variable [Finite G]

theorem exists_member_of_D_same_gen (hΩ : HypOmegaMod Ω)
    (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hTR : T ≤ R ⊔ W ⊔ OCW W) : ∃ K ∈ Ω, R ≤ K ∧ T ≤ K := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨K', hK', hTK'⟩ := exists_isSylow2In_of_mem_RSet hT.1
  suffices hKK : K = K' from ⟨K, hK, hRK.1, hKK ▸ hTK'.1⟩
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hPN : R ⊔ W ≤ Subgroup.normalizer (OCW W : Set G) :=
    sup_le (hR.2.trans (normalizer_le_normalizer_OCW W))
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_OCW W))
  have hP2 : IsPGroup 2 ↥(R ⊔ W) := hRK.2.1.to_sup_of_normal_right' hW2 hR.2
  have hPZ : IsSylow2In (R ⊔ W) (R ⊔ W ⊔ OCW W) := by
    refine ⟨le_sup_left, hP2, fun V hVZ hV2 hPV => ?_⟩
    refine le_antisymm (fun v hv => ?_) hPV
    have hvZ : v ∈ ((R ⊔ W ⊔ OCW W : Subgroup G) : Set G) := hVZ hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (R ⊔ W) (OCW W) hPN] at hvZ
    obtain ⟨p', hp', c, hc, rfl⟩ := hvZ
    have hcV : c ∈ V := by
      have := V.mul_mem (V.inv_mem (hPV hp')) hv
      simpa using this
    have hc1 : c = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc
      (hV2.to_le (Subgroup.zpowers_le.mpr hcV))
    subst hc1
    simpa using hp'
  obtain ⟨V, hVZ, hTV⟩ := IsSylow2In.exists_ge hTK'.2.1 hTR
  obtain ⟨x, hxZ, hxV⟩ := Asc77.Thompson.exists_conj_of_isSylow2In hPZ hVZ
  have hxZ' : x ∈ ((OCW W ⊔ (R ⊔ W) : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hxZ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (OCW W) (R ⊔ W) hPN] at hxZ'
  obtain ⟨c, hc, p', hp', rfl⟩ := hxZ'
  have hV : V = conjSub c (R ⊔ W) := by
    rw [← hxV, conjSub_mul, conjSub_eq_self_of_mem hp']
  have hcN : c ∈ Subgroup.normalizer (W : Set G) := OCW_le_normalizer W hc
  have hT' : conjSub c⁻¹ T ∈ DSet Ω W := Q3CL.Thompson.conjSub_mem_D hΩ hT (Subgroup.inv_mem _ hcN)
  have hT'P : conjSub c⁻¹ T ≤ R ⊔ W := by
    have h1 : conjSub c⁻¹ T ≤ conjSub c⁻¹ (conjSub c (R ⊔ W)) := conjSub_mono (hV ▸ hTV)
    rwa [conjSub_inv_conjSub] at h1
  obtain ⟨S', hS'⟩ := hP2.exists_le_sylow
  have hh4 : 4 ≤ Nat.card T := by
    have := hΩ.eight_le_of_mem_RSet hT.1
    omega
  by_cases hRT : R = conjSub c⁻¹ T
  · have hTeq : T = conjSub c R := by rw [hRT, conjSub_conjSub_inv]
    have hK'' : conjSub c K ∈ Ω := hΩ.conjInvariant c K hK
    have hTcK : T ≤ conjSub c K := hTeq ▸ conjSub_mono hRK.1
    have hKK' : K' = conjSub c K := hΩ.eq_of_le_of_le hK' hK'' hTK'.2.1 hh4 hTK'.1 hTcK
    have hU := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hR hK hRK
    have hUK : K ⊓ W ≤ conjSub c K := fun u hu => by
      have hcu : u * c = c * u := Subgroup.mem_centralizer_iff.mp (OCW_le_centralizer W hc) u hu.2
      have hc' : c * u * c⁻¹ = u := by
        rw [← hcu]
        group
      have := conj_mem_conjSub (n := c) hu.1
      rwa [hc'] at this
    have hKc : K = conjSub c K :=
      hΩ.eq_of_mem_USet hU.2.1 hK hK'' inf_le_left hUK
    exact hKc.trans hKK'.symm
  · exfalso
    have hcomm : Commutes R (conjSub c⁻¹ T) :=
      l6_7_proved G Ω hΩ S' R hR.1 _ hT'.1 (le_sup_left.trans hS') (hT'P.trans hS') hRT
    obtain ⟨t', ht'T, ht'W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hT'
    have ht'P : t' ∈ ((W ⊔ R : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hT'P ht'T
    rw [Subgroup.coe_mul_of_right_le_normalizer_left W R hR.2] at ht'P
    obtain ⟨w, hw, r', hr', rfl⟩ := ht'P
    obtain ⟨K'', hK'', hT''K''⟩ := exists_isSylow2In_of_mem_RSet hT'.1
    have hinfo := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hT' hK'' hT''K''
    have hquat : IsQuatSub (conjSub c⁻¹ T) := hΩ.isQuatSub_of_mem_RSet hT'.1
    obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK''
    have hzT : z ∈ conjSub c⁻¹ T := AscL62.mem_of_uniqueInvolution_of_pGroup hz hT''K''.1
      hT''K''.2.1 (by have := hquat.eight_le; omega)
    have hzT'' : IsUniqueInvolution (conjSub c⁻¹ T) z :=
      AscL62.isUniqueInvolution_of_le hz hT''K''.1 hzT
    obtain ⟨g, hg⟩ := Thompson.exists_zpowers_eq_inf_W hΩ hW hT'
    have hgm : g ∈ conjSub c⁻¹ T ⊓ W := hg ▸ Subgroup.mem_zpowers g
    have hinv := AscL62.conj_eq_inv_of_not_mem hquat hzT'' (inf_le_left : conjSub c⁻¹ T ⊓ W ≤ _)
      hinfo.2.2.1 hinfo.2.2.2.2 ht'T (fun h => ht'W h.2) hgm
    have hr'g : r' * g = g * r' := hcomm r' hr' g hgm.1
    have hwg : w * g = g * w := hWab w hw g hgm.2
    have hcen : w * r' * g * (w * r')⁻¹ = g := by
      calc w * r' * g * (w * r')⁻¹ = w * (r' * g) * r'⁻¹ * w⁻¹ := by group
        _ = w * (g * r') * r'⁻¹ * w⁻¹ := by rw [hr'g]
        _ = w * g * w⁻¹ := by group
        _ = g * w * w⁻¹ := by rw [hwg]
        _ = g := by group
    have hgi : g = g⁻¹ := hcen.symm.trans hinv
    have hg2 : g * g = 1 := by
      calc g * g = g * g⁻¹ := by rw [← hgi]
        _ = 1 := mul_inv_cancel g
    have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    have hcard : Nat.card ↥(conjSub c⁻¹ T ⊓ W) ≤ 2 := by
      rw [← hg, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) hord
    have := hinfo.2.2.2.1
    omega
end Fixed
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T7A
open CFSG.ClassicalInvolution.Asc77.T7A
section Finite
open Equiv
end Finite
end T7A
section Members
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem piG_ne_of_ne_members_gen (hΩ : HypOmegaMod Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R T K J : Subgroup G} (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hKJ : K ≠ J) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (htW : t ∉ W) :
    piG W r ≠ piG W t := by
  intro heq
  have hTR : T ≤ R ⊔ W ⊔ OCW W :=
    le_sup_of_piG_eq hr hR.2 hT.2 fun x hx hxW =>
      (Q3CL.Thompson.D_piG_eq hΩ hW hT hx ht hxW htW).trans heq.symm
  obtain ⟨M, hM, hRM, hTM⟩ := Thompson.exists_member_of_D_same_gen hΩ hW hR hT hTR
  have h8R := hΩ.eight_le_of_mem_RSet hR.1
  have h8T := hΩ.eight_le_of_mem_RSet hT.1
  have h1 : K = M := hΩ.eq_of_le_of_le hK hM hRK.2.1 (by omega) hRK.1 hRM
  have h2 : J = M := hΩ.eq_of_le_of_le hJ hM hTJ.2.1 (by omega) hTJ.1 hTM
  exact hKJ (h1.trans h2.symm)
end Members
section Exclude
end Exclude
end Asc77

end

section Typed

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

namespace Thompson

theorem exists_conj_mem_DSet (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω)
    (hW : W ∈ WSet Ω) (S : Sylow 2 G) :
    ∃ g : G, ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → conjSub g R ∈ DSet Ω W :=
  exists_conj_mem_DSet_gen (Uniform.hypOmegaGenU_of_modU (Uniform.MemberType.cert_sl2 3 1) hΩ)
    hW S

theorem exists_member_of_D_same (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω)
    (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hTR : T ≤ R ⊔ W ⊔ OCW W) : ∃ K ∈ Ω, R ≤ K ∧ T ≤ K :=
  exists_member_of_D_same_gen (Uniform.hypOmegaGenU_of_modU (Uniform.MemberType.cert_sl2 3 1) hΩ)
    hW hR hT hTR

end Thompson

theorem piG_ne_of_ne_members (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω)
    (hW : W ∈ WSet Ω) {R T K J : Subgroup G} (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hKJ : K ≠ J) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (htW : t ∉ W) :
    piG W r ≠ piG W t :=
  piG_ne_of_ne_members_gen (Uniform.hypOmegaGenU_of_modU (Uniform.MemberType.cert_sl2 3 1) hΩ)
    hW hR hT hK hJ hRK hTJ hKJ hr ht htW

end Asc77

end Typed

end CFSG.ClassicalInvolution.Q3.Q3T8
