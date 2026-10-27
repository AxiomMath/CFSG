module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Abs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools

namespace YCfg

theorem sylCfg_yAct {G : Type} [Group G] [Finite G] {S V J : Subgroup G}
    (hS2 : IsPGroup 2 ↥S) (hV3 : IsPGroup 3 ↥V) (hSV : S ≤ normalizer (V : Set G))
    (hVJ : V ≤ normalizer (J : Set G)) [Group.IsPerfect ↥J]
    (hnc : ¬ V ≤ centralizer (J : Set G)) (hsyl : IsSylowOf 2 (S ⊓ J) J) :
    SylCfg (↥J ⧸ center ↥J) ((S.subgroupOf (normalizer (J : Set G))).map (yAct J))
      ((V.subgroupOf (normalizer (J : Set G))).map (yAct J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hS2.comap_subtype.map _
  · exact hV3.comap_subtype.map _
  · intro h
    apply hnc
    intro v hv
    have hvN : v ∈ normalizer (J : Set G) := hVJ hv
    have h1 : yAct J ⟨v, hvN⟩ ∈ (V.subgroupOf (normalizer (J : Set G))).map (yAct J) :=
      ⟨⟨v, hvN⟩, hv, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (yAct_eq_one_iff J ⟨v, hvN⟩).mp h1
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := ht
    have hsV : ∀ x : G, (x ∈ V ↔ (s : G) * x * (s : G)⁻¹ ∈ V) := fun x =>
      mem_normalizer_iff.mp (hSV hs) x
    rw [mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨s * v * s⁻¹, ?_, by simp⟩
      show ((s * v * s⁻¹ : ↥(normalizer (J : Set G))) : G) ∈ V
      simpa using (hsV v).mp hv
    · rintro ⟨v', hv', hv'eq⟩
      refine ⟨s⁻¹ * v' * s, ?_, ?_⟩
      · show ((s⁻¹ * v' * s : ↥(normalizer (J : Set G))) : G) ∈ V
        apply (hsV _).mpr
        show (s : G) * ((s : G)⁻¹ * (v' : G) * (s : G)) * (s : G)⁻¹ ∈ V
        have h1 : (s : G) * ((s : G)⁻¹ * (v' : G) * (s : G)) * (s : G)⁻¹ = (v' : G) := by group
        rw [h1]
        exact hv'
      · rw [map_mul, map_mul, map_inv, hv'eq]
        group
  · obtain ⟨R, hR⟩ := hsyl.exists_sylow_eq_subgroupOf
    refine ⟨(R : Subgroup ↥J).map (innHom ↥J), ?_, (isSylowOf_map_innHom R).le,
      isSylowOf_map_innHom R⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ S ⊓ J := by
      have : x ∈ (S ⊓ J).subgroupOf J := hR ▸ hx
      exact this
    exact ⟨⟨(x : G), le_normalizer x.2⟩, hx'.1, yAct_of_mem J x⟩

theorem mem_normalizer_of_odd_order {A : Type*} [Group A] [Finite A]
    (hc : ∀ K₁ K₂ K₃ : Subgroup A, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃) {J : Subgroup A} (hJ : IsComponent J) {v : A}
    (hv : Odd (orderOf v)) : v ∈ normalizer (J : Set A) := by
  let cj : A → Subgroup A → Subgroup A := fun g K => K.map (MulAut.conj g).toMonoidHom
  have cj_mul : ∀ g h K, cj (g * h) K = cj g (cj h K) := by
    intro g h K
    simp only [cj, Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have cj_inj : ∀ g, Function.Injective (cj g) := fun g =>
    Subgroup.map_injective (MulAut.conj g).injective
  have key : ∀ g : A, g ∈ normalizer (J : Set A) ↔ cj g J = J := by
    intro g
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  have hcomp : ∀ (g : A) (K : Subgroup A), IsComponent K → IsComponent (cj g K) :=
    fun g K hK => CFSG.LocalCores.isComponent_map_mulEquiv _ hK
  have hJ1 := hcomp v J hJ
  have hJ2 := hcomp v (cj v J) hJ1
  rcases hc J (cj v J) (cj v (cj v J)) hJ hJ1 hJ2 with h | h | h
  · exact (key v).mpr h.symm
  · have h2 : cj (v * v) J = J := by rw [cj_mul]; exact h.symm
    have h3 : v * v ∈ normalizer (J : Set A) := (key _).mpr h2
    obtain ⟨m, hm⟩ := hv
    have h4 : v = (v * v) ^ (m + 1) := by
      rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf v + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [h4]
    exact Subgroup.pow_mem _ h3 _
  · exact (key v).mpr ((cj_inj v h).symm)

end YCfg

theorem AFrame.v_normalizes_component {A : Type} [Group A] [Finite A] {zb : A}
    {Sb Vb J : Subgroup A} (hfr : AFrame A zb Sb Vb)
    (hcomps : ∀ K₁ K₂ K₃ : Subgroup A, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃) (hJ : IsComponent J) : Vb ≤ normalizer (J : Set A) := by
  intro v hv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hfr.v3 ⟨v, hv⟩
  have hodd : Odd (orderOf v) := by
    rw [← Subgroup.orderOf_mk v hv, hk]
    exact Odd.pow (by decide)
  exact YCfg.mem_normalizer_of_odd_order hcomps hJ hodd

theorem AFrame.sylCfg_of_comps {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}
    (hfr : AFrame A zb Sb Vb)
    (hcomps : ∀ K₁ K₂ K₃ : Subgroup A, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃) (hJ : IsComponent J)
    (hnc : ¬ Vb ≤ centralizer (J : Set A)) :
    IsSimpleGroup (↥J ⧸ center ↥J) ∧ SylCfgOf (↥J ⧸ center ↥J) := by
  have : Group.IsPerfect ↥J := hJ.1.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowOf 2 (Sb ⊓ J) J := YCfg.isSylowOf_inf_isSubnormal_top hfr.sylow hJ.2
  exact ⟨hJ.1.2.1, _, _, YCfg.sylCfg_yAct hfr.sylow.isPGroup hfr.v3 hfr.v_norm
    (hfr.v_normalizes_component hcomps hJ) hnc hsyl⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
