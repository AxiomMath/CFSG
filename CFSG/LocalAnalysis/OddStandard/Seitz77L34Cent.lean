module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Act
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ComponentClassification CFSG.PSL3Four.Native CFSG.ABGLocalTools
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem l34SylCent_spec
    (h : ∃ P : Subgroup (Equiv.Perm (Fin 42)), P ≤ S ∧ Nat.card P = 64 ∧
      ∀ x ∈ R, (∀ p ∈ P, x * p = p * x) → x ∈ P) :
    ∃ P : Subgroup (Equiv.Perm (Fin 42)), IsSylowOf 2 P S ∧
      ∀ x ∈ R, (∀ p ∈ P, x * p = p * x) → x ∈ P := by
  obtain ⟨P, hPS, hcardP, hc⟩ := h
  refine ⟨P, ?_, hc⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_iff.2 ⟨hPS, IsPGroup.of_card (n := 6) (by rw [hcardP]; norm_num), ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := P) (K := S)
  rw [inf_eq_left.2 hPS, hcardP, PSL3Four.card_S] at h1
  have : P.relIndex S = 315 := by omega
  rw [this]
  norm_num

theorem centralizer_V_le {G : Type*} [Group G] [Finite G]
    {A V : Subgroup G} (hA : commutator ↥A = ⊤) (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S)
    (hV : IsSylowOf 2 V A)
    (hcheck : ∃ P : Subgroup (Equiv.Perm (Fin 42)), P ≤ S ∧ Nat.card P = 64 ∧
      ∀ x ∈ R, (∀ p ∈ P, x * p = p * x) → x ∈ P) :
    normalizer (A : Set G) ⊓ centralizer (V : Set G) ≤
      (V ⊓ centralizer (V : Set G)) ⊔ centralizer (A : Set G) := by
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoL3Four.HypII.l34AutModel hA e
  obtain ⟨P, hPsyl, hPc⟩ := l34SylCent_spec hcheck
  obtain ⟨g, hg⟩ : ∃ g : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 42),
      ∀ n, g n = (ψ n : Equiv.Perm (Fin 42)) := ⟨PSL3Four.R.subtype.comp ψ, fun n => rfl⟩
  have hVA : V ≤ A := hV.le
  have hVN : IsSylowOf 2 (V.subgroupOf (normalizer (A : Set G)))
      (A.subgroupOf (normalizer (A : Set G))) := by
    refine (isSylowOf_map_subtype_iff (normalizer (A : Set G))).1 ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le (hVA.trans le_normalizer),
      Subgroup.map_subgroupOf_eq_of_le le_normalizer]
  have himg := L34.isSylowOf_map hVN g
  have hAimg : (A.subgroupOf (normalizer (A : Set G))).map g = S := by
    ext s
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hg]
      exact hψ.map_mem a ha
    · intro hs
      obtain ⟨a, ha, hax⟩ := hψ.exists_eq ⟨s, S_le_R hs⟩ (Subgroup.mem_subgroupOf.2 hs)
      exact ⟨⟨a, le_normalizer ha⟩, ha, by rw [hg, hax]⟩
  rw [hAimg] at himg
  obtain ⟨s, hsS, hs⟩ := hPsyl.exists_mem_conj himg
  rintro x ⟨hxN, hxV⟩
  have hxV' : ∀ v ∈ V, x * v = v * x := fun v hv =>
    (mem_centralizer_iff.1 hxV v hv).symm
  have hρ : s⁻¹ * (ψ ⟨x, hxN⟩ : Equiv.Perm (Fin 42)) * s ∈ P := by
    refine hPc _ (R.mul_mem (R.mul_mem (R.inv_mem (S_le_R hsS)) (ψ ⟨x, hxN⟩).2) (S_le_R hsS))
      fun p hp => ?_
    have hp' : s * p * s⁻¹ ∈ (V.subgroupOf (normalizer (A : Set G))).map g := by
      rw [hs]
      simpa [mul_assoc] using hp
    obtain ⟨v, hv, hvp⟩ := hp'
    have hcomm : (ψ ⟨x, hxN⟩ : Equiv.Perm (Fin 42)) * (ψ v : Equiv.Perm (Fin 42)) =
        (ψ v : Equiv.Perm (Fin 42)) * ψ ⟨x, hxN⟩ := by
      have h1 : (⟨x, hxN⟩ : ↥(normalizer (A : Set G))) * v = v * ⟨x, hxN⟩ :=
        Subtype.ext (hxV' v hv)
      have h2 := congrArg (fun z => (ψ z : Equiv.Perm (Fin 42))) h1
      simpa [map_mul] using h2
    have hψv' : (ψ v : Equiv.Perm (Fin 42)) = s * p * s⁻¹ := by
      rw [← hg]
      exact hvp
    rw [hψv'] at hcomm
    calc s⁻¹ * ψ ⟨x, hxN⟩ * s * p = s⁻¹ * (ψ ⟨x, hxN⟩ * (s * p * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * p * s⁻¹) * ψ ⟨x, hxN⟩) * s := by rw [hcomm]
      _ = p * (s⁻¹ * ψ ⟨x, hxN⟩ * s) := by group
  have hρ' : (ψ ⟨x, hxN⟩ : Equiv.Perm (Fin 42)) ∈
      (V.subgroupOf (normalizer (A : Set G))).map g := by
    rw [hs]
    simpa using hρ
  obtain ⟨v, hv, hvx⟩ := hρ'
  have hψv : ψ v = ψ ⟨x, hxN⟩ := Subtype.ext (by rw [← hg, hvx])
  have hv' : (v : G) ∈ V := hv
  have hk : ψ (v⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hψv, inv_mul_cancel]
  have hkC : (v : G)⁻¹ * x ∈ centralizer (A : Set G) := (hψ.eq_one_iff (v⁻¹ * ⟨x, hxN⟩)).1 hk
  have hxeq : x = (v : G) * ((v : G)⁻¹ * x) := by group
  have hvc : (v : G) ∈ centralizer (V : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    have h1 : w * ((v : G)⁻¹ * x) = ((v : G)⁻¹ * x) * w :=
      mem_centralizer_iff.1 hkC w (hVA hw)
    have e1 : (v : G) * w * ((v : G)⁻¹ * x) = w * (v : G) * ((v : G)⁻¹ * x) := by
      calc (v : G) * w * ((v : G)⁻¹ * x) = (v : G) * (w * ((v : G)⁻¹ * x)) := by group
        _ = (v : G) * (((v : G)⁻¹ * x) * w) := by rw [h1]
        _ = ((v : G) * ((v : G)⁻¹ * x)) * w := by group
        _ = x * w := by rw [← hxeq]
        _ = w * x := hxV' w hw
        _ = w * ((v : G) * ((v : G)⁻¹ * x)) := by rw [← hxeq]
        _ = w * (v : G) * ((v : G)⁻¹ * x) := by group
    exact (mul_right_cancel e1).symm
  rw [hxeq]
  exact mul_mem_sup ⟨hv', hvc⟩ hkC

end CFSG.OddStandard.Seitz77
