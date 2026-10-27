module

public import CFSG.GH74.Uniqueness.SU.SU10Setup
public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU8

variable {G : Type} [Group G] [Finite G] {Hh : Subgroup G}

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 Hh)

omit [Finite G] in
theorem map_conj_eq_of_normal {X : Type} [Group X] (N : Subgroup X) [N.Normal] (g : X) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (inferInstance : N.Normal).conj_mem k hk g
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    swap
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
    have := (inferInstance : N.Normal).conj_mem x hx g⁻¹
    simpa using this

theorem exists_lift_component {K₁ : Subgroup (Hbar Hh)} (hK : IsComponent K₁) (hn : K₁.Normal) :
    ∃ L : Subgroup G, GLS.IsPCompIn 2 Hh L ∧ Hh ≤ normalizer (L : Set G) ∧
      hbarImage Hh L = K₁ := by
  obtain ⟨L', hL', hLK⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hK
  have hker : ¬ 2 ∣ Nat.card (π).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp coprime_card_pPrimeCore
  obtain ⟨hbij, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (π) (QuotientGroup.mk'_surjective _) hker
  have hnorm : ∀ h : ↥Hh, L'.map (MulAut.conj h).toMonoidHom = L' := by
    intro h
    have h1 : CFSG.IsPComponent 2 (L'.map (MulAut.conj h).toMonoidHom) :=
      CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj h) hL'
    refine hbij.injOn h1 hL' ?_
    have hcomp : (π).comp (MulAut.conj h).toMonoidHom =
        (MulAut.conj (π h)).toMonoidHom.comp (π) := by
      ext x
      simp [MulAut.conj_apply]
    show (L'.map (MulAut.conj h).toMonoidHom).map π = L'.map π
    rw [hLK, Subgroup.map_map, hcomp, ← Subgroup.map_map, hLK]
    exact map_conj_eq_of_normal K₁ (π h)
  have hL'n : L'.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ ∈ L'.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
    rwa [hnorm g] at this⟩
  have hsub : (L'.map Hh.subtype).subgroupOf Hh = L' :=
    Subgroup.comap_map_eq_self_of_injective Hh.subtype_injective L'
  refine ⟨L'.map Hh.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_, ?_⟩
  · rw [hsub]
    exact hL'
  · have hn : ((L'.map Hh.subtype).subgroupOf Hh).Normal := by
      rw [hsub]
      exact hL'n
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le L')).mp hn
  · unfold hbarImage
    rw [hsub]
    exact hLK

omit [Finite G] in
theorem mem_L_sup_centralizerBar {L : Subgroup G} {K₁ : Subgroup (Hbar Hh)}
    (hL : hbarImage Hh L = K₁) {x : G} (hx : x ∈ Hh)
    (hxK : π ⟨x, hx⟩ ∈ K₁ ⊔ centralizer (K₁ : Set (Hbar Hh))) :
    x ∈ L ⊔ centralizerBar Hh L := by
  have hcomm : ∀ a ∈ K₁, ∀ b ∈ centralizer (K₁ : Set (Hbar Hh)), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha
  obtain ⟨k, hk, c, hc, hkc⟩ := SU1.mem_sup_of_commute hcomm hxK
  have hk' : k ∈ hbarImage Hh L := hL ▸ hk
  obtain ⟨l', hl', hl'k⟩ := Subgroup.mem_map.mp hk'
  have hlL : (l' : G) ∈ L := (Subgroup.mem_subgroupOf).mp hl'
  have himg : π (l'⁻¹ * ⟨x, hx⟩) = c := by
    rw [map_mul, map_inv, hl'k, ← hkc]
    group
  have hcb : ((l'⁻¹ * ⟨x, hx⟩ : ↥Hh) : G) ∈ centralizerBar Hh L := by
    refine ⟨l'⁻¹ * ⟨x, hx⟩, ?_, rfl⟩
    show π (l'⁻¹ * ⟨x, hx⟩) ∈ centralizer ((hbarImage Hh L : Subgroup (Hbar Hh)) : Set (Hbar Hh))
    rw [himg, hL]
    exact hc
  have : x = (l' : G) * ((l'⁻¹ * ⟨x, hx⟩ : ↥Hh) : G) := by simp
  rw [this]
  exact (L ⊔ centralizerBar Hh L).mul_mem (Subgroup.mem_sup_left hlL)
    (Subgroup.mem_sup_right hcb)

end CFSG.GH74.Uniqueness.SU.SU10
