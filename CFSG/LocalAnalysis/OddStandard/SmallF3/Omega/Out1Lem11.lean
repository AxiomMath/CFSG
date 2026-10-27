module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma38
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.LiteratureLocal.TightCommuting

private theorem aor_mem_normalizer_subgroupOf_of_mem {G : Type*} [Group G] {S H : Subgroup G}
    {g : ↥S} (hg : (g : G) ∈ normalizer (H : Set G)) :
    g ∈ normalizer (H.subgroupOf S : Set ↥S) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hg (x : G)

private theorem aor_mem_normalizer_subgroupOf_rev {G : Type*} [Group G] {S H : Subgroup G}
    (hHS : H ≤ S) {g : ↥S} (hg : g ∈ normalizer (H.subgroupOf S : Set ↥S)) :
    (g : G) ∈ normalizer (H : Set G) := by
  have hginv : g⁻¹ ∈ normalizer (H.subgroupOf S : Set ↥S) := inv_mem hg
  rw [Subgroup.mem_normalizer_iff] at hg hginv ⊢
  intro x
  constructor
  · intro hx
    have h := (hg ⟨x, hHS hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
    rw [Subgroup.mem_subgroupOf] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  · intro hx
    have hmS : (g : G) * x * (g : G)⁻¹ ∈ S := hHS hx
    have hmH : (⟨(g : G) * x * (g : G)⁻¹, hmS⟩ : ↥S) ∈ H.subgroupOf S := hx
    have h := (hginv ⟨(g : G) * x * (g : G)⁻¹, hmS⟩).mp hmH
    rw [Subgroup.mem_subgroupOf] at h
    have hxeq : ((g⁻¹ * ⟨(g : G) * x * (g : G)⁻¹, hmS⟩ * (g⁻¹)⁻¹ : ↥S) : G) = x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [hxeq] at h

theorem aor_commutes_of_ti {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) (K : Subgroup T)
    (hK : ¬ CFSG.Open.IsElemAbelian 2 K)
    (hTI : ∀ g : T, g ∉ normalizer (K : Set T) → K ⊓ rightConjugate K g = ⊥)
    {g : T} (hg : g ∉ normalizer (K : Set T)) : Commutes K (rightConjugate K g) := by
  have hK2 : IsPGroup 2 K := hT.to_subgroup K
  have hKne : K ≠ ⊥ := fun hbot =>
    hK (by rw [hbot]; exact CFSG.Open.isElemAbelian_bot 2)
  have heven : Even (Nat.card K) := by
    rcases hK2.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.eq_bot_of_card_eq K h1) hKne
    · exact even_iff_two_dvd.mpr h2
  have htight : TightlyEmbedded K :=
    ⟨heven, fun x hx => by
      rw [hTI x hx, Subgroup.card_bot]
      exact odd_one⟩
  have hs : Setup K ⊤ K ⊤ :=
    { tight := htight
      le_inf := le_inf le_top le_rfl
      sylow := by
        intro R hR _ hKR
        exact le_antisymm (hR.trans inf_le_right) hKR
      pGroup := hK2
      ne_bot := hKne
      S_le := le_rfl
      S_pGroup := hT.to_subgroup ⊤
      le_S := le_top }
  have hΦ : frattini K ≠ ⊥ := fun h =>
    hK (CFSG.ComponentClassification.Asc76X.isElemAbelian_of_frattini_eq_bot hK2 h)
  have hne : K ≠ rightConjugate K g := fun h =>
    hg ((rightConjugate_eq_self_iff K g).mp h.symm)
  exact hs.commutes_conjugatesIn hΦ K ⟨1, mem_top 1, (rightConjugate_one K).symm, le_top⟩
    (rightConjugate K g) ⟨g, mem_top g, rfl, le_top⟩ hne

theorem asc82Lemma11_holds : ∀ (G : Type) [Group G] [Finite G] (T X : Subgroup G), IsPGroup 2 T →
    X ≤ T → ¬ CFSG.Open.IsElemAbelian 2 X →
    (∀ t ∈ T, t ∉ normalizer (X : Set G) → X ⊓ CFSG.conjugate X t = ⊥) →
      ∀ t ∈ T, t ∉ normalizer (X : Set G) →
        X ⊓ CFSG.conjugate X t = ⊥ ∧ ∀ a ∈ X, ∀ b ∈ CFSG.conjugate X t, a * b = b * a := by
  intro G _ _ T X hT hXT hnel hTI t ht htn
  have hK' : ¬ CFSG.Open.IsElemAbelian 2 (X.subgroupOf T) := fun h =>
    hnel (by
      have hmap : CFSG.Open.IsElemAbelian 2 ((X.subgroupOf T).map T.subtype) :=
        CFSG.Open.IsElemAbelian.map h T.subtype
      rwa [Subgroup.map_subgroupOf_eq_of_le hXT] at hmap)
  have hTI' : ∀ g' : ↥T, g' ∉ normalizer (X.subgroupOf T : Set ↥T) →
      X.subgroupOf T ⊓ rightConjugate (X.subgroupOf T) g' = ⊥ := by
    intro g' hg'
    have hgG : (g' : G) ∉ normalizer (X : Set G) :=
      fun h => hg' (aor_mem_normalizer_subgroupOf_of_mem h)
    have hinf : X ⊓ rightConjugate X (g' : G) = ⊥ := hTI (g' : G) g'.2 hgG
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxK : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx.1
    have hxR : (x : G) ∈ rightConjugate X (g' : G) := by
      rw [mem_rightConjugate_iff]
      have h : g' * x * g'⁻¹ ∈ X.subgroupOf T :=
        (mem_rightConjugate_iff (X.subgroupOf T) g' x).mp hx.2
      rw [Subgroup.mem_subgroupOf] at h
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hmem : (x : G) ∈ X ⊓ rightConjugate X (g' : G) := ⟨hxK, hxR⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hg' : (⟨t, ht⟩ : ↥T) ∉ normalizer (X.subgroupOf T : Set ↥T) :=
    fun h => htn (aor_mem_normalizer_subgroupOf_rev hXT h)
  have hcomm := aor_commutes_of_ti hT (X.subgroupOf T) hK' hTI' hg'
  refine ⟨hTI t ht htn, ?_⟩
  intro a ha b hb
  have hbX : t * b * t⁻¹ ∈ X := (mem_rightConjugate_iff X t b).mp hb
  have hbT : b ∈ T := by
    have h1 : t * b * t⁻¹ ∈ T := hXT hbX
    have h2 : b = t⁻¹ * (t * b * t⁻¹) * t := by group
    rw [h2]
    exact mul_mem (mul_mem (T.inv_mem ht) h1) ht
  let a' : X.subgroupOf T := ⟨⟨a, hXT ha⟩, ha⟩
  let b' : rightConjugate (X.subgroupOf T) ⟨t, ht⟩ :=
    ⟨⟨b, hbT⟩, by
      rw [mem_rightConjugate_iff]
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hbX⟩
  have h := congrArg (fun z : ↥T => (z : G))
    (hcomm (a' : ↥T) a'.2 (b' : ↥T) b'.2)
  simpa [a', b'] using h

end CFSG.OddStandard.SmallF3.Omega
