module

public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem isSylow2In_inf (hd : Sec19Data p f K z S W) :
    IsSylow2In ((S : Subgroup G) ⊓ K) K := by
  obtain ⟨Q₀, hQ₀S⟩ := hd.sylow
  have hQ := isSylow2In_map_sylow K Q₀
  have heq : (S : Subgroup G) ⊓ K = (Q₀ : Subgroup ↥K).map K.subtype :=
    hQ.eq_of_le (S.isPGroup'.to_le inf_le_left) inf_le_right (le_inf hQ₀S hQ.1)
  rw [heq]
  exact hQ

theorem inf_mem_rSet (hd : Sec19Data p f K z S W) :
    (S : Subgroup G) ⊓ K ∈ RSet (CoreAssembly.conjClass K) :=
  mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) (isSylow2In_inf hd)

theorem isUniqueInvolution_inf (hd : Sec19Data p f K z S W) :
    IsUniqueInvolution ((S : Subgroup G) ⊓ K) z :=
  isUniqueInvolution_of_mem_rSet_of_le hd.tight.toTightBranch (inf_mem_rSet hd) inf_le_right

theorem le_normalizer_inf (hd : Sec19Data p f K z S W) :
    (S : Subgroup G) ≤ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  intro s hs
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
    exact hd.hSz hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxS, hxK⟩
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hxS) (Subgroup.inv_mem _ hs),
      (Subgroup.mem_normalizer_iff.mp hsK x).mp hxK⟩
  · rintro ⟨hxS, hxK⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hsK x).mpr hxK⟩
    have h1 : s⁻¹ * (s * x * s⁻¹) * s ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hxS) hs
    have e : s⁻¹ * (s * x * s⁻¹) * s = x := by group
    rwa [e] at h1

theorem eight_le_card_inf [IsSimpleGroup G] (hd : Sec19Data p f K z S W) :
    8 ≤ Nat.card ↥((S : Subgroup G) ⊓ K) :=
  (hypOmegaMod_of_tightD hd.tight).eight_le_of_mem_RSet hd.tight.branch.odd (inf_mem_rSet hd)

theorem exists_eta (hd : Sec19Data p f K z S W) :
    ∃ η : Set (Subgroup G), ∃ S' : Sylow 2 G, η ∈ etaSet (CoreAssembly.conjClass K) S' ∧
      (∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧ W = ⨆ U ∈ η, U ∧
      ∀ U ∈ η, U ≤ (S : Subgroup G) := by
  obtain ⟨η, ⟨S', hηS', hinv⟩, hWη⟩ := hd.hW
  refine ⟨η, S', hηS', hinv, hWη, fun U hU => ?_⟩
  have hUW : U ≤ W := hWη ▸ le_iSup₂ (f := fun (V : Subgroup G) (_ : V ∈ η) => V) U hU
  exact hUW.trans hd.hWS

omit [Finite G] in
theorem mem_etaG {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) :
    η ∈ etaG (CoreAssembly.conjClass K) :=
  ⟨S', hη, hinv⟩

omit [Finite G] in
theorem conjSub_iSup_le {η : Set (Subgroup G)} {x : G} (h : ∀ U ∈ η, conjSub x U ∈ η) :
    conjSub x (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
  rw [conjSub, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun U hU => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_iSup₂ (f := fun (V : Subgroup G) (_ : V ∈ η) => V) _ (h U hU)

theorem conjSub_iSup_eq {η : Set (Subgroup G)} {x : G} (h : ∀ U ∈ η, conjSub x U ∈ η) :
    conjSub x (⨆ U ∈ η, U) = ⨆ U ∈ η, U :=
  Subgroup.eq_of_le_of_card_ge (conjSub_iSup_le h) (natCard_conjSub _ x).ge

variable [IsSimpleGroup G]

theorem comm_of_mem (hd : Sec19Data p f K z S W) : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, S', hη, hinv, hWη, -⟩ := exists_eta hd
  have h := ((l6_9_proved p f hd.tight.branch.odd hd.tight.branch.five G _
    (hypOmegaMod_of_tightD hd.tight) S').2 η hη hinv).1
  rw [hWη]
  exact h

theorem mem_eta_of_le (hd : Sec19Data p f K z S W) {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) (hWη : W = ⨆ U ∈ η, U)
    {U : Subgroup G} (hU : U ∈ USet (CoreAssembly.conjClass K)) (hUW : U ≤ W) : U ∈ η := by
  have h := ((l6_9_proved p f hd.tight.branch.odd hd.tight.branch.five G _
    (hypOmegaMod_of_tightD hd.tight) S').2 η hη hinv).2
  rw [← h]
  exact ⟨hU, hWη ▸ hUW⟩

theorem inf_mem_eta (hd : Sec19Data p f K z S W) {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) (hWη : W = ⨆ U ∈ η, U)
    (hηS : ∀ U ∈ η, U ≤ (S : Subgroup G)) : K ⊓ W ∈ η := by
  have h8 := eight_le_card_inf hd
  rw [inf_comm] at h8
  have h := l6_11_proved p f hd.tight.branch.odd hd.tight.branch.five G _
    (hypOmegaMod_of_tightD hd.tight) S η (mem_etaG hη hinv) hηS K
    (CoreAssembly.mem_conjClass_self K) (by omega)
  rwa [← hWη] at h

theorem conjSub_mem_eta (hd : Sec19Data p f K z S W) {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) {S₁ : Sylow 2 G}
    (hηS₁ : ∀ U ∈ η, U ≤ (S₁ : Subgroup G)) {R₁ : Subgroup G}
    (hR₁ : R₁ ∈ RSet (CoreAssembly.conjClass K)) (hR₁S₁ : R₁ ≤ (S₁ : Subgroup G)) {x : G}
    (hx : x ∈ R₁) : ∀ U ∈ η, conjSub x U ∈ η :=
  (l6_10_proved p f hd.tight.branch.odd hd.tight.branch.five G _
    (hypOmegaMod_of_tightD hd.tight) S₁ η (mem_etaG hη hinv) hηS₁).1 R₁ hR₁ hR₁S₁ x hx

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
