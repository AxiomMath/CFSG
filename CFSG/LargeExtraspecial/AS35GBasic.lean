module

public import CFSG.LargeExtraspecial.AS35DFourNine
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

namespace AschTI

variable {G : Type} [Group G] (S : Setting G)

theorem normalizer_QG : normalizer (S.QG : Set G) = S.M := by
  refine le_antisymm (fun x hx => ?_) S.M_le_normalizer_QG
  have hz : x * S.z * x⁻¹ ∈ S.QG := (mem_normalizer_iff.mp hx S.z).mp S.z_mem_QG
  have hc : ∀ y ∈ S.QG, x * S.z * x⁻¹ * y = y * (x * S.z * x⁻¹) := by
    intro y hy
    have hy' : x⁻¹ * y * x ∈ S.QG := by
      have h := (mem_normalizer_iff.mp (inv_mem hx) y).mp hy
      rwa [inv_inv] at h
    have hcomm := S.z_comm_QG hy'
    calc x * S.z * x⁻¹ * y = x * (S.z * (x⁻¹ * y * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * y * x) * S.z) * x⁻¹ := by rw [hcomm]
      _ = y * (x * S.z * x⁻¹) := by group
  rcases S.eq_one_or_z_of_commute hz hc with h | h
  · exact absurd (by simpa using h) S.z_ne_one
  · exact S.mem_M_iff.mpr (by calc x * S.z = x * S.z * x⁻¹ * x := by group
      _ = S.z * x := by rw [h])

theorem QG_inf_Qa_eq_bot (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) : S.QG ⊓ S.Qa g = ⊥ := by
  by_contra h
  exact hgM (hTI g h)

theorem normalizer_Qa (g : G) :
    normalizer (S.Qa g : Set G) = centralizer ({g * S.z * g⁻¹} : Set G) :=
  normalizer_QG (S.conjBy g)

theorem isPGroup_Qa (g : G) : IsPGroup 2 (S.Qa g) := (S.conjBy g).isPGroup_QG

theorem isPGroup_tiP (g : G) : IsPGroup 2 (S.tiP g) := (isPGroup_Qa S g).to_le inf_le_left

theorem t_mem_tiP {g : G} (hgz : g * S.z * g⁻¹ ∈ S.M) : g * S.z * g⁻¹ ∈ S.tiP g :=
  ⟨(S.conjBy g).z_mem_QG, hgz⟩

theorem t_ne_one (g : G) : g * S.z * g⁻¹ ≠ 1 := (S.conjBy g).z_ne_one

theorem z_mem_tiR {g : G} (hgz : g * S.z * g⁻¹ ∈ S.M) : S.z ∈ S.tiR g :=
  ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.mem_M_iff.mp hgz).symm⟩

theorem tiP_ne_bot {g : G} (hgz : g * S.z * g⁻¹ ∈ S.M) : S.tiP g ≠ ⊥ := fun h =>
  t_ne_one S g (by simpa [h] using t_mem_tiP S hgz)

theorem tiP_le_normalizer (g : G) : S.tiP g ≤ normalizer (S.QG : Set G) := by
  rw [normalizer_QG]
  exact inf_le_right

theorem tiP_inf_QG (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G} (hgM : g ∉ S.M) :
    S.tiP g ⊓ S.QG = ⊥ := by
  rw [eq_bot_iff, ← QG_inf_Qa_eq_bot S hTI hgM, inf_comm]
  exact inf_le_inf_left _ inf_le_left

theorem eq_one_of_mem_tiP_of_mem_QG (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) {x : G} (hxP : x ∈ S.tiP g) (hxQ : x ∈ S.QG) : x = 1 := by
  have h : x ∈ S.tiP g ⊓ S.QG := ⟨hxP, hxQ⟩
  rwa [tiP_inf_QG S hTI hgM] at h

theorem commute_of_mem_tiR_of_mem_tiP (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) {r p : G} (hr : r ∈ S.tiR g) (hp : p ∈ S.tiP g) : r * p = p * r := by
  have hQ : p * r * p⁻¹ * r⁻¹ ∈ S.QG :=
    S.QG.mul_mem (S.conj_mem_QG hp.2 hr.1) (S.QG.inv_mem hr.1)
  have hQa : p * r * p⁻¹ * r⁻¹ ∈ S.Qa g := by
    have h1 : r * p⁻¹ * r⁻¹ ∈ S.Qa g :=
      (S.conjBy g).conj_mem_QG hr.2 ((S.Qa g).inv_mem hp.1)
    have h2 := (S.Qa g).mul_mem hp.1 h1
    simpa only [mul_assoc] using h2
  have h1 : p * r * p⁻¹ * r⁻¹ = 1 := by
    have h : p * r * p⁻¹ * r⁻¹ ∈ S.QG ⊓ S.Qa g := ⟨hQ, hQa⟩
    rwa [QG_inf_Qa_eq_bot S hTI hgM] at h
  calc r * p = (p * r * p⁻¹ * r⁻¹)⁻¹ * (p * r) := by group
    _ = p * r := by rw [h1, inv_one, one_mul]

variable [Finite G]

theorem tightlyEmbedded_QG (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) :
    TightlyEmbedded S.QG := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [S.card_QG_eq_card_Q, S.card_Q_eq]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  · have hxM : x⁻¹ ∉ S.M := by
      rw [← normalizer_QG S]
      exact fun h => hx (by simpa using inv_mem h)
    have hconj : rightConjugate S.QG x = S.Qa x⁻¹ := (S.Qa_eq_map x⁻¹).symm
    rw [hconj, QG_inf_Qa_eq_bot S hTI hxM, Subgroup.card_bot]
    exact odd_one

theorem tightlyEmbedded_Qa (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) (g : G) :
    TightlyEmbedded (S.Qa g) := by
  rw [S.Qa_eq_map]
  exact tightlyEmbedded_map_equiv _ (tightlyEmbedded_QG S hTI) (MulAut.conj g)

theorem isSylowOf_self {P : Subgroup G} (hP : IsPGroup 2 P) : IsSylowOf 2 P P :=
  isSylowOf_iff.mpr ⟨le_rfl, hP, by rw [Subgroup.relIndex_self]; norm_num⟩

theorem normalizer_tiP_le (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgz : g * S.z * g⁻¹ ∈ S.M) :
    normalizer (S.tiP g : Set G) ≤ centralizer ({g * S.z * g⁻¹} : Set G) := by
  rw [← normalizer_Qa]
  exact normalizer_two_subgroup_le _ _ (tightlyEmbedded_Qa S hTI g) (isPGroup_tiP S g)
    inf_le_left (tiP_ne_bot S hgz)

theorem centralizer_le_of_mem_tiP (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g p : G}
    (hp : p ∈ S.tiP g) (hp1 : p ≠ 1) :
    centralizer ({p} : Set G) ≤ centralizer ({g * S.z * g⁻¹} : Set G) := by
  have hle : zpowers p ≤ S.Qa g := (zpowers_le).mpr hp.1
  have hne : zpowers p ≠ ⊥ := fun h => hp1 (by
    have := mem_zpowers p
    rwa [h, mem_bot] at this)
  have h := centralizer_two_subgroup_le _ _ (tightlyEmbedded_Qa S hTI g)
    ((isPGroup_Qa S g).to_le hle) hle hne
  rw [normalizer_Qa, zpowers_eq_closure, centralizer_closure] at h
  exact h

theorem QG_inf_normalizer_tiP (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) (hgz : g * S.z * g⁻¹ ∈ S.M) :
    S.QG ⊓ normalizer (S.tiP g : Set G) = S.tiR g := by
  refine le_antisymm (fun x hx => ⟨hx.1, normalizer_tiP_le S hTI hgz hx.2⟩) fun r hr => ?_
  refine ⟨hr.1, mem_normalizer_iff.mpr fun p => ?_⟩
  have hc : ∀ q ∈ S.tiP g, r * q * r⁻¹ = q := fun q hq => by
    rw [commute_of_mem_tiR_of_mem_tiP S hTI hgM hr hq]
    group
  constructor
  · intro hp
    rwa [hc p hp]
  · intro hp
    have h := hc _ hp
    have h' : p = r * p * r⁻¹ := by
      calc p = r⁻¹ * (r * p * r⁻¹) * r := by group
        _ = r⁻¹ * (r * (r * p * r⁻¹) * r⁻¹) * r := by rw [h]
        _ = r * p * r⁻¹ := by group
    rw [h']
    exact hp

theorem card_tiR_eq_card_tiP (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) (hgz : g * S.z * g⁻¹ ∈ S.M) :
    Nat.card (S.tiR g) = Nat.card (S.tiP g) := by
  have hT : IsSylowOf 2 (S.tiP g) (S.Qa g ⊓ normalizer (S.QG : Set G)) := by
    rw [normalizer_QG]
    exact isSylowOf_self (isPGroup_tiP S g)
  have hKJ : Odd (Nat.card (S.QG ⊓ S.Qa g : Subgroup G)) := by
    rw [QG_inf_Qa_eq_bot S hTI hgM, Subgroup.card_bot]
    exact odd_one
  have hfac : (Nat.card S.QG).factorization 2 = (Nat.card (S.Qa g)).factorization 2 := by
    rw [S.card_Qa]
  have h := CFSG.ComponentClassification.Asc76.Lemma22.card_inf_normalizer
    (tightlyEmbedded_QG S hTI) (tightlyEmbedded_Qa S hTI g) hKJ hfac hT (tiP_ne_bot S hgz)
    (isSylowOf_self S.isPGroup_QG) (tiP_le_normalizer S g)
  rwa [QG_inf_normalizer_tiP S hTI hgM hgz] at h

end AschTI

end CFSG.LargeExtraspecial
