module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23L63Frame
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueIndex
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUnique

public section

namespace CFSG.EvenSporadicStandard.Solomon78.F23L63

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ CFSG.EvenSporadicStandard.TwoFi22.DS81

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

@[expose] def IsE {G : Type} [Group G] (B : Subgroup G) : Prop :=
  (∀ b ∈ B, b ^ 2 = 1) ∧ Nat.card B = 2 ^ 11

@[expose] def conjSub {G : Type} [Group G] (g : G) (B : Subgroup G) : Subgroup G :=
  B.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub_iff {G : Type} [Group G] {g x : G} {B : Subgroup G} :
    x ∈ conjSub g B ↔ g⁻¹ * x * g ∈ B := by
  unfold conjSub
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conjSub_conjSub {G : Type} [Group G] (g h : G) (B : Subgroup G) :
    conjSub g (conjSub h B) = conjSub (g * h) B := by
  ext x
  rw [mem_conjSub_iff, mem_conjSub_iff, mem_conjSub_iff, mul_inv_rev]
  simp only [mul_assoc]

theorem conjSub_one {G : Type} [Group G] (B : Subgroup G) : conjSub 1 B = B := by
  ext x
  simp [mem_conjSub_iff]

theorem conjSub_inv_conjSub {G : Type} [Group G] (g : G) (B : Subgroup G) :
    conjSub g⁻¹ (conjSub g B) = B := by
  rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv {G : Type} [Group G] (g : G) (B : Subgroup G) :
    conjSub g (conjSub g⁻¹ B) = B := by
  rw [conjSub_conjSub, mul_inv_cancel, conjSub_one]

theorem card_conjSub {G : Type} [Group G] (g : G) (B : Subgroup G) :
    Nat.card (conjSub g B) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem IsE.conjSub {G : Type} [Group G] {B : Subgroup G} (h : IsE B) (g : G) :
    IsE (conjSub g B) := by
  refine ⟨fun b hb => ?_, by rw [card_conjSub]; exact h.2⟩
  have h1 := h.1 _ (mem_conjSub_iff.1 hb)
  rw [pow_two] at h1 ⊢
  calc b * b = g * ((g⁻¹ * b * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem mem_sylow_smul_iff {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {g x : G} {P : Sylow p G} :
    x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul]
  exact mem_conjSub_iff

section Sylow

@[expose] noncomputable def frameT : Subgroup J := Classical.choose exists_frameT

theorem frameT_spec : frameT ≤ centralizer {d} ∧ Nat.card (frameT : Subgroup J) = 2 ^ 18 ∧
    ∀ x ∈ D23, x ∈ (frameT : Subgroup J) ↔ ∃ i, fjHom (eVec i) = x :=
  Classical.choose_spec exists_frameT

theorem isPGroup_frameT : IsPGroup 2 (frameT : Subgroup J) :=
  IsPGroup.of_card (n := 18) frameT_spec.2.1

theorem not_dvd_index_frameT : ¬ 2 ∣ (frameT : Subgroup J).index := by
  have h := Subgroup.card_mul_index (frameT : Subgroup J)
  rw [frameT_spec.2.1, card_J] at h
  norm_num at h
  omega

@[expose] noncomputable def frameSylow : Sylow 2 J := isPGroup_frameT.toSylow not_dvd_index_frameT

end Sylow

section Unique

theorem eq_frameE_of_le_frameT {B : Subgroup J} (hB : IsE B) (hle : B ≤ frameT) :
    B = frameE := by
  have hBCd : B ≤ Cd := hle.trans frameT_spec.1
  have hN : B.subgroupOf Cd ≤ normalizer (E0 : Set Cd) := fun b hb =>
    frameT_le_normalizer frameT_spec.2.2 (hle (Subgroup.mem_subgroupOf.1 hb))
  have hsq : ∀ b ∈ B.subgroupOf Cd, b ^ 2 = 1 := fun b hb =>
    Subtype.ext (by simpa using hB.1 _ (Subgroup.mem_subgroupOf.1 hb))
  have hcard : Nat.card (B.subgroupOf Cd) = 2 ^ 11 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBCd).toEquiv).trans hB.2
  have heq := E0_unique _ hN hsq hcard
  ext x
  constructor
  · intro hx
    have : (⟨x, hBCd hx⟩ : Cd) ∈ B.subgroupOf Cd := Subgroup.mem_subgroupOf.2 hx
    rw [heq] at this
    exact Subgroup.mem_subgroupOf.1 this
  · intro hx
    have : (⟨x, frameE_le_Cd hx⟩ : Cd) ∈ E0 := Subgroup.mem_subgroupOf.2 hx
    rw [← heq] at this
    exact Subgroup.mem_subgroupOf.1 this

theorem eq_conjSub_frameE_of_le {g : J} {S : Subgroup J} (hS : S = conjSub g frameT)
    {B : Subgroup J} (hB : IsE B) (hle : B ≤ S) : B = conjSub g frameE := by
  have hle' : conjSub g⁻¹ B ≤ frameT := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ B := by
      have := mem_conjSub_iff.1 hx
      simpa using this
    have h2 : g * x * g⁻¹ ∈ conjSub g frameT := hS ▸ hle h1
    have h3 := mem_conjSub_iff.1 h2
    simpa [mul_assoc] using h3
  have h := eq_frameE_of_le_frameT (hB.conjSub g⁻¹) hle'
  rw [← h, conjSub_conjSub_inv]

theorem eq_of_le_sylow (S : Sylow 2 J) {B₁ B₂ : Subgroup J} (h₁ : IsE B₁) (h₂ : IsE B₂)
    (hl₁ : B₁ ≤ S) (hl₂ : B₂ ≤ S) : B₁ = B₂ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J frameSylow S
  have hS : (S : Subgroup J) = conjSub g frameT := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  rw [eq_conjSub_frameE_of_le hS h₁ hl₁, eq_conjSub_frameE_of_le hS h₂ hl₂]

theorem exists_conj_eq_frameE {B : Subgroup J} (hB : IsE B) : ∃ g : J, B = conjSub g frameE := by
  obtain ⟨S, hS⟩ := (IsPGroup.of_card (n := 11) hB.2).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J frameSylow S
  have hS' : (S : Subgroup J) = conjSub g frameT := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  exact ⟨g, eq_conjSub_frameE_of_le hS' hB hS⟩

theorem exists_conj_of_le (H : Subgroup J) (hH : ¬ 2 ∣ H.index) {B₁ B₂ : Subgroup J}
    (h₁ : IsE B₁) (h₂ : IsE B₂) (hl₁ : B₁ ≤ H) (hl₂ : B₂ ≤ H) :
    ∃ h ∈ H, B₂ = conjSub h B₁ := by
  have hp : ∀ B : Subgroup J, IsE B → B ≤ H → IsPGroup 2 (B.subgroupOf H) := fun B hB hl =>
    IsPGroup.of_card (n := 11)
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl).toEquiv).trans hB.2)
  obtain ⟨Q₁, hQ₁⟩ := (hp B₁ h₁ hl₁).exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := (hp B₂ h₂ hl₂).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H Q₁ Q₂
  have hS₂p : IsPGroup 2 (Q₂.map H.subtype) := Q₂.2.map H.subtype
  have hS₂i : ¬ 2 ∣ (Q₂.map H.subtype).index := by
    have h1 := Subgroup.relIndex_mul_index (Subgroup.map_subtype_le (Q₂ : Subgroup H))
    have e : (Q₂.map H.subtype).subgroupOf H = (Q₂ : Subgroup H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [Subgroup.relIndex, e] at h1
    rw [← h1]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h2 | h2
    · exact Q₂.not_dvd_index h2
    · exact hH h2
  let S₂ : Sylow 2 J := hS₂p.toSylow hS₂i
  have hS₂ : (S₂ : Subgroup J) = Q₂.map H.subtype := rfl
  have hB₂ : B₂ ≤ S₂ := by
    intro x hx
    rw [hS₂]
    exact ⟨⟨x, hl₂ hx⟩, hQ₂ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hB₁ : conjSub (h : J) B₁ ≤ S₂ := by
    intro x hx
    have hxH : x ∈ H := by
      have := mem_conjSub_iff.1 hx
      have h3 : (h : J) * ((h : J)⁻¹ * x * (h : J)) * (h : J)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem h.2 (hl₁ this)) (H.inv_mem h.2)
      simpa [mul_assoc] using h3
    rw [hS₂]
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [← hh]
    refine mem_sylow_smul_iff.2 (hQ₁ (Subgroup.mem_subgroupOf.2 ?_))
    exact mem_conjSub_iff.1 hx
  exact ⟨h, h.2, eq_of_le_sylow S₂ h₂ (h₁.conjSub h) hB₂ hB₁⟩

end Unique

theorem mem_normalizer_of_conjSub_eq {G : Type} [Group G] {n : G} {E : Subgroup G}
    (h : conjSub n E = E) : n ∈ normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  conv_rhs => rw [← h, mem_conjSub_iff]
  simp [mul_assoc]

section Transitive

theorem frameE_isE : IsE (frameE : Subgroup J) := ⟨frameE_sq, frameE_card⟩

theorem not_dvd_index_centralizer {q : J} (hq : q ∈ D23) :
    ¬ 2 ∣ (centralizer ({q} : Set J)).index := by
  have h := Subgroup.card_mul_index (centralizer ({q} : Set J))
  rw [CFSG.Sporadic.FischerOddCore.card_centralizer_of_isConj (hq : IsConj d q),
    card_centralizer_d, card_J] at h
  omega

theorem exists_mem_normalizer_frameE {p q : J} (hp : p ∈ (frameE : Subgroup J)) (hpD : p ∈ D23)
    (hq : q ∈ (frameE : Subgroup J)) (hqD : q ∈ D23) :
    ∃ n ∈ normalizer ((frameE : Subgroup J) : Set J), n * p * n⁻¹ = q := by
  obtain ⟨g, hg⟩ := isConj_iff.1 ((hpD : IsConj d p).symm.trans hqD)
  have hcomm : ∀ x ∈ (frameE : Subgroup J), x * q = q * x := fun x hx => frameE_comm x hx q hq
  have hl₁ : (frameE : Subgroup J) ≤ centralizer ({q} : Set J) := fun x hx =>
    mem_centralizer_singleton_iff.2 (hcomm x hx)
  have hl₂ : conjSub g (frameE : Subgroup J) ≤ centralizer ({q} : Set J) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have hx' := mem_conjSub_iff.1 hx
    have hqx : g⁻¹ * q * g ∈ (frameE : Subgroup J) := by
      rw [← hg]
      simpa [mul_assoc] using hp
    have := frameE_comm _ hx' _ hqx
    calc x * q = g * ((g⁻¹ * x * g) * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * q * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = q * x := by group
  obtain ⟨h, hh, hEq⟩ := exists_conj_of_le _ (not_dvd_index_centralizer hqD) frameE_isE
    (frameE_isE.conjSub g) hl₁ hl₂
  have hn : conjSub (h⁻¹ * g) (frameE : Subgroup J) = frameE :=
    ((conjSub_conjSub h⁻¹ g _).symm.trans (by rw [hEq])).trans (conjSub_inv_conjSub h _)
  have hhq := mem_centralizer_singleton_iff.1 hh
  refine ⟨h⁻¹ * g, mem_normalizer_of_conjSub_eq hn, ?_⟩
  calc h⁻¹ * g * p * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * p * g⁻¹) * h := by group
    _ = h⁻¹ * q * h := by rw [hg]
    _ = q := by rw [mul_assoc, ← hhq]; group

end Transitive

end CFSG.EvenSporadicStandard.Solomon78.F23L63
