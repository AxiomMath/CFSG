module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

theorem mem_of_normal_of_isSylowOf {p : ℕ} [Fact p.Prime] [Finite G] {M K P : Subgroup G}
    (hK : (K.subgroupOf M).Normal) (hP : CFSG.ABGLocalTools.IsSylowOf p P M) (hPK : P ≤ K)
    {x : G} (hxM : x ∈ M) {k : ℕ} (hx : orderOf x = p ^ k) : x ∈ K := by
  classical
  let x' : ↥M := ⟨x, hxM⟩
  have hx'ord : orderOf x' = p ^ k :=
    (Subgroup.orderOf_coe x').symm.trans hx
  have hx'p : IsPGroup p (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hx'ord])
  obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
  obtain ⟨S', hS'⟩ := hx'p.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) S S'
  have hSK : S ≤ K.subgroupOf M := by
    rw [hS]
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hPK (Subgroup.mem_subgroupOf.mp hy))
  have hS'K : S' ≤ K.subgroupOf M := by
    rw [← hm]
    intro y hy
    rw [Sylow.coe_subgroup_smul] at hy
    obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hy
    simpa [MulAut.conj_apply] using hK.conj_mem z (hSK hz) m
  exact Subgroup.mem_subgroupOf.mp (hS'K (hS' (Subgroup.mem_zpowers x')))

theorem exists_isSylowOf_inf_eq_of_le {p : ℕ} [Fact p.Prime] [Finite G] {M P Q0 : Subgroup G}
    (hPM : P ≤ M) (hQ0 : CFSG.ABGLocalTools.IsSylowOf p Q0 P) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p R M ∧ R ⊓ P = Q0 := by
  classical
  let P' : Subgroup ↥M := P.subgroupOf M
  obtain ⟨S, hS⟩ := hQ0.exists_sylow_eq_subgroupOf
  let e : ↥P' ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPM
  let S' : Sylow p ↥P' := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hS'coe : (S' : Subgroup ↥P') = (S : Subgroup ↥P).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hS'mem : ∀ x : ↥P', x ∈ (S' : Subgroup ↥P') ↔ e x ∈ (S : Subgroup ↥P) := by
    intro x
    rw [hS'coe]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hxe : e x = y := by
        rw [← hyx]
        exact e.apply_symm_apply y
      rwa [hxe]
    · intro hx
      exact ⟨e x, hx, by simp⟩
  have hP'coe : ∀ x : ↥P', ((x : ↥M) : G) = ((e x : ↥P) : G) := fun x => rfl
  obtain ⟨R, hRcomap⟩ := Sylow.exists_comap_subtype_eq S'
  refine ⟨(R : Subgroup ↥M).map M.subtype, ⟨R, rfl⟩, ?_⟩
  ext g
  constructor
  · intro hg
    obtain ⟨hgRmap, hgP⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hgRmap
    have hrP : ((r : ↥M) : G) ∈ P := hgP
    let x : ↥P' := ⟨r, hrP⟩
    have hxS' : x ∈ (S' : Subgroup ↥P') := by
      rw [← hRcomap]
      exact hrR
    have hxS : e x ∈ (S : Subgroup ↥P) := (hS'mem x).mp hxS'
    have hxQ0 : ((e x : ↥P) : G) ∈ Q0 := by
      rw [hS] at hxS
      exact Subgroup.mem_subgroupOf.mp hxS
    rwa [← hP'coe x] at hxQ0
  · intro hgQ0
    have hgP : g ∈ P := hQ0.le hgQ0
    let x : ↥P' := ⟨⟨g, hPM hgP⟩, hgP⟩
    have hxS : e x ∈ (S : Subgroup ↥P) := by
      rw [hS]
      exact Subgroup.mem_subgroupOf.mpr (by rw [← hP'coe x]; exact hgQ0)
    have hxS' : x ∈ (S' : Subgroup ↥P') := (hS'mem x).mpr hxS
    have hxR : (x : ↥P') ∈ R.comap P'.subtype := by
      rw [hRcomap]
      exact hxS'
    have hxR' : (x : ↥M) ∈ (R : Subgroup ↥M) := hxR
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨(x : ↥M), hxR', rfl⟩, hgP⟩

theorem isSylowOf_le_normalizer_inf {p : ℕ} [Fact p.Prime] [Finite G] {M P R : Subgroup G}
    (hPM : P ≤ M) (hPn : (P.subgroupOf M).Normal)
    (hR : CFSG.ABGLocalTools.IsSylowOf p R M) :
    R ≤ Subgroup.normalizer (R ⊓ P : Set G) := by
  have hMn : M ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).1 hPn
  intro r hr
  change r ∈ Subgroup.normalizer ((R ⊓ P : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨R.mul_mem (R.mul_mem hr hx.1) (R.inv_mem hr),
      (Subgroup.mem_normalizer_iff.mp (hMn (hR.le hr)) x).mp hx.2⟩
  · intro hx
    have hr' : r⁻¹ ∈ R := R.inv_mem hr
    have hxR : x ∈ R := by
      have h1 : r⁻¹ * (r * x * r⁻¹) * r ∈ R :=
        R.mul_mem (R.mul_mem hr' hx.1) (by simpa using R.inv_mem hr')
      simpa [mul_assoc] using h1
    have hxP : x ∈ P := by
      have h1 : r⁻¹ * (r * x * r⁻¹) * r ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hMn (hR.le hr'))
          (r * x * r⁻¹)).mp hx.2
      simpa [mul_assoc] using h1
    exact ⟨hxR, hxP⟩

theorem exists_isSylowOf_le_of_normal_of_le_normalizer {p : ℕ} [Fact p.Prime] [Finite G]
    {M P Q Q0 : Subgroup G} (hPM : P ≤ M) (hPn : (P.subgroupOf M).Normal)
    (hQq : IsPGroup p Q) (hQ0 : CFSG.ABGLocalTools.IsSylowOf p Q0 P)
    (hQN : Q ≤ M ⊓ Subgroup.normalizer (Q0 : Set G))
    (hQn : (Q.subgroupOf (M ⊓ Subgroup.normalizer (Q0 : Set G))).Normal) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p R M ∧ Q ≤ R ∧
      (Q.subgroupOf R).Normal := by
  classical
  obtain ⟨R, hR, hRP⟩ := exists_isSylowOf_inf_eq_of_le (p := p) hPM hQ0
  have hRnormP : R ≤ Subgroup.normalizer (R ⊓ P : Set G) :=
    isSylowOf_le_normalizer_inf hPM hPn hR
  have hRQ0 : R ≤ Subgroup.normalizer (Q0 : Set G) := hRP ▸ hRnormP
  have hQnN : M ⊓ Subgroup.normalizer (Q0 : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).1 hQn
  have hRN : R ≤ Subgroup.normalizer (Q : Set G) := fun r hr =>
    hQnN ⟨hR.le hr, hRQ0 hr⟩
  have hQRq : IsPGroup p ↥(Q ⊔ R) := hQq.to_sup_of_normal_left' hR.isPGroup hRN
  have hQRle : Q ⊔ R ≤ M := sup_le (hQN.trans inf_le_left) hR.le
  have hQReq : Q ⊔ R = R := hR.eq_of_le le_sup_right hQRle hQRq
  have hQR : Q ≤ R := by rw [← hQReq]; exact le_sup_left
  exact ⟨R, hR, hQR, (Subgroup.normal_subgroupOf_iff_le_normalizer hQR).2 hRN⟩

end CFSG.GroupTheory
