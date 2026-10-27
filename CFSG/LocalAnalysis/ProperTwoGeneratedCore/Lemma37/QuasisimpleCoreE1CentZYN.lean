module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZY

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem e1Pi_conj_eq_iff {n r : e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))}
    (hn : (n : J ⧸ Subgroup.center J) ∈ e1NBar (Subgroup.center J) u m y x)
    (hr : (r : J ⧸ Subgroup.center J) ∈ e1RBar (Subgroup.center J) u m y x) :
    e1Pi (e1ZM (Subgroup.center J) u m y x) n * e1Pi (e1ZM (Subgroup.center J) u m y x) r *
        (e1Pi (e1ZM (Subgroup.center J) u m y x) n)⁻¹ = e1Pi (e1ZM (Subgroup.center J) u m y x) r ↔
      (n : J ⧸ Subgroup.center J) * r * (n : J ⧸ Subgroup.center J)⁻¹ = r ∨
        (n : J ⧸ Subgroup.center J) * r * (n : J ⧸ Subgroup.center J)⁻¹ =
          r * caseC3Word (Subgroup.center J) u m y x 40 := by
  rw [← map_inv, ← map_mul, ← map_mul,
    d.e1Pi_eq_iff (CaseC3BCD.conj_mem_of_mem_e1NBar hn _ hr) hr]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

omit d in
theorem e1Pi_mem_normalizer {n : e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))}
    (hn : (n : J ⧸ Subgroup.center J) ∈ e1NBar (Subgroup.center J) u m y x) :
    e1Pi (e1ZM (Subgroup.center J) u m y x) n ∈ Subgroup.normalizer
      ((((e1RBar (Subgroup.center J) u m y x).subgroupOf
        (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
          (e1Pi (e1ZM (Subgroup.center J) u m y x)) : Subgroup (E1Y (Subgroup.center J) u m y x)) :
            Set (E1Y (Subgroup.center J) u m y x)) := by
  refine mem_normalizer_of_forall_conj_mem fun a ha => ?_
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ha
  rw [← map_inv, ← map_mul, ← map_mul]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
    (CaseC3BCD.conj_mem_of_mem_e1NBar hn _ (Subgroup.mem_subgroupOf.mp hr)))

theorem exists_e1Pi_eq {q : E1Y (Subgroup.center J) u m y x}
    (hq : q ∈ Subgroup.normalizer ((((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1Pi (e1ZM (Subgroup.center J) u m y x)) : Subgroup (E1Y (Subgroup.center J) u m y x)) :
          Set (E1Y (Subgroup.center J) u m y x))) :
    ∃ n : e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)),
      (n : J ⧸ Subgroup.center J) ∈ e1NBar (Subgroup.center J) u m y x ∧
        e1Pi (e1ZM (Subgroup.center J) u m y x) n = q := by
  have hb := d.caseC3BCD
  obtain ⟨n, hn, rfl⟩ := exists_e1Pi_eq_of_mem_normalizer (e1ZM (Subgroup.center J) u m y x)
    hb.isPGroup_e1RBar.comap_subtype (hb.not_two_dvd_relIndex S rfl) hq
  exact ⟨n, ⟨n.2, mem_normalizer_of_forall_conj_mem fun s hs => Subgroup.mem_subgroupOf.mp
    (hn ⟨s, hb.e1RBar_le_e1M0 hs⟩ (Subgroup.mem_subgroupOf.mpr hs))⟩, rfl⟩

theorem e1Pi_mem_centralizer {n : e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))}
    (hn : (n : J ⧸ Subgroup.center J) ∈ e1KBar (Subgroup.center J) u m y x) :
    e1Pi (e1ZM (Subgroup.center J) u m y x) n ∈ Subgroup.centralizer
      ((((e1RBar (Subgroup.center J) u m y x).subgroupOf
        (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
          (e1Pi (e1ZM (Subgroup.center J) u m y x)) : Subgroup (E1Y (Subgroup.center J) u m y x)) :
            Set (E1Y (Subgroup.center J) u m y x)) := by
  obtain ⟨hnN, hnK⟩ := (d.caseC3BCD.mem_e1KBar_iff S rfl).mp hn
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_subgroupOf] at hr
  have h := (d.e1Pi_conj_eq_iff hnN hr).mpr (hnK _ hr)
  calc e1Pi (e1ZM (Subgroup.center J) u m y x) r * e1Pi (e1ZM (Subgroup.center J) u m y x) n =
        e1Pi (e1ZM (Subgroup.center J) u m y x) n * e1Pi (e1ZM (Subgroup.center J) u m y x) r *
          (e1Pi (e1ZM (Subgroup.center J) u m y x) n)⁻¹ *
            e1Pi (e1ZM (Subgroup.center J) u m y x) n := by rw [h]
    _ = _ := by group

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem relIndex_centralizer_normalizer_e1Y_le :
    (Subgroup.centralizer ((((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1Pi (e1ZM (Subgroup.center J) u m y x)) : Subgroup (E1Y (Subgroup.center J) u m y x)) :
          Set (E1Y (Subgroup.center J) u m y x))).relIndex
      (Subgroup.normalizer ((((e1RBar (Subgroup.center J) u m y x).subgroupOf
        (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
          (e1Pi (e1ZM (Subgroup.center J) u m y x)) : Subgroup (E1Y (Subgroup.center J) u m y x)) :
            Set (E1Y (Subgroup.center J) u m y x))) ≤ 3 := by
  set P := ((e1RBar (Subgroup.center J) u m y x).subgroupOf
    (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
      (e1Pi (e1ZM (Subgroup.center J) u m y x)) with hP
  set NY := Subgroup.normalizer (P : Set (E1Y (Subgroup.center J) u m y x)) with hNY
  set CY := Subgroup.centralizer (P : Set (E1Y (Subgroup.center J) u m y x)) with hCY
  let ψ : e1NBar (Subgroup.center J) u m y x →* NY :=
    ((e1Pi (e1ZM (Subgroup.center J) u m y x)).comp
      (Subgroup.inclusion CaseC3BCD.e1NBar_le_e1M0)).codRestrict NY
        fun n => e1Pi_mem_normalizer n.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨n, hn, rfl⟩ := d.exists_e1Pi_eq hq
    exact ⟨⟨n, hn⟩, rfl⟩
  have hK : (e1KBar (Subgroup.center J) u m y x).subgroupOf (e1NBar (Subgroup.center J) u m y x) ≤
      (CY.subgroupOf NY).comap ψ := fun n hn =>
    d.e1Pi_mem_centralizer (n := Subgroup.inclusion CaseC3BCD.e1NBar_le_e1M0 n)
      (Subgroup.mem_subgroupOf.mp hn)
  have h3 := d.relIndex_e1KBar_eq_three htype
  calc CY.relIndex NY = ((CY.subgroupOf NY).comap ψ).index :=
        (Subgroup.index_comap_of_surjective _ hψ).symm
    _ ≤ ((e1KBar (Subgroup.center J) u m y x).subgroupOf
          (e1NBar (Subgroup.center J) u m y x)).index :=
        Nat.le_of_dvd (by rw [show ((e1KBar (Subgroup.center J) u m y x).subgroupOf
          (e1NBar (Subgroup.center J) u m y x)).index = 3 from h3]; norm_num)
          (Subgroup.index_dvd_of_le hK)
    _ = 3 := h3

theorem conj_ne_of_not_mem_centralizer_e1Y {q : E1Y (Subgroup.center J) u m y x}
    (hq : q ∈ Subgroup.normalizer ((((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1Pi (e1ZM (Subgroup.center J) u m y x)) : Subgroup (E1Y (Subgroup.center J) u m y x)) :
          Set (E1Y (Subgroup.center J) u m y x)))
    (hqC : q ∉ Subgroup.centralizer ((((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1Pi (e1ZM (Subgroup.center J) u m y x)) : Subgroup (E1Y (Subgroup.center J) u m y x)) :
          Set (E1Y (Subgroup.center J) u m y x)))
    {a : E1Y (Subgroup.center J) u m y x}
    (ha : a ∈ ((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map (e1Pi (e1ZM (Subgroup.center J) u m y x)))
    (ha1 : a ≠ 1) : q * a * q⁻¹ ≠ a := by
  have hb := d.caseC3BCD
  obtain ⟨n, hn, rfl⟩ := d.exists_e1Pi_eq hq
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_subgroupOf] at hr
  have hnK : (n : J ⧸ Subgroup.center J) ∉ e1KBar (Subgroup.center J) u m y x := fun hK =>
    hqC (d.e1Pi_mem_centralizer hK)
  have hr1 : (r : J ⧸ Subgroup.center J) ≠ 1 := fun h1 =>
    ha1 ((d.e1Pi_eq_one_iff hr).mpr (d.mem_e1ZM_iff.mpr (Or.inl h1)))
  have hrz : (r : J ⧸ Subgroup.center J) ≠ caseC3Word (Subgroup.center J) u m y x 40 := fun h1 =>
    ha1 ((d.e1Pi_eq_one_iff hr).mpr (d.mem_e1ZM_iff.mpr (Or.inr h1)))
  obtain ⟨hne1, hne2⟩ := hb.conj_ne_of_not_mem_e1KBar_typeD htype S rfl hn hnK hr hr1 hrz
  intro h
  rcases (d.e1Pi_conj_eq_iff hn hr).mp h with h' | h'
  exacts [hne1 h', hne2 h']

omit htype in
theorem conj_mem_e1RBar_sup_of_normal
    (hn : (((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1Pi (e1ZM (Subgroup.center J) u m y x))).Normal)
    {g : J ⧸ Subgroup.center J} (hg : g ∈ e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))
    {r : J ⧸ Subgroup.center J} (hr : r ∈ e1RBar (Subgroup.center J) u m y x) :
    g * r * g⁻¹ ∈ e1RBar (Subgroup.center J) u m y x ⊔
      (CFSG.pPrimeCore 2 (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))).subtype := by
  have h := Subgroup.mem_map_of_mem (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))).subtype
    (conj_mem_sup_of_normal_map (e1ZM (Subgroup.center J) u m y x) e1ZM_le_center
      d.isPGroup_e1ZM d.e1ZM_le hn ⟨g, hg⟩ (r := ⟨r, d.caseC3BCD.e1RBar_le_e1M0 hr⟩)
        (Subgroup.mem_subgroupOf.mpr hr))
  rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr d.caseC3BCD.e1RBar_le_e1M0] at h

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
