module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Datum
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec64_cyclic_comm' {U : Subgroup G} (hU : IsCyclic ↥U) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) : a * b = b * a := by
  obtain ⟨g, hg⟩ := hU.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have h : (⟨a, ha⟩ : ↥U) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    rw [← hi, ← hj]
    exact zpow_mul_comm g i j
  exact congrArg Subtype.val h

theorem sec64_transfer [Finite G] (h33 : Asc82Lemma33) (h63 : Asc82Lemma63)
    (hE8 : Asc82Case64E8) {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    (hHyp : Asc82Hyp62 G) {X Y T : Subgroup G} {x y : G} (hXC : InC X) (hXF : InFStar X)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hXY : X ≤ Y)
    (hxN : x ∉ centralizer (Y : Set G)) (hYC : InCStar Y) (hYF : InFStar Y)
    (hT : IsSylow2Of T (centralizer (X : Set G))) (hxT : x ∈ T) (hyT : y ∈ T)
    (halt : ∀ R : Subgroup G, IsPGroup 2 ↥R →
      R ≤ normalizer (Y : Set G) ⊓ centralizer (X : Set G) → Sec64Alt X Y R) :
    Sec64Cfg T (centralizer (Y : Set G)) x y ∧ Sec64Tri T (centralizer (Y : Set G)) y ∧
      (¬ (centralizer (Y : Set G)).relIndex (T ⊓ centralizer ({y} : Set G)) ≤ 2 →
        IsU33 X ∨ IsL29 X) := by
  have hTp : IsPGroup 2 ↥T := hT.2.1
  have hyH : y ∈ centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYc.1 ha)
  have hRN : ∀ r ∈ T ⊓ centralizer ({y} : Set G), r ∈ normalizer (Y : Set G) := by
    intro r hr
    exact sec64_mem_normalizer h63 hS hHyp hy hYc hYF hr.2
  have hRH : ∀ r ∈ T ⊓ centralizer ({y} : Set G),
      ∀ h ∈ centralizer (Y : Set G), r * h * r⁻¹ ∈ centralizer (Y : Set G) := by
    intro r hr h hh
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hb : r⁻¹ * a * r ∈ Y :=
      (Subgroup.mem_normalizer_iff''.mp (hRN r hr) a).mp ha
    have hcomm : (r⁻¹ * a * r) * h = h * (r⁻¹ * a * r) :=
      Subgroup.mem_centralizer_iff.mp hh (r⁻¹ * a * r) hb
    calc a * (r * h * r⁻¹)
        = r * ((r⁻¹ * a * r) * h) * r⁻¹ := by group
        _ = r * (h * (r⁻¹ * a * r)) * r⁻¹ := by rw [hcomm]
        _ = (r * h * r⁻¹) * a := by group
  have hcfg : Sec64Cfg T (centralizer (Y : Set G)) x y :=
    ⟨hTp, hx, hy, hxy, hxT, hyT, hxN, hyH, hRH,
      sec64_isCyclic_U h33 hS hYc hYC hYF hTp hyT⟩
  have hRp : IsPGroup 2 ↥(T ⊓ centralizer ({y} : Set G)) := hTp.to_le inf_le_left
  have hRle : T ⊓ centralizer ({y} : Set G) ≤
      normalizer (Y : Set G) ⊓ centralizer (X : Set G) := by
    intro r hr
    exact ⟨hRN r hr, hT.1 hr.1⟩
  have hAlt := halt (T ⊓ centralizer ({y} : Set G)) hRp hRle
  have hUcyc : IsCyclic ↥(T ⊓ centralizer (Y : Set G)) :=
    sec63_isCyclic_inf h33 hS hYC hYF hTp
  have hyU : y ∈ T ⊓ centralizer (Y : Set G) := ⟨hyT, hyH⟩
  have hUeq : T ⊓ centralizer ({y} : Set G) ⊓ centralizer (Y : Set G) =
      T ⊓ centralizer (Y : Set G) := by
    ext r
    simp only [Subgroup.mem_inf]
    refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (sec64_cyclic_comm' hUcyc hyU h).symm
  have hAltTri := hAlt
  have hTri : Sec64Tri T (centralizer (Y : Set G)) y := by
    unfold Sec64Tri
    unfold Sec64Alt at hAltTri
    rcases hAltTri with h | h | h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨?_, h.2.2⟩)
      intro hel h8 hU2 hne
      exact hE8 G t L hS hHyp y X Y T hy hXC hXF h.1 hYc hXY hYC hYF h.2.1 hT hyT
        hel h8 (hUeq ▸ hU2) hne
    · exact Or.inr (Or.inr h.2.2)
    · exact Or.inr (Or.inr h.2.2)
  refine ⟨hcfg, hTri, ?_⟩
  intro hgt
  unfold Sec64Alt at hAlt
  rcases hAlt with h | h | h | h
  · exact absurd h hgt
  · exact Or.inr h.1
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem asc82Lemma64_of (h33 : Asc82Lemma33) (h63 : Asc82Lemma63) (hsh : Asc82Shapes)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) (hCh : Asc82AutCentChain3) (hE8 : Asc82Case64E8)
    (hout : Asc82Outside) : Asc82Lemma64 := by
  intro G _ _ t L hS hHyp X hXC hXF T hT
  rcases sec64_datum h63 hsh hP hF hCh hS hHyp hXC hXF with
    hXCS | ⟨x, y, Y, hx, hy, hxy, hxCX, hYc, hXY, hxN, hYC, hYF, hshape, halt⟩
  · left
    have hcyc := sec63_isCyclic_inf h33 hS hXCS hXF hT.2.1
    rwa [inf_eq_left.mpr hT.1] at hcyc
  · have hyCX : y ∈ centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYc.1 (hXY ha))
    obtain ⟨T', hT', hxT', hyT', hrk, hsrk, -⟩ :=
      sec64_sylow_pair hT hx hy hxy hxCX hyCX
    obtain ⟨cfg, tri, hgt⟩ :=
      sec64_transfer h33 h63 hE8 hS hHyp hXC hXF hx hy hxy hYc hXY hxN hYC hYF
        hT' hxT' hyT' halt
    have hout' := sec64_core hout cfg tri
    unfold Sec64Out at hout'
    have hshape' : IsL3Eps3 X ∨ IsL29 X ∨ IsOmega5 X := by
      rcases hshape with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    rcases hout' with h | ⟨h1, h2⟩
    · right; left; exact ⟨hshape', hrk ▸ h⟩
    · right; right; exact ⟨hgt h1, hsrk ▸ h2⟩

end CFSG.OddStandard.SmallF3.Omega
