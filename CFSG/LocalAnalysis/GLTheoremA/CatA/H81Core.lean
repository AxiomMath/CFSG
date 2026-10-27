module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Cent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem map_centralizer_quot {p : ℕ} (hp : p.Prime) {L : Subgroup G} (yK : ↥L)
    (hy : IsPGroup p (Subgroup.zpowers yK)) :
    (Subgroup.centralizer ({yK} : Set ↥L)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) =
      Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥L) yK} : Set (PQuot p L)) := by
  have hyA : yK ∈ Subgroup.normalizer ((⊤ : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have h := map_inf_centralizer_eq hp (QuotientGroup.mk' (GLAPPrimeCore p ↥L))
    (coprime_inf_quot hp L) (A := ⊤) hy hyA
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), top_inf_eq] at h
  exact h

theorem exists_choice_component {p : ℕ} (hp : p.Prime) {L : Subgroup G} (yK : ↥L)
    (hy : IsPGroup p (Subgroup.zpowers yK)) (JH : Subgroup (PQuot p L))
    (hJ : GLAPComponent p (Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥L) yK} :
      Set (PQuot p L))) JH)
    (hu : ∀ M : Subgroup (PQuot p L), GLAPComponent p
      (Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥L) yK} : Set (PQuot p L))) M → M = JH) :
    ∃ JK : Subgroup ↥L, GLAPComponent p (Subgroup.centralizer ({yK} : Set ↥L)) JK ∧
      JK.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) = JH ∧
      (∀ T : Subgroup ↥L, GLAPComponent p (Subgroup.centralizer ({yK} : Set ↥L)) T → T = JK) ∧
      GLAPLayer p (Subgroup.centralizer ({yK} : Set ↥L)) = JK := by
  have hC := map_centralizer_quot hp yK hy
  have hψ := coprime_inf_quot hp L
  obtain ⟨JK, hJK, hmap⟩ := component_lift hp (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) hψ _ (M := JH)
    (by rw [hC]; exact hJ)
  have huniq : ∀ T : Subgroup ↥L, GLAPComponent p (Subgroup.centralizer ({yK} : Set ↥L)) T → T = JK := by
    intro T hT
    have h1 := component_image hp (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) hψ _ hT
    rw [hC] at h1
    have h2 := hu _ h1
    have heq : T.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) =
        JK.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) := h2.trans hmap.symm
    exact component_eq_of_map_eq hp _ hψ hT hJK heq
  refine ⟨JK, hJK, hmap, huniq, layer_eq_of_unique hJK huniq⟩

theorem map_subtype_centralizer {L : Subgroup G} (yK : ↥L) :
    (Subgroup.centralizer ({yK} : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.centralizer ({(yK : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : yK * k = k * yK := by
      have := Subgroup.mem_centralizer_iff.1 hk yK (Set.mem_singleton _)
      exact this
    refine ⟨k.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := congrArg Subtype.val hk'
    simpa using this
  · rintro ⟨hgL, hg⟩
    refine ⟨⟨g, hgL⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_, rfl⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 hg (h : G) (Set.mem_singleton _)
    simpa using this

theorem component_map_subtype {p : ℕ} (hp : p.Prime) {L : Subgroup G} {K S : Subgroup ↥L}
    (hS : GLAPComponent p K S) : GLAPComponent p (K.map L.subtype) (S.map L.subtype) :=
  component_image hp L.subtype (fun A => coprime_ker_subtype L A) K hS

theorem centMod_of_commute {p : ℕ} {J : Subgroup G} {g : G} (hg : ∀ j ∈ J, g * j = j * g) :
    CentMod p J g := by
  have hfix : ∀ j ∈ J, g⁻¹ * j * g = j := by
    intro j hj
    rw [mul_assoc, ← hg j hj]
    group
  have hnorm : g ∈ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have e : g * h * g⁻¹ = h := by
        rw [hg h hh]
        group
      rw [e]
      exact hh
    · intro hh
      have e := hfix _ hh
      rw [show h = g⁻¹ * (g * h * g⁻¹) * g by group, e]
      exact hh
  refine centMod_iff.2 (mem_centModSubgroup.2 ⟨hnorm, fun l hl => ?_⟩)
  have h1 : ⁅l, g⁆ = 1 := by
    rw [commutatorElement_def, ← hg l hl]
    group
  rw [h1]
  exact Subgroup.one_mem _

end CFSG.LocalAnalysis.GLTheoremA.H81
