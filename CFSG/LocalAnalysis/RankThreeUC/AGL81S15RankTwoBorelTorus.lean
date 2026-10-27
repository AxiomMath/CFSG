module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.SylowTwoEquiv

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

@[expose] def IsBorelTorus {G : Type} [Group G] (q : ℕ) (U E : Subgroup G) : Prop :=
  E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
    ∀ a ∈ Subgroup.normalizer (U : Set G), ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ U

@[expose] def HasBorelTorus (G : Type) [Group G] (q : ℕ) (U : Subgroup G) : Prop :=
  ∃ E : Subgroup G, IsBorelTorus q U E

theorem isBorelTorus_of_le_torus {G : Type} [Group G] {q : ℕ} {U H E : Subgroup G}
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hB : ∀ g ∈ Subgroup.normalizer (U : Set G), ∃ u ∈ U, ∃ h ∈ H, g = u * h)
    (hEH : E ≤ H) (hE : IsElemAbelian q E) (hcard : Nat.card E = q ^ 2) :
    IsBorelTorus q U E := by
  refine ⟨hEH.trans hHU, hE, hcard, ?_⟩
  intro a ha
  obtain ⟨u, hu, h, hh, rfl⟩ := hB a ha
  intro e he
  have heH : e ∈ H := hEH he
  have hhe : h * e * h⁻¹ = e := by
    rw [hHcomm h hh e heH, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : e * u⁻¹ * e⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hHU heH) u⁻¹).mp (Subgroup.inv_mem _ hu)
  have h1 : u * e * u⁻¹ * e⁻¹ ∈ U := by
    have := Subgroup.mul_mem U hu h2
    simpa [mul_assoc] using this
  have hmain : (u * h) * e * (u * h)⁻¹ * e⁻¹ = u * e * u⁻¹ * e⁻¹ := by
    rw [show (u * h) * e * (u * h)⁻¹ * e⁻¹ = u * (h * e * h⁻¹) * u⁻¹ * e⁻¹ by group,
      hhe]
  rw [hmain]
  exact h1

theorem IsBorelTorus.map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {q : ℕ}
    {U E : Subgroup G} (h : IsBorelTorus q U E) :
    IsBorelTorus q (U.map φ.toMonoidHom) (E.map φ.toMonoidHom) := by
  obtain ⟨hEnorm, hEel, hEcard, hEcomm⟩ := h
  obtain ⟨hEcomm', hEexp⟩ := hEel
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono (f := φ.toMonoidHom) hEnorm).trans
      (Subgroup.le_normalizer_map φ.toMonoidHom)
  · refine ⟨?_, ?_⟩
    · exact @Subgroup.map_isMulCommutative G G' _ _ E φ.toMonoidHom hEcomm'
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [← map_pow φ.toMonoidHom e q, hEexp e he, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective, hEcard]
  · intro a' ha' e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    have hmap : (Subgroup.normalizer (U : Set G)).map φ.toMonoidHom =
        Subgroup.normalizer ((U.map φ.toMonoidHom) : Set G') :=
      Subgroup.map_equiv_normalizer_eq U φ
    have ha'' : φ.symm a' ∈ Subgroup.normalizer (U : Set G) := by
      have ha'map : a' ∈ (Subgroup.normalizer (U : Set G)).map φ.toMonoidHom := by
        rw [hmap]
        exact ha'
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha'map
      rw [← hba]
      simpa using hb
    have h := hEcomm (φ.symm a') ha'' e he
    have h2 := Subgroup.mem_map_of_mem φ.toMonoidHom h
    simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using h2

theorem HasBorelTorus.of_isSylowTwoOf {G : Type} [Group G] [Finite G] {q : ℕ}
    {U₀ U : Subgroup G} (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (h : HasBorelTorus G q U₀) :
    HasBorelTorus G q U := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨g, -, hg⟩ := CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hU₀ hU
  refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_⟩
  rw [hg]
  exact IsBorelTorus.map (MulAut.conj g) hE

theorem HasBorelTorus.of_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G']
    (φ : G ≃* G') {q : ℕ} {U₀ : Subgroup G} (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (h : HasBorelTorus G q U₀) {U : Subgroup G'}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasBorelTorus G' q U := by
  have hfin : Finite G := Finite.of_injective (φ : G → G') φ.injective
  have hU₀' : CFSG.QuasithinUnique.IsSylowTwoOf (U₀.map φ.toMonoidHom) ⊤ := by
    have := @CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv G G' _ _ hfin _ U₀ ⊤ φ hU₀
    simpa using this
  obtain ⟨E, hE⟩ := h
  exact HasBorelTorus.of_isSylowTwoOf hU₀' hU
    ⟨E.map φ.toMonoidHom, IsBorelTorus.map φ hE⟩

theorem exists_borelTorus_of_hasBorelTorus {G : Type} [Group G] {S L : Subgroup G} {q : ℕ}
    (h : HasBorelTorus ↥L q ((S ⊓ L).subgroupOf L)) :
    ∃ E : Subgroup G, E ≤ L ∧ E ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
      IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      ∀ a ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G), ∀ e ∈ E,
        a * e * a⁻¹ * e⁻¹ ∈ S ⊓ L := by
  classical
  obtain ⟨E₀, hE₀norm, hE₀ab, hE₀card, hE₀comm⟩ := h
  have hcomap : (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).comap L.subtype =
      Subgroup.normalizer (((S ⊓ L).subgroupOf L : Subgroup L) : Set L) :=
    Subgroup.comap_normalizer_eq_of_le_range (by simp)
  refine ⟨E₀.map L.subtype, Subgroup.map_subtype_le E₀, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).comap L.subtype := by
      rw [hcomap]
      exact hE₀norm hy
    exact Subgroup.mem_comap.mp hy'
  · refine ⟨@Subgroup.map_isMulCommutative ↥L G _ _ E₀ L.subtype hE₀ab.1, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    simpa using congrArg L.subtype (hE₀ab.2 y hy)
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact hE₀card
  · intro a ha e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    have haN : (⟨a, ha.1⟩ : ↥L) ∈
        Subgroup.normalizer (((S ⊓ L).subgroupOf L : Subgroup L) : Set L) := by
      rw [← hcomap]
      exact Subgroup.mem_comap.mpr (by simpa using ha.2)
    have hmem := Subgroup.mem_subgroupOf.mp (hE₀comm ⟨a, ha.1⟩ haN e₀ he₀)
    simpa using hmem

end CFSG.LocalAnalysis.RankThreeUC.S15

end
