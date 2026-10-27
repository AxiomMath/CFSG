module

public import CFSG.GF2Type.Aschbacher1976Full.HSBadLocal2
public import CFSG.GF2Type.Aschbacher1976Full.HSTransStarConj
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxInterfaces

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_le_H {z : G} {T : Sylow 2 G} (hTH : (T : Subgroup G) ≤ Hz z)
    {P : Subgroup G} (hP : IsPGroup 2 ↥P) (hPH : P ≤ Hz z) :
    ∃ T' : Sylow 2 G, P ≤ (T' : Subgroup G) ∧ (T' : Subgroup G) ≤ Hz z ∧
      ∃ g : G, ∀ x : G, x ∈ (T' : Subgroup G) ↔ g⁻¹ * x * g ∈ (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T₀ : Subgroup ↥(Hz z) := (T : Subgroup G).subgroupOf (Hz z)
  have hT₀ : IsPGroup 2 ↥T₀ := T.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hmax : ∀ {X : Subgroup ↥(Hz z)}, IsPGroup 2 ↥X → T₀ ≤ X → X = T₀ := by
    intro X hX hle
    have hX' : IsPGroup 2 ↥(X.map (Hz z).subtype) := hX.map _
    have hle' : (T : Subgroup G) ≤ X.map (Hz z).subtype := fun t ht =>
      ⟨⟨t, hTH ht⟩, hle (show (⟨t, hTH ht⟩ : ↥(Hz z)) ∈ T₀ from ht), rfl⟩
    have heq := T.is_maximal' hX' hle'
    refine le_antisymm (fun x hx => ?_) hle
    have : (x : G) ∈ X.map (Hz z).subtype := ⟨x, hx, rfl⟩
    rw [heq] at this
    exact this
  let S₀ : Sylow 2 ↥(Hz z) := ⟨T₀, hT₀, hmax⟩
  let P₀ : Subgroup ↥(Hz z) := P.subgroupOf (Hz z)
  have hP₀ : IsPGroup 2 ↥P₀ := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨R, hR⟩ := hP₀.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (↥(Hz z)) S₀ R
  have hmem : ∀ x : ↥(Hz z), x ∈ ((h • S₀ : Sylow 2 ↥(Hz z)) : Subgroup ↥(Hz z)) ↔
      h⁻¹ * x * h ∈ T₀ := TransStar.mem_smul_sylow_iff (G := ↥(Hz z)) h S₀
  have hhH : (h : G) ∈ Hz z := h.2
  refine ⟨(h : G) • T, ?_, ?_, (h : G), TransStar.mem_smul_sylow_iff (h : G) T⟩
  · intro x hx
    have hx' : (⟨x, hPH hx⟩ : ↥(Hz z)) ∈ P₀ := hx
    have := (hmem _).mp (hR hx')
    have h2 : (h : G)⁻¹ * x * (h : G) ∈ (T : Subgroup G) := this
    exact (TransStar.mem_smul_sylow_iff (h : G) T x).mpr h2
  · intro x hx
    have h2 := (TransStar.mem_smul_sylow_iff (h : G) T x).mp hx
    have h3 := hTH h2
    have : x = (h : G) * ((h : G)⁻¹ * x * (h : G)) * (h : G)⁻¹ := by group
    rw [this]
    exact (Hz z).mul_mem ((Hz z).mul_mem hhH h3) ((Hz z).inv_mem hhH)

theorem cruxFibre_holds : ∀ {G : Type} [Group G] [Finite G] {z : G} {T : Sylow 2 G}, BadAt z T → FibreProp z := by
  intro G _ _ z T hbad u hu u' hu' hS
  obtain ⟨hset, hti, hTH, hcard⟩ := hbad
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  obtain ⟨y, hy⟩ := exists_gen_H hD hz hF2 hu
  obtain ⟨y', hy'⟩ := exists_gen_H hD hz hF2 hu'
  have ha := yBar_eq hD hz hF2 hti hu hy
  have ha' := yBar_eq hD hz hF2 hti hu' hy'
  have hker : IsPGroup 2 ↥(qmk z).ker := by
    rw [ker_qmk]
    exact hF2.comap_subtype
  have hpre := IsPGroup.comap_of_ker_isPGroup hS (qmk z) hker
  set P₂ := ((Subgroup.closure ({yBar z u, yBar z u'} : Set (Qbar z))).comap (qmk z)).map
    (Hz z).subtype with hP₂
  have hP₂2 : IsPGroup 2 ↥P₂ := hpre.map _
  have hP₂H : P₂ ≤ Hz z := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hyP : (y : G) ∈ P₂ := by
    refine ⟨y, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [← ha]
    exact Subgroup.subset_closure (by simp)
  have hyP' : (y' : G) ∈ P₂ := by
    refine ⟨y', Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [← ha']
    exact Subgroup.subset_closure (by simp)
  obtain ⟨T', hPT', hT'H, -⟩ := exists_sylow_le_H hTH hP₂2 hP₂H
  have hcard' : Nat.card (ET (T' : Subgroup G) z) = 4 := by
    rw [TransStar.card_ET_eq z T T']
    exact hcard
  obtain ⟨Z₀, A₀, hD₀⟩ := Width.exists_Z4Data hZ4
  have c : BL.Ctx z 2 Z₀ A₀ T' := ⟨hD₀, hz, hF2, hT'H⟩
  have hu1 := ZF_props hD hz hF2 hu.1
  have hu1' := ZF_props hD hz hF2 hu'.1
  have hv : IsConj z u ∧ ZF u ≤ (T' : Subgroup G) :=
    ⟨hu.1, by rw [hy]; exact zpowers_le.mpr (hPT' hyP)⟩
  have hw : IsConj z u' ∧ ZF u' ≤ (T' : Subgroup G) :=
    ⟨hu'.1, by rw [hy']; exact zpowers_le.mpr (hPT' hyP')⟩
  rcases Bad.eq_or_eq_mul c hti hcard' hv hu.2.1 hw hu'.2.1 with h | h
  · exact Or.inl h
  · exact Or.inr h

end CFSG.GF2Type.Aschbacher1976Full.HS
