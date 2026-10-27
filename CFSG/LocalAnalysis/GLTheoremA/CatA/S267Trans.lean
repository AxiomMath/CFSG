module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot
public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop65Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.P65

section Cards

variable {A Ω : Type} [Group A] [Finite A] [Group Ω]

theorem inf_ker_eq_bot' {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    {P : Subgroup A} (hP : IsPGroup p P) : P ⊓ π.ker = ⊥ :=
  inf_eq_bot_of_isPGroup hp hP hN

theorem card_map_of_isPGroup {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    {P : Subgroup A} (hP : IsPGroup p P) : Nat.card (P.map π) = Nat.card P := by
  have hbot := inf_ker_eq_bot' hp π hN hP
  have hinj : Function.Injective (π.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : A) ∈ P ⊓ π.ker := ⟨x.2, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx)⟩
    rw [hbot, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  have hrange : (π.comp P.subtype).range = P.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

end Cards

section InD

variable {A Ω : Type} [Group A] [Finite A] [Group Ω] [Finite Ω]

theorem inD_of_quot {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    {M B₁ : Subgroup A} (hB : IsElemAbelian p B₁) (hBM : B₁ ≤ Subgroup.normalizer (M : Set A))
    {D' J' : Subgroup Ω} (hIn : InD p (B₁.map π) 1 (M.map π) D' J') :
    ∃ J : Subgroup A, J.map π = J' ∧ InD p B₁ 1 M (B₁ ⊓ D'.comap π) J := by
  obtain ⟨⟨hDB, hD2, hDB2⟩, ⟨hJc, hBJ, hCM⟩, hE⟩ := hIn
  have hBp : IsPGroup p B₁ := isPGroup_of_isElemAbelian hB
  have hBc : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := fun x hx y hy => isElemAbelian_commute hB hx hy
  set D : Subgroup A := B₁ ⊓ D'.comap π with hD
  have hDB₁ : D ≤ B₁ := inf_le_left
  have hDmap : D.map π = D' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := hDB hy
      exact ⟨b, ⟨hb, hy⟩, rfl⟩
  have hcD : Nat.card D = Nat.card D' := by
    rw [← hDmap]; exact (card_map_of_isPGroup hp π hN (hBp.to_le hDB₁)).symm
  have hcB : Nat.card B₁ = Nat.card (B₁.map π) := (card_map_of_isPGroup hp π hN hBp).symm
  obtain ⟨J, hJ, hJmap, hBJ'⟩ := exists_glaPComponent_lift_invariant hp π hN hBp hBM hBc hDB hJc hBJ
  refine ⟨J, hJmap, ⟨hDB₁, ?_, ?_⟩, ⟨hJ, hBJ', ?_⟩, ?_⟩
  · rw [hcD]; exact hD2
  · rw [hcD, hcB]; exact hDB2
  · intro b hb
    rw [centMod_iff, mem_centModSubgroup_map_iff hp π hN (hBJ' hb), hJmap, ← centMod_iff,
      hCM (π b) ⟨b, hb, rfl⟩]
    simp only [hD, Subgroup.mem_inf, Subgroup.mem_comap]
    exact ⟨fun h => ⟨hb, h⟩, fun h => h.2⟩
  · intro hD2'
    have hD'2 : Nat.card D' = p ^ 2 := by rw [← hcD]; exact hD2'
    obtain ⟨Ē, hĒB, hĒ, hĒc, hDĒ, hlay⟩ := hE hD'2
    set E : Subgroup A := B₁ ⊓ Ē.comap π with hEdef
    have hEB : E ≤ B₁ := inf_le_left
    have hEmap : E.map π = Ē := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · intro y hy
        obtain ⟨b, hb, rfl⟩ := hĒB hy
        exact ⟨b, ⟨hb, hy⟩, rfl⟩
    have hEel : IsElemAbelian p E := isElemAbelian_mono hB hEB
    have hEp : IsPGroup p E := hBp.to_le hEB
    have hcE : Nat.card E = Nat.card Ē := by
      rw [← hEmap]; exact (card_map_of_isPGroup hp π hN hEp).symm
    refine ⟨E, hEB, hEel, by rw [hcE]; exact hĒc, ?_, ?_⟩
    · intro x hx
      exact ⟨hDB₁ hx, hDĒ (by rw [← hDmap]; exact ⟨x, hx, rfl⟩)⟩
    · have hEJ : E ≤ Subgroup.normalizer (J : Set A) := hEB.trans hBJ'
      have hmap := map_inf_centralizer hp π hN hEp hEJ
      rw [← glaPLayer_map_ne_bot_iff hp π hN, hmap, hJmap, hEmap]
      exact hlay

end InD

section Inj

variable {A Ω : Type} [Group A] [Finite A] [Group Ω] [Finite Ω]

theorem map_inf_centralizer_inj (π : A →* Ω) (hπ : Function.Injective π) (M D : Subgroup A) :
    (M ⊓ Subgroup.centralizer (D : Set A)).map π =
      M.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup Ω) : Set Ω) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hxM, hxC⟩, rfl⟩
    refine ⟨⟨x, hxM, rfl⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    show π e * π x = π x * π e
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hxC e he)]
  · rintro _ ⟨⟨m, hmM, rfl⟩, hyC⟩
    refine ⟨m, ⟨hmM, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩, rfl⟩
    apply hπ
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hyC (π e) ⟨e, he, rfl⟩

theorem inD_map_inj {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hπ : Function.Injective π)
    {M B₁ D J : Subgroup A} (hIn : InD p B₁ 1 M D J) :
    InD p (B₁.map π) 1 (M.map π) (D.map π) (J.map π) := by
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [(MonoidHom.ker_eq_bot_iff π).2 hπ, Subgroup.card_bot]
    exact hp.not_dvd_one
  obtain ⟨⟨hDB, hD2, hDB2⟩, ⟨hJc, hBJ, hCM⟩, hE⟩ := hIn
  have hc : ∀ P : Subgroup A, Nat.card (P.map π) = Nat.card P := fun P =>
    Subgroup.card_map_of_injective hπ
  refine ⟨⟨Subgroup.map_mono hDB, by rw [hc]; exact hD2, by rw [hc, hc]; exact hDB2⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := glaPComponent_map hp π (coprime_inf_ker hp π hker _) hJc
    rwa [map_inf_centralizer_inj π hπ] at h
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨b * j * b⁻¹, (Subgroup.mem_normalizer_iff.1 (hBJ hb) j).1 hj, by simp⟩
    · rintro ⟨j, hj, hjz⟩
      refine ⟨b⁻¹ * j * b, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hBJ (B₁.inv_mem hb)) j).1 hj
        simpa using this
      · simp only [map_mul, map_inv]
        rw [hjz]; group
  · rintro _ ⟨b, hb, rfl⟩
    rw [centMod_iff, ← mem_centModSubgroup_map_iff hp π hker (hBJ hb), ← centMod_iff, hCM b hb]
    constructor
    · intro h; exact ⟨b, h, rfl⟩
    · rintro ⟨d, hd, hdb⟩
      have := hπ hdb
      rw [← this]; exact hd
  · intro hD2'
    have hDc : Nat.card D = p ^ 2 := by rw [← hc]; exact hD2'
    obtain ⟨E, hEB, hEl, hEc, hDE, hlay⟩ := hE hDc
    refine ⟨E.map π, Subgroup.map_mono hEB, CFSG.SectionRank.isElemAbelian_map hEl π,
      by rw [hc]; exact hEc, Subgroup.map_mono hDE, ?_⟩
    rw [← map_inf_centralizer_inj π hπ, glaPLayer_map_ne_bot_iff hp π hker]
    exact hlay

end Inj

section InjMore

variable {A Ω : Type} [Group A] [Finite A] [Group Ω] [Finite Ω]

theorem mem_normalizer_map_iff_inj (π : A →* Ω) (hπ : Function.Injective π) {J : Subgroup A} {b : A} :
    π b ∈ Subgroup.normalizer ((J.map π : Subgroup Ω) : Set Ω) ↔
      b ∈ Subgroup.normalizer (J : Set A) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 h (π y)
    constructor
    · intro hy
      obtain ⟨j, hj, hjy⟩ := h1.1 ⟨y, hy, rfl⟩
      have : π j = π (b * y * b⁻¹) := by rw [hjy]; simp
      rw [← hπ this]; exact hj
    · intro hy
      have : π y ∈ J.map π := by
        rw [h1]
        exact ⟨b * y * b⁻¹, hy, by simp⟩
      obtain ⟨j, hj, hjy⟩ := this
      rw [← hπ hjy]; exact hj
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨b * j * b⁻¹, (Subgroup.mem_normalizer_iff.1 h j).1 hj, by simp⟩
    · rintro ⟨j, hj, hjz⟩
      refine ⟨b⁻¹ * j * b, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h) j).1 hj
        simpa using this
      · simp only [map_mul, map_inv]
        rw [hjz]; group

theorem mem_centModSubgroup_map_iff_inj {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hπ : Function.Injective π)
    {J : Subgroup A} {b : A} :
    b ∈ centModSubgroup p J ↔ π b ∈ centModSubgroup p (J.map π) := by
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [(MonoidHom.ker_eq_bot_iff π).2 hπ, Subgroup.card_bot]
    exact hp.not_dvd_one
  by_cases hb : b ∈ Subgroup.normalizer (J : Set A)
  · exact mem_centModSubgroup_map_iff hp π hker hb
  · have h2 : π b ∉ Subgroup.normalizer ((J.map π : Subgroup Ω) : Set Ω) := fun h =>
      hb ((mem_normalizer_map_iff_inj π hπ).1 h)
    exact ⟨fun h' => absurd h'.1 hb, fun h' => absurd h'.1 h2⟩

theorem map_glaPLayer {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) (Y : Subgroup A) :
    (GLAPLayer p Y).map π = GLAPLayer p (Y.map π) := by
  unfold GLAPLayer
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_map hp π (coprime_inf_ker hp π hN Y) hJ)
  · refine sSup_le fun J' hJ' => ?_
    obtain ⟨J, hJ, rfl⟩ := exists_glaPComponent_map_eq hp π (coprime_inf_ker hp π hN Y) hJ'
    exact Subgroup.map_mono (le_sSup hJ)

end InjMore

section CentModCard

variable {A Ω : Type} [Group A] [Finite A] [Group Ω] [Finite Ω]

theorem map_inf_centModSubgroup {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    {B₁ K₀ : Subgroup A} (hB : B₁ ≤ Subgroup.normalizer (K₀ : Set A)) :
    (B₁ ⊓ centModSubgroup p K₀).map π = B₁.map π ⊓ centModSubgroup p (K₀.map π) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hxB, hxC⟩, rfl⟩
    exact ⟨⟨x, hxB, rfl⟩, (mem_centModSubgroup_map_iff hp π hN (hB hxB)).1 hxC⟩
  · rintro _ ⟨⟨x, hxB, rfl⟩, hyC⟩
    exact ⟨x, ⟨hxB, (mem_centModSubgroup_map_iff hp π hN (hB hxB)).2 hyC⟩, rfl⟩

theorem card_inf_centModSubgroup_map {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    {B₁ K₀ : Subgroup A} (hB1 : IsPGroup p B₁) (hB : B₁ ≤ Subgroup.normalizer (K₀ : Set A)) :
    Nat.card ↥(B₁.map π ⊓ centModSubgroup p (K₀.map π)) = Nat.card ↥(B₁ ⊓ centModSubgroup p K₀) := by
  rw [← map_inf_centModSubgroup hp π hN hB]
  exact card_map_of_isPGroup hp π hN (hB1.to_le inf_le_left)

end CentModCard

end CFSG.LocalAnalysis.GLTheoremA.S267

end
