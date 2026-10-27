module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Types
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Par

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.LinearGroups

section Perm

variable {F : Type} [Field F] [Finite F] (r : ℕ) [Fact r.Prime] [CharP F r]

theorem mem_pointSylow_iff {ω : Omega F} {g : ↥(coordinateG F)}
    (hg : (g : Equiv.Perm (Omega F)) none = ω) {u : ↥(coordinateG F)} :
    u ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)) ↔
      ((g⁻¹ * u * g : ↥(coordinateG F)) : Equiv.Perm (Omega F)) ∈ coordinateU F := by
  rw [pointSylow_eq r hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    coe_coordinateUSylow, Subgroup.mem_subgroupOf]
  simp [MulAut.inv_apply, mul_assoc]

theorem eq_of_mem_pointSylow_of_fix {ω x : Omega F} {u : ↥(coordinateG F)}
    (hu : u ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F))) (hu1 : u ≠ 1)
    (hx : (u : Equiv.Perm (Omega F)) x = x) : x = ω := by
  obtain ⟨g, hg⟩ := coordinateG_transitive F none ω
  have hmem := (mem_pointSylow_iff r hg).mp hu
  rw [coordinateU_eq_range] at hmem
  obtain ⟨b, hb⟩ := hmem
  have h1 : ((g⁻¹ * u * g : ↥(coordinateG F)) : Equiv.Perm (Omega F))
      ((g : Equiv.Perm (Omega F))⁻¹ x) = (g : Equiv.Perm (Omega F))⁻¹ x := by
    simp [Equiv.Perm.mul_apply, hx]
  rw [← hb] at h1
  cases hy : (g : Equiv.Perm (Omega F))⁻¹ x with
  | none =>
    have : x = (g : Equiv.Perm (Omega F)) none := by
      rw [← hy]
      simp
    rw [this, hg]
  | some y =>
    exfalso
    rw [hy] at h1
    simp only [translationHom, MonoidHom.coe_mk, OneHom.coe_mk, translation_some,
      Option.some_inj, add_eq_left] at h1
    have hb1 : b = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using h1
    rw [hb1, map_one] at hb
    apply hu1
    have h2 : g⁻¹ * u * g = 1 := Subtype.ext hb.symm
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group

omit [Finite F] in
theorem eq_translation_of_comm {B : Equiv.Perm (Omega F)} (h0 : B none = none)
    (hc : ∀ t : F, B * translation F t = translation F t * B) :
    ∃ c : F, B = translation F c := by
  have h1 : B (some 0) ≠ none := by
    intro h
    exact Option.some_ne_none _ (B.injective (h.trans h0.symm))
  obtain ⟨c, hc0⟩ := Option.ne_none_iff_exists'.mp h1
  refine ⟨c, Equiv.ext fun x => ?_⟩
  cases x with
  | none => rw [h0, translation_none]
  | some x =>
    have h2 := congrArg (fun f : Equiv.Perm (Omega F) => f (some 0)) (hc x)
    simp only [Equiv.Perm.mul_apply, translation_some, zero_add, hc0] at h2
    rw [h2, translation_some, add_comm]

omit [Finite F] [Fact r.Prime] in
theorem translation_pow_char (c : F) : translation F c ^ r = 1 := by
  have h : translation F c = translationHom F (Multiplicative.ofAdd c) := rfl
  rw [h, ← map_pow]
  have : (Multiplicative.ofAdd c) ^ r = 1 := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow]
  rw [this, map_one]

theorem aut_coordinateG_eq_conj {B : Equiv.Perm (Omega F)} {α : MulAut ↥(coordinateG F)}
    (hα : ∀ g : ↥(coordinateG F), ((α g : ↥(coordinateG F)) : Equiv.Perm (Omega F)) =
      B * g * B⁻¹)
    (hHH : ∀ S : Subgroup ↥(coordinateG F), IsPGroup r ↥S → (∀ x ∈ S, α x ∈ S) →
      ∀ x ∈ S, α x = x)
    {E : Subgroup ↥(coordinateG F)} (hnb : E ≠ ⊥) (hE : IsPGroup r ↥E)
    (hinv : ∀ x ∈ E, α x ∈ E) :
    ∃ B' : ↥(coordinateG F), B' ^ r = 1 ∧ ∀ g, α g = B' * g * B'⁻¹ := by
  classical
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  obtain ⟨ω, rfl⟩ := (pointSylow_bijective (K := F) r).2 S
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnb
  have huS : (u : ↥(coordinateG F)) ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)) :=
    hS u.2
  have hu1' : (u : ↥(coordinateG F)) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hωfix : ∀ v ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)),
      (v : Equiv.Perm (Omega F)) ω = ω := by
    have : ω ∈ {x : Omega F | ∀ v ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)),
        (v : Equiv.Perm (Omega F)) x = x} := by
      rw [pointSylow_fixed]
      rfl
    exact this
  have hSinv : ∀ x ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)),
      α x ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)) := by
    have hsurj : Function.Surjective α.toMonoidHom := α.surjective
    obtain ⟨ω', hω'⟩ := (pointSylow_bijective (K := F) r).2
      (Sylow.mapSurjective hsurj (pointSylow F r ω))
    have hcoe : (pointSylow F r ω' : Subgroup ↥(coordinateG F)) =
        (pointSylow F r ω : Subgroup ↥(coordinateG F)).map α.toMonoidHom := by
      rw [hω']
      exact Sylow.coe_mapSurjective hsurj _
    have h1 : α u ∈ (pointSylow F r ω' : Subgroup ↥(coordinateG F)) := by
      rw [hcoe]
      exact ⟨u, huS, rfl⟩
    have h2 : α u ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)) := hS (hinv u u.2)
    have hne : α u ≠ 1 := by
      intro h
      apply hu1'
      apply α.injective
      rw [h, map_one]
    have hωω : ω = ω' := eq_of_mem_pointSylow_of_fix r h1 hne (hωfix _ h2)
    intro x hx
    have : α x ∈ (pointSylow F r ω' : Subgroup ↥(coordinateG F)) := by
      rw [hcoe]
      exact ⟨x, hx, rfl⟩
    rwa [← hωω] at this
  have hfixS := hHH _ (pointSylow F r ω).isPGroup' hSinv
  have hcomm : ∀ x ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)),
      B * (x : Equiv.Perm (Omega F)) = (x : Equiv.Perm (Omega F)) * B := by
    intro x hx
    have h1 := hα x
    rw [hfixS x hx] at h1
    calc B * (x : Equiv.Perm (Omega F)) = (B * x * B⁻¹) * B := by group
      _ = (x : Equiv.Perm (Omega F)) * B := by rw [← h1]
  have hBω : B ω = ω := by
    refine eq_of_mem_pointSylow_of_fix r huS hu1' ?_
    have h1 := hcomm u huS
    have h2 := congrArg (fun f : Equiv.Perm (Omega F) => f ω) h1
    simp only [Equiv.Perm.mul_apply] at h2
    rw [hωfix u huS] at h2
    exact h2.symm
  obtain ⟨g, hg⟩ := coordinateG_transitive F none ω
  have hB'0 : ((g : Equiv.Perm (Omega F))⁻¹ * B * (g : Equiv.Perm (Omega F))) none = none := by
    simp only [Equiv.Perm.mul_apply]
    rw [hg, hBω, ← hg]
    simp
  have hB'c : ∀ t : F, ((g : Equiv.Perm (Omega F))⁻¹ * B * (g : Equiv.Perm (Omega F))) *
      translation F t = translation F t *
        ((g : Equiv.Perm (Omega F))⁻¹ * B * (g : Equiv.Perm (Omega F))) := by
    intro t
    let τ : ↥(coordinateG F) := ⟨translation F t, translation_mem_coordinateG t⟩
    have hmem : g * τ * g⁻¹ ∈ (pointSylow F r ω : Subgroup ↥(coordinateG F)) := by
      rw [mem_pointSylow_iff r hg]
      have : g⁻¹ * (g * τ * g⁻¹) * g = τ := by group
      rw [this]
      exact translation_mem_coordinateU t
    have h1 := hcomm _ hmem
    have h2 : B * ((g : Equiv.Perm (Omega F)) * translation F t *
        (g : Equiv.Perm (Omega F))⁻¹) = ((g : Equiv.Perm (Omega F)) * translation F t *
          (g : Equiv.Perm (Omega F))⁻¹) * B := h1
    calc ((g : Equiv.Perm (Omega F))⁻¹ * B * (g : Equiv.Perm (Omega F))) * translation F t
        = (g : Equiv.Perm (Omega F))⁻¹ * (B * ((g : Equiv.Perm (Omega F)) * translation F t *
            (g : Equiv.Perm (Omega F))⁻¹)) * (g : Equiv.Perm (Omega F)) := by group
      _ = (g : Equiv.Perm (Omega F))⁻¹ * (((g : Equiv.Perm (Omega F)) * translation F t *
            (g : Equiv.Perm (Omega F))⁻¹) * B) * (g : Equiv.Perm (Omega F)) := by rw [h2]
      _ = translation F t * ((g : Equiv.Perm (Omega F))⁻¹ * B *
            (g : Equiv.Perm (Omega F))) := by group
  obtain ⟨c, hc⟩ := eq_translation_of_comm hB'0 hB'c
  let τc : ↥(coordinateG F) := ⟨translation F c, translation_mem_coordinateG c⟩
  refine ⟨g * τc * g⁻¹, ?_, fun x => ?_⟩
  · have h1 : τc ^ r = 1 := Subtype.ext (translation_pow_char r c)
    rw [conj_pow, h1]
    group
  · apply Subtype.ext
    rw [hα x]
    have hBc : B = (g : Equiv.Perm (Omega F)) * translation F c *
        (g : Equiv.Perm (Omega F))⁻¹ := by
      rw [← hc]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hBc]
    rfl

end Perm

section Outer

variable {Y : Type} [Group Y]

theorem e1_l2 : E1Type FL2d := by
  classical
  intro r Y _ _ hr hr2 hY b hb1 hbr hHH E hE hinv
  obtain ⟨f, hf, h⟩ := hY
  obtain ⟨-, -, -, -, F, _, _, hcard, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data h
  have : Fact r.Prime := ⟨hr⟩
  have : CharP F r := charP_of_card_eq_pow hr hf hcard
  by_contra hne
  let ψ : Y ≃* ↥(coordinateG F) := e.trans (pslEquivCoordinateG F)
  obtain ⟨c, hcapp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_two_automorphism_semilinear_isomorphism
      F
  let α : MulAut ↥(coordinateG F) := MulAut.congr ψ b
  let B : coordinateE F := c.symm α
  have hα : ∀ g : ↥(coordinateG F), ((α g : ↥(coordinateG F)) : Equiv.Perm (Omega F)) =
      (B : Equiv.Perm (Omega F)) * g * (B : Equiv.Perm (Omega F))⁻¹ := by
    intro g
    rw [← hcapp B g, MulEquiv.apply_symm_apply]
  have hαψ : ∀ y : Y, α (ψ y) = ψ (b y) := by
    intro y
    simp [α, MulAut.congr_apply]
  obtain ⟨B', hB'r, hB'⟩ := aut_coordinateG_eq_conj r (B := (B : Equiv.Perm (Omega F))) (α := α)
    hα (fun S hS hSinv x hx => by
      have h1 := hHH (S.comap ψ.toMonoidHom) (hS.comap_of_injective ψ.toMonoidHom ψ.injective)
        (fun y hy => by
          change ψ (b y) ∈ S
          rw [← hαψ]
          exact hSinv _ hy) (ψ.symm x) (by simpa using hx)
      have h2 := congrArg ψ h1
      rw [← hαψ] at h2
      simpa using h2)
    (E := E.map ψ.toMonoidHom) (by
      intro h0
      exact hne ((Subgroup.map_eq_bot_iff_of_injective E ψ.injective).mp h0))
    (hE.map ψ.toMonoidHom) (by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨b y, hinv y hy, (hαψ y).symm⟩)
  have hbu : b = MulAut.conj (ψ.symm B') := by
    ext y
    apply ψ.injective
    rw [← hαψ, hB', MulAut.conj_apply]
    simp
  have hbr1 : b ^ r = 1 := by
    rw [hbu, ← map_pow, ← map_pow, hB'r, map_one, map_one]
  have hdvd : orderOf b ∣ r := orderOf_dvd_of_pow_eq_one hbr1
  rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
  · exact hb1 (orderOf_eq_one_iff.mp h1)
  · exact hbr (h1 ▸ dvd_rfl)

end Outer

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
