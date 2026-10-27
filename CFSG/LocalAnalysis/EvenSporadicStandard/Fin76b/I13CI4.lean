module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Ctx

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem aut_conj_conj {G : Type*} [Group G] {E : Subgroup G} (φ : MulAut ↥E) (e : ↥E) :
    φ * MulAut.conj e * φ⁻¹ = MulAut.conj (φ e) := by
  refine MulEquiv.ext fun f => ?_
  show φ (e * φ.symm f * e⁻¹) = φ e * f * (φ e)⁻¹
  rw [map_mul, map_mul, map_inv]
  simp

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem conj_eq_one_iff {e : ↥E} : (MulAut.conj e : MulAut ↥E) = 1 ↔ (e : G) = 1 ∨ (e : G) = t := by
  constructor
  · intro he
    have hcomm : ∀ f ∈ E, f * (e : G) = e * f := by
      intro f hf
      have := congrArg (fun φ : MulAut ↥E => ((φ ⟨f, hf⟩ : ↥E) : G)) he
      have h5 : (e : G) * f * (e : G)⁻¹ = f := by
        simpa [MulAut.conj_apply] using this
      calc f * (e : G) = ((e : G) * f * (e : G)⁻¹) * e := by rw [h5]
        _ = e * f := by group
    exact c.h.conf.econfig.center e e.2 hcomm
  · rintro (h | h)
    · have : e = 1 := Subtype.ext h
      rw [this, map_one]
    · refine MulEquiv.ext fun f => ?_
      apply Subtype.ext
      show (e : G) * (f : G) * (e : G)⁻¹ = f
      rw [h]
      have := c.h.t_comm_E (f : G) f.2
      calc t * (f : G) * t⁻¹ = (t * f) * t⁻¹ := rfl
        _ = f := by rw [← this]; group


theorem card_cent_inn_le {φ : MulAut ↥E} (hfix : Nat.card {e : ↥E // φ e = e} = 4) :
    Nat.card ↥(innAutE E ⊓ centralizer ({φ} : Set (MulAut ↥E))) ≤ 4 := by
  classical
  set K : Subgroup (MulAut ↥E) := innAutE E ⊓ centralizer ({φ} : Set (MulAut ↥E)) with hK
  let conjE : ↥E →* MulAut ↥E := MulAut.conj
  set D : Subgroup ↥E := K.comap conjE with hD
  have hmemD : ∀ e : ↥E, e ∈ D ↔ conjE e ∈ centralizer ({φ} : Set (MulAut ↥E)) := by
    intro e
    simp only [hD, hK, mem_comap, mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨⟨e, rfl⟩, h⟩⟩
  have hcentral : ∀ u : ↥E, (MulAut.conj u : MulAut ↥E) = 1 → ∀ f : ↥E, u * f = f * u := by
    intro u hu f
    rcases (c.conj_eq_one_iff).1 hu with h | h
    · have : u = 1 := Subtype.ext h
      rw [this]
      simp
    · apply Subtype.ext
      show (u : G) * f = f * u
      rw [h]
      exact (c.h.t_comm_E (f : G) f.2).symm
  have hcentD : ∀ e : ↥E, e ∈ D → (MulAut.conj (e⁻¹ * φ e) : MulAut ↥E) = 1 := by
    intro e he
    have h1 : MulAut.conj e * φ = φ * MulAut.conj e :=
      mem_centralizer_singleton_iff.1 ((hmemD e).1 he)
    have h2 := aut_conj_conj φ e
    have h3 : MulAut.conj (φ e) = MulAut.conj e := by
      rw [← h2, ← h1]
      group
    rw [map_mul, map_inv, h3]
    group
  let Φ : ↥D →* ↥E := MonoidHom.mk' (fun d => (d : ↥E)⁻¹ * φ (d : ↥E)) (by
    intro d d'
    have hu := hcentral _ (hcentD d d.2)
    show ((d * d' : ↥D) : ↥E)⁻¹ * φ ((d * d' : ↥D) : ↥E) =
      ((d : ↥E)⁻¹ * φ d) * ((d' : ↥E)⁻¹ * φ d')
    calc ((d * d' : ↥D) : ↥E)⁻¹ * φ ((d * d' : ↥D) : ↥E)
        = (d' : ↥E)⁻¹ * ((d : ↥E)⁻¹ * φ d) * φ d' := by
          show ((d : ↥E) * d')⁻¹ * φ ((d : ↥E) * d') = _
          rw [map_mul, mul_inv_rev]
          group
      _ = ((d : ↥E)⁻¹ * φ d) * (d' : ↥E)⁻¹ * φ d' := by rw [(hu (d' : ↥E)⁻¹).symm]
      _ = ((d : ↥E)⁻¹ * φ d) * ((d' : ↥E)⁻¹ * φ d') := by group)
  have hrange : Nat.card Φ.range ≤ 2 := by
    have ht' : t ∈ E := c.h.t_mem_E
    have hsub : (Φ.range : Set ↥E) ⊆ {1, ⟨t, ht'⟩} := by
      rintro _ ⟨d, rfl⟩
      rcases (c.conj_eq_one_iff).1 (hcentD d d.2) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_insert_le (1 : ↥E) ({⟨t, ht'⟩} : Set ↥E)
    rw [Set.ncard_singleton] at h2
    rw [← Nat.card_coe_set_eq] at h1
    exact h1.trans h2
  have hker : Nat.card Φ.ker ≤ 4 := by
    have hinj : Function.Injective (fun d : Φ.ker => (⟨((d : ↥D) : ↥E), by
        have h0 : ((d : ↥D) : ↥E)⁻¹ * φ ((d : ↥D) : ↥E) = 1 := d.2
        exact (inv_mul_eq_one.1 h0).symm⟩ : {e : ↥E // φ e = e})) := by
      intro a b hab
      have h5 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h5)
    have := Nat.card_le_card_of_injective _ hinj
    rwa [hfix] at this
  have hDcard : Nat.card ↥D ≤ 8 := by
    have h1 := Subgroup.card_ker_mul_card_range Φ
    calc Nat.card ↥D = Nat.card Φ.ker * Nat.card Φ.range := h1.symm
      _ ≤ 4 * 2 := Nat.mul_le_mul hker hrange
  let g : ↥D →* MulAut ↥E := conjE.comp D.subtype
  have hgrange : g.range = K := by
    ext j
    constructor
    · rintro ⟨d, rfl⟩
      exact d.2
    · intro hj
      obtain ⟨e, rfl⟩ := hj.1
      exact ⟨⟨e, hj⟩, rfl⟩
  have hgker : 2 ≤ Nat.card g.ker := by
    have ht' : t ∈ E := c.h.t_mem_E
    have htD : (⟨t, ht'⟩ : ↥E) ∈ D := by
      rw [hmemD]
      have : conjE ⟨t, ht'⟩ = 1 := (c.conj_eq_one_iff).2 (Or.inr rfl)
      rw [this]
      exact one_mem _
    let f : Bool → g.ker := fun b =>
      if b then ⟨⟨⟨t, ht'⟩, htD⟩, (c.conj_eq_one_iff).2 (Or.inr rfl)⟩ else 1
    have hinj : Function.Injective f := by
      intro a b hab
      cases a <;> cases b
      · rfl
      · exfalso
        have h5 := congrArg (fun u : g.ker => (((u : ↥D) : ↥E) : G)) hab
        have h6 : (1 : G) = t := h5
        exact c.h.t_ne h6.symm
      · exfalso
        have h5 := congrArg (fun u : g.ker => (((u : ↥D) : ↥E) : G)) hab
        have h6 : t = (1 : G) := h5
        exact c.h.t_ne h6
      · rfl
    have := Nat.card_le_card_of_injective f hinj
    simpa using this
  have h1 := Subgroup.card_ker_mul_card_range g
  rw [hgrange] at h1
  by_contra hcon
  have : 2 * 5 ≤ Nat.card g.ker * Nat.card K := Nat.mul_le_mul hgker (by omega)
  omega

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
