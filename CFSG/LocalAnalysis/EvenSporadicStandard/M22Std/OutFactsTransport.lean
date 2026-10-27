module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.DataTransport

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {X Y : Type} [Group X] [Group Y]

theorem congr_conj (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_apply_mk (e : X ≃* Y) (α : MulAut X) (x : X) :
    MulAut.congr e α (e x) = e (α x) := by
  simp [MulAut.congr_apply]

section General

variable (e : X ≃* Y) (φ : MulAut X ≃* MulAut Y)
  (hc : ∀ x, φ (MulAut.conj x) = MulAut.conj (e x)) (ha : ∀ α x, φ α (e x) = e (α x))

include ha in
theorem symm_apply_mk (β : MulAut Y) (x : X) : φ.symm β x = e.symm (β (e x)) := by
  have h := ha (φ.symm β) x
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

include hc in
theorem symm_conj (y : Y) : φ.symm (MulAut.conj y) = MulAut.conj (e.symm y) := by
  have h := hc (e.symm y)
  rw [e.apply_symm_apply] at h
  rw [← h, MulEquiv.symm_apply_apply]

theorem mem_map_phi {S : Subgroup (MulAut X)} {β : MulAut Y} :
    β ∈ S.map φ.toMonoidHom ↔ φ.symm β ∈ S :=
  Subgroup.mem_map_equiv

include hc in
theorem innerImage_map' (F : Subgroup X) :
    (innerImage X F).map φ.toMonoidHom = innerImage Y (F.map e.toMonoidHom) := by
  ext β
  constructor
  · rintro ⟨α, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨e f, ⟨f, hf, rfl⟩, (hc f).symm⟩
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨MulAut.conj f, ⟨f, hf, rfl⟩, hc f⟩

include hc in
theorem innerImage_top_map' :
    (innerImage X ⊤).map φ.toMonoidHom = innerImage Y ⊤ := by
  rw [innerImage_map' e φ hc, Subgroup.map_top_of_surjective _ e.surjective]

include ha in
theorem autOrbit_map' (S : Subgroup (MulAut X)) (x : X) :
    autOrbit (S.map φ.toMonoidHom) (e x) = e '' autOrbit S x := by
  ext y
  constructor
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨α x, ⟨α, hα, rfl⟩, (ha α x).symm⟩
  · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    exact ⟨φ α, ⟨α, hα, rfl⟩, (ha α x).symm⟩

theorem autConjClass_map' (S : Subgroup (MulAut X)) (β : MulAut X) :
    autConjClass (S.map φ.toMonoidHom) (φ β) = φ '' autConjClass S β := by
  ext γ
  constructor
  · rintro ⟨α', hα', rfl⟩
    obtain ⟨α, hα, rfl⟩ := hα'
    exact ⟨α * β * α⁻¹, ⟨α, hα, rfl⟩, by rw [map_mul, map_mul, map_inv]; rfl⟩
  · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    exact ⟨φ α, ⟨α, hα, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

include hc ha in
theorem SylowWitness.map' {S : Subgroup (MulAut X)} {t : X} {F : Subgroup X}
    (W : SylowWitness X S t F) :
    SylowWitness Y (S.map φ.toMonoidHom) (e t) (F.map e.toMonoidHom) := by
  have hF : ∀ x, e x ∈ F.map e.toMonoidHom ↔ x ∈ F := fun x =>
    Subgroup.mem_map_iff_mem e.injective
  have hsymm : ∀ β : MulAut Y, φ (φ.symm β) = β := fun β => φ.apply_symm_apply β
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, W.sq, map_one]
  · exact fun h => W.ne (e.injective (by rw [h, map_one]))
  · obtain ⟨g, hg⟩ := W.fourth
    exact ⟨e g, by simp only [← map_mul, hg]⟩
  · rw [mem_map_phi, symm_conj e φ hc, e.symm_apply_apply]
    exact W.mem
  · intro α hα
    have hα' : φ.symm α ∈ S := (mem_map_phi φ).1 hα
    have key := W.center (φ.symm α) hα'
    have h1 : (∀ β ∈ S.map φ.toMonoidHom, β * α = α * β) ↔
        ∀ β' ∈ S, β' * φ.symm α = φ.symm α * β' := by
      constructor
      · intro hc' β' hβ'
        have := hc' (φ β') ((mem_map_phi φ).2 (by rwa [MulEquiv.symm_apply_apply]))
        have h2 := congrArg φ.symm this
        simpa only [map_mul, MulEquiv.symm_apply_apply] using h2
      · intro hc' β hβ
        have := hc' (φ.symm β) ((mem_map_phi φ).1 hβ)
        have h2 := congrArg φ this
        simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
    have h2 : (α = 1 ∨ α = MulAut.conj (e t)) ↔
        (φ.symm α = 1 ∨ φ.symm α = MulAut.conj t) := by
      constructor
      · rintro (h | h)
        · left; rw [h, map_one]
        · right; rw [h, symm_conj e φ hc, e.symm_apply_apply]
      · rintro (h | h)
        · left
          have := congrArg φ h
          rwa [hsymm, map_one] at this
        · right
          have := congrArg φ h
          rwa [hsymm, hc] at this
    rw [h1, h2]
    exact key
  · exact (hF t).2 W.t_mem
  · have := NData.map (φ := e.toMonoidHom) e.injective W.nd
    rwa [MonoidHom.range_eq_top_of_surjective _ e.surjective] at this
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective e.injective]
      exact W.e16.card
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, W.e16.sq x hx, map_one]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, W.e16.comm x hx y hy]
    · intro β hβ y
      obtain ⟨x, rfl⟩ := e.surjective y
      have h1 : β (e x) = e ((φ.symm β) x) := by
        rw [symm_apply_mk e φ ha, e.apply_symm_apply]
      rw [h1, hF, hF]
      exact W.e16.normal (φ.symm β) ((mem_map_phi φ).1 hβ) x
    · rw [← innerImage_map' e φ hc]
      exact Subgroup.map_mono W.e16.inner_le
    · intro β hβ
      have h1 : ∀ x ∈ F, φ.symm β x = x := by
        intro x hx
        rw [symm_apply_mk e φ ha, hβ (e x) ((hF x).2 hx), e.symm_apply_apply]
      have h2 := Subgroup.mem_map_of_mem φ.toMonoidHom (W.e16.cent (φ.symm β) h1)
      rw [innerImage_map' e φ hc] at h2
      simpa only [MulEquiv.coe_toMonoidHom, hsymm] using h2
    · obtain ⟨x, hx, hx1, h8⟩ := W.e16.orbit8
      refine ⟨e x, (hF x).2 hx, fun h => hx1 (e.injective (by rw [h, map_one])), ?_⟩
      rw [autOrbit_map' e φ ha, Set.ncard_image_of_injective _ e.injective]
      exact h8
    · intro E hES hEn hEc hEsq hEcard hEself hE8
      set E' : Subgroup (MulAut X) := E.map φ.symm.toMonoidHom with hE'
      have hmemE' : ∀ γ, γ ∈ E' ↔ φ γ ∈ E := fun γ => by
        rw [hE', Subgroup.mem_map_equiv, MulEquiv.symm_symm]
      have hmemS : ∀ γ, γ ∈ S ↔ φ γ ∈ S.map φ.toMonoidHom := fun γ => by
        rw [mem_map_phi, MulEquiv.symm_apply_apply]
      have := W.e16.unique E' ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · have h3 := congrArg (fun K => K.map φ.toMonoidHom) this
        rw [innerImage_map' e φ hc] at h3
        rw [← h3, hE', Subgroup.map_map]
        ext γ
        simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
          Function.comp_apply]
        constructor
        · intro hγ
          exact ⟨γ, hγ, hsymm γ⟩
        · rintro ⟨δ, hδ, rfl⟩
          rwa [hsymm]
      · intro γ hγ
        exact (hmemS γ).2 (hES ((hmemE' γ).1 hγ))
      · intro α hα β hβ
        rw [hmemE'] at hβ ⊢
        have := hEn (φ α) ((hmemS α).1 hα) (φ β) hβ
        simpa only [map_mul, map_inv] using this
      · intro α hα β hβ
        rw [hmemE'] at hα hβ
        have := hEc _ hα _ hβ
        have h2 := congrArg φ.symm this
        simpa only [map_mul, MulEquiv.symm_apply_apply] using h2
      · intro α hα
        rw [hmemE'] at hα
        have := hEsq _ hα
        have h2 := congrArg φ.symm this
        simpa only [map_mul, MulEquiv.symm_apply_apply, map_one] using h2
      · have : Nat.card E' = Nat.card E :=
          Nat.card_congr
            (Subgroup.equivMapOfInjective E φ.symm.toMonoidHom φ.symm.injective).toEquiv.symm
        rw [this]
        exact hEcard
      · intro γ hγ hcomm
        rw [hmemE']
        refine hEself (φ γ) ((hmemS γ).1 hγ) (fun β hβ => ?_)
        have h0 : φ.symm β ∈ E' := by rw [hmemE', hsymm]; exact hβ
        have := hcomm (φ.symm β) h0
        have h2 := congrArg φ this
        simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
      · obtain ⟨β, hβ, hβ1, hβ8⟩ := hE8
        have hmem : φ.symm β ∈ E' := by rw [hmemE', hsymm]; exact hβ
        refine ⟨φ.symm β, hmem, fun h => hβ1 (by simpa using congrArg φ h), ?_⟩
        have h1 := autConjClass_map' φ S (φ.symm β)
        rw [hsymm] at h1
        rw [h1, Set.ncard_image_of_injective _ φ.injective] at hβ8
        exact hβ8
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective S φ.toMonoidHom φ.injective).toEquiv.symm]
    exact W.card_S
  · obtain ⟨s, hs, hs1, hs2⟩ := W.outer_inv
    refine ⟨φ s, Subgroup.mem_map_of_mem _ hs, ?_, ?_⟩
    · rw [← innerImage_top_map' e φ hc]
      intro h
      exact hs1 ((Subgroup.mem_map_iff_mem φ.injective).1 h)
    · rw [← map_mul, hs2, map_one]
  · have hbij : ∀ P : MulAut X → Prop, ∀ Q : MulAut Y → Prop, (∀ s, Q (φ s) ↔ P s) →
        {s : MulAut Y | Q s}.ncard = {s : MulAut X | P s}.ncard := by
      intro P Q hPQ
      have : {s : MulAut Y | Q s} = φ '' {s : MulAut X | P s} := by
        ext s
        constructor
        · intro hs
          exact ⟨φ.symm s, (hPQ _).1 (by rw [hsymm]; exact hs), hsymm s⟩
        · rintro ⟨s', hs', rfl⟩
          exact (hPQ s').2 hs'
      rw [this, Set.ncard_image_of_injective _ φ.injective]
    have hnot : ∀ s, φ s ∈ innerImage Y ⊤ ↔ s ∈ innerImage X ⊤ := fun s => by
      rw [← innerImage_top_map' e φ hc]
      exact Subgroup.mem_map_iff_mem φ.injective
    have hS : ∀ s, φ s ∈ S.map φ.toMonoidHom ↔ s ∈ S := fun s =>
      Subgroup.mem_map_iff_mem φ.injective
    rw [hbij (fun s => s ∈ S ∧ s ∉ innerImage X ⊤ ∧ s * s = 1)
      (fun s => s ∈ S.map φ.toMonoidHom ∧ s ∉ innerImage Y ⊤ ∧ s * s = 1) (fun s => by
        rw [hS, hnot, ← map_mul]
        simp only [map_eq_one_iff φ φ.injective]),
      hbij (fun s => s ∈ S ∧ s ∉ innerImage X ⊤ ∧ s * s = MulAut.conj t)
      (fun s => s ∈ S.map φ.toMonoidHom ∧ s ∉ innerImage Y ⊤ ∧ s * s = MulAut.conj (e t))
      (fun s => by
        rw [hS, hnot, ← map_mul, ← hc t]
        exact and_congr_right fun _ => and_congr_right fun _ => φ.injective.eq_iff)]
    exact W.count_ne

end General

end CFSG.EvenSporadicStandard.M22Std
