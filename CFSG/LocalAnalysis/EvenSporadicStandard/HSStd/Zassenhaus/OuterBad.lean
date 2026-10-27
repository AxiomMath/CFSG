module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterGood

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

theorem commutator_D_eq (h : HSOuterSetup G L t S z n v s) :
    ⁅centralizer ({t} : Set G) ⊓ centralizer ({v} : Set G),
      centralizer ({t} : Set G) ⊓ centralizer ({v} : Set G)⁆ = derivedCentralizerIn L v := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    exact commutator_mem_derived h (mem_centralizer_singleton_iff.1 ha.1)
      (mem_centralizer_singleton_iff.1 ha.2) (mem_centralizer_singleton_iff.1 hb.1)
      (mem_centralizer_singleton_iff.1 hb.2)
  · rw [derivedCentralizerIn_eq_commutator]
    apply Subgroup.commutator_mono <;>
    · intro y hy
      exact ⟨mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h.t_mem y hy.2), hy.1⟩

theorem mem_normalizer_derived (h : HSOuterSetup G L t S z n v s) {g : G}
    (hgv : g * v = v * g) (hgt : g * t * g⁻¹ = t * v) :
    g ∈ normalizer ((derivedCentralizerIn L v : Subgroup G) : Set G) := by
  have hv2 : v * v = 1 := h.ctx.v_sq
  have ht2 : t * t = 1 := t_sq h
  have htv : t * v = v * t := h.t_comm_v
  have hgvi : g * v * g⁻¹ = v := by rw [hgv]; group
  have hgt' : g⁻¹ * t * g = t * v := by
    have h1 : t = g⁻¹ * (t * v) * g := by rw [← hgt]; group
    have h2 : g⁻¹ * (t * v) * g = (g⁻¹ * t * g) * (g⁻¹ * v * g) := by group
    have h3 : g⁻¹ * v * g = v := by
      have : v = g⁻¹ * (g * v * g⁻¹) * g := by group
      rw [hgvi] at this
      exact this.symm
    rw [h3] at h2
    have h4 : t = (g⁻¹ * t * g) * v := by rw [← h2]; exact h1
    calc g⁻¹ * t * g = ((g⁻¹ * t * g) * v) * v := by rw [mul_assoc _ v v, hv2, mul_one]
      _ = t * v := by rw [← h4]
  apply mem_normalizer_of_map_le
  rw [← commutator_D_eq h, Subgroup.map_commutator]
  apply Subgroup.commutator_mono <;>
  · rintro _ ⟨d, ⟨hd1, hd2⟩, rfl⟩
    have hdt : d * t = t * d := mem_centralizer_singleton_iff.1 hd1
    have hdv : d * v = v * d := mem_centralizer_singleton_iff.1 hd2
    refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
    ·
      have e1 : (MulAut.conj g).toMonoidHom d = g * d * g⁻¹ := by simp [MulAut.conj_apply]
      rw [e1]
      have e2 : g * d * g⁻¹ * t * (g * d * g⁻¹)⁻¹ = t := by
        calc g * d * g⁻¹ * t * (g * d * g⁻¹)⁻¹
            = g * d * (g⁻¹ * t * g) * d⁻¹ * g⁻¹ := by group
          _ = g * d * (t * v) * d⁻¹ * g⁻¹ := by rw [hgt']
          _ = g * (d * t * d⁻¹) * (d * v * d⁻¹) * g⁻¹ := by group
          _ = g * t * v * g⁻¹ := by
            rw [hdt, hdv]; group
          _ = (g * t * g⁻¹) * (g * v * g⁻¹) := by group
          _ = (t * v) * v := by rw [hgt, hgvi]
          _ = t := by rw [mul_assoc, hv2, mul_one]
      calc g * d * g⁻¹ * t = (g * d * g⁻¹ * t * (g * d * g⁻¹)⁻¹) * (g * d * g⁻¹) := by group
        _ = t * (g * d * g⁻¹) := by rw [e2]
    · have e1 : (MulAut.conj g).toMonoidHom d = g * d * g⁻¹ := by simp [MulAut.conj_apply]
      rw [e1]
      calc g * d * g⁻¹ * v = g * d * (g⁻¹ * v * g) * g⁻¹ := by group
        _ = g * d * v * g⁻¹ := by
          have : g⁻¹ * v * g = v := by
            have : v = g⁻¹ * (g * v * g⁻¹) * g := by group
            rw [hgvi] at this
            exact this.symm
          rw [this]
        _ = g * (d * v) * g⁻¹ := by group
        _ = g * (v * d) * g⁻¹ := by rw [hdv]
        _ = g * v * d * g⁻¹ := by group
        _ = (g * v * g⁻¹) * (g * d * g⁻¹) := by group
        _ = v * (g * d * g⁻¹) := by rw [hgvi]

theorem exists_inner_Y (h : HSOuterSetup G L t S z n v s) {g : G}
    (hg : g ∈ normalizer ((derivedCentralizerIn L v : Subgroup G) : Set G)) :
    ∃ y ∈ centralizer ({v} : Set G) ⊓ L,
      ∀ l ∈ derivedCentralizerIn L v, g * l * g⁻¹ = y * l * y⁻¹ := by
  obtain ⟨e⟩ := h.ctx.v_cls
  set T := centralizer ({v} : Set G) ⊓ L with hT
  let ψ : Perm (Fin 8) →* G := T.subtype.comp e.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hrange : ψ.range = T := by
    ext g
    constructor
    · rintro ⟨σ, rfl⟩
      exact (e.symm σ).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [ψ]⟩
  have hΛ : derivedCentralizerIn L v = (alternatingGroup (Fin 8)).map ψ :=
    map_commutator_range ψ hψ T hrange
  set N : Subgroup G := normalizer ((derivedCentralizerIn L v : Subgroup G) : Set G) with hN
  have hψN : ∀ σ, ψ σ ∈ N := by
    intro σ
    rw [hN, mem_set_normalizer_iff]
    intro l
    have hy : ψ σ ∈ T := (e.symm σ).2
    constructor
    · exact fun hl => conj_mem_derived hy hl
    · intro hl
      have := conj_mem_derived (T.inv_mem hy) hl
      simpa [mul_assoc] using this
  let ψ' : Perm (Fin 8) →* N := ψ.codRestrict N hψN
  have hψ' : Function.Injective ψ' := fun a b hab => by
    have h1 : ((ψ' a : N) : G) = ((ψ' b : N) : G) := by rw [hab]
    exact hψ h1
  have hmapeq : (alternatingGroup (Fin 8)).map ψ' =
      (derivedCentralizerIn L v).subgroupOf N := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact mem_subgroupOf.2 (hΛ ▸ ⟨a, ha, rfl⟩)
    · intro hx
      obtain ⟨a, ha, hax⟩ := (hΛ ▸ mem_subgroupOf.1 hx : (x : G) ∈ (alternatingGroup (Fin 8)).map ψ)
      exact ⟨a, ha, Subtype.ext hax⟩
  have hN' : ((alternatingGroup (Fin 8)).map ψ').Normal := by
    rw [hmapeq]
    exact Subgroup.normal_in_normalizer
  obtain ⟨σ, hσ⟩ := exists_conj_perm_eight ψ' hψ' hN' ⟨g, hg⟩
  refine ⟨ψ σ, (e.symm σ).2, fun l hl => ?_⟩
  have hlN : l ∈ N := le_normalizer hl
  have := hσ ⟨l, hlN⟩ (hmapeq ▸ mem_subgroupOf.2 hl)
  exact congrArg Subtype.val this

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
