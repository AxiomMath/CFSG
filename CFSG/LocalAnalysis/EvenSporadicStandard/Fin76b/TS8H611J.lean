module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611I

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

@[expose] noncomputable def wThetaHom {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) :
    ↥(Wsub h hα (zpowers α)) →* ↥E where
  toFun w := ⟨(w : G) * (z * (w : G) * z⁻¹), by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmem, -⟩ :=
      h.lemma611Cl_of_pairing hα hF hM hp
    exact hmem _ w.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' w w' := Subtype.ext (h.theta_mul hα hF hM hp w.2 w'.2)

theorem card_W1 {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) :
    Nat.card ↥(Wsub h hα (zpowers α)) = 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsurj⟩ :=
    h.lemma611Cl_of_pairing hα hF hM hp
  set f := h.wThetaHom hα hF hM hp with hf
  have htW : t ∈ Wsub h hα (zpowers α) := h.Zg_mem_Wsub hα _ (h.t_mem_Zg hα)
  have hker : f.ker = zpowers (⟨t, htW⟩ : ↥(Wsub h hα (zpowers α))) := by
    ext w
    have hw := w.2
    rw [MonoidHom.mem_ker, mem_zpowers_iff]
    constructor
    · intro h1
      have h2 : (w : G) * (z * (w : G) * z⁻¹) = 1 := congrArg Subtype.val h1
      rcases (h.theta_eq_one_iff hα hw).1 h2 with e | e
      · exact ⟨0, Subtype.ext (by simp [e])⟩
      · exact ⟨1, Subtype.ext (by simp [e])⟩
    · rintro ⟨k, hk⟩
      have hsq : (⟨t, htW⟩ : ↥(Wsub h hα (zpowers α))) * ⟨t, htW⟩ = 1 :=
        Subtype.ext h.t_sq
      rcases mem_zpowers_sq_eq_one hsq (mem_zpowers_iff.2 ⟨k, rfl⟩) with e | e
      · rw [← hk, e, map_one]
      · rw [← hk, e]
        exact Subtype.ext (by
          show t * (z * t * z⁻¹) = 1
          rw [h.z_conj_t, h.t_sq])
  have hcardker : Nat.card f.ker = 2 := by
    rw [hker, Nat.card_zpowers]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using h.t_sq)
    · intro e
      exact h.t_ne (congrArg Subtype.val e)
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff]
    intro e _
    obtain ⟨w, hw, hwe⟩ := hsurj e e.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwe.symm⟩
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, Subgroup.card_top, hcardker, h.wf.card_E] at h1
  omega

theorem card_W2 {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) :
    Nat.card ↥(Wsub h hα (zpowers (α * t))) = 64 := by
  rw [← h.card_W1 hα hF hM hp]
  have hzz : ∀ u : G, z * (z * u * z⁻¹) * z⁻¹ = u := fun u => by
    calc z * (z * u * z⁻¹) * z⁻¹ = (z * z) * u * (z * z)⁻¹ := by group
      _ = u := by rw [h.z_sq]; group
  refine Nat.card_congr ⟨fun w => ⟨z * (w : G) * z⁻¹, h.conj_z_W2 hα w.2⟩,
    fun w => ⟨z * (w : G) * z⁻¹, h.conj_z_W1 hα w.2⟩, fun w => ?_, fun w => ?_⟩
  · exact Subtype.ext (hzz _)
  · exact Subtype.ext (hzz _)

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
