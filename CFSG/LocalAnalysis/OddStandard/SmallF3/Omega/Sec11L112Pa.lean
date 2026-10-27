module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Pm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Au
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace Sec11Perm

variable {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem relabel (h : Sec11Perm A M Alt φ) (π : Equiv.Perm (Fin 6)) [hN : Alt.Normal] :
    Sec11Perm A M Alt (fun v => φ (permVec π v)) where
  mem v := h.mem _
  mul v w := by
    show φ (permVec π (v + w)) = φ (permVec π v) * φ (permVec π w)
    rw [sec11_permVec_add]
    exact h.mul _ _
  ker v := by
    show φ (permVec π v) = 1 ↔ _
    rw [h.ker, sec11_permVec_eq_zero_iff, sec11_permVec_eq_one_iff]
  surj a ha := by
    obtain ⟨w, hw⟩ := h.surj a ha
    refine ⟨permVec π⁻¹ w, ?_⟩
    show φ (permVec π (permVec π⁻¹ w)) = a
    rw [← permVec_mul, mul_inv_cancel, permVec_one]
    exact hw
  act m hm := by
    obtain ⟨σ, hσ, hact⟩ := h.act m hm
    refine ⟨π⁻¹ * σ * π, ?_, fun v => ?_⟩
    · simpa using hN.conj_mem σ hσ π⁻¹
    · show m * φ (permVec π v) * m⁻¹ = φ (permVec π (permVec (π⁻¹ * σ * π) v))
      rw [hact, ← permVec_mul, ← permVec_mul]
      congr 2
      group
  act_surj σ hσ := by
    obtain ⟨m, hm, hact⟩ := h.act_surj (π * σ * π⁻¹) (hN.conj_mem σ hσ π)
    refine ⟨m, hm, fun v => ?_⟩
    show m * φ (permVec π v) * m⁻¹ = φ (permVec π (permVec σ v))
    rw [hact, ← permVec_mul, ← permVec_mul]
    congr 2
    group

theorem toIsPermModuleMod (h : Sec11Perm A M Alt φ) (hM : M ≤ normalizer (A : Set G)) :
    IsPermModuleMod (n := 6) (fun _ => True) ({0, fun _ => 1} : Set (Fin 6 → ZMod 2))
      φ A ⊥ M Alt := by
  refine ⟨bot_le, ?_, hM, ?_, fun v _ => h.mem v, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    exact Subgroup.normal_bot
  · intro m _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  · intro v w _ _
    rw [Subgroup.mem_bot, h.mul]
    group
  · intro v _
    rw [Subgroup.mem_bot, h.ker]
    exact Iff.rfl
  · intro x hx
    obtain ⟨v, hv⟩ := h.surj x hx
    exact ⟨v, trivial, by rw [Subgroup.mem_bot, hv]; group⟩
  · intro m hm
    obtain ⟨σ, hσ, hact⟩ := h.act m hm
    exact ⟨σ, hσ, fun v _ => by rw [Subgroup.mem_bot, hact]; group⟩
  · intro σ hσ
    obtain ⟨m, hm, hact⟩ := h.act_surj σ hσ
    exact ⟨m, hm, fun v _ => by rw [Subgroup.mem_bot, hact]; group⟩

theorem of_isPermModuleMod
    (h : IsPermModuleMod (n := 6) (fun _ => True) ({0, fun _ => 1} : Set (Fin 6 → ZMod 2))
      φ A ⊥ M Alt) : Sec11Perm A M Alt φ := by
  obtain ⟨-, -, -, -, hmem, hmul, hker, hsurj, hact, hact'⟩ := h
  refine ⟨fun v => hmem v trivial, fun v w => ?_, fun v => ?_, fun a ha => ?_, fun m hm => ?_,
    fun σ hσ => ?_⟩
  · have := hmul v w trivial trivial
    rw [Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this.symm
  · have := hker v trivial
    rw [Subgroup.mem_bot] at this
    exact this.trans Iff.rfl
  · obtain ⟨v, -, hv⟩ := hsurj a ha
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hv
    exact ⟨v, hv⟩
  · obtain ⟨σ, hσ, hs⟩ := hact m hm
    refine ⟨σ, hσ, fun v => ?_⟩
    have := hs v trivial
    rw [Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this
  · obtain ⟨m, hm, hs⟩ := hact' σ hσ
    refine ⟨m, hm, fun v => ?_⟩
    have := hs v trivial
    rw [Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this

@[expose] noncomputable def toAutIn (hM : M ≤ normalizer (A : Set G)) : ↥M →* ↥(autIn M A) :=
  (A.normalizerMonoidHom.comp (Subgroup.inclusion hM)).codRestrict (autIn M A) fun m =>
    sec1011_conjAut_mem (Y := A) m.2 (hM m.2)

theorem toAutIn_surjective (hM : M ≤ normalizer (A : Set G)) :
    Function.Surjective (toAutIn (A := A) hM) := by
  rintro ⟨α, hα⟩
  obtain ⟨m, hmM, hm, rfl⟩ := sec1011_exists_conjAut hα
  exact ⟨⟨m, hmM⟩, rfl⟩

theorem ker_toAutIn (h : Sec11Perm A M Alt φ) (hM : M ≤ normalizer (A : Set G)) :
    (toAutIn (A := A) hM).ker = h.rhoHom.ker := by
  ext m
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  rw [h.rhoHom_apply, h.rho_eq_one_iff m.2]
  constructor
  · intro h1 a ha
    have h2 : (((toAutIn (A := A) hM m : ↥(autIn M A)) : MulAut ↥A) ⟨a, ha⟩ : G) =
        m * a * (m : G)⁻¹ := rfl
    rw [← h2, h1]
    rfl
  · intro hc
    apply Subtype.ext
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    exact hc a.1 a.2

@[expose] noncomputable def autInEquiv (h : Sec11Perm A M Alt φ) (hM : M ≤ normalizer (A : Set G)) :
    ↥(autIn M A) ≃* ↥Alt :=
  ((QuotientGroup.quotientKerEquivOfSurjective (toAutIn (A := A) hM)
      (toAutIn_surjective hM)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_toAutIn h hM)).trans
      (QuotientGroup.quotientKerEquivRange h.rhoHom))).trans
    (MulEquiv.subgroupCongr h.range_rhoHom)

end Sec11Perm

end CFSG.OddStandard.SmallF3.Omega
