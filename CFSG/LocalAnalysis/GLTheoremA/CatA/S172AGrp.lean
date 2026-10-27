module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.PerfectAutomorphisms

section Center

variable {X : Type} [Group X]

theorem mulAut_conj_eq_one_iff (g : X) : MulAut.conj g = 1 ↔ g ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h y
    have hy : MulAut.conj g y = y := by rw [h]; rfl
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hy
    exact hy.symm
  · intro h
    ext y
    rw [MulAut.conj_apply, MulAut.one_apply, ← h y, mul_inv_cancel_right]

theorem centerQuotientHom_conj_eq_one_iff [Group.IsPerfect X] (g : X) :
    centerQuotientHom X (MulAut.conj g) = 1 ↔ g ∈ Subgroup.center X := by
  rw [← mulAut_conj_eq_one_iff]
  constructor
  · intro h
    apply centerQuotientHom_injective X
    rw [h, map_one]
  · intro h
    rw [h, map_one]

theorem center_quotient_center_eq_bot [Group.IsPerfect X]
    [hS : IsSimpleGroup (X ⧸ Subgroup.center X)] :
    Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center (X ⧸ Subgroup.center X)) with h | h
  · exact h
  · exfalso
    have hcomm : ⁅(⊤ : Subgroup (X ⧸ Subgroup.center X)), (⊤ : Subgroup (X ⧸ Subgroup.center X))⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      have ha : a ∈ Subgroup.center (X ⧸ Subgroup.center X) := h ▸ Subgroup.mem_top a
      exact Subgroup.mem_center_iff.1 ha b
    have htop : commutator (X ⧸ Subgroup.center X) = ⊤ :=
      Group.IsPerfect.commutator_eq_top
    have hbot : (⊥ : Subgroup (X ⧸ Subgroup.center X)) = ⊤ := by
      rw [← hcomm]
      exact htop
    exact (bot_ne_top : (⊥ : Subgroup (X ⧸ Subgroup.center X)) ≠ ⊤) hbot

theorem conj_injective_of_center_eq_bot {Y : Type} [Group Y]
    (h : Subgroup.center Y = ⊥) : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center Y := (mulAut_conj_eq_one_iff g).1 hg
  rw [h] at hmem
  exact (Subgroup.mem_bot.1 hmem)

theorem center_quotient_eq_map [Group.IsPerfect X] {O : Subgroup X} [O.Normal]
    (hO : O ≤ Subgroup.center X) :
    Subgroup.center (X ⧸ O) = (Subgroup.center X).map (QuotientGroup.mk' O) := by
  ext q
  constructor
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O q
    have key : ∀ h : X, QuotientGroup.mk' O h ∈ Subgroup.center (X ⧸ O) →
        ∀ x : X, h⁻¹ * x⁻¹ * h * x ∈ O := by
      intro h hh x
      have hc := Subgroup.mem_center_iff.1 hh (QuotientGroup.mk' O x)
      rw [← map_mul, ← map_mul] at hc
      have hc' : (x * h)⁻¹ * (h * x) ∈ O := QuotientGroup.eq.1 hc
      have e : (x * h)⁻¹ * (h * x) = h⁻¹ * x⁻¹ * h * x := by group
      rwa [e] at hc'
    have hg' : QuotientGroup.mk' O g⁻¹ ∈ Subgroup.center (X ⧸ O) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hq
    have hcomm : ∀ x : X, g * x⁻¹ * g⁻¹ * x ∈ O := by
      intro x
      have := key g⁻¹ hg' x
      simpa using this
    have hgc : g ∈ Subgroup.center X := by
      rw [← centerQuotientHom_conj_eq_one_iff]
      ext y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) y
      have h1 : centerQuotientHom X (MulAut.conj g) (QuotientGroup.mk' (Subgroup.center X) x) =
          QuotientGroup.mk' (Subgroup.center X) (g * x * g⁻¹) :=
        onCenterQuotient_apply_mk (MulAut.conj g) x
      rw [h1, MulAut.one_apply]
      refine (QuotientGroup.eq).2 ?_
      have e : (g * x * g⁻¹)⁻¹ * x = g * x⁻¹ * g⁻¹ * x := by group
      rw [e]
      exact hO (hcomm x)
    exact ⟨g, hgc, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y']

end Center

section Normalizer

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem normalizerMonoidHom_eq_one_iff (K : Subgroup Ω)
    (g : ↥(Subgroup.normalizer (K : Set Ω))) :
    K.normalizerMonoidHom g = 1 ↔ (g : Ω) ∈ Subgroup.centralizer (K : Set Ω) := by
  have h := Subgroup.normalizerMonoidHom_ker (H := K)
  constructor
  · intro hg
    have hm : g ∈ K.normalizerMonoidHom.ker := hg
    rw [h, Subgroup.mem_subgroupOf] at hm
    exact hm
  · intro hg
    have hm : g ∈ K.normalizerMonoidHom.ker := by
      rw [h, Subgroup.mem_subgroupOf]
      exact hg
    exact hm

theorem normalizer_action_eq_one_iff {K : Subgroup Ω} [Group.IsPerfect ↥K]
    (g : ↥(Subgroup.normalizer (K : Set Ω))) :
    centerQuotientHom ↥K (K.normalizerMonoidHom g) = 1 ↔
      (g : Ω) ∈ Subgroup.centralizer (K : Set Ω) := by
  rw [← normalizerMonoidHom_eq_one_iff]
  constructor
  · intro h
    apply centerQuotientHom_injective ↥K
    rw [h, map_one]
  · intro h
    rw [h, map_one]

end Normalizer

section PSimple

variable {Ω : Type} [Group Ω] [Finite Ω]

noncomputable def pSimpleEquivCenterQuot (p : ℕ) {K : Subgroup Ω} [Group.IsPerfect ↥K]
    (hO : GLAPPrimeCore p ↥K ≤ Subgroup.center ↥K) :
    (↥K ⧸ Subgroup.center ↥K) ≃* PSimple p K :=
  (QuotientGroup.quotientQuotientEquivQuotient (GLAPPrimeCore p ↥K) (Subgroup.center ↥K) hO).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_quotient_eq_map hO).symm)

end PSimple

end CFSG.LocalAnalysis.GLTheoremA.S172A

end
