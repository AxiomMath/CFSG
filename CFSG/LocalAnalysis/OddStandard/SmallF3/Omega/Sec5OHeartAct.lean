module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartA8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {φ : (Fin 6 → ZMod 2) → G}

@[expose] def sec5oActs (φ : (Fin 6 → ZMod 2) → G) (m : G) (σ : Equiv.Perm (Fin 8)) : Prop :=
  ∀ w : Fin 8 → ZMod 2, IsEvenVec w →
    m * φ (heartCoord w) * m⁻¹ = φ (heartCoord (permVec σ w))

theorem sec5o_acts_mul {m m' : G} {σ τ : Equiv.Perm (Fin 8)} (h : sec5oActs φ m σ)
    (h' : sec5oActs φ m' τ) : sec5oActs φ (m * m') (σ * τ) := by
  intro w hw
  have h1 := h' w hw
  have h2 := h (permVec τ w) (isEvenVec_permVec τ hw)
  calc m * m' * φ (heartCoord w) * (m * m')⁻¹
      = m * (m' * φ (heartCoord w) * m'⁻¹) * m⁻¹ := by group
    _ = m * φ (heartCoord (permVec τ w)) * m⁻¹ := by rw [h1]
    _ = φ (heartCoord (permVec σ (permVec τ w))) := h2
    _ = φ (heartCoord (permVec (σ * τ) w)) := by rw [sec5b_permVec_mul]

theorem sec5o_acts_inv {m : G} {σ : Equiv.Perm (Fin 8)} (h : sec5oActs φ m σ) :
    sec5oActs φ m⁻¹ σ⁻¹ := by
  intro w hw
  have hw' : IsEvenVec (permVec σ⁻¹ w) := isEvenVec_permVec σ⁻¹ hw
  have h1 := h (permVec σ⁻¹ w) hw'
  have hfix : permVec σ (permVec σ⁻¹ w) = w := by
    rw [← sec5b_permVec_mul, mul_inv_cancel]
    rfl
  rw [hfix] at h1
  calc m⁻¹ * φ (heartCoord w) * m⁻¹⁻¹
      = m⁻¹ * (m * φ (heartCoord (permVec σ⁻¹ w)) * m⁻¹) * m := by rw [h1, inv_inv]
    _ = φ (heartCoord (permVec σ⁻¹ w)) := by group

section Model

variable {A H : Subgroup G} {t : G} {L : Subgroup G} {z r : G}

theorem sec5o_acts_of_conjCoord (h : IsPerm6 φ A H) {m : G} (hm : m ∈ normalizer (A : Set G))
    {σ : Equiv.Perm (Fin 8)}
    (hσ : ∀ w : Fin 8 → ZMod 2, IsEvenVec w →
      conjCoord φ m (heartCoord w) = heartCoord (permVec σ w)) : sec5oActs φ m σ := by
  intro w hw
  rw [← h.conjCoord_spec hm, hσ w hw]

theorem sec5o_acts_alt8 [Finite G] (f59 : Asc82Fact59) (hm : Sec5Model58 t L z r A φ)
    (ht : conjClassIn (normalizer (A : Set G)) t =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6) {σ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ alternatingGroup (Fin 8)) :
    ∃ m ∈ normalizer (A : Set G), sec5oActs φ m σ := by
  have hle := sec5b_alt8_le (fun τ hτ => sec5b_extPerm_mem_heartAlt hm hτ)
    (sec5b_heartAlt_move f59 hm ht)
  have hmem : σ ∈ heartAltSet φ A := hle hσ
  obtain ⟨m, hmN, hmσ⟩ := hmem
  exact ⟨m, hmN, sec5o_acts_of_conjCoord hm.perm hmN hmσ⟩

theorem sec5o_acts_extPerm (hm : Sec5Model58 t L z r A φ) {τ : Equiv.Perm (Fin 6)}
    (hτ : τ ∈ alternatingGroup (Fin 6)) :
    ∃ m ∈ L ⊓ normalizer (A : Set G), sec5oActs φ m (extPerm τ) := by
  have hlift : ∀ σ ∈ alternatingGroup (Fin 6), ∃ h ∈ L ⊓ normalizer (A : Set G),
      ∀ v, True → h * φ v * h⁻¹ = φ (permVec σ v) := by
    have h := hm.perm
    unfold IsPerm6 IsPermModuleVia at h
    exact h.2.2.2.2
  obtain ⟨a, ha, hact⟩ := hlift τ hτ
  refine ⟨a, ha, fun w _ => ?_⟩
  rw [sec5b_heartCoord_extPerm]
  exact hact (heartCoord w) trivial

theorem sec5o_t_eq (hm : Sec5Model58 t L z r A φ) :
    φ (heartCoord (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1)) = t := by
  rw [sec5b_heartCoord_pair_six_seven]
  exact hm.map_one

end Model

end CFSG.OddStandard.SmallF3.Omega
