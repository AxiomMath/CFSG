module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.GH74.GLS.IVK.A7.Core

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open Equiv Equiv.Perm

section Perm

theorem cycleType_of_odd_involution {σ : Perm (Fin 7)} (hσ : σ * σ = 1) (hs : sign σ = -1) :
    σ.cycleType = {2} ∨ σ.cycleType = {2, 2, 2} := by
  have hne : σ ≠ 1 := by
    rintro rfl
    simp at hs
  rcases CFSG.GH74.GLS.IVK.A7.involution_cycleType σ (by rw [pow_two]; exact hσ) hne with
    h | h | h
  · exact Or.inl h
  · exfalso
    have h1 := Equiv.Perm.sign_of_cycleType σ
    rw [h, hs] at h1
    revert h1
    decide
  · exact Or.inr h

noncomputable def evenCentralizerEquiv (σ : Perm (Fin 7)) :
    evenCentralizer σ ≃*
      ↥(Subgroup.centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
  (Subgroup.equivMapOfInjective (evenCentralizer σ) (alternatingGroup (Fin 7)).subtype
    (alternatingGroup (Fin 7)).subtype_injective).trans (MulEquiv.subgroupCongr (by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr ha, a.2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨⟨x, hx2⟩, Subgroup.mem_centralizer_singleton_iff.mp hx1, rfl⟩))

theorem nonempty_evenCentralizer_equiv_perm_five {σ : Perm (Fin 7)} (hc : σ.cycleType = {2}) :
    Nonempty (evenCentralizer σ ≃* Perm (Fin 5)) := by
  obtain ⟨e⟩ := CFSG.GH74.GLS.IVK.A7.centralizer_A7_swap_equiv
    (Equiv.Perm.isSwap_iff_cycleType.mpr hc)
  exact ⟨(evenCentralizerEquiv σ).trans e⟩

theorem nonempty_evenCentralizer_equiv_perm_four {σ : Perm (Fin 7)}
    (hc : σ.cycleType = {2, 2, 2}) : Nonempty (evenCentralizer σ ≃* Perm (Fin 4)) := by
  obtain ⟨e⟩ := CFSG.GH74.GLS.IVK.A7.centralizer_A7_two_two_two_equiv hc
  exact ⟨(evenCentralizerEquiv σ).trans e⟩

theorem natCard_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  try decide

theorem natCard_perm_four : Nat.card (Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  try decide

theorem nonempty_equiv_alternatingGroup_of_index_two {A : Type*} [Group A] {n : ℕ}
    (e : A ≃* Perm (Fin n)) {P : Subgroup A} (hP : P.index = 2) :
    Nonempty (↥P ≃* alternatingGroup (Fin n)) := by
  have h1 : (P.map (e : A →* Perm (Fin n))).index = 2 := by
    rw [Subgroup.index_map_equiv]
    exact hP
  have h2 := Equiv.Perm.eq_alternatingGroup_of_index_eq_two h1
  exact ⟨(Subgroup.equivMapOfInjective P (e : A →* Perm (Fin n)) e.injective).trans
    (MulEquiv.subgroupCongr h2)⟩

end Perm

section Fixed

variable {E : Type*} [Group E] [Finite E] {π : E →* A7} {z : E}


omit [Finite E] in
theorem map_mem_evenCentralizer_of_fixed (h : IsDoubleCoverA7 π z) (α : MulAut E) {x : E}
    (hx : α x = x) : π x ∈ evenCentralizer (h.autPerm α) := by
  have h1 := h.autPerm_spec α x
  rw [hx] at h1
  show (π x : Perm (Fin 7)) * h.autPerm α = h.autPerm α * (π x : Perm (Fin 7))
  calc (π x : Perm (Fin 7)) * h.autPerm α
      = (h.autPerm α * (π x : Perm (Fin 7)) * (h.autPerm α)⁻¹) * h.autPerm α := by rw [← h1]
    _ = h.autPerm α * π x := by group

theorem card_fixedIn_top (h : IsDoubleCoverA7 π z) (α : MulAut E) (hα : α * α = 1) (hne : α ≠ 1) :
    Nat.card (fixedIn α ⊤) = Nat.card (evenCentralizer (h.autPerm α)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : Perm (Fin 7) := h.autPerm α with hσdef
  have hσ : σ * σ = 1 := by rw [hσdef, ← map_mul, hα, map_one]
  set C : Subgroup A7 := evenCentralizer σ with hC
  set H : Subgroup E := C.comap π with hH
  have hHcard : Nat.card H = 2 * Nat.card C := by
    rw [hH, QuaternionStructure.natCard_comap_eq π h.surjective C, h.card_ker]
  have hHfix : ∀ x ∈ H, π (α x) = π x := fun x hx => h.map_apply_eq_of_mem_evenCentralizer α hx
  have hle := h.card_le_two_mul_card_fixedIn α H hHfix
  have hFeq : fixedIn α ⊤ = fixedIn α H := by
    ext x
    constructor
    · rintro ⟨-, hx⟩
      exact ⟨map_mem_evenCentralizer_of_fixed h α hx, hx⟩
    · rintro ⟨-, hx⟩
      exact ⟨trivial, hx⟩
  have hFH : fixedIn α H ≤ H := inf_le_left
  have hdvd : Nat.card (fixedIn α H) ∣ Nat.card H := Subgroup.card_dvd_of_le hFH
  have hne' : ¬ H ≤ fixedIn α H := by
    intro hHF
    have hmod : Nat.card C % 16 = 8 := card_evenCentralizer_mod hσ
    have h16 : 16 ∣ Nat.card H := by
      rw [hHcard]
      omega
    have h16' : 2 ^ 4 ∣ Nat.card H := by simpa using h16
    obtain ⟨B₀, hB₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 h16'
    set Q₀ : Subgroup E := B₀.map H.subtype with hQ₀
    have hQ₀card : Nat.card Q₀ = 2 ^ (Nat.card E).factorization 2 := by
      rw [hQ₀, Subgroup.card_map_of_injective H.subtype_injective, hB₀, h.card_E,
        Nat.factorization_def _ Nat.prime_two]
      decide +kernel
    let Q : Sylow 2 E := Sylow.ofCard Q₀ hQ₀card
    apply hne
    apply h.mulAut_eq_one_of_centralizes_sylow Q α
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    exact (hHF y.2).2
  have hlt : Nat.card (fixedIn α H) < Nat.card H := by
    by_contra hc
    push Not at hc
    exact hne' (Subgroup.eq_of_le_of_card_ge hFH hc).ge
  have hpos : 0 < Nat.card (fixedIn α H) := Nat.card_pos
  have hF2 : Nat.card H = 2 * Nat.card (fixedIn α H) := by
    obtain ⟨m, hm⟩ := hdvd
    have hm3 : m < 3 := by
      by_contra hc
      push Not at hc
      nlinarith
    interval_cases m <;> omega
  rw [hFeq]
  omega

theorem card_map_fixedIn_top (h : IsDoubleCoverA7 π z) (α : MulAut E) (hα : α * α = 1)
    (hne : α ≠ 1) :
    2 * Nat.card ((fixedIn α ⊤).map π) = Nat.card (evenCentralizer (h.autPerm α)) := by
  have hzF : z ∈ fixedIn α ⊤ := ⟨trivial, h.mulAut_apply_z α⟩
  have hkerle : π.ker ≤ fixedIn α ⊤ := by
    intro w hw
    rcases (h.ker_iff w).mp hw with rfl | rfl
    · exact one_mem _
    · exact hzF
  have hker : Nat.card (π.comp (fixedIn α ⊤).subtype).ker = 2 := by
    have h1 : (π.comp (fixedIn α ⊤).subtype).ker = π.ker.subgroupOf (fixedIn α ⊤) := by
      ext x
      simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [h1, ← h.card_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
  have h2 := Subgroup.card_ker_mul_card_range (π.comp (fixedIn α ⊤).subtype)
  rw [hker, MonoidHom.range_comp, Subgroup.range_subtype,
    card_fixedIn_top h α hα hne] at h2
  exact h2

omit [Finite E] in
theorem map_fixedIn_top_le (h : IsDoubleCoverA7 π z) (α : MulAut E) :
    (fixedIn α ⊤).map π ≤ evenCentralizer (h.autPerm α) := by
  rintro _ ⟨x, hx, rfl⟩
  exact map_mem_evenCentralizer_of_fixed h α hx.2

theorem index_map_fixedIn_top (h : IsDoubleCoverA7 π z) (α : MulAut E) (hα : α * α = 1)
    (hne : α ≠ 1) :
    (((fixedIn α ⊤).map π).subgroupOf (evenCentralizer (h.autPerm α))).index = 2 := by
  have h1 := Subgroup.card_mul_index
    (((fixedIn α ⊤).map π).subgroupOf (evenCentralizer (h.autPerm α)))
  have h2 : Nat.card (((fixedIn α ⊤).map π).subgroupOf (evenCentralizer (h.autPerm α))) =
      Nat.card ((fixedIn α ⊤).map π) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (map_fixedIn_top_le h α)).toEquiv
  rw [h2] at h1
  have h3 := card_map_fixedIn_top h α hα hne
  have hpos : 0 < Nat.card ((fixedIn α ⊤).map π) := Nat.card_pos
  have : Nat.card ((fixedIn α ⊤).map π) * (((fixedIn α ⊤).map π).subgroupOf
      (evenCentralizer (h.autPerm α))).index = Nat.card ((fixedIn α ⊤).map π) * 2 := by
    rw [h1, ← h3]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem nonempty_image_equiv_alternating_five (h : IsDoubleCoverA7 π z) (α : MulAut E)
    (hα : α * α = 1) (hne : α ≠ 1) (hc : (h.autPerm α).cycleType = {2}) :
    Nonempty (↥((fixedIn α ⊤).map π) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := nonempty_evenCentralizer_equiv_perm_five hc
  obtain ⟨e'⟩ := nonempty_equiv_alternatingGroup_of_index_two e (index_map_fixedIn_top h α hα hne)
  exact ⟨(Subgroup.subgroupOfEquivOfLe (map_fixedIn_top_le h α)).symm.trans e'⟩

theorem nonempty_image_equiv_alternating_four (h : IsDoubleCoverA7 π z) (α : MulAut E)
    (hα : α * α = 1) (hne : α ≠ 1) (hc : (h.autPerm α).cycleType = {2, 2, 2}) :
    Nonempty (↥((fixedIn α ⊤).map π) ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨e⟩ := nonempty_evenCentralizer_equiv_perm_four hc
  obtain ⟨e'⟩ := nonempty_equiv_alternatingGroup_of_index_two e (index_map_fixedIn_top h α hα hne)
  exact ⟨(Subgroup.subgroupOfEquivOfLe (map_fixedIn_top_le h α)).symm.trans e'⟩

theorem card_fixedIn_top_five (h : IsDoubleCoverA7 π z) (α : MulAut E) (hα : α * α = 1)
    (hne : α ≠ 1) (hc : (h.autPerm α).cycleType = {2}) : Nat.card (fixedIn α ⊤) = 120 := by
  obtain ⟨e⟩ := nonempty_evenCentralizer_equiv_perm_five hc
  rw [card_fixedIn_top h α hα hne, Nat.card_congr e.toEquiv, natCard_perm_five]

theorem card_fixedIn_top_four (h : IsDoubleCoverA7 π z) (α : MulAut E) (hα : α * α = 1)
    (hne : α ≠ 1) (hc : (h.autPerm α).cycleType = {2, 2, 2}) : Nat.card (fixedIn α ⊤) = 24 := by
  obtain ⟨e⟩ := nonempty_evenCentralizer_equiv_perm_four hc
  rw [card_fixedIn_top h α hα hne, Nat.card_congr e.toEquiv, natCard_perm_four]

end Fixed

end CFSG.ClassicalInvolution.Hat2A7
