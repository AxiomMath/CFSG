module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Step9

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

namespace Eight

open S6M

namespace E32Conf

variable {X : Type} [Group X] [Finite X] (C : E32Conf X)

abbrev NUW : Subgroup X := C.U ⊓ normalizer (C.W : Set X)

theorem W_le_NUW : C.W ≤ C.NUW := le_inf inf_le_left le_normalizer

section Setup

variable {y : X} (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)
include hyU hyN hyW

theorem mem_W_or (u : X) (hu : u ∈ C.NUW) : u ∈ C.W ∨ u * y⁻¹ ∈ C.W := by
  by_cases huW : u ∈ C.W
  · exact Or.inl huW
  · exact Or.inr (C.mul_inv_mem_W hyU hyN hyW hu.1 hu.2 huW)

theorem sq_mem_W : y * y ∈ C.W := by
  rcases C.mem_W_or hyU hyN hyW (y * y) ⟨mul_mem hyU hyU, mul_mem hyN hyN⟩ with h | h
  · exact h
  · exact absurd (by rwa [mul_inv_cancel_right] at h) hyW

theorem conj_inv_eq {A : Subgroup X} (hA : C.W ≤ normalizer (A : Set X)) :
    conjugate A y⁻¹ = conjugate A y := by
  have h1 : conjugate A (y * y) = A := conjugate_eq_of_mem_normalizer (hA (C.sq_mem_W hyU hyN hyW))
  calc conjugate A y⁻¹ = conjugate (conjugate A (y * y)) y⁻¹ := by rw [h1]
    _ = conjugate A y := by rw [conjugate_conjugate, mul_inv_cancel_right]

theorem conj_mem_Ey {A : Subgroup X} (hA : C.W ≤ normalizer (A : Set X)) {f : X}
    (hf : f * y⁻¹ ∈ C.W) {e : X} (he : e ∈ A) : f * e * f⁻¹ ∈ conjugate A y := by
  have hAy : C.W ≤ normalizer ((conjugate A y : Subgroup X) : Set X) := by
    intro w hw
    apply mem_normalizer_of_conjugate_eq
    have hw' : y * w * y⁻¹ ∈ C.W := by
      have := (mem_normalizer_iff.mp hyN w).mp hw
      exact this
    rw [conjugate_conjugate, show y * w = (y * w * y⁻¹) * y by group, ← conjugate_conjugate,
      conjugate_eq_of_mem_normalizer (hA hw')]
  have h1 : y * e * y⁻¹ ∈ conjugate A y := by
    rw [← C.conj_inv_eq hyU hyN hyW hA, mem_conjugate_iff, inv_inv]
    rwa [show y⁻¹ * (y * e * y⁻¹) * y = e by group]
  have h2 := (mem_normalizer_iff.mp (hAy hf) _).mp h1
  rwa [show f * y⁻¹ * (y * e * y⁻¹) * (f * y⁻¹)⁻¹ = f * e * f⁻¹ by group] at h2

end Setup

theorem conj_mem_E {y : X} {A : Subgroup X} (hA : C.W ≤ normalizer (A : Set X)) {f : X}
    (hf : f * y⁻¹ ∈ C.W) {g : X} (hg : g ∈ conjugate A y) : f * g * f⁻¹ ∈ A := by
  rw [mem_conjugate_iff] at hg
  have := (mem_normalizer_iff.mp (hA hf) _).mp hg
  rwa [show f * y⁻¹ * (y * g * y⁻¹) * (f * y⁻¹)⁻¹ = f * g * f⁻¹ by group] at this

theorem W_le_normalizer_E : C.W ≤ normalizer (C.E : Set X) := inf_le_right

@[expose] noncomputable def ψW {F : Subgroup X} (hF : F ≤ C.W) : ↥F →* Equiv.Perm (Fin 6) :=
  C.π.comp (inclusion (hF.trans inf_le_right))

theorem mem_range_ψW {F : Subgroup X} (hF : F ≤ C.W) {t : Equiv.Perm (Fin 6)} :
    t ∈ (C.ψW hF).range ↔ ∃ f, ∃ hf : f ∈ F, C.π ⟨f, (hF hf).2⟩ = t := by
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

theorem card_eq_mul_of_le_W {F : Subgroup X} (hF : F ≤ C.W) :
    Nat.card F = Nat.card ↥(F ⊓ C.E) * Nat.card (C.ψW hF).range := by
  have h1 := Subgroup.card_ker_mul_card_range (C.ψW hF)
  have hmap : (C.ψW hF).ker.map F.subtype = F ⊓ C.E := by
    ext f
    constructor
    · rintro ⟨⟨f, hf⟩, hker, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨hf, C.π_ker ⟨f, (hF hf).2⟩ (hF hf).1 hker⟩
    · intro hf
      obtain ⟨hf1, hf2⟩ := Subgroup.mem_inf.mp hf
      exact ⟨⟨f, hf1⟩, C.π_E (e := ⟨f, (hF hf1).2⟩) hf2, rfl⟩
  have hker : Nat.card (C.ψW hF).ker = Nat.card ↥(F ⊓ C.E) := by
    rw [← card_map_of_injective F.subtype_injective, hmap]
  rw [← h1, hker]

theorem fix_of_le_W {F : Subgroup X} (hF : F ≤ C.W)
    (hFc : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f) {v : V5} (hv : C.θ v ∈ F) :
    v ∈ fixSet ((C.ψW hF).range : Set (Equiv.Perm (Fin 6))) := by
  intro t ht
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψW hF).mp ht
  exact (C.comm_iff _ v).mp (hFc f hf _ hv)

theorem range_ψW_le_W {F : Subgroup X} (hF : F ≤ C.W) : (C.ψW hF).range ≤ Wsub := by
  intro t ht
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψW hF).mp ht
  exact C.π_W _ (hF hf).1

theorem range_ψW_comm {F : Subgroup X} (hF : F ≤ C.W)
    (hFc : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f) {s t : Equiv.Perm (Fin 6)}
    (hs : s ∈ (C.ψW hF).range) (ht : t ∈ (C.ψW hF).range) : s * t = t * s := by
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψW hF).mp hs
  obtain ⟨g, hg, rfl⟩ := (C.mem_range_ψW hF).mp ht
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hFc f hf g hg)

theorem range_ψW_sq {F : Subgroup X} (hF : F ≤ C.W) (hF2 : ∀ f ∈ F, f * f = 1)
    {t : Equiv.Perm (Fin 6)} (ht : t ∈ (C.ψW hF).range) : t * t = 1 := by
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψW hF).mp ht
  rw [← map_mul, ← map_one C.π]
  congr 1
  exact Subtype.ext (hF2 f hf)

theorem range_ψW_le_V {F : Subgroup X} (hF : F ≤ C.W) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFc : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f) (hF32 : Nat.card F = 32) :
    (C.ψW hF).range ≤ Vsub := by
  intro t ht
  have htW := C.range_ψW_le_W hF ht
  have hsq := C.range_ψW_sq hF hF2 ht
  have h1 := List.all_eq_true.mp Wlist_inv_cases t htW
  simp only [hsq, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    List.contains_iff_mem] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exfalso
    have hB := card_mul_fixSet_le_of_B _ (C.range_ψW_le_W hF)
      (fun s hs u hu => C.range_ψW_comm hF hFc hs hu) ht h1
    have hK : Nat.card ↥(F ⊓ C.E) ≤ (fixSet ((C.ψW hF).range : Set (Equiv.Perm (Fin 6)))).ncard :=
      C.card_le_ncard _ fun k hk => by
        obtain ⟨v, rfl⟩ := C.mem_E_iff.mp (Subgroup.mem_inf.mp hk).2
        exact ⟨v, C.fix_of_le_W hF hFc (Subgroup.mem_inf.mp hk).1, rfl⟩
    have hcard := C.card_eq_mul_of_le_W hF
    rw [hF32] at hcard
    have : 32 ≤ 16 := by
      calc 32 = Nat.card ↥(F ⊓ C.E) * Nat.card (C.ψW hF).range := hcard
        _ ≤ (fixSet ((C.ψW hF).range : Set (Equiv.Perm (Fin 6)))).ncard *
            Nat.card (C.ψW hF).range := Nat.mul_le_mul_right _ hK
        _ = Nat.card (C.ψW hF).range *
            (fixSet ((C.ψW hF).range : Set (Equiv.Perm (Fin 6)))).ncard := mul_comm _ _
        _ ≤ 16 := hB
    omega

abbrev Q (y : X) : Subgroup X := C.E ⊔ conjugate C.E y

abbrev Q0 (y : X) : Subgroup X := C.E0 ⊔ conjugate C.E0 y

section Qsec

variable {y : X} (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)

omit hyU hyW in
theorem Q_le_W (hyN : y ∈ normalizer (C.W : Set X)) : C.Q y ≤ C.W :=
  sup_le C.E_le_W (C.conj_le_W le_rfl hyN)

omit hyU hyW in
theorem exists_mul_of_mem_Q (hyN : y ∈ normalizer (C.W : Set X)) {q : X} (hq : q ∈ C.Q y) :
    ∃ e ∈ C.E, ∃ g ∈ conjugate C.E y, q = e * g := by
  have hle : conjugate C.E y ≤ normalizer (C.E : Set X) :=
    (C.conj_le_W le_rfl hyN).trans C.W_le_normalizer_E
  have hq' : q ∈ ((C.E : Set X) * (conjugate C.E y : Set X)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hq
  obtain ⟨e, he, g, hg, rfl⟩ := Set.mem_mul.mp hq'
  exact ⟨e, he, g, hg, rfl⟩

include hyU hyN hyW

theorem parity_eq {e₁ e₂ g₁ g₂ : X} (he₁ : e₁ ∈ C.E) (he₂ : e₂ ∈ C.E)
    (hg₁ : g₁ ∈ conjugate C.E y) (hg₂ : g₂ ∈ conjugate C.E y) (h : e₁ * g₁ = e₂ * g₂) :
    e₁ ∈ C.E0 ↔ e₂ ∈ C.E0 := by
  have hk : e₂⁻¹ * e₁ ∈ conjugate C.E y ⊓ C.E := by
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (inv_mem he₂) he₁⟩
    rw [show e₂⁻¹ * e₁ = g₂ * g₁⁻¹ by
      calc e₂⁻¹ * e₁ = e₂⁻¹ * (e₁ * g₁) * g₁⁻¹ := by group
        _ = e₂⁻¹ * (e₂ * g₂) * g₁⁻¹ := by rw [h]
        _ = g₂ * g₁⁻¹ := by group]
    exact mul_mem hg₂ (inv_mem hg₁)
  have hk0 := C.inf_le_E0 hyU hyN hyW hk
  constructor
  · intro h1
    have := mul_mem h1 (inv_mem hk0)
    rwa [show e₁ * (e₂⁻¹ * e₁)⁻¹ = e₂ by group] at this
  · intro h2
    have := mul_mem h2 hk0
    rwa [show e₂ * (e₂⁻¹ * e₁) = e₁ by group] at this

theorem mem_Q_of_π {w : X} (hw : w ∈ C.W) (hπ : C.π ⟨w, hw.2⟩ ∈ Vsub) : w ∈ C.Q y := by
  rw [← C.range_ψ_eq hyU hyN hyW] at hπ
  obtain ⟨g, hg, hgw⟩ := (C.mem_range_ψ le_rfl hyN).mp hπ
  have hgW := C.conj_le_W le_rfl hyN hg
  have h1 : C.π ⟨w * g⁻¹, mul_mem hw.2 (inv_mem hgW.2)⟩ = 1 := by
    rw [show (⟨w * g⁻¹, mul_mem hw.2 (inv_mem hgW.2)⟩ : ↥C.N) = ⟨w, hw.2⟩ * ⟨g, hgW.2⟩⁻¹ from
      rfl, map_mul, map_inv, ← hgw]
    exact mul_inv_cancel _
  have h2 := C.π_ker _ (mul_mem (Subgroup.mem_inf.mp hw).1
    (inv_mem (Subgroup.mem_inf.mp hgW).1)) h1
  rw [show w = (w * g⁻¹) * g by group]
  exact mul_mem_sup h2 hg

theorem exists_mul_of_π0 {w : X} (hw : w ∈ C.W) (hπ : C.π ⟨w, hw.2⟩ ∈ V0sub) :
    ∃ e ∈ C.E, ∃ g ∈ conjugate C.E0 y, w = e * g := by
  rw [← C.range_ψ0_eq hyU hyN hyW] at hπ
  obtain ⟨g, hg, hgw⟩ := (C.mem_range_ψ C.E0_le_E hyN).mp hπ
  have hgW := C.conj_E0_le_W hyN hg
  have h1 : C.π ⟨w * g⁻¹, mul_mem hw.2 (inv_mem hgW.2)⟩ = 1 := by
    rw [show (⟨w * g⁻¹, mul_mem hw.2 (inv_mem hgW.2)⟩ : ↥C.N) = ⟨w, hw.2⟩ * ⟨g, hgW.2⟩⁻¹ from
      rfl, map_mul, map_inv, ← hgw]
    exact mul_inv_cancel _
  exact ⟨w * g⁻¹, C.π_ker _ (mul_mem (Subgroup.mem_inf.mp hw).1
    (inv_mem (Subgroup.mem_inf.mp hgW).1)) h1, g, hg, by group⟩

theorem π_mem_V_of_mem_Q {q : X} (hq : q ∈ C.Q y) :
    C.π ⟨q, (C.Q_le_W hyN hq).2⟩ ∈ Vsub := by
  obtain ⟨e, he, g, hg, rfl⟩ := C.exists_mul_of_mem_Q hyN hq
  have heW := C.E_le_W he
  have hgW := C.conj_le_W le_rfl hyN hg
  rw [show (⟨e * g, (C.Q_le_W hyN hq).2⟩ : ↥C.N) = ⟨e, heW.2⟩ * ⟨g, hgW.2⟩ from rfl, map_mul,
    C.π_E (e := ⟨e, heW.2⟩) he, one_mul, ← C.range_ψ_eq hyU hyN hyW]
  exact (C.mem_range_ψ le_rfl hyN).mpr ⟨g, hg, rfl⟩

end Qsec

end E32Conf

end Eight

end CFSG.ComponentClassification.GSThmB
