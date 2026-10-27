module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem mem_conjugate_iff (H : Subgroup G) (g x : G) :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem Sec3SettingLB.conjugate [Finite G] {t : G} {L : Subgroup G} (h : Sec3SettingLB G t L)
    (g : G) : Sec3SettingLB G (g⁻¹ * t * g) (CFSG.conjugate L g) := by
  refine ⟨⟨h.simple, h.a1, h.a2, h.notChev3, ?_, ?_, h.inF.conjugate g⟩, h.lBalance, h.kProper,
    h.notCat⟩
  · have h' := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rwa [MulAut.conj_apply, inv_inv, h.involution] at h'
  · have h' := h.component.map_mulEquiv (MulAut.conj g⁻¹)
    change IsComponentIn (CFSG.conjugate L g)
      (CFSG.conjugate (centralizer ({t} : Set G)) g) at h'
    rw [conjugate_centralizer_singleton t g] at h'
    exact h'

theorem lieModel_quotient_oddCore_conjugate {L : Subgroup G} (g : G) {tag : CFSG.Open.StatedLieTag}
    {n p f : ℕ} (h : LieModel (↥L ⧸ oddCore ↥L) tag n p f) :
    LieModel (↥(CFSG.conjugate L g) ⧸ oddCore ↥(CFSG.conjugate L g)) tag n p f := by
  have e : ↥L ≃* ↥(CFSG.conjugate L g) :=
    Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  obtain ⟨e'⟩ := nonempty_quotient_oddCore_mulEquiv e
  exact LieModel.of_mulEquiv e' h

theorem IsI4PlusIn.conjugate {X : Subgroup G} {y : G} (h : IsI4PlusIn X y) (g : G) :
    IsI4PlusIn (CFSG.conjugate X g) (g⁻¹ * y * g) := by
  obtain ⟨hy, K, hK⟩ := h
  refine ⟨?_, CFSG.conjugate K g, hK.conjugate g⟩
  have h' := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) y
  rwa [MulAut.conj_apply, inv_inv, hy] at h'

theorem IsI4PlusIn.mem {X : Subgroup G} {y : G} (h : IsI4PlusIn X y) : y ∈ X := by
  obtain ⟨-, K, hK⟩ := h
  exact (hK.2.1 hK.1).1

theorem orderOf_conjugate_eq (x g : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
  simpa [MulAut.conj_apply] using h

theorem mem_normalizer_of_conjugate_eq {H : Subgroup G} {c : G} (h : CFSG.conjugate H c = H) :
    c ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h2 := mem_conjugate_iff H c x
  rw [h] at h2
  exact h2

theorem isOmegaPlusIn_conjugate {Y : Subgroup G} (h : IsOmegaPlusIn Y) (g : G) :
    IsOmegaPlusIn (CFSG.conjugate Y g) :=
  ⟨h.1.conjugate g, lieModel_quotient_oddCore_conjugate g h.2⟩

theorem sec3PocketData_of_sl23PocketIn {t : G} {L : Subgroup G} (ht : orderOf t = 2)
    (hL : IsComponentIn L (centralizer ({t} : Set G))) (hLF : InFStar L)
    (hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L) {z : G} {K : Subgroup G}
    (hz2 : orderOf z = 2) (hK : Sl23PocketIn L z K) : Sec3PocketData t L z K :=
  ⟨ht, hL, hLF, hz2, (hK.2.1 hK.1).1, hK.2.1.trans inf_le_left, hK.of_normal hL.le hnorm⟩

theorem conj_mul_of_commute {t l : G} (h : l * t = t * l) (x : G) :
    l⁻¹ * (t * x) * l = t * (l⁻¹ * x * l) := by
  calc l⁻¹ * (t * x) * l = (l⁻¹ * t * l) * (l⁻¹ * x * l) := by group
    _ = t * (l⁻¹ * x * l) := by
      congr 1
      rw [mul_assoc, ← h]
      group

end CFSG.OddStandard.SmallF3.Omega
