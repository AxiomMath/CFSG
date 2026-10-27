module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem Sec10Ctx.conjugate [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (h : Sec10Ctx G t L S z K1 K2) (g : G) :
    Sec10Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g)
      (CFSG.conjugate K1 g) (CFSG.conjugate K2 g) :=
  { toSec10Z :=
      { toSec10Setting :=
          { toSec3SettingLB := h.toSec10Z.toSec10Setting.toSec3SettingLB.conjugate g
            psp4 := lieModel_quotient_oddCore_conjugate g h.psp4 }
        toAsc82Notation := h.toAsc82Notation.conjugate g }
    pocket1 := h.pocket1.conjugate g
    pocket2 := h.pocket2.conjugate g
    ne := fun heq => h.ne (Subgroup.map_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective heq) }

theorem kl_mem_normalizer_sup {X Y : Subgroup G} {n : G} (hX : n ∈ normalizer (X : Set G))
    (hY : n ∈ normalizer (Y : Set G)) : n ∈ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  have h1 := sec10C_conjugate_eq_of_normalizer hX
  have h2 := sec10C_conjugate_eq_of_normalizer hY
  unfold CFSG.conjugate at h1 h2 ⊢
  rw [Subgroup.map_sup, h1, h2]

theorem kl_centralizer_conj {L : Subgroup G} {m c : G} (hm : m ∈ normalizer (L : Set G))
    (hc : c ∈ centralizer (L : Set G)) : m * c * m⁻¹ ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : m⁻¹ * l * m ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set G)).inv_mem hm) l).mp hl
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hl'
  calc l * (m * c * m⁻¹) = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
    _ = m * c * m⁻¹ * l := by group

theorem kl_innerOn_conj {L : Subgroup G} {m x : G} (hm : m ∈ normalizer (L : Set G))
    (hx : InnerOn L x) : InnerOn L (m * x * m⁻¹) := by
  obtain ⟨l, hl, c, hc, rfl⟩ := innerOn_decompose hx
  have e : m * (l * c) * m⁻¹ = (m * l * m⁻¹) * (m * c * m⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp hm l).mp hl)
    (kl_centralizer_conj hm hc)

theorem kl_innerOn_conj_iff {L : Subgroup G} {m x : G} (hm : m ∈ normalizer (L : Set G)) :
    InnerOn L (m * x * m⁻¹) ↔ InnerOn L x := by
  refine ⟨fun h => ?_, kl_innerOn_conj hm⟩
  have := kl_innerOn_conj ((normalizer (L : Set G)).inv_mem hm) h
  simpa [mul_assoc] using this

theorem kl_isI4PlusIn_conj {L : Subgroup G} {m y : G} (hm : m ∈ normalizer (L : Set G))
    (h : IsI4PlusIn L y) : IsI4PlusIn L (m * y * m⁻¹) := by
  have h1 := h.conjugate m⁻¹
  rwa [sec10C_conjugate_eq_of_normalizer ((normalizer (L : Set G)).inv_mem hm), inv_inv] at h1

theorem kl_inducesTypeSome_conj {L : Subgroup G} {m s : G} (hm : m ∈ normalizer (L : Set G))
    {n : ℕ} {ε : ℤˣ} {r : ℕ} {α : ℤˣ} (h : InducesTypeSome L s n ε r α) :
    InducesTypeSome L (m * s * m⁻¹) n ε r α := by
  have h1 := inducesTypeSome_conjugate h m⁻¹
  rwa [sec10C_conjugate_eq_of_normalizer ((normalizer (L : Set G)).inv_mem hm), inv_inv] at h1

end CFSG.OddStandard.SmallF3.Omega
