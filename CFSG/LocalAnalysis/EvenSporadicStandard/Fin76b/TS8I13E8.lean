module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13E8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Ctx

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c

theorem center_card_le {x : G} (hxz : ∃ g : G, x = g * z * g⁻¹) {C : Subgroup G}
    (hC2 : IsPGroup 2 C) (hCx : C ≤ centralizer ({x} : Set G))
    (hcard : Nat.card T ≤ Nat.card C) :
    Set.ncard {a : G | a ∈ C ∧ ∀ u ∈ C, a * u = u * a} ≤ 4 := by
  obtain ⟨g, rfl⟩ := hxz
  have hcfg := c.h.oe.cfg
  set C' : Subgroup G := C.map (MulAut.conj g⁻¹).toMonoidHom with hC'
  have hC'2 : IsPGroup 2 C' := hC2.map _
  have hC'card : Nat.card C' = Nat.card C :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hC'z : C' ≤ centralizer ({z} : Set G) := by
    intro y hy
    have hy' := mem_conjMap.1 hy
    have hcomm := mem_centralizer_singleton_iff.1 (hCx hy')
    rw [mem_centralizer_singleton_iff]
    calc y * z = g⁻¹ * ((g * y * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * y * g⁻¹)) * g := by rw [hcomm]
      _ = z * y := by group
  have hTz : T ≤ centralizer ({z} : Set G) := hcfg.T_le
  have hT2 : IsPGroup 2 T := hcfg.T_pgroup
  have hCmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({z} : Set G) → C' ≤ P →
      P ≤ C' := by
    intro P hP hPz hle
    have h1 : Nat.card P ≤ Nat.card T := c.h.cent_z_card_le hP hPz
    have heq : C' = P := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [heq]
  have hTmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({z} : Set G) →
      T ≤ P → P ≤ T := by
    intro P hP hPz hle
    have h1 : Nat.card P ≤ Nat.card T := c.h.cent_z_card_le hP hPz
    have heq : T = P := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [heq]
  obtain ⟨h, -, hh⟩ := sylow_conj hTz hC'z hT2 hC'2 hTmax hCmax
  let f : G → G := fun a => h⁻¹ * (g⁻¹ * a * g) * h
  have hmem4 : ∀ a ∈ {a : G | a ∈ C ∧ ∀ u ∈ C, a * u = u * a},
      f a ∈ ({1, z, t, z * t} : Set G) := by
    rintro a ⟨ha, hcen⟩
    have haC' : g⁻¹ * a * g ∈ C' := by
      refine mem_conjMap.2 ?_
      simpa [mul_assoc] using ha
    have haT : f a ∈ T := by
      have := (hh (g⁻¹ * a * g)).1 haC'
      simpa [f, mul_assoc] using this
    have hcT : ∀ y ∈ T, y * f a = f a * y := by
      intro y hy
      have hy' : h * y * h⁻¹ ∈ C' := (hh _).2 (by simpa [mul_assoc] using hy)
      have hyC : g * (h * y * h⁻¹) * g⁻¹ ∈ C := mem_conjMap.1 hy'
      have h1 := hcen _ hyC
      calc y * f a = h⁻¹ * g⁻¹ * ((g * (h * y * h⁻¹) * g⁻¹) * a) * g * h := by
            simp only [f]; group
        _ = h⁻¹ * g⁻¹ * (a * (g * (h * y * h⁻¹) * g⁻¹)) * g * h := by rw [h1]
        _ = f a * y := by simp only [f]; group
    rcases hcfg.center_T (f a) haT hcT with h1 | h1 | h1 | h1
    · simp [h1]
    · simp [h1]
    · simp [h1]
    · simp [h1]
  have hinj : Set.InjOn f {a : G | a ∈ C ∧ ∀ u ∈ C, a * u = u * a} := by
    intro a _ b _ hab
    simp only [f] at hab
    have h1 := mul_right_cancel hab
    have h2 := mul_left_cancel h1
    have h3 := mul_right_cancel h2
    exact mul_left_cancel h3
  have h4 : Set.ncard ({1, z, t, z * t} : Set G) ≤ 4 := by
    have h1 : ({z * t} : Set G).ncard = 1 := Set.ncard_singleton _
    have h2 := Set.ncard_insert_le t ({z * t} : Set G)
    have h3 := Set.ncard_insert_le z (insert t ({z * t} : Set G))
    have h5 := Set.ncard_insert_le (1 : G) (insert z (insert t ({z * t} : Set G)))
    omega
  exact (Set.ncard_le_ncard_of_injOn f hmem4 hinj (Set.toFinite _)).trans h4

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
