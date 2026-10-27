module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup

theorem map_conj_le_normalizer {Y : Type*} [Group Y] {A W : Subgroup Y} (g : Y)
    (h : A ≤ normalizer (W : Set Y)) :
    A.map (MulAut.conj g).toMonoidHom ≤
      normalizer ((W.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) := by
  rw [← map_equiv_normalizer_eq]
  exact map_mono h

theorem map_conj_zpowers {Y : Type*} [Group Y] (g x : Y) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers (g * x * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem card_map_conj {Y : Type*} [Group Y] (g : Y) (H : Subgroup Y) :
    Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = Nat.card ↥H :=
  card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_map_conj {Y : Type*} [Group Y] {p : ℕ} (g : Y) {H : Subgroup Y}
    (hH : IsPGroup p ↥H) : IsPGroup p ↥(H.map (MulAut.conj g).toMonoidHom) :=
  hH.map _

theorem le_zpowers_of_map_conj {Y : Type*} [Group Y] (g x : Y) {H : Subgroup Y}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ zpowers (g * x * g⁻¹)) : H ≤ zpowers x := by
  rw [← map_conj_zpowers] at h
  exact (map_le_map_iff_of_injective (MulAut.conj g).injective).1 h

theorem map_conj_le_centralizer {Y : Type*} [Group Y] {A : Subgroup Y} {t : Y} (g : Y)
    (h : A ≤ centralizer ({t} : Set Y)) :
    A.map (MulAut.conj g).toMonoidHom ≤ centralizer ({g * t * g⁻¹} : Set Y) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have hta : t * a = a * t := mem_centralizer_iff.1 (h ha) t rfl
  calc g * t * g⁻¹ * (MulAut.conj g).toMonoidHom a
      = g * (t * a) * g⁻¹ := by simp [MulAut.conj_apply, mul_assoc]
    _ = g * (a * t) * g⁻¹ := by rw [hta]
    _ = (MulAut.conj g).toMonoidHom a * (g * t * g⁻¹) := by simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_commutator {Y : Type*} [Group Y] (g : Y) (A : Subgroup Y) :
    ⁅A.map (MulAut.conj g).toMonoidHom, A.map (MulAut.conj g).toMonoidHom⁆ =
      (⁅A, A⁆).map (MulAut.conj g).toMonoidHom :=
  (map_commutator A A _).symm

theorem map_conj_le_normalizer_zpowers {Y : Type*} [Group Y] {A : Subgroup Y} {x : Y} (g : Y)
    (h : A ≤ normalizer (zpowers x : Set Y)) :
    A.map (MulAut.conj g).toMonoidHom ≤ normalizer (zpowers (g * x * g⁻¹) : Set Y) := by
  rw [← map_conj_zpowers]
  exact map_conj_le_normalizer g h

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
