module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Gen

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG
open scoped commutatorElement

section Diagonal

variable {N : Type} [Group N]

@[expose] def zDiagHom (J : Subgroup N) (z : N)
    (hc : ∀ x ∈ J, ∀ y ∈ J, (z * x * z⁻¹) * y = y * (z * x * z⁻¹)) : ↥J →* N :=
  MonoidHom.mk' (fun x : ↥J => (x : N) * (z * (x : N) * z⁻¹)) fun x y => by
    have h := hc (x : N) x.2 (y : N) y.2
    show (x : N) * (y : N) * (z * ((x : N) * (y : N)) * z⁻¹) =
      (x : N) * (z * (x : N) * z⁻¹) * ((y : N) * (z * (y : N) * z⁻¹))
    calc (x : N) * (y : N) * (z * ((x : N) * (y : N)) * z⁻¹)
        = (x : N) * ((y : N) * (z * (x : N) * z⁻¹)) * (z * (y : N) * z⁻¹) := by group
      _ = (x : N) * ((z * (x : N) * z⁻¹) * (y : N)) * (z * (y : N) * z⁻¹) := by rw [← h]
      _ = (x : N) * (z * (x : N) * z⁻¹) * ((y : N) * (z * (y : N) * z⁻¹)) := by group

theorem zDiagHom_apply (J : Subgroup N) (z : N)
    (hc : ∀ x ∈ J, ∀ y ∈ J, (z * x * z⁻¹) * y = y * (z * x * z⁻¹)) (x : ↥J) :
    zDiagHom J z hc x = (x : N) * (z * (x : N) * z⁻¹) := rfl

theorem ker_zDiagHom_le_center (J : Subgroup N) (z : N)
    (hc : ∀ x ∈ J, ∀ y ∈ J, (z * x * z⁻¹) * y = y * (z * x * z⁻¹)) :
    (zDiagHom J z hc).ker ≤ Subgroup.center ↥J := by
  intro x hx
  rw [MonoidHom.mem_ker, zDiagHom_apply] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : (x : N) = (z * (x : N) * z⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hx
  have h2 : (x : N) = z * (x : N)⁻¹ * z⁻¹ :=
    h1.trans (by group)
  apply Subtype.ext
  show (y : N) * (x : N) = (x : N) * (y : N)
  have h3 := hc ((x : N)⁻¹) (J.inv_mem x.2) (y : N) y.2
  rw [← h2] at h3
  exact h3.symm

theorem isQuasisimple_range_zDiagHom {J : Subgroup N} (hJ : IsQuasisimple ↥J) (z : N)
    (hc : ∀ x ∈ J, ∀ y ∈ J, (z * x * z⁻¹) * y = y * (z * x * z⁻¹)) :
    IsQuasisimple ↥(zDiagHom J z hc).range :=
  CFSG.LocalCores.isQuasisimple_of_surjective hJ (zDiagHom J z hc).rangeRestrict
    (zDiagHom J z hc).rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact ker_zDiagHom_le_center J z hc)

theorem zDiagHom_conj {J : Subgroup N} {z : N}
    (hc : ∀ x ∈ J, ∀ y ∈ J, (z * x * z⁻¹) * y = y * (z * x * z⁻¹)) {v : N}
    (hvz : v * z = z * v) (x : ↥J) (hx₁ : v * (x : N) * v⁻¹ ∈ J) :
    zDiagHom J z hc ⟨v * (x : N) * v⁻¹, hx₁⟩ = v * zDiagHom J z hc x * v⁻¹ := by
  have hvz' : v * z * v⁻¹ = z := by rw [hvz]; group
  rw [zDiagHom_apply, zDiagHom_apply]
  show v * (x : N) * v⁻¹ * (z * (v * (x : N) * v⁻¹) * z⁻¹) =
    v * ((x : N) * (z * (x : N) * z⁻¹)) * v⁻¹
  calc v * (x : N) * v⁻¹ * (z * (v * (x : N) * v⁻¹) * z⁻¹)
      = (v * (x : N) * v⁻¹) * ((v * z * v⁻¹) * (v * (x : N) * v⁻¹) * (v * z * v⁻¹)⁻¹) := by
        rw [hvz']
    _ = v * ((x : N) * (z * (x : N) * z⁻¹)) * v⁻¹ := by group

theorem commutator_mem_centralizer_of_inv_mul_conj {J : Subgroup N} {x a : N} (hx : x ∈ J)
    (hw : x⁻¹ * (a * x * a⁻¹) ∈ centralizer (J : Set N)) :
    ⁅x, a⁆ ∈ centralizer (J : Set N) := by
  have hxw : x * (x⁻¹ * (a * x * a⁻¹)) = (x⁻¹ * (a * x * a⁻¹)) * x :=
    Subgroup.mem_centralizer_iff.mp hw x hx
  have h3 : x * (x⁻¹ * (a * x * a⁻¹))⁻¹ = (x⁻¹ * (a * x * a⁻¹))⁻¹ * x :=
    (Commute.inv_right (show Commute x (x⁻¹ * (a * x * a⁻¹)) from hxw)).eq
  have hxa : x * a * x⁻¹ * a⁻¹ = (x⁻¹ * (a * x * a⁻¹))⁻¹ := by
    calc x * a * x⁻¹ * a⁻¹ = (x * (x⁻¹ * (a * x * a⁻¹))⁻¹) * x⁻¹ := by group
      _ = ((x⁻¹ * (a * x * a⁻¹))⁻¹ * x) * x⁻¹ := by rw [h3]
      _ = (x⁻¹ * (a * x * a⁻¹))⁻¹ := by group
  rw [commutatorElement_def, hxa]
  exact Subgroup.inv_mem _ hw

end Diagonal

theorem mem_normalizer_of_diagonal {N : Type} [Group N] [Finite N] {J : Subgroup N}
    (hJ : IsComponent J) {p : ℕ} (hp : p.Prime) {V O : Subgroup N} {z : N}
    (hzz : z * z = 1) (hVO : V ≤ O) (hOp : IsPGroup p ↥O) (hOz : ∀ o ∈ O, o * z = z * o)
    (hON : ∀ c : N, c * z = z * c → ∀ o ∈ O, c * o * c⁻¹ ∈ O)
    (hVn : V ≤ normalizer (J : Set N))
    (hfaith : ∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N)) (hV1 : V ≠ ⊥) :
    z ∈ normalizer (J : Set N) := by
  by_contra hzn
  have hJc : IsComponent (J.map (MulAut.conj z).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z) hJ
  have hcomm : ⁅J, J.map (MulAut.conj z).toMonoidHom⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hJ hJc with h | h
    · exact absurd (mem_normalizer_iff_map_conj_eq.mpr h.symm) hzn
    · exact h
  have hc : ∀ x ∈ J, ∀ y ∈ J, (z * x * z⁻¹) * y = y * (z * x * z⁻¹) := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hy
    exact Subgroup.mem_centralizer_iff.mp hle _ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  set D : Subgroup N := (zDiagHom J z hc).range
  have hDq : IsQuasisimple ↥D := isQuasisimple_range_zDiagHom hJ.1 z hc
  have hVz : ∀ v ∈ V, v * z = z * v := fun v hv => hOz v (hVO hv)
  have hDz : ∀ d ∈ D, d * z = z * d := by
    intro d hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hd
    rw [zDiagHom_apply]
    have hzx : z * (z * (x : N) * z⁻¹) * z⁻¹ = x := by
      calc z * (z * (x : N) * z⁻¹) * z⁻¹ = (z * z) * (x : N) * (z * z)⁻¹ := by group
        _ = x := by rw [hzz]; group
    have hd : z * ((x : N) * (z * (x : N) * z⁻¹)) * z⁻¹ = (x : N) * (z * (x : N) * z⁻¹) := by
      calc z * ((x : N) * (z * (x : N) * z⁻¹)) * z⁻¹
          = (z * (x : N) * z⁻¹) * (z * (z * (x : N) * z⁻¹) * z⁻¹) := by group
        _ = (z * (x : N) * z⁻¹) * x := by rw [hzx]
        _ = (x : N) * (z * (x : N) * z⁻¹) := hc x x.2 x x.2
    exact (mul_inv_eq_iff_eq_mul.mp hd).symm
  have hDO : ∀ d ∈ D, ∀ o ∈ O, d * o * d⁻¹ ∈ O := fun d hd o ho => hON d (hDz d hd) o ho
  have hVD : ∀ v ∈ V, ∀ d ∈ D, v * d * v⁻¹ ∈ D := by
    intro v hv d hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hd
    have hx₁ : v * (x : N) * v⁻¹ ∈ J := (mem_normalizer_iff.mp (hVn hv) x).mp x.2
    exact ⟨⟨_, hx₁⟩, zDiagHom_conj hc (hVz v hv) x hx₁⟩
  have hVnD : V ≤ normalizer (D : Set N) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨fun hd => hVD v hv d hd, fun hd => ?_⟩
    have := hVD v⁻¹ (V.inv_mem hv) _ hd
    simpa [mul_assoc] using this
  set O₁ : Subgroup N := O ⊓ normalizer (D : Set N)
  have hO₁p : IsPGroup p ↥O₁ := hOp.to_le inf_le_left
  have hDO₁ : ∀ d ∈ D, d ∈ normalizer (O₁ : Set N) := by
    have key : ∀ d ∈ D, ∀ y ∈ O₁, d * y * d⁻¹ ∈ O₁ := fun d hd y hy =>
      ⟨hDO d hd y hy.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hd) hy.2)
        (Subgroup.inv_mem _ (Subgroup.le_normalizer hd))⟩
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key d hd y, fun hy => ?_⟩
    have := key d⁻¹ (D.inv_mem hd) _ hy
    simpa [mul_assoc] using this
  have hcent : O₁ ≤ centralizer (D : Set N) :=
    L915.commute_of_normal_pgroup_of_normal_quasisimple (Y := N) hp
      (H := normalizer (D : Set N) ⊓ normalizer (O₁ : Set N)) (U := O₁) (I := D) hDq
      (le_inf Subgroup.le_normalizer hDO₁) (fun h hh => hh.1)
      (fun x hx => ⟨hx.2, Subgroup.le_normalizer hx⟩) (fun h hh => hh.2) hO₁p
  have hVc : V ≤ centralizer (D : Set N) := fun v hv => hcent (le_inf hVO hVnD hv)
  have hcomm2 : ⁅J, V⁆ ≤ centralizer (J : Set N) := by
    refine Subgroup.commutator_le.mpr fun x hx v hv => ?_
    have hx₁ : v * x * v⁻¹ ∈ J := (mem_normalizer_iff.mp (hVn hv) x).mp hx
    have hvD : v * ((x : N) * (z * x * z⁻¹)) = (x * (z * x * z⁻¹)) * v :=
      (Subgroup.mem_centralizer_iff.mp (hVc hv) (x * (z * x * z⁻¹))
        ⟨⟨x, hx⟩, rfl⟩).symm
    have h := zDiagHom_conj hc (hVz v hv) ⟨x, hx⟩ hx₁
    have h' : v * x * v⁻¹ * (z * (v * x * v⁻¹) * z⁻¹) = x * (z * x * z⁻¹) := by
      have h0 : v * (x * (z * x * z⁻¹)) * v⁻¹ = x * (z * x * z⁻¹) := by
        rw [hvD]; group
      rw [zDiagHom_apply, zDiagHom_apply] at h
      exact h.trans h0
    have hw : x⁻¹ * (v * x * v⁻¹) = z * (x * (v * x * v⁻¹)⁻¹) * z⁻¹ := by
      calc x⁻¹ * (v * x * v⁻¹)
          = x⁻¹ * ((v * x * v⁻¹) * (z * (v * x * v⁻¹) * z⁻¹)) *
              (z * (v * x * v⁻¹) * z⁻¹)⁻¹ := by group
        _ = x⁻¹ * (x * (z * x * z⁻¹)) * (z * (v * x * v⁻¹) * z⁻¹)⁻¹ := by rw [h']
        _ = z * (x * (v * x * v⁻¹)⁻¹) * z⁻¹ := by group
    refine commutator_mem_centralizer_of_inv_mul_conj hx ?_
    rw [hw, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc _ (J.mul_mem hx (J.inv_mem hx₁)) y hy).symm
  have hVcJ : V ≤ centralizer (J : Set N) :=
    L915.le_centralizer_of_commutator_le_centralizer hJ.1.1 hcomm2
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  refine hfaith v hv hv1' fun x hx => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp (hVcJ hv) x hx

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
