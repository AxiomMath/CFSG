module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section FirstFactor

variable {G : Type*} [Group G] {t : G}

theorem linearSwapDiag_injective {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) :
    Function.Injective (linearSwapDiag hA) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [linearSwapDiag_apply] at ha
  have h1 : (a : G) = (t * a * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left ha
  have hmem : (a : G) ∈ A ⊓ A.map (MulAut.conj t).toMonoidHom := by
    refine mem_inf.2 ⟨a.2, ?_⟩
    rw [h1]
    exact (A.map (MulAut.conj t).toMonoidHom).inv_mem ⟨a, a.2, rfl⟩
  rw [hAA, mem_bot] at hmem
  exact Subtype.ext hmem

theorem exists_mem_mul_conj_eq_of_mem_sup (ht : t * t = 1) {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {y : G}
    (hy : y ∈ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hyt : t * y = y * t) :
    ∃ a ∈ A, a * (t * a * t⁻¹) = y := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have comm : ∀ (a : A) (b : A.map (MulAut.conj t).toMonoidHom),
      Commute (A.subtype a) ((A.map (MulAut.conj t).toMonoidHom).subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hA b.2) a a.2)
  have hr := MonoidHom.noncommCoprod_range A.subtype
    (A.map (MulAut.conj t).toMonoidHom).subtype comm
  rw [range_subtype, range_subtype] at hr
  rw [← hr] at hy
  obtain ⟨⟨a, b⟩, hab⟩ := hy
  rw [MonoidHom.noncommCoprod_apply] at hab
  obtain ⟨a', ha', hb⟩ := b.2
  change (a : G) * b = y at hab
  change t * a' * t⁻¹ = (b : G) at hb
  have hty : t * y * t⁻¹ = (t * a * t⁻¹) * a' := by
    rw [← hab, ← hb]
    calc t * (↑a * (t * a' * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * ((t * t) * a' * (t⁻¹ * t⁻¹)) := by
          group
      _ = (t * a * t⁻¹) * a' := by
          rw [ht, ← mul_inv_rev, ht, inv_one, one_mul, mul_one]
  have hyy : t * y * t⁻¹ = y := by rw [hyt, mul_inv_cancel_right]
  have hc : (t * a * t⁻¹) * a' = a' * (t * a * t⁻¹) :=
    (mem_centralizer_iff.1 (hA ⟨a, a.2, rfl⟩) a' ha').symm
  have hkey : (a : G)⁻¹ * a' = t * (a' * (a : G)⁻¹) * t⁻¹ := by
    have h1 : a' * (t * a * t⁻¹) = (a : G) * (t * a' * t⁻¹) := by
      rw [← hc, ← hty, hyy, ← hab, ← hb]
    calc (a : G)⁻¹ * a' = (a : G)⁻¹ * (a' * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
      _ = (a : G)⁻¹ * ((a : G) * (t * a' * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by rw [h1]
      _ = t * (a' * (a : G)⁻¹) * t⁻¹ := by group
  have hmem : (a : G)⁻¹ * a' ∈ A ⊓ A.map (MulAut.conj t).toMonoidHom := by
    refine mem_inf.2 ⟨A.mul_mem (A.inv_mem a.2) ha', ?_⟩
    rw [hkey]
    exact ⟨a' * (a : G)⁻¹, A.mul_mem ha' (A.inv_mem a.2), rfl⟩
  rw [hAA, mem_bot] at hmem
  have haa : a' = (a : G) := by
    calc a' = (a : G) * ((a : G)⁻¹ * a') := by group
      _ = a := by rw [hmem, mul_one]
  refine ⟨a, a.2, ?_⟩
  rw [← hab, ← hb, haa]

theorem exists_firstFactor_of_le_sup (ht : t * t = 1) {A D : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hDA : D ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom)
    (hDt : D ≤ centralizer ({t} : Set G)) (hperf : ⁅D, D⁆ = D) :
    ∃ F : Subgroup G, F ≤ A ∧ ⁅F, F⁆ = F ∧
      (∀ x ∈ F, x * (t * x * t⁻¹) ∈ D) ∧ ∀ y ∈ D, ∃ x ∈ F, x * (t * x * t⁻¹) = y := by
  set δ := linearSwapDiag hA with hδ
  have hinj := linearSwapDiag_injective hA hAA
  set T : Subgroup A := D.comap δ with hT
  have hTD : T.map δ = D := by
    refine le_antisymm (map_comap_le _ _) fun y hy => ?_
    obtain ⟨a, ha, hay⟩ := exists_mem_mul_conj_eq_of_mem_sup ht hA hAA (hDA hy)
      (mem_centralizer_singleton_iff.1 (hDt hy)).symm
    refine ⟨⟨a, ha⟩, ?_, hay⟩
    change δ ⟨a, ha⟩ ∈ D
    rw [hδ, linearSwapDiag_apply]
    change a * (t * a * t⁻¹) ∈ D
    rw [hay]
    exact hy
  have hTperf : ⁅T, T⁆ = T := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hTD, hperf]
  refine ⟨T.map A.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hTperf]
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := (hTD ▸ hy : y ∈ T.map δ)
    exact ⟨x, ⟨x, hx, rfl⟩, hxy⟩

theorem map_conj_le_centralizer_comm (ht : t * t = 1) {A B : Subgroup G}
    (h : B.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) :
    A.map (MulAut.conj t).toMonoidHom ≤ centralizer (B : Set G) := by
  have key : ∀ z : G, t * (t * z * t⁻¹) * t⁻¹ = z := fun z => by
    calc t * (t * z * t⁻¹) * t⁻¹ = (t * t) * z * (t * t)⁻¹ := by group
      _ = z := by rw [ht, one_mul, inv_one, mul_one]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  intro y hy
  have h1 : x * (t * y * t⁻¹) = (t * y * t⁻¹) * x := mem_centralizer_iff.1 (h ⟨y, hy, rfl⟩) x hx
  change y * (t * x * t⁻¹) = (t * x * t⁻¹) * y
  have h2 : (t * x * t⁻¹) * (t * (t * y * t⁻¹) * t⁻¹) =
      (t * (t * y * t⁻¹) * t⁻¹) * (t * x * t⁻¹) := by
    calc (t * x * t⁻¹) * (t * (t * y * t⁻¹) * t⁻¹) = t * (x * (t * y * t⁻¹)) * t⁻¹ := by group
      _ = t * ((t * y * t⁻¹) * x) * t⁻¹ := by rw [h1]
      _ = (t * (t * y * t⁻¹) * t⁻¹) * (t * x * t⁻¹) := by group
  rw [key] at h2
  exact h2.symm

end FirstFactor

end CFSG.SeitzReduction.LinearPilot
