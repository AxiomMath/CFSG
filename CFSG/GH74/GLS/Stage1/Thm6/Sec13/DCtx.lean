module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L131b
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Dprep
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ClassCard

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

structure D13 (x : G) (T V H : Subgroup G) (f : G) : Prop where
  out : Out12 G x T V
  hI : InH x V H f
  iv1 : Hzero H f ⊓ zpowers x = ⊥
  iv2 : Hzero H f ⊔ zpowers x = H
  iv3 : ∀ g ∈ H, ∀ q ∈ Hzero H f, g * q * g⁻¹ ∈ Hzero H f
  iv4 : IsYGroup ↥(Hzero H f)
  cl1 : ∀ g : G, g ∈ normalizer (V : Set G) → g ∈ normalizer (H : Set G) →
    cj g (Hzero H f) = Hzero H f

theorem conj_mem_Mm {V H : Subgroup G} {f m : G} (hfV : f ∈ normalizer (V : Set G))
    (hfH : f ∈ normalizer (H : Set G)) (hm : m ∈ Mm V H) : f * m * f⁻¹ ∈ Mm V H := by
  refine ⟨?_, (normalizer (H : Set G)).mul_mem
    ((normalizer (H : Set G)).mul_mem hfH hm.2) ((normalizer (H : Set G)).inv_mem hfH)⟩
  show f * m * f⁻¹ ∈ centralizer (V : Set G)
  rw [mem_centralizer_iff]
  intro v hv
  have hv' : f⁻¹ * v * f ∈ V := (mem_normalizer_iff''.1 hfV v).1 hv
  have hc := mem_centralizer_iff.1 hm.1 (f⁻¹ * v * f) hv'
  calc v * (f * m * f⁻¹) = f * ((f⁻¹ * v * f) * m) * f⁻¹ := by group
    _ = f * (m * (f⁻¹ * v * f)) * f⁻¹ := by rw [hc]
    _ = (f * m * f⁻¹) * v := by group

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f)
include d

theorem x_not_mem_H0 : x ∉ Hzero H f := InH.x_not_mem_of_inf d.out d.iv1

theorem H0_le : Hzero H f ≤ H := le_trans le_sup_left d.iv2.le

theorem f_x : f * x * f⁻¹ = x := mul_inv_eq_iff_eq_mul.2 d.hI.f_comm_x

theorem conj_mem {g : G} (hgN : g ∈ normalizer (V : Set G)) (hgH : g ∈ normalizer (H : Set G)) :
    ∃ q ∈ Hzero H f, g * x * g⁻¹ = q * x := by
  have hxH : x ∈ H := d.hI.x_mem
  have hy : g * x * g⁻¹ ∈ H := (mem_normalizer_iff.1 hgH x).1 hxH
  rw [← d.iv2] at hy
  obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_invol d.out.x_sq (fun q hq => d.iv3 x hxH q hq)).1 hy
  · exfalso
    apply d.x_not_mem_H0
    have h2 : g * x * g⁻¹ ∈ cj g (Hzero H f) := by rw [d.cl1 g hgN hgH, h1]; exact hq
    have h3 := mem_cj.1 h2
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e] at h3
    exact h3
  · exact ⟨q, hq, h1⟩

theorem cls_sub {y : G} (hy : y ∈ cls (Mm V H) x) : ∃ q ∈ Hzero H f, y = q * x := by
  obtain ⟨m, hm, rfl⟩ := hy
  exact d.conj_mem (centralizer_le_normalizer _ hm.1) hm.2

theorem f_stable {y : G} (hy : y ∈ cls (Mm V H) x) : f * y * f⁻¹ ∈ cls (Mm V H) x := by
  obtain ⟨m, hm, rfl⟩ := hy
  refine ⟨f * m * f⁻¹, conj_mem_Mm d.hI.f_N d.hI.f_H hm, ?_⟩
  calc f * (m * x * m⁻¹) * f⁻¹ = (f * m * f⁻¹) * (f * x * f⁻¹) * (f * m * f⁻¹)⁻¹ := by group
    _ = (f * m * f⁻¹) * x * (f * m * f⁻¹)⁻¹ := by rw [d.f_x]

theorem fix_eq {y : G} (hy : y ∈ cls (Mm V H) x) (hfy : f * y * f⁻¹ = y) : y = x := by
  obtain ⟨q, hq, rfl⟩ := d.cls_sub hy
  have hH : q * x ∈ H := H.mul_mem (d.H0_le hq) d.hI.x_mem
  have hc : q * x ∈ H ⊓ centralizer ({f} : Set G) := by
    refine ⟨hH, ?_⟩
    show q * x ∈ centralizer ({f} : Set G)
    rw [mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact mul_inv_eq_iff_eq_mul.1 hfy
  rw [d.hI.C_H, mem_zpowers_involution d.out.x_sq] at hc
  rcases hc with h1 | h1
  · exfalso
    obtain ⟨m, -, hmy⟩ := hy
    have h2 : m * x * m⁻¹ = 1 := by rw [← hmy]; exact h1
    apply d.out.x_ne
    calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
      _ = 1 := by rw [h2]; group
  · exact h1

end D13

theorem x_mem_cls {x : G} {M : Subgroup G} : x ∈ cls M x :=
  ⟨1, one_mem _, by simp⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
