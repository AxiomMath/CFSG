module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DR
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DFix
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DAbel

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f)
include d

theorem sylow_of_maximal [Finite G]
    (hmax : ∀ (H' : Subgroup G) (f' : G), InH x V H' f' → Nat.card H' ≤ Nat.card H) :
    Sylow2In H (centralizer (V : Set G)) := by
  by_contra hns
  obtain ⟨R, hR, hHR⟩ := exists_sylow_gt d.hI.H2 d.hI.H_le hns
  obtain ⟨n, hn1, hn, hRc, hX⟩ := d.cls_full hR hHR
  have hinv := d.inv_of_cls hX
  have hinvV := d.inv_mem_V hinv
  obtain ⟨f', hf'3, hf'R, hf'V, hf'x, hf'act⟩ := d.exists_f' hR hHR
  have hnc : ∃ v ∈ V, f' * v * f'⁻¹ ≠ v := by
    obtain ⟨v, hv, hne⟩ := d.exists_moved
    exact ⟨v, hv, by rw [hf'act v hv]; exact hne⟩
  have hxR : x ∈ R := hHR.le d.hI.x_mem
  have hfx : f' * x * f'⁻¹ = x := mul_inv_eq_iff_eq_mul.2 hf'x
  have hI' : InH x V R f' := by
    refine ⟨d.hI.E_le.trans hHR.le, fun r hr => (hR.le hr).1, hR.isPGroup, hf'3, hf'V, hf'R, ?_, ?_⟩
    · intro hc
      obtain ⟨v, hv, hne⟩ := hnc
      apply hne
      have := mem_centralizer_iff.1 hc v hv
      calc f' * v * f'⁻¹ = (f' * v) * f'⁻¹ := rfl
        _ = (v * f') * f'⁻¹ := by rw [← this]
        _ = v := by group
    · ext r
      constructor
      · rintro ⟨hrR, hrc⟩
        have hrf : f' * r = r * f' := mem_centralizer_iff.1 hrc f' rfl
        have hrfix : f' * r * f'⁻¹ = r := mul_inv_eq_iff_eq_mul.2 hrf
        have hcls : r * x * r⁻¹ ∈ cls (Mm V H) x := ⟨r, hR.le hrR, rfl⟩
        obtain ⟨q, hq, hqy⟩ := d.cls_sub hcls
        have hyH : r * x * r⁻¹ ∈ H := by
          rw [hqy]; exact H.mul_mem (d.H0_le hq) d.hI.x_mem
        have hyfix : f' * (r * x * r⁻¹) * f'⁻¹ = r * x * r⁻¹ := by
          calc f' * (r * x * r⁻¹) * f'⁻¹
              = (f' * r * f'⁻¹) * (f' * x * f'⁻¹) * (f' * r * f'⁻¹)⁻¹ := by group
            _ = r * x * r⁻¹ := by rw [hrfix, hfx]
        rcases d.cent_H_f' hinvV hf'3 hf'V hf'x hnc hyH hyfix with hy1 | hyx
        · exfalso
          apply d.out.x_ne
          calc x = r⁻¹ * (r * x * r⁻¹) * r := by group
            _ = 1 := by rw [hy1]; group
        · have hrx : r * x = x * r := by
            have := hyx
            exact mul_inv_eq_iff_eq_mul.1 this
          have hrC : r ∈ R ⊓ centralizer ({x} : Set G) := by
            refine ⟨hrR, ?_⟩
            show r ∈ centralizer ({x} : Set G)
            rw [mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            exact hrx.symm
          rw [d.R_inf_cent hR.isPGroup hR.le hHR.le] at hrC
          have hrH : r ∈ H := d.hI.E_le hrC
          rcases d.cent_H_f' hinvV hf'3 hf'V hf'x hnc hrH hrfix with h1 | h1
          · rw [h1]; exact one_mem _
          · rw [h1]; exact mem_zpowers x
      · intro hr
        rw [mem_zpowers_involution d.out.x_sq] at hr
        rcases hr with hr | hr
        · rw [hr]; exact ⟨one_mem _, one_mem _⟩
        · rw [hr]
          refine ⟨hxR, ?_⟩
          show x ∈ centralizer ({f'} : Set G)
          rw [mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hf'x
  have h1 := hmax R f' hI'
  have h2 := Subgroup.card_lt_of_lt hHR
  omega

end D13

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
