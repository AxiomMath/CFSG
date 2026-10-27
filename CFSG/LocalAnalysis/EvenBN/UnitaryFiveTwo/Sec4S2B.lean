module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S2A
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSSix

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem fld_mem_X₄sub_sup_Fsub {g : SU52} (hg : g ∈ X₄sub ⊔ Fsub) : fld g ∈ X₄sub ⊔ Fsub := by
  rw [← commutator_Ssub_eq_X₄sub_sup_Fsub] at hg ⊢
  have hle : (⁅Ssub, Ssub⁆ : Subgroup SU52).map fld.toMonoidHom ≤ ⁅Ssub, Ssub⁆ := by
    rw [map_commutator]
    exact commutator_mono (fun _ ⟨x, hx, e⟩ => e ▸ fld_mem_Ssub hx)
      (fun _ ⟨x, hx, e⟩ => e ▸ fld_mem_Ssub hx)
  exact hle ⟨g, hg, rfl⟩

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_normalizer_S_of_mem_normalizer_XF (h : d.Hyp) {n : G} (hnH : n ∈ d.H)
    (hn : n ∈ normalizer ((d.X₄ ⊔ d.F : Subgroup G) : Set G)) :
    n ∈ normalizer (d.S : Set G) := by
  set φ : MulAut SU52 := h.act ⟨n, hnH⟩ with hφ
  have hφι : ∀ g, d.ι (φ g) = n * d.ι g * n⁻¹ := fun g => h.ι_act_apply ⟨n, hnH⟩ g
  have hφS' : ∀ g ∈ X₄sub ⊔ Fsub, φ g ∈ X₄sub ⊔ Fsub := fun g hg => by
    have hg' : d.ι g ∈ d.X₄ ⊔ d.F := by
      have : d.ι g ∈ d.pull (X₄sub ⊔ Fsub) := ⟨g, hg, rfl⟩
      rwa [d.pull_sup] at this
    have : d.ι (φ g) ∈ d.pull (X₄sub ⊔ Fsub) := by
      rw [hφι, d.pull_sup]
      exact (mem_normalizer_iff.1 hn _).1 hg'
    exact d.ι_mem_pull_iff.1 this
  have hS : ∀ g ∈ Ssub, φ g ∈ Ssub := by
    obtain ⟨s, hs | hs⟩ := exists_eq_conj_or_eq_conj_mul_fld φ
    · have hsN : s ∈ normalizer ((⁅Ssub, Ssub⁆ : Subgroup SU52) : Set SU52) := by
        rw [commutator_Ssub_eq_X₄sub_sup_Fsub]
        refine mem_normalizer_fintype fun y hy => ?_
        have := hφS' y hy
        rwa [hs, MulAut.conj_apply] at this
      rw [normalizer_commutator_Ssub] at hsN
      intro g hg
      rw [hs, MulAut.conj_apply]
      exact (mem_normalizer_iff.1 hsN g).1 hg
    · have hsN : s ∈ normalizer ((⁅Ssub, Ssub⁆ : Subgroup SU52) : Set SU52) := by
        rw [commutator_Ssub_eq_X₄sub_sup_Fsub]
        refine mem_normalizer_fintype fun y hy => ?_
        have := hφS' (fld y) (fld_mem_X₄sub_sup_Fsub hy)
        rwa [hs, MulAut.mul_apply, fld_fld, MulAut.conj_apply] at this
      rw [normalizer_commutator_Ssub] at hsN
      intro g hg
      rw [hs, MulAut.mul_apply, MulAut.conj_apply]
      exact (mem_normalizer_iff.1 hsN _).1 (fld_mem_Ssub hg)
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨g, hg, rfl⟩ := hx
  rw [← hφι]
  exact ⟨φ g, hS g hg, rfl⟩

theorem NHS_le_normalizer_R₃ (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.R₃ : Set G) := fun g hg =>
  mem_normalizer_fintype fun _ hx => conj_mem_oTwo (h.NHS_le_normalizer_R₂ hg) hx

theorem R₃D₂_inf_H_le_NHS (h : d.Hyp) :
    (d.R₃ ⊔ d.D₂) ⊓ d.H ≤ normalizer (d.S : Set G) ⊓ d.H := by
  intro n hn
  obtain ⟨hnP, hnH⟩ := Subgroup.mem_inf.1 hn
  obtain ⟨hnY, hnX⟩ := (sup_le h.R₃_le_cenMod h.D₂_le_cenMod) hnP
  have hL : ∀ x ∈ d.L, n * x * n⁻¹ ∈ d.L := fun x hx =>
    (mem_normalizer_iff.1 (h.H_le_normalizer hnH) x).1 hx
  have hFc : ∀ z ∈ d.L, z ∈ d.Y → z ∈ d.F := fun z hzL hzY =>
    (h.mem_F_iff_Y z).2 ⟨hzY, mem_centralizer_singleton_iff.1 (h.L_le_H hzL)⟩
  have hle : d.X₄ ⊔ d.F ≤ (d.X₄ ⊔ d.F).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun f hf => ?_)
    · change n * a * n⁻¹ ∈ d.X₄ ⊔ d.F
      have haL : a ∈ d.L := d.pull_le_L X₄sub ha
      have hc : n * a * n⁻¹ * a⁻¹ ∈ d.F := hFc _ (mul_mem (hL a haL) (inv_mem haL)) (hnX a ha)
      rw [show n * a * n⁻¹ = (n * a * n⁻¹ * a⁻¹) * a by group]
      exact mul_mem (mem_sup_right hc) (mem_sup_left ha)
    · change n * f * n⁻¹ ∈ d.X₄ ⊔ d.F
      exact mem_sup_right (hFc _ (hL f (h.F_le_L hf)) ((mem_normalizer_iff.1 hnY f).1
        (h.F_le_Y hf)))
  exact Subgroup.mem_inf.2 ⟨h.mem_normalizer_S_of_mem_normalizer_XF hnH
    (mem_normalizer_fintype fun x hx => hle hx), hnH⟩

theorem R₃D₂_inf_H_le_R (h : d.Hyp) : (d.R₃ ⊔ d.D₂) ⊓ d.H ≤ d.R := by
  refine h.le_R_of_isPGroup ((h.isPGroup_R₃_sup_D₂).to_le inf_le_left) h.R₃D₂_inf_H_le_NHS
    fun g hg q hq => ?_
  obtain ⟨hqP, hqH⟩ := Subgroup.mem_inf.1 hq
  have hgR₃ := h.NHS_le_normalizer_R₃ hg
  have hgD₂ : g ∈ normalizer (d.D₂ : Set G) := h.XC₀_le_normalizer_D₂ (h.NHS_le_XC₀ hg)
  have hle : d.R₃ ⊔ d.D₂ ≤ (d.R₃ ⊔ d.D₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun x hx => mem_sup_left ((mem_normalizer_iff.1 hgR₃ x).1 hx))
      (fun x hx => mem_sup_right ((mem_normalizer_iff.1 hgD₂ x).1 hx))
  exact Subgroup.mem_inf.2 ⟨hle hqP, mul_mem (mul_mem hg.2 hqH) (inv_mem hg.2)⟩

theorem exists_eq_mul_of_mem_R₃ (h : d.Hyp) {x : G} (hx : x ∈ d.R₃) :
    ∃ r ∈ d.R, ∃ e ∈ d.D₂, x = r * e := by
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₂ : Set G) ⊓ d.H) d.D₂
    (fun g hg => h.XC₀_le_normalizer_D₂ (h.NHA₂_le_XC₀ hg))
  obtain ⟨n, hn, e, he, rfl⟩ : x ∈ ((normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) : Set G) *
      (d.D₂ : Set G) := by
    rw [← hset, ← h.XC₀_eq_sup]
    exact h.R₃_le_XC₀ hx
  have hnP : n ∈ (d.R₃ ⊔ d.D₂) ⊓ d.H := by
    refine Subgroup.mem_inf.2 ⟨?_, hn.2⟩
    have := mul_mem (mem_sup_left hx : n * e ∈ d.R₃ ⊔ d.D₂) (inv_mem (mem_sup_right he))
    rwa [mul_inv_cancel_right] at this
  exact ⟨n, h.R₃D₂_inf_H_le_R hnP, e, he, rfl⟩

theorem R₃_le_R_sup_D₂ (h : d.Hyp) : d.R₃ ≤ d.R ⊔ d.D₂ := fun x hx => by
  obtain ⟨r, hr, e, he, rfl⟩ := h.exists_eq_mul_of_mem_R₃ hx
  exact mul_mem (mem_sup_left hr) (mem_sup_right he)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
