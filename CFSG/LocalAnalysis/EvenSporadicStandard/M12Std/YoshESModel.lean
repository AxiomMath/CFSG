module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshUEModel

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

theorem conj_inv_mem {Γ : Type*} [Group Γ] [Finite Γ] (E : Subgroup Γ) (n : Γ)
    (hn : ∀ x ∈ E, n * x * n⁻¹ ∈ E) : ∀ x ∈ E, n⁻¹ * x * n ∈ E := by
  let f : E → E := fun x => ⟨n * x * n⁻¹, hn x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h' : n * (x : Γ) * n⁻¹ = n * (y : Γ) * n⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h')
  intro x hx
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hf ⟨x, hx⟩
  have hy' : n * (y : Γ) * n⁻¹ = x := congrArg Subtype.val hy
  rw [← hy']
  simpa [mul_assoc] using y.2

theorem normalizes_of_gens {Γ : Type*} [Group Γ] [Finite Γ] (E : Subgroup Γ) (gens : Set Γ)
    (h : ∀ g ∈ gens, ∀ x ∈ E, g * x * g⁻¹ ∈ E) :
    ∀ n ∈ Subgroup.closure gens, ∀ x ∈ E, n * x * n⁻¹ ∈ E := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => intro x hx; simpa using hx
  | mul a b _ _ ha hb =>
    intro x hx
    have := ha _ (hb x hx)
    simpa [mul_assoc] using this
  | inv a _ ha => intro x hx; simpa using conj_inv_mem E a ha x hx

theorem ueCheck_enum {α k : ℕ} (h : ueCheck α k = true) :
    EnumSpec 16 (wgens α k eWords) (tenum (wgens α k eWords)) ∧
      EnumSpec 16 (wgens α k sWords) (tenum (wgens α k sWords)) := by
  unfold ueCheck ueCheckG at h
  simp only [Bool.and_eq_true] at h
  exact ⟨(tsub_spec h.1.1).1, (tsub_spec h.1.2).1⟩

section ES

variable {gE gS LE LS gN : Array Table} {cT : Table} {c : Equiv.Perm (Fin 16)}

theorem esEnumCheck_spec (hEs : EnumSpec 16 gE LE) (hSs : EnumSpec 16 gS LS) (hc : Rep 16 cT c)
    (hgN : ∀ T ∈ gN, permOK 16 T = true) (h : esEnumCheck gE gS cT LE LS gN = true) :
    (∀ s ∈ tsub gS, s * c = c * s) ∧
    (∀ z ∈ tsub gS, (∀ s ∈ tsub gS, z * s = s * z) → z = 1 ∨ z = c) ∧
    (∀ z ∈ tsub gE, (∀ s ∈ tsub gE, z * s = s * z) → z = 1 ∨ z = c) ∧
    (∀ n ∈ Subgroup.closure (tp 16 '' {x | x ∈ gN}), ∀ x ∈ tsub gE, n * x * n⁻¹ ∈ tsub gE) := by
  unfold esEnumCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hgE : ∀ T ∈ gE, Rep 16 T (tp 16 T) := fun T hT => rep_tp (hEs.perm T hT)
  have hgS : ∀ T ∈ gS, Rep 16 T (tp 16 T) := fun T hT => rep_tp (hSs.perm T hT)
  have hcen : ∀ {g : Array Table} {L : Array Table}, EnumSpec 16 g L →
      (∀ T ∈ g, Rep 16 T (tp 16 T)) →
      (L.toList.all fun y => !g.all (commTT 16 y) || tblEq 16 y (idT 16) || tblEq 16 y cT) = true →
      ∀ z ∈ tsub g, (∀ s ∈ tsub g, z * s = s * z) → z = 1 ∨ z = c := by
    intro g L hs hg hall z hz hzs
    obtain ⟨T, hT, hrep⟩ := hs.exists_entry hz
    have hy := List.all_eq_true.1 hall T (Array.mem_toList_iff.2 hT)
    have hcg : g.all (commTT 16 T) = true := by
      rw [Array.all_eq_true']
      intro T' hT'
      exact (commTT_iff hrep (hg T' hT')).2
        (hzs _ (Subgroup.subset_closure ⟨T', hT', rfl⟩))
    rw [hcg] at hy
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hy
    rcases hy with hy | hy
    · left
      exact (tblEq_iff_eq hrep (Rep.idT (by norm_num))).1 hy
    · right
      exact (tblEq_iff_eq hrep hc).1 hy
  refine ⟨?_, hcen hSs hgS h2, hcen hEs hgE h3, ?_⟩
  · have hle : tsub gS ≤ centralizer ({c} : Set (Equiv.Perm (Fin 16))) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨T, hT, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact ((commTT_iff hc (hgS T hT)).1 (Array.all_eq_true'.1 h1 T hT)).symm
    intro s hs
    exact mem_centralizer_singleton_iff.1 (hle hs)
  · apply normalizes_of_gens
    rintro _ ⟨T, hT, rfl⟩ x hx
    refine conj_mem_of_gens (tp 16 T) (fun T' hT' => ?_) x hx
    have := Array.all_eq_true'.1 (Array.all_eq_true'.1 h4 T hT) T' hT'
    exact (hEs.memTab_iff' (rep_conjT (by norm_num) (rep_tp (hgN T hT)) (hgE T' hT'))).1 this

end ES

end CFSG.EvenSporadicStandard.M12Std.Yosh
