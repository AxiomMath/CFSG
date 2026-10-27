module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSubCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshUE

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

theorem conj_mem_of_gens {gens : Array Table} (s : Equiv.Perm (Fin 16))
    (hs : ∀ T ∈ gens, s * tp 16 T * s⁻¹ ∈ tsub gens) :
    ∀ x ∈ tsub gens, s * x * s⁻¹ ∈ tsub gens := by
  intro x hx
  have : tsub gens ≤ (tsub gens).comap (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨T, hT, rfl⟩
    exact hs T hT
  simpa [MulAut.conj_apply] using this hx

section UE

variable {gE gS LE LS : Array Table} {cT : Table} {c : Equiv.Perm (Fin 16)}

theorem ueEnumCheck_spec (hEs : EnumSpec 16 gE LE) (hSs : EnumSpec 16 gS LS) (hc : Rep 16 cT c)
    (h : ueEnumCheck gE gS cT LE LS = true) :
    tsub gE ≤ tsub gS ∧
    (∀ s ∈ tsub gS, ∀ x ∈ tsub gE, s * x * s⁻¹ ∈ tsub gE) ∧
    c ∈ tsub gE ∧
    (∀ x ∈ tsub gE, x * x = 1 ∨ x * x = c) ∧
    (∀ x ∈ tsub gE, ∀ y ∈ tsub gE, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c) ∧
    (∃ s₁ ∈ tsub gS, ∃ s₂ ∈ tsub gS, ⁅s₁, s₂⁆ ∉ tsub gE) ∧
    (∀ y ∈ tsub gS, y ∉ tsub gE → (y * y = 1 ∨ y * y = c) →
      Nat.card {x : Equiv.Perm (Fin 16) // x ∈ tsub gE ∧ (⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c)} ≤ 32) ∧
    (∀ y₁ ∈ tsub gS, ∀ y₂ ∈ tsub gS, y₁ ∉ tsub gE → y₂ ∉ tsub gE →
      (y₁ * y₁ = 1 ∨ y₁ * y₁ = c) → (y₂ * y₂ = 1 ∨ y₂ * y₂ = c) →
      (∀ x ∈ tsub gE, ((⁅x, y₁⁆ = 1 ∨ ⁅x, y₁⁆ = c) ↔ (⁅x, y₂⁆ = 1 ∨ ⁅x, y₂⁆ = c))) →
      y₁⁻¹ * y₂ ∈ tsub gE) := by
  unfold ueEnumCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hgE : ∀ T ∈ gE, Rep 16 T (tp 16 T) := fun T hT => rep_tp (hEs.perm T hT)
  have hgS : ∀ T ∈ gS, Rep 16 T (tp 16 T) := fun T hT => rep_tp (hSs.perm T hT)
  have hES : tsub gE ≤ tsub gS := by
    rw [Subgroup.closure_le]
    rintro _ ⟨T, hT, rfl⟩
    exact (hSs.memTab_iff' (hgE T hT)).1 (Array.all_eq_true'.1 h1 T hT)
  have hnorm : ∀ s ∈ tsub gS, ∀ x ∈ tsub gE, s * x * s⁻¹ ∈ tsub gE := by
    intro s hs
    obtain ⟨Ts, hTs, hrs⟩ := hSs.exists_entry hs
    apply conj_mem_of_gens
    intro T hT
    have h2' := List.all_eq_true.1 h2 Ts (Array.mem_toList_iff.2 hTs)
    have h3' := Array.all_eq_true'.1 h2' T hT
    exact (hEs.memTab_iff' (rep_conjT (by norm_num) hrs (hgE T hT))).1 h3'
  have hcE : c ∈ tsub gE := (hEs.memTab_iff' hc).1 h3
  have hsq : ∀ x ∈ tsub gE, x * x = 1 ∨ x * x = c :=
    hEs.forall_toList fun T hT g hg =>
      (sqIn_iff (by norm_num) hc hg).1 (List.all_eq_true.1 h4 T hT)
  have hcomm : ∀ x ∈ tsub gE, ∀ y ∈ tsub gE, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c := by
    refine hEs.forall_forall_mem hEs fun a ha b hb => ?_
    have h5' := List.all_eq_true.1
      (List.all_eq_true.1 h5 a (Array.mem_toList_iff.2 ha)) b (Array.mem_toList_iff.2 hb)
    exact (commIn_iff (by norm_num) hc (hEs.rep_mem ha).1 (hEs.rep_mem hb).1).1 h5'
  have hC : ∃ s₁ ∈ tsub gS, ∃ s₂ ∈ tsub gS, ⁅s₁, s₂⁆ ∉ tsub gE := by
    obtain ⟨a, ha, h6'⟩ := Array.any_eq_true'.1 h6
    obtain ⟨b, hb, h6''⟩ := Array.any_eq_true'.1 h6'
    refine ⟨tp 16 a, subset_closure ⟨a, ha, rfl⟩, tp 16 b, subset_closure ⟨b, hb, rfl⟩, ?_⟩
    intro hmem
    have := (hEs.memTab_iff' (rep_commutatorT (by norm_num) (hgS a ha) (hgS b hb))).2 hmem
    rw [this] at h6''
    exact absurd h6'' (by simp)
  have hY : ∀ T ∈ LS, ∀ y : Equiv.Perm (Fin 16), Rep 16 T y → y ∉ tsub gE →
      (y * y = 1 ∨ y * y = c) →
      T ∈ LS.toList.filter fun y => !memTab 16 LE.toList y && sqIn 16 cT y := by
    intro T hT y hrep hyE hysq
    have hnm : memTab 16 LE.toList T = false := by
      cases hm : memTab 16 LE.toList T
      · rfl
      · exact absurd ((hEs.memTab_iff' hrep).1 hm) hyE
    exact List.mem_filter.2 ⟨Array.mem_toList_iff.2 hT, by
      simp [hnm, (sqIn_iff (by norm_num) hc hrep).2 hysq]⟩
  have hA : ∀ y ∈ tsub gS, y ∉ tsub gE → (y * y = 1 ∨ y * y = c) →
      Nat.card {x : Equiv.Perm (Fin 16) // x ∈ tsub gE ∧ (⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c)} ≤ 32 := by
    intro y hy hyE hysq
    obtain ⟨T, hT, hrep⟩ := hSs.exists_entry hy
    have h7' := List.all_eq_true.1 h7 T (hY T hT y hrep hyE hysq)
    rw [decide_eq_true_eq] at h7'
    have := hEs.card_filter (fun x => ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c) (fun T' => commIn 16 cT T' T)
      (fun T' hT' => commIn_iff (by norm_num) hc (hEs.rep_mem hT').1 hrep)
    rw [this]
    exact h7'
  have hB : ∀ y₁ ∈ tsub gS, ∀ y₂ ∈ tsub gS, y₁ ∉ tsub gE → y₂ ∉ tsub gE →
      (y₁ * y₁ = 1 ∨ y₁ * y₁ = c) → (y₂ * y₂ = 1 ∨ y₂ * y₂ = c) →
      (∀ x ∈ tsub gE, ((⁅x, y₁⁆ = 1 ∨ ⁅x, y₁⁆ = c) ↔ (⁅x, y₂⁆ = 1 ∨ ⁅x, y₂⁆ = c))) →
      y₁⁻¹ * y₂ ∈ tsub gE := by
    intro y₁ hy₁ y₂ hy₂ hy₁E hy₂E hsq₁ hsq₂ hiff
    obtain ⟨T₁, hT₁, hr₁⟩ := hSs.exists_entry hy₁
    obtain ⟨T₂, hT₂, hr₂⟩ := hSs.exists_entry hy₂
    have h8' := List.all_eq_true.1 (List.all_eq_true.1 h8 (T₁, LE.toList.map fun x =>
      commIn 16 cT x T₁) (List.mem_map.2 ⟨T₁, hY T₁ hT₁ y₁ hr₁ hy₁E hsq₁, rfl⟩))
      (T₂, LE.toList.map fun x => commIn 16 cT x T₂)
      (List.mem_map.2 ⟨T₂, hY T₂ hT₂ y₂ hr₂ hy₂E hsq₂, rfl⟩)
    have hsig : (LE.toList.map fun x => commIn 16 cT x T₁) =
        (LE.toList.map fun x => commIn 16 cT x T₂) := by
      refine List.map_congr_left fun x hx => ?_
      have hrx := (hEs.rep_mem (Array.mem_toList_iff.1 hx)).1
      have hmx := (hEs.rep_mem (Array.mem_toList_iff.1 hx)).2
      rw [Bool.eq_iff_iff, commIn_iff (by norm_num) hc hrx hr₁,
        commIn_iff (by norm_num) hc hrx hr₂]
      exact hiff _ hmx
    simp only [hsig, bne_self_eq_false, Bool.false_or] at h8'
    exact (hEs.memTab_iff' ((rep_invT_of_rep (by norm_num) hr₁).compT hr₂)).1 h8'
  exact ⟨hES, hnorm, hcE, hsq, hcomm, hC, hA, hB⟩

theorem ueCheckG_spec (hc : Rep 16 cT c) (h : ueCheckG gE gS cT = true) :
    Nat.card (tsub gE) = 128 ∧ Nat.card (tsub gS) = 1024 ∧ tsub gE ≤ tsub gS ∧
    (∀ s ∈ tsub gS, ∀ x ∈ tsub gE, s * x * s⁻¹ ∈ tsub gE) ∧ c ∈ tsub gE ∧
    (∀ x ∈ tsub gE, x * x = 1 ∨ x * x = c) ∧
    (∀ x ∈ tsub gE, ∀ y ∈ tsub gE, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c) ∧
    (∀ D : Subgroup (Equiv.Perm (Fin 16)), D ≤ tsub gS → Nat.card D = 128 →
      (∀ x ∈ D, x * x = 1 ∨ x * x = c) → (∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c) →
      D = tsub gE) := by
  unfold ueCheckG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨hEs, -⟩ := tsub_spec h1
  obtain ⟨hSs, -⟩ := tsub_spec h2
  have hE := card_tsub h1
  have hS := card_tsub h2
  obtain ⟨hES, hnorm, hcE, hsq, hcomm, hC, hA, hB⟩ := ueEnumCheck_spec hEs hSs hc h3
  refine ⟨hE, hS, hES, hnorm, hcE, hsq, hcomm, fun D hDS hD hDsq hDcomm => ?_⟩
  exact ue_unique (tsub gS) (tsub gE) D c hES hDS hnorm hcE hS hE hD hDsq hDcomm hC hA hB

end UE

end CFSG.EvenSporadicStandard.M12Std.Yosh
