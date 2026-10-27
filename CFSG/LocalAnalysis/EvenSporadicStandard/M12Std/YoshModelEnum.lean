module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshES

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

section Image

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

theorem ψ_e (E : NEmb e₀ d α k) (he2 : orderOf e = 2) : ψ E (wp α k (swN eWord)) = e := by
  rw [ψ_wp, show swN eWord = [((5 : Fin 9), true)] by decide]
  exact val_e he2

theorem e_mem_EG (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    (hue : ueCheck α k = true) : e ∈ EG E := by
  obtain ⟨hEs, -⟩ := ueCheck_enum hue
  have hmem : nwT α k eWord ∈ wgens α k eWords :=
    (mem_wgens (α := α) (k := k)).2 ⟨eWord, by decide, rfl⟩
  have h : ψ E (wp α k (swN eWord)) ∈ EG E := by
    refine ψ_mem_img E (wp_mem α k _) ?_
    rw [← tp_nwT D (hEs.perm _ hmem)]
    exact Subgroup.subset_closure ⟨_, hmem, rfl⟩
  rwa [ψ_e E he2] at h

theorem img_closure (E : NEmb e₀ d α k) {P : Set (Equiv.Perm (Fin 16))} (hP : P ⊆ NG α k) :
    img E (Subgroup.closure P) = Subgroup.closure (ψ E '' P) := by
  have hle : Subgroup.closure P ≤ NG α k := (Subgroup.closure_le _).2 hP
  have key : ∀ g ∈ Subgroup.closure P, ψ E g ∈ Subgroup.closure (ψ E '' P) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure ⟨x, hx, rfl⟩
    | one => rw [ψ_one]; exact one_mem _
    | mul x y hx hy ihx ihy =>
      rw [ψ_mul E (hle hx) (hle hy)]
      exact mul_mem ihx ihy
    | inv x hx ihx =>
      rw [ψ_inv E (hle hx)]
      exact inv_mem ihx
  apply le_antisymm
  · intro y hy
    obtain ⟨g, -, hgK, rfl⟩ := (mem_img' E).1 hy
    exact key g hgK
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ψ_mem_img E (hP hx) (Subgroup.subset_closure hx)

theorem forall_mem_img_enum (E : NEmb e₀ d α k) {gens L : Array Table}
    (hL : EnumSpec 16 gens L) {φ : G → Prop}
    (H : ∀ T ∈ L, φ (ψ E (tablePerm 16 T))) : ∀ y ∈ img E (tsub gens), φ y := by
  rw [forall_mem_img' E]
  intro g _ hg
  exact hL.forall_mem (Q := fun g => φ (ψ E g)) H g hg

theorem exists_entry_of_mem_img (E : NEmb e₀ d α k) {gens L : Array Table}
    (hL : EnumSpec 16 gens L) (hK : tsub gens ≤ NG α k) {y : G} (hy : y ∈ img E (tsub gens)) :
    ∃ T ∈ L, y = ψ E (tablePerm 16 T) ∧ Rep 16 T (tablePerm 16 T) ∧ tablePerm 16 T ∈ NG α k := by
  obtain ⟨g, hg, hgK, rfl⟩ := (mem_img' E).1 hy
  obtain ⟨T, hT, hrep⟩ := hL.exists_entry hgK
  have h := tablePerm_eq hrep
  refine ⟨T, hT, ?_, ?_, ?_⟩
  · rw [h]
  · rw [h]; exact hrep
  · rw [h]; exact hg

theorem ψ_mem_img_enum (E : NEmb e₀ d α k) {gens L : Array Table}
    (hL : EnumSpec 16 gens L) (hK : tsub gens ≤ NG α k) {T : Table} (hT : T ∈ L) :
    ψ E (tablePerm 16 T) ∈ img E (tsub gens) :=
  ψ_mem_img E (hK (hL.rep_mem hT).2) (hL.rep_mem hT).2

theorem card_img_filter (E : NEmb e₀ d α k) {gens L : Array Table}
    (hL : EnumSpec 16 gens L) (hK : tsub gens ≤ NG α k) (φ : G → Prop) (P : Table → Bool)
    (hP : ∀ T ∈ L, P T = true ↔ φ (ψ E (tablePerm 16 T))) :
    Nat.card {y : G // y ∈ img E (tsub gens) ∧ φ y} = (L.toList.filter P).length := by
  rw [← hL.card_filter (fun g => φ (ψ E g)) P hP]
  symm
  refine Nat.card_eq_of_bijective
    (fun g => ⟨ψ E g.1, ψ_mem_img E (hK g.2.1) g.2.1, g.2.2⟩) ⟨?_, ?_⟩
  · intro g h hgh
    exact Subtype.ext (ψ_inj E (hK g.2.1) (hK h.2.1) (congrArg Subtype.val hgh))
  · rintro ⟨y, hy, hφ⟩
    obtain ⟨g, hg, hgK, rfl⟩ := (mem_img' E).1 hy
    exact ⟨⟨g, hgK, hφ⟩, rfl⟩

theorem img_inf_centralizer (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))}
    {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) :
    img E K ⊓ centralizer ({ψ E g} : Set G) = img E (K ⊓ centralizer ({g} : Set _)) := by
  ext y
  rw [Subgroup.mem_inf, mem_centralizer_singleton_iff, mem_img', mem_img']
  constructor
  · rintro ⟨⟨m, hm, hmK, rfl⟩, hyc⟩
    refine ⟨m, hm, Subgroup.mem_inf.2 ⟨hmK, mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
    rw [← ψ_mul E hm hg, ← ψ_mul E hg hm] at hyc
    exact ψ_inj E ((NG α k).mul_mem hm hg) ((NG α k).mul_mem hg hm) hyc
  · rintro ⟨m, hm, hK, rfl⟩
    obtain ⟨hmK, hmc⟩ := Subgroup.mem_inf.1 hK
    refine ⟨⟨m, hm, hmK, rfl⟩, ?_⟩
    rw [← ψ_mul E hm hg, ← ψ_mul E hg hm, mem_centralizer_singleton_iff.1 hmc]

theorem card_img_inf_centralizer (E : NEmb e₀ d α k) {gens L : Array Table}
    (hL : EnumSpec 16 gens L) (hK : tsub gens ≤ NG α k) {T : Table} {g : Equiv.Perm (Fin 16)}
    (hT : Rep 16 T g) (hg : g ∈ NG α k) :
    Nat.card (img E (tsub gens) ⊓ centralizer ({ψ E g} : Set G) : Subgroup G) =
      (L.toList.filter (commTT 16 T)).length := by
  rw [img_inf_centralizer E hg, card_img E (inf_le_left.trans hK)]
  exact hL.card_inf_centralizer hT

end Image

end CFSG.EvenSporadicStandard.M12Std.Yosh
