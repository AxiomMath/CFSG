module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelEnum

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

section Word

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

@[expose] noncomputable def pw (α k : ℕ) (W : List Int) : Equiv.Perm (Fin 16) := wp α k (swN W)

theorem pw_mem (α k : ℕ) (W : List Int) : pw α k W ∈ NG α k := wp_mem α k _

theorem rep_pw (D : FusionData α k) (W : List Int) : Rep 16 (nwT α k W) (pw α k W) :=
  rep_nwT D W

theorem ψ_pw (E : NEmb e₀ d α k) (W : List Int) : ψ E (pw α k W) = val e₀ d α (swN W) :=
  ψ_wp E _

theorem ψ_comm_iff (E : NEmb e₀ d α k) {g h : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k)
    (hh : h ∈ NG α k) : ψ E g * ψ E h = ψ E h * ψ E g ↔ g * h = h * g := by
  rw [← ψ_mul E hg hh, ← ψ_mul E hh hg]
  exact ⟨ψ_inj E ((NG α k).mul_mem hg hh) ((NG α k).mul_mem hh hg), fun h => by rw [h]⟩

theorem commTT_ψ (E : NEmb e₀ d α k) {S T : Table} {g h : Equiv.Perm (Fin 16)}
    (hS : Rep 16 S g) (hT : Rep 16 T h) (hg : g ∈ NG α k) (hh : h ∈ NG α k) :
    commTT 16 S T = true ↔ ψ E g * ψ E h = ψ E h * ψ E g :=
  (commTT_iff hS hT).trans (ψ_comm_iff E hg hh).symm

theorem tblEq_ψ (E : NEmb e₀ d α k) {S T : Table} {g h : Equiv.Perm (Fin 16)}
    (hS : Rep 16 S g) (hT : Rep 16 T h) (hg : g ∈ NG α k) (hh : h ∈ NG α k) :
    tblEq 16 S T = true ↔ ψ E g = ψ E h :=
  (tblEq_iff_eq hS hT).trans ⟨fun h => by rw [h], ψ_inj E hg hh⟩

theorem memTab_iff_mem_img (E : NEmb e₀ d α k) {gens L : Array Table} (hL : EnumSpec 16 gens L)
    {T : Table} {g : Equiv.Perm (Fin 16)} (hT : Rep 16 T g) (hg : g ∈ NG α k) :
    memTab 16 L.toList T = true ↔ ψ E g ∈ img E (tsub gens) :=
  (hL.memTab_iff' hT).trans ⟨fun h => ψ_mem_img E hg h, fun h => mem_of_ψ_mem_img E hg h⟩

theorem ψ_eq_iff (E : NEmb e₀ d α k) {g h : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k)
    (hh : h ∈ NG α k) : ψ E g = ψ E h ↔ g = h :=
  ⟨ψ_inj E hg hh, fun h' => by rw [h']⟩

theorem ψ_eq_one_iff (E : NEmb e₀ d α k) {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) :
    ψ E g = 1 ↔ g = 1 := by
  have h := ψ_eq_iff E hg (NG α k).one_mem
  rwa [ψ_one] at h

theorem tblEq_idT_ψ (E : NEmb e₀ d α k) {S : Table} {g : Equiv.Perm (Fin 16)}
    (hS : Rep 16 S g) (hg : g ∈ NG α k) : tblEq 16 S (idT 16) = true ↔ ψ E g = 1 := by
  rw [ψ_eq_one_iff E hg, tblEq_iff_eq hS (Rep.idT (by norm_num))]

theorem commutator_mem_NG {g h : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) (hh : h ∈ NG α k) :
    ⁅g, h⁆ ∈ NG α k := by
  simp only [commutatorElement_def]
  exact (NG α k).mul_mem ((NG α k).mul_mem ((NG α k).mul_mem hg hh) ((NG α k).inv_mem hg))
    ((NG α k).inv_mem hh)

theorem commIn_ψ (E : NEmb e₀ d α k) {cT a b : Table} {c x y : Equiv.Perm (Fin 16)}
    (hc : Rep 16 cT c) (ha : Rep 16 a x) (hb : Rep 16 b y) (hcN : c ∈ NG α k) (hx : x ∈ NG α k)
    (hy : y ∈ NG α k) :
    commIn 16 cT a b = true ↔ ⁅ψ E x, ψ E y⁆ = 1 ∨ ⁅ψ E x, ψ E y⁆ = ψ E c := by
  rw [commIn_iff (by norm_num) hc ha hb, ← ψ_comm E hx hy]
  have hxy := commutator_mem_NG hx hy
  rw [ψ_eq_one_iff E hxy, ψ_eq_iff E hxy hcN]

theorem sqIn_ψ (E : NEmb e₀ d α k) {cT a : Table} {c x : Equiv.Perm (Fin 16)} (hc : Rep 16 cT c)
    (ha : Rep 16 a x) (hcN : c ∈ NG α k) (hx : x ∈ NG α k) :
    sqIn 16 cT a = true ↔ ψ E x * ψ E x = 1 ∨ ψ E x * ψ E x = ψ E c := by
  rw [sqIn_iff (by norm_num) hc ha, ← ψ_mul E hx hx]
  have hxx : x * x ∈ NG α k := (NG α k).mul_mem hx hx
  rw [ψ_eq_one_iff E hxx, ψ_eq_iff E hxx hcN]

theorem forall_mem_img_inf_centralizer (E : NEmb e₀ d α k) {gens L : Array Table}
    (hL : EnumSpec 16 gens L) {T : Table} {g : Equiv.Perm (Fin 16)} (hT : Rep 16 T g)
    (hg : g ∈ NG α k) {φ : G → Prop}
    (H : ∀ T' ∈ L.toList.filter (commTT 16 T), φ (ψ E (tablePerm 16 T'))) :
    ∀ y ∈ img E (tsub gens) ⊓ centralizer ({ψ E g} : Set G), φ y := by
  intro y hy
  rw [img_inf_centralizer E hg] at hy
  obtain ⟨g', hg', hK', rfl⟩ := (mem_img' E).1 hy
  obtain ⟨hK1, hK2⟩ := Subgroup.mem_inf.1 hK'
  obtain ⟨T', hT', hrep'⟩ := hL.exists_entry hK1
  have hcomm : commTT 16 T T' = true :=
    (commTT_iff hT hrep').2 (mem_centralizer_singleton_iff.1 hK2).symm
  have := H T' (List.mem_filter.2 ⟨Array.mem_toList_iff.2 hT', hcomm⟩)
  rwa [tablePerm_eq hrep'] at this

theorem mem_img_inf_centralizer_of_filter (E : NEmb e₀ d α k) {gens L : Array Table}
    (hL : EnumSpec 16 gens L) (hK : tsub gens ≤ NG α k) {T : Table} {g : Equiv.Perm (Fin 16)}
    (hT : Rep 16 T g) (hg : g ∈ NG α k) {T' : Table}
    (hT' : T' ∈ L.toList.filter (commTT 16 T)) :
    ψ E (tablePerm 16 T') ∈ img E (tsub gens) ⊓ centralizer ({ψ E g} : Set G) := by
  obtain ⟨hT1, hT2⟩ := List.mem_filter.1 hT'
  have hmem := Array.mem_toList_iff.1 hT1
  obtain ⟨hrep', hmem'⟩ := hL.rep_mem hmem
  refine Subgroup.mem_inf.2 ⟨ψ_mem_img_enum E hL hK hmem, mem_centralizer_singleton_iff.2 ?_⟩
  exact ((commTT_ψ E hT hrep' hg (hK hmem')).1 hT2).symm

end Word

end CFSG.EvenSporadicStandard.M12Std.Yosh
