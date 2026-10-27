module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseSec
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResPCore
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrDefs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)

section Cit3


variable {X : Type} [Group X] [Finite X] {r n : ℕ} {Φ : Set (Subgroup X)}

theorem setE_orbit (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n) (hB : TightBelowR r n)
    (h : TypeRFam r Φ) (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n)
    (hgen : omegaGen Φ = ⊤) {A B : Subgroup X} (hA : A ∈ Φ) (hAB : B ∈ omegaNbr Φ A)
    (hconj : ∃ g ∈ omegaGen Φ, conjSub g A = B) : SetE r (CoreAssembly.conjClass A) := by
  have hcl := h.hyp.conjInvariant
  have hsub : CoreAssembly.conjClass A ⊆ Φ := by
    rintro _ ⟨g, rfl⟩
    exact hcl g A hA
  have hinv : ConjInvariant (CoreAssembly.conjClass A) := by
    rintro g _ ⟨g', rfl⟩
    exact ⟨g * g', conjSub_mul g g' A⟩
  refine ⟨hr, h.subfam hsub hinv, hO, ?_⟩
  obtain ⟨zA, hzA⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hA
  obtain ⟨S', hd, hc⟩ := tightClsR_orbGrp (by omega) h4 h hO hn hA hzA
  obtain ⟨g, hg, hgA⟩ := hconj
  have hne := not_tightEdgeless_orbGrp h4 h hO hn hA hAB hg hgA
  have hlt : Nat.card ↥(Vtx.orbGrp Φ A) < n :=
    lt_of_le_of_lt (Subgroup.card_le_card_group _) hn
  have hin := inO2_of_edge_four_le hr hB hNo hlt hd hc hne
  have hN : ∀ g : X, conjSub g (Vtx.orbGrp Φ A) = Vtx.orbGrp Φ A := fun g =>
    Vtx.conjSub_orbGrp (by rw [hgen]; exact Subgroup.mem_top g)
  obtain ⟨Q, hQn, hQ2, hzQ⟩ :=
    exists_normal_two_of_normal (Vtx.orbGrp Φ A) hN (Vtx.le_orbGrp A hzA.mem) hin
  intro L hL u hu
  obtain ⟨g', rfl⟩ := hL
  refine ⟨Q, hQn, hQ2, ?_⟩
  rw [← (hzA.conj g').eq hu]
  exact hQn.conj_mem zA hzQ g'

theorem setE_of_transitive (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hB : TightBelowR r n) (h : TypeRFam r Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hn : Nat.card X < n) (hgen : omegaGen Φ = ⊤) {A B : Subgroup X} (hA : A ∈ Φ)
    (hAB : B ∈ omegaNbr Φ A) (htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g A = L) :
    SetE r Φ := by
  have hS := setE_orbit hr hNo h4 hB h hO hn hgen hA hAB (htr B hAB.1)
  have heq : CoreAssembly.conjClass A = Φ := by
    ext L
    constructor
    · rintro ⟨g, rfl⟩
      exact h.hyp.conjInvariant g A hA
    · intro hL
      obtain ⟨g, -, hg⟩ := htr L hL
      exact ⟨g, hg⟩
  rwa [heq] at hS

theorem tightSecLinkGenR_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hB : TightBelowR r n) : TightSecLinkGenR r n := by
  intro X _ _ hn Φ h hO hgen _ A hA B hAB hBA _ u v hu hv
  have hconjB : ∃ g ∈ omegaGen Φ, conjSub g A = B := by
    obtain ⟨g, hg⟩ := hBA
    exact ⟨g, by rw [hgen]; exact Subgroup.mem_top g, hg⟩
  have hS := setE_orbit hr hNo h4 hB h hO hn hgen hA hAB hconjB
  have hA₀ : A ∈ CoreAssembly.conjClass A := ⟨1, conjSub_one A⟩
  have hB₀ : B ∈ CoreAssembly.conjClass A := hBA
  set iA : ↥(CoreAssembly.conjClass A) := ⟨A, hA₀⟩ with hiA
  set iB : ↥(CoreAssembly.conjClass A) := ⟨B, hB₀⟩ with hiB
  have hu' : u = hS.zi iA := hS.inv_eq_zi hA₀ hu
  have hv' : v = hS.zi iB := hS.inv_eq_zi hB₀ hv
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun T hT => ?_
  by_cases hT0 : T ∈ CoreAssembly.conjClass A
  · set t : ↥(CoreAssembly.conjClass A) := ⟨T, hT0⟩ with ht
    by_cases h1 : NC A T
    · by_cases h2 : NC B T
      · have hn1 : nnv t iA = 1 := nnv_eq_one_iff.mpr h1.symm
        have hn2 : nnv t iB = 1 := nnv_eq_one_iff.mpr h2.symm
        have := hS.le_centralizer_sup iA iB t (hn1.trans hn2.symm)
        rw [← hu', ← hv'] at this
        exact this.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      · have := hS.le_centralizer_of_not_nc (i := iB) (j := t) h2
        rw [← hv'] at this
        exact this.trans (le_sup_right.trans le_sup_left)
    · have := hS.le_centralizer_of_not_nc (i := iA) (j := t) h1
      rw [← hu'] at this
      exact this.trans (le_sup_left.trans le_sup_left)
  · have hnc : ¬ ∃ g ∈ omegaGen Φ, conjSub g A = T := by
      rintro ⟨g, -, hg⟩
      exact hT0 ⟨g, hg⟩
    have hcomm := Vtx.commutes_of_not_conj h4 h hO hn hA hT hnc
    have : T ≤ Subgroup.centralizer ({u} : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm u hu.mem x hx).symm
    exact this.trans (le_sup_left.trans le_sup_left)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
