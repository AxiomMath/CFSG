module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthTorus
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentDecomp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I164

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.K159 CFSG.Open CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem i167COrth_witt_triv_aux1 {g : V ≃ₗ[F] V} {P : Submodule F V} (hP : RegOn Q P)
    (hgP : ∀ y ∈ P, g y ∈ P) (hgP' : ∀ y ∈ polarPerp Q P, g y ∈ polarPerp Q P)
    (hfix : ∀ y ∈ P, g y = y → y = 0) : fixedSpace g ≤ polarPerp Q P := by
  intro w hw
  have hc := isCompl_polarPerp (nondegenerate_of_regOn hP)
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := w))
  rw [mem_fixedSpace, map_add] at hw
  have h1 : g u - u ∈ P := Submodule.sub_mem _ (hgP u hu) hu
  have h2 : g u - u ∈ polarPerp Q P := by
    have : g u - u = z - g z := by
      rw [← sub_eq_zero, show g u - u - (z - g z) = g u + g z - (u + z) by abel]
      exact sub_eq_zero.2 hw
    rw [this]
    exact Submodule.sub_mem _ hz (hgP' z hz)
  have h3 : g u - u = 0 := by
    have := (disjoint_iff.1 hc.disjoint) ▸ (show g u - u ∈ P ⊓ polarPerp Q P from ⟨h1, h2⟩)
    exact (Submodule.mem_bot F).1 this
  have hu0 : u = 0 := hfix u hu (sub_eq_zero.1 h3)
  rw [hu0, zero_add]
  exact hz

theorem i167COrth_witt_triv (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {m : ℕ} (hdim : Module.finrank F V = 2 * m) (hm : 4 ≤ m)
    {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian p A)
    (hmax : ∀ E : Subgroup ↥(orthDerived Q), IsElemAbelian p E → A ≤ E → E = A)
    {g : ↥(orthDerived Q)} (hgA : g ∈ A) (hg : orderOf g = p)
    (hCA : ∀ a ∈ A, (∀ w ∈ fixedSpace (g : V ≃ₗ[F] V), (a : V ≃ₗ[F] V) w = w) →
      a ∈ Subgroup.zpowers g) :
    Module.finrank F V = Module.finrank F (fixedSpace (g : V ≃ₗ[F] V)) + 2 ∧
      (IsPlusType Q ↔ ¬ IsPlusType (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype)) := by
  classical
  have hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ u ∈ T, Q u = 0 := by
    by_cases hplus : IsPlusType Q
    · exact exists_threeSingular hQ hdim (Or.inl ⟨hplus, by omega⟩)
    · exact exists_threeSingular hQ hdim (Or.inr ⟨hplus, hm⟩)
  obtain ⟨P, hP2, hPreg, hPm, hPinv, hPfix⟩ := i167COrth_adapted_plane hQ hp hp2 hpq hA hgA hg
  obtain ⟨h, hhp, hhP, hhperp, hhcomm⟩ :=
    i167COrth_partial_rotation hQ hp hp2 hT hA hgA hPreg hPinv
  have hWperp : fixedSpace (g : V ≃ₗ[F] V) ≤ polarPerp Q P :=
    i167COrth_witt_triv_aux1 hPreg (hPinv g hgA)
      (fun y hy => apply_mem_polarPerp hPinv hgA hy) hPfix
  have hhA : h ∈ A := by
    have hE := rk2_isElemAbelian_sup_zpowers hA hhp (fun a ha => (hhcomm a ha).symm)
    rw [← hmax _ hE le_sup_left]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers h)
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    simp at hP2
  have hhg : h = g :=
    i167COrth_eq_of_mem_zpowers hp hg hP0 (hPinv g hgA) hPfix
      (hCA h hhA (fun w hw => hhperp w (hWperp hw))) hhP
  have hW : fixedSpace (g : V ≃ₗ[F] V) = polarPerp Q P :=
    le_antisymm hWperp fun w hw => by
      rw [mem_fixedSpace, ← hhg]
      exact hhperp w hw
  have hfin : Module.finrank F (polarPerp Q P) = Module.finrank F V - Module.finrank F P :=
    finrank_polarPerp hQ P
  have hle : Module.finrank F P ≤ Module.finrank F V := Submodule.finrank_le P
  refine ⟨?_, ?_⟩
  · rw [hW, hfin]
    omega
  · rw [hW, isPlusType_comp_polarPerp_iff hQ hdim (by omega) (nondegenerate_of_regOn hPreg) hP2 hPm]
    exact not_not.symm

end CFSG.LocalAnalysis.GLTheoremA.I167

end
