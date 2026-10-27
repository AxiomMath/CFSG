module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentRot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.K159 CFSG.Open
  CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem exists_planeFrame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Odd n) {Bb : Subgroup ↥(orthDerived Q)}
    (hBb : IsElemAbelian p Bb) (hcard : Nat.card Bb = p ^ (n - 1)) :
    ∃ (U : Fin (n - 1) → Submodule F V) (e : Fin (n - 1) → ↥(orthDerived Q)),
      IsPlaneFrame Q p U e Bb := by
  have hreg : RegOn Q ⊤ := fun u _ h =>
    hQ.1 u fun w => by simpa [QuadraticMap.polarBilin_apply_apply] using h w Submodule.mem_top
  obtain ⟨r, U, hU⟩ := exists_planeDecomp hQ hp hp2 hpq hBb ⊤ hreg fun _ _ _ _ => Submodule.mem_top
  have hle : p ^ (n - 1) ≤ p ^ r := hcard ▸ hU.card_le_pow hBb hp
  have hn1 : n - 1 ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have hrn : r ≤ n := by
    have h1 := hU.toIsPlaneSystem.finrank_biSup Finset.univ
    have h2 := Submodule.finrank_le (⨆ j ∈ (Finset.univ : Finset (Fin r)), U j)
    rw [h1, Finset.card_univ, Fintype.card_fin, hdim] at h2
    omega
  have hrne : r ≠ n := by
    intro hrn'
    subst hrn'
    have h := hU.toIsPlaneSystem.isPlusType_iff_of_finrank hdim
    rcases Nat.even_or_odd r with he | ho
    · exact Nat.not_even_iff_odd.2 (htype.1 (h.2 he)) he
    · exact Nat.not_even_iff_odd.2 ho (h.1 (htype.2 ho))
  have hr : r = n - 1 := by omega
  subst hr
  obtain ⟨e, he⟩ := hU.exists_planeFrame hBb hp hcard
  exact ⟨U, e, he⟩

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
