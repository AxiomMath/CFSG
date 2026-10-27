module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcNum
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcFpf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply zpowMatrix_zpowMatrix zpowMatrix_one)
open scoped commutatorElement Matrix

variable {τ : Tag}

theorem weylTuple_of_weylMat {z : WeylGroup τ} {s : ℤ}
    (hz : weylMat z = s • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) (hs : s = 1 ∨ s = -1)
    {L : Type} [Field L] (β : Fin τ.rank → Lˣ) : weylTuple z β = fun i => β i ^ s := by
  have h1 : weylMat z⁻¹ * weylMat z = 1 := by
    rw [← weylMat_mul, inv_mul_cancel, weylMat_one]
  have h2 : weylMat z⁻¹ = s • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) := by
    rw [hz] at h1
    rcases hs with rfl | rfl
    · simpa using h1
    · have h3 : -weylMat z⁻¹ = 1 := by simpa using h1
      calc weylMat z⁻¹ = -(-weylMat z⁻¹) := (neg_neg _).symm
        _ = (-1 : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) := by rw [h3]; simp
  rw [weylTuple_eq_zpowMatrix, h2]
  funext i
  rw [zpowMatrix_apply]
  simp [Matrix.smul_apply, Matrix.one_apply]

theorem torusFpf_dc {w u z : WeylGroup τ} {s : ℤ} {k p q e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ q) (he : orderOf ((q : ℕ) : ZMod p) = e)
    (hz : weylMat z = s • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) (hs1 : s = 1 ∨ s = -1)
    (hu : u = z * w ^ k) (hs : (s = 1 ∧ ¬ e ∣ k) ∨ (s = -1 ∧ e ∣ k)) : TorusFpf τ q p w u := by
  obtain ⟨q', hqq', harith⟩ := exists_inv_arith hp hp2 hpq he s k hs
  intro L _ _ Fr hFr β hβ hβp hfix
  exact fpf_scalar hFr hp hqq' (weylTuple_of_weylMat hz hs1) hu harith hβ hβp hfix

theorem SylowFrame.wcOn_dcw {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    {w a b c d : List (Fin τ.rank)} {z : WeylGroup τ} {s : ℤ} {k e : ℕ}
    (hF : SylowFrame τ F p (wp τ w)) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = e)
    (hz : weylMat z = s • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) (hs1 : s = 1 ∨ s = -1)
    (ha : wordMat τ a * wordMat τ w = wordMat τ w * wordMat τ a)
    (hb : wordMat τ b * wordMat τ w = wordMat τ w * wordMat τ b)
    (hc : wordMat τ c * wordMat τ w = wordMat τ w * wordMat τ c)
    (hd : wordMat τ d * wordMat τ w = wordMat τ w * wordMat τ d)
    (hdc : wordMat τ (cw (cw a b) (cw c d)) = s • wordMat τ w ^ k)
    (hs : (s = 1 ∧ ¬ e ∣ k) ∨ (s = -1 ∧ e ∣ k)) : WCOn p (adjointGroup τ F) :=
  hF.wcOn_dc (wp_mem_centralizer ha) (wp_mem_centralizer hb) (wp_mem_centralizer hc)
    (wp_mem_centralizer hd)
    (torusFpf_dc Fact.out hp2 hpq he hz hs1 (wp_dcw_eq hz hdc) hs)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
