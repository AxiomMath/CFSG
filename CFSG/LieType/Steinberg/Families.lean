module

public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Steinberg.Classical.Symplectic
public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LieType.Steinberg.Classical.SpinOdd
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.Universal.Unitary.Extras

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

universe w

theorem sl_conclusionA (m : ℕ) (F : Type) [Field F] :
    ConclusionA.{0, w} (SpecialLinear.rootDatum m F) :=
  conclusionA_of (SpecialLinear.isCTGroupDatum m F) (SpecialLinear.steinbergExtras m F)

theorem sl_conclusionB (m : ℕ) (F : Type) [Field F] [Finite F] (hm : 2 ≤ m) :
    ConclusionB (SpecialLinear.rootDatum m F) F (SL.x m F) :=
  conclusionB_of rfl (SpecialLinear.isCTGroupDatum m F) (SpecialLinear.steinbergExtras m F)
    SL.isParametrization
    (fun O => ⟨SL.commC (m := m), fun α _ β _ p _ => by
      simp only [Set.mem_insert_iff]
      exact Or.inl (SL.commC_natAbs (m := m) α β p), SL.commutatorFormula O⟩)
    (fun O C hC => SL.chevalleyExtras hm O C hC)

theorem sp_conclusionA (n : ℕ) (F : Type) [Field F] :
    ConclusionA.{0, w} (Symplectic.rootDatum n F) :=
  conclusionA_of (Symplectic.isCTGroupDatum n F) (Symplectic.steinbergExtras n F)

theorem sp_conclusionB (n : ℕ) (F : Type) [Field F] [Finite F] (hn : 2 ≤ n) :
    ConclusionB (Symplectic.rootDatum n F) F (Sp.x n F) :=
  conclusionB_of rfl (Symplectic.isCTGroupDatum n F) (Symplectic.steinbergExtras n F)
    Sp.isParametrization
    (fun O => ⟨Sp.commC, Sp.commC_natAbs_mem, Sp.commutatorFormula O⟩)
    (fun O C hC => Sp.chevalleyExtras hn O C hC)

theorem su_conclusionA {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n) :
    ConclusionA.{0, w} (Unitary.rootDatum hF n) := by
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
  exact conclusionA_of (Unitary.isCTGroupDatum hF n hn ζ hζ)
    (Unitary.steinbergExtras hF n hn ζ hζ)

theorem spinPlus_conclusionA (n : ℕ) (K : Type) [Field K] (hn : 3 ≤ n) :
    ConclusionA.{0, w} (Spin.plusDatum n K hn) :=
  conclusionA_of (SpinPlus.isCTGroupDatum hn) (Spin.plusDatum_steinbergExtras hn)

theorem spinPlus_conclusionB (n : ℕ) (K : Type) [Field K] [Finite K] (hn : 3 ≤ n) :
    ConclusionB (Spin.plusDatum n K hn) K (SpinPlus.x n K hn) :=
  SpinPlus.conclusionB hn

theorem spinOdd_conclusionA (n : ℕ) (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    ConclusionA.{0, w} (Spin.oddDatum n K) :=
  conclusionA_of (Spin.oddDatum_isCTGroupDatum n K (Spin.oddDatum_iSup_eq_top n K h2 hn))
    (Spin.oddDatum_steinbergExtras h2)

theorem spinOdd_conclusionB (n : ℕ) (K : Type) [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (hn : 3 ≤ n) : ConclusionB (Spin.oddDatum n K) K (SpinOdd.x n K) :=
  SpinOdd.conclusionB h2 hn

theorem spinMinus_conclusionA (n : ℕ) {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) :
    ConclusionA.{0, w} (Spin.Twisted.minusDatum n hirr) :=
  Spin.Twisted.minusDatum_conclusionA n hirr hn

theorem e6_conclusionA (k : Type) [Field k] : ConclusionA.{0, w} (e6Datum k) :=
  conclusionA_of (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k)

theorem e6_conclusionB (k : Type) [Field k] [Finite k] :
    ConclusionB (e6Datum k) k (e6Data_valid.xm k) :=
  conclusionB_of rfl (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k)
    (e6Datum_isParametrization k _ (roots_eq isFiniteType_cartan_E6))
    (fun O => e6Datum_commutatorFormula k _ (roots_eq isFiniteType_cartan_E6) O)
    (fun O C hC => e6_chevalleyExtras k O C hC)

theorem e7_conclusionA (k : Type) [Field k] : ConclusionA.{0, w} (e7Datum k) :=
  conclusionA_of (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k)

theorem e7_conclusionB (k : Type) [Field k] [Finite k] :
    ConclusionB (e7Datum k) k (e7Data_valid.xm k) :=
  conclusionB_of rfl (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k)
    (e7Datum_isParametrization k _ (roots_eq isFiniteType_cartan_E7))
    (fun O => e7Datum_commutatorFormula k _ (roots_eq isFiniteType_cartan_E7) O)
    (fun O C hC => e7_chevalleyExtras k O C hC)

end CFSG.LieType.Steinberg
