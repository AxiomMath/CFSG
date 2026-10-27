module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyGen
public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne

set_option linter.unusedSectionVars false

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem iform_eq_sum_single (x v : Fin τ.rank → ℤ) :
    iform x v = ∑ l, v l * iform x (Pi.single l 1) := by
  have hv : v = ∑ l, v l • (Pi.single l 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  have : ∀ s : Finset (Fin τ.rank), iform x (∑ l ∈ s, v l • (Pi.single l 1 : Fin τ.rank → ℤ)) =
      ∑ l ∈ s, v l * iform x (Pi.single l 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [iform]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_right, iform_smul_right, ih]
  exact this _

@[expose] def Hchar (x : Fin τ.rank → ℤ) (u : Lˣ) : Fin τ.rank → Lˣ :=
  fun l => u ^ iform x (Pi.single l 1)

@[expose] noncomputable def Hel (x : Fin τ.rank → ℤ) (u : Lˣ) : ModGL τ L :=
  rootDiagUnit τ (Hchar x u)

theorem rootChar_Hchar (x v : Fin τ.rank → ℤ) (u : Lˣ) :
    rootChar (Hchar x u) v = u ^ iform x v := by
  rw [iform_eq_sum_single x v]
  simp only [rootChar, Hchar, ← zpow_mul]
  rw [← prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun l _ => by rw [mul_comm]

theorem Hchar_add (x y : Fin τ.rank → ℤ) (u : Lˣ) :
    Hchar (τ := τ) x u * Hchar y u = Hchar (x + y) u := by
  funext l
  simp only [Hchar, Pi.mul_apply, iform_add_left, zpow_add]

theorem Hchar_mul (x : Fin τ.rank → ℤ) (u v : Lˣ) :
    Hchar (τ := τ) x u * Hchar x v = Hchar x (u * v) := by
  funext l
  simp only [Hchar, Pi.mul_apply, mul_zpow]

theorem Hchar_pow (x : Fin τ.rank → ℤ) (u : Lˣ) (c : ℤ) :
    Hchar (τ := τ) x u ^ c = Hchar x (u ^ c) := by
  funext l
  simp only [Hchar, Pi.pow_apply]
  rw [← zpow_mul, ← zpow_mul, mul_comm]

theorem Hel_add (x y : Fin τ.rank → ℤ) (u : Lˣ) :
    Hel (L := L) (τ := τ) (x + y) u = Hel x u * Hel y u := by
  unfold Hel
  rw [← Hchar_add, rootDiagUnit_mul]

theorem Hel_zero (u : Lˣ) : Hel (L := L) (τ := τ) 0 u = 1 := by
  unfold Hel
  have : Hchar (τ := τ) 0 u = 1 := by funext l; simp [Hchar, iform]
  rw [this, rootDiagUnit_one]

theorem Hel_root_eq_rootSL2 (hτ : SimplyLacedTag τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (u : Lˣ) : Hel (L := L) β u = rootSL2 τ L β (HSL u) := by
  symm
  refine rootSL2_HSL_eq_rootDiagUnit hβ (fun i => iform β (Pi.single i 1)) ?_ u
  intro δ hδ
  rw [iform_self_eq_two hτ hβ, Int.mul_ediv_cancel_left _ (by norm_num)]
  exact iform_eq_sum_single β δ

theorem Hel_root_mem_rootSpan (hτ : SimplyLacedTag τ) [IsAlgClosed L] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (u : Lˣ) : Hel (L := L) β u ∈ rootSpan τ L {β, -β} := by
  rw [Hel_root_eq_rootSL2 hτ hβ]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair hβ _

end Torus

end CFSG.HardMathSupport.Timmesfeld.LangTorus
