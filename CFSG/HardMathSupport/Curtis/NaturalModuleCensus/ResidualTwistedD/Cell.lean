module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.Conj
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.FlagLinkM
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.Eichler
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.Orthogonal
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.ShortNode
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixBarFull

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.BorelTits Matrix

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem false_of_fixBarFull_pomegaMinus (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn4 : 4 ≤ n)
    (hcard : Nat.card F = 2)
    {J : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c)))}
    {v : StatedProj (StatedOmega (StatedQuadMinus n F b c))} (h : FixBarFull J 3 v) : False := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  obtain ⟨T, hT, hNJ, -⟩ := h.base.parab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T.index := by
    have h2 := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
  let T' : Sylow 2 (StatedProj (StatedOmega (StatedQuadMinus n F b c))) := hT.2.1.toSylow hidx
  have hNJ' : Subgroup.normalizer (T' : Set (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) ≤
      J := hNJ
  obtain ⟨g, π', hπ', hQ, hBJ⟩ := exists_conj_borelQuotient hirr hn4 T' J hNJ'
  have hvJ : v ∈ J := perfectJoin_le _ h.base.join
  by_cases hex : ∃ j : Fin (n - 1), 1 ≤ j.val ∧
      ¬ (rankOne (minusDatum n hirr).rootGroup j).map π' ≤ J
  · obtain ⟨j, hj1, hj⟩ := hex
    obtain ⟨W, hWQ, hWdim, hWstab⟩ := exists_stab_of_missing_node hirr hn4 π' g hπ' hQ hBJ hj
    exact false_of_stable_totSingular hirr hn4 hcard h.base.pow hvJ h.fix_all W hWQ
      (by omega) hWstab
  · push Not at hex
    obtain ⟨j0, hj0⟩ := exists_node_not_rankOne_le hQ hBJ h.base.ne_top
    have hj00 : j0.val = 0 := by
      by_contra hne
      exact hj0 (hex j0 (by omega))
    let s : Fin (n - 1) := ⟨n - 2, by omega⟩
    have hs : (rankOne (minusDatum n hirr).rootGroup s).map π' ≤ J := hex s (by simp [s]; omega)
    obtain ⟨A, hA, hAperf, x, hxA, hx3⟩ :=
      exists_perfect_order_three_of_shortNode hirr hcard hQ s (by simp only [s]; omega)
    have his : j0 ≠ s := fun he => by
      have := congrArg Fin.val he
      simp [s] at this
      omega
    have key : ∀ i j : Fin (n - 1), i ≠ j → i.val = 0 → j.val = n - 2 → cartanB (n - 1) i j = 0 := by
      intro i j hij hi hj
      unfold cartanB
      simp only [Matrix.of_apply]
      have h2 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
      simp only [hij, h2, ↓reduceIte]
    have hcart : (minusDatum n hirr).cartan j0 s = 0 := key j0 s his hj00 rfl
    exact hj0 (rankOne_le_of_orthogonal hQ h.base.cyc h.base.pow h.base.join h.fix_all hs hA
      hAperf hxA hx3 his hcart)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
