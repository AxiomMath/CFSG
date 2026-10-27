module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.StraightenTw
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Main
public import CFSG.RankThree.PartOne.KE6.Tw6D4Weyl
public import CFSG.RankThree.PartOne.KE6.Phi3D4Weyl
public import CFSG.RankThree.PartOne.KE6.Phi3Frame
public import CFSG.RankThree.PartOne.KE6.Phi3Torsion
public import CFSG.RankThree.PartOne.KE6.Phi3Transport

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.E6 (e6Word wordProd_e6Word_smul)


section Theta

variable {L : Type} [Field L] [IsAlgClosed L]

@[expose] def twTheta (L : Type) [Field L] : ModGL Tag.E6 L :=
  canonicalRep (coxeterSystem Tag.E6) L twNeg * tw6P L

theorem canonicalRep_mem_mono (w : WeylGroup Tag.E6) :
    canonicalRep (coxeterSystem Tag.E6) L w ∈ monomialSubgroup Tag.E6 L :=
  Subgroup.mem_sup_right (canonicalRep_mem_closure (coxeterSystem Tag.E6) L w)

@[expose] def d4MaxWordE6 : List (Fin Tag.E6.rank) := [4, 3, 2, 1, 3, 4, 3, 2, 1, 3, 2, 1]

theorem twNeg_tw6Wt_check : ∀ i j : Fin Tag.E6.rank,
    (-(permLattice twE6Rho ((e6Word tw6WtWord).foldr (reflect Tag.E6) (Pi.single i 1))) :
        Fin Tag.E6.rank → ℤ) j =
      (d4MaxWordE6.foldr (reflect Tag.E6) (Pi.single i 1) : Fin Tag.E6.rank → ℤ) j := by
  decide +kernel

theorem twNeg_mul_tw6Wt_eq : twNeg * tw6Wt = (coxeterSystem Tag.E6).wordProd d4MaxWordE6 := by
  refine ext_single fun i => ?_
  have h1 : (coxeterSystem Tag.E6).wordProd d4MaxWordE6 •
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      d4MaxWordE6.foldr (reflect Tag.E6) (Pi.single i 1) := wordProd_smul _ _
  have h2 : tw6Wt • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      (e6Word tw6WtWord).foldr (reflect Tag.E6) (Pi.single i 1) := wordProd_e6Word_smul _ _
  rw [mul_smul, h1, h2, twNeg_smul]
  funext j
  exact twNeg_tw6Wt_check i j

theorem twNeg_mul_tw6Wt_mem : twNeg * tw6Wt ∈ kernelWeylGroup (triChar stdChar) := by
  rw [twNeg_mul_tw6Wt_eq, CoxeterSystem.wordProd]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    simp only [d4MaxWordE6, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  refine Subgroup.subset_closure ⟨1, i, ?_, by rw [one_mul, inv_one, mul_one]⟩
  rw [one_smul, mem_kernelRoots_stdChar, mem_parabolicRoots_d4Support_iff']
  refine ⟨isRoot_single Tag.E6 i, ?_, ?_⟩
  · rcases hi' with rfl | rfl | rfl | rfl <;> decide
  · rcases hi' with rfl | rfl | rfl | rfl <;> decide

theorem twTheta_conj_on_Q :
    ∃ h ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support,
      ∀ y ∈ subsystemGroup Tag.E6 L d4Support,
        twTheta L * y * (twTheta L)⁻¹ = h * y * h⁻¹ := by
  obtain ⟨m₀, hm₀M, hm₀W, hm₀P⟩ := exists_monomial_eq_diagramMap_on_d4 (Ω := L)
  set n₀ := canonicalRep (coxeterSystem Tag.E6) L twNeg with hn₀
  set g := n₀ * m₀ with hg
  have hgmono : g ∈ monomialSubgroup Tag.E6 L := mul_mem (canonicalRep_mem_mono _) hm₀M
  have hgmaps : MapsRootLines g (twNeg * tw6Wt) := by
    have := (mapsRootLines_canonicalRep (R := L) twNeg).mul
      (mapsRootLines_weylQuotientHom ⟨m₀, hm₀M⟩)
    rwa [hm₀W] at this
  have hnu := canonicalRep_mem_sup_of_mem_kernelWeylGroup (L := L) twNeg_mul_tw6Wt_mem
  have hq : g * (canonicalRep (coxeterSystem Tag.E6) L (twNeg * tw6Wt))⁻¹ ∈
      torusGroup Tag.E6 L := by
    refine E8Lift.mem_torusGroup_of_mapsRootLines_one
      (mul_mem hgmono (inv_mem (canonicalRep_mem_mono _))) ?_
    have := hgmaps.mul (mapsRootLines_canonicalRep (R := L) (twNeg * tw6Wt)).inv
    rwa [mul_inv_cancel] at this
  have hgmem : g ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support := by
    have e : g = (g * (canonicalRep (coxeterSystem Tag.E6) L (twNeg * tw6Wt))⁻¹) *
        canonicalRep (coxeterSystem Tag.E6) L (twNeg * tw6Wt) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hq) hnu
  refine ⟨g, hgmem, fun y hy => ?_⟩
  have h1 := hm₀P y hy
  simp only [twTheta]
  calc n₀ * tw6P L * y * (n₀ * tw6P L)⁻¹ = n₀ * (tw6P L * y * (tw6P L)⁻¹) * n₀⁻¹ := by group
    _ = n₀ * (m₀ * y * m₀⁻¹) * n₀⁻¹ := by rw [h1]
    _ = g * y * g⁻¹ := by rw [hg]; group

theorem twNeg_twistHomE6_mul_mem_torus (Fr : L →+* L) (s : WeylGroup Tag.E6) :
    canonicalRep (coxeterSystem Tag.E6) L twNeg *
      twistHomE6 Fr (canonicalRep (coxeterSystem Tag.E6) L s) *
        (canonicalRep (coxeterSystem Tag.E6) L twNeg)⁻¹ *
          (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ ∈ torusGroup Tag.E6 L := by
  rw [twistHomE6_canonicalRep]
  have hmono : canonicalRep (coxeterSystem Tag.E6) L twNeg *
      canonicalRep (coxeterSystem Tag.E6) L (twDelta s) *
        (canonicalRep (coxeterSystem Tag.E6) L twNeg)⁻¹ *
          (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (mul_mem (canonicalRep_mem_mono _) (canonicalRep_mem_mono _))
      (inv_mem (canonicalRep_mem_mono _))) (inv_mem (canonicalRep_mem_mono _))
  refine E8Lift.mem_torusGroup_of_mapsRootLines_one hmono ?_
  have h := (((mapsRootLines_canonicalRep (R := L) twNeg).mul
    (mapsRootLines_canonicalRep (R := L) (twDelta s))).mul
      (mapsRootLines_canonicalRep (R := L) twNeg).inv).mul
        (mapsRootLines_canonicalRep (R := L) s).inv
  have e : twNeg * twDelta s * twNeg⁻¹ * s⁻¹ = 1 := by
    rw [twDelta_eq_conj, twNeg_inv]
    calc twNeg * (twNeg * s * twNeg) * twNeg * s⁻¹ =
        (twNeg * twNeg) * s * (twNeg * twNeg) * s⁻¹ := by group
      _ = 1 := by rw [twNeg_mul_self]; group
  rwa [e] at h

theorem mem_heisM_of_conj_mem {a : Fin Tag.E6.rank → Lˣ} {s : WeylGroup Tag.E6}
    (hs : ∀ α, IsRoot Tag.E6 α → (rootChar a α = 1 ↔ s • α ∈ parabolicRoots Tag.E6 d4Support))
    {x : ModGL Tag.E6 L}
    (hx : canonicalRep (coxeterSystem Tag.E6) L s * x *
      (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ ∈
        torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support) : x ∈ heisM a := by
  have hconj := map_conj_heisM (L := L) hs
  have hxT : canonicalRep (coxeterSystem Tag.E6) L s * x *
      (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ ∈
        (heisM a).map (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L s)).toMonoidHom := by
    rw [hconj]
    exact hx
  obtain ⟨g', hg', hg'x⟩ := hxT
  have : g' = x := by
    have h1 : canonicalRep (coxeterSystem Tag.E6) L s * g' *
        (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ =
        canonicalRep (coxeterSystem Tag.E6) L s * x *
          (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ := hg'x
    calc g' = (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ *
          (canonicalRep (coxeterSystem Tag.E6) L s * g' *
            (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹) *
          canonicalRep (coxeterSystem Tag.E6) L s := by group
      _ = x := by rw [h1]; group
  rw [← this]
  exact hg'

theorem twC0_mem_heisM {a : Fin Tag.E6.rank → Lˣ} {s : WeylGroup Tag.E6}
    (hs : ∀ α, IsRoot Tag.E6 α → (rootChar a α = 1 ↔ s • α ∈ parabolicRoots Tag.E6 d4Support))
    {h : ModGL Tag.E6 L} (hh : h ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support)
    (Fr : L →+* L) :
    (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ * h⁻¹ *
      canonicalRep (coxeterSystem Tag.E6) L twNeg *
      twistHomE6 Fr (canonicalRep (coxeterSystem Tag.E6) L s) *
      (canonicalRep (coxeterSystem Tag.E6) L twNeg)⁻¹ ∈ heisM a := by
  refine mem_heisM_of_conj_mem hs ?_
  have e : canonicalRep (coxeterSystem Tag.E6) L s *
      ((canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ * h⁻¹ *
        canonicalRep (coxeterSystem Tag.E6) L twNeg *
        twistHomE6 Fr (canonicalRep (coxeterSystem Tag.E6) L s) *
        (canonicalRep (coxeterSystem Tag.E6) L twNeg)⁻¹) *
      (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ =
      h⁻¹ * (canonicalRep (coxeterSystem Tag.E6) L twNeg *
        twistHomE6 Fr (canonicalRep (coxeterSystem Tag.E6) L s) *
        (canonicalRep (coxeterSystem Tag.E6) L twNeg)⁻¹ *
        (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem hh) (Subgroup.mem_sup_left (twNeg_twistHomE6_mul_mem_torus Fr s))

end Theta

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4
