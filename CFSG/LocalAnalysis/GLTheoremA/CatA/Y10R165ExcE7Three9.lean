module

public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three7

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open scoped Matrix

section A5Cert


theorem e7T3CertA5_comps :
    e7T3CertA5.comps = [({ kind := 3, u := [6, 5, 1, 3], rot := false } : E7T3Comp)] := rfl

end A5Cert

section Kernel


theorem rootCharKernel_e7T3XTuple {p : ℕ} [NeZero p] {L : Type} [Field L] {ζ : Lˣ}
    (hp : p.Prime) (hp3 : 3 < p) (hζ : IsPrimitiveRoot ζ p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    rootCharKernel (fun i => ζ ^ (e7T3XColumn ε q i).val) =
      (fun γ => (coxeterSystem Tag.E7).wordProd e7T3CertA5.w • γ) ''
        parabolicRoots Tag.E7 (a5Nodes Tag.E7) := by
  rw [rootCharKernel_e7T3XColumn hp hp3 hζ hε hq,
    e7T3_rootSet_single (c := e7T3CertA5)
      (cm := ({ kind := 3, u := [6, 5, 1, 3], rot := false } : E7T3Comp))
      e7T3CertA5_comps (by decide)]
  rfl

end Kernel

section Tuple

theorem e7T3XTuple_pow_eq_one {p : ℕ} [NeZero p] {L : Type} [Field L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} (i : Fin Tag.E7.rank) :
    (fun i => ζ ^ (e7T3XColumn ε q i).val) i ^ p = 1 := by
  have h : (ζ ^ (e7T3XColumn ε q i).val) ^ (p : ℤ) =
      ζ ^ ((e7T3XColumn ε q i).val * (p : ℤ)) :=
    (_root_.zpow_mul ζ ((e7T3XColumn ε q i).val) (p : ℤ)).symm
  rw [← zpow_natCast, h]
  exact (hζ.zpow_eq_one_iff_dvd _).2 (dvd_mul_left (p : ℤ) _)

theorem e7T3XTuple_ne_one {p : ℕ} [NeZero p] {L : Type} [Field L] {ζ : Lˣ}
    (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} :
    (fun i => ζ ^ (e7T3XColumn ε q i).val) ≠ 1 := by
  intro h
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have h3 := congrFun h (⟨3, by decide⟩ : Fin Tag.E7.rank)
  simp only [Pi.one_apply] at h3
  have hA3 : e7T3AVec (⟨3, by decide⟩ : Fin Tag.E7.rank) = 1 := by
    decide +kernel
  have hD3 : e7T3DVec (⟨3, by decide⟩ : Fin Tag.E7.rank) = 0 := by
    decide +kernel
  have hcol : e7T3XColumn ε q (⟨3, by decide⟩ : Fin Tag.E7.rank) = 1 := by
    show (e7T3AVec (⟨3, by decide⟩ : Fin Tag.E7.rank) : ZMod p) +
      ((ε : ZMod p) * q) * (e7T3DVec (⟨3, by decide⟩ : Fin Tag.E7.rank) : ZMod p) = 1
    rw [hA3, hD3]
    norm_num
  rw [hcol, ZMod.val_one] at h3
  exact hζ.ne_one hp.one_lt (by simpa using h3)

theorem e7T3XTuple_orderOf {p : ℕ} [NeZero p] {L : Type} [Field L] {ζ : Lˣ}
    (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} :
    orderOf (fun i => ζ ^ (e7T3XColumn ε q i).val) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (funext fun i => e7T3XTuple_pow_eq_one hζ i)
    (e7T3XTuple_ne_one hp hζ)

end Tuple

section Cert


theorem e7T3XTuple_hcert {L : Type} [Field L] {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) :
    ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (((coxeterSystem Tag.E7).wordProd e7T3CertA5.w)⁻¹ *
          weylQuotientHom Tag.E7 L ⟨n, hnm⟩ *
          (coxeterSystem Tag.E7).wordProd e7T3CertA5.w) • α = u • (ε • α) := by
  obtain ⟨hg, hact⟩ := e7T3_comp_eps (L := L) hε hnW
    (cm := ({ kind := 3, u := [6, 5, 1, 3], rot := false } : E7T3Comp))
    (e7T3CertA5_good.1 _ (by rw [e7T3CertA5_comps]; exact List.mem_singleton_self _))
  refine ⟨(coxeterSystem Tag.E7).wordProd [6, 5, 1, 3], ?_, ?_⟩
  · simpa only [show e7T3J 3 = a5Nodes Tag.E7 from rfl] using hg
  · intro α hα
    have h := hact α (by simpa only [show e7T3J 3 = a5Nodes Tag.E7 from rfl] using hα)
    rw [h]
    simp only [e7T3Beta, permLattice_one]
    exact (weyl_smul_zsmul_pm _ hε α).symm

end Cert

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
