module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
open scoped commutatorElement

variable {τ : Tag} {L : Type} [Field L]

theorem NFix_conj_rootDiagUnit [IsAlgClosed L] {n : ModGL τ L} {Fr : L →+* L} (y : NFix n Fr)
    (b : Fin τ.rank → Lˣ) :
    (y : ModGL τ L) * rootDiagUnit τ b * (y : ModGL τ L)⁻¹ =
      rootDiagUnit τ (weylTuple (NFixToWeyl n Fr y) b) := by
  obtain ⟨w, k, hk, hyk⟩ :=
    monomialSubgroup_le_torusWeylCosets (NFix_le_monomialSubgroup n Fr y.2)
  have hmaps : MapsRootLines (y : ModGL τ L) w := by
    rw [hyk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  rw [NFixToWeyl_eq hmaps, hyk]
  have hconj := canonicalRep_conj_rootDiagUnit (K := L) w b
  calc k * canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
          (k * canonicalRep (coxeterSystem τ) L w)⁻¹
        = k * (canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
            (canonicalRep (coxeterSystem τ) L w)⁻¹) * k⁻¹ := by group
    _ = k * rootDiagUnit τ (weylTuple w b) * k⁻¹ := by rw [hconj]
    _ = rootDiagUnit τ (weylTuple w b) := by
        rw [torusGroup_mul_comm hk (rootDiagUnit_mem_torusGroup _), mul_assoc, mul_inv_cancel,
          mul_one]

theorem entrywise_eq_pow_of_mem_torusGroup [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {x : ModGL τ L} (hx : x ∈ torusGroup τ L) :
    Units.map (entrywiseHom Fr) x = x ^ q := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [show Units.map (entrywiseHom Fr) (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map Fr.toMonoidHom (a i) from
    Units.ext (entrywise_rootDiag Fr a)]
  change rootDiagUnitHom τ L _ = (rootDiagUnitHom τ L a) ^ q
  rw [← map_pow]
  congr 1
  funext i
  exact Units.ext (by simp [hFr])

theorem canonicalRep_conj_eq_pow_of_mem_twistedTorus [IsAlgClosed L] {w : WeylGroup τ}
    {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {x : ModGL τ L}
    (hx : x ∈ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)))
    {p q' : ℕ} (hxp : x ^ p = 1) (hqq' : q * q' ≡ 1 [MOD p]) :
    canonicalRep (coxeterSystem τ) L w * x * (canonicalRep (coxeterSystem τ) L w)⁻¹ = x ^ q' := by
  set n := canonicalRep (coxeterSystem τ) L w
  set z := n * x * n⁻¹ with hz
  have hfix : n * Units.map (entrywiseHom Fr) x * n⁻¹ = x := hx.2
  rw [entrywise_eq_pow_of_mem_torusGroup hFr hx.1] at hfix
  have hzq : z ^ q = x := by rw [hz, conj_pow, hfix]
  have hzp : z ^ p = 1 := by rw [hz, conj_pow, hxp, mul_one, mul_inv_cancel]
  have hmod : q * q' ≡ 1 [MOD orderOf z] := Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hzp) hqq'
  calc z = z ^ (q * q') := by rw [pow_eq_pow_iff_modEq.2 hmod, pow_one]
    _ = x ^ q' := by rw [pow_mul, hzq]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
