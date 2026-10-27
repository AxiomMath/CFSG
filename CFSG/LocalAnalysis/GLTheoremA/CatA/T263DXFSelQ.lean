module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXSelQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHardDefs
import all CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem exists_comp_of_twistedE6_q
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq4 : 4 ≤ 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (hβmem : β ∈ innAutDerived ↥(twistedE6RootGroup K σ))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) (P : Subgroup ↥(twistedE6RootGroup K σ))
    (hPβ : P ≤ fixSubgroup β) (hP2 : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) :
    ∃ J : Subgroup ↥(twistedE6RootGroup K σ), IsComponentOf J (fixSubgroup β) ∧ ⁅P, J⁆ ≠ ⊥ ∧
      P ≤ J ⊔ (fixSubgroup β ⊓ Subgroup.centralizer (J : Set ↥(twistedE6RootGroup K σ))) := by
  have hK2 : ringChar K = 2 := ringChar_eq_two_of_card_eq_pow (n := f * 2)
    (by rw [hK, ← pow_mul])
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  obtain ⟨h, rfl⟩ := mem_range_twistedE6InndiagConj_of_mem_innAutDerived Nat.prime_two hf hK σ hσ
    hβmem
  have hp1 : h ^ p = 1 := twistedE6InndiagConj_injective Nat.prime_two hf hK σ hσ
    (by rw [map_pow, hβp, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
  have hmon : MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two hf hK σ hσ hp hp2 hp hp2 (Or.inr hq4)
      hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  exact exists_comp_of_langSetup_q hK2 S (by rw [hSq]; exact hq4) hp hp2 hT hap h1 ι hinj hrange
    _ hconj P hPβ hP2 hP1

theorem modelSelQ_twistedE6
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq4 : 4 ≤ 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ModelSelQ p ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  intro r hrp hr1 P hPC hP2 hP1
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj r
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hβ1 : MulAut.conj r ≠ 1 := by
    intro h
    refine hr1 (Subgroup.mem_bot.1 ?_)
    rw [← hZ, Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rwa [mul_inv_eq_iff_eq_mul, eq_comm] at h1
  have hβp : (MulAut.conj r) ^ p = 1 := by rw [← map_pow, hrp, map_one]
  have hβmem : MulAut.conj r ∈ innAutDerived ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨r, rfl⟩
  have := exists_comp_of_twistedE6_q hf hK σ hσ hq4 hp hp2 (MulAut.conj r) hβmem hβp hβ1 P
    (hfix ▸ hPC) hP2 hP1
  rwa [hfix] at this

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
