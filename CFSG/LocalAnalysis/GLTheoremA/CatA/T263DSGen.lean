module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GVac
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem t263Desc_of_cover {Q Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (hcov : ∀ i, Q i → Q₁ i ∨ Q₂ i)
    (h₁ : T263Desc Q₁) (h₂ : T263Desc Q₂) : T263Desc Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ
  obtain ⟨i, hi, e⟩ := hQ
  rcases hcov i hi with h | h
  · exact h₁ p hp hp2 Ω hK S B hSn hSq hSp hSc ⟨i, h, e⟩
  · exact h₂ p hp hp2 Ω hK S B hSn hSq hSp hSc ⟨i, h, e⟩

theorem t263_inner_elt_pow {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥) {x : Ω} (hxp : x ^ p = 1)
    (hxC : x ∉ Subgroup.centralizer (S : Set Ω)) {s : PSimple p S}
    (hs : MI.indAut p S x (t263_normalizer_of_normal hSn) = MulAut.conj s) : s ^ p = 1 ∧ s ≠ 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hcomp : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  haveI : IsSimpleGroup (PSimple p S) := (pSimpleEquiv hSp).isSimpleGroup
  have hnab : ∃ a b : PSimple p S, a * b ≠ b * a := by
    have := CFSG.StandardType.exists_mul_ne_mul_centerQuot_of_perfect hSq.1 inferInstance
    obtain ⟨a, b, hab⟩ := this
    refine ⟨(pSimpleEquiv hSp).symm a, (pSimpleEquiv hSp).symm b, fun h => hab ?_⟩
    have := congrArg (pSimpleEquiv hSp) h
    simpa using this
  have hZ : Subgroup.center (PSimple p S) = ⊥ :=
    CFSG.StandardType.center_eq_bot_of_isSimpleGroup_of_nonabelian hnab
  have hind1 : MI.indAut p S x hxN ^ p = 1 := by
    show chevAut p S ⟨x⁻¹, hxN'⟩ ^ p = 1
    rw [← map_pow]
    have : (⟨x⁻¹, hxN'⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ p = 1 :=
      Subtype.ext (by simp [inv_pow, hxp])
    rw [this, map_one]
  refine ⟨?_, ?_⟩
  · rw [hs, ← map_pow] at hind1
    have hc : s ^ p ∈ Subgroup.center (PSimple p S) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (PSimple p S) => φ g) hind1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ p = s ^ p * g * (s ^ p)⁻¹ * s ^ p := by rw [this]
        _ = s ^ p * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  · intro h1
    have h2 : chevAut p S ⟨x⁻¹, hxN'⟩ = 1 := by
      have : MI.indAut p S x hxN = 1 := by rw [hs, h1, map_one]
      exact this
    have h3 := (chevAut_eq_one_iff hp hcomp hxN').1 h2
    exact hxC (by simpa using Subgroup.inv_mem _ ((centMod_iff_centralizer hSp hxN').1 h3))

theorem t263_false_of_inner_comm_invol {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x w : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hwS : w ∈ S) (hw2 : orderOf w = 2) (hwx : x * w = w * x)
    (hinn : ∃ s : PSimple p S, MI.indAut p S x (t263_normalizer_of_normal hSn) = MulAut.conj s)
    (hno : ∀ s t : PSimple p S, s ^ p = 1 → s ≠ 1 → orderOf t = 2 → t * s = s * t → False) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  obtain ⟨s, hs⟩ := hinn
  obtain ⟨hsp, hs1⟩ := t263_inner_elt_pow hp hSn hSq hSp hxp hxC hs
  let wS : ↥S := ⟨w, hwS⟩
  have hwS2 : orderOf wS = 2 := by
    rw [← hw2, ← Subgroup.orderOf_coe]
  let wb : PSimple p S := chevQuotHom p S wS
  have hwb1 : wb ≠ 1 := by
    intro h1
    have h2 : QuotientGroup.mk wS = (1 : ↥S ⧸ Subgroup.center ↥S) := by
      rw [← pSimpleEquiv_chevQuotHom hSp wS]
      exact (congrArg (pSimpleEquiv hSp) h1).trans (map_one _)
    exact t263_not_mem_center_of_orderOf_two hp hp2 hSp hwS2 ((QuotientGroup.eq_one_iff wS).1 h2)
  have hwb2 : orderOf wb = 2 := by
    refine orderOf_eq_prime ?_ hwb1
    have : wS ^ 2 = 1 := hwS2 ▸ pow_orderOf_eq_one wS
    show chevQuotHom p S wS ^ 2 = 1
    rw [← map_pow, this, map_one]
  have hfix : MI.indAut p S x hxN wb = wb := by
    have h3 := chevAut_chevQuotHom p S ⟨x⁻¹, hxN'⟩ wS
    have e : S.normalizerMonoidHom ⟨x⁻¹, hxN'⟩ wS = wS := by
      apply Subtype.ext
      show x⁻¹ * w * (x⁻¹)⁻¹ = w
      rw [inv_inv, mul_assoc, ← hwx, inv_mul_cancel_left]
    rw [e] at h3
    exact h3
  have hcomm : wb * s = s * wb := by
    have h1 : s * wb * s⁻¹ = wb := by
      have := hfix
      rw [hs, MulAut.conj_apply] at this
      exact this
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  exact hno s wb hsp hs1 hwb2 hcomm

theorem t263_exists_invol_of_comm {Ω : Type} [Group Ω] [Finite Ω] {B₀ T' : Subgroup Ω} {x : Ω}
    (hT'2 : IsPGroup 2 T') (hxcomm : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥) :
    ∃ w : Ω, w ∈ T' ∧ orderOf w = 2 ∧ x * w = w * x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : T' ⊓ Subgroup.centralizer ({x} : Set Ω) ≠ ⊥ := by
    intro h
    apply hxcomm
    rw [h]
    exact Subgroup.commutator_bot_right B₀
  have hU2 : IsPGroup 2 ↥(T' ⊓ Subgroup.centralizer ({x} : Set Ω)) := hT'2.to_le inf_le_left
  obtain ⟨w, hwU, hw2⟩ := exists_orderOf_two_of_isPGroup hU2 hne
  exact ⟨w, hwU.1, hw2, (Subgroup.mem_centralizer_singleton_iff.1 hwU.2).symm⟩

end CFSG.LocalAnalysis.GLTheoremA.T263

end
