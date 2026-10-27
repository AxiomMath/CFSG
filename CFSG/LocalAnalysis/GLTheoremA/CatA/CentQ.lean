module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs117
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator

section Main


theorem centCompQuasi_of_lie {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqd : q ≠ d.1.characteristic) {x : S} (hx : x ^ q = 1) (hx1 : x ≠ 1) (r : ℕ) :
    CentCompQuasi S x r := by
  have hβ : (MulAut.conj x : MulAut S) ^ q = 1 := by rw [← map_pow, hx, map_one]
  have hβ1 : (MulAut.conj x : MulAut S) ≠ 1 := by
    intro h
    apply hx1
    have hz : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h g
      rw [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [b3Lie_center_eq_bot hnc, Subgroup.mem_bot] at hz
    exact hz
  exact centCompQuasi_of_perfectInLayer
    (LieSemisimple.lieSemisimpleCent S hS hnc d ⟨e⟩ q hq hq2 hqd _ hβ hβ1)

theorem centQuasiAt_holds (G : Type) [Group G] [Finite G] : CentQuasiAt G := by
  intro K y r hr hr2 hchev hK hy hord Y hY
  obtain ⟨q, hq, hq2, hqy⟩ := hord
  refine centQuasi_lift hy hr ?_ Y hY
  have hS : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2
  have hnc : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hK
  set x : ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk (⟨y, hy⟩ : ↥K) with hxdef
  have hyq : y ^ q = 1 := by rw [← hqy]; exact pow_orderOf_eq_one y
  have hxq : x ^ q = 1 := by
    rw [hxdef, ← QuotientGroup.mk_pow]
    have : (⟨y, hy⟩ : ↥K) ^ q = 1 := Subtype.ext (by simpa using hyq)
    rw [this]; rfl
  by_cases hx1 : x = 1
  · rw [hx1]
    exact centCompQuasi_one hnc r
  rcases centQIndexCases_of_marking hchev with ⟨d, hd, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | hcard |
    ⟨⟨d, hd, ⟨e⟩⟩, hcard⟩
  · exact centCompQuasi_of_lie hS hnc d e hq hq2 (by rw [hd]; exact hq2) hxq hx1 r
  · exact centCompQuasi_of_mulEquiv e hr (centCompQuasi_alt 5 (Or.inl rfl) hq hq2
      (by rw [← map_pow, hxq, map_one]) (fun h => hx1 (e.map_eq_one_iff.1 h)) r hr)
  · exact centCompQuasi_of_mulEquiv e hr (centCompQuasi_alt 6 (Or.inr (Or.inl rfl)) hq hq2
      (by rw [← map_pow, hxq, map_one]) (fun h => hx1 (e.map_eq_one_iff.1 h)) r hr)
  · exact centCompQuasi_of_mulEquiv e hr (centCompQuasi_alt 8 (Or.inr (Or.inr rfl)) hq hq2
      (by rw [← map_pow, hxq, map_one]) (fun h => hx1 (e.map_eq_one_iff.1 h)) r hr)
  · exact centCompQuasi_card168 hnc hcard hx1 r
  · by_cases hq3 : q = 3
    · subst hq3
      haveI := hS
      exact centCompQuasi_u33 hnc d hd e hcard hxq hx1 hr hr2
    · exact centCompQuasi_of_lie hS hnc d e hq hq2 (by rw [hd]; exact hq3) hxq hx1 r

end Main

end CFSG.LocalAnalysis.GLTheoremA
