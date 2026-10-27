module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClQuad
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClBlk
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClEl
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.RankThree.PartOne.S11d.OrthCaseH

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks (fixedByEnd mem_fixedByEnd)

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [FiniteDimensional F V] in
private theorem finrank_fixedByEnd_ne_eight (hF : Nat.card F = 2) (hV : finrank F V = 10)
    {e y : V ≃ₗ[F] V} (hy : y ^ 11 = 1) (hy1 : y ≠ 1) (hey : e * y = y * e) :
    finrank F ↥(fixedByEnd e) ≠ 8 := by
  by_cases he : e = 1
  · have htop : fixedByEnd e = ⊤ := eq_top_iff.2 fun v _ => mem_fixedByEnd.2 (by rw [he]; rfl)
    rw [htop, finrank_top, hV]
    norm_num
  · rw [fixedByEnd_eq_bot_of_commute_eleven hF hV he hy hy1 hey, finrank_bot]
    norm_num

private theorem specialBlock_le_orthDerived_ten (hF : Nat.card F = 2) (hV : finrank F V = 10)
    (hQ : (polarBilin Q).Nondegenerate) {a : V ≃ₗ[F] V} (haQ : ∀ v, Q (a v) = Q v)
    (ha3 : a ^ 3 = 1) (hfix : finrank F ↥(fixedSpace a) = 2) :
    specialBlock Q a (cyc3 F) ≤ orthDerived Q := by
  haveI := charP_two hF
  haveI : Fact (Irreducible (cyc3 F)) := ⟨irreducible_cyc3 hF⟩
  have hx : OddOrderIsometry Q 3 a := ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 haQ, ha3,
    cast_three_ne_zero_of_card_two hF, fun v hv => hQ.1 v hv⟩
  have hc := Submodule.finrank_add_eq_of_isCompl (isCompl_fixedSpace_cyc3 hF hx)
  have hm := finrank_cyc3 (x := a) hF
  have hh := cyc3_mem_primaryFactors (x := a) hF (by omega)
  exact specialBlock_le_orthDerived hF hx hQ
    (exists_threeSingular_of_dim Q hQ (m := 5) (by norm_num) (by rw [hV])) hh

theorem exists_layer_pair_orthDerived (hF : Nat.card F = 2) (hV : finrank F V = 10)
    (hQ : (polarBilin Q).Nondegenerate)
    {A T : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian 3 A) (h81 : 81 ≤ Nat.card A)
    {d y : ↥(orthDerived Q)} (hdA : d ∈ A) (hd : d ≠ 1) (hy : y ^ 11 = 1) (hy1 : y ≠ 1)
    (hdy : d * y = y * d) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hAT : A ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q))) :
    ∃ e ∈ A, e * y ≠ y * e ∧
      GLAPLayer 3 (Subgroup.centralizer ({d} : Set ↥(orthDerived Q)) ⊓
        Subgroup.centralizer ({e} : Set ↥(orthDerived Q))) ≠ ⊥ := by
  classical
  haveI := charP_two hF
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun g : V ≃ₗ[F] V => (g : V → V))
    fun g g' h => LinearEquiv.ext (congrFun h)
  let ι : ↥(orthDerived Q) →* (V ≃ₗ[F] V) := (orthDerived Q).subtype
  have hι : Function.Injective ι := (orthDerived Q).subtype_injective
  have hιQ : ∀ g : ↥(orthDerived Q), ∀ v, Q ((g : V ≃ₗ[F] V) v) = Q v := fun g =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (orthDerived_le_orthogonalGroup g.2)
  have halt : (polarBilin Q).IsAlt := fun v => by
    change polar Q v v = 0
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hιf : ∀ g : ↥(orthDerived Q), ∀ u v, polarBilin Q ((g : V ≃ₗ[F] V) u) ((g : V ≃ₗ[F] V) v) =
      polarBilin Q u v := fun g u v => by
    rw [polarBilin_apply_apply, polarBilin_apply_apply]
    show Q ((g : V ≃ₗ[F] V) u + (g : V ≃ₗ[F] V) v) - Q ((g : V ≃ₗ[F] V) u) -
      Q ((g : V ≃ₗ[F] V) v) = Q (u + v) - Q u - Q v
    rw [← map_add (g : V ≃ₗ[F] V), hιQ, hιQ, hιQ]
  have hd1 : (d : V ≃ₗ[F] V) ≠ 1 := fun h => hd (Subtype.ext h)
  have hy' : (y : V ≃ₗ[F] V) ^ 11 = 1 := by rw [← Subgroup.coe_pow, hy]; rfl
  have hy1' : (y : V ≃ₗ[F] V) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hdy' : (d : V ≃ₗ[F] V) * y = y * d := by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hdy]
  have hd0 : fixedByEnd (d : V ≃ₗ[F] V) = ⊥ :=
    fixedByEnd_eq_bot_of_commute_eleven hF hV hd1 hy' hy1' hdy'
  obtain ⟨e', he'A, he8⟩ := exists_finrank_fixedByEnd_eq_eight hF hV halt hQ (hA.map ι)
    (by rw [Subgroup.card_map_of_injective hι]; exact h81)
    (by rintro _ ⟨g, -, rfl⟩ u v; exact hιf g u v) (Subgroup.mem_map_of_mem ι hdA) hd0
    (hT.map ι) (fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hι).1 h))
    (by rintro _ ⟨g, -, rfl⟩ u v; exact hιf g u v)
    ((Subgroup.map_mono hAT).trans (Subgroup.le_normalizer_map ι))
  have hc : ∀ g h : ↥(orthDerived Q), g * h = h * g → (g : V ≃ₗ[F] V) * h = h * g :=
    fun g h hgh => by simpa using congrArg Subtype.val hgh
  have hc' : ∀ g h : ↥(orthDerived Q), (g : V ≃ₗ[F] V) * h = h * g → g * h = h * g :=
    fun g h hgh => Subtype.ext (by simpa using hgh)
  obtain ⟨e, heA, rfl⟩ := Subgroup.mem_map.1 he'A
  have he8' : finrank F ↥(fixedByEnd (e : V ≃ₗ[F] V)) = 8 := he8
  have hde : d * e = e * d := hA.comm hdA heA
  refine ⟨e, heA, fun hey => finrank_fixedByEnd_ne_eight hF hV hy' hy1' (hc e y hey) he8',
    fun hbot => ?_⟩
  have hd3 : (d : V ≃ₗ[F] V) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hA.2 d hdA]; rfl
  have he3 : (e : V ≃ₗ[F] V) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hA.2 e heA]; rfl
  have hmap : (Subgroup.centralizer ({d} : Set ↥(orthDerived Q)) ⊓
      Subgroup.centralizer ({e} : Set ↥(orthDerived Q))).map ι =
      orthDerived Q ⊓ Subgroup.centralizer ({(d : V ≃ₗ[F] V)} : Set (V ≃ₗ[F] V)) ⊓
        Subgroup.centralizer ({(e : V ≃ₗ[F] V)} : Set (V ≃ₗ[F] V)) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨g, ⟨hgd, hge⟩, rfl⟩
      exact ⟨⟨g.2, hc g d hgd⟩, hc g e hge⟩
    · rintro ⟨⟨hz, hzd⟩, hze⟩
      exact ⟨⟨z, hz⟩, ⟨hc' ⟨z, hz⟩ d hzd, hc' ⟨z, hz⟩ e hze⟩, rfl⟩
  have hL := CFSG.glaPLayer_map_eq_of_injective Nat.prime_three ι hι
    (Subgroup.centralizer ({d} : Set ↥(orthDerived Q)) ⊓
      Subgroup.centralizer ({e} : Set ↥(orthDerived Q)))
  rw [hbot, Subgroup.map_bot, hmap] at hL
  exact glaPLayer_inf_ne_bot_of_quadratic hF hV hQ hd3 he3 (hc d e hde) (hιQ d) (hιQ e) hd0 he8'
    (X := orthDerived Q)
    (fun a haQ ha3 hfix => specialBlock_le_orthDerived_ten hF hV hQ haQ ha3 hfix)
    (fun g hg _ _ => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
      (orthDerived_le_orthogonalGroup hg)) hL.symm

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
