module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.SylowFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.TauCetiBridge
open scoped Matrix

set_option linter.unusedSectionVars false

section F4Neg


theorem innerPlaneBalance_adjointF4_of_negBalance {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : LangTorusPlaneBalance Tag.F4 f4Neg p fun q => p ∣ q + 1) (K : Type) [Field K]
    [Finite K] (hpq : p ∣ Nat.card K + 1) : InnerPlaneBalance p (adjointGroup Tag.F4 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data_F4 K
  set L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set n := canonicalRep (coxeterSystem Tag.F4) L f4Neg with hn
  set ι : adjointGroup Tag.F4 K →* ModGL Tag.F4 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.F4 K).subtype with hι
  have hιinj : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have : NeZero (((Nat.card K + 1 : ℕ)) : L) := ⟨by
    rw [Nat.cast_add, hK0, zero_add, Nat.cast_one]
    exact one_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.card K + 1)
  set ζu : Lˣ := (hζ.isUnit (by omega)).unit with hζu
  have hζu' : IsPrimitiveRoot ζu (Nat.card K + 1) :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  have hord : orderOf ζu = Nat.card K + 1 := hζu'.eq_orderOf.symm
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card (L := L)
    (rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_F4.choose_spec) f4Neg_smul hFr
    hζu'.pow_eq_one
  rw [hord] at hH₀card
  set X := H₀.map (MulAut.conj g0).toMonoidHom with hX
  have hXι : X ≤ ι.range := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype,
      ← (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices Tag.F4 (Or.inr rfl)
        K L Fr hFr).1,
      ← map_conj_twModel hg0C hg0]
    exact Subgroup.map_mono (hH₀T.trans (twistedTorus_le_twModel n Fr))
  set S : Subgroup (adjointGroup Tag.F4 K) := X.comap ι with hS
  have hScard : Nat.card S = (Nat.card K + 1) ^ Tag.F4.rank := by
    have hmap : S.map ι = X := by
      rw [hS, Subgroup.map_comap_eq, inf_eq_right.2 hXι]
    rw [← Subgroup.card_map_of_injective hιinj, hmap, hX,
      Subgroup.card_map_of_injective (MulAut.conj g0).injective, hH₀card]
  have hfac : (Nat.card (adjointGroup Tag.F4 K)).factorization p =
      (Nat.card S).factorization p := by
    rw [card_adjointGroup_F4, factorization_ordF4_of_dvd_add_one hp hp5 hq2 hpq,
      hScard, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      show Tag.F4.rank = 4 from rfl]
  have hconjS : ∀ A : Subgroup (adjointGroup Tag.F4 K), IsPGroup p A →
      ∃ c : adjointGroup Tag.F4 K, ∀ x ∈ A, c * x * c⁻¹ ∈ S := by
    intro A hA
    obtain ⟨S₁⟩ : Nonempty (Sylow p ↥S) := inferInstance
    set C : Subgroup (adjointGroup Tag.F4 K) := (S₁ : Subgroup ↥S).map S.subtype with hC
    have hCcard : Nat.card C = p ^ (Nat.card (adjointGroup Tag.F4 K)).factorization p := by
      rw [hC, Subgroup.card_map_of_injective S.subtype_injective, Sylow.card_eq_multiplicity, hfac]
    let P₀ : Sylow p (adjointGroup Tag.F4 K) := Sylow.ofCard C hCcard
    obtain ⟨P', hP'⟩ := hA.exists_le_sylow
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (adjointGroup Tag.F4 K) P₀ P'
    refine ⟨h⁻¹, fun x hx => ?_⟩
    have hxP' : x ∈ (P' : Subgroup (adjointGroup Tag.F4 K)) := hP' hx
    have : (P' : Subgroup (adjointGroup Tag.F4 K)) = (h • P₀ : Sylow p _) := by rw [hh]
    rw [this, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP'
    have hxC : h⁻¹ * x * h ∈ C := by
      have := hxP'
      rw [Sylow.coe_ofCard] at this
      exact this
    have hxS : h⁻¹ * x * h ∈ S := by
      obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hxC
      rw [← hy]
      exact y.2
    simpa using hxS
  refine innerPlaneBalance_of_conj_sylow hp
    (mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K))
    (fun x => baseChangeGL (algebraMap K L) (x : ModGL Tag.F4 K) ∈
      (twistedTorusOf n (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom)
    (fun A hA => ?_) fun D₁ hpow₁ hcard₁ hP₁ H hH =>
      hL K hpq Fr hFr g0 hg0C hg0 D₁ hpow₁ hcard₁ hP₁ H hH
  obtain ⟨c, hc⟩ := hconjS A fun x => ⟨1, Subtype.ext (by simpa using hA x.1 x.2)⟩
  exact ⟨c, fun x hx => Subgroup.map_mono hH₀T (hc x hx)⟩

end F4Neg

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
