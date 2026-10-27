module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NTri
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec4
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec6
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AR2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapMB
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT2e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDBase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Sporadic.Schreier.J4SFrattini
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8abC

open KD7 KD8ab KD8abB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {T₁ : Subgroup X}

omit [Finite X] in
theorem map_conj_le_centralizer {g : X} {K : Subgroup X}
    (hKc : K ≤ centralizer ({g * t * g⁻¹} : Set X)) :
    K.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({t} : Set X) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxc := mem_centralizer_singleton_iff.mp (hKc hx)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [mem_centralizer_singleton_iff]
  calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxc]
    _ = t * (g⁻¹ * x * g) := by group

theorem not_conjTo_of_card (S : KDBase A C) {m : X} {K : Subgroup X} (hK : IsPGroup 2 K)
    (hKc : K ≤ centralizer ({m} : Set X)) (hcard : 64 < Nat.card K) : ¬ ConjTo t m := by
  rintro ⟨g, rfl⟩
  set K' : Subgroup X := K.map (MulAut.conj g⁻¹).toMonoidHom
  have hK' : IsPGroup 2 K' := hK.map _
  obtain ⟨h, -, hh⟩ := SD.exists_conj_le_T (A := A) hK' (map_conj_le_centralizer hKc)
  have h1 : Nat.card (K'.map (MulAut.conj h).toMonoidHom) = Nat.card K := by
    rw [card_map_of_injective (MulAut.conj h).injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  have h2 := card_le_of_le hh
  rw [h1, KD46.card_T_64 S] at h2
  omega

theorem d8_mul_refl_pow_four : ∀ e : ZMod 8, dbit8 e = 0 → (d8 * aff8 (-1) e) ^ 4 ≠ 1 := by
  decide

theorem not_conjTo_of_exp4 (S : KDBase A C) {m : X} {K : Subgroup X} (hK : IsPGroup 2 K)
    (hKc : K ≤ centralizer ({m} : Set X)) (hcard : 64 ≤ Nat.card K)
    (hexp : ∀ g ∈ K, g ^ 4 = 1) : ¬ ConjTo t m := by
  rintro ⟨g, rfl⟩
  set K' : Subgroup X := K.map (MulAut.conj g⁻¹).toMonoidHom
  have hK' : IsPGroup 2 K' := hK.map _
  obtain ⟨h, -, hh⟩ := SD.exists_conj_le_T (A := A) hK' (map_conj_le_centralizer hKc)
  have h1 : Nat.card (K'.map (MulAut.conj h).toMonoidHom) = Nat.card K := by
    rw [card_map_of_injective (MulAut.conj h).injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  have heq : K'.map (MulAut.conj h).toMonoidHom = A.T :=
    eq_of_le_of_card_ge hh (by rw [h1, KD46.card_T_64 S]; exact hcard)
  have hdy : C.d * S.y ∈ A.T := mul_mem C.d_mem (KD46.y_mem_T S)
  have h4 : (C.d * S.y) ^ 4 = 1 := by
    have hdy' := hdy
    rw [← heq] at hdy'
    obtain ⟨_, ⟨x, hx, rfl⟩, hxe⟩ := hdy'
    have e : C.d * S.y = (h * g⁻¹) * x * (h * g⁻¹)⁻¹ := by
      rw [← hxe]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e, conj_pow, hexp x hx, mul_one, mul_inv_cancel]
  obtain ⟨e, he, hψy⟩ := KD46.ψ_y S
  have h5 := SD.ψX_pow (A := A) hdy 4
  rw [h4, SD.ψX_one, SD.ψX_mul C.d_mem (KD46.y_mem_T S), SDKD.ψX_d C, hψy] at h5
  exact d8_mul_refl_pow_four e he h5.symm

omit [Finite X] in
theorem card_le_of_orbit {N : Subgroup X} {x : X} (I : Finset X)
    (hI : ∀ n ∈ N, n * x * n⁻¹ ∈ I) :
    Nat.card N ≤ I.card * Nat.card (N ⊓ centralizer ({x} : Set X) : Subgroup X) := by
  classical
  set D : Subgroup N := (N ⊓ centralizer ({x} : Set X)).subgroupOf N with hDdef
  have hD : Nat.card D = Nat.card (N ⊓ centralizer ({x} : Set X) : Subgroup X) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmemD : ∀ a b : N, a⁻¹ * b ∈ D ↔ (a : X) * x * (a : X)⁻¹ = (b : X) * x * (b : X)⁻¹ := by
    intro a b
    rw [hDdef, mem_subgroupOf, coe_mul, coe_inv, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hc⟩
      have e : (a : X)⁻¹ * b * x * ((a : X)⁻¹ * b)⁻¹ = x := by rw [hc, mul_inv_cancel_right]
      calc (a : X) * x * (a : X)⁻¹
          = a * ((a : X)⁻¹ * b * x * ((a : X)⁻¹ * b)⁻¹) * (a : X)⁻¹ := by rw [e]
        _ = (b : X) * x * (b : X)⁻¹ := by group
    · intro h
      refine ⟨mul_mem (inv_mem a.2) b.2, ?_⟩
      calc (a : X)⁻¹ * b * x = (a : X)⁻¹ * ((b : X) * x * (b : X)⁻¹) * b := by group
        _ = (a : X)⁻¹ * ((a : X) * x * (a : X)⁻¹) * b := by rw [h]
        _ = x * ((a : X)⁻¹ * b) := by group
  let f : N ⧸ D → I := Quotient.lift (fun n : N => ⟨(n : X) * x * (n : X)⁻¹, hI n n.2⟩)
    (fun a b hab => Subtype.ext ((hmemD a b).mp (QuotientGroup.leftRel_apply.mp hab)))
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on
    induction q₂ using QuotientGroup.induction_on
    rw [QuotientGroup.eq]
    exact (hmemD _ _).mpr (congrArg Subtype.val h)
  have h1 : Nat.card (N ⧸ D) ≤ I.card := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card (α := I), Fintype.card_coe] at this
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D, hD]
  exact Nat.mul_le_mul_right _ h1

theorem false_of_transfer [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (ht : orderOf t = 2) (P : Sylow 2 X) {M : Subgroup X} (hMP : M ≤ P)
    (hindex : M.relIndex P = 2) (hM : ∀ m ∈ M, ¬ ConjTo t m) : False :=
  KD8ab.false_of_transfer' hX ht P.isPGroup' (fun _ hR hle => P.is_maximal' hR hle) hMP hindex
    hM

theorem exists_mem_normalizer {T Q : Subgroup X} (hQ : IsPGroup 2 Q) (hTQ : T < Q) :
    ∃ h ∈ Q, h ∉ T ∧ h ∈ normalizer (T : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := T.subgroupOf Q with hI
  have hIne : I ≠ ⊤ := by
    intro htop
    apply hTQ.ne
    refine le_antisymm hTQ.le (fun x hx => ?_)
    have : (⟨x, hx⟩ : Q) ∈ I := by rw [htop]; trivial
    exact this
  have hnil : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : I < normalizer (I : Set Q) :=
    Group.normalizerCondition_of_isNilpotent I (lt_of_le_of_ne le_top hIne)
  obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun h => hxI h, ?_⟩
  have hxsub : x ∈ (normalizer (T : Set X)).subgroupOf Q := by
    rw [subgroupOf_normalizer_eq hTQ.le]
    exact hxN
  exact mem_subgroupOf.mp hxsub

theorem card_le_256 {S : KDBase A C} (B : KD8abB.BData S T₁) {g : X} {K : Subgroup X}
    (hK : IsPGroup 2 K)
    (hKN : K ≤ normalizer (((S.E S.y).map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X)) :
    Nat.card K ≤ 256 := by
  set K' : Subgroup X := K.map (MulAut.conj g⁻¹).toMonoidHom with hK'def
  have hK' : IsPGroup 2 K' := hK.map _
  have hmem : ∀ y : X, y ∈ (S.E S.y).map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ S.E S.y := by
    intro y
    rw [mem_map_equiv, MulAut.conj_symm_apply]
  have hK'N : K' ≤ normalizer (S.E S.y : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mem_normalizer_iff]
    intro e
    have h1 := (mem_normalizer_iff.mp (hKN hx)) (g * e * g⁻¹)
    rw [hmem, hmem, show g⁻¹ * (g * e * g⁻¹) * g = e by group,
      show g⁻¹ * (x * (g * e * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * e * (g⁻¹ * x * g)⁻¹ by group] at h1
    exact h1
  obtain ⟨k, -, hkS⟩ := KD8abB.exists_conj_le_of_max B.G.D₁.S₁_le hK'N B.isPGroup_S₁ hK'
    B.G.D₁.S₁_maximal
  have hle : K'.map (MulAut.conj k⁻¹).toMonoidHom ≤ B.G.D₁.S₁ := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hkS y hy
  calc Nat.card K = Nat.card K' := (card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    _ = Nat.card (K'.map (MulAut.conj k⁻¹).toMonoidHom) :=
        (card_map_of_injective (MulAut.conj k⁻¹).injective).symm
    _ ≤ Nat.card B.G.D₁.S₁ := card_le_of_le hle
    _ = 256 := B.card_S₁

end KD8abC

end CFSG.OddStandard.SmallF3.L33.KD
