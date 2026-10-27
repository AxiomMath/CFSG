module

public import CFSG.ClassicalInvolution.Q3.TL4Thm5Outer
public import CFSG.ClassicalInvolution.Q3.TA3LeafL2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3U4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5G2D4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4
public import CFSG.ClassicalInvolution.Q3.TA3LeafTwistedG2
public import CFSG.ClassicalInvolution.Q3.TA3SmallBase
public import CFSG.ClassicalInvolution.Q3.TL4Thm6PSp43
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Split

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

section Cit3


@[expose] def Thm5SmallLeaf (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CIT3Below (Nat.card X) → ∀ Φ : Set (Subgroup X),
    TypeRFam 3 Φ → classicalInvolutionOddCore X = ⊥ → IsSimpleGroup ↥(genFittingFStar X) →
    (∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) →
    (∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M) → omegaGen Φ = ⊤ →
    TwoSubgroupsFourGenerated ↥(genFittingFStar X) → P ↥(genFittingFStar X) →
    ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, ∀ z t : X, IsUniqueInvolution K z → IsUniqueInvolution J t →
      alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥

end Cit3

namespace Small

theorem outTwoCyclic_l33 {F : Type} [Group F] [Finite F] (h : LieModel F .PSL 3 3 1) :
    Nobq.OutTwoCyclic F := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : Finite (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K) :=
    Finite.of_equiv F e.toEquiv
  refine Nobq.OutTwoCyclic.of_mulEquiv e (TA3.outTwoCyclic_of_card_dvd (m := 1) odd_one ?_)
  have h1 :=
    LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
      (k := K) Nat.prime_three le_rfl le_rfl hK
  norm_num at h1
  simpa using h1

section Datum

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem tightCls_of_gen (hΦ : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (htr : ∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M) (hgen : omegaGen Φ = ⊤)
    {K : Subgroup X} (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z) (S : Sylow 2 ↥K) :
    TightDatum K S z ∧ TightCls X K S z ∧ CoreAssembly.conjClass K = Φ ∧ tightCore K = K := by
  have hcl : CoreAssembly.conjClass K = Φ := by
    ext M
    constructor
    · rintro ⟨g, rfl⟩
      exact hΦ.hyp.conjInvariant g K hK
    · intro hM
      exact htr K hK M hM
  have hcore : tightCore K = K := hΦ.closure_twoElts hK
  refine ⟨Vtx.tightDatum_of_mem hΦ hK hz S, ⟨Vtx.nonempty_sylow_equiv hΦ hK S, ?_, hO⟩, hcl,
    hcore⟩
  show (⨆ g : X, conjSub g (tightCore K)) = ⊤
  rw [hcore, ← iSup_conjClass_eq, hcl]
  exact hgen

omit [Finite X] in
theorem false_of_tightEdgeless {K : Subgroup X} (hK : K ∈ Φ)
    (hcl : CoreAssembly.conjClass K = Φ) (hcore : tightCore K = K) (hed : TightEdgeless K)
    {J : Subgroup X} (hJ : J ∈ omegaNbr Φ K) : False := by
  have h1 : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore K)) := hed
  rw [hcore, hcl] at h1
  exact h1 K hK J hJ.1 (Or.inl hJ)

end Datum

section Leaves


theorem leaf_of_split {P Q₃ Q : ∀ (F : Type) [Group F], Prop}
    (hs : ∀ (F : Type) [Group F], P F → Q₃ F ∨ Q F) (h₃ : Thm5SmallLeaf Q₃)
    (h : Thm5SmallLeaf Q) : Thm5SmallLeaf P := by
  intro X _ _ hA Φ hΦ hO hss hnab htr hgen hG hPF
  rcases hs _ hPF with h1 | h1
  · exact h₃ X hA Φ hΦ hO hss hnab htr hgen hG h1
  · exact h X hA Φ hΦ hO hss hnab htr hgen hG h1

theorem leaf_of_noQ8Datum {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → TA3.NoQ8Datum F) : Thm5SmallLeaf P := by
  intro X _ _ _ Φ hΦ hO hs hnab htr hgen hG hPF K hK J hJ z t hz ht
  exfalso
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  obtain ⟨hd, hc, -, -⟩ := tightCls_of_gen hΦ hO htr hgen hK hz S
  have := genFittingFStar_normal X
  exact h _ hPF X (genFittingFStar X) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) hG K S z hd hc.1

theorem leaf_of_noDatum {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → Nobq.NoDatum F) : Thm5SmallLeaf P := by
  intro X _ _ _ Φ hΦ hO hs hnab htr hgen hG hPF K hK J hJ z t hz ht
  exfalso
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  obtain ⟨hd, -, -, -⟩ := tightCls_of_gen hΦ hO htr hgen hK hz S
  have := genFittingFStar_normal X
  obtain ⟨r, hr, ⟨eS⟩⟩ := hd.quat
  exact h _ hPF X (genFittingFStar X) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) K S r hr ⟨eS⟩ z hd.mem hd.order hd.cent
    hd.normal

theorem leaf_of_oddCore {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
      (∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) → P ↥(genFittingFStar X) → ∀ a : X,
        orderOf a = 2 → oddCoreOf (Subgroup.centralizer ({a} : Set X)) = ⊥) :
    Thm5SmallLeaf P := by
  intro X _ _ _ Φ hΦ hO hs hnab htr hgen hG hPF K hK J hJ z t hz ht
  obtain ⟨-, hzt⟩ := Outer.ne_and_commute_of_mem_omegaNbr hΦ hK hz hJ ht
  exact Outer.alphaOf_pair_eq_bot hz.sq ht.sq hzt hz.ne_one fun a ha ha1 =>
    h X hs hnab hPF a (Outer.orderOf_eq_two_of_mem_pair hz.sq ht.sq hzt ha ha1)

theorem leaf_of_autOddFreeInner {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
      P F → Q3NM.AutOddFreeInner F ∧ Nobq.OutTwoCyclic F) : Thm5SmallLeaf P := by
  intro X _ _ _ Φ hΦ hO hs hnab htr hgen hG hPF K hK J hJ z t hz ht
  obtain ⟨-, hzt⟩ := Outer.ne_and_commute_of_mem_omegaNbr hΦ hK hz hJ ht
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  obtain ⟨hd, -, -, -⟩ := tightCls_of_gen hΦ hO htr hgen hK hz S
  have := genFittingFStar_normal X
  obtain ⟨hAI, hOut⟩ := h _ hnab hPF
  obtain ⟨hzF, -⟩ := TA3.TightDatum.exists_cyclic4_of_outTwoCyclic hd
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) hOut
  obtain ⟨g, hg⟩ := Outer.exists_conj_of_trans htr hK hz hJ.1 ht
  have htF : t ∈ genFittingFStar X := hg ▸ (genFittingFStar_normal X).conj_mem z hzF g
  exact Outer.alphaOf_eq_bot_of_autOddFreeInner hO hs hnab hAI hzF htF hz.sq ht.sq hzt hz.ne_one

theorem leaf_m11 :
    Thm5SmallLeaf TA3.SmallM11 :=
  leaf_of_oddCore fun X _ _ hs hnab hPF a ha => by
    have : (genFittingFStar X).Normal := genFittingFStar_normal X
    obtain ⟨ψ⟩ := hPF
    have h := CFSG.Sporadic.Schreier.oddCore_centralizer_eq_bot_of_normal
      CFSG.Sporadic.Schreier.m11_inner_oddCore
      (CFSG.Sporadic.Schreier.m11_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num)))
      CFSG.Sporadic.Schreier.m11_outer_oddCore (genFittingFStar X) ψ
      (centralizer_genFittingFStar_eq_bot hnab) a ha
    show (classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set X))).map _ = ⊥
    rw [show classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set X)) =
      CFSG.oddCore ↥(Subgroup.centralizer ({a} : Set X)) from rfl, h, Subgroup.map_bot]

theorem leaf_m12 :
    Thm5SmallLeaf TA3.SmallM12 :=
  leaf_of_oddCore fun _ _ _ hs hnab hPF _ ha => Outer.oddCoreOf_eq_bot_of_m12 hs hnab hPF ha

theorem autOddFreeInner_of_lieModel3 {t : Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (hFT : IsFundTag t) (hadm : Assembly.LowTwoRank.StatedLieAdmissible t m 3 1)
    (hD4 : ¬ (t = .POmegaPlus ∧ m = 4)) (hT : t ≠ .trialityD4) (F : Type) [Group F] [Finite F]
    [IsSimpleGroup F] (h : LieModel F t m 3 1) : Q3NM.AutOddFreeInner F := by
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover t m 3 1 Nat.prime_three (by norm_num) hFT hadm F h
  exact Q3NM.autOddFreeInnerTag_of_not_D4 hD4 hT Nat.prime_three hFT hadm F ψ hψ hker

theorem autOddFreeInner_of_lieModel_td4 (F : Type) [Group F] [Finite F] [IsSimpleGroup F]
    (h : LieModel F .trialityD4 0 3 1) : Q3NM.AutOddFreeInner F := by
  have hadm : Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1 :=
    ⟨Nat.prime_three, le_rfl, rfl⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover .trialityD4 0 3 1 Nat.prime_three (by norm_num) trivial hadm F h
  exact Q3NM.autOddFreeInnerTag_trialityD4 Nat.prime_three trivial hadm F ψ hψ hker

theorem leaf_g23 : Thm5SmallLeaf fun F _ => LieModel F .G2 0 3 1 :=
  leaf_of_autOddFreeInner fun F _ _ _ _ h =>
    ⟨autOddFreeInner_of_lieModel3 (t := .G2) (m := 0) trivial ⟨Nat.prime_three, le_rfl, by decide⟩
      (by decide) (by decide) F h,
      TA3.outTwoCyclic_G2 (by norm_num)
        (Upgrade.chevalleyExceptionalModel_of_lieModel (by decide) h)⟩

theorem leaf_d43 : Thm5SmallLeaf fun F _ => LieModel F .trialityD4 0 3 1 :=
  leaf_of_autOddFreeInner fun F _ _ _ _ h =>
    ⟨autOddFreeInner_of_lieModel_td4 F h, TA3.outTwoCyclic_trialityD4 (by norm_num)
      (Upgrade.chevalleyExceptionalModel_of_lieModel (by decide) h)⟩

theorem leaf_l53 : Thm5SmallLeaf fun F _ => LieModel F .PSL 5 3 1 :=
  leaf_of_autOddFreeInner fun F _ _ _ _ h =>
    ⟨autOddFreeInner_of_lieModel3 (t := .PSL) (m := 5) trivial ⟨Nat.prime_three, le_rfl, by decide⟩
      (by decide) (by decide) F h, TA3.outTwoCyclic_PSL5 Nat.prime_three le_rfl (by norm_num) h⟩

theorem leaf_u33 : Thm5SmallLeaf fun F _ => LieModel F .PSU 3 3 1 :=
  leaf_of_autOddFreeInner fun F _ _ _ _ h =>
    ⟨autOddFreeInner_of_lieModel3 (t := .PSU) (m := 3) trivial ⟨Nat.prime_three, le_rfl, by decide⟩
      (by decide) (by decide) F h,
      TA3.outTwoCyclic_PSU (Upgrade.statedClassicalModel_of_lieModel (by decide) h) (by decide)⟩

theorem leaf_l33 : Thm5SmallLeaf fun F _ => LieModel F .PSL 3 3 1 :=
  leaf_of_autOddFreeInner fun F _ _ _ _ h =>
    ⟨autOddFreeInner_of_lieModel3 (t := .PSL) (m := 3) trivial ⟨Nat.prime_three, le_rfl, by decide⟩
      (by decide) (by decide) F h, outTwoCyclic_l33 h⟩

theorem leaf_l2 : Thm5SmallLeaf TA3.SmallL2 := by
  intro X _ _ _ Φ hΦ hO hs hnab htr hgen _ hPF K hK J hJ z t hz _
  exfalso
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  obtain ⟨hd, hc, hcl, hcore⟩ := tightCls_of_gen hΦ hO htr hgen hK hz S
  obtain ⟨p, f, hp, hp2, hf, hadm, F, _, _, hcard, ⟨e₀⟩⟩ := hPF
  obtain ⟨-, -, -, -, h3⟩ := hadm
  have : Fact p.Prime := ⟨hp⟩
  have hKodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hcard⟩
  have hK3 : 3 < Nat.card F := by
    have hq3 : p ^ f ≠ 3 := fun h => h3 (by rw [h])
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpq : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have := genFittingFStar_normal X
  let e : genFittingFStar X ≃* GorensteinWalter.PSL2 F :=
    e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hsurj := GorensteinWalter.pGammaL2ToMulAutPSL2_surjective F hcard hKodd hK3
  have hι := GorensteinWalter.normalPSL2ToPGammaL2_injective (genFittingFStar X) F hKodd hK3 e
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) hsurj
  exact false_of_tightEdgeless hK hcl hcore (TA3.tightEdgeless_of_embedding hKodd hd hc _ hι) hJ

theorem leaf_psp4 : Thm5SmallLeaf TA3.SmallPSp4 :=
  leaf_of_split Thm6.split_psp4 (leaf_of_noQ8Datum Thm6.noQ8Datum_psp43)
    (leaf_of_noQ8Datum TA3.noQ8Datum_psp4Ne3)

theorem leaf_twistedG2 : Thm5SmallLeaf TA3.SmallTwistedG2 :=
  leaf_of_noDatum TA3.noDatum_smallTwistedG2

theorem leaf_l4 : Thm5SmallLeaf TA3.SmallL4 :=
  leaf_of_split Thm6.split_l4 (leaf_of_noQ8Datum TA3.noQ8Datum_l43)
    (leaf_of_noQ8Datum TA3.noQ8Datum_l4Ne3)

theorem leaf_u4 : Thm5SmallLeaf TA3.SmallU4 :=
  leaf_of_split Thm6.split_u4 (leaf_of_noQ8Datum TA3.noQ8Datum_u43)
    (leaf_of_noQ8Datum TA3.noQ8Datum_u4Ne3)

theorem leaf_u5 : Thm5SmallLeaf TA3.SmallU5 :=
  leaf_of_noQ8Datum TA3.noQ8Datum_u5

theorem leaf_g2 : Thm5SmallLeaf TA3.SmallG2 :=
  leaf_of_split Thm6.split_g2 leaf_g23 (leaf_of_noQ8Datum TA3.noQ8Datum_g2Ne3)

theorem leaf_d4 : Thm5SmallLeaf TA3.SmallD4 :=
  leaf_of_split Thm6.split_d4 leaf_d43 (leaf_of_noQ8Datum TA3.noQ8Datum_d4Ne3)

theorem leaf_l5 : Thm5SmallLeaf TA3.SmallL5 :=
  leaf_of_split Thm6.split_l5 leaf_l53 (leaf_of_noQ8Datum TA3.noQ8Datum_l5Ne3)

end Leaves

end Small

theorem thm5SmallR_three_of (hGH : GH74SectionalModels) (hL3 : Thm5SmallLeaf TA3.SmallL3Ne3)
    (hU3 : Thm5SmallLeaf TA3.SmallU3Ne3) {n : ℕ} (hA : CIT3Below n) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → ∀ Φ : Set (Subgroup X), TypeRFam 3 Φ →
      classicalInvolutionOddCore X = ⊥ → IsSimpleGroup ↥(genFittingFStar X) →
      (∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) →
      (∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M) → omegaGen Φ = ⊤ →
      TwoSubgroupsFourGenerated ↥(genFittingFStar X) →
      ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, ∀ z t : X, IsUniqueInvolution K z → IsUniqueInvolution J t →
        alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥ := by
  intro X _ _ hXn Φ hΦ hO hs hnab htr hgen hP K hK J hJ z t hz ht
  have hA' : CIT3Below (Nat.card X) := hXn ▸ hA
  rcases TA3.smallList hGH _ hnab hP with (h | h | h | h | h | h | h | h | h | h | h | h | h) | hex
  · exact Small.leaf_g2 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_d4 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_psp4 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_twistedG2 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_l4 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_u4 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_l5 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_u5 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_m12 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_l2 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exact Small.leaf_of_split Thm6.split_l3 Small.leaf_l33 hL3 X hA' Φ hΦ hO hs hnab htr hgen hP
      h K hK J hJ z t hz ht
  · exact Small.leaf_of_split Thm6.split_u3 Small.leaf_u33 hU3 X hA' Φ hΦ hO hs hnab htr hgen hP
      h K hK J hJ z t hz ht
  · exact Small.leaf_m11 X hA' Φ hΦ hO hs hnab htr hgen hP h K hK J hJ z t hz ht
  · exfalso
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
    obtain ⟨hd, -, -, -⟩ := Small.tightCls_of_gen hΦ hO htr hgen hK hz S
    have := genFittingFStar_normal X
    obtain ⟨r, hr, ⟨eS⟩⟩ := hd.quat
    exact (Nobq.smallNoDatum_of_dvd Nobq.card_outer_Ly_dvd_two).noDatum _ hex X
      (genFittingFStar X) ⟨MulEquiv.refl _⟩ (Nobq.centralizer_genFittingFStar_eq_bot hnab) K S r
      hr ⟨eS⟩ z hd.mem hd.order hd.cent hd.normal

end CFSG.ClassicalInvolution.Q3.TL4
