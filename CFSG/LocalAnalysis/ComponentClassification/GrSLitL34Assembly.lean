module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReach39
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitThmBReach
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReduction
public import CFSG.LocalAnalysis.ComponentClassification.GSFMReduction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Central
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34CentralZ
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate2022
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2195
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2198
public import Certificates.Certificate2199
public import Certificates.Certificate2200
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2203
public import Certificates.Certificate2204
public import Certificates.Certificate2205
public import Certificates.Certificate2233
public import Certificates.Certificate2234
public import Certificates.Certificate2235
public import Certificates.Certificate2278
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3046
public import Certificates.Certificate3086
public import Certificates.Certificate3120
public import Certificates.Certificate3139
public import Certificates.Certificate3157
public import Certificates.Certificate3168
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainRankTwoMaximality
public import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def GSL34ClosedType (K : Type) [Group K] : Prop :=
  IsL34Type (K ⧸ Open.fusionZStar K) ∨ IsL2Type 5 (K ⧸ Open.fusionZStar K) ∨
    IsL2Type 7 (K ⧸ Open.fusionZStar K)

theorem GSL34ClosedType.of_equiv {L M : Type} [Group L] [Group M]
    (e : L ⧸ Open.fusionZStar L ≃* M ⧸ Open.fusionZStar M) (h : GSL34ClosedType M) :
    GSL34ClosedType L := by
  rcases h with h | h | h
  · exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  · exact Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h))
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h))

variable {G : Type} [Group G] [Finite G]

theorem gsL34ClosedType_of_gsWeakCorr (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {L M : Subgroup G}
    (h : GSWeakCorr a L b M) (hbZ : b ∉ center G) (hM : GSL34ClosedType M) :
    GSL34ClosedType L := by
  rcases gsWeakCorr_type_dichotomy hS hK h hbZ with he | ⟨hMa, hTM, hTpc, hlt, he⟩
  · obtain ⟨e⟩ := he
    exact GSL34ClosedType.of_equiv e hM
  · obtain ⟨e⟩ := he
    obtain ⟨ha, hb, hab, -, -, hMb, hMp, -⟩ := h
    refine GSL34ClosedType.of_equiv e ?_
    rcases hM with hτ | hτ | hτ
    · rcases l34FixedInput G a b M _ ha hb hab hMb hMp hMa hTM hTpc hlt hτ with hρ | hρ
      · exact Or.inr (Or.inl hρ)
      · exact Or.inr (Or.inr hρ)
    · exact (l2FixedInput.1 G a b M _ ha hb hab hMb hMp hMa hTM hTpc hlt hτ).elim
    · exact (l2FixedInput.2 G a b M _ ha hb hab hMb hMp hMa hTM hTpc hlt hτ).elim

theorem gsL34ClosedType_of_gsWeakReach (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) (hZ : ∀ z : G, orderOf z = 2 → z ∉ center G)
    {J₀ J : Subgroup G} (h : GSWeakReach J₀ J) (hJ : GSL34ClosedType J) : GSL34ClosedType J₀ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hJ
  | head hst _ ih =>
    obtain ⟨a, b, hC⟩ := hst
    exact gsL34ClosedType_of_gsWeakCorr hS hK hC (hZ b hC.2.1) ih

theorem card_of_gsL34ClosedType {K : Type} [Group K] (h : GSL34ClosedType K) :
    Nat.card (K ⧸ Open.fusionZStar K) = 20160 ∨ Nat.card (K ⧸ Open.fusionZStar K) = 60 ∨
      Nat.card (K ⧸ Open.fusionZStar K) = 168 := by
  rcases h with h | h | h
  · exact Or.inl (GSThmB.card_of_lieModel_L34 h)
  · right; left
    rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h]
    decide
  · right; right
    rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h]
    decide

theorem eq_of_ordA_one_eq_sixty {m : ℕ} (h : Open.ordA 1 m = 60) : m = 4 ∨ m = 5 := by
  rcases GSThmB.eq_of_ordA_one_eq (Or.inl h) with h4 | h5 | h7
  · exact Or.inl h4
  · exact Or.inr h5
  · subst h7
    exact absurd h (by decide)

theorem eq_of_ordA_one_eq_168 {m : ℕ} (h : Open.ordA 1 m = 168) : m = 7 := by
  rcases GSThmB.eq_of_ordA_one_eq (Or.inr h) with h4 | h5 | h7
  · subst h4
    exact absurd h (by decide)
  · subst h5
    exact absurd h (by decide)
  · exact h7

theorem eq_and_eq_one_of_pow_eq_prime {p f q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ^ f = q) :
    p = q ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    exact hq.one_lt.ne h
  have hpq : p ∣ q := h ▸ dvd_pow_self p hf
  rcases (Nat.dvd_prime hq).mp hpq with h1 | h1
  · exact absurd h1 hp.one_lt.ne'
  · subst h1
    refine ⟨rfl, ?_⟩
    have := Nat.pow_right_injective hp.two_le (show p ^ f = p ^ 1 by rw [pow_one, h])
    exact this

omit [Finite G] in
theorem pumpUp_le_centralizer {J : Subgroup G} {t : G} :
    pumpUp J t ≤ centralizer ({t} : Set G) := by
  refine iSup₂_le fun g hg => ?_
  have hgC : g ∈ centralizer ({t} : Set G) := map_subtype_le _ hg
  rintro _ ⟨y, hy, rfl⟩
  have hyC : y ∈ centralizer ({t} : Set G) := (map_subtype_le _ hy).2
  exact mul_mem (mul_mem (inv_mem hgC) hyC) (inv_mem (inv_mem hgC))

end CFSG.ComponentClassification.GrSLit
