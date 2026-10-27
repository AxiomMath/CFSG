module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InnRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Inn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173InnDiagImage
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinAut
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UniAut
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_map_congr)
open scoped commutatorElement

namespace Noncyc

private theorem not_isCyclic_of_card {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) : ¬ IsCyclic E := by
  intro hc
  have h1 : Monoid.exponent E = Nat.card E := IsCyclic.exponent_eq_card
  have h2 : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (by simpa using hE.2 y y.2)
  have h3 : Nat.card E ≤ p := h1 ▸ Nat.le_of_dvd hp.pos h2
  have h4 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h4
  omega

private theorem exists_not_isCyclic_of_surjective {H Q : Type*} [Group H] [Finite H] [Group Q]
    {p : ℕ} (hp : p.Prime) (π : H →* Q) (hπ : Function.Surjective π) (E : Subgroup Q)
    (hEp : IsPGroup p E) (hE : ¬ IsCyclic E) :
    ∃ P : Subgroup H, IsPGroup p P ∧ ¬ IsCyclic P := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite Q := Finite.of_surjective π hπ
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  refine ⟨(P : Subgroup H), P.isPGroup', fun hc => hE ?_⟩
  obtain ⟨T, hET⟩ := hEp.exists_le_sylow
  haveI h1 : IsCyclic ↥((P : Subgroup H).map π) :=
    isCyclic_of_surjective (π.subgroupMap (P : Subgroup H)) (π.subgroupMap_surjective _)
  haveI : IsCyclic ↥(T : Subgroup Q) :=
    (Sylow.equiv T (P.mapSurjective hπ)).isCyclic.mpr h1
  exact Subgroup.isCyclic_of_le hET

private theorem card_le_mul_card_inf_of_le_cyclic {G : Type*} [Group G] [Finite G]
    (N D : Subgroup G) [N.Normal] (hcyc : IsCyclic (D ⧸ N.subgroupOf D)) {p : ℕ} (hp : p.Prime)
    (E : Subgroup G) (hE : IsElemAbelian p E) (hED : E ≤ D) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ N) := by
  obtain ⟨γ, hγ⟩ := hcyc.exists_generator
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective γ
  refine CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_le_mul_card_inf_of_zpowers N hp E hE
    (g₀ : G) fun y hy => ?_
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hγ (QuotientGroup.mk ⟨y, hED hy⟩))
  refine ⟨-j, ?_⟩
  have h1 : (QuotientGroup.mk (g₀ ^ (-j) * (⟨y, hED hy⟩ : D)) : D ⧸ N.subgroupOf D) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← hj, _root_.zpow_neg, inv_mul_cancel]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

private abbrev NoncycProp (p : ℕ) : CFSG.Assembly.LargeEvenRawCont := fun R _ I _ =>
  (∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsElemAbelian p E →
        Nat.card E ≤ p * Nat.card ↥(E ⊓ (MulAut.conj : R →* MulAut R).range)) ∨
    ∃ r, 2 ≤ r ∧ GGTorusLift p r R

private theorem noncyc_linear {lab : GLALabel} (htag : lab.tag = .A) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ∣ rk2DiagIndex lab) : Rk2LabelAll lab (NoncycProp p) := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .A := htag
  cases ht
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', Or.inl ?_⟩
  intro E hE hEel
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hd : 3 ≤ l + 1 := by
    have h1 : p ∣ l + 1 :=
      hpd.trans (by simpa [rk2DiagIndex] using Nat.gcd_dvd_left (l + 1) (2 ^ n - 1))
    have h2 := Nat.le_of_dvd (by omega) h1
    have h3 := hp.two_le
    omega
  have hcl : Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) K)) Set.univ ∪
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K) →*
          MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K)))) ≤
      RecipeFieldLinear.recI (l + 1) K := by
    refine (Subgroup.closure_le (RecipeFieldLinear.recI (l + 1) K)).mpr (Set.union_subset ?_ ?_)
    · intro y hy
      rw [RecipeFieldLinear.coe_recI]
      exact hy
    · rintro _ ⟨r, rfl⟩
      exact RecipeFieldLinear.conj_mem_recI r
  have hErec : E ≤ RecipeFieldLinear.recI (l + 1) K := hE.trans hcl
  let e := TypeA.recipeEquiv (l + 1) K
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hE'D : E.map (MulAut.congr e).toMonoidHom ≤ linearAutGroup (l + 1) K := by
    intro y hy
    obtain ⟨z, hzE, rfl⟩ := Subgroup.mem_map.mp hy
    exact (RecipeFieldLinear.mem_recI_iff).mp (hErec hzE)
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_le_mul_card_inf_inner_of_le hd hp _
    (hEel.map _) hE'D
  rw [Subgroup.card_map_of_injective hinj, AutSt.range_conj_congr e,
    ← Subgroup.map_inf_eq _ _ _ hinj, Subgroup.card_map_of_injective hinj] at h
  exact h

private theorem noncyc_unitary {lab : GLALabel} (hlab : GLAInLambda2 lab) (htag : lab.tag = .twA)
    {p : ℕ} (hp : p.Prime) : Rk2LabelAll lab (NoncycProp p) := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .twA := htag
  cases ht
  dsimp only [GLAInLambda2] at hlab ⊢
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', Or.inl ?_⟩
  intro E hE hEel
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hn : 1 ≤ n := by simpa using hlab.1
  have hl2 : 2 ≤ l := hlab.2.1
  have hd : 3 ≤ l + 1 := by omega
  have hne : ¬(l + 1 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨h3, h2⟩
    have hl : l = 2 := by omega
    have hn2 : 2 ≤ n := hlab.2.2 hl
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have h : UnitaryFieldData 2 n K := unitaryFieldData_of_card hn hK
  have hd1 : 1 ≤ l + 1 := by omega
  have hcl : Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
          (LargeEvenGUSet (Fin (l + 1)) K (2 ^ n)) ∪
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))))) ≤
      RecipeFieldSU.recIU (l + 1) h hd1 := by
    refine (Subgroup.closure_le (RecipeFieldSU.recIU (l + 1) h hd1)).mpr (Set.union_subset ?_ ?_)
    · intro y hy
      rw [RecipeFieldSU.coe_recIU h hK hd1]
      exact hy
    · rintro _ ⟨r, rfl⟩
      exact RecipeFieldSU.conj_mem_recIU h hd1 r
  have hErec : E ≤ RecipeFieldSU.recIU (l + 1) h hd1 := hE.trans hcl
  let e := InndiagSU.projEquiv h hd1
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hE'D : E.map (MulAut.congr e).toMonoidHom ≤ UnitaryHigher.primeFormD h
      ((1 : GL (Fin (l + 1)) K) : Matrix (Fin (l + 1)) (Fin (l + 1)) K) := by
    intro y hy
    obtain ⟨z, hzE, rfl⟩ := Subgroup.mem_map.mp hy
    exact (RecipeFieldSU.mem_recIU_iff h hd1).mp (hErec hzE)
  haveI := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.finite_mulAut_primeFormP h
    ((1 : GL (Fin (l + 1)) K) : Matrix (Fin (l + 1)) (Fin (l + 1)) K)
  have hcyc := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.isCyclic_unitaryD_quotient h hd hne
  have h1 := card_le_mul_card_inf_of_le_cyclic _ _ hcyc hp _ (hEel.map _) hE'D
  rw [Subgroup.card_map_of_injective hinj, ← inner_map_congr e,
    ← Subgroup.map_inf_eq _ _ _ hinj, Subgroup.card_map_of_injective hinj] at h1
  exact h1

section Certificates


private theorem noncyc_inn {lab : GLALabel} (hlab : GLAInLambda2 lab) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : ¬ p ∣ rk2DiagIndex lab) : Rk2LabelAll lab (NoncycProp p) := by
  intro Q hQ
  refine rk2_rawDatum_mono (fun R _ I F h => ⟨h.1, Or.inl fun E hE hEel => ?_⟩)
    (rk2_pSubgroup_le_inn' hlab hp hp2 hpd Q hQ)
  rw [inf_eq_left.2 (h.2 E hE hEel.isPGroup)]
  exact Nat.le_mul_of_pos_left _ hp.pos

private theorem noncyc_E6 {lab : GLALabel} (htag : lab.tag = .E6) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ rk2DiagIndex lab) : Rk2LabelAll lab (NoncycProp p) := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .E6 := htag
  cases ht
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
    (hpd.trans (by simpa [rk2DiagIndex] using Nat.gcd_dvd_left 3 (2 ^ n - 1)))
  subst hp3
  have h3 : 3 ∣ 2 ^ n - 1 :=
    hpd.trans (by simpa [rk2DiagIndex] using Nat.gcd_dvd_right 3 (2 ^ n - 1))
  intro Q hQ
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := TableBExc.recipeChevalleyE6_torusLift_three h3 hQ
  exact ⟨K, i1, i2, hK, hq.1, Or.inr ⟨5, by norm_num, hq.2⟩⟩

private theorem noncyc_twE6 {lab : GLALabel} (hlab : GLAInLambda2 lab) (htag : lab.tag = .twE6)
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ rk2DiagIndex lab) : Rk2LabelAll lab (NoncycProp p) := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .twE6 := htag
  cases ht
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
    (hpd.trans (by simpa [rk2DiagIndex] using Nat.gcd_dvd_left 3 (2 ^ n + 1)))
  subst hp3
  have h3 : 3 ∣ 2 ^ n + 1 :=
    hpd.trans (by simpa [rk2DiagIndex] using Nat.gcd_dvd_right 3 (2 ^ n + 1))
  have hn : 1 ≤ n := by simpa using hlab.1
  intro Q hQ
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  letI : Field K := i1
  letI : Finite K := i2
  exact ⟨K, i1, i2, hK, hq, Or.inr ⟨TwE6Delta.liftRank 3, by simp [TwE6Delta.liftRank],
    ggTorusLift_twE6Add_holds hn hK Nat.prime_three h3⟩⟩

private theorem noncyc_all {lab : GLALabel} (hlab : GLAInLambda2 lab) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : Rk2LabelAll lab (NoncycProp p) := by
  by_cases hpd : p ∣ rk2DiagIndex lab
  · obtain ⟨t, l, n⟩ := lab
    cases t
    case A => exact noncyc_linear rfl hp hp2 hpd
    case twA => exact noncyc_unitary hlab rfl hp
    case E6 => exact noncyc_E6 rfl hp hpd
    case twE6 => exact noncyc_twE6 hlab rfl hp hpd
    all_goals exact absurd hpd hp.not_dvd_one
  · exact noncyc_inn hlab hp hp2 hpd

end Certificates

end Noncyc

open Noncyc in
theorem i173FactNoncyc_holds :
    I173FactNoncyc := by
  intro p Y _ _ S B x hp hp2 _hq _hchev hB hB4 hxB hx1 _hBN hcent hmark
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSperf, lab, hlab, hraw⟩ :=
    rk2_marking_and_labelAll (P' := fun _ => NoncycProp p) (fun lab hlab => noncyc_all hlab hp hp2)
      hmark
  obtain ⟨R, _, I, F, -, -, θ, ⟨hN, hind⟩, hprop⟩ := rk2_rawDatum_exists hraw
  obtain ⟨E, hEle, hEel, hEcard⟩ := exists_elemAbelian_image_of_innerDiag hp hB hB4 hxB hx1 hcent hSperf θ hN hind
  obtain ⟨P, hPp, hPnc⟩ : ∃ P : Subgroup ↥S, IsPGroup p P ∧ ¬ IsCyclic P := by
    rcases hprop with hinn | ⟨r, hr, hT⟩
    ·
      have h1 := hinn E hEle hEel
      have hE₀el : IsElemAbelian p (E ⊓ (MulAut.conj : R →* MulAut R).range) :=
        hEel.mono inf_le_left
      have hE₀card : p ^ 2 ≤ Nat.card ↥(E ⊓ (MulAut.conj : R →* MulAut R).range) := by
        have h2 : p * p ^ 2 ≤ p * Nat.card ↥(E ⊓ (MulAut.conj : R →* MulAut R).range) := by
          calc p * p ^ 2 = p ^ 3 := by ring
            _ ≤ Nat.card E := hEcard
            _ ≤ _ := h1
        exact Nat.le_of_mul_le_mul_left h2 hp.pos
      let π : ↥S →* MulAut R := (MulAut.conj : R →* MulAut R).comp (ggQuotHom θ)
      have hE₀π : E ⊓ (MulAut.conj : R →* MulAut R).range ≤ π.range := by
        intro y hy
        obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 (Subgroup.mem_inf.1 hy).2
        obtain ⟨s, hs⟩ := ggQuotHom_surjective θ r
        exact ⟨s, (congrArg MulAut.conj hs).trans hr⟩
      have hsub := hE₀el.subgroupOf π.range
      refine exists_not_isCyclic_of_surjective hp π.rangeRestrict π.rangeRestrict_surjective
        ((E ⊓ (MulAut.conj : R →* MulAut R).range).subgroupOf π.range) hsub.isPGroup
        (not_isCyclic_of_card hp hsub ?_)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀π).toEquiv]
      exact hE₀card
    ·
      obtain ⟨U, E', -, -, -, hE'el, hE'card, -⟩ :=
        hT ↥S (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hSperf
      refine ⟨E', hE'el.isPGroup, not_isCyclic_of_card hp hE'el ?_⟩
      rw [hE'card]
      exact Nat.pow_le_pow_right hp.pos hr
  refine ⟨P.map S.subtype, Subgroup.map_subtype_le P, hPp.map _, fun hc => hPnc ?_⟩
  exact (Subgroup.equivMapOfInjective P S.subtype S.subtype_injective).isCyclic.mpr hc

end CFSG.LocalAnalysis.GLTheoremA.T173

end
