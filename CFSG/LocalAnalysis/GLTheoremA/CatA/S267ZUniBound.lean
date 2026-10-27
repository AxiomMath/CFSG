module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCyc
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux2
import CFSG.GH74.Uniqueness.SU.SU7Gen3
import CFSG.RankThree.PartOne.KF.F128SU
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {ℓ f : ℕ} {K : Type} [Field K]

noncomputable abbrev innDiag (h : UnitaryFieldData ℓ f K) : Subgroup (MulAut (PU h)) :=
  primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

noncomputable abbrev fieldFactor (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) :
    MulAut (PU h) →* (K ≃+* K) :=
  primeFormFieldFactor h (isPrimeFormGram_one (n := 3)) (le_refl 3)
    (not_three_two_of_ne_two h.prime hℓ)

theorem ker_fieldFactor (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) :
    (fieldFactor h hℓ).ker = innDiag h :=
  ker_primeFormFieldFactor h _ _ _

theorem ker_primeFormConjHom (h : UnitaryFieldData ℓ f K) :
    (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).ker =
      (StatedScalars (Fin 3) K).subgroupOf
        (primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  ext A
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have key := primeFormPsi_eq_one_iff h (isPrimeFormGram_one (n := 3)) (le_refl 3) ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at key
  rw [key]
  constructor
  · rintro ⟨-, c, -, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨rfl, c, ?_, hc.symm⟩
    exact norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num) 1 (hc ▸ A.2)

noncomputable def statedProjEquivInnDiag (h : UnitaryFieldData ℓ f K) :
    StatedProj (primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ≃*
      (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_primeFormConjHom h).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem isElemAbelian_inf_left {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (H : Subgroup G) : IsElemAbelian p (E ⊓ H) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x hx.1⟩
  have hc := hE.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩
  have hc' : (a : G) * b = b * a := congrArg (Subtype.val : E → G) hc
  exact Subtype.ext hc'

theorem card_inf_innDiag_le [Finite K] (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (PU h))} (hE : IsElemAbelian p E) :
    Nat.card ↥(E ⊓ innDiag h) ≤ p ^ 2 := by
  haveI : CharP K ℓ := h.charP
  have hF : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K ℓ] at h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).1 h0).symm
  set c := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  set e := statedProjEquivInnDiag h
  let ι : StatedProj (primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) →*
      MulAut (PU h) := c.range.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := c.range.subtype_injective.comp e.injective
  have hrange : innDiag h ≤ ι.range := by
    intro y hy
    refine ⟨e.symm ⟨y, hy⟩, ?_⟩
    change ((e (e.symm ⟨y, hy⟩) : c.range) : MulAut (PU h)) = y
    rw [MulEquiv.apply_symm_apply]
  set W := (E ⊓ innDiag h).comap ι
  have hWmap : W.map ι = E ⊓ innDiag h := Subgroup.map_comap_eq_self (inf_le_right.trans hrange)
  have hW : IsElemAbelian p W := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff hι p W, hWmap]
    exact isElemAbelian_inf_left hE _
  have hcard : Nat.card W = Nat.card ↥(E ⊓ innDiag h) := by
    rw [← hWmap, Subgroup.card_map_of_injective hι]
  have := card_le_pow_statedProj hp hp2 hF (by norm_num : 0 < 3) _ W hW
  rwa [hcard] at this

private theorem finite_ringEquiv [Finite K] : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) fun _ _ hσ =>
    RingEquiv.ext (congrFun hσ)

theorem card_map_fieldFactor_le [Finite K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) {p : ℕ}
    (hp : p.Prime) {E : Subgroup (MulAut (PU h))} (hE : IsElemAbelian p E) :
    Nat.card ↥(E.map (fieldFactor h hℓ)) ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := CFSG.LocalAnalysis.GLTheoremA.FP.isCyclic_ringEquiv K
  haveI : Finite (K ≃+* K) := finite_ringEquiv
  refine CFSG.AGLEmbedding.card_le_of_isCyclic_of_pow_eq_one _ ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, hE.2 a ha, map_one]

theorem card_le_pow_three [Finite K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (PU h))}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have h1 := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker (fieldFactor h hℓ) E
  rw [ker_fieldFactor] at h1
  rw [← h1, pow_succ']
  exact Nat.mul_le_mul (card_map_fieldFactor_le h hℓ hp hE) (card_inf_innDiag_le h hp hp2 hpℓ hE)

theorem dvd_add_one_of_le_card_inf_innDiag [Finite K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (PU h))}
    (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card ↥(E ⊓ innDiag h)) :
    p ∣ ℓ ^ f + 1 := by
  by_contra hnd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  set W := E ⊓ innDiag h with hWdef
  have hWel : IsElemAbelian p W := isElemAbelian_inf_left hE _
  have hWcard : Nat.card W = p ^ 2 := le_antisymm (card_inf_innDiag_le h hp hp2 hpℓ hE) hcard
  have hcop : Nat.Coprime p (ℓ ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  have hWinn : W ≤ inner (PU h) := by
    intro x hx
    have hq := card_primeFormD_quotient_dvd h (1 : GL (Fin 3) K)
    let y : ↥(innDiag h) ⧸ (inner (PU h)).subgroupOf (innDiag h) :=
      QuotientGroup.mk (⟨x, hx.2⟩ : innDiag h)
    have hy1 : y ^ p = 1 := by
      change QuotientGroup.mk ((⟨x, hx.2⟩ : innDiag h) ^ p) = _
      have hxp : (⟨x, hx.2⟩ : innDiag h) ^ p = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hE.2 x hx.1)
      rw [hxp, QuotientGroup.mk_one]
    have hy2 : y ^ Nat.card (↥(innDiag h) ⧸ (inner (PU h)).subgroupOf (innDiag h)) = 1 :=
      pow_card_eq_one'
    have hc : Nat.Coprime p (Nat.card (↥(innDiag h) ⧸ (inner (PU h)).subgroupOf (innDiag h))) :=
      Nat.Coprime.coprime_dvd_right hq hcop
    have hy : y = 1 := by
      have := (pow_gcd_eq_one (a := y)).2 ⟨hy1, hy2⟩
      rwa [hc, pow_one] at this
    have hmem := (QuotientGroup.eq_one_iff _).1 hy
    rwa [Subgroup.mem_subgroupOf] at hmem
  have hconj : Function.Injective (MulAut.conj : PU h →* MulAut (PU h)) :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_conj_inj_of_center_bot (center_PU_eq_bot h hℓ)
  set W' := W.comap (MulAut.conj : PU h →* MulAut (PU h))
  have hW'map : W'.map (MulAut.conj : PU h →* MulAut (PU h)) = W :=
    Subgroup.map_comap_eq_self hWinn
  have hW'el : IsElemAbelian p W' := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff hconj p W', hW'map]
    exact hWel
  have hW'card : Nat.card W' = p ^ 2 := by
    rw [← hWcard, ← hW'map, Subgroup.card_map_of_injective hconj]
  have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (PU h)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hW'el hW'card
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hpq : ¬ p ∣ ℓ ^ f := fun hd => hpℓ
    ((Nat.prime_dvd_prime_iff_eq hp h.prime).1 (hp.dvd_of_dvd_pow hd))
  have hN : ¬ p ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (ℓ ^ f) K)) := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel h.prime hK (by norm_num)).2.2]
    exact fun hd => hnd (hd.trans (Nat.gcd_dvd_right 3 _))
  have h3 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSU 3 (ℓ ^ f) K)) := by
    rw [← CFSG.SectionRank.pRank_quotient_eq _ hN,
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (PUEquivStated h)]
    exact h2
  have hQ0 : (-((ℓ ^ f : ℕ) : ZMod p)) ≠ 0 := by
    rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    exact hpq
  have he0 : 0 < orderOf (-((ℓ ^ f : ℕ) : ZMod p)) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hQ0⟩)
  have he1 : orderOf (-((ℓ ^ f : ℕ) : ZMod p)) ≠ 1 := fun h1 => hnd (by
    have : (-((ℓ ^ f : ℕ) : ZMod p)) = 1 := orderOf_eq_one_iff.1 h1
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast at this ⊢
    linear_combination -this)
  have hcond : 3 / orderOf (-((ℓ ^ f : ℕ) : ZMod p)) ≤ 1 :=
    Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul he0).2 (by omega))
  have h1 := CFSG.RankThree.PartOne.pRank_statedSU_le_one (n := 3) hp hp2 hK hpq (by norm_num)
    hcond
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
  omega

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
