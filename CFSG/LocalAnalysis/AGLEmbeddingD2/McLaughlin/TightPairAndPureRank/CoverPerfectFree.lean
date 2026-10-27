module

public import CFSG.GroupTheory.SteinbergCBFTPSolvable
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.SteinbergCBFTSCN
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.HallHigman CFSG.Open CFSG.GroupTheory.FT63ChII
open scoped commutatorElement

theorem isCyclic_map {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    [IsCyclic K] : IsCyclic (K.map f) := by
  have h : IsCyclic (f.comp K.subtype).range :=
    isCyclic_of_surjective (f.comp K.subtype).rangeRestrict (f.comp K.subtype).rangeRestrict_surjective
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h

theorem false_of_perfect_pSolvable_cyclicSylow {V : Type*} [Group V] [Finite V]
    (hperf : ⁅(⊤ : Subgroup V), (⊤ : Subgroup V)⁆ = ⊤) (h3 : 3 ∣ Nat.card V)
    (hsolv : IsPSolvable 3 V) (hcyc : ∀ P : Sylow 3 V, IsCyclic (P : Subgroup V)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup V := CFSG.pPrimeCore 3 V with hN
  haveI : N.Normal := CFSG.pPrimeCore_normal
  set Vb := V ⧸ N with hVb
  have hsolvb : IsPSolvable 3 Vb :=
    isPSolvable_of_isPiSeparable
      ((isPiSeparable_of_isPSolvable Nat.prime_three hsolv).quotient N)
  have hcoreb : CFSG.pPrimeCore 3 Vb = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hchar := isCharacteristicP_of_isPSolvable hsolvb hcoreb
  set Q : Subgroup Vb := CFSG.pCore 3 Vb with hQ
  haveI hQn : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup 3 Q := CFSG.pCore_isPGroup
  have hQcyc : IsCyclic Q := by
    obtain ⟨P₀⟩ : Nonempty (Sylow 3 V) := inferInstance
    have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
    set P₁ : Sylow 3 Vb := P₀.mapSurjective hsurj with hP₁
    have hP₁c : (P₁ : Subgroup Vb) = (P₀ : Subgroup V).map (QuotientGroup.mk' N) := by
      rw [hP₁, Sylow.coe_mapSurjective]
    have hcP₁ : IsCyclic (P₁ : Subgroup Vb) := by
      rw [hP₁c]
      haveI := hcyc P₀
      exact isCyclic_map (QuotientGroup.mk' N) (P₀ : Subgroup V)
    exact Subgroup.isCyclic_of_le (hQp.le_sylow_of_normal P₁)
  have hperfb : ⁅(⊤ : Subgroup Vb), (⊤ : Subgroup Vb)⁆ = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hperf
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      at h
    exact h
  have hMulComm : ∀ f g : MulAut Q, f * g = g * f := fun f g =>
    (IsCyclic.mulAutMulEquiv Q).injective (by rw [map_mul, map_mul, mul_comm])
  have hcomm : ∀ a b : Vb, ⁅a, b⁆ ∈ Q := by
    intro a b
    refine hchar ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : (MulAut.conjNormal (H := Q) ⁅a, b⁆) = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hMulComm _ _)
    have h2 := congrArg (fun f : MulAut Q => (f ⟨q, hq⟩ : Q).1) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hQtop : Q = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hperfb]
    exact Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
  have hVbcyc : IsCyclic Vb := by
    haveI : IsCyclic (⊤ : Subgroup Vb) := hQtop ▸ hQcyc
    exact isCyclic_of_surjective (⊤ : Subgroup Vb).subtype
      (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)
  have hVbtriv : (⊤ : Subgroup Vb) = ⊥ := by
    rw [← hperfb, eq_bot_iff]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact IsCyclic.commGroup.mul_comm a b
  have hcardVb : Nat.card Vb = 1 := by
    rw [← Subgroup.card_top (G := Vb), hVbtriv, Subgroup.card_bot]
  have hcard : Nat.card V = Nat.card N := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardVb, one_mul] at this
    exact this
  have hcop : Nat.Coprime 3 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have := Nat.Coprime.eq_one_of_dvd hcop (hcard ▸ h3)
  omega

theorem perfectFree_of_pSolvable_pRank_le_one {W : Type*} [Group W] [Finite W] {A : Subgroup W}
    (hs : IsPSolvable 3 ↥A) (hr : Open.pRank 3 A ≤ 1) {V : Subgroup W} (hVA : V ≤ A)
    (hV : ⁅V, V⁆ = V) : ¬ 3 ∣ Nat.card V := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ = ⊤ := by
    apply Subgroup.map_injective V.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hV
  have hsolv : IsPSolvable 3 ↥V :=
    isPSolvable_of_isPiSeparable
      (isPiSeparable_of_le hVA (isPiSeparable_of_isPSolvable Nat.prime_three hs))
  have hr' : CFSG.pRank 3 ↥A ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hr
  refine false_of_perfect_pSolvable_cyclicSylow hperf h3 hsolv fun P => ?_
  have hP3 : IsPGroup 3 ((P : Subgroup ↥V).map V.subtype) := P.isPGroup'.map V.subtype
  have hc := CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
    (L := A) (S := (P : Subgroup ↥V).map V.subtype)
    (by rintro _ ⟨x, -, rfl⟩; exact hVA x.2) hP3 hr'
  exact isCyclic_of_surjective
    ((Subgroup.equivMapOfInjective (P : Subgroup ↥V) V.subtype V.subtype_injective).symm.toMonoidHom)
    (Subgroup.equivMapOfInjective (P : Subgroup ↥V) V.subtype V.subtype_injective).symm.surjective

theorem false_of_lift_elemAbelian {X Y : Type*} [Group X] [Finite X] [Group Y] (ψ : X →* Y)
    (hr : Open.pRank 3 (⊤ : Subgroup X) ≤ 1) {E : Subgroup Y} (hE : E ≤ ψ.range)
    (hel : IsElemAbelian 3 E) (hcard : Nat.card E = 9) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Et : Subgroup X := E.comap ψ with hEt
  let ψ' : ↥Et →* ↥E := (ψ.comp Et.subtype).codRestrict E fun x => x.2
  have hψ' : Function.Surjective ψ' := by
    intro y
    obtain ⟨x, hx⟩ := hE y.2
    exact ⟨⟨x, by simp [hEt, hx]⟩, Subtype.ext hx⟩
  haveI : Finite E := Finite.of_surjective ψ' hψ'
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥Et) := inferInstance
  set P₁ : Sylow 3 ↥E := P.mapSurjective hψ' with hP₁
  have hP₁c : (P₁ : Subgroup ↥E) = (P : Subgroup ↥Et).map ψ' := by
    rw [hP₁, Sylow.coe_mapSurjective]
  have hP₁top : (P₁ : Subgroup ↥E) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Sylow.card_eq_multiplicity, hcard, show (9 : ℕ) = 3 ^ 2 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hRp : IsPGroup 3 (((P : Subgroup ↥Et).map Et.subtype)) := P.isPGroup'.map Et.subtype
  have hRc := CFSG.RankThree.PartTwo.Sec20.Res5.isCyclic_of_pRank_le_one hr hRp
  have hPc : IsCyclic (P : Subgroup ↥Et) :=
    isCyclic_of_surjective
      ((Subgroup.equivMapOfInjective (P : Subgroup ↥Et) Et.subtype Et.subtype_injective).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective (P : Subgroup ↥Et) Et.subtype Et.subtype_injective).symm.surjective
  have hmc : IsCyclic ((P : Subgroup ↥Et).map ψ') := isCyclic_map ψ' _
  rw [← hP₁c, hP₁top] at hmc
  haveI : IsCyclic ↥E := isCyclic_of_surjective (⊤ : Subgroup ↥E).subtype
    (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
  have h1 : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ 3 = 1 := Subtype.ext (hel.2 g g.2)
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [h1, hcard] at h3
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
