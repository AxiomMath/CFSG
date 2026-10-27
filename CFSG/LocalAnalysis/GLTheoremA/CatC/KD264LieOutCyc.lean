module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterA
public import CFSG.Walter.Bender1970.S3.TransitivityTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OutCycAt (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ D : Subgroup (MulAut S), IsElemAbelian p D →
    Nat.card D ≤ p * Nat.card ↥(D ⊓ innAutDerived S)

theorem outCycAt_of_mulEquiv {p : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : OutCycAt p S) : OutCycAt p S' := by
  intro D' hD'
  let φ : MulAut S' ≃* MulAut S := MulAut.congr e.symm
  let D : Subgroup (MulAut S) := D'.map φ.toMonoidHom
  have hcard : Nat.card D = Nat.card D' :=
    Subgroup.card_map_of_injective (K := D') φ.injective
  have habel : IsElemAbelian p D := hD'.map φ.toMonoidHom
  have hle := h D habel
  have hmap : (D' ⊓ innAutDerived S').map φ.toMonoidHom = D ⊓ innAutDerived S := by
    rw [Subgroup.map_inf _ _ _ φ.injective]
    rw [show D'.map φ.toMonoidHom = D from rfl]
    rw [show (innAutDerived S').map φ.toMonoidHom = innAutDerived S from
      map_innAutDerived_congr e.symm]
  have hcard2 : Nat.card ↥(D ⊓ innAutDerived S) = Nat.card ↥(D' ⊓ innAutDerived S') := by
    rw [← hmap, Subgroup.card_map_of_injective φ.injective]
  rw [hcard, hcard2] at hle
  exact hle

theorem outCycAt_of_cyclic {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (E : Subgroup (MulAut S)) (hE : ∀ α : MulAut S, α ^ p = 1 → α ∈ E)
    {C : Type*} [Group C] [IsCyclic C] (φ : E →* C)
    (hker : ∀ x : E, φ x = 1 → (x : MulAut S) ^ p = 1 → (x : MulAut S) ∈ innAutDerived S) :
    OutCycAt p S := by
  intro D hD
  have hDE : D ≤ E := fun x hx => hE x (hD.2 x hx)
  let φ' : D →* C := φ.comp (Subgroup.inclusion hDE)
  have hhexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    show ((x : D) : MulAut S) ^ p = 1
    exact hD.2 x x.2)
  have hcard := CFSG.HardMathSupport.Timmesfeld.DefChar.card_le_mul_card_ker hp hhexp φ'
  let ψ : φ'.ker → ↥(D ⊓ innAutDerived S) := fun x =>
    ⟨(x.1 : MulAut S), Subgroup.mem_inf.mpr ⟨x.1.2,
      hker (Subgroup.inclusion hDE x.1) x.2 (by simpa using hD.2 x.1 x.1.2)⟩⟩
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 : ((a.1 : D) : MulAut S) = ((b.1 : D) : MulAut S) :=
      congrArg (fun y : ↥(D ⊓ innAutDerived S) => (y : MulAut S)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hker_le : Nat.card φ'.ker ≤ Nat.card ↥(D ⊓ innAutDerived S) :=
    Nat.card_le_card_of_injective ψ hψ
  calc Nat.card D ≤ p * Nat.card φ'.ker := hcard
    _ ≤ p * Nat.card ↥(D ⊓ innAutDerived S) := Nat.mul_le_mul_left _ hker_le

theorem outCycAt_of_outPChain {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (h : CFSG.RankThree.PartOne.OutStructure.OutPChain p S) : OutCycAt p S := by
  intro D hD
  haveI : ((CFSG.RankThree.PartOne.OutStructure.Inn S).subgroupOf D).Normal := inferInstance
  have hcyc : IsCyclic (D ⧸ (CFSG.RankThree.PartOne.OutStructure.Inn S).subgroupOf D) := by
    classical
    by_cases hDI : D ≤ CFSG.RankThree.PartOne.OutStructure.Inn S
    · haveI : Subsingleton (D ⧸ (CFSG.RankThree.PartOne.OutStructure.Inn S).subgroupOf D) := by
        rw [QuotientGroup.subsingleton_iff]
        exact (Subgroup.subgroupOf_eq_top).mpr hDI
      infer_instance
    · obtain ⟨x, hxD, hxI⟩ := Set.not_subset.mp hDI
      let q : D →* D ⧸ (CFSG.RankThree.PartOne.OutStructure.Inn S).subgroupOf D :=
        QuotientGroup.mk' _
      let xd : D := ⟨x, hxD⟩
      have hxd_ne : q xd ≠ 1 := by
        intro hq
        apply hxI
        have hmem : xd ∈ (CFSG.RankThree.PartOne.OutStructure.Inn S).subgroupOf D :=
          (QuotientGroup.eq_one_iff xd).mp hq
        exact Subgroup.mem_subgroupOf.mp hmem
      have hgen : ∀ zd : D, q zd ∈ Subgroup.zpowers (q xd) := by
        intro zd
        have hcomm : (xd : MulAut S) * (zd : MulAut S) = (zd : MulAut S) * (xd : MulAut S) := by
          simpa using congrArg Subtype.val (hD.1.is_comm.comm xd zd)
        have hxp : (xd : MulAut S) ^ (p ^ 1) ∈ CFSG.RankThree.PartOne.OutStructure.Inn S := by
          rw [pow_one]
          rw [show (xd : MulAut S) ^ p = 1 from hD.2 x hxD]
          exact (CFSG.RankThree.PartOne.OutStructure.Inn S).one_mem
        have hzp : (zd : MulAut S) ^ (p ^ 1) ∈ CFSG.RankThree.PartOne.OutStructure.Inn S := by
          rw [pow_one]
          rw [show (zd : MulAut S) ^ p = 1 from hD.2 zd zd.2]
          exact (CFSG.RankThree.PartOne.OutStructure.Inn S).one_mem
        rcases CFSG.RankThree.PartOne.OutStructure.OutPChain.comparable h hcomm hxp hzp with
          ⟨m, hm⟩ | ⟨m, hm⟩
        · have hmem : xd * zd ^ m ∈ (CFSG.RankThree.PartOne.OutStructure.Inn S).subgroupOf D := by
            rw [Subgroup.mem_subgroupOf]
            simpa using hm
          have hq1 : q xd * (q zd) ^ m = 1 := by
            rw [← map_zpow, ← map_mul]
            exact (QuotientGroup.eq_one_iff (xd * zd ^ m)).mpr hmem
          have hzpow : (q zd) ^ m = (q xd)⁻¹ := eq_inv_of_mul_eq_one_right hq1
          have hzdp : (q zd) ^ p = 1 := by
            rw [← map_pow]
            have h1 : zd ^ p = 1 := by
              apply Subtype.ext
              simpa using hD.2 zd zd.2
            rw [h1, map_one]
          have hnotdvd : ¬ (p : ℤ) ∣ m := by
            intro hdvd
            obtain ⟨k, hk⟩ := hdvd
            have h1 : (q zd) ^ m = 1 := by
              rw [hk, zpow_mul, zpow_natCast, hzdp, one_zpow]
            have h2 : (q xd)⁻¹ = 1 := by rw [← hzpow, h1]
            exact hxd_ne (inv_eq_one.mp h2)
          have hα : (q zd) ^ p ∈ Subgroup.zpowers (q xd) := by
            rw [hzdp]
            exact Subgroup.one_mem _
          have h1 : (q zd) ^ m ∈ Subgroup.zpowers (q xd) := by
            rw [hzpow]
            exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
          exact CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_not_dvd
            (I := Subgroup.zpowers (q xd)) hp hα h1 hnotdvd
        · have hmem : zd * xd ^ m ∈ (CFSG.RankThree.PartOne.OutStructure.Inn S).subgroupOf D := by
            rw [Subgroup.mem_subgroupOf]
            simpa using hm
          have hq1 : q zd * (q xd) ^ m = 1 := by
            rw [← map_zpow, ← map_mul]
            exact (QuotientGroup.eq_one_iff (zd * xd ^ m)).mpr hmem
          have hzbar : q zd = (q xd) ^ (-m) := by
            rw [zpow_neg]
            exact eq_inv_of_mul_eq_one_left hq1
          exact Subgroup.mem_zpowers_iff.mpr ⟨-m, hzbar.symm⟩
      have htop : Subgroup.zpowers (q xd) = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective
          (N := (CFSG.RankThree.PartOne.OutStructure.Inn S).subgroupOf D) y
        exact hgen z
      exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨q xd, htop⟩
  have hcard : Nat.card D ≤ p * Nat.card ↥(D ⊓ CFSG.RankThree.PartOne.OutStructure.Inn S) :=
    CFSG.Walter.card_le_mul_card_inf_of_isCyclic (U := D)
      (C := CFSG.RankThree.PartOne.OutStructure.Inn S) (V := D) hcyc le_rfl hp hD.2
  refine hcard.trans (Nat.mul_le_mul_left _ ?_)
  exact Nat.card_mono (Set.toFinite _) (by
    intro y hy
    exact inf_le_inf_left _ (inner_le_innAutDerived S) hy)

@[expose] def LieOutCyc (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic → P d.1 →
    OutCycAt p (TauCeti.CFSGIndex.lie d).Group

theorem kd264OutCyc_of_families (h1 : LieOutCyc isLinearIdx) (h2 : LieOutCyc isUnitaryIdx)
    (h3 : LieOutCyc isClassicalBCDIdx) (h4 : LieOutCyc isTrialityIdx)
    (h5 : LieOutCyc isExcUntwistedIdx) (h6 : LieOutCyc isExcTwistedIdx) : KD264OutCyc := by
  intro d p hp hp2 hpc D hD
  obtain ⟨e, hd⟩ := d
  cases e with
  | A n q => exact h1 ⟨.A n q, hd⟩ p hp hp2 hpc trivial D hD
  | twistedA n q => exact h2 ⟨.twistedA n q, hd⟩ p hp hp2 hpc trivial D hD
  | B n q => exact h3 ⟨.B n q, hd⟩ p hp hp2 hpc trivial D hD
  | C n q => exact h3 ⟨.C n q, hd⟩ p hp hp2 hpc trivial D hD
  | D n q => exact h3 ⟨.D n q, hd⟩ p hp hp2 hpc trivial D hD
  | twistedD n q => exact h3 ⟨.twistedD n q, hd⟩ p hp hp2 hpc trivial D hD
  | E6 q => exact h5 ⟨.E6 q, hd⟩ p hp hp2 hpc trivial D hD
  | E7 q => exact h5 ⟨.E7 q, hd⟩ p hp hp2 hpc trivial D hD
  | E8 q => exact h5 ⟨.E8 q, hd⟩ p hp hp2 hpc trivial D hD
  | F4 q => exact h5 ⟨.F4 q, hd⟩ p hp hp2 hpc trivial D hD
  | G2 q => exact h5 ⟨.G2 q, hd⟩ p hp hp2 hpc trivial D hD
  | twistedE6 q => exact h6 ⟨.twistedE6 q, hd⟩ p hp hp2 hpc trivial D hD
  | trialityD4 q => exact h4 ⟨.trialityD4 q, hd⟩ p hp hp2 hpc trivial D hD
  | suzuki k => exact h6 ⟨.suzuki k, hd⟩ p hp hp2 hpc trivial D hD
  | reeG2 k => exact h6 ⟨.reeG2 k, hd⟩ p hp hp2 hpc trivial D hD
  | reeF4 k => exact h6 ⟨.reeF4 k, hd⟩ p hp hp2 hpc trivial D hD
  | tits => exact h6 ⟨.tits, hd⟩ p hp hp2 hpc trivial D hD

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
