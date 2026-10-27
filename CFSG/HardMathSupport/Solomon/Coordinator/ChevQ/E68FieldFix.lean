module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318E68
public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Index
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FixedGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)

namespace E68FieldFixAux

theorem center_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hc : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [hH, Subgroup.mem_bot] at hc
  exact e.injective (by rw [hc, map_one])

theorem fixed_map_congr {G H : Type} [Group G] [Group H] (e : G ≃* H) (α : MulAut G) :
    (fixedSubgroup α).map e.toMonoidHom = fixedSubgroup (MulAut.congr e α) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixedSubgroup] at hx ⊢
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.coe_toMonoidHom, hx]
  · intro hy
    rw [mem_fixedSubgroup] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixedSubgroup]
    apply e.injective
    simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hy

theorem fixed_map_conj {G : Type} [Group G] (ψ γ : MulAut G) :
    (fixedSubgroup γ).map ψ.toMonoidHom = fixedSubgroup (ψ * γ * ψ⁻¹) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixedSubgroup] at hx
    rw [mem_fixedSubgroup, MulAut.mul_apply, MulAut.mul_apply, MulEquiv.coe_toMonoidHom]
    simp [hx]
  · intro hy
    rw [mem_fixedSubgroup, MulAut.mul_apply, MulAut.mul_apply] at hy
    refine ⟨ψ⁻¹ y, ?_, by simp⟩
    rw [mem_fixedSubgroup]
    apply ψ.injective
    rw [hy]
    simp

theorem congr_eq_conj_imp {K C : Type} [Group K] [Group C] (e : K ≃* C) (α : MulAut K) (g : C)
    (h : MulAut.congr e α = MulAut.conj g) : α = MulAut.conj (e.symm g) := by
  refine MulEquiv.ext fun k => ?_
  apply e.injective
  have hk := congrArg (fun φ : MulAut C => φ (e k)) h
  simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.symm_apply_apply] at hk
  rw [MulAut.conj_apply, map_mul, map_mul]
  simp only [MulEquiv.apply_symm_apply, map_inv]
  rw [← hk]
  simp

theorem fixedSubgroup_le_pow {G : Type*} [Group G] (α : MulAut G) (n : ℕ) :
    fixedSubgroup α ≤ fixedSubgroup (α ^ n) := by
  intro x hx
  have hfix : α x = x := hx
  show (α ^ n) x = x
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, hfix]
    exact ih

theorem fixedSubgroup_pow_eq {G : Type*} [Group G] {α : MulAut G} {r j : ℕ}
    (hαr : (α ^ r) ^ j = α) : fixedSubgroup α = fixedSubgroup (α ^ r) :=
  le_antisymm (fixedSubgroup_le_pow α r) (by
    have := fixedSubgroup_le_pow (α ^ r) j
    rwa [hαr] at this)

end E68FieldFixAux

set_option linter.unusedSectionVars false


namespace E68FieldFixAux

theorem entrywiseFixedGroup_E6_eq_of_card_two {M : Type} [Field M] [Finite M] (σ : M ≃+* M)
    (h2 : Nat.card (fixSubfield σ) = 2) :
    entrywiseFixedGroup Tag.E6 σ = fixedFieldImage Tag.E6 σ := by
  refine le_antisymm ?_ fixedFieldImage_le
  obtain ⟨-, h⟩ := fixedFieldImage_index_dvd_card (τ := Tag.E6) σ
  rw [h2] at h
  have h1 : ((fixedFieldImage Tag.E6 σ).subgroupOf (entrywiseFixedGroup Tag.E6 σ)).index = 1 := by
    have h' : (2 - 1 : ℕ) ^ Tag.E6.rank = 1 := by simp
    rw [h'] at h
    exact Nat.dvd_one.1 h
  rw [Subgroup.index_eq_one] at h1
  intro g hg
  have hmem : (⟨g, hg⟩ : entrywiseFixedGroup Tag.E6 σ) ∈
      (fixedFieldImage Tag.E6 σ).subgroupOf (entrywiseFixedGroup Tag.E6 σ) := by
    rw [h1]
    exact Subgroup.mem_top _
  exact hmem

theorem exists_fixed_equiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    (β : MulAut ↥(adjointGroup Tag.E6 K)) (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ (MulAut.conj : ↥(adjointGroup Tag.E6 K) →*
      MulAut ↥(adjointGroup Tag.E6 K)).range) :
    ∃ T : K ≃+* K, Nat.card (fixSubfield T) = 2 ∧
      Nonempty (↥(fixedSubgroup β) ≃* ↥(adjointGroup Tag.E6 (fixSubfield T))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, T, r, j, ψ, hd, -, hTcard, -, -, hβr, hψ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag Tag.E6
      (Or.inl rfl) (ℓ := 2) (f := 3) (p := 3) (by norm_num) K hK Nat.prime_three (by norm_num) β hβ3
      (fun g a h => by
        obtain ⟨-, h7⟩ := CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner Tag.E6
          (Or.inl rfl) K Nat.prime_three g a β h hβ3 hβout
        rw [hK] at h7
        norm_num at h7)
  have hd1 : d = 1 := by omega
  subst hd1
  have h2 : Nat.card (fixSubfield T) = 2 := by rw [hTcard]; norm_num
  have hΓJ := entrywiseFixedGroup_E6_eq_of_card_two T h2
  refine ⟨T, h2, ⟨?_⟩⟩
  have hfix : fixedSubgroup β = fixedSubgroup (β ^ r) := fixedSubgroup_pow_eq hβr
  have E2 : ↥(fixedSubgroup β) ≃* ↥(fixedSubgroup (entrywiseAdjointAut Tag.E6 T)) :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr ((congrArg (Subgroup.map ψ.toMonoidHom) hfix).trans
        ((fixed_map_conj ψ (β ^ r)).trans (congrArg fixedSubgroup hψ))))
  exact E2.trans (CFSG.LieType.SeitzGeneration.ExcOuterLeOne.fixedEquivOfEq (τ := Tag.E6) T hΓJ)

end E68FieldFixAux

theorem e68FieldFix_holds : Gen2318E68Aux.E68FieldFix := by
  classical
  intro S _ _ d hd hS β hβ3 hβout
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | E6 q =>
    obtain ⟨hq2, hqe⟩ := hd
    obtain ⟨e⟩ := hS
    have hKcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
    have hqcard : q.card = 2 ^ 3 := by
      rw [TauCeti.PrimePower.card_def, hq2, hqe]
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq2 (GaloisField 2 3)
      (hKcard.trans hqcard.symm)
    let eG : S ≃* ↥(adjointGroup Tag.E6 (GaloisField 2 3)) :=
      (e.trans eB.symm).trans
        (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv Tag.E6 (GaloisField 2 3))
    have hβ'3 : MulAut.congr eG β ^ 3 = 1 := by
      rw [← map_pow, hβ3, map_one]
    have hβ'out : MulAut.congr eG β ∉ (MulAut.conj : ↥(adjointGroup Tag.E6 (GaloisField 2 3)) →*
        MulAut ↥(adjointGroup Tag.E6 (GaloisField 2 3))).range := by
      rintro ⟨g, hg⟩
      exact hβout ⟨eG.symm g, (E68FieldFixAux.congr_eq_conj_imp eG β g hg.symm).symm⟩
    obtain ⟨T, hT2, ⟨F⟩⟩ := E68FieldFixAux.exists_fixed_equiv hKcard _ hβ'3 hβ'out
    have E1 : ↥(fixedSubgroup β) ≃* ↥(fixedSubgroup (MulAut.congr eG β)) :=
      (Subgroup.equivMapOfInjective _ eG.toMonoidHom eG.injective).trans
        (MulEquiv.subgroupCongr (E68FieldFixAux.fixed_map_congr eG β))
    let Ffix : ↥(fixedSubgroup β) ≃* ↥(adjointGroup Tag.E6 (fixSubfield T)) := E1.trans F
    have hq6 : CFSG.IsQuasisimple ↥(adjointGroup Tag.E6 (fixSubfield T)) :=
      CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 (fixSubfield T)
    have hZ6 : Subgroup.center ↥(adjointGroup Tag.E6 (fixSubfield T)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hsimple6 : IsSimpleGroup ↥(adjointGroup Tag.E6 (fixSubfield T)) :=
      CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq6
        ((QuotientGroup.quotientMulEquivOfEq hZ6).trans QuotientGroup.quotientBot).symm
    have hsimpleH : IsSimpleGroup ↥(fixedSubgroup β) :=
      (MulEquiv.isSimpleGroup_congr Ffix).2 hsimple6
    have hperfH : Group.IsPerfect ↥(fixedSubgroup β) :=
      haveI := hq6.1
      Group.IsPerfect.ofSurjective (f := Ffix.symm.toMonoidHom) Ffix.symm.surjective
    have hZH : Subgroup.center ↥(fixedSubgroup β) = ⊥ :=
      E68FieldFixAux.center_eq_bot_of_mulEquiv Ffix hZ6
    let q₀ : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
    have hv₀ : (TauCeti.LieTypeIndex.E6 q₀).Valid := TauCeti.LieTypeIndex.valid_E6 q₀
    have hcard₀ : Nat.card ↥(fixSubfield T) = q₀.card := by
      rw [hT2, TauCeti.PrimePower.card_def]
      rfl
    obtain ⟨eB0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q₀ hv₀ rfl (fixSubfield T) hcard₀
    let eFix : ↥(fixedSubgroup β) ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E6 q₀, hv₀⟩).Group :=
      Ffix.trans
        ((CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv Tag.E6
          (fixSubfield T)).symm.trans eB0)
    refine ⟨fixedSubgroup β, fun s => mem_fixedSubgroup, hZH, ⟨hperfH.commutator_eq_top, ?_⟩,
      ⟨TauCeti.LieTypeIndex.E6 q₀, hv₀⟩, ⟨rfl, rfl⟩, ⟨eFix⟩⟩
    exact (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hZH).trans
      QuotientGroup.quotientBot)).2 hsimpleH
  | _ => exact absurd hd (by simp [IsE6EightIndex])

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
