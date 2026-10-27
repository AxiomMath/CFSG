module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.CentralLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLChev
public import CFSG.Quasithin.EmptyFaithful.R3c21A

public section

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding TauCeti CFSG.Adapters.RankTwoModelTransports

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

theorem isClassicalTwoOrG2_of_statedPSU {G : Type} [Group G] {k f : ℕ}
    (h : StatedClassicalModel G .PSU k 2 f) (hk : 3 ≤ k) (hkq : (k, 2 ^ f) ≠ (3, 2)) :
    IsClassicalTwoOrG2 G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  let q : PrimePower := ⟨2, f, hadm.1, by have := hadm.2.1; omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hv : (LieTypeIndex.twistedA r q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by omega, fun h2 => ?_⟩, fun h => h⟩
    simp only [PrimePower.card_def, q]
    have hf2 : f ≠ 1 := by
      rintro rfl
      exact hkq (by rw [h2]; rfl)
    have hf1 := hadm.2.1
    have : 2 ≤ f := by omega
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
  have hdq : IsClassicalOrG2Index (LieTypeIndex.twistedA r q) := rfl
  let L := GaloisField 2 (2 * f)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLcard : Nat.card L = Nat.card K := by
    have h2f : 2 * f ≠ 0 := by have := hadm.2.1; omega
    rw [hK, GaloisField.card 2 (2 * f) h2f, ← pow_mul, mul_comm]
  let φ : K ≃+* L := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard hLcard.symm
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := by
    simp [ValidLieTypeIndex.characteristic, q]
  have he : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = f := by
    simp [ValidLieTypeIndex.fieldExponent, q]
  have key : ∀ (c e : ℕ) (_ : Fact c.Prime), c = 2 → e = f →
      StatedProj (StatedSU (r + 1) (c ^ e) (GaloisField c (2 * e)))
      ≃* StatedProj (StatedSU (r + 1) (2 ^ f) (GaloisField 2 (2 * f))) := by
    intro c e _ hc he
    subst hc he
    exact MulEquiv.refl _
  let eT := (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv).trans
    (key _ _ _ hc he)
  exact Or.inl ⟨⟨.twistedA r q, hv⟩, hdq, ⟨(θ.trans (statedProjCongr (glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ (r + 1) (2 ^ f))
    (glCongr_statedScalars φ))).trans eT.symm⟩⟩


section SUModels

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.Quasithin.SmithC27

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

include hF

theorem one_le_f : 1 ≤ f := by
  by_contra h
  have hf : f = 0 := by omega
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF, hf] at h1
  norm_num at h1

theorem isChevComponent_su {n' : ℕ} (hn : 3 ≤ n') (hnq : (n', 2 ^ f) ≠ (3, 2)) :
    CFSG.IsQuasisimple (SU (unitaryInvolution F 2 f) n') ∧
      IsClassicalTwoOrG2 (SU (unitaryInvolution F 2 f) n' ⧸
        Subgroup.center (SU (unitaryInvolution F 2 f) n')) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSU n' 2 f := ⟨Nat.prime_two, one_le_f hF, hn, hnq⟩
  exact ⟨isQuasisimple_SU hF hn hnq, isClassicalTwoOrG2_of_statedPSU
    (statedClassicalModel_center_quotient hadm hF) hn hnq⟩


theorem su_two_chev (hf : 2 ≤ f) :
    CFSG.IsQuasisimple (SU (unitaryInvolution F 2 f) 2) ∧
      IsClassicalTwoOrG2 (SU (unitaryInvolution F 2 f) 2 ⧸
        Subgroup.center (SU (unitaryInvolution F 2 f) 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  have hq : Nat.card (fixedSubfield F 2 f) = 2 ^ f := card_fixedSubfield hF
  have h4 : 4 ≤ Nat.card (fixedSubfield F 2 f) := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨h1, h2⟩ := isChevComponent_sl (F := fixedSubfield F 2 f) (k := 2) (Or.inr ⟨rfl, h4⟩)
  let e := hypEquiv hζ0 hζ
  exact ⟨isQuasisimple_of_mulEquiv e h1, isClassicalTwoOrG2_of_mulEquiv (quotCenterCongr e) h2⟩

theorem su_two_solvable (hf : f = 1) : Group.IsSolvable (SU (unitaryInvolution F 2 f) 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  have hq : Nat.card (fixedSubfield F 2 f) = 2 ^ f := card_fixedSubfield hF
  have : Fintype (fixedSubfield F 2 f) := Fintype.ofFinite _
  have hcard : Fintype.card (fixedSubfield F 2 f) = 2 := by
    rw [← Nat.card_eq_fintype_card, hq, hf]; norm_num
  have hs : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f)) :=
    CFSG.Quasithin.R3c21.S0.isSolvable_sl2_of_card_two hcard
  let e := hypEquiv hζ0 hζ
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem su_three_solvable (hf : f = 1) : Group.IsSolvable (SU (unitaryInvolution F 2 f) 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hf
  have hs := CFSG.Quasithin.isSolvable_statedSU_one (F := F) hF
  let e := equivStatedSU hF 3
  exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ e.toMonoidHom e.injective hs

end SUModels


section CentralMap

open CFSG.LieType.CurtisTits

theorem chev_map_of_central_kernel {K Y : Type} [Group K] [Group Y] (π : K →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center K) {C : Subgroup K} {M : Type} [Group M]
    (e : M ≃* ↥C) (h : CFSG.IsQuasisimple M ∧ IsClassicalTwoOrG2 (M ⧸ Subgroup.center M)) :
    CFSG.IsQuasisimple ↥(C.map π) ∧
      IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π)) := by
  let ψ : M →* ↥(C.map π) := MonoidHom.codRestrict (π.comp (C.subtype.comp e.toMonoidHom))
    (C.map π) (fun x => ⟨(e x : K), (e x).2, rfl⟩)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨y, c, hc, rfl⟩
    exact ⟨e.symm ⟨c, hc⟩, Subtype.ext (by simp [ψ])⟩
  have hker' : ψ.ker ≤ Subgroup.center M := by
    intro x hx
    have h1 : π (e x : K) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [ψ] using this
    have hz := hker _ h1
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro m
    apply e.injective
    apply Subtype.ext
    simpa using hz (e m : K)
  have hφ : ∃ k, ψ k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := h.1.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hx : x ∈ Subgroup.center M := hker' (MonoidHom.mem_ker.mpr (hcon x))
    have := Subgroup.mem_center_iff.mp hx y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← this]
  exact ⟨isQuasisimple_of_surjective h.1 hsurj hφ,
    isClassicalTwoOrG2_of_mulEquiv (centralQuotientEquivOfIsQuasisimple h.1 hsurj hker') h.2⟩

end CentralMap

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
