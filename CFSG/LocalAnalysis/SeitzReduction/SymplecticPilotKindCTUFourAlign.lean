module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUFourLabel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUFourOrth

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore ordSL)
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)
open scoped MatrixGroups

theorem ctuf_ordSL_two_sq_lt {q : ℕ} (hq : 2 ≤ q) : ordSL 2 q ^ 2 < ordSL 2 (q ^ 2) := by
  rw [F4Pilot.ordSL_two, F4Pilot.ordSL_two]
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = a + 1 := ⟨q ^ 2 - 1, by omega⟩
  have h1 : q ^ 2 - 1 = a := by omega
  have h2 : (q ^ 2) ^ 2 - 1 = a * (a + 2) := by
    rw [ha, show (a + 1) ^ 2 = a * (a + 2) + 1 by ring, Nat.add_sub_cancel]
  rw [h1, h2, mul_pow]
  have ha3 : 3 ≤ a := by omega
  have hpos : 0 < q ^ 2 := by positivity
  have : a ^ 2 < a * (a + 2) := by nlinarith
  exact Nat.mul_lt_mul_of_pos_left this hpos

section Embed

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem CtuParam.natCard_blockSpecialLinear_le_stringCore (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) (hN : 3 ≤ N) {k : Fin N} (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    {B : Finset (Fin N)} (hkB : k ∉ B) (hB : 2 ≤ B.card) {l : Fin N} (hlk : l ≠ k)
    (hlB : l ∉ B) : Nat.card (blockSpecialLinear (K := F) B) ≤ Nat.card (stringCore e B) := by
  have hσ := unitaryInvolution_involutive hF
  set SB := blockSpecialLinear (K := F) B with hSB
  set φ₁ : SB →* G := P.Φ.comp (((ctufSiegel (unitaryInvolution F 2 f) hσ ε hε).comp
    SB.subtype).codRestrict (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))
      fun A => ctufSiegel_mem_ctuBlock_singleton (hσ := hσ) (hε := hε) hkB A.2) with hφ₁
  have hkl : k ≠ l := Ne.symm hlk
  have hc3 : ({k} : Finset (Fin N))ᶜ.card = N - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hq : (2 * ({k} : Finset (Fin N))ᶜ.card + ε, 2 ^ f) ≠ (3, 2) := by
    rw [hc3]
    intro h'
    have := (Prod.mk.inj h').1
    omega
  have hinj := P.injective_overlap hF hkl (by rw [hc3]; omega) hq
  have hkl' : ∀ A : SB, ctufSiegel (unitaryInvolution F 2 f) hσ ε hε (A : SL(N, F)) ∈
      ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) := fun A =>
    ctufSiegel_mem_ctuBlock (fun p hp => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hkB
      · exact hlB) A.2
  have hφ₁inj : Function.Injective φ₁ := by
    intro A A' h
    have h2 := hinj (a₁ := ⟨_, hkl' A⟩) (a₂ := ⟨_, hkl' A'⟩) h
    exact Subtype.ext (ctufSiegel_injective (congrArg Subtype.val h2))
  have hrange : φ₁.range ≤ stringCore e B := by
    rintro _ ⟨A, rfl⟩
    exact P.ctufSiegel_mem_stringCore hF hf hkB hB A.2
  calc Nat.card SB = Nat.card φ₁.range := Nat.card_congr (MonoidHom.ofInjective hφ₁inj).toEquiv
    _ ≤ Nat.card (stringCore e B) := Subgroup.card_le_of_le hrange

end Embed

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp 4 K} {t : G}

theorem false_of_siegelSwapParam_of_ctuParam (S : SiegelSwapParam e t)
    (hKc : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e 3) : False := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have h01 : (0 : Fin 4).val + 1 < 4 := by decide
  have hne : (0 : Fin 4) ≠ ⟨(0 : Fin 4).val + 1, h01⟩ := fun h =>
    absurd (congrArg Fin.val h) (by norm_num)
  have hB : ({0, ⟨(0 : Fin 4).val + 1, h01⟩} : Finset (Fin 4)).card = 2 := Finset.card_pair hne
  have h3B : (3 : Fin 4) ∉ ({0, ⟨(0 : Fin 4).val + 1, h01⟩} : Finset (Fin 4)) := by
    simp [Fin.ext_iff]
  have h2B : (2 : Fin 4) ∉ ({0, ⟨(0 : Fin 4).val + 1, h01⟩} : Finset (Fin 4)) := by
    simp [Fin.ext_iff]
  have hcard := P.natCard_blockSpecialLinear_le_stringCore hF hf (by norm_num)
    (B := {0, ⟨(0 : Fin 4).val + 1, h01⟩}) h3B (by omega) (l := 2) (by decide) h2B
  rw [← pieceCore_singleton_eq_stringCore e h01, S.natCard_pieceCore_singleton hK (by norm_num)
    h01, F4Pilot.natCard_blockSpecialLinear (by omega), hB, hF, hKc] at hcard
  have h2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (four_le_two_pow hf)
  exact absurd hcard (not_le.2 (ctuf_ordSL_two_sq_lt h2))

end Swap

section Align

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K} {t : G}

theorem ctuf_ctuaTwist_zero_apply {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}
    {ν : Fˣ} (hν : σ ν * ν = 1) (b : Bool) (y : SU σ (2 * N + 0)) :
    ctuaTwist (Nat.zero_le 1) σ hσ ν hν b y = bif b then ctuaBarAut σ hσ _ y else y := by
  rw [ctuaTwist, MulAut.mul_apply]
  cases b
  · apply Subtype.ext
    rw [Bool.cond_false, MulAut.one_apply, coe_ctuaConjAut, ctuaTorGL_eq_one_of_zero, one_mul,
      inv_one, mul_one]
    rfl
  · apply Subtype.ext
    rw [Bool.cond_true, coe_ctuaConjAut, ctuaTorGL_eq_one_of_zero, one_mul, inv_one, mul_one]
    rfl

theorem exists_ctuParamAgree_of_siegelFieldParam
    (S : SiegelFieldParam e t ι (unitaryInvolution F 2 f)) (hKc : Nat.card K = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hN : 4 ≤ N)
    (P : ∀ k : Fin N, CtuParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 f) ι hι e k) :
    ∃ Q : ∀ k : Fin N, CtuParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 f) ι hι e k,
      CtuParamAgree Q := by
  have hσ := unitaryInvolution_involutive hF
  choose Q hQ using fun k => (P k).exists_siegel_normalized S hKc hF hf hN
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl := mem_ctuBlock_pair hx hx'
  obtain ⟨ν, hν, b, h1⟩ := (Q k).exists_twist_of_overlap hKc hF hf hN hkl (Q l)
  cases b
  · refine (h1 x hxkl).trans (congrArg (Q l).Φ (Subtype.ext ?_))
    change ctuaTwist (Nat.zero_le 1) (unitaryInvolution F 2 f) hσ ν hν false x = x
    rw [ctuf_ctuaTwist_zero_apply]
    rfl
  · exfalso
    obtain ⟨p, hp, p', hp', hpp'⟩ : ∃ p ∈ ({k, l} : Finset (Fin N))ᶜ,
        ∃ p' ∈ ({k, l} : Finset (Fin N))ᶜ, p ≠ p' := by
      refine Finset.one_lt_card.1 ?_
      rw [Finset.card_compl, Finset.card_pair hkl, Fintype.card_fin]
      omega
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hp hp'
    obtain ⟨c, hc⟩ := exists_unitaryInvolution_ne_ctua hF (by omega)
    set T := SpecialLinearGroup.transvection hpp' c with hTdef
    have hTpp : T ∈ blockSpecialLinear (K := F) ({p, p'} : Finset (Fin N)) :=
      LinearPilot.transvection_mem_blockSpecialLinear hpp' (by simp) (by simp) c
    have hTk : T ∈ blockSpecialLinear (K := F) ({k} : Finset (Fin N))ᶜ :=
      LinearPilot.transvection_mem_blockSpecialLinear hpp' (by simpa using hp.1)
        (by simpa using hp'.1) c
    have hTl : T ∈ blockSpecialLinear (K := F) ({l} : Finset (Fin N))ᶜ :=
      LinearPilot.transvection_mem_blockSpecialLinear hpp' (by simpa using hp.2)
        (by simpa using hp'.2) c
    have hσT : SpecialLinearGroup.map (unitaryInvolution F 2 f : F →+* F) T ∈
        blockSpecialLinear (K := F) ({l} : Finset (Fin N))ᶜ :=
      LinearPilot.map_ringHom_mem_blockSpecialLinear _ hTl
    have hy : ctufSiegel (unitaryInvolution F 2 f) hσ 0 (Nat.zero_le 1) T ∈
        ctuBlock (unitaryInvolution F 2 f) 0 ({k, l} : Finset (Fin N)) :=
      ctufSiegel_mem_ctuBlock (fun r hr => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
        rcases hr with rfl | rfl
        · exact fun h => h.elim (fun h' => hp.1 h'.symm) (fun h' => hp'.1 h'.symm)
        · exact fun h => h.elim (fun h' => hp.2 h'.symm) (fun h' => hp'.2 h'.symm)) hTpp
    have h2 := h1 _ hy
    have e1 : (Q k).Φ ⟨ctufSiegel (unitaryInvolution F 2 f) hσ 0 (Nat.zero_le 1) T,
        ctuBlock_pair_le_left _ k l hy⟩ = S.Φ ⟨leviEmbedSL F N T, T, rfl⟩ := hQ k T hTk
    have e2 : (Q l).Φ ⟨ctuaTwist (Nat.zero_le 1) (unitaryInvolution F 2 f) hσ ν hν true
        (ctufSiegel (unitaryInvolution F 2 f) hσ 0 (Nat.zero_le 1) T),
          ctuBlock_pair_le_right _ k l ((ctuaTwist_mem_ctuBlock_iff hν true _ _).2 hy)⟩ =
        S.Φ ⟨leviEmbedSL F N (SpecialLinearGroup.map (unitaryInvolution F 2 f : F →+* F) T), _,
          rfl⟩ := by
      refine Eq.trans ?_ (hQ l _ hσT)
      congr 1
      apply Subtype.ext
      change ctuaTwist (Nat.zero_le 1) (unitaryInvolution F 2 f) hσ ν hν true
        (ctufSiegel (unitaryInvolution F 2 f) hσ 0 (Nat.zero_le 1) T) =
          ctufSiegel (unitaryInvolution F 2 f) hσ 0 (Nat.zero_le 1)
            (SpecialLinearGroup.map (unitaryInvolution F 2 f : F →+* F) T)
      rw [ctuf_ctuaTwist_zero_apply, Bool.cond_true]
      exact ctuaBarAut_ctufSiegel T
    have e3 := S.eq_of_Φ_eq (ctuf_notMem_compl_singleton l) hTl hσT ((e1.symm.trans h2).trans e2)
    have e4 := congrArg (fun A : SL(N, F) => (A : Matrix (Fin N) (Fin N) F) p p') e3
    simp only [hTdef, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      single_apply_same, Matrix.one_apply_ne hpp', zero_add] at e4
    exact hc e4.symm

end Align

theorem spUnitaryEvenFourAlignInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) :
    SpUnitaryEvenFourAlignInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hP F _ _ _ hF ι hι hPk
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hσ := unitaryInvolution_involutive hF
  have hσσ : unitaryInvolution F 2 f * unitaryInvolution F 2 f = 1 := RingEquiv.ext hσ
  have hσ1 : unitaryInvolution F 2 f ≠ 1 := by
    obtain ⟨c, hc⟩ := exists_unitaryInvolution_ne_ctua hF (by omega)
    intro h
    apply hc
    rw [h]
    rfl
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf (by norm_num) e htC ht
    (oddCentralSplit_siegelLevi (by norm_num)) ι hσ1 hσσ (ctuf_fix_iff hKc hF (by omega) hι)
    with ⟨htX, hnorm⟩ | hS | hS
  · exfalso
    obtain ⟨K', _, h, _, C₀, hC, hC₀, ι', ⟨U⟩⟩ := hP 3
    have : Finite K' := h.finite
    have : CharP K' 2 := h.charP
    have hF' : Nat.card K' = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    set ι₃ : K →+* K' := h.fixedField.subtype.comp (ι' : K →+* h.fixedField) with hι₃def
    have hι₃ : ∀ c, unitaryInvolution K' 2 f (ι₃ c) = ι₃ c := fun c => by
      rw [unitaryInvolution_apply, ← h.bar_apply]
      exact h.mem_fixedField.1 (ι' c).2
    exact false_of_siegel_normal_of_ctuParam hset hKc hF' hf (by norm_num) htC ht
      (ctuParamOfUnitary (hι := hι₃) (RingEquiv.refl K') (fun _ => rfl) U)
      (ctuParamOfUnitary_conj (hι := hι₃) (unitaryInvolution_involutive hF') _ _ U) htX hnorm
  · obtain ⟨S⟩ := hS
    exact exists_ctuParamAgree_of_siegelFieldParam S hKc hF hf (by norm_num)
      fun k => (hPk k).some
  · obtain ⟨S⟩ := hS
    exact (false_of_siegelSwapParam_of_ctuParam S hKc hF hf (hPk 3).some).elim

theorem spUnitaryParamCTInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) :
    SpUnitaryParamCTInput :=
  spUnitaryParamCTInput_of_align_orth (spUnitaryEvenFourAlignInput_of_clauses hcat hdet)
    (spUnitaryEvenFourOrthInput_of_clauses hcat hdet)

theorem spUnitaryParamCTInput_of_catalogue
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) : SpUnitaryParamCTInput :=
  spUnitaryParamCTInput_of_clauses hcat (LinearPilot.slmEvenTypeDetAt (by norm_num))

end CFSG.SeitzReduction.SymplecticPilot
