module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpHigh
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafSp4C

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf
open CFSG.Open (StatedLieTag StatedLieAdmissible StatedProj StatedSp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace PSpFive

open CFSG.ComponentClassification.CatLeafProof.X10Sp

private theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem false_of_five_model {X : Type} [Group X] {t : StatedLieTag} {m e : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp) (hm : m ≠ 0) (h3 : 3 ≤ lieSylowExponent t m)
    (he : 1 ≤ e) (hX : Nat.card X = 60) (h : Blueprint.LieModel X t m 5 e) : False := by
  obtain ⟨-, hfac⟩ := lieOrder_of_lieModel ht (by norm_num : (5 : ℕ) ≠ 2) hm h
  have h1 : 5 ^ (lieSylowExponent t m * e) ∣ 60 := by
    rw [← hfac, ← hX]
    exact Nat.ordProj_dvd _ 5
  have h2 : 5 ^ 3 ∣ 5 ^ (lieSylowExponent t m * e) :=
    pow_dvd_pow 5 (h3.trans (Nat.le_mul_of_pos_right _ he))
  have h3' := h2.trans h1
  norm_num at h3'

private theorem three_le_psl {n : ℕ} (hn : 3 ≤ n) : 3 ≤ lieSylowExponent .PSL n := by
  change 3 ≤ n * (n - 1) / 2
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  exact Nat.mul_le_mul hn (by omega)

private theorem three_le_psu {n : ℕ} (hn : 3 ≤ n) : 3 ≤ lieSylowExponent .PSU n := by
  change 3 ≤ n * (n - 1) / 2
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  exact Nat.mul_le_mul hn (by omega)

private theorem three_le_psp {n : ℕ} (hn : 2 ≤ n) : 3 ≤ lieSylowExponent .PSp n := by
  change 3 ≤ n ^ 2
  nlinarith

theorem false_of_a5_high {K : Type} [Field K] [Finite K] {n f : ℕ} (hK : Nat.card K = 5 ^ f)
    (hadm : StatedLieAdmissible .PSp n 5 f) (hn : 3 ≤ n)
    {α : MulAut (StatedProj (StatedSp n K))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {L : Subgroup (fixedSubgroup α)} (hL : IsPComponent 2 L)
    (hA : Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨eA⟩ := hA
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hq : IsQuasisimple L :=
    CatalogueBSymplecticB.odd_symplectic_involution_fixed_p_components 5 f hp hp2 hadm.2.1 K hK n
      (by omega) α hα2 hα1 2 Nat.prime_two L hL
  have hsub : L.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hL
    exact h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := eA.isSimpleGroup
  have hZO : center L = pPrimeCore 2 L := GSThmB.X10Rec.center_eq_pPrimeCore hq hs
  have hZ : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z * z = 1 → z = 1 := by
    intro z hzL hzc hzz
    exact congrArg Subtype.val (eq_one_of_mem_center hZO (z := ⟨z, hzL⟩)
      (mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).symm) (Subtype.ext hzz))
  have hcard : Nat.card (L ⧸ center L) = 60 :=
    (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZO).toEquiv).trans
      ((Nat.card_congr eA.toEquiv).trans card_alt_five)
  rcases fixed_component_models hp hp2 hK hadm hn hα2 hα1 ⟨hq, hsub⟩ hZ with
    ⟨hd, h⟩ | ⟨hd, h⟩ | ⟨he, hd, h⟩ | ⟨_, -, hd, h⟩
  · exact false_of_five_model (Or.inl rfl) (by omega) (three_le_psl hn) hd.2.1 hcard h
  · exact false_of_five_model (Or.inr (Or.inl rfl)) (by omega) (three_le_psu hn) hd.2.1 hcard h
  · obtain ⟨k, hk⟩ := he
    exact false_of_five_model (Or.inr (Or.inr rfl)) (by omega) (three_le_psp (by omega)) hd.2.1
      hcard h
  · exact false_of_five_model (Or.inr (Or.inr rfl)) (by omega) (three_le_psp (by omega)) hd.2.1
      hcard h

private theorem num_a {q : ℕ} (hq : 5 ≤ q) (h : q * (q ^ 2 - 1) = 60) : False := by
  have h25 : 25 ≤ q ^ 2 := by nlinarith
  have : 5 * 24 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq (by omega)
  omega

private theorem num_b {q : ℕ} (hq : 5 ≤ q) (h : q * (q ^ 2 - 1) = 120) : q = 5 := by
  by_contra hne
  have h6 : 6 ≤ q := by omega
  have h36 : 36 ≤ q ^ 2 := by nlinarith
  have : 6 * 35 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h6 (by omega)
  omega

private theorem num_c {q : ℕ} (hq : 5 ≤ q) (h : q ^ 2 * ((q ^ 2) ^ 2 - 1) = 120) : False := by
  have h25 : 25 ≤ q ^ 2 := by nlinarith
  have h625 : 625 ≤ (q ^ 2) ^ 2 := by nlinarith
  have : 25 * 624 ≤ q ^ 2 * ((q ^ 2) ^ 2 - 1) := Nat.mul_le_mul h25 (by omega)
  omega

private theorem num_d {k : ℕ} (hq : 5 ≤ k ^ 2)
    (h : k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) = 120) : False := by
  have hk3 : 3 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k <;> omega
  have h9 : 9 ≤ k ^ 2 := by nlinarith
  have e4 : k ^ 4 = (k ^ 2) ^ 2 := by ring
  have h81 : 81 ≤ k ^ 4 := by rw [e4]; nlinarith
  have h8 : 8 ≤ k ^ 2 - 1 := by omega
  have h80 : 80 ≤ k ^ 4 - 1 := by omega
  have h640 : 8 * 80 ≤ (k ^ 2 - 1) * (k ^ 4 - 1) := Nat.mul_le_mul h8 h80
  have : 81 * 640 ≤ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := Nat.mul_le_mul h81 h640
  omega

theorem psp4_f {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    {α : MulAut (StatedProj (StatedSp 2 K))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hMX : M ≤ CatFactsSp4.fixOf α)
    (hM : IsPComponent 2 (M.subgroupOf (CatFactsSp4.fixOf α)))
    (hA : Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin 5))) : f = 1 := by
  obtain ⟨eA⟩ := hA
  have h5 : 5 ≤ 5 ^ f := Nat.le_self_pow (by omega) 5
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hnt : Nontrivial (M ⧸ pPrimeCore 2 M) := (eA.isSimpleGroup).toNontrivial
  have hcardM : Nat.card M = 60 * Nat.card (pPrimeCore 2 M) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 M), Nat.card_congr eA.toEquiv,
      card_alt_five]
  rcases GSThmB.Pump516.psp4_fixed_cases (p := 5) (by norm_num) (by norm_num) hf hK h5 hα2 hα1 hMX
      hM with ⟨hO, hc⟩ | ⟨hs, hc⟩ | ⟨hs, hc⟩ | ⟨hs, k, hk, hc⟩
  · exfalso
    rw [hO, Subgroup.card_bot] at hcardM
    exact num_a h5 (by omega)
  · haveI := hs
    have hO := GSThmB.Pump516.pPrimeCore_eq_bot_of_simple hnt
    rw [hO, Subgroup.card_bot] at hcardM
    have h55 : 5 ^ f = 5 ^ 1 := by
      have := num_b h5 (by omega)
      simpa using this
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) h55
  · exfalso
    haveI := hs
    have hO := GSThmB.Pump516.pPrimeCore_eq_bot_of_simple hnt
    rw [hO, Subgroup.card_bot] at hcardM
    exact num_c h5 (by omega)
  · exfalso
    haveI := hs
    have hO := GSThmB.Pump516.pPrimeCore_eq_bot_of_simple hnt
    rw [hO, Subgroup.card_bot] at hcardM
    exact num_d (hk ▸ h5) (by omega)

end PSpFive

theorem fivePump_char5_PSp : FivePumpCharFiveClause .PSp := by
  intro S _ _ hs _hna hF σ P hP hZ eP _huniq
  obtain ⟨n, f, hm⟩ := hF
  have hadm : StatedLieAdmissible .PSp n 5 f := hm.admissible
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hf1 : 1 ≤ f := hadm.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel' hadm hm
  have : IsSimpleGroup S := hs
  have hσ1 : σ ≠ 1 := hP.ne_one
  obtain ⟨hσ2', hPF, hPp, -⟩ := hP
  have hσ2 : σ * σ = 1 := MulEquiv.ext fun y => hσ2' y
  obtain ⟨eP⟩ := eP
  have hcβ : ∀ (β : MulAut S) x, e (β x) = MulAut.congr e β (e x) := fun β x => by
    simp [MulAut.congr_apply]
  have hα2 : MulAut.congr e σ * MulAut.congr e σ = 1 := by rw [← map_mul, hσ2, map_one]
  have hα1 : MulAut.congr e σ ≠ 1 := fun h =>
    hσ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨hM0, hM⟩ := CatFactsSp4.isPComponent_map_fixOf (hcβ σ) hPF hPp
  let eM : P ≃* P.map e.toMonoidHom := P.equivMapOfInjective e.toMonoidHom e.injective
  have hAM : Nonempty ((P.map e.toMonoidHom) ⧸ pPrimeCore 2 (P.map e.toMonoidHom) ≃*
      alternatingGroup (Fin 5)) :=
    ⟨(CatalogueBAlternating.primeCoreQuotientEquiv 2 eM).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans eP)⟩
  have hnf : n = 2 ∧ f = 1 := by
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · obtain rfl : n = 2 := by omega
      exact ⟨rfl, PSpFive.psp4_f hf1 hK hα2 hα1 hM0 hM hAM⟩
    · exfalso
      obtain ⟨eAM⟩ := hAM
      exact PSpFive.false_of_a5_high hK hadm hge hα2 hα1 hM
        ⟨(CatalogueBAlternating.primeCoreQuotientEquiv 2
          (Subgroup.subgroupOfEquivOfLe hM0)).trans eAM⟩
  obtain ⟨rfl, rfl⟩ := hnf
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))))

end CFSG.ComponentClassification.SolMax.FiveCat
