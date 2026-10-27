module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldDefs
public import CFSG.RankThree.PartOne.S11d.FixedFactsPSL

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank
  (StatedLieAdmissible StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

theorem fixesNonLocalized_psl_ge_three {T : Type} [Group T] [Finite T] {p f n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn3 : 3 ≤ n) (hC : StatedClassicalModel T .PSL n 2 f)
    (hdiag : ¬ p ∣ Nat.gcd n (2 ^ f - 1)) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) : FixesNonLocalized α := by
  have h0 := hC
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ f := hC.1.2.1
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have hdiagK : ¬ p ∣ Nat.gcd n (Nat.card K - 1) := by rwa [hK]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  let e : T ≃* projectiveSL n K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  have : Finite (projectiveSL n K) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (projectiveSL n K) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'p : MulAut.congr e α ^ p = 1 := by
    rw [← map_pow, hαp, map_one]
  have hα'ord : orderOf (MulAut.congr e α) = p := by
    refine orderOf_eq_prime hα'p ?_
    intro h1
    exact hα'inn (h1 ▸ (innerAut (projectiveSL n K)).one_mem)
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn3
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hE : MulAut.congr e α ∈ semilinearAutGroup n K := by
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2' : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2'
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ linearAutGroup n K := by
    intro hD
    exact hα'inn (OutStructure.linear_D2 hp hn3 hdiagK _ hD 1
      (by rw [pow_one, hα'p]; exact Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two hf
      hn3 hK
  obtain ⟨hpf, σ, hσord, ⟨h, -, hαh⟩, hkcard⟩ := hdesc p hp hp2 _ hE hD hα'ord
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h1 | h1
    · simp [h1] at hf
    · exact h1
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  rw [hfdiv] at hkcard
  have hfixset : {x : projectiveSL n K | fieldAut n K σ x = x} =
      ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :
        Set (projectiveSL n K)) := by
    by_cases hpq : p ∣ 2 ^ (p * f₀) - 1
    · have hpn : ¬ p ∣ n := fun hpn => hdiag (Nat.dvd_gcd hpn hpq)
      have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm
      exact (higher_linear_prime_subfield_fixed_group_and_full_centralizer Nat.prime_two hp hp2
        hf hn3 hcop hK σ hσord).2.1
    · exact (nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer Nat.prime_two hp
        (by omega) hp2 hf hn3 hK hpq σ hσord).2.2.1
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) (semilinearFixedSubfield σ)
  have hfixeq : fixSub (fieldAut n K σ) =
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
    ext x
    exact Set.ext_iff.mp hfixset x
  have hs : IsSimpleGroup (projectiveSL n ↥(semilinearFixedSubfield σ)) :=
    KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnab : ∃ a b : projectiveSL n ↥(semilinearFixedSubfield σ), a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL
      (n := n) (K := ↥(semilinearFixedSubfield σ)) hn3
    push Not at h1
    exact h1
  have hXmodel : LieModel (projectiveSL n ↥(semilinearFixedSubfield σ)) .PSL n 2 f₀ :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨⟨Nat.prime_two, hf₀, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
          fun hc => by have := (Prod.mk.inj hc).1; omega⟩,
        ↥(semilinearFixedSubfield σ), inferInstance, inferInstance, hkcard,
        ⟨(LinearCover.projectiveSpecialLinearEquivProjectiveSL n
          ↥(semilinearFixedSubfield σ)).symm.trans
            (projectiveSpecialLinearGroupEquivStatedProj n ↥(semilinearFixedSubfield σ))⟩⟩
  set φ : T ≃* projectiveSL n K := e.trans (h⁻¹ : MulAut (projectiveSL n K)) with hφ
  have hφα : MulAut.congr φ α = fieldAut n K σ := by
    have : MulAut.congr φ α = h⁻¹ * MulAut.congr e α * h⁻¹⁻¹ := rfl
    rw [this, hαh]
    group
  set N := (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range with hN
  have hNΓ : N ≤ fixSub (MulAut.congr φ α) := by rw [hφα, hfixeq]
  have hΓN : fixSub (MulAut.congr φ α) = N := by rw [hφα, hfixeq]
  have hNnorm : (N.subgroupOf (fixSub (MulAut.congr φ α))).Normal := by
    rw [hΓN, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hsolv : Group.IsSolvable (↥(fixSub (MulAut.congr φ α)) ⧸
      N.subgroupOf (fixSub (MulAut.congr φ α))) := by
    have : Subsingleton (↥(fixSub (MulAut.congr φ α)) ⧸
        N.subgroupOf (fixSub (MulAut.congr φ α))) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr (hΓN ▸ (x⁻¹ * y).2)
    exact inferInstance
  let eNk : ↥N ≃* projectiveSL n ↥(semilinearFixedSubfield σ) :=
    (MonoidHom.ofInjective hinj).symm
  have hNperf : Group.IsPerfect ↥N := by
    have hperf : Group.IsPerfect (projectiveSL n ↥(semilinearFixedSubfield σ)) :=
      isPerfect_of_simple_nonabelian hnab
    exact Group.IsPerfect.ofSurjective (f := eNk.symm.toMonoidHom) eNk.symm.surjective
  have hZ : Subgroup.center (projectiveSL n ↥(semilinearFixedSubfield σ)) = ⊥ :=
    center_eq_bot_of_simple' hnab
  have hX : LieModel (↥N ⧸ Subgroup.center ↥N) .PSL n 2 f₀ :=
    lieModel_of_mulEquiv
      ((centerQuotientCongr eNk).trans (centerQuotientEquivSelf hZ)).symm hXmodel
  exact FixesNonLocalized.of_fixedFacts
    (fixedFacts_of_iso φ α ((lieModel_classical_iff (by decide)).mpr h0) hf₀ N hNΓ hNnorm hNperf
      hsolv (SignalizerFunctorTheorem.NonLocal.nonLocalized_linearSubfield hn3 _)
      (fun x hx _ => hΓN ▸ hx) (Or.inl fun x hx _ => hΓN ▸ hx) (Or.inl hX))

theorem fixesNonLocalized_psl_two {T : Type} [Group T] [Finite T]
    {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hC : StatedClassicalModel T .PSL 2 2 f)
    (hq : f ≠ p) {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    FixesNonLocalized α := by
  have h0 := hC
  have hf : 1 ≤ f := hC.1.2.1
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hαord : orderOf α = p := orderOf_eq_prime hαp (fun h1 => hαinn (h1 ▸ (innerAut T).one_mem))
  let ψ : T ≃* coordinateG K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (pslEquivCoordinateG K)
  obtain ⟨hpf, -⟩ := psl_two_exists_fixSub_equiv hp hp2 hf hK ψ hαord hαinn
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 2 ≤ f₀ := by
    rcases Nat.lt_or_ge f₀ 2 with h1 | h1
    · have : f₀ = 1 := by
        rcases Nat.eq_zero_or_pos f₀ with h2 | h2
        · simp [h2] at hf
        · omega
      exact absurd (by rw [this, mul_one]) hq
    · exact h1
  exact FixesNonLocalized.of_fixedFacts
    (fixedFacts_PSL_two hp hp5 ((lieModel_classical_iff (by decide)).mpr h0) hf₀ α hαp hαinn)

end CFSG.AGLEmbedding.LieOut
