module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Pump
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear
public import CFSG.LocalAnalysis.GLTheoremA.S3.KD76cHolds
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Shapes

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv)

theorem fixSubgroup_fieldAut_eq_range {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) {τ : K ≃+* K} (hτp : τ ^ p = 1) (hpK : ¬ p ∣ Nat.card Kˣ) :
    fixSubgroup (fieldAut n K τ) =
      (linearSubfieldInclusion n (semilinearFixedSubfield τ)).range := by
  have hk : ∀ x, x ∈ semilinearFixedSubfield τ ↔ τ x = x := fun x => RingHom.mem_eqLocusField
  ext x
  exact (mem_fixSubgroup).trans
    (Set.ext_iff.1 (fixed_points_eq_range hk hn (root_descent_of_not_dvd hp hk hτp hpK)) x)

theorem not_dvd_card_units_of_card_eq {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) : ¬ p ∣ Nat.card Kˣ := by
  rw [Nat.card_units, hK]
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem isChevSimple_projectiveSL {r p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hr : 2 ≤ r) {F : Type} [Field F] (hF : Nat.card F = p ^ f) :
    IsChevSimple p (projectiveSL (r + 1) F) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hp.ne_zero)
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  haveI : Fact q.p.Prime := ⟨hp⟩
  have hq3 : 3 ≤ q.card := by
    have h1 : 3 ≤ p := by have := hp.two_le; omega
    have h2 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    rw [TauCeti.PrimePower.card_def]
    exact h1.trans h2
  have hv : (TauCeti.LieTypeIndex.A r q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    rintro (⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩) <;> omega
  let e : projectiveSL (r + 1) F ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group :=
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) F).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
        (CFSG.ClassicalModels.finiteFieldEquivGaloisField F p f hf hF) (Fin (r + 1)))).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm
  exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩, TauCeti.LieTypeIndex.characteristic_A r q,
    ⟨e⟩⟩

theorem outerCentData_fieldAut_of_three_le {n p f : ℕ} (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = p ^ f) {τ : K ≃+* K}
    (hτ : orderOf τ = p) (hout : fieldAut n K τ ∉ innerAut (projectiveSL n K)) :
    OuterCentData p (fieldAut n K τ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
  haveI : CharP K p := finite_field_prime_power_characteristic hp hf hK
  haveI : Finite (projectiveSL n K) := inferInstance
  set k : Subfield K := semilinearFixedSubfield τ with hk_def
  have hk : ∀ x, x ∈ k ↔ τ x = x := fun x => RingHom.mem_eqLocusField
  obtain ⟨hpf, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hτ
  have hτp : τ ^ p = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hf' : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hC : fixSubgroup (fieldAut n K τ) = (linearSubfieldInclusion n k).range :=
    fixSubgroup_fieldAut_eq_range (by omega) hp hτp (not_dvd_card_units_of_card_eq hp hf hK)
  obtain ⟨hsimp, hnab⟩ := simple_nonabelian_range_linearSubfieldInclusion hn k
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  have hs : IsSimpleGroup ↥(fixSubgroup (fieldAut n K τ)) := by
    rw [hC]
    exact hsimp
  have hnc : ∃ a b : ↥(fixSubgroup (fieldAut n K τ)), a * b ≠ b * a := by
    rw [hC]
    by_contra h
    push Not at h
    exact hnab fun a b => h a b
  have hdvd : p ∣ Nat.card ↥(fixSubgroup (fieldAut n K τ)) := by
    rw [hC, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    refine CFSG.SignalizerFunctorTheorem.CatalogBridge.dvd_card_projectiveSL_of_dvd (by omega) hp ?_
    rw [hkcard]
    exact dvd_pow_self p (by omega)
  have hchev : IsChevSimple p ↥(fixSubgroup (fieldAut n K τ)) := by
    rw [hC]
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    exact isChevSimple_of_mulEquiv (MonoidHom.ofInjective hinj)
      (isChevSimple_projectiveSL hp hp2 hf' (by omega) hkcard)
  have hZ : Subgroup.center (projectiveSL n K) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn
  have hord : orderOf (fieldAut n K τ) = p := by
    rw [orderOf_fieldAut hn, hτ]
  refine OuterCentData.ofSimpleNormal hp (SimpleNormalData.ofSimple hs hnc hchev hdvd) ?_ ?_
  · intro _ w hw _ hfix
    have hfixing : w ∈ fixingSubgroup (MulAut (projectiveSL n K))
        ((linearSubfieldInclusion n k).range : Set (projectiveSL n K)) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact hfix y (by rw [hC]; exact hy)
    rw [fixingSubgroup_range_linearSubfieldInclusion hk hn] at hfixing
    have h1 : orderOf w ∣ orderOf (fieldAut n K τ) := orderOf_dvd_of_mem_zpowers hfixing
    rw [hord] at h1
    have h2 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd hw.symm h1
    rw [orderOf_eq_one_iff.1 h2]
    exact (innerAut (projectiveSL n K)).one_mem
  · intro hp3 _ β' hβ' hcomm _
    subst hp3
    exact exists_inner_on_fixSubgroup_of_pump hp hZ hord hout
      (fun D hexp hcard => CFSG.LocalAnalysis.GLTheoremA.kd76c_exists_inner_projectiveSL hp hp2 hn D
        hexp hcard) hβ' hcomm

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
