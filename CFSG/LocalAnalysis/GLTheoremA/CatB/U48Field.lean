module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K)

noncomputable section

theorem fieldFactor4_fieldSU4 (σ : K ≃+* K) : fieldFactor4 (fieldSU4 σ) = σ := by
  have hC := isPrimeFormGram_one (n := 4) (K := K)
  obtain ⟨-, -, -, -, -, hff, -⟩ :=
    unitary_prime_form_full_semilinear_realization hK hC hn4 hq4
  have key : (MulAut.congr ePU4.symm) (fieldSU4 σ) = primeFormFieldHom hK hC σ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H z =>
      apply ePU4.injective
      change ePU4 (ePU4.symm (fieldSU4 σ (ePU4 (z : PU4)))) = _
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
  have h1 := hff 1 σ
  rw [map_one, one_mul] at h1
  change primeFormFieldFactor hK hC hn4 hq4 ((MulAut.congr ePU4.symm) (fieldSU4 σ)) = σ
  rw [key]
  exact h1

abbrev RU : Type := LargeEvenProj (LargeEvenSUGroup (Fin (3 + 1)) K (2 ^ 3))

@[expose] def rMk : SU4 →* RU :=
  (LargeEvenProjMk (LargeEvenSUGroup (Fin (3 + 1)) K (2 ^ 3))).comp
    (MulEquiv.subgroupCongr SU4_eq_stated).toMonoidHom

theorem rMk_injective : Function.Injective rMk := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 := (QuotientGroup.eq_one_iff _).1 hx
  rw [Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  have hcen : x ∈ Subgroup.center SU4 := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hx' : ((x : SU4) : GL (Fin 4) K) = Matrix.GeneralLinearGroup.scalar (Fin 4) c := hc.symm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx']
    exact Subgroup.mem_center_iff.1 (TauCeti.scalar_mem_center (ι := Fin 4) (k := K) c) _
  rw [center_SU4, Subgroup.mem_bot] at hcen
  exact hcen

theorem rMk_surjective : Function.Surjective rMk :=
  (QuotientGroup.mk'_surjective _).comp (MulEquiv.surjective _)

@[expose] def toR : SU4 ≃* RU := MulEquiv.ofBijective rMk ⟨rMk_injective, rMk_surjective⟩

theorem toR_apply (x : SU4) : toR x = rMk x := rfl

theorem exists_noncomm_SU4 : ∃ a b : SU4, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center SU4 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.2 fun g => h g x
  rw [center_SU4] at hc
  haveI := isSimpleGroup_SU4
  obtain ⟨x, hx⟩ := exists_ne (1 : SU4)
  have : x ∈ (⊥ : Subgroup SU4) := by rw [hc]; exact Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.1 this)

theorem isSimpleGroup_RU : IsSimpleGroup RU := by
  haveI := isSimpleGroup_SU4
  exact toR.symm.isSimpleGroup

theorem exists_noncomm_RU : ∃ a b : RU, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := exists_noncomm_SU4
  exact ⟨toR a, toR b, fun h => hab (toR.injective (by rw [map_mul, map_mul, h]))⟩

theorem mem_GUSet (x : SU4) : ((x : GL (Fin 4) K)) ∈ LargeEvenGUSet (Fin (3 + 1)) K (2 ^ 3) := by
  refine ⟨1, one_ne_zero, by simp, ?_⟩
  have := (mem_SUid.mp x.2).2
  rw [one_smul]
  convert this using 2
  ext i j
  simp [conjTr, σ4, CFSG.LieType.BorelTits.unitaryInvolution_apply, iterateFrobenius_def]

theorem proj_eq_rMk (h₁ : ↥(LargeEvenSUGroup (Fin (3 + 1)) K (2 ^ 3))) :
    LargeEvenProjMk (LargeEvenSUGroup (Fin (3 + 1)) K (2 ^ 3)) h₁ =
      rMk ⟨(h₁ : GL (Fin 4) K), by rw [SU4_eq_stated]; exact h₁.2⟩ := rfl

theorem fieldOn_of_outer {G : Type} [Group G] [Finite G] {X L : Subgroup G} {b : G}
    (hL : GLAPComponent 3 X L) (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center (PQuot 3 L) = ⊥) (e : PQuot 3 L ≃* SU4) (γ : MulAut SU4)
    (hγ : ∀ q : PQuot 3 L, γ (e q) = e (barAut L b hb q)) (hγ3 : γ ^ 3 = 1)
    (hγ1 : fieldFactor4 γ ≠ 1) : FieldOn 3 b L := by
  obtain ⟨h, hh⟩ := exists_conj_fieldSU4 hγ3 hγ1
  set φ : K ≃+* K := fieldFactor4 γ with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hγ3, map_one]
  have hord : orderOf (fieldSU4 φ) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [fieldSU4_pow, hφ3, fieldSU4_one]
    · intro h1
      apply hγ1
      have := congrArg fieldFactor4 h1
      rwa [fieldFactor4_fieldSU4, map_one] at this
  have hγeq : γ = MulAut.conj h * fieldSU4 φ * (MulAut.conj h)⁻¹ := by
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have h1 := hh ((MulAut.conj h)⁻¹ x)
    have h2 : h * ((MulAut.conj h)⁻¹ x) * h⁻¹ = x := by
      rw [MulAut.inv_apply]
      simp [MulAut.conj_symm_apply, mul_assoc]
    rw [h2] at h1
    rw [h1]
    simp [MulAut.conj_apply]
  refine ⟨hb, ?_⟩
  have hperf : commutator (PQuot 3 L) = ⊤ :=
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL).1
  refine ⟨hperf, ⟨.twA, 3, 3⟩, ⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
  dsimp only [LargeEvenRawDatum]
  refine ⟨K, inferInstance, inferInstance, by rw [card_K], ?_⟩
  refine ⟨isSimpleGroup_RU, exists_noncomm_RU,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans (e.trans toR),
    ?_⟩
  refine ⟨Or.inl (by decide), MulAut.congr toR (fieldSU4 φ), ?_, MulAut.congr toR (MulAut.conj h), ?_,
    ?_, ?_⟩
  ·
    refine ⟨φ, fun h₁ h₁' hrel => ?_⟩
    rw [proj_eq_rMk, proj_eq_rMk, ← toR_apply, ← toR_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSU4, coe_glAut]
    exact hrel.symm
  ·
    refine ⟨(h : GL (Fin 4) K), mem_GUSet h, fun h₁ h₁' hrel => ?_⟩
    rw [proj_eq_rMk, proj_eq_rMk, ← toR_apply, ← toR_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [MulAut.conj_apply]
    exact hrel.symm
  ·
    exact (orderOf_injective (MulAut.congr toR).toMonoidHom (MulAut.congr toR).injective
      (fieldSU4 φ)).trans hord
  ·
    intro l l' hrel
    have huf : MulAut.congr toR (MulAut.conj h) * MulAut.congr toR (fieldSU4 φ) *
        (MulAut.congr toR (MulAut.conj h))⁻¹ = MulAut.congr toR γ := by
      rw [← map_inv, ← map_mul, ← map_mul, hγeq]
    rw [huf]
    have hl' : barAut L b hb l = l' := (indRel_iff_barAut hb l l').1 hrel
    change (MulAut.congr toR γ) (toR (e l)) = toR (e l')
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hγ, hl']

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
