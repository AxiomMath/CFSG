module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeModelQ
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23JSide

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

theorem betaHat_eq_of_mem_kernel {G : Type} [Group G] {J : Subgroup G} {y : G}
    (hyK : y ∈ coreActionKernel J) (e : Jhat J) :
    betaHat J (mem_coreActionKernel.mp hyK).1 e = e := by
  obtain ⟨j, rfl⟩ := jq_surjective J e
  rw [betaHat_jq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  obtain ⟨o, ho, hoe⟩ := (mem_coreActionKernel.mp hyK).2 j j.2
  have hoe' : (o : G) = (j : G)⁻¹ * y⁻¹ * j * y := hoe
  have e1 : (conjJ J (mem_coreActionKernel.mp hyK).1 j)⁻¹ * j = o⁻¹ := by
    apply Subtype.ext
    show (y⁻¹ * (j : G) * y)⁻¹ * j = (o : G)⁻¹
    rw [hoe']
    group
  rw [e1]
  exact inv_mem ho

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H}

theorem betaHat_x_involutive (e : Jhat h.J) :
    betaHat h.J (h.S_le_normalizer h.x_mem) (betaHat h.J (h.S_le_normalizer h.x_mem) e) = e := by
  have hxK : h.x * h.x ∈ coreActionKernel h.J := by
    have := (mem_inf.mp (mem_inf.mp h.x_sq_mem).1).2
    rwa [pow_two] at this
  rw [← GrS4.betaHat_mul_apply (h.S_le_normalizer h.x_mem) (h.S_le_normalizer h.x_mem) e]
  exact betaHat_eq_of_mem_kernel hxK e

section Model


theorem isPGroup_hjD : IsPGroup 2 (T0.comap hjQ) := by
  refine IsPGroup.comap_of_ker_isPGroup (IsPGroup.of_card (n := 6) (by rw [card_T0]; norm_num)) hjQ ?_
  intro g
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  have := mul_self_of_mem_ker g.2
  simpa [pow_one, sq] using this

theorem index_hjD : (T0.comap hjQ).index = 315 := by
  have hsurj : Function.Surjective (hjQ.codRestrict PSL3Four.S hjQ_mem_S) := fun s => by
    obtain ⟨e, he⟩ := hjQ_surj s s.2
    exact ⟨e, Subtype.ext he⟩
  have heq : T0.comap hjQ = (T0.subgroupOf PSL3Four.S).comap
      (hjQ.codRestrict PSL3Four.S hjQ_mem_S) := by
    ext e
    simp [mem_subgroupOf]
  rw [heq, Subgroup.index_comap_of_surjective _ hsurj]
  have h1 := (T0.subgroupOf PSL3Four.S).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_S).toEquiv, card_T0, card_S] at h1
  omega

@[expose] def hjSyl : Sylow 2 ↥hjJ :=
  isPGroup_hjD.toSylow (by rw [index_hjD]; decide)

theorem mem_hjSyl {e : ↥hjJ} : e ∈ (hjSyl : Subgroup ↥hjJ) ↔ hjQ e ∈ T0 := by
  rw [hjSyl, IsPGroup.toSylow_coe]
  rfl

end Model

variable (hKa : conjugate h.K h.a = h.K)

theorem exists_psi'
    (Ψ : OddBar h.J ≃* ↥hjJ) :
    ∃ g : ↥hjJ, ∀ e : ↥hjJ, hjQ e ∈ T0 ↔
      ∃ d, ∃ hdD : d ∈ h.D, g * Ψ (jq h.J ⟨d, h.D_le_J hdD⟩) * g⁻¹ = e := by
  obtain ⟨hDJ, T, hT⟩ := isSylowTwoIn_D h
  set S₁ : Sylow 2 ↥hjJ :=
    (T.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥h.J))).mapSurjective
      (f := Ψ.toMonoidHom) Ψ.surjective with hS₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥hjJ S₁ hjSyl
  refine ⟨g, fun e => ?_⟩
  rw [← mem_hjSyl, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    change s ∈ (((T : Subgroup ↥h.J).map (QuotientGroup.mk' (pPrimeCore 2 ↥h.J))).map
      Ψ.toMonoidHom) at hs
    obtain ⟨y, ⟨j, hj, rfl⟩, rfl⟩ := hs
    rw [SetLike.mem_coe, hT, mem_subgroupOf] at hj
    refine ⟨(j : H), hj, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply]
    rfl
  · rintro ⟨d, hdD, rfl⟩
    refine ⟨Ψ (jq h.J ⟨d, h.D_le_J hdD⟩), ?_, ?_⟩
    · change Ψ (jq h.J ⟨d, h.D_le_J hdD⟩) ∈ (((T : Subgroup ↥h.J).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥h.J))).map Ψ.toMonoidHom)
      exact ⟨_, ⟨⟨d, h.D_le_J hdD⟩, by rw [SetLike.mem_coe, hT, mem_subgroupOf]; exact hdD, rfl⟩,
        rfl⟩
    · rw [MulAut.smul_def, MulAut.conj_apply]

end CFSG.ComponentClassification.GSThmB.CF23L34
