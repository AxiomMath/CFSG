module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNSetting

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def coreKernel (M K : Subgroup X) : Subgroup X :=
  ⨅ (m : X) (_ : m ∈ M), coreActionKernel (conjugate K m)

omit [Finite X] in
theorem mem_coreKernel {M K : Subgroup X} {x : X} :
    x ∈ coreKernel M K ↔ ∀ m ∈ M, x ∈ coreActionKernel (conjugate K m) := by
  simp only [coreKernel, mem_iInf]

omit [Finite X] in
theorem mem_coreActionKernel_of_mem_coreKernel {M K : Subgroup X} {x : X}
    (hx : x ∈ coreKernel M K) : x ∈ coreActionKernel K := by
  have h := mem_coreKernel.mp hx 1 (one_mem M)
  rwa [conjugate_one] at h

omit [Finite X] in
theorem conj_mem_coreKernel {M K : Subgroup X} {t x : X} (ht : t ∈ M)
    (hx : x ∈ coreKernel M K) : t * x * t⁻¹ ∈ coreKernel M K := by
  refine mem_coreKernel.mpr fun m hm => FooteLit.mem_coreActionKernel_conjugate_iff.mpr ?_
  have h := FooteLit.mem_coreActionKernel_conjugate_iff.mp
    (mem_coreKernel.mp hx (m * t) (mul_mem hm ht))
  rwa [show m * t * x * (m * t)⁻¹ = m * (t * x * t⁻¹) * m⁻¹ by group] at h

theorem le_coreActionKernel_of_ne {M J J' : Subgroup X} (hJM : J ≤ M) (hJ'M : J' ≤ M)
    (hJ : IsPComponent 2 (J.subgroupOf M)) (hJ' : IsPComponent 2 (J'.subgroupOf M))
    (hne : J ≠ J') : J' ≤ coreActionKernel J := by
  have hJJ' := GrS5.commutator_le_inf_oddIn hJM hJ'M hJ hJ' hne
  refine fun y hy => mem_coreActionKernel.mpr
    ⟨(GrS5.commutator_le_of_ne hJM hJ'M hJ hJ' hne).2 hy, fun j hj => ?_⟩
  have h1 := (mem_inf.mp (hJJ' (commutator_mem_commutator (inv_mem hj) (inv_mem hy)))).1
  rwa [commutatorElement_def, inv_inv, inv_inv] at h1

theorem isSylowTwoIn_conjugate {T H : Subgroup X} (hT : IsSylowTwoIn T H) {c : X}
    (hc : c ∈ H) : IsSylowTwoIn (conjugate T c) H := by
  refine GrS4.isSylowTwoIn_of_not_dvd (conjugate_le_of_mem hT.1 hc) (hT.isPGroup.map _) ?_
  have hH : conjugate H c = H := conjugate_eq_of_mem_normalizer (le_normalizer hc)
  have h1 := relIndex_map_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom) T H
    (MulAut.conj c⁻¹).injective
  have h2 : (conjugate T c).relIndex H = T.relIndex H := by
    conv_lhs => rw [← hH]
    exact h1
  rw [h2]
  exact GrS4.not_two_dvd_relIndex_of_isSylowTwoIn hT

omit [Finite X] in
theorem exists_isSylowTwoIn_le {Q H : Subgroup X} (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) :
    ∃ T : Subgroup X, IsSylowTwoIn T H ∧ Q ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Q.subgroupOf H) := hQ.of_equiv (subgroupOfEquivOfLe hQH).symm
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  refine ⟨(P : Subgroup H).map H.subtype, ⟨map_subtype_le _, P, ?_⟩,
    fun q hq => ⟨⟨q, hQH hq⟩, hP (mem_subgroupOf.mpr hq), rfl⟩⟩
  exact (comap_map_eq_self_of_injective H.subtype_injective _).symm

omit [Finite X] in
theorem isPGroup_zpowers {x : X} (hx : orderOf x = 2) : IsPGroup 2 (zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

theorem normalizer_L_le : normalizer (L : Set X) ≤ normalizer (K : Set X) := by
  intro n hn
  have hnM : n ∈ normalizer (W : Set X) := h.normalizer_le hn
  by_contra hnK
  have hne : K ≠ conjugate K n := fun e => hnK (mem_normalizer_of_conjugate_eq e.symm)
  have hc := GrS5.commutator_le_inf_oddIn h.le_normalizer (conjugate_le_of_mem h.le_normalizer hnM)
    h.isPComponent_K (isPComponent_conjugate_subgroupOf hnM h.isPComponent_K) hne
  have hLn : L ≤ conjugate K n := by
    rw [← conjugate_eq_of_mem_normalizer hn]
    exact map_mono h.le_K
  have hLO : L ≤ oddIn K := by
    rw [← GrS4.commutator_eq_self_of_gsMaximalSetting h.toGSMaximalSetting]
    exact (commutator_mono h.le_K hLn).trans (hc.trans inf_le_left)
  exact GrS4.not_odd_card_of_isPComponent h.le_centralizer h.isPComponent
    ((odd_card_map_pPrimeCore K).of_dvd_nat (card_dvd_of_le hLO))

theorem exists_sylow (hMax : MaximalTwoComponentInputHe) :
    ∃ T : Subgroup X, IsSylowTwoIn T (normalizer (W : Set X)) ∧ a ∈ T ∧
      IsSylowTwoIn (T ⊓ normalizer (K : Set X))
        (normalizer (W : Set X) ⊓ normalizer (K : Set X)) ∧
      IsSylowTwoIn (T ⊓ centralizer ({a} : Set X)) (centralizer ({a} : Set X)) := by
  obtain ⟨S₁, hS₁, haS₁⟩ := exists_isSylowTwoIn_mem
    (mem_centralizer_singleton_iff.mpr rfl : a ∈ centralizer ({a} : Set X)) h.orderOf_eq
  have hCK : centralizer ({a} : Set X) ≤ normalizer (K : Set X) :=
    (h.centralizer_le_normalizer hMax).trans h.normalizer_L_le
  have hS₁H : S₁ ≤ normalizer (W : Set X) ⊓ normalizer (K : Set X) :=
    le_inf (hS₁.1.trans (h.centralizer_le hMax)) (hS₁.1.trans hCK)
  obtain ⟨T₁, hT₁, hS₁T₁⟩ := exists_isSylowTwoIn_le hS₁H hS₁.isPGroup
  obtain ⟨T, hT, hT₁T⟩ := exists_isSylowTwoIn_le (hT₁.1.trans inf_le_left) hT₁.isPGroup
  have hT2 := hT.isPGroup
  have h1 : T ⊓ normalizer (K : Set X) = T₁ :=
    hT₁.eq_of_le (le_inf hT₁T (hT₁.1.trans inf_le_right))
      (inf_le_inf_right _ hT.1) (hT2.to_le inf_le_left)
  have h2 : T ⊓ centralizer ({a} : Set X) = S₁ :=
    hS₁.eq_of_le (le_inf (hS₁T₁.trans hT₁T) hS₁.1) inf_le_right (hT2.to_le inf_le_left)
  exact ⟨T, hT, hT₁T (hS₁T₁ haS₁), h1 ▸ hT₁, h2 ▸ hS₁⟩

theorem inf_coreKernel_eq_bot
    (hMax : MaximalTwoComponentInputHe)
    (hS : SchreierFor Blueprint.Catalog) (hHN : HeldNotProperFixedInput)
    (h64 : HeldSylowElementarySixtyFour) (hMult : TBLit.HeldTrivialMultiplier)
    {T : Subgroup X} (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set X)) (haT : a ∈ T)
    (hTK : ¬ T ≤ normalizer (K : Set X)) :
    T ⊓ coreKernel (normalizer (W : Set X)) K = ⊥ := by
  by_contra hne
  have hTn : T ≤ normalizer ((T ⊓ coreKernel (normalizer (W : Set X)) K : Subgroup X) :
      Set X) := by
    intro t ht
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hx).1) (inv_mem ht),
      conj_mem_coreKernel (hTM ht) (mem_inf.mp hx).2⟩
  obtain ⟨z, hzQ, hz2, hzc⟩ := exists_central_involution hT2 inf_le_left hTn hne
  have hzK := mem_coreActionKernel_of_mem_coreKernel (mem_inf.mp hzQ).2
  exact hTK fun t ht =>
    h.mem_normalizer_of_commute hMax hS hHN h64 hMult hz2 (hzc a haT) hzK (hTM ht) (hzc t ht)

end Setting

end CFSG.ComponentClassification.GrSLit.HeSN
