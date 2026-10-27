module

public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralKernel
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem center_eq_bot_of_isQuasisimple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : IsQuasisimple Q) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨u, v, huv⟩ := hQ.2.2
    induction u using QuotientGroup.induction_on with | H x => ?_
    induction v using QuotientGroup.induction_on with | H y => ?_
    have hx : x ∈ center Q := h ▸ mem_top x
    apply huv
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hx y]

theorem fixedSubgroup_conj {G : Type*} [Group G] (s : G) :
    fixedSubgroup (MulAut.conj s) = centralizer ({s} : Set G) := by
  ext x
  rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, MulAut.conj_apply,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * s = s * x * s⁻¹ * s := by rw [h]
      _ = s * x := by group
  · intro h
    calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [h]
      _ = x := by group

theorem map_oddCoreIn_le {H H' : Type*} [Group H] [Group H'] [Finite H] (φ : H →* H')
    (X : Subgroup H) : (oddCoreIn X).map φ ≤ oddCoreIn (X.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold oddCoreIn
  rw [map_map, ← OddQuot.subtype_comp_subgroupMap, ← map_map]
  exact map_mono (CFSG.map_pPrimeCore_le (φ.subgroupMap X) (φ.subgroupMap_surjective X))

section CentralKernel

variable {L S : Type*} [Group L] [Group S] [Finite L] {π : L →* S}

theorem not_two_dvd_card_ker (hK : π.ker ≤ center L) {M : Subgroup L}
    (hZ : center (M ⧸ pPrimeCore 2 M) = ⊥) : ¬ 2 ∣ Nat.card (π.domRestrict M).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (π.domRestrict M).ker ≤ pPrimeCore 2 M := by
    intro x hx
    have hxZ : (x : L) ∈ center L := hK (by rw [MonoidHom.mem_ker] at hx ⊢; exact hx)
    rw [← QuotientGroup.eq_one_iff, ← mem_bot, ← hZ, mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (mem_center_iff.mp hxZ y))
  intro h2
  exact (Nat.not_even_iff_odd.mpr OddQuot.odd_card_pPrimeCore)
    (even_iff_two_dvd.mpr (h2.trans (card_dvd_of_le hle)))

variable [Finite S] {a : MulAut L} {α : MulAut S}

theorem isPComponent_map_fixed (hK : π.ker ≤ center L) (hπ : Function.Surjective π)
    (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x)) {M : Subgroup L}
    (hMa : M ≤ fixedSubgroup a) (hM : IsPComponent 2 (M.subgroupOf (fixedSubgroup a)))
    (hMk : ¬ 2 ∣ Nat.card (π.domRestrict M).ker) :
    M.map π ≤ fixedSubgroup α ∧ IsPComponent 2 ((M.map π).subgroupOf (fixedSubgroup α)) ∧
      Nonempty (M ⧸ pPrimeCore 2 M ≃* (M.map π) ⧸ pPrimeCore 2 (M.map π)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIα : (fixedSubgroup a).map π ≤ fixedSubgroup α := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff] at hx ⊢
    rw [← hcomm, hx]
  have hMI : M.map π ≤ (fixedSubgroup a).map π := map_mono hMa
  obtain ⟨e, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv (p := 2) π M hMk
  refine ⟨hMI.trans hIα, ?_, ⟨e⟩⟩
  have hnorm := LocalAnalysis.ComponentInitial.fixedImage_normal hK hπ ha hcomm
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hMI hIα hnorm.isSubnormal]
  obtain ⟨hsub, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMa).mp hM
  refine (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hMI).mpr ⟨?_, ?_, ?_⟩
  · rw [← OddQuot.map_subgroupOf_subgroupMap π hMa]
    exact hsub.map (π.subgroupMap_surjective _)
  · rw [← CatalogueBPrimeJoin.primeResidual_map_surjective 2 (π.subgroupMap M)
      (π.subgroupMap_surjective M), hres]
    exact map_top_of_surjective _ (π.subgroupMap_surjective M)
  · exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mp hq

end CentralKernel

end CFSG.ComponentClassification.GSThmB.Pump516
