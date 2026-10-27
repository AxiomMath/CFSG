module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TypeIExteriorFixedElementPowers
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem conj_mem_hallCoreIn {M : Subgroup G} {y m : G} (hm : m ∈ M)
    (hy : y ∈ hallCoreIn M) : m⁻¹ * y * m ∈ hallCoreIn M := by
  rw [hallCoreIn_def] at hy ⊢
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨(⟨m, hm⟩ : M)⁻¹ * y' * ⟨m, hm⟩, ?_, by simp⟩
  simpa using hallCore_normal.conj_mem _ hy' ((⟨m, hm⟩ : M)⁻¹)

theorem conj_mem_hallCoreIn_iff {M : Subgroup G} {y m : G} (hm : m ∈ M) :
    m⁻¹ * y * m ∈ hallCoreIn M ↔ y ∈ hallCoreIn M := by
  refine ⟨fun h => ?_, conj_mem_hallCoreIn hm⟩
  simpa [mul_assoc] using conj_mem_hallCoreIn (M.inv_mem hm) h

theorem conj_mem_exteriorFixedSet {M : Subgroup G} {y m : G} (hm : m ∈ M)
    (hy : y ∈ exteriorFixedSet (hallCoreIn M) M) :
    m⁻¹ * y * m ∈ exteriorFixedSet (hallCoreIn M) M := by
  obtain ⟨hyM, hyH, hyc⟩ := hy
  refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hm) hyM) hm, ?_, ?_⟩
  · exact fun h => hyH ((conj_mem_hallCoreIn_iff hm).1 h)
  ·
    obtain ⟨x, hx, hx1⟩ :=
      (centIn (hallCoreIn M) {y}).nontrivial_iff_exists_ne_one.1
        ((centIn (hallCoreIn M) {y}).nontrivial_iff_ne_bot.2 hyc)
    have hxH : x ∈ hallCoreIn M := (mem_centIn.1 hx).1
    have hxc : y * x = x * y := (mem_centIn.1 hx).2 y rfl
    refine (centIn (hallCoreIn M) {m⁻¹ * y * m}).nontrivial_iff_ne_bot.1
      ((centIn (hallCoreIn M) {m⁻¹ * y * m}).nontrivial_iff_exists_ne_one.2
        ⟨m⁻¹ * x * m, mem_centIn.2 ⟨conj_mem_hallCoreIn hm hxH, ?_⟩, ?_⟩)
    · intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      calc m⁻¹ * y * m * (m⁻¹ * x * m) = m⁻¹ * (y * x) * m := by group
        _ = m⁻¹ * (x * y) * m := by rw [hxc]
        _ = m⁻¹ * x * m * (m⁻¹ * y * m) := by group
    · intro h
      apply hx1
      have hxconj : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
      rw [hxconj, h]
      group

theorem FTS_type_I_exterior_ti
    (h₁ : Statements.FTS_type_I_complement_structure.{u})
    (h₂ : Statements.FTS_type_I_core_kappa_identity.{u}) :
    Statements.FTS_type_I_exterior_ti.{u} := by
  intro G _ _ hG M hM hMI hD
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hMN : Subgroup.normalizer (M : Set G) = M :=
    normalizer_coe_eq_of_isCoatom_of_oddOrder_of_proper_solvable hG.not_isMulCommutative
      hG.odd_natCard hG.isSolvable_of_ne_top hM
  have hcard : Nat.card (hallCoreIn M) = Nat.card (hallCore ↥M) := by
    rw [hallCoreIn_def, Subgroup.card_subtype]
  have hidx : (hallCoreIn M).relIndex M = (hallCore ↥M).index := relIndex_hallCoreIn M
  have hab : (Nat.card (hallCoreIn M)).Coprime ((hallCoreIn M).relIndex M) := by
    rw [hcard, hidx]; exact isGreatest_hallCore.1.2.2
  obtain ⟨k, hk0, hk1⟩ := Nat.chineseRemainder hab 0 1
  have hak : Nat.card (hallCoreIn M) ∣ k := Nat.modEq_zero_iff_dvd.1 hk0
  have hpow := FTS_type_I_exterior_power_centralizer h₁ h₂ G hG M hM hMI k hak hk1
  have hle : ∀ d ∈ exteriorFixedSet (hallCoreIn M) M,
      Subgroup.centralizer {d ^ k} ≤ M := fun d hd => (hpow d hd).2.2.2.le
  have huniq : ∀ d ∈ exteriorFixedSet (hallCoreIn M) M, ∀ K : Subgroup G, IsCoatom K →
      Subgroup.centralizer {d ^ k} ≤ K → K = M :=
    fun d hd K hK hKle => (hpow d hd).2.2.2.eq_of_isCoatom hK hKle
  have hstab : ∀ m ∈ M, (fun d => m⁻¹ * d * m) '' exteriorFixedSet (hallCoreIn M) M ⊆
      exteriorFixedSet (hallCoreIn M) M := by
    rintro m hm y ⟨z, hz, rfl⟩
    exact conj_mem_exteriorFixedSet hm hz
  obtain ⟨hnorm, hdisj⟩ :=
    normalizer_eq_and_disjoint_conj_of_isCoatom_centralizer_pow hM hMN hD hstab hle huniq
  refine ⟨hnorm, fun g hg => hdisj g hg, fun y hy z hz g hgz => ?_⟩
  by_contra hgM
  have hmem : z ∈ exteriorFixedSet (hallCoreIn M) M ∩
      (fun d => g⁻¹ * d * g) '' exteriorFixedSet (hallCoreIn M) M := ⟨hz, ⟨y, hy, hgz⟩⟩
  rw [hdisj g hgM] at hmem
  exact hmem

end CFSG.FeitThompson.Proofs

end
