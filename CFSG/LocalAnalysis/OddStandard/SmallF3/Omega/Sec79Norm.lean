module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem exists_conj_involution_of_cyclic_sylow [Finite G] {K : Subgroup G}
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P K → IsCyclic P) {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : ∃ k ∈ K, k * a * k⁻¹ = b := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (↥K)) := inferInstance
  have hP' : IsSylow2Of (((P : Subgroup ↥K).map K.subtype)) K := isSylow2Of_map_sylow P
  have hPcyc : IsCyclic ↥(((P : Subgroup ↥K).map K.subtype)) := hcyc _ hP'
  haveI : IsCyclic ↥(((P : Subgroup ↥K).map K.subtype)) := hPcyc
  have hAcard : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, ha2]
  have hA : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [hAcard]; norm_num)
  have hAK : Subgroup.zpowers a ≤ K := by
    rw [Subgroup.zpowers_le]; exact ha
  obtain ⟨c₁, hc₁K, hc₁⟩ := exists_conj_le_of_isSylow2Of hP' hA hAK
  have hBcard : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers, hb2]
  have hB : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [hBcard]; norm_num)
  have hBK : Subgroup.zpowers b ≤ K := by
    rw [Subgroup.zpowers_le]; exact hb
  obtain ⟨c₂, hc₂K, hc₂⟩ := exists_conj_le_of_isSylow2Of hP' hB hBK
  have hu_mem : c₁ * a * c₁⁻¹ ∈ ((P : Subgroup ↥K).map K.subtype) :=
    hc₁ a (Subgroup.mem_zpowers a)
  have hv_mem : c₂ * b * c₂⁻¹ ∈ ((P : Subgroup ↥K).map K.subtype) :=
    hc₂ b (Subgroup.mem_zpowers b)
  have hu2 : orderOf (c₁ * a * c₁⁻¹) = 2 := by
    rw [show c₁ * a * c₁⁻¹ = (MulAut.conj c₁) a by simp [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq, ha2]
  have hv2 : orderOf (c₂ * b * c₂⁻¹) = 2 := by
    rw [show c₂ * b * c₂⁻¹ = (MulAut.conj c₂) b by simp [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq, hb2]
  have heq : (⟨c₁ * a * c₁⁻¹, hu_mem⟩ : ↥(((P : Subgroup ↥K).map K.subtype))) =
      ⟨c₂ * b * c₂⁻¹, hv_mem⟩ :=
    eq_of_commuting_involutions_of_cyclic_sylow (fun Q => inferInstance)
      (by rw [Subgroup.orderOf_mk]; exact hu2)
      (by rw [Subgroup.orderOf_mk]; exact hv2) (mul_comm' _ _)
  have hval : c₁ * a * c₁⁻¹ = c₂ * b * c₂⁻¹ := congrArg Subtype.val heq
  refine ⟨c₂⁻¹ * c₁, K.mul_mem (K.inv_mem hc₂K) hc₁K, ?_⟩
  calc (c₂⁻¹ * c₁) * a * (c₂⁻¹ * c₁)⁻¹
      = c₂⁻¹ * (c₁ * a * c₁⁻¹) * c₂ := by group
    _ = c₂⁻¹ * (c₂ * b * c₂⁻¹) * c₂ := by rw [hval]
    _ = b := by group

theorem sec7_normalizer_decomp [Finite G] (h72 : Asc82Lemma72) {t : G} {L S : Subgroup G}
    {z : G} (hctx : Sec7Ctx G t L S z) :
    ∀ n ∈ normalizer (L : Set G), ∃ h ∈ centralizer ({t} : Set G),
      ∃ c ∈ centralizer (L : Set G), n = h * c := by
  intro n hn
  classical
  have hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P :=
    h72 G t L hctx.toSec3SettingLB hctx.omega6
  have ht'C : n⁻¹ * t * n ∈ centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have hmem : n * l * n⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hn l).mp hl
    have hcomm : (n * l * n⁻¹) * t = t * (n * l * n⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hctx.le_centralizer hmem)
    calc l * (n⁻¹ * t * n) = n⁻¹ * (n * l * n⁻¹) * t * n := by group
      _ = n⁻¹ * (t * (n * l * n⁻¹)) * n := by
        simpa only [mul_assoc] using congrArg (fun x => n⁻¹ * x * n) hcomm
      _ = (n⁻¹ * t * n) * l := by group
  have ht'2 : orderOf (n⁻¹ * t * n) = 2 := by
    rw [show n⁻¹ * t * n = (MulAut.conj n⁻¹) t by simp [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq, hctx.involution]
  obtain ⟨k, hkK, hk⟩ := exists_conj_involution_of_cyclic_sylow hcyc
    hctx.t_mem_centralizer ht'C hctx.involution ht'2
  refine ⟨n * k, ?_, k⁻¹, (centralizer (L : Set G)).inv_mem hkK, by group⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc (n * k) * t = n * (k * t * k⁻¹) * k := by group
    _ = n * (n⁻¹ * t * n) * k := by rw [hk]
    _ = t * (n * k) := by group

end CFSG.OddStandard.SmallF3.Omega
