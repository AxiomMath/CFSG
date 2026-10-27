module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CenterAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

theorem conj_mem_zpowers_of_zpowers_zeta {Y : Type*} [Group Y] {ζ ŵ t : Y} (hŵo : orderOf ŵ = 3)
    (hζ1 : ζ ≠ 1) (hζw : ζ ∈ Subgroup.zpowers ŵ) (ht : t * ζ * t⁻¹ ∈ Subgroup.zpowers ζ) :
    t * ŵ * t⁻¹ ∈ Subgroup.zpowers ŵ := by
  have hle : Subgroup.zpowers ζ ≤ Subgroup.zpowers ŵ := by
    rw [Subgroup.zpowers_le]; exact hζw
  have hŵ3 : ŵ ^ 3 = 1 := by
    have := pow_orderOf_eq_one ŵ
    rwa [hŵo] at this
  have hζ3 : ζ ^ 3 = 1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hŵ3, one_zpow]
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hcard : Nat.card (Subgroup.zpowers ŵ) ≤ Nat.card (Subgroup.zpowers ζ) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hŵo, hζo]
  have heq : Subgroup.zpowers ζ = Subgroup.zpowers ŵ := by
    have : Finite (Subgroup.zpowers ŵ) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [Nat.card_zpowers, hŵo]; norm_num
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  have hŵζ : ŵ ∈ Subgroup.zpowers ζ := by rw [heq]; exact Subgroup.mem_zpowers ŵ
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hŵζ
  have h1 : t * ŵ * t⁻¹ = (t * ζ * t⁻¹) ^ j := by rw [← hj]; simp [conj_zpow]
  rw [h1]
  exact Subgroup.zpow_mem _ (heq ▸ ht) j

theorem conj_eq_inv_of_zpowers {Y : Type*} [Group Y] {ζ ŵ t : Y}
    (hζw : ζ ∈ Subgroup.zpowers ŵ) (hinv : t * ŵ * t⁻¹ = ŵ⁻¹) : t * ζ * t⁻¹ = ζ⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζw
  rw [← conj_zpow, hinv, inv_zpow]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_axis_mem_zpowers_of_mk {P : Sylow 3 G} {M R : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hRP : R ≤ (P : Subgroup G)) {w z t : G} (hwR : w ∈ R)
    (hwo : orderOf w = 3) (hwz : w ∉ Subgroup.zpowers z) (hzR : z ∈ R)
    (hwc : ∀ g ∈ R, Commute w g)
    (hΩR : ∀ g ∈ R, (∀ h ∈ R, Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers z)
    (htR : t ∈ Subgroup.normalizer (R : Set G)) (htM : t ∈ M)
    (hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hPM (hRP hwR)⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩)⁻¹ ∈
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hPM (hRP hwR)⟩)) :
    t * w * t⁻¹ ∈ Subgroup.zpowers w := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkdef
  have hwM : w ∈ M := hPM (hRP hwR)
  have hzM : z ∈ M := hPM (hRP hzR)
  have hP3 : IsPGroup 3 ((P : Subgroup G).subgroupOf M) := P.isPGroup'.comap_subtype
  have hinj : ∀ a b : ↥M, (a : G) ∈ (P : Subgroup G) → (b : G) ∈ (P : Subgroup G) →
      mk a = mk b → a = b := fun a b ha hb hab =>
    eq_of_mk_pCore_two_eq_of_isPGroup_three hP3 ha hb hab
  set ν := t * w * t⁻¹ with hν
  have hνR : ν ∈ R := (Subgroup.mem_normalizer_iff.mp htR w).mp hwR
  have hνc : ∀ g ∈ R, Commute ν g := by
    intro g hg
    have hg' : t⁻¹ * g * t ∈ R :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem htR) g).mp hg
        |> fun h => by simpa using h
    have h1 := (hwc _ hg').eq
    calc ν * g = t * (w * (t⁻¹ * g * t)) * t⁻¹ := by simp [hν, mul_assoc]
      _ = t * ((t⁻¹ * g * t) * w) * t⁻¹ := by rw [h1]
      _ = g * ν := by simp [hν, mul_assoc]
  have hν3 : ν ^ 3 = 1 := by
    have hw3 : w ^ 3 = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hwo] at this
    rw [hν, conj_pow, hw3, mul_one, mul_inv_cancel]
  have hΩν := hΩR ν hνR hνc hν3
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff (hwc z hzR)).mp hΩν
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hνM : ν ∈ M := by rw [← huv]; exact M.mul_mem (M.zpow_mem hwM a) (M.zpow_mem hzM b)
  have hmkν : mk ⟨t, htM⟩ * mk ⟨w, hwM⟩ * (mk ⟨t, htM⟩)⁻¹ =
      mk ⟨w, hwM⟩ ^ a * mk ⟨z, hzM⟩ ^ b := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_zpow, ← map_zpow, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    simpa [hν] using huv.symm
  have hmk' : mk ⟨w, hwM⟩ ^ a * mk ⟨z, hzM⟩ ^ b ∈ Subgroup.zpowers (mk ⟨w, hwM⟩) := by
    rw [← hmkν]; exact hmk
  have hzb : mk ⟨z, hzM⟩ ^ b ∈ Subgroup.zpowers (mk ⟨w, hwM⟩) :=
    (Subgroup.mul_mem_cancel_left _ (Subgroup.zpow_mem_zpowers _ _)).mp hmk'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzb
  have hjb : (⟨w, hwM⟩ : ↥M) ^ j = (⟨z, hzM⟩ : ↥M) ^ b := by
    refine hinj _ _ ?_ ?_ ?_
    · exact (P : Subgroup G).zpow_mem (hRP hwR) j
    · exact (P : Subgroup G).zpow_mem (hRP hzR) b
    · rw [map_zpow, map_zpow]; exact hj
  have hjb' : w ^ j = z ^ b := by simpa using congrArg Subtype.val hjb
  have hbot : Subgroup.zpowers w ⊓ Subgroup.zpowers z = ⊥ :=
    zpowers_inf_eq_bot_of_not_mem' Nat.prime_three hwo hwz
  have hz1 : z ^ b = 1 := by
    have : z ^ b ∈ Subgroup.zpowers w ⊓ Subgroup.zpowers z :=
      ⟨hjb' ▸ Subgroup.zpow_mem_zpowers _ _, Subgroup.zpow_mem_zpowers _ _⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [← huv, hz1, mul_one]
  exact Subgroup.zpow_mem_zpowers _ _

end CFSG.LocalAnalysis.RankThreeTheoremC
