module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LQuat
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LE4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Odd

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b3L

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

theorem map_subgroupOf_subgroupMap {X Y : Type} [Group X] [Group Y] {A B : Subgroup X}
    (hAB : A ≤ B) (π : X →* Y) :
    (A.subgroupOf B).map (π.subgroupMap B) = (A.map π).subgroupOf (B.map π) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact mem_subgroupOf.mpr ⟨c, mem_subgroupOf.mp hc, rfl⟩
  · intro hy
    obtain ⟨l, hl, hly⟩ := mem_map.mp (mem_subgroupOf.mp hy)
    exact ⟨⟨l, hAB hl⟩, mem_subgroupOf.mpr hl, Subtype.ext hly⟩

variable {G : Type} [Group G] [Finite G] {z₁ z₂ : G} {L₁ K : Subgroup G}

omit [Finite G] in
theorem mk_mem_center (hK : K ≤ centralizer {z₁}) (hz₁K : z₁ ∈ K) :
    QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) g
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (mem_centralizer_singleton_iff.mp (hK g.2)))

omit [Finite G] in
theorem mk_mul_self {z : G} (hz : orderOf z = 2) (hzK : z ∈ K) :
    QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z, hzK⟩ * QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z, hzK⟩ =
      1 := by
  rw [← map_mul]
  have : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := by
    apply Subtype.ext
    change z * z = 1
    rw [← pow_two, ← hz, pow_orderOf_eq_one]
  rw [this, map_one]

theorem mk_ne_one {z : G} (hz : orderOf z = 2) (hzK : z ∈ K) :
    QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z, hzK⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have h1 : (⟨z, hzK⟩ : ↥K) = 1 :=
    F3L57.eq_one_of_pow_two_pow_of_mem (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h
      (k := 1) (by
        apply Subtype.ext
        change z ^ 2 ^ 1 = 1
        rw [pow_one, ← hz, pow_orderOf_eq_one])
  have h2 : z = 1 := congrArg Subtype.val h1
  rw [h2, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem exists_quat_config (hz₁ : orderOf z₁ = 2) (hz₂ : orderOf z₂ = 2)
    (hL₁ : IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂})) (hz₁L : z₁ ∈ L₁)
    (he₁ : Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3))) (hK : K ≤ centralizer {z₁})
    (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K) (hz₁K : z₁ ∈ K) (hz₂K : z₂ ∈ K) :
    ∃ Q : Subgroup (↥K ⧸ pPrimeCore 2 ↥K),
      Q ≤ centralizer {QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩} ∧
      (Q.subgroupOf (centralizer {QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩})).IsSubnormal ∧
      IsPGroup 2 (↥Q ⧸ pPrimeCore 2 ↥Q) ∧ Group.IsSolvable (↥Q ⧸ pPrimeCore 2 ↥Q) ∧
      ∃ a ∈ Q, ∃ b ∈ Q, a * a = QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∧
        b * b = QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∧
        a * b = QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ * (b * a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he₁
  obtain ⟨hle, hsub⟩ := range_iota_subnormal hz₂ hL₁ hK hO₁ hz₂K
  obtain ⟨-, z, a, b, hz₁z, -, haa, hbb, hab⟩ :=
    exists_sylow_data hz₁ hz₁L (hL₁.1.trans inf_le_left) e
  have hp := isPGroup_range_quotient (iota hO₁) (psi e) (odd_card_ker_psi e) (psi_pow_eight e)
  have hc : iota hO₁ z = QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ := by
    rw [iota_apply]
    congr 1
    exact Subtype.ext (by rw [coe_toK]; exact hz₁z)
  have := hp.isNilpotent
  refine ⟨(iota hO₁).range, hle, hsub, hp, inferInstance, iota hO₁ a, ⟨a, rfl⟩, iota hO₁ b,
    ⟨b, rfl⟩, ?_, ?_, ?_⟩
  · rw [← map_mul, haa, hc]
  · rw [← map_mul, hbb, hc]
  · rw [← map_mul, ← map_mul, hab, map_mul, hc]

theorem field_eq_one (h51E4 : Harris82Lemma51E4) (hz₁ : orderOf z₁ = 2) (hz₂ : orderOf z₂ = 2)
    (hL₁ : IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂})) (hz₁L : z₁ ∈ L₁)
    (he₁ : Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)))
    (hKc : IsTwoComponentIn K (centralizer {z₁})) (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K)
    (hz₂K : z₂ ∈ K)
    (hz₂Z : (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K))
    {τ : StatedLieTag} {n f : ℕ} (hm : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) τ n 3 f) :
    f = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he₁
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, -, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hX.2.1
  have hι := odd_card_ker_iota hO₁
  have hψ := odd_card_ker_psi e
  have hψ8 := psi_pow_eight e
  obtain ⟨hsurj, z, -, -, hz₁z, hz, -⟩ := exists_sylow_data hz₁ hz₁L (hL₁.1.trans inf_le_left) e
  obtain ⟨hle, hsub⟩ := range_iota_subnormal hz₂ hL₁ hKc.1 hO₁ hz₂K
  have hzZ : iota hO₁ z ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    have hc : iota hO₁ z = QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ := by
      rw [iota_apply]
      congr 1
      exact Subtype.ext (by rw [coe_toK]; exact hz₁z)
    rw [hc]
    exact mk_mem_center hKc.1 hz₁K
  set t : ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩ with ht_def
  have ht : t * t = 1 := mk_mul_self hz₂ hz₂K
  have htZ : t ∉ center (↥K ⧸ pPrimeCore 2 ↥K) := hz₂Z
  have htM : ∀ m, iota hO₁ m * t = t * iota hO₁ m := fun m =>
    mem_centralizer_singleton_iff.mp (hle ⟨m, rfl⟩)
  set π := QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)) with hπ
  have hR4 := isKleinFour_range (iota hO₁) (psi e) hι hψ hψ8 hsurj hz hzZ
  have htR := not_mem_range (iota hO₁) (psi e) hι hψ hψ8 hsurj hz hzZ ht htZ htM
  have ht2 : orderOf (π t) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, ht, map_one]
    · rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htZ
  have hCle : (centralizer {t}).map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hx]
  have hR : (π.comp (iota hO₁)).range = (iota hO₁).range.map π := MonoidHom.range_comp _ _
  have hRC : (π.comp (iota hO₁)).range ≤ centralizer {π t} := by
    rw [hR]
    exact (map_mono hle).trans hCle
  have hRsub : ((π.comp (iota hO₁)).range.subgroupOf (centralizer {π t})).IsSubnormal := by
    have hN := P58b.normal_map_centralizer_of_ker π (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) t
    have h1 : (((iota hO₁).range.map π).subgroupOf ((centralizer {t}).map π)).IsSubnormal := by
      rw [← map_subgroupOf_subgroupMap hle π]
      exact hsub.map (MonoidHom.subgroupMap_surjective _ _)
    rw [hR]
    exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans (map_mono hle) hCle h1 hN.isSubnormal
  have h3 := h51E4 _ τ n 3 f Nat.prime_three (by norm_num) hmX (π t) ht2 _ hRC hRsub htR hR4
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h3.trans (pow_one 3).symm)

end CFSG.ComponentClassification.HarrisLit.T1.P58b3L
