module

public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.WP2Stand
public import CFSG.ClassicalInvolution.AschTight.TzFusion

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.T6A

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

structure Setup194 (p f : ℕ) [Fact p.Prime] (K : Subgroup G) (z : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  member : IsClassicalMember p f K z
  nonabelian : ∃ x y : G, x * y ≠ y * x
  edgeless : DEdgeless (CoreAssembly.conjClass K)
  normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G)

namespace Setup194

variable {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G} (ht : Setup194 p f K z)
include ht

omit [Finite G] in
theorem le_centralizer : K ≤ Subgroup.centralizer ({z} : Set G) :=
  isSubnormal_le ht.member.subnormal

theorem uniqueInvolutionNormal : UniqueInvolutionNormal K z := by
  let Q : Sylow 2 K := Classical.choice Sylow.nonempty
  exact uniqueInvolutionNormal_of_quaternion_sylow ht.member.orderOf_eq_two ht.member.mem
    ht.le_centralizer ((Subgroup.normal_subgroupOf_iff_le_normalizer ht.le_centralizer).mpr
      ht.normEq.ge) Q (quaternion_sylow_of_isClassicalMember ht.odd ht.five ht.member Q)

theorem isUniqueInvolution : IsUniqueInvolution K z := by
  have hU := ht.uniqueInvolutionNormal
  refine ⟨hU.2.1, ?_, ?_, ?_⟩
  · intro h
    have h2 := hU.1
    rw [h, orderOf_one] at h2
    omega
  · rw [← sq, ← hU.1, pow_orderOf_eq_one]
  · intro y hy hy2
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (hU.2.2.1 y hy (orderOf_eq_prime (by rw [sq]; exact hy2) h1))

omit [Finite G] in
theorem conjSub_eq_conjSub {a b : G} (h : a * z * a⁻¹ = b * z * b⁻¹) :
    conjSub a K = conjSub b K := by
  have hn : b⁻¹ * a ∈ Subgroup.normalizer (K : Set G) := by
    rw [ht.normEq, Subgroup.mem_centralizer_singleton_iff]
    calc b⁻¹ * a * z = b⁻¹ * (a * z * a⁻¹) * a := by group
      _ = b⁻¹ * (b * z * b⁻¹) * a := by rw [h]
      _ = z * (b⁻¹ * a) := by group
  calc conjSub a K = conjSub b (conjSub (b⁻¹ * a) K) := by rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub b K := by rw [conjSub_eq_of_mem_normalizer hn]

theorem mem_normalizer_of_commute {K₁ : Subgroup G} (hK₁ : K₁ ∈ CoreAssembly.conjClass K)
    {z₁ : G} (hz₁ : IsUniqueInvolution K₁ z₁) {v : G} (hv : v * z₁ = z₁ * v) :
    v ∈ Subgroup.normalizer (K₁ : Set G) := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K K₁ hK₁
  obtain rfl : z₁ = a * z * a⁻¹ := hz₁.eq (ht.isUniqueInvolution.conj a)
  have hconj : conjSub v (conjSub a K) = conjSub a K := by
    rw [← conjSub_mul]
    apply ht.conjSub_eq_conjSub
    calc v * a * z * (v * a)⁻¹ = v * (a * z * a⁻¹) * v⁻¹ := by group
      _ = a * z * a⁻¹ * v * v⁻¹ := by rw [hv]
      _ = a * z * a⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx : v * x * v⁻¹ ∈ conjSub v (conjSub a K) ↔ x ∈ conjSub a K := by
    rw [mem_conjSub_iff]
    simp [mul_assoc]
  rw [hconj] at hx
  exact hx.symm

theorem mem_of_isSylow2Of {P : Subgroup G} (hP : IsSylow2Of P K) : z ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := ht.uniqueInvolutionNormal
  have h2K : 2 ∣ Nat.card K := by
    have h := Subgroup.orderOf_dvd_natCard K hU.2.1
    rwa [hU.1] at h
  have hPcard := hP.card_eq
  have h2P : 2 ∣ Nat.card P := by
    rw [hPcard]
    have hpos : 0 < (Nat.card K).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2K
    exact dvd_pow_self 2 hpos.ne'
  obtain ⟨⟨x, hxP⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2P
  have hx2' : orderOf x = 2 := by rw [← Subgroup.orderOf_mk x hxP]; exact hx2
  rw [← hU.2.2.1 x (hP.1 hxP) hx2']
  exact hxP

theorem isUniqueInvolution_of_mem_rSet_of_le {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) : IsUniqueInvolution R z := by
  have hI := ht.isUniqueInvolution
  have h8 := (exists_ne_comm_of_mem_rSet ht.odd ht.five ht.member hR).2
  obtain ⟨k, hk⟩ := (isPGroup_of_mem_rSet hR).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk, pow_zero] at h8
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have huz : (u : G) = z := ht.uniqueInvolutionNormal.2.2.1 _ (hRK u.2) hu'
  exact ⟨huz ▸ u.2, hI.ne_one, hI.sq, fun y hy hy2 => hI.unique y (hRK hy) hy2⟩

theorem mem_omegaNbr_of_commuting_sylow {g : G}
    (hg : g ∉ Subgroup.normalizer (K : Set G)) {P₁ P₂ : Subgroup G} (hP₁ : IsSylow2Of P₁ K)
    (hP₂ : IsSylow2Of P₂ (conjSubgroup g K)) (hcomm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) :
    conjSubgroup g K ∈ Asc77.omegaNbr (CoreAssembly.conjClass K) K := by
  have hzP₁ := ht.mem_of_isSylow2Of hP₁
  obtain ⟨T, hT⟩ := hP₂.exists_sylow
  refine ⟨⟨g, rfl⟩, fun h => hg (conjSubgroup_eq_self_iff.mp h), P₂,
    ⟨conjSubgroup g K, ⟨g, rfl⟩, T, hT.symm⟩, hP₂.1, ?_⟩
  intro y hy
  rw [ht.normEq, Subgroup.mem_centralizer_singleton_iff]
  exact (hcomm z hzP₁ y hy).symm

theorem conjSubgroup_sylow_eq (Q : Sylow 2 K) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hQS : (Q : Subgroup K).map K.subtype ≤ S) {g : G}
    (hgS : conjSubgroup g ((Q : Subgroup K).map K.subtype) ≤ S) :
    conjSubgroup g ((Q : Subgroup K).map K.subtype) = (Q : Subgroup K).map K.subtype := by
  have hU := ht.uniqueInvolutionNormal
  have hQq := quaternion_sylow_of_isClassicalMember ht.odd ht.five ht.member Q
  have hzQ : z ∈ (Q : Subgroup K).map K.subtype :=
    ht.mem_of_isSylow2Of (isSylow2Of_map_subtype Q)
  by_contra hne
  have h1 : conjSubgroup 1 ((Q : Subgroup K).map K.subtype) ≤ S := by
    rw [conjSubgroup_one]
    exact hQS
  have hne' : conjSubgroup 1 ((Q : Subgroup K).map K.subtype) ≠
      conjSubgroup g ((Q : Subgroup K).map K.subtype) := by
    rw [conjSubgroup_one]
    exact fun h => hne h.symm
  obtain ⟨hbot, hcomm⟩ := quaternion_conjugates_commute Q hQq hzQ hU.1 hU.2.2.2.1 hU.2.2.2.2 hS
    hQS h1 hgS hne'
  rw [conjSubgroup_one] at hbot hcomm
  by_cases hg : g ∈ Subgroup.normalizer (K : Set G)
  · have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [← ht.normEq]
      exact hg
    have hz' : z ∈ conjSubgroup g ((Q : Subgroup K).map K.subtype) := by
      have h := mem_conjSubgroup_of_mem (g := g) hzQ
      rwa [show g * z * g⁻¹ = z by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hgz]; group] at h
    have hz1 : z ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_inf.mpr ⟨hzQ, hz'⟩
    rw [Subgroup.mem_bot] at hz1
    have h2 := hU.1
    rw [hz1] at h2
    simp at h2
  · exact absurd (Or.inl (ht.mem_omegaNbr_of_commuting_sylow hg (isSylow2Of_map_subtype Q)
      ((isSylow2Of_map_subtype Q).conj g) hcomm))
      (ht.edgeless K (CoreAssembly.mem_conjClass_self K) _ ⟨g, rfl⟩)

end Setup194

variable {p f : ℕ} [Fact p.Prime]

theorem eq_conjClass {Ω : Set (Subgroup G)} {K : Subgroup G} (hs : AscStand p f Ω K) :
    Ω = CoreAssembly.conjClass K := by
  ext J
  constructor
  · intro hJ
    obtain ⟨g, hg⟩ := hs.trans J hJ
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact hs.hyp.conjInvariant g K hs.mem

theorem setup194_of_stand {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
    (hs : AscStand p f Ω K) (he : DEdgeless Ω) (hz : IsUniqueInvolution K z) :
    Setup194 p f K z := by
  have hΩ := eq_conjClass hs
  obtain ⟨z', hz'⟩ := hs.hyp.classical K hs.mem
  have hz'1 : z' ≠ 1 := by
    intro h1
    have h2 := hz'.orderOf_eq_two
    rw [h1, orderOf_one] at h2
    omega
  have hz'2 : z' * z' = 1 := by rw [← sq, ← hz'.orderOf_eq_two, pow_orderOf_eq_one]
  obtain rfl : z' = z := (hz.unique z' hz'.mem hz'2).resolve_left hz'1
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hR : (Q : Subgroup K).map K.subtype ∈ RSet (CoreAssembly.conjClass K) :=
    ⟨K, CoreAssembly.mem_conjClass_self K, Q, rfl⟩
  obtain ⟨x, -, y, -, hxy⟩ := (exists_ne_comm_of_mem_rSet hs.odd hs.five hz' hR).1
  refine ⟨hs.odd, hs.five, hz', ⟨x, y, hxy⟩, hΩ ▸ he, le_antisymm ?_ ?_⟩
  · intro n hn
    have hmem : n * z' * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn z').mp hz.mem
    have h2 : n * z' * n⁻¹ * (n * z' * n⁻¹) = 1 := by
      calc n * z' * n⁻¹ * (n * z' * n⁻¹) = n * (z' * z') * n⁻¹ := by group
        _ = 1 := by rw [hz'2]; group
    have h1 : n * z' * n⁻¹ ≠ 1 := fun h => hz'1 (by
      calc z' = n⁻¹ * (n * z' * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group)
    have h := (hz.unique _ hmem h2).resolve_left h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * z' = n * z' * n⁻¹ * n := by group
      _ = z' * n := by rw [h]
  · intro c hc
    have hcz : c * z' * c⁻¹ = z' := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
    have hKc : conjSub c K ∈ Ω := hs.hyp.conjInvariant c K hs.mem
    have hzc : IsUniqueInvolution (conjSub c K) z' := hcz ▸ hz.conj c
    rcases Set.mem_insert_iff.mp (mem_kPerp_of_twin hs.hyp hKc hs.mem hzc hz) with h | h
    · exact mem_normalizer_iff_conjSub_eq.mpr h
    · exact absurd (Or.inl h) (he K hs.mem _ hKc)

end CFSG.ClassicalInvolution.Disconnected.AschTight.T6A
