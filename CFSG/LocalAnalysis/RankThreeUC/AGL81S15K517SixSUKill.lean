module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixFam
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixSU6
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixQuot
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517ChevGenQFam

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank

section Node

variable {W : Type} [Group W] [Finite W] {L : Subgroup W} {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}
  {π : K →* ↥L ⧸ Subgroup.center ↥L}

theorem two_le_pRank_of_nodeE9 (hbq : BorelQuotient D n H π M) {A : Subgroup W} (hA : A ≤ L)
    {k : Fin D.rank} (hk : NodeIn (D := D) L A π k) {a b m : K} (ha : a ∈ rankOne D.rootGroup k)
    (hb : b ∈ rankOne D.rootGroup k) (hm : m ∈ rankOne D.rootGroup k) (ha3 : a ^ 3 = 1)
    (ha1 : a ∉ Subgroup.center K) (hb3 : b ^ 3 = 1) (hb1 : b ∉ Subgroup.center K)
    (hma : m * a * m⁻¹ = a⁻¹) (hab : a * b = b * a) (hmb : m * b = b * m) :
    2 ≤ CFSG.Open.pRank 3 A := by
  have hq : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L := by
    rw [QuotientGroup.ker_mk']
  exact two_le_pRank_of_subgroupOf hA (two_le_pRank_of_images hq hbq.ker_central
    (hk ⟨a, ha, rfl⟩) (hk ⟨b, hb, rfl⟩) (hk ⟨m, hm, rfl⟩) ha3 ha1 hb3 hb1 hma hab hmb)

theorem two_le_pRank_of_nodePairE9 (hbq : BorelQuotient D n H π M) {A : Subgroup W} (hA : A ≤ L)
    {k k' : Fin D.rank} (hk : NodeIn (D := D) L A π k) (hk' : NodeIn (D := D) L A π k') {a b m : K}
    (ha : a ∈ rankOne D.rootGroup k) (hm : m ∈ rankOne D.rootGroup k)
    (hb : b ∈ rankOne D.rootGroup k ⊔ rankOne D.rootGroup k') (ha3 : a ^ 3 = 1)
    (ha1 : a ∉ Subgroup.center K) (hb3 : b ^ 3 = 1) (hb1 : b ∉ Subgroup.center K)
    (hma : m * a * m⁻¹ = a⁻¹) (hab : a * b = b * a) (hmb : m * b = b * m) :
    2 ≤ CFSG.Open.pRank 3 A := by
  have hq : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L := by
    rw [QuotientGroup.ker_mk']
  have hjoin : (rankOne D.rootGroup k ⊔ rankOne D.rootGroup k').map π ≤
      (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    rw [Subgroup.map_sup]
    exact sup_le hk hk'
  exact two_le_pRank_of_subgroupOf hA (two_le_pRank_of_images hq hbq.ker_central
    (hk ⟨a, ha, rfl⟩) (hjoin ⟨b, hb, rfl⟩) (hk ⟨m, hm, rfl⟩) ha3 ha1 hb3 hb1 hma hab hmb)

theorem center_quotient_eq_bot (hL : CFSG.Open.IsQuasisimple ↥L) :
    Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
  obtain ⟨hcomm, hsimple⟩ := hL
  haveI : (Subgroup.center (↥L ⧸ Subgroup.center ↥L)).Normal := inferInstance
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ Subgroup.center ↥L)) with h | h
  · exact h
  · exfalso
    have hY : ∀ a b : ↥L ⧸ Subgroup.center ↥L, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
    have hle : commutator ↥L ≤ Subgroup.center ↥L := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun x _ y _ => ?_
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hY _ _)
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hZ : Subgroup.center ↥L = ⊤ := top_le_iff.1 (hcomm ▸ hle)
    obtain ⟨x, y, hxy⟩ := hsimple.exists_pair_ne
    apply hxy
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [(QuotientGroup.eq_one_iff x').2 (hZ ▸ Subgroup.mem_top x'),
      (QuotientGroup.eq_one_iff y').2 (hZ ▸ Subgroup.mem_top y')]

theorem two_le_pRank_of_nodePairHeis (hL : CFSG.Open.IsQuasisimple ↥L)
    (hbq : BorelQuotient D n H π M) {A : Subgroup W} (hA : A ≤ L) {k k' : Fin D.rank}
    (hk : NodeIn (D := D) L A π k) (hk' : NodeIn (D := D) L A π k') {a b : K}
    (ha : a ∈ rankOne D.rootGroup k ⊔ rankOne D.rootGroup k')
    (hb : b ∈ rankOne D.rootGroup k ⊔ rankOne D.rootGroup k') (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hc : ⁅a, b⁆ ∈ Subgroup.center K) (ha1 : a ∉ Subgroup.center K)
    (hind : ∀ (i : ℕ) (z : K), z ∈ Subgroup.center K → b ≠ a ^ i * z) :
    2 ≤ CFSG.Open.pRank 3 A := by
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  have hjoin : (rankOne D.rootGroup k ⊔ rankOne D.rootGroup k').map π ≤
      (A.subgroupOf L).map q := by
    rw [Subgroup.map_sup]
    exact sup_le hk hk'
  obtain ⟨α, hα, hαa⟩ := hjoin ⟨a, ha, rfl⟩
  obtain ⟨β, hβ, hβb⟩ := hjoin ⟨b, hb, rfl⟩
  have hcen := center_quotient_eq_bot hL
  have hker : ∀ z ∈ π.ker, z ∈ Subgroup.center K := hbq.ker_central
  refine two_le_pRank_of_subgroupOf hA (two_le_pRank_three_of_quotient q (A := A.subgroupOf L)
    (α := α) (β := β) hα hβ ?_ ?_ ?_ ?_ ?_)
  · rw [hαa, ← map_pow, ha3, map_one]
  · rw [hβb, ← map_pow, hb3, map_one]
  · rw [hαa, hβb, ← map_mul, ← map_mul]
    have h1 : π ⁅a, b⁆ ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := hbq.surj g
      have := Subgroup.mem_center_iff.1 hc g'
      rw [← map_mul, ← map_mul, this]
    have h2 : π ⁅a, b⁆ = 1 := by
      rw [hcen, Subgroup.mem_bot] at h1
      exact h1
    have h3 : ⁅a, b⁆ = (a * b) * (b * a)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h3, map_mul, map_inv] at h2
    exact mul_inv_eq_one.1 h2
  · rw [hαa]
    intro h
    exact ha1 (hker a (MonoidHom.mem_ker.2 h))
  · rw [hαa, hβb]
    intro h
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h
    have h3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
    have hai : a ^ i = a ^ (i % 3).toNat := by
      calc a ^ i = a ^ (3 * (i / 3) + i % 3) := by rw [Int.mul_ediv_add_emod]
        _ = (a ^ (3 : ℤ)) ^ (i / 3) * a ^ (i % 3) := by rw [zpow_add, ← zpow_mul]
        _ = a ^ (i % 3) := by rw [h3, one_zpow, one_mul]
        _ = a ^ (i % 3).toNat := by
          rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    have h4 : π b = π (a ^ (i % 3).toNat) := by
      rw [← hi, ← hai, map_zpow]
    refine hind (i % 3).toNat ((a ^ (i % 3).toNat)⁻¹ * b) (hker _ (MonoidHom.mem_ker.2 ?_)) (by group)
    rw [map_mul, map_inv, h4, inv_mul_cancel]

end Node


section Pigeon

theorem false_of_triple_classes {ι : Type*} {p₁ p₂ : ι → Prop} {a b c : ι}
    (hcov : ∀ i, p₁ i ∨ p₂ i) (h₁ : ¬ (p₁ a ∧ p₁ b) ∧ ¬ (p₁ a ∧ p₁ c) ∧ ¬ (p₁ b ∧ p₁ c))
    (h₂ : ¬ (p₂ a ∧ p₂ b) ∧ ¬ (p₂ a ∧ p₂ c) ∧ ¬ (p₂ b ∧ p₂ c)) : False := by
  rcases hcov a with ha | ha <;> rcases hcov b with hb | hb <;> rcases hcov c with hc | hc
  · exact h₁.1 ⟨ha, hb⟩
  · exact h₁.1 ⟨ha, hb⟩
  · exact h₁.2.1 ⟨ha, hc⟩
  · exact h₂.2.2 ⟨hb, hc⟩
  · exact h₁.2.2 ⟨hb, hc⟩
  · exact h₂.2.1 ⟨ha, hc⟩
  · exact h₂.1 ⟨ha, hb⟩
  · exact h₂.1 ⟨ha, hb⟩

end Pigeon

section SU

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}
  {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem three_dvd_sq_sub_one (h3 : 3 ∣ 2 ^ f + 1) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ f = c + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  rw [hc] at h3 ⊢
  have : (c + 1) ^ 2 - 1 = c * (c + 2) := by
    have : (c + 1) ^ 2 = c * (c + 2) + 1 := by ring
    omega
  rw [this]
  exact Dvd.dvd.mul_left (by omega) c

theorem false_of_su_odd (hS : IsSylowTwoOf S₀ L) (hcov : CoveredByTwo L S₀ A₁ A₂) (hA₁ : A₁ ≤ L)
    (hA₂ : A₂ ≤ L) (h₁ : CFSG.Open.pRank 3 A₁ ≤ 1) (h₂ : CFSG.Open.pRank 3 A₂ ≤ 1)
    (hF : Nat.card F = (2 ^ f) ^ 2) (h3 : 3 ∣ 2 ^ f + 1) {n : ℕ} (hn : 5 ≤ n) (hodd : Odd n)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* StatedProj (StatedSU n (2 ^ f) F)) : False := by
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
  have hbq := borelQuotient_su hF (by omega) ζ hζ e
  obtain ⟨π', hπ', hcl⟩ := cover_classes hS hcov hbq
  let k : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩
  have hk : ¬ k.val + 1 < n / 2 := by
    show ¬ n / 2 - 1 + 1 < n / 2
    omega
  obtain ⟨a, b, m, ha, hb, hm, ha3, hb3, ha1, hb1, hma, hab, hmb⟩ :=
    su_last_E9 hF hn hodd h3 k hk
  rcases hcl k with h | h
  · have := two_le_pRank_of_nodeE9 hπ' hA₁ h ha hb hm ha3 ha1 hb3 hb1 hma hab hmb
    omega
  · have := two_le_pRank_of_nodeE9 hπ' hA₂ h ha hb hm ha3 ha1 hb3 hb1 hma hab hmb
    omega

theorem false_of_su_even (hS : IsSylowTwoOf S₀ L) (hcov : CoveredByTwo L S₀ A₁ A₂)
    (hA₁ : A₁ ≤ L) (hA₂ : A₂ ≤ L) (h₁ : CFSG.Open.pRank 3 A₁ ≤ 1) (h₂ : CFSG.Open.pRank 3 A₂ ≤ 1)
    (hF : Nat.card F = (2 ^ f) ^ 2) (h3 : 3 ∣ 2 ^ f + 1) {n : ℕ} (hn : 8 ≤ n) (heven : Even n)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* StatedProj (StatedSU n (2 ^ f) F)) : False := by
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
  have hbq := borelQuotient_su hF (by omega) ζ hζ e
  obtain ⟨π', hπ', hcl⟩ := cover_classes hS hcov hbq
  have hdiv : (Unitary.rootDatum hF n).divisible = ∅ := by
    show Unitary.divisible n = ∅
    simp only [Unitary.divisible, if_pos heven]
  have hodd : ∀ i, OddNode (rankOne (Unitary.rootDatum hF n).rootGroup i) 3 := fun i =>
    K517ChevGenQ.oddNode_su_sq hF (by omega) i Nat.prime_three (by norm_num)
      (three_dvd_sq_sub_one h3)
  let i0 : Fin (n / 2) := ⟨0, by omega⟩
  let i1 : Fin (n / 2) := ⟨1, by omega⟩
  let i2 : Fin (n / 2) := ⟨2, by omega⟩
  have hbad02 : BadPair (Unitary.rootDatum hF n) i0 i2 := by
    refine ⟨fun h => by have h' := congrArg Fin.val h; simp [i0, i2] at h', Or.inl ?_⟩
    show Unitary.cartan n i0 i2 = 0
    simp only [Unitary.cartan, if_pos heven]
    exact cartanC_zero (by simp [i0, i2])
  have key : ∀ {A : Subgroup W}, A ≤ L → CFSG.Open.pRank 3 A ≤ 1 →
      ¬ (NodeIn (D := Unitary.rootDatum hF n) L A π' i0 ∧
        NodeIn (D := Unitary.rootDatum hF n) L A π' i1) ∧
      ¬ (NodeIn (D := Unitary.rootDatum hF n) L A π' i0 ∧
        NodeIn (D := Unitary.rootDatum hF n) L A π' i2) ∧
      ¬ (NodeIn (D := Unitary.rootDatum hF n) L A π' i1 ∧
        NodeIn (D := Unitary.rootDatum hF n) L A π' i2) := by
    intro A hA hr
    refine ⟨fun ⟨hi, hj⟩ => ?_, fun ⟨hi, hj⟩ => ?_, fun ⟨hi, hj⟩ => ?_⟩
    · obtain ⟨a, b, m, ha, hm, hb, ha3, hb3, ha1, hb1, hma, hab, hmb⟩ :=
        su_short_pair_E9 hF hn heven h3 i0 i1 rfl (by show 1 + 1 < n / 2; omega)
      have := two_le_pRank_of_nodePairE9 hπ' hA hi hj ha hm hb ha3 ha1 hb3 hb1 hma hab hmb
      omega
    · have := two_le_pRank_of_badPair hπ' hdiv hodd hA hbad02 hi hj
      omega
    · obtain ⟨a, b, m, ha, hm, hb, ha3, hb3, ha1, hb1, hma, hab, hmb⟩ :=
        su_short_pair_E9 hF hn heven h3 i1 i2 rfl (by show 2 + 1 < n / 2; omega)
      have := two_le_pRank_of_nodePairE9 hπ' hA hi hj ha hm hb ha3 ha1 hb3 hb1 hma hab hmb
      omega
  exact false_of_triple_classes (a := i0) (b := i1) (c := i2) hcl (key hA₁ h₁) (key hA₂ h₂)

theorem false_of_su_six (hL : CFSG.Open.IsQuasisimple ↥L) (hS : IsSylowTwoOf S₀ L)
    (hcov : CoveredByTwo L S₀ A₁ A₂) (hA₁ : A₁ ≤ L) (hA₂ : A₂ ≤ L)
    (h₁ : CFSG.Open.pRank 3 A₁ ≤ 1) (h₂ : CFSG.Open.pRank 3 A₂ ≤ 1)
    (hF : Nat.card F = (2 ^ f) ^ 2) (h3 : 3 ∣ 2 ^ f + 1)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* StatedProj (StatedSU 6 (2 ^ f) F)) : False := by
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
  have hbq := borelQuotient_su hF (by norm_num) ζ hζ e
  obtain ⟨π', hπ', hcl⟩ := cover_classes hS hcov hbq
  have hdiv : (Unitary.rootDatum hF 6).divisible = ∅ := by
    show Unitary.divisible 6 = ∅
    simp only [Unitary.divisible, if_pos (show Even 6 by decide)]
  have hodd : ∀ i, OddNode (rankOne (Unitary.rootDatum hF 6).rootGroup i) 3 := fun i =>
    K517ChevGenQ.oddNode_su_sq hF (by norm_num) i Nat.prime_three (by norm_num)
      (three_dvd_sq_sub_one h3)
  let i0 : Fin (6 / 2) := ⟨0, by norm_num⟩
  let i1 : Fin (6 / 2) := ⟨1, by norm_num⟩
  let i2 : Fin (6 / 2) := ⟨2, by norm_num⟩
  have hbad02 : BadPair (Unitary.rootDatum hF 6) i0 i2 := by
    show BadPairMat (Unitary.cartan 6) i0 i2
    unfold Unitary.cartan
    rw [if_pos (show Even 6 by decide)]
    decide +kernel
  have hbad12 : BadPair (Unitary.rootDatum hF 6) i1 i2 := by
    show BadPairMat (Unitary.cartan 6) i1 i2
    unfold Unitary.cartan
    rw [if_pos (show Even 6 by decide)]
    decide +kernel
  obtain ⟨a, b, ha, hb, ha3, hb3, hc, ha1, hind⟩ := su_six_heis hF h3
  have key : ∀ {A : Subgroup W}, A ≤ L → CFSG.Open.pRank 3 A ≤ 1 →
      ¬ (NodeIn (D := Unitary.rootDatum hF 6) L A π' i0 ∧
        NodeIn (D := Unitary.rootDatum hF 6) L A π' i1) ∧
      ¬ (NodeIn (D := Unitary.rootDatum hF 6) L A π' i0 ∧
        NodeIn (D := Unitary.rootDatum hF 6) L A π' i2) ∧
      ¬ (NodeIn (D := Unitary.rootDatum hF 6) L A π' i1 ∧
        NodeIn (D := Unitary.rootDatum hF 6) L A π' i2) := by
    intro A hA hr
    refine ⟨fun ⟨hi, hj⟩ => ?_, fun ⟨hi, hj⟩ => ?_, fun ⟨hi, hj⟩ => ?_⟩
    · have := two_le_pRank_of_nodePairHeis hL hπ' hA hi hj ha hb ha3 hb3 hc ha1 hind
      omega
    · have := two_le_pRank_of_badPair hπ' hdiv hodd hA hbad02 hi hj
      omega
    · have := two_le_pRank_of_badPair hπ' hdiv hodd hA hbad12 hi hj
      omega
  exact false_of_triple_classes (a := i0) (b := i1) (c := i2) hcl (key hA₁ h₁) (key hA₂ h₂)

theorem false_of_su (hL : CFSG.Open.IsQuasisimple ↥L) (hS : IsSylowTwoOf S₀ L)
    (hcov : CoveredByTwo L S₀ A₁ A₂) (hA₁ : A₁ ≤ L) (hA₂ : A₂ ≤ L)
    (h₁ : CFSG.Open.pRank 3 A₁ ≤ 1) (h₂ : CFSG.Open.pRank 3 A₂ ≤ 1)
    (hF : Nat.card F = (2 ^ f) ^ 2) (h3 : 3 ∣ 2 ^ f + 1) {n : ℕ} (hn : 5 ≤ n)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* StatedProj (StatedSU n (2 ^ f) F)) : False := by
  by_cases hodd : Odd n
  · exact false_of_su_odd hS hcov hA₁ hA₂ h₁ h₂ hF h3 hn hodd e
  · have heven : Even n := Nat.not_odd_iff_even.1 hodd
    by_cases h6 : n = 6
    · subst h6
      exact false_of_su_six hL hS hcov hA₁ hA₂ h₁ h₂ hF h3 e
    · have hn8 : 8 ≤ n := by
        obtain ⟨t, ht⟩ := heven
        omega
      exact false_of_su_even hS hcov hA₁ hA₂ h₁ h₂ hF h3 hn8 heven e

end SU

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
