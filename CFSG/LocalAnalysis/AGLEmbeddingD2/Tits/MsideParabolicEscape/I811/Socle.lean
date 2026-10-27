module

public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Reduction

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open scoped IsMulCommutative in
theorem eq_one_of_mem_center_of_isPerfect {p : ℕ} [Fact p.Prime] {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] (P : Sylow p K) [IsMulCommutative ↥(P : Subgroup K)] {z : K}
    (hz : z ∈ Subgroup.center K) (hzP : z ∈ (P : Subgroup K)) : z = 1 := by
  classical
  have key : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup K) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center K := Subgroup.pow_mem _ hz k
    rw [mul_assoc, (Subgroup.mem_center_iff.mp hzk g₀).symm, ← mul_assoc, inv_mul_cancel,
      one_mul]
  have ht := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup K)) z key
  have htriv : MonoidHom.transfer (MonoidHom.id (P : Subgroup K)) z = 1 := by
    have h1 := Abelianization.commutator_subset_ker
      (MonoidHom.transfer (MonoidHom.id (P : Subgroup K)))
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact h1 (Subgroup.mem_top z)
  rw [htriv] at ht
  have hpow : z ^ (P : Subgroup K).index = 1 := by
    have := congrArg Subtype.val ht
    simpa using this.symm
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨z, hzP⟩
  have hzk : z ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (p ^ k) (P : Subgroup K).index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzk)
    (orderOf_dvd_of_pow_eq_one hpow))

theorem zpowers_eq_of_commute_of_cyclic {Y : Type} [Group Y] [Finite Y]
    (hcyc : ∀ X : Subgroup Y, IsPGroup 3 X → IsCyclic X) {x y : Y} (hx : orderOf x = 3)
    (hy : orderOf y = 3) (hxy : x * y = y * x) :
    Subgroup.zpowers y = Subgroup.zpowers x := by
  refine CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.eq_of_card_three_of_le_normalizer
    (B := ⊤) (fun X _ hX => hcyc X hX) le_top le_top (by rw [Nat.card_zpowers, hx])
    (by rw [Nat.card_zpowers, hy]) ?_
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute y (x ^ k) := ((Commute.zpow_right (Commute.symm hxy) k))
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers x k
  · intro hz
    have hc : Commute y z := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      have : z = y⁻¹ * x ^ k * y := by rw [hk]; group
      rw [this]
      have h1 : Commute y (x ^ k) := ((Commute.zpow_right (Commute.symm hxy) k))
      exact Commute.mul_right (Commute.mul_right (Commute.inv_right (Commute.refl y)) h1)
        (Commute.refl y)
    rw [hc.eq, mul_inv_cancel_right] at hz
    exact hz

theorem exists_simple_socle {B : Type} [Group B] [Finite B]
    (hcyc : ∀ X : Subgroup B, IsPGroup 3 X → IsCyclic X)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 B) :
    ∃ K : Subgroup (B ⧸ primeComplementCore (G := B) 3), K.Normal ∧ IsSimpleGroup ↥K ∧
      (∃ a b : K, a * b ≠ b * a) ∧
      Subgroup.centralizer (K : Set (B ⧸ primeComplementCore (G := B) 3)) = ⊥ ∧
      ∀ X : Subgroup (B ⧸ primeComplementCore (G := B) 3), Nat.card X = 3 → X ≤ K := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := B ⧸ primeComplementCore (G := B) 3 with hYdef
  have hO : CFSG.pPrimeCore 3 Y = ⊥ := pPrimeCore_three_quotient_eq_bot B
  have hcycY : ∀ X : Subgroup Y, IsPGroup 3 X → IsCyclic X := by
    intro X hX
    obtain ⟨W, hW3, hWX⟩ :=
      CFSG.AGLEmbeddingD2.exists_isPGroup_map_mk_eq_of_isPGroup (primeComplementCore (G := B) 3) hX
    have := hcyc W hW3
    rw [← hWX]
    exact isCyclic_of_surjective ((QuotientGroup.mk' _).subgroupMap W)
      (MonoidHom.subgroupMap_surjective _ W)
  have hnc : ¬ HasPrimeConstraint (G := B) 3 := fun h =>
    hns (isPSolvable_three_of_hasPrimeConstraint_of_cyclic hcyc h)
  have hlayer := layer_ne_bot_of_not_hasPrimeConstraint hnc
  obtain ⟨K, hK⟩ : ∃ K : Subgroup Y, CFSG.IsComponent K := by
    by_contra h
    push Not at h
    apply hlayer
    have : {K : Subgroup Y | CFSG.IsComponent K} = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
    simp only [CFSG.layer.eq_sSup]
    rw [this, sSup_empty]
  have hnsK : ¬ CFSG.HallHigman.IsPSolvable 3 K := GNQuotient.not_isPSolvable_of_isComponent hO hK
  have h3K : 3 ∣ Nat.card K := by
    by_contra h
    exact hnsK (isPSolvable_three_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h))
  have : Group.IsPerfect ↥K := hK.1.1
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
      intro h3
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥K) 3 h3
      have hzp : IsPGroup 3 (Subgroup.zpowers (z : ↥K)) := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one]
      obtain ⟨P, hP⟩ := hzp.exists_le_sylow
      have hPc : IsCyclic ↥(P : Subgroup ↥K) := by
        have h1 := hcycY ((P : Subgroup ↥K).map K.subtype) (P.isPGroup'.map _)
        exact isCyclic_of_map_injective K.subtype K.subtype_injective _
      have : IsMulCommutative ↥(P : Subgroup ↥K) := inferInstance
      have hz1 := eq_one_of_mem_center_of_isPerfect P z.2 (hP (Subgroup.mem_zpowers _))
      have : orderOf z = 1 := by
        rw [← Subgroup.orderOf_coe, hz1, orderOf_one]
      omega
    have hsub : ((Subgroup.center ↥K).map K.subtype).IsSubnormal :=
      Subgroup.IsSubnormal.step _ K (Subgroup.map_subtype_le _) hK.2 (by
        rw [show ((Subgroup.center ↥K).map K.subtype).subgroupOf K = Subgroup.center ↥K from
          Subgroup.comap_map_eq_self_of_injective K.subtype_injective _]
        infer_instance)
    have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hsub (by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3)
    rw [hO, le_bot_iff] at hle
    exact Subgroup.map_injective K.subtype_injective (by rw [hle, Subgroup.map_bot])
  have hsimple : IsSimpleGroup ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup_congr.1
      hK.1.2.1
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
  set x : Y := (x0 : Y) with hx
  have hxK : x ∈ K := x0.2
  have hxo : orderOf x = 3 := by rw [hx, Subgroup.orderOf_coe, hx0]
  have hcen : ∀ y ∈ K, (∀ k ∈ K, y * k = k * y) → y = 1 := by
    intro y hyK hy
    have : (⟨y, hyK⟩ : K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hy k k.2).symm
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hcomm3 : ∀ y : Y, orderOf y = 3 → (∀ k ∈ K, y * k = k * y) → False := by
    intro y hy hyc
    have hyx := zpowers_eq_of_commute_of_cyclic hcycY hxo hy (hyc x hxK).symm
    have hyK : y ∈ K := by
      have : y ∈ Subgroup.zpowers x := hyx ▸ Subgroup.mem_zpowers y
      exact (Subgroup.zpowers_le.mpr hxK) this
    have := hcen y hyK hyc
    rw [this, orderOf_one] at hy
    omega
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    have hKg : CFSG.IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK
    rcases CFSG.LocalCores.distinct_components_commute hK hKg with h | h
    · have : g * k * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨k, hk, rfl⟩
      rwa [← h] at this
    · exfalso
      refine hcomm3 (g * x * g⁻¹) (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hxo])
        fun k' hk' => ?_
      have hmem : g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨x, hxK, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk') _ hmem
  have hC : Subgroup.centralizer (K : Set Y) = ⊥ := by
    have hCn : (Subgroup.centralizer (K : Set Y)).Normal := by
      have := hKn
      infer_instance
    have hC3 : ¬ 3 ∣ Nat.card (Subgroup.centralizer (K : Set Y)) := by
      intro h3
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
        (G := Subgroup.centralizer (K : Set Y)) 3 h3
      refine hcomm3 (y : Y) (by rw [Subgroup.orderOf_coe, hy]) fun k hk => ?_
      exact (Subgroup.mem_centralizer_iff.mp y.2 k hk).symm
    have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hCn.isSubnormal
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hC3)
    rwa [hO, le_bot_iff] at hle
  have hX : ∀ X : Subgroup Y, Nat.card X = 3 → X ≤ K := by
    intro X hX3
    have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hX3, pow_one])
    obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
    have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
    obtain ⟨Q, hxQ⟩ := hxp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q P
    set x' := g * x * g⁻¹ with hx'
    have hx'P : x' ∈ (P : Subgroup Y) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨x, hxQ (Subgroup.mem_zpowers x), rfl⟩
    have hx'K : x' ∈ K := hKn.conj_mem x hxK g
    have hx'o : orderOf x' = 3 := by rw [hx', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hxo]
    have hPc : IsCyclic ↥(P : Subgroup Y) := hcycY _ P.isPGroup'
    have : IsCyclic ↥X := isCyclic_of_prime_card (p := 3) hX3
    obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := ↥X)
    have hyo : orderOf (y : Y) = 3 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hX3]
    have hXy : X = Subgroup.zpowers (y : Y) := by
      refine le_antisymm (fun a ha => ?_) (Subgroup.zpowers_le.mpr y.2)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨a, ha⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
    have hcomm : (y : Y) * x' = x' * y := by
      have h := (IsCyclic.isMulCommutative (α := ↥(P : Subgroup Y))).is_comm.comm
        ⟨(y : Y), hXP y.2⟩ ⟨x', hx'P⟩
      exact congrArg Subtype.val h
    have hyx := zpowers_eq_of_commute_of_cyclic hcycY hx'o hyo hcomm.symm
    rw [hXy, hyx]
    exact Subgroup.zpowers_le.mpr hx'K
  exact ⟨K, hKn, hsimple, hnab, hC, hX⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
