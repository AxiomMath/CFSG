module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSym
public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.Walter.AStar.Subnormal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym

open CFSG.Open Subgroup

variable {R : Type*} [Group R]

theorem pCoreOf_top_eq (p : ℕ) : pCoreOf p (⊤ : Subgroup R) = CFSG.pCore p R := by
  have h := CFSG.pCore_map_iso p (Subgroup.topEquiv.symm : R ≃* ↥(⊤ : Subgroup R))
  unfold pCoreOf
  rw [← h, Subgroup.map_map]
  have : (⊤ : Subgroup R).subtype.comp (Subgroup.topEquiv.symm : R ≃* ↥(⊤ : Subgroup R)).toMonoidHom
      = MonoidHom.id R := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

theorem le_pCore_of_subnormal (p : ℕ) {U : Subgroup R} (hU : U.IsSubnormal) (hp : IsPGroup p U) :
    U ≤ CFSG.pCore p R := by
  have h1 := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf p
    (IsSubnormal.top_iff.2 hU) hp
  rwa [pCoreOf_top_eq] at h1

theorem eq_bot_of_subnormal_isPGroup_two (h : CFSG.pCore 2 R = ⊥) :
    ∀ Z : Subgroup R, Z.IsSubnormal → IsPGroup 2 Z → Z = ⊥ := by
  intro Z hZ hp
  have h1 := le_pCore_of_subnormal 2 hZ hp
  rw [h] at h1
  exact le_bot_iff.1 h1

theorem exists_involution_mem_sylow [Finite R] {X : Subgroup R} (hX : IsSymThree X)
    (hXs : IsSubnormal X ⊤) (T : Sylow 2 R) :
    ∃ s ∈ (T : Subgroup R), s ∈ X ∧ s ^ 2 = 1 ∧ s ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_symThree hX
  obtain ⟨P, hP⟩ :=
    CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T (IsSubnormal.top_iff.1 hXs)
  have hcard : Nat.card P = 2 := by
    have h := Sylow.card_eq_multiplicity P
    rw [card_symThree hX] at h
    have h6 : (6 : ℕ).factorization 2 = 1 := by
      have h23 : (6 : ℕ) = 2 * 3 := by norm_num
      rw [h23, Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd]
    rw [h6] at h
    simpa using h
  have hcard' : Nat.card ↥((T : Subgroup R) ⊓ X) = 2 := by
    rw [← hP, Subgroup.card_map_of_injective X.subtype_injective]
    exact hcard
  haveI : Finite ↥((T : Subgroup R) ⊓ X) := Nat.finite_of_card_ne_zero (by rw [hcard']; norm_num)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hcard'])
  have hy2 : (y : R) ^ 2 = 1 := by
    have h1 : y ^ 2 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy] at this
    simpa using congrArg Subtype.val h1
  have hy1 : (y : R) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    omega
  exact ⟨y, (y.2).1, (y.2).2, hy2, hy1⟩

theorem mem_pCore_three [Finite R] {X : Subgroup R} (hX : IsSymThree X) (hXs : IsSubnormal X ⊤)
    {a : R} (ha : a ∈ X) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) : a ∈ CFSG.pCore 3 R := by
  obtain ⟨hXa, ⟨s, hs, hs2, hs1⟩⟩ := symThree_of_order_three hX ha ha3 ha1
  obtain ⟨hinv, hXeq⟩ := hXa s hs hs2 hs1
  have hnorm : X ≤ normalizer ((zpowers a : Subgroup R) : Set R) := by
    rw [hXeq, Subgroup.closure_le]
    intro y hy
    rcases hy with h | h
    · rw [h]; exact Subgroup.le_normalizer (Subgroup.mem_zpowers a)
    · rw [h]; exact mem_normalizer_zpowers_of_inv hinv
  have hzX : zpowers a ≤ X := by rw [Subgroup.zpowers_le]; exact ha
  have hsub1 : IsSubnormal (zpowers a) X :=
    (IsSubnormal.iff_subgroupOf hzX).2
      (Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hzX).2 hnorm))
  have hsub : IsSubnormal (zpowers a) ⊤ := hsub1.trans hXs
  have hp : IsPGroup 3 (zpowers a) := by
    rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers]
    have hd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · simpa using h
  exact le_pCore_of_subnormal 3 (IsSubnormal.top_iff.1 hsub) hp (Subgroup.mem_zpowers a)

theorem eq_of_shared_three [Finite R]
    (hO2 : ∀ Z : Subgroup R, Z.IsSubnormal → IsPGroup 2 Z → Z = ⊥)
    {X X' : Subgroup R} (hX : IsSymThree X) (hX' : IsSymThree X')
    (hXs : IsSubnormal X ⊤) (hXs' : IsSubnormal X' ⊤) {a : R} (ha : a ∈ X) (ha' : a ∈ X')
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) : X = X' := by
  obtain ⟨hXa, ⟨s, hs, hs2, hs1⟩⟩ := symThree_of_order_three hX ha ha3 ha1
  obtain ⟨hXa', ⟨s', hs', hs2', hs1'⟩⟩ := symThree_of_order_three hX' ha' ha3 ha1
  obtain ⟨hinv, hXeq⟩ := hXa s hs hs2 hs1
  obtain ⟨hinv', hXeq'⟩ := hXa' s' hs' hs2' hs1'
  have hss : s * s = 1 := by rw [← pow_two]; exact hs2
  have hss' : s' * s' = 1 := by rw [← pow_two]; exact hs2'
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsi' : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hss'
  set z : R := s * s' with hz
  set W : Subgroup R := X ⊔ X' with hW
  have hWs : W.IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_sup (IsSubnormal.top_iff.1 hXs) (IsSubnormal.top_iff.1 hXs')
  have haW : a ∈ W := le_sup_left (a := X) (b := X') ha
  have hsW : s ∈ W := le_sup_left (a := X) (b := X') hs
  have hs'W : s' ∈ W := le_sup_right (a := X) (b := X') hs'
  have hzW : z ∈ W := W.mul_mem hsW hs'W
  have hza : z * a * z⁻¹ = a := by
    have h1 : s' * a * s'⁻¹ = a⁻¹ := hinv'
    calc z * a * z⁻¹ = s * (s' * a * s'⁻¹) * s⁻¹ := by simp only [hz, mul_inv_rev]; group
      _ = s * a⁻¹ * s⁻¹ := by rw [h1]
      _ = (s * a * s⁻¹)⁻¹ := by group
      _ = a := by rw [hinv, inv_inv]
  have hsz : s * z * s⁻¹ = z⁻¹ := by
    calc s * z * s⁻¹ = (s * s) * s' * s⁻¹ := by simp only [hz]; group
      _ = s' * s⁻¹ := by rw [hss, one_mul]
      _ = s'⁻¹ * s⁻¹ := by rw [hsi']
      _ = z⁻¹ := by simp [hz, mul_inv_rev]
  have hs'z : s' * z * s'⁻¹ = z⁻¹ := by
    calc s' * z * s'⁻¹ = s' * s * (s' * s'⁻¹) := by simp only [hz]; group
      _ = s' * s := by group
      _ = s'⁻¹ * s⁻¹ := by rw [hsi, hsi']
      _ = z⁻¹ := by simp [hz, mul_inv_rev]
  have hodd : Odd (orderOf z) := by
    by_contra hnodd
    rw [Nat.not_odd_iff_even] at hnodd
    obtain ⟨k, hk⟩ := hnodd
    have hnpos : 0 < orderOf z := orderOf_pos z
    have hkpos : 0 < k := by omega
    set v : R := z ^ k with hv
    have hv2 : v ^ 2 = 1 := by
      rw [hv, ← pow_mul, show k * 2 = orderOf z by omega]
      exact pow_orderOf_eq_one z
    have hv1 : v ≠ 1 := by
      intro h
      have : orderOf z ∣ k := orderOf_dvd_of_pow_eq_one h
      have := Nat.le_of_dvd hkpos this
      omega
    have hvv : v * v = 1 := by rw [← pow_two]; exact hv2
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    have hcomm_a : a * v * a⁻¹ = v := by
      have : a * z * a⁻¹ = z := by
        have h1 := hza
        have h2 : z * a = a * z := by
          calc z * a = (z * a * z⁻¹) * z := by group
            _ = a * z := by rw [hza]
        calc a * z * a⁻¹ = (z * a) * a⁻¹ := by rw [h2]
          _ = z := by group
      rw [hv, ← conj_pow, this]
    have hcomm_s : s * v * s⁻¹ = v := by
      rw [hv, ← conj_pow, hsz, inv_pow, ← hv, hvi]
    have hcomm_s' : s' * v * s'⁻¹ = v := by
      rw [hv, ← conj_pow, hs'z, inv_pow, ← hv, hvi]
    have hnorm : W ≤ normalizer ((zpowers v : Subgroup R) : Set R) := by
      refine sup_le ?_ ?_
      · rw [hXeq, Subgroup.closure_le]
        intro y hy
        rcases hy with h | h
        · rw [h]; exact mem_normalizer_zpowers_of_comm hcomm_a
        · rw [h]; exact mem_normalizer_zpowers_of_comm hcomm_s
      · rw [hXeq', Subgroup.closure_le]
        intro y hy
        rcases hy with h | h
        · rw [h]; exact mem_normalizer_zpowers_of_comm hcomm_a
        · rw [h]; exact mem_normalizer_zpowers_of_comm hcomm_s'
    have hvW : zpowers v ≤ W := by
      rw [Subgroup.zpowers_le]
      exact pow_mem hzW k
    have hU : (zpowers v).IsSubnormal :=
      Subgroup.IsSubnormal.trans hvW
        (Subgroup.Normal.isSubnormal
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hvW).2 hnorm)) hWs
    have hpg : IsPGroup 2 (zpowers v) := by
      rw [IsPGroup.iff_card]
      refine ⟨1, ?_⟩
      rw [Nat.card_zpowers]
      have hd : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hv2
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hv1
      · simpa using h
    have hbot := hO2 _ hU hpg
    exact hv1 (by
      have : v ∈ zpowers v := Subgroup.mem_zpowers v
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this)
  have hXW : X ≤ W := le_sup_left
  have hX'W : X' ≤ W := le_sup_right
  have hsubW : IsSubnormal X W := by
    have h := hXs.inf_of_le (le_top : W ≤ ⊤)
    rwa [inf_eq_left.2 hXW] at h
  have hXeqW : X = W := by
    refine eq_of_subnormal_of_forall_normal hsubW fun N hXN hNW hNn => ?_
    have hconj := (Subgroup.normal_subgroupOf_iff hNW).1 hNn
    have hsN : s ∈ N := hXN hs
    have haN : a ∈ N := hXN ha
    have hz2 : z ^ 2 ∈ N := by
      have h1 : z * s * z⁻¹ ∈ N := hconj s z hsN hzW
      have h2 : z * s * z⁻¹ * s⁻¹ ∈ N := N.mul_mem h1 (N.inv_mem hsN)
      have h3 : z * s * z⁻¹ * s⁻¹ = z ^ 2 := by
        have e2 : s * z⁻¹ * s⁻¹ = z := by
          have : s * z⁻¹ * s⁻¹ = (s * z * s⁻¹)⁻¹ := by group
          rw [this, hsz, inv_inv]
        calc z * s * z⁻¹ * s⁻¹ = z * (s * z⁻¹ * s⁻¹) := by group
          _ = z ^ 2 := by rw [e2, pow_two]
      rwa [h3] at h2
    have hzN : z ∈ N := by
      obtain ⟨j, hj⟩ := hodd
      have h4 : (z ^ 2) ^ (j + 1) = z := by
        rw [← pow_mul]
        have : 2 * (j + 1) = orderOf z + 1 := by omega
        rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
      rw [← h4]
      exact pow_mem hz2 _
    have hs'N : s' ∈ N := by
      have : s' = s * z := by
        calc s' = (s * s) * s' := by rw [hss, one_mul]
          _ = s * z := by simp only [hz, mul_assoc]
      rw [this]
      exact N.mul_mem hsN hzN
    have hX'N : X' ≤ N := by
      rw [hXeq', Subgroup.closure_le]
      intro y hy
      rcases hy with h | h
      · rw [h]; exact haN
      · rw [h]; exact hs'N
    apply le_antisymm hNW
    exact sup_le hXN hX'N
  have hX'X : X' ≤ X := hXeqW ▸ hX'W
  haveI := finite_symThree hX
  exact (Subgroup.eq_of_le_of_card_ge hX'X (by rw [card_symThree hX, card_symThree hX'])).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym
