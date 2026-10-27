module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Eighteen
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Rank
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem zjo_exists_isSylowOf_normalized {q r : ℕ} (hq : q.Prime) (hr : r.Prime) {Q Y : Subgroup G}
    (hQ : IsPGroup q Q) (hQY : Q ≤ normalizer (Y : Set G)) (hY : q.Coprime (Nat.card Y)) :
    ∃ A : Subgroup G, IsSylowOf r A Y ∧ Q ≤ normalizer (A : Set G) := by
  classical
  let φ := ambientSubgroupActionHom Q Y hQY
  let _ : MulDistribMulAction Q Y := MulDistribMulAction.compHom Y φ
  obtain ⟨S, hS⟩ := coprime_pGroup_has_invariant_sylow q hq hQ hY r hr
  have hSinv : ∀ g : Q, (S : Subgroup Y).map (φ g).toMonoidHom = S := by
    intro g
    have h := congrArg (fun T : Sylow r Y => (T : Subgroup Y)) (hS g)
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h
    exact h
  exact ⟨(S : Subgroup Y).map Y.subtype, ⟨S, rfl⟩,
    (ambient_subgroup_action_image_invariant_iff Q Y hQY S).1 hSinv⟩

theorem zjo_solvable_of_normal_sylow_two {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [S.Normal] (hS : IsSylowOf 2 S K) : Group.IsSolvable K := by
  classical
  obtain ⟨Q, hQ⟩ := hS
  have hQS : (Q : Subgroup K) = S.subgroupOf K := by
    rw [← hQ]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  have hQn : (Q : Subgroup K).Normal := by
    rw [hQS]
    infer_instance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Group.IsSolvable (Q : Subgroup K) := by
    have : Group.IsNilpotent (Q : Subgroup K) := Q.isPGroup'.isNilpotent
    infer_instance
  have hodd : Odd (Nat.card (K ⧸ (Q : Subgroup K))) := by
    rw [← Subgroup.index, Nat.odd_iff]
    have := Q.not_dvd_index
    omega
  have h2 : Group.IsSolvable (K ⧸ (Q : Subgroup K)) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range (Q : Subgroup K).subtype
    (QuotientGroup.mk' (Q : Subgroup K)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem zj_J0 {p : ℕ} {Y : Type} [Group Y] [Finite Y] {K D V J : Subgroup Y} [K.Normal]
    (hZ : ZJFrame p K D V) {L : Subgroup (Y ⧸ K)} (hLs : IsSimpleGroup L)
    (hLc : centralizer (L : Set (Y ⧸ K)) = ⊥) (hJn : J.Normal)
    (hJL : J.map (QuotientGroup.mk' K) = L) (hJp : pElementSubgroup p J = J)
    (hJJ : ⁅J, J⁆ = J) (hJK : (CFSG.pPrimeCore p ↥J).map J.subtype = J ⊓ K) :
    ¬ 3 ∣ Nat.card (⁅J, (CFSG.pPrimeCore p ↥J).map J.subtype⁆ : Subgroup Y) := by
  classical
  have hp := hZ.pre.prime
  have hp2 := hZ.pre.odd
  rw [hJK]
  intro h3
  set R : Subgroup Y := J ⊓ K with hR
  have hRJ : R ≤ J := inf_le_left
  have hRK : R ≤ K := inf_le_right
  have hRn : R.Normal := inferInstance
  have hRcop : p.Coprime (Nat.card R) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hRK) hZ.pre.coprime
  have hJ0R : ⁅J, R⁆ ≤ R := Subgroup.commutator_le_right J R
  have hJ0cop : p.Coprime (Nat.card (⁅J, R⁆ : Subgroup Y)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hJ0R) hRcop
  have hp3 : p ≠ 3 := by
    rintro rfl
    have := Nat.Coprime.eq_one_of_dvd hJ0cop h3
    omega
  have hp5 : 5 ≤ p := by
    by_contra hlt
    push Not at hlt
    interval_cases p <;> simp_all <;> exact absurd hp (by norm_num)
  have hDp : IsPGroup p D := IsPGroup.of_card hZ.pre.card
  have hDN : D ≤ normalizer ((⁅J, R⁆ : Subgroup Y) : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨Y₃, hY₃, hDY₃⟩ :=
    zjo_exists_isSylowOf_normalized (q := p) (r := 3) hp Nat.prime_three hDp hDN hJ0cop
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ0J : ⁅J, R⁆ ≤ J := Subgroup.commutator_le_left J R
  have hJ0K : ⁅J, R⁆ ≤ K := hJ0R.trans hRK
  have hfrat : ∀ j ∈ J, ∃ n ∈ J ⊓ normalizer (Y₃ : Set Y), ∃ k ∈ (⁅J, R⁆ : Subgroup Y),
      n * k = j := by
    intro j hj
    obtain ⟨Q, hQ⟩ := hY₃
    have h := Sylow.normalizer_sup_eq_top Q
    have hQ' : (Q : Subgroup ↥(⁅J, R⁆ : Subgroup Y)).map (⁅J, R⁆ : Subgroup Y).subtype = Y₃ := hQ
    rw [hQ'] at h
    have hj' : j ∈ normalizer (Y₃ : Set Y) ⊔ (⁅J, R⁆ : Subgroup Y) := by rw [h]; exact trivial
    obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hj'
    refine ⟨n, ⟨?_, hn⟩, k, hk, rfl⟩
    have := J.mul_mem hj (J.inv_mem (hJ0J hk))
    simpa using this
  have hcover : ∀ l ∈ L, ∃ n ∈ J ⊓ normalizer (Y₃ : Set Y), QuotientGroup.mk' K n = l := by
    intro l hl
    rw [← hJL] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    obtain ⟨n, hn, k, hk, rfl⟩ := hfrat j hj
    refine ⟨n, hn, ?_⟩
    have hk1 : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).mpr (hJ0K hk)
    rw [map_mul, hk1, mul_one]
  have hKsolv : Group.IsSolvable K := zjo_solvable_of_normal_sylow_two hZ.sylow2
  have hRs : Group.IsSolvable R :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hRK)
  have hJR : ⁅J, J⁆ ⊔ R = J := by
    rw [hJJ]
    exact sup_eq_left.mpr hRJ
  have hnot := eighteen_ten_solvable hp Nat.prime_three hRJ hJn hRn hRcop hRs hJp hJR hY₃ h3
  have hfaith : D ⊓ centralizer (Y₃ : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro d ⟨hdD, hdC⟩
    rw [Subgroup.mem_bot]
    by_contra hd1
    have hdK : d ∉ K := by
      intro hdK
      have h1 : orderOf d ∣ p := orderOf_dvd_of_pow_eq_one (hZ.pre.elem.2 d hdD)
      have h2 : orderOf d ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hdK
      have h3 := Nat.eq_one_of_dvd_coprimes hZ.pre.coprime h1 h2
      exact hd1 (orderOf_eq_one_iff.mp h3)
    have hdbar : QuotientGroup.mk' K d ≠ 1 := fun h => hdK ((QuotientGroup.eq_one_iff d).mp h)
    have hnc : QuotientGroup.mk' K d ∉ centralizer (L : Set (Y ⧸ K)) := by
      rw [hLc]
      exact hdbar
    rw [mem_centralizer_iff] at hnc
    push Not at hnc
    obtain ⟨l, hlL, hl⟩ := hnc
    obtain ⟨n, hnJ, hnN⟩ := hcover l hlL
    have := hLs
    set C : Subgroup Y := centralizer (Y₃ : Set Y) ⊓ J with hC
    set T : Subgroup (Y ⧸ K) := C.map (QuotientGroup.mk' K) with hT
    have hTL : T ≤ L := by
      rw [← hJL]
      exact Subgroup.map_mono inf_le_right
    have hconj : ∀ m ∈ J ⊓ normalizer (Y₃ : Set Y), ∀ c ∈ C, m * c * m⁻¹ ∈ C := by
      intro m hm c hc
      refine ⟨?_, J.mul_mem (J.mul_mem hm.1 hc.2) (J.inv_mem hm.1)⟩
      show m * c * m⁻¹ ∈ centralizer (Y₃ : Set Y)
      rw [mem_centralizer_iff]
      intro y hy
      have hzmem : m⁻¹ * y * m ∈ Y₃ := by
        simpa using (mem_normalizer_iff.mp (inv_mem hm.2) y).mp hy
      have hz := mem_centralizer_iff.mp (show c ∈ centralizer (Y₃ : Set Y) from hc.1) _ hzmem
      calc y * (m * c * m⁻¹) = m * ((m⁻¹ * y * m) * c) * m⁻¹ := by group
        _ = m * (c * (m⁻¹ * y * m)) * m⁻¹ := by rw [hz]
        _ = m * c * m⁻¹ * y := by group
    have hTn : (T.subgroupOf L).Normal := by
      refine ⟨fun t ht g => ?_⟩
      obtain ⟨c, hcC, hct⟩ := ht
      obtain ⟨m, hmJ, hmg⟩ := hcover g.1 g.2
      refine ⟨m * c * m⁻¹, hconj m hmJ c hcC, ?_⟩
      show QuotientGroup.mk' K (m * c * m⁻¹) = (g : Y ⧸ K) * (t : Y ⧸ K) * (g : Y ⧸ K)⁻¹
      rw [map_mul, map_mul, map_inv, hct, hmg]
      rfl
    have hcC : d⁻¹ * (n⁻¹ * d * n) ∈ C := by
      refine ⟨?_, ?_⟩
      · show d⁻¹ * (n⁻¹ * d * n) ∈ centralizer (Y₃ : Set Y)
        rw [mem_centralizer_iff]
        intro y hy
        have hz : n * y * n⁻¹ ∈ Y₃ := (mem_normalizer_iff.mp hnJ.2 y).mp hy
        have hdC' : d ∈ centralizer (Y₃ : Set Y) := hdC
        have h1 := mem_centralizer_iff.mp hdC' y hy
        have h2 := mem_centralizer_iff.mp hdC' _ hz
        have hdy : y * d⁻¹ = d⁻¹ * y := by
          calc y * d⁻¹ = d⁻¹ * (d * y) * d⁻¹ := by group
            _ = d⁻¹ * (y * d) * d⁻¹ := by rw [h1]
            _ = d⁻¹ * y := by group
        have hnd : y * (n⁻¹ * d * n) = (n⁻¹ * d * n) * y := by
          calc y * (n⁻¹ * d * n) = n⁻¹ * ((n * y * n⁻¹) * d) * n := by group
            _ = n⁻¹ * (d * (n * y * n⁻¹)) * n := by rw [h2]
            _ = (n⁻¹ * d * n) * y := by group
        calc y * (d⁻¹ * (n⁻¹ * d * n)) = (y * d⁻¹) * (n⁻¹ * d * n) := by group
          _ = d⁻¹ * (y * (n⁻¹ * d * n)) := by rw [hdy]; group
          _ = d⁻¹ * ((n⁻¹ * d * n) * y) := by rw [hnd]
          _ = d⁻¹ * (n⁻¹ * d * n) * y := by group
      · have h1 : d⁻¹ * n⁻¹ * d ∈ J := by
          have := hJn.conj_mem n⁻¹ (J.inv_mem hnJ.1) d⁻¹
          simpa using this
        have := J.mul_mem h1 hnJ.1
        simpa [mul_assoc] using this
    have hne : T.subgroupOf L ≠ ⊥ := by
      intro hbot
      have hmem : (⟨QuotientGroup.mk' K (d⁻¹ * (n⁻¹ * d * n)), hTL ⟨_, hcC, rfl⟩⟩ : ↥L) ∈
          T.subgroupOf L := ⟨_, hcC, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : QuotientGroup.mk' K (d⁻¹ * (n⁻¹ * d * n)) = 1 := congrArg Subtype.val hmem
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hnN] at h1
      apply hl
      have h2 : l⁻¹ * QuotientGroup.mk' K d * l = QuotientGroup.mk' K d := by
        rw [inv_mul_eq_one] at h1
        exact h1.symm
      have h3 : QuotientGroup.mk' K d * l = l * QuotientGroup.mk' K d := by
        calc QuotientGroup.mk' K d * l = l * (l⁻¹ * QuotientGroup.mk' K d * l) := by group
          _ = l * QuotientGroup.mk' K d := by rw [h2]
      exact h3.symm
    have := hTn
    have htop : T.subgroupOf L = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf L)).resolve_left hne
    have hLT : L ≤ T := fun x hx => by
      have : (⟨x, hx⟩ : ↥L) ∈ T.subgroupOf L := by rw [htop]; trivial
      exact this
    refine hnot (fun j hj => ?_)
    have hjL : QuotientGroup.mk' K j ∈ L := by
      rw [← hJL]
      exact ⟨j, hj, rfl⟩
    obtain ⟨c, hcC', hcj⟩ := hLT hjL
    have hmem : c⁻¹ * j ∈ R := by
      refine ⟨J.mul_mem (J.inv_mem hcC'.2) hj, ?_⟩
      have h1 : QuotientGroup.mk' K (c⁻¹ * j) = 1 := by
        rw [map_mul, map_inv, hcj, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hjeq : j = c * (c⁻¹ * j) := by group
    rw [hjeq]
    exact Subgroup.mul_mem_sup hcC' hmem
  obtain ⟨A, -, hAe, hA4⟩ := exists_isElemAbelian_card_three_pow_four hp hp5 hZ.pre.elem
    hZ.pre.card hY₃.isPGroup hDY₃ hfaith
  have h27 := hZ.rank3 A hAe
  have h81 : (3 : ℕ) ^ 4 ≤ 3 ^ 3 := hA4.trans h27
  norm_num at h81

end CFSG.LocalAnalysis.RankThreeTheoremC
