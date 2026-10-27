module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
public import CFSG.GroupTheory.AllPSubgroupsIsCyclicOfPRankLeOne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverTransport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

private theorem mem_zpowers_pow_of_mem_inf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Q R : Subgroup G} (hQp : IsPGroup p Q) (hQc : IsCyclic Q) {r : G} (hr : ∃ k : ℕ, orderOf r = p ^ k)
    (hrQ : r ∈ Q) (hrR : r ∉ R) {x : G} (hxQ : x ∈ Q) (hxR : x ∈ R) :
    x ∈ Subgroup.zpowers (r ^ p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hr
  obtain ⟨i, hi⟩ : ∃ i : ℕ, orderOf x = p ^ i :=
    (IsPGroup.iff_orderOf.1 hQp) ⟨x, hxQ⟩ |>.imp fun i hi => by
      rw [← hi, Subgroup.orderOf_mk]
  have hxz : Subgroup.zpowers x ≤ Q := Subgroup.zpowers_le.2 hxQ
  have hrz : Subgroup.zpowers r ≤ Q := Subgroup.zpowers_le.2 hrQ
  have hcard : ∀ (y : G) (hy : Subgroup.zpowers y ≤ Q), Nat.card ((Subgroup.zpowers y).subgroupOf Q) =
      orderOf y := fun y hy => by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hy).toEquiv, Nat.card_zpowers]
  have hmem : ∀ {y z : G}, Subgroup.zpowers y ≤ Q → Subgroup.zpowers z ≤ Q →
      (Subgroup.zpowers y).subgroupOf Q ≤ (Subgroup.zpowers z).subgroupOf Q →
        y ∈ Subgroup.zpowers z := fun {y z} hy hz h => by
    have hyQ : y ∈ Q := hy (Subgroup.mem_zpowers y)
    have h1 : (⟨y, hyQ⟩ : Q) ∈ (Subgroup.zpowers y).subgroupOf Q :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers y)
    exact Subgroup.mem_subgroupOf.1 (h h1)
  have hxr : x ∈ Subgroup.zpowers r := by
    rcases le_total i k with hik | hki
    · have h1 : Nat.card ((Subgroup.zpowers x).subgroupOf Q) ∣
          Nat.card ((Subgroup.zpowers r).subgroupOf Q) := by
        rw [hcard x hxz, hcard r hrz, hi, hk]
        exact pow_dvd_pow p hik
      exact hmem hxz hrz ((IsCyclic.subgroup_le_iff_card_dvd).2 h1)
    · have h1 : Nat.card ((Subgroup.zpowers r).subgroupOf Q) ∣
          Nat.card ((Subgroup.zpowers x).subgroupOf Q) := by
        rw [hcard x hxz, hcard r hrz, hi, hk]
        exact pow_dvd_pow p hki
      have : r ∈ Subgroup.zpowers x := hmem hrz hxz ((IsCyclic.subgroup_le_iff_card_dvd).2 h1)
      exact absurd ((Subgroup.zpowers_le.2 hxR) this) hrR
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxr
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, r ^ m' = x := by
    have h0 : (0 : ℤ) ≤ m % (orderOf r : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast (orderOf_pos r).ne')
    refine ⟨(m % (orderOf r : ℤ)).toNat, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg h0, zpow_mod_orderOf, hm]
  by_cases hpm : p ∣ m'
  · obtain ⟨c, hc⟩ := hpm
    refine ⟨(c : ℤ), ?_⟩
    show (r ^ p) ^ (c : ℤ) = x
    rw [zpow_natCast, ← pow_mul, ← hc, hm']
  · exfalso
    have hcop : Nat.Coprime m' (orderOf r) := by
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
    have : r = x ^ j := by rw [← hm']; exact hj.symm
    exact hrR (by rw [this]; exact R.pow_mem hxR j)

private theorem exists_pElement_of_mem_map {G H : Type*} [Group G] [Finite G] [Group H] {p : ℕ}
    [Fact p.Prime] (φ : G →* H) {R : Subgroup G} {z : H} (hz : z ∈ R.map φ)
    (hzp : ∃ k : ℕ, orderOf z = p ^ k) :
    ∃ w ∈ R, (∃ k : ℕ, orderOf w = p ^ k) ∧ φ w = z := by
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨e, he, hφ⟩ := exists_pElement_lift φ (x := y) hzp
  exact ⟨y ^ e, R.pow_mem hy e, he, hφ⟩

theorem lambda_pRank {G H : Type} [Group G] [Finite G] [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (R : Subgroup G) [R.Normal] (φ : G →* H) {r : G}
    (hr : ∃ k : ℕ, orderOf r = p ^ k) (hrR : r ∉ R) (hgen : R ⊔ Subgroup.zpowers r = ⊤)
    (hz : ∃ z ∈ R.map φ, z ≠ 1 ∧ ∃ k : ℕ, orderOf z = p ^ k)
    (hRK : ∀ ψ : H, (∃ k : ℕ, orderOf ψ = p ^ k) → ψ ∉ R.map φ →
      2 ≤ CFSG.Open.pRank p (R.map φ ⊔ Subgroup.zpowers ψ)) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  have hle : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 1 := by omega
  have hcyc := CFSG.all_pSubgroups_isCyclic_of_pRank_le_one hp hp2 hle
  obtain ⟨k, hk⟩ := hr
  have hφr : ∃ j : ℕ, orderOf (φ r) = p ^ j := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (hk ▸ orderOf_map_dvd φ r)
    exact ⟨j, hj⟩
  by_cases hψ : φ r ∈ R.map φ
  ·
    set T : Set G := {w | w ∈ R ∧ ∃ k : ℕ, orderOf w = p ^ k} with hT
    have hTne : T.Nonempty := ⟨1, R.one_mem, 0, by simp⟩
    obtain ⟨w₀, hw₀T, hw₀max⟩ :=
      Set.exists_max_image T (fun w => orderOf (φ w)) (Set.toFinite T) hTne
    obtain ⟨hw₀R, a, ha⟩ := hw₀T
    obtain ⟨z, hzI, hz1, j, hj⟩ := hz
    obtain ⟨w₁, hw₁R, hw₁p, hw₁⟩ := exists_pElement_of_mem_map φ hzI ⟨j, hj⟩
    have hle1 : orderOf z ≤ orderOf (φ w₀) := by
      have := hw₀max w₁ ⟨hw₁R, hw₁p⟩
      rwa [hw₁] at this
    obtain ⟨e, he⟩ : ∃ e : ℕ, orderOf (φ w₀) = p ^ e := by
      obtain ⟨j', -, hj'⟩ := (Nat.dvd_prime_pow hp).1 (ha ▸ orderOf_map_dvd φ w₀)
      exact ⟨j', hj'⟩
    have he1 : 1 ≤ e := by
      by_contra h0
      have he0 : e = 0 := by omega
      rw [he0, pow_zero] at he
      have : orderOf z = 1 := by
        have := orderOf_pos z
        omega
      exact hz1 (orderOf_eq_one_iff.1 this)
    obtain ⟨y, hyR, hyp, hy⟩ := exists_pElement_of_mem_map φ hψ hφr
    obtain ⟨c, hc⟩ := hφr
    have hcle : c ≤ e := by
      have h1 := hw₀max y ⟨hyR, hyp⟩
      rw [hy, hc, he] at h1
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    have hrp : IsPGroup p (Subgroup.zpowers r) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
    obtain ⟨Q, hrQ⟩ := hrp.exists_le_sylow
    have hQc : IsCyclic ↥(Q : Subgroup G) := hcyc Q le_top Q.isPGroup'
    have hw₀p : IsPGroup p (Subgroup.zpowers w₀) := IsPGroup.of_card (by rw [Nat.card_zpowers, ha])
    obtain ⟨Q₁, hw₀Q₁⟩ := hw₀p.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₁ Q
    have hx'Q : g * w₀ * g⁻¹ ∈ (Q : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul w₀ (MulAut.conj g) _
        (hw₀Q₁ (Subgroup.mem_zpowers w₀))
    have hx'R : g * w₀ * g⁻¹ ∈ R := Subgroup.Normal.conj_mem ‹R.Normal› w₀ hw₀R g
    have hx'z := mem_zpowers_pow_of_mem_inf hp Q.isPGroup' hQc ⟨k, hk⟩
      (hrQ (Subgroup.mem_zpowers r)) hrR hx'Q hx'R
    have hmem : φ (g * w₀ * g⁻¹) ∈ Subgroup.zpowers (φ r ^ p) := by
      have := Subgroup.mem_map_of_mem φ hx'z
      rwa [MonoidHom.map_zpowers, map_pow] at this
    have h1 : orderOf (φ (g * w₀ * g⁻¹)) = p ^ e := by
      rw [← he, map_mul, map_mul, map_inv]
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj (φ g)) (φ w₀)
    have h2 : orderOf (φ (g * w₀ * g⁻¹)) ∣ orderOf (φ r ^ p) := orderOf_dvd_of_mem_zpowers hmem
    have h3 : orderOf (φ r ^ p) ∣ p ^ (c - 1) := by
      rcases c with _ | c'
      · have : φ r = 1 := orderOf_eq_one_iff.1 (by rw [hc, pow_zero])
        rw [this, one_pow, orderOf_one]
        exact one_dvd _
      · show orderOf (φ r ^ p) ∣ p ^ c'
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, mul_comm, ← pow_succ, ← hc, pow_orderOf_eq_one]
    have h4 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 (h1 ▸ h2.trans h3)
    omega
  · have h2 := hRK (φ r) hφr hψ
    have hmap : R.map φ ⊔ Subgroup.zpowers (φ r) = (⊤ : Subgroup G).map φ := by
      rw [← hgen, Subgroup.map_sup, MonoidHom.map_zpowers]
    rw [hmap] at h2
    have := CFSG.LocalAnalysis.RankThreeUC.S15.two_le_pRank_of_map φ hp hp2 ⊤ h2
    omega

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
