module

public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem sup_glbPrimeCore_eq_map_comap {G : Type} [Group G] [Finite G] (p : ℕ)
    {H R : Subgroup G} (hRH : R ≤ H) :
    R ⊔ GLBPrimeCore p H =
      (((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))).comap
        (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype := by
  have e : (primeComplementCore (G := H) p).map H.subtype = GLBPrimeCore p H := by
    rw [glbPrimeCore_eq_primeComplementCoreOf]
    rfl
  rw [QuotientGroup.comap_map_mk', Subgroup.map_sup, e, Subgroup.map_subgroupOf_eq_of_le hRH,
    sup_comm]

theorem exists_pow_map_eq_of_pow_two_pow_eq_one {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (t : A) {j : ℕ} (hj : f t ^ 2 ^ j = 1) :
    ∃ n : ℕ, (∃ a : ℕ, (t ^ n) ^ 2 ^ a = 1) ∧ f (t ^ n) = f t := by
  obtain ⟨a, u, hu, hau⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
  have hcop : u.Coprime (orderOf (f t)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hj)
      (Nat.Coprime.pow_right j (Odd.coprime_two_right hu))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨u * m, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, show u * m * 2 ^ a = orderOf t * m by rw [hau]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_mul, hm]

theorem stmtJ3Data_of (hS : KFactJ3Sylow) (hO : KFactJ3OuterInvolution)
    (hOR : KFactJ3OuterRank) : StmtJ3Data := by
  intro G _ _ P M H R h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKn, hK, hC⟩ := h.socle
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.reducedNongeneration
  have hRH : R ≤ H := h.ext.le_H
  have hRp : IsPGroup 3 R := h.ext.isPGroup
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  have hNX : Subgroup.normalizer ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :
      Set (H ⧸ primeComplementCore (G := H) 3)) ≤ X₀ :=
    (normalizer_le_weakCore_of_rank 3 Nat.prime_three _ hred.three_le_pRank).trans
      hred.weakCore_le
  have hIS := j3InSitu_of hS hO hOR hKn hK hC Rbar hNX hred.ne_top
  have hTX : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ X₀ :=
    Subgroup.le_normalizer.trans hNX
  have hT1 : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≠ ⊤ := fun h' =>
    hred.ne_top (eq_top_iff.mpr (h' ▸ hTX))
  have hZ1 := hIS.centerOf_ne_bot hT1
  have hD1 : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) 3), W ≤ X₀ →
      X₀ ≤ Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) 3)) →
      W = ⊥ ∨ centerOf (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ W :=
    fun W hW hWn => hIS.eq_bot_or_le Rbar.isPGroup' hTX hW hWn
  rw [hRbar] at hIS hZ1 hD1
  have hXb : ((centerOf R).subgroupOf H).map π = centerOf ((R.subgroupOf H).map π) :=
    map_inf_centralizer_eq hRH hRp
  have hX1 : centerOf R ≠ ⊥ := by
    intro h0
    apply hZ1
    rw [← hXb, h0, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hZp : IsPGroup 3 (centerOf ((R.subgroupOf H).map π)) :=
    (hRp.comap_subtype.map π).to_le inf_le_left
  have hsurv : D1SurvivorData 3 P M H R (centerOf R) := by
    refine h.ext.survivorData_of_map h.glob inf_le_left hX1 (fun W hW hWn hWc => ?_)
      (by rw [hXb]; exact hD1) (by rw [hXb]; exact inf_le_right.trans hIS.centralizer_center)
    rcases hD1 W hW ((Subgroup.normal_subgroupOf_iff_le_normalizer hW).mp hWn) with h0 | hle
    · exact h0
    · refine absurd ?_ hZ1
      rw [← inf_eq_left.mpr hle]
      exact inf_eq_bot_of_isPGroup Nat.prime_three hZp hWc
  have hB := sup_glbPrimeCore_eq_map_comap 3 hRH
  refine ⟨hsurv, pRank_inf_le_of_pRank_top_le Nat.prime_three hIS.pRank_le, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := hIS.nonabelian
    refine ⟨a, Subgroup.mem_subgroupOf.mp ha, b, Subgroup.mem_subgroupOf.mp hb, fun hab' => hab ?_⟩
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext hab']
  ·
    obtain ⟨_, ⟨⟨k, hkX, rfl⟩, hkN⟩, hk2, hkW⟩ := hIS.singer
    obtain ⟨o, ho, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
      (comap_normalizer_map_le_sup Nat.prime_three (primeComplementCore (G := H) 3)
        (primeComplementCore_coprime 3) hRp.comap_subtype hkN)
    have hπo : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    have hπt : π (o * t) = π t := by rw [map_mul, hπo, one_mul]
    have hoM : o ∈ (H ⊓ M).subgroupOf H := Subgroup.mem_subgroupOf.mpr
      ⟨o.2, h.ext.primeCore_le ((mem_primeComplementCore_iff_mem_glbPrimeCore 3 o).mp ho)⟩
    have htM : t ∈ (H ⊓ M).subgroupOf H := by
      simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hoM) hkX
    have htN : (t : G) ∈ Subgroup.normalizer (R : Set G) := by
      have h1 : (t : G) ∈ Subgroup.normalizer
          (((R.subgroupOf H).map H.subtype : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map H.subtype ⟨t, ht, rfl⟩
      rwa [Subgroup.map_subgroupOf_eq_of_le hRH] at h1
    obtain ⟨j, hj⟩ := hk2 ⟨π (o * t), Subgroup.mem_zpowers _⟩
    have hj' : π t ^ 2 ^ j = 1 := by
      rw [← hπt]
      simpa using congrArg Subtype.val hj
    obtain ⟨n, ⟨a, ha⟩, hn⟩ := exists_pow_map_eq_of_pow_two_pow_eq_one π t hj'
    refine ⟨(t : G) ^ n, by simpa using Subgroup.mem_subgroupOf.mp (Subgroup.pow_mem _ htM n),
      Subgroup.pow_mem _ htN n,
      isPGroup_zpowers_of_pow_prime_pow_eq_one (n := a) (by simpa using congrArg Subtype.val ha),
      fun W hWR hWidx hsW => ?_⟩
    have hWRb : (W.subgroupOf H).map π ≤ (R.subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono H hWR)
    refine hkW ((W.subgroupOf H).map π) hWRb ?_ ?_
    ·
      have hc : ∀ {U : Subgroup G}, U ≤ R → Nat.card ((U.subgroupOf H).map π) = Nat.card U :=
        fun {U} hU => (card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3)
          (T := U.subgroupOf H) (hRp.to_le hU).comap_subtype).trans
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hU.trans hRH)).toEquiv)
      have e1 := Subgroup.relIndex_mul_card W R
      rw [inf_eq_left.mpr hWR, hWidx] at e1
      have e2 := Subgroup.relIndex_mul_card ((W.subgroupOf H).map π) ((R.subgroupOf H).map π)
      rw [inf_eq_left.mpr hWRb, hc hWR, hc le_rfl] at e2
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (e2.trans e1.symm)
    ·
      have h1 : ((t ^ n) ^ 2 : H) ∈ (Subgroup.zpowers (((t : G) ^ n) ^ 2)).subgroupOf H := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, Subgroup.coe_pow]
        exact Subgroup.mem_zpowers _
      have h2 := map_mk_le_normalizer_map_mk (p := 3) (H := H) ((Subgroup.zpowers_le).mpr hsW)
        (Subgroup.mem_map_of_mem π h1)
      rwa [map_pow, hn, ← hπt] at h2
  ·
    rw [hB]
    intro k hk
    have h1 : (⟨k, hk.1⟩ : H) ∈ Subgroup.normalizer
        ((((R.subgroupOf H).map π).comap π : Subgroup H) : Set H) :=
      Subgroup.le_normalizer_comap π
        (hIS.le_normalizer (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk)))
    exact Subgroup.le_normalizer_map H.subtype ⟨⟨k, hk.1⟩, h1, rfl⟩
  ·
    intro k hk
    obtain ⟨e, he⟩ := hIS.two_top (π ⟨k, hk.1⟩)
      (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk))
    refine ⟨e, ?_⟩
    rw [hB]
    refine ⟨⟨k, hk.1⟩ ^ 2 ^ e, Subgroup.mem_comap.mpr ?_, by simp⟩
    rw [map_pow]
    exact he

end CFSG.AGLEmbedding
