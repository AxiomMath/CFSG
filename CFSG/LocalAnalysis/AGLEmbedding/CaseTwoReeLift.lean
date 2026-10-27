module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G} {z : G}

theorem D1Extremal.centralizer_le_of_reducedCentralizer (hext : D1Extremal p P M H R)
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    (hodd : Odd (Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)))
    {J : D1CzQuot p z} (hJX : J ∈ d1CzX0 p M z) (hJ2 : J ^ 2 = 1) (hJ1 : J ≠ 1)
    {X : Subgroup (D1CzQuot p z)} (hXp : IsPGroup p X) (hXX : X ≤ d1CzX0 p M z)
    (hXJ : X ≤ Subgroup.centralizer ({J} : Set (D1CzQuot p z)))
    (hXR : Nat.card R ≤ Nat.card X) (hXr : Open.pRank p R < Open.pRank p X) :
    Subgroup.centralizer ({J} : Set (D1CzQuot p z)) ≤ d1CzX0 p M z := by
  have hp := hext.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G)
  set OC := primeComplementCore (G := C) p
  set ρ := QuotientGroup.mk' OC
  have hOC := primeComplementCore_coprime (G := C) p
  have hO2 : Nat.Coprime 2 (Nat.card OC) := Nat.coprime_two_left.mpr hodd
  have hmemM : ∀ g : C, ρ g ∈ d1CzX0 p M z → (g : G) ∈ M := by
    rintro g ⟨c, hc, hcg⟩
    have h1 : c⁻¹ * g ∈ OC := by
      rw [← QuotientGroup.ker_mk' OC, MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.mpr hcg
    simpa using M.mul_mem hc.2 (hext.mem_of_mem_primeCore hRz h1)
  obtain ⟨c, hc, hcJ⟩ := hJX
  obtain ⟨m, hj2, hjJ⟩ := exists_isPGroup_zpowers_pow_eq ρ (y := c) (by rw [hcJ, hJ2])
  set j : C := c ^ m
  have hjJ' : ρ j = J := hjJ.trans hcJ
  have hj1 : (j : G) ≠ 1 := fun h => hJ1 (by rw [← hjJ', show j = 1 from Subtype.ext h, map_one])
  have hlift : ∀ x ∈ Subgroup.centralizer ({J} : Set (D1CzQuot p z)),
      ∃ g ∈ Subgroup.centralizer ({j} : Set C), ρ g = x := fun x hx =>
    exists_mem_centralizer_mk_eq Nat.prime_two OC hO2 hj2 (by rw [hjJ']; exact hx)
  set W : Subgroup C := Subgroup.centralizer ({j} : Set C) ⊓ M.subgroupOf C
  have hXW : X ≤ W.map ρ := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hlift x (hXJ hx)
    exact ⟨g, ⟨hg, hmemM g (hXX hx)⟩, rfl⟩
  obtain ⟨T, hTW, hTp, hTX⟩ := exists_isPGroup_le_map_eq ρ hXp hXW
  set Xh : Subgroup G := T.map C.subtype
  have hXhp : IsPGroup p Xh := hTp.map _
  have hXhT : Xh.subgroupOf C = T := Subgroup.comap_map_eq_self_of_injective C.subtype_injective T
  have hXhcard : Nat.card Xh = Nat.card X := by
    obtain ⟨φ, -⟩ := exists_mulEquiv_map_mk OC hp hOC hXhp (Subgroup.map_subtype_le T)
    rw [Nat.card_congr φ.toEquiv, hXhT, hTX]
  have hXhr : Open.pRank p Xh = Open.pRank p X := by
    rw [← hTX, pRank_map_mk_eq_pRank_map_subtype hp OC hOC T]
  set N := Subgroup.normalizer ((Subgroup.zpowers (j : G) : Subgroup G) : Set G)
  have hj2G : IsPGroup 2 (Subgroup.zpowers (j : G)) := by
    have h := hj2.map C.subtype
    rwa [MonoidHom.map_zpowers] at h
  have hN : IsTwoLocal N := ⟨_, by rwa [Ne, Subgroup.zpowers_eq_bot], hj2G, rfl⟩
  have hCN : ∀ g : C, g ∈ Subgroup.centralizer ({j} : Set C) → (g : G) ∈ N := fun g hg =>
    mem_normalizer_zpowers_of_mem_zpowers (by
      rw [show (g : G) * (j : G) * (g : G)⁻¹ = j by
        rw [← Subgroup.coe_mul, Subgroup.mem_centralizer_singleton_iff.mp hg, Subgroup.coe_mul,
          mul_inv_cancel_right]]
      exact Subgroup.mem_zpowers _)
  have hXhN : Xh ≤ N := by
    rintro _ ⟨t, ht, rfl⟩
    exact hCN t (hTW ht).1
  have hXhM : Xh ≤ M := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hTW ht).2
  have hNM : N ≤ M := hext.le_of_card_le_of_pRank_lt hXhM hXhp (hXhcard ▸ hXR) (hXhr ▸ hXr) hN
    hXhN
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hlift x hx
  exact ⟨g, ⟨g.2, hNM (hCN g hg)⟩, rfl⟩

variable {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} {P₃ : Sylow 3 G}

theorem D1CaseTwoData.card_inf_le (hd : D1CaseTwoData 3 P₃ M H R Rbar)
    (hL28 : KFactL28AutThree) {L : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hL : IsComponentOf L ⊤) (hLX : ¬ L ≤ d1X0 3 M H) (hLc : IsCaseTwoGroup 3 L) {z : H}
    (hzR : (z : G) ∈ R) (hzp : orderOf (z : G) = 3)
    (hRz : R ≤ Subgroup.centralizer ({(z : G)} : Set G))
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) 3) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) 3)))
    {K : Subgroup (D1CzQuot 3 (z : G))} (hzK : d1CzElt 3 (z : G) ∉ K) :
    Nat.card (((R.subgroupOf (Subgroup.centralizer ({(z : G)} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({(z : G)} : Set G)) 3)) ⊓
        K : Subgroup (D1CzQuot 3 (z : G)))) ≤ 27 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set C := Subgroup.centralizer ({(z : G)} : Set G)
  set OC := primeComplementCore (G := C) 3
  set ρ := QuotientGroup.mk' OC
  set OH := primeComplementCore (G := H) 3
  set π := QuotientGroup.mk' OH
  have hOC := primeComplementCore_coprime (G := C) 3
  have hOH := primeComplementCore_coprime (G := H) 3
  have hRp : IsPGroup 3 R := hd.cfg.ext.isPGroup
  set S : Subgroup G := R ⊓ (K.comap ρ).map C.subtype
  have hSR : S ≤ R := inf_le_left
  have hSp : IsPGroup 3 S := hRp.to_le hSR
  have h1 : (R.subgroupOf C).map ρ ⊓ K ≤ (S.subgroupOf C).map ρ := by
    rintro _ ⟨⟨r, hr, rfl⟩, hrK⟩
    exact ⟨r, ⟨hr, r, hrK, rfl⟩, rfl⟩
  obtain ⟨φC, -⟩ := exists_mulEquiv_map_mk OC hp hOC hSp (hSR.trans hRz)
  obtain ⟨φH, -⟩ := exists_mulEquiv_map_mk OH hp hOH hSp (hSR.trans hd.cfg.ext.le_H)
  set Sb := (S.subgroupOf H).map π
  have hSbR : Sb ≤ (Rbar : Subgroup (H ⧸ OH)) := by
    rw [hd.cfg.rbar]
    exact Subgroup.map_mono fun s hs => hSR hs
  have hZc : IsCyclic ((Rbar : Subgroup (H ⧸ OH)) ⊓ Subgroup.centralizer (L : Set (H ⧸ OH)) :
      Subgroup (H ⧸ OH)) := by
    by_contra hnc
    have h2 := two_le_pRank_of_isPGroup_not_isCyclic hp (by norm_num)
      (Rbar.isPGroup'.to_le inf_le_left) hnc
    have h1 := hd.cfg.red.pRank_inf_centralizer_le_one_of_not_le hL hLX
    omega
  have hzZ : π z ∈ (Rbar : Subgroup (H ⧸ OH)) ⊓ Subgroup.centralizer (L : Set (H ⧸ OH)) :=
    ⟨by rw [hd.cfg.rbar]; exact ⟨z, hzR, rfl⟩, hzL⟩
  have hzp' : orderOf (π z) = 3 :=
    orderOf_mk_of_coprime hp OH hOH ((Subgroup.orderOf_coe z).symm.trans hzp)
  have hSbC : Sb ⊓ Subgroup.centralizer (L : Set (H ⧸ OH)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨s, hs, rfl⟩, hsL⟩
    obtain ⟨hsR, c, hcK, hcs⟩ := hs
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxZ : π s ∈ (Rbar : Subgroup (H ⧸ OH)) ⊓ Subgroup.centralizer (L : Set (H ⧸ OH)) :=
      ⟨hSbR ⟨s, ⟨hsR, c, hcK, hcs⟩, rfl⟩, hsL⟩
    have hxp : IsPGroup 3 (Subgroup.zpowers (π s)) :=
      Rbar.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxZ.1)
    obtain ⟨t, ht⟩ : ∃ t : Subgroup.zpowers (π s), orderOf t = 3 := by
      refine exists_prime_orderOf_dvd_card' 3 ?_
      rcases hxp.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.zpowers_eq_bot.mp (Subgroup.card_eq_one.mp h1)) hx1
      · exact h1
    have htZ : (t : H ⧸ OH) ∈
        (Rbar : Subgroup (H ⧸ OH)) ⊓ Subgroup.centralizer (L : Set (H ⧸ OH)) :=
      Subgroup.zpowers_le.mpr hxZ t.2
    have hzt := mem_zpowers_of_orderOf_eq_of_isCyclic hzZ htZ
      (by rw [hzp', Subgroup.orderOf_coe, ht])
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.zpowers_le.mpr t.2 hzt)
    have hsn : s ^ n = z := eq_of_mk_eq_of_isPGroup hp OH hOH hRp.comap_subtype
      ((R.subgroupOf H).zpow_mem hsR n) hzR (by rw [map_zpow]; exact hn)
    apply hzK
    have hcs' : (c : G) = (s : G) := hcs
    have hcz : c ^ n = ⟨(z : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
      apply Subtype.ext
      change ((c ^ n : C) : G) = (z : G)
      rw [Subgroup.coe_zpow, hcs', ← Subgroup.coe_zpow, hsn]
    rw [d1CzElt, ← hcz, map_zpow]
    exact K.zpow_mem hcK n
  calc Nat.card ((R.subgroupOf C).map ρ ⊓ K : Subgroup (D1CzQuot 3 (z : G)))
      ≤ Nat.card ((S.subgroupOf C).map ρ) := Subgroup.card_le_of_le h1
    _ = Nat.card Sb := (Nat.card_congr φC.toEquiv).symm.trans (Nat.card_congr φH.toEquiv)
    _ ≤ 27 := card_le_of_inf_centralizer_eq_bot hL28 hLc (hSp.comap_subtype.map π)
      (hSbR.trans (hd.cfg.red.sylow_le_normalizer_component hL)) hSbC

end CFSG.AGLEmbedding
