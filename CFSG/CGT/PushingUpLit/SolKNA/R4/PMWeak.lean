module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMFour

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem weak_alt {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) {s : G}
    (hJs : IsUniqueInvolution J s) (hsne : s ≠ z) {y : G} (hyS : y ∈ (S : Subgroup G))
    (hyJ : y ∈ J) (hy1 : y ≠ 1) :
    (y = s ∧ ∀ w ∈ J, orderOf w = 4 → w * z ≠ z * w) ∨
      ∃ V₀ ∈ USet (CoreAssembly.conjClass K),
        V₀ ≤ J ⊓ Subgroup.centralizer ({z} : Set G) ∧ y ∈ V₀ := by
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hK := CoreAssembly.mem_conjClass_self K
  have hJK : J ≠ K := by
    rintro rfl
    exact hsne ((hI.unique s hJs.mem hJs.sq).resolve_left hJs.ne_one)
  have hs2 : orderOf s = 2 :=
    orderOf_eq_prime (show s ^ 2 = 1 by rw [sq]; exact hJs.sq) hJs.ne_one
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyS)
  have hJC : Subgroup.zpowers y ≤ J ⊓ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hyJ, hd.hSz hyS⟩
  obtain ⟨V₀, hV₀, hyV₀'⟩ := IsSylow2In.exists_ge hy2 hJC
  have hyV₀ : y ∈ V₀ := hyV₀' (Subgroup.mem_zpowers y)
  have hord : 2 ≤ Nat.card V₀ := by
    have h1 : Nat.card (Subgroup.zpowers y) ≤ Nat.card V₀ := Subgroup.card_le_of_le hyV₀'
    rw [Nat.card_zpowers] at h1
    have h2 : 0 < orderOf y := orderOf_pos y
    have h3 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    omega
  have hsV₀ : s ∈ V₀ := S1911.mem_of_le_member hJs (hV₀.1.trans inf_le_left) hV₀.2.1 hord
  have hleft : V₀ = Subgroup.zpowers s → y = s ∧ ∀ w ∈ J, orderOf w = 4 → w * z ≠ z * w := by
    intro hV1
    have hcard2 : Nat.card V₀ = 2 := by rw [hV1, Nat.card_zpowers, hs2]
    refine ⟨?_, fun w hwJ hw4 hwz => ?_⟩
    · rw [hV1] at hyV₀
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyV₀
      have hk2 : s ^ (k % 2) = y := by
        have h := zpow_mod_orderOf s k
        rw [hs2] at h
        rw [← hk]
        simpa using h
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · rw [h0, zpow_zero] at hk2
        exact absurd hk2.symm hy1
      · rw [h1, zpow_one] at hk2
        exact hk2.symm
    · have hw2 : IsPGroup 2 (Subgroup.zpowers w) := S19T.isPGroup_zpowers_of_orderOf_four hw4
      obtain ⟨V₁, hV₁, hwV₁⟩ := IsSylow2In.exists_ge hw2
        (Subgroup.zpowers_le.mpr ⟨hwJ, Subgroup.mem_centralizer_singleton_iff.mpr hwz⟩ :
          Subgroup.zpowers w ≤ J ⊓ Subgroup.centralizer ({z} : Set G))
      have h4 : 4 ≤ Nat.card V₁ := by
        calc 4 = Nat.card (Subgroup.zpowers w) := by rw [Nat.card_zpowers, hw4]
          _ ≤ Nat.card V₁ := Subgroup.card_le_of_le hwV₁
      have h5 := IsSylow2In.natCard_eq hV₀ hV₁
      omega
  rcases Sec6Gen.Pair.six_two hΩ ⟨hK, hJ, hI, hJs, hsne.symm⟩ hV₀ hsV₀ with
    ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
  · exact Or.inl (hleft hV1)
  · exact Or.inl (hleft hV1)
  · exact Or.inr ⟨V₀, hV3, hV₀.1, hyV₀⟩
  · exact absurd ((hV₀.1.trans inf_le_right).trans hd.tight.centralizer_le_normalizer)
      (S1911.not_le_normalizer_of_mem_rSet hd.tight.edgeless hJ hK hJK hV4
        (hV₀.1.trans inf_le_left))

theorem weak_usets (hr : 4 ≤ r) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) {s : G}
    (hJs : IsUniqueInvolution J s) (hsne : s ≠ z) {V₀ : Subgroup G}
    (hV₀ : V₀ ∈ USet (CoreAssembly.conjClass K)) (hV₀J : V₀ ≤ J)
    (hV₀z : V₀ ≤ Subgroup.centralizer ({z} : Set G)) {y : G} (hyV₀ : y ∈ V₀) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * y * c⁻¹ ∈ pmSubgroup (K ⊓ W) := by
  have hΩ := hd.tight.hypGen
  have hV2 : IsPGroup 2 V₀ := Sec6Gen.isPGroup_of_mem_USet hΩ hV₀
  obtain ⟨c, hcz, hcV⟩ := exists_conj_le_of_sylow_le S hd.hSz hV₀z hV2
  have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hU' : conjSub c V₀ ∈ USet (CoreAssembly.conjClass K) :=
    S19B.conjSub_mem_USet hΩ.conjInvariant hV₀ c
  have hU'J : conjSub c V₀ ≤ conjSub c J := conjSub_mono hV₀J
  have hJc : conjSub c J ∈ CoreAssembly.conjClass K := hΩ.conjInvariant c J hJ
  have hJcs : IsUniqueInvolution (conjSub c J) (c * s * c⁻¹) := hJs.conj c
  have hsub : conjSub c V₀ ≤ pmSubgroup (K ⊓ W) := by
    rcases hd.invol_eq_or_of_mem_USet hU' hcV hJc hU'J hJcs with h | h | h
    · exfalso
      apply hsne
      calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
        _ = z := by rw [h, mul_assoc, ← hcz', inv_mul_cancel_left]
    ·
      have hJt : IsUniqueInvolution (conjSub c J) t := by
        have h' := hJcs
        rw [h] at h'
        exact h'
      have hJL : conjSub c J = L :=
        hd.tight.eq_of_isUniqueInvolution_member hJc hd.memL hJt hd.invL
      have hsub1 : conjSub c V₀ ≤ (S : Subgroup G) ⊓ L := fun x hx =>
        ⟨hcV hx, by have h'' := hU'J hx; rwa [hJL] at h''⟩
      rw [hd.inf_member_eq] at hsub1
      exact hsub1.trans hd.V_le_pm
    ·
      obtain ⟨r₀, hr₀R, hr₀t⟩ := hd.exists_conj_eq_mul
      have hLr : conjSub r₀ L ∈ CoreAssembly.conjClass K := hΩ.conjInvariant r₀ L hd.memL
      have hLrz : IsUniqueInvolution (conjSub r₀ L) (t * z) := by
        have h' := hd.invL.conj r₀
        rw [hr₀t] at h'
        exact h'
      have hJz : IsUniqueInvolution (conjSub c J) (t * z) := by
        have h' := hJcs
        rw [h] at h'
        exact h'
      have hJr : conjSub c J = conjSub r₀ L :=
        hd.tight.eq_of_isUniqueInvolution_member hJc hLr hJz hLrz
      have hsub1 : conjSub c V₀ ≤ conjSub r₀ V := by
        intro x hx
        have hxS : x ∈ (S : Subgroup G) := hcV hx
        have hxL : x ∈ conjSub r₀ L := by
          have h'' := hU'J hx
          rwa [hJr] at h''
        rw [mem_conjSub_iff] at hxL ⊢
        have hxS' : r₀⁻¹ * x * r₀ ∈ (S : Subgroup G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hr₀R.1) hxS) hr₀R.1
        have hmem : r₀⁻¹ * x * r₀ ∈ (S : Subgroup G) ⊓ L := ⟨hxS', hxL⟩
        rwa [hd.inf_member_eq] at hmem
      exact hsub1.trans (hd.conjSub_V_le_pm hr hr₀R)
  exact ⟨c, hcz, hsub (conj_mem_conjSub (n := c) hyV₀)⟩

theorem hweak (hr : 4 ≤ r) {y : G} (hy : y ∈ (S : Subgroup G) ⊓ K) (hy1 : y ≠ 1) {g : G}
    (hg : g⁻¹ * y * g ∈ (S : Subgroup G)) : g⁻¹ * y * g ∈ pmSubgroup (K ⊓ W) := by
  have hSz := hd.hSz
  have hI := hd.tight.isUniqueInvolution
  by_cases hgK : g ∈ Subgroup.normalizer (K : Set G)
  · have hK' : g⁻¹ * y * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) y).mp hy.2
      simpa using this
    exact hd.inf_core_le_pm hr ⟨hg, hK'⟩
  · have hΩ := hd.tight.hypGen
    have hJ : conjSub g⁻¹ K ∈ CoreAssembly.conjClass K :=
      hΩ.conjInvariant g⁻¹ K (CoreAssembly.mem_conjClass_self K)
    have hJs : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
      have h := hI.conj g⁻¹
      rwa [inv_inv] at h
    have hyJ : g⁻¹ * y * g ∈ conjSub g⁻¹ K := by
      have h := conj_mem_conjSub (n := g⁻¹) hy.2
      rwa [inv_inv] at h
    have hy'1 : g⁻¹ * y * g ≠ 1 := by
      intro h
      apply hy1
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hsne : g⁻¹ * z * g ≠ z := by
      intro h
      apply hgK
      rw [hd.tight.normEq, Subgroup.mem_centralizer_singleton_iff]
      calc g * z = g * (g⁻¹ * z * g) := by rw [h]
        _ = z * g := by group
    rcases hd.weak_alt hJ hJs hsne hg hyJ hy'1 with ⟨hys, hno⟩ | ⟨V₀, hV₀, hV₀le, hyV₀⟩
    · by_contra hcon
      have hs2 : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by rw [hys]; exact hJs.sq
      obtain ⟨w, hwR, hwx, -, hw4⟩ := hd.exists_order_four hr hg hs2 hcon
      rw [hys] at hwx
      obtain ⟨w', hw'J, hw'4, hw'z⟩ := hd.exists_comm_of_comm hJ hJs hsne hwR.2 hw4 hwx
      exact hno w' hw'J hw'4 hw'z
    · obtain ⟨c, hcz, hc⟩ := hd.weak_usets hr hJ hJs hsne hV₀ (hV₀le.trans inf_le_left)
        (hV₀le.trans inf_le_right) hyV₀
      have hy'z : g⁻¹ * y * g ∈ Subgroup.centralizer ({z} : Set G) := hSz hg
      have hcy : c * (g⁻¹ * y * g) * c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hcz hy'z) (Subgroup.inv_mem _ hcz)
      have hyU : c * (g⁻¹ * y * g) * c⁻¹ ∈
          Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) :=
        pmSubgroup_le_normalizer _ hc
      have e : c⁻¹ * (c * (g⁻¹ * y * g) * c⁻¹) * c = g⁻¹ * y * g := by group
      have hyU' : c⁻¹ * (c * (g⁻¹ * y * g) * c⁻¹) * c ∈
          Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) := by
        rw [e]
        exact hd.le_normalizer_inf_W hr hg
      have := (hd.actsPM_conj_iff_inf hr hcz hcy hyU hyU').mp hc
      rwa [e] at this

end TightSylowDataTR

end CFSG.CGT.PushingUpLit.SolKNA.R4
