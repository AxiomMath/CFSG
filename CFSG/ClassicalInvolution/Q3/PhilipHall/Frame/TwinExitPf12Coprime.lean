module

public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12

open CFSG CFSG.Open CFSG.ClassicalInvolution

set_option linter.unusedSectionVars false

section Abstract

variable {G : Type*} [Group G]

theorem fixes_of_fixes_centralizer [Finite G] {L : Subgroup G} (hL : IsPGroup 2 L) {α σ : G}
    (hαL : ∀ x ∈ L, α * x * α⁻¹ ∈ L) (hσ : σ ∈ L) (hασ : α * σ = σ * α) {m : ℕ} (hm : Odd m)
    (hαm : α ^ m = 1)
    (hfix : ∀ x ∈ L, σ * x = x * σ → α * x = x * α) : ∀ x ∈ L, α * x = x * α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent L := hL.isNilpotent
  obtain ⟨N, hN⟩ := Group.IsNilpotent.nilpotent L
  have main : ∀ n : ℕ, ∀ x : L, x ∈ Subgroup.upperCentralSeries L n → α * (x : G) * α⁻¹ = x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      have : x = 1 := by simpa using hx
      subst this
      simp
    | succ n ih =>
      intro x hx
      have hmem := Subgroup.mem_upperCentralSeries_succ_iff.mp hx ⟨σ, hσ⟩
      rw [commutatorElement_def] at hmem
      have hc := ih _ hmem
      set a : G := α * (x : G) * α⁻¹ with ha
      have haL : a ∈ L := hαL _ x.2
      have hασ' : α * σ * α⁻¹ = σ := by rw [hασ]; group
      have hc' : a * σ * a⁻¹ * σ⁻¹ = (x : G) * σ * (x : G)⁻¹ * σ⁻¹ := by
        have h1 : α * ((x : G) * σ * (x : G)⁻¹ * σ⁻¹) * α⁻¹ = a * σ * a⁻¹ * σ⁻¹ := by
          rw [ha]
          have : α * ((x : G) * σ * (x : G)⁻¹ * σ⁻¹) * α⁻¹ =
              (α * (x : G) * α⁻¹) * (α * σ * α⁻¹) * (α * (x : G) * α⁻¹)⁻¹ * (α * σ * α⁻¹)⁻¹ := by
            group
          rw [this, hασ']
        rw [← h1]
        simpa using hc
      set w : G := a⁻¹ * (x : G) with hw
      have hwL : w ∈ L := L.mul_mem (L.inv_mem haL) x.2
      have hσw : σ * w = w * σ := by
        have h2 : a * σ * a⁻¹ = (x : G) * σ * (x : G)⁻¹ := by
          have := hc'
          calc a * σ * a⁻¹ = (a * σ * a⁻¹ * σ⁻¹) * σ := by group
            _ = ((x : G) * σ * (x : G)⁻¹ * σ⁻¹) * σ := by rw [this]
            _ = (x : G) * σ * (x : G)⁻¹ := by group
        rw [hw]
        calc σ * (a⁻¹ * (x : G)) = a⁻¹ * (a * σ * a⁻¹) * (x : G) := by group
          _ = a⁻¹ * ((x : G) * σ * (x : G)⁻¹) * (x : G) := by rw [h2]
          _ = a⁻¹ * (x : G) * σ := by group
      have hαw : α * w = w * α := hfix w hwL hσw
      have hαw' : α * w * α⁻¹ = w := by rw [hαw]; group
      have hit : ∀ k : ℕ, α ^ k * (x : G) * (α ^ k)⁻¹ = (x : G) * (w ^ k)⁻¹ := by
        have hxa : α * (x : G) * α⁻¹ = (x : G) * w⁻¹ := by
          rw [← ha, hw]; group
        have hwk : ∀ k : ℕ, α * w ^ k * α⁻¹ = w ^ k := by
          intro k
          induction k with
          | zero => simp
          | succ k ihk =>
            have e : w ^ (k + 1) = w ^ k * w := pow_succ w k
            have : α * w ^ (k + 1) * α⁻¹ = (α * w ^ k * α⁻¹) * (α * w * α⁻¹) := by
              rw [e]; group
            rw [this, ihk, hαw']
            exact (pow_succ w k).symm
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          have e : α ^ (k + 1) * (x : G) * (α ^ (k + 1))⁻¹ =
              α * (α ^ k * (x : G) * (α ^ k)⁻¹) * α⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
          rw [e, ihk]
          have e2 : α * ((x : G) * (w ^ k)⁻¹) * α⁻¹ =
              (α * (x : G) * α⁻¹) * (α * w ^ k * α⁻¹)⁻¹ := by group
          rw [e2, hxa, hwk, pow_succ']
          group
      have hwm : w ^ m = 1 := by
        have := hit m
        rw [hαm] at this
        simp at this
        exact this
      have hw1 : w = 1 := by
        have hord : ∃ k, orderOf (⟨w, hwL⟩ : L) = 2 ^ k := (IsPGroup.iff_orderOf.mp hL) ⟨w, hwL⟩
        obtain ⟨k, hk⟩ := hord
        have hord' : orderOf (⟨w, hwL⟩ : L) = orderOf w := Subgroup.orderOf_mk _ _
        have hdvd : orderOf w ∣ m := orderOf_dvd_of_pow_eq_one hwm
        have hdvd2 : orderOf w ∣ 2 ^ k := by rw [← hord', hk]
        have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
        have h1 : orderOf w = 1 := (Nat.Coprime.coprime_dvd_left hdvd2 hcop).eq_one_of_dvd hdvd
        exact orderOf_eq_one_iff.mp h1
      have : a = (x : G) := by
        have h3 : (x : G) = a * w := by rw [hw]; group
        rw [h3, hw1]; simp
      exact this
  intro x hx
  have h1 : (⟨x, hx⟩ : L) ∈ Subgroup.upperCentralSeries L N := by rw [hN]; exact Subgroup.mem_top _
  have := main N ⟨x, hx⟩ h1
  simp only at this
  calc α * x = (α * x * α⁻¹) * α := by group
    _ = x * α := by rw [this]

end Abstract

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_odd_orderOf_of_pGroup {L : Subgroup G} (hL : IsPGroup 2 L) {y : G} (hy : y ∈ L)
    (hodd : Odd (orderOf y)) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hL) ⟨y, hy⟩
  have hord : orderOf (⟨y, hy⟩ : L) = orderOf y := Subgroup.orderOf_mk _ _
  rw [hord] at hk
  have hk0 : k = 0 := by
    by_contra hne
    have : Even (orderOf y) := by rw [hk]; exact (Nat.even_pow.mpr ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.mpr hodd) this
  rw [hk0] at hk
  exact orderOf_eq_one_iff.mp (by simpa using hk)

theorem odd_orderOf_of_mem_odd {Q : Subgroup G} (hQ : Odd (Nat.card Q)) {y : G} (hy : y ∈ Q) :
    Odd (orderOf y) :=
  Odd.of_dvd_nat hQ (Subgroup.orderOf_dvd_natCard Q hy)

open Balance in
theorem oddCoreIn_centralizer_le_centralizer_of_normal {P : Subgroup G} (hPn : P.Normal)
    (hP : IsPGroup 2 P) {z : G} (hz : IsPGroup 2 (Subgroup.zpowers z)) :
    oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ Subgroup.centralizer (P : Set G) := by
  have := hPn
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  set Q : Subgroup G := oddCoreIn C with hQ
  set L : Subgroup G := P ⊔ Subgroup.zpowers z with hLdef
  have hL : IsPGroup 2 L := IsPGroup.to_sup_of_normal_left hP hz
  have hzL : z ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hPL : P ≤ L := le_sup_left
  have hQodd : Odd (Nat.card Q) := odd_card_oddCoreIn C
  intro α hα
  have hαC : α ∈ C := oddCoreIn_le C hα
  have hαz : α * z = z * α := Subgroup.mem_centralizer_singleton_iff.mp hαC
  have hαL : ∀ x ∈ L, α * x * α⁻¹ ∈ L := by
    intro x hx
    obtain ⟨y, hy, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have h1 : α * z ^ n = z ^ n * α := ((show Commute α z from hαz).zpow_right n).eq
    have h2 : α * (y * z ^ n) * α⁻¹ = (α * y * α⁻¹) * z ^ n := by
      calc α * (y * z ^ n) * α⁻¹ = (α * y * α⁻¹) * (α * z ^ n * α⁻¹) := by group
        _ = (α * y * α⁻¹) * z ^ n := by rw [h1]; group
    rw [h2]
    exact L.mul_mem (hPL (hPn.conj_mem y hy α)) (L.zpow_mem hzL n)
  have hm : Odd (orderOf α) := odd_orderOf_of_mem_odd hQodd hα
  have hfix : ∀ x ∈ L, z * x = x * z → α * x = x * α := by
    intro x hxL hzx
    have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm
    have h1 : x * α⁻¹ * x⁻¹ ∈ Q := conj_mem_oddCoreIn hxC (Q.inv_mem hα)
    have h2 : α * x * α⁻¹ * x⁻¹ ∈ Q := by
      have := Q.mul_mem hα h1
      have e : α * (x * α⁻¹ * x⁻¹) = α * x * α⁻¹ * x⁻¹ := by group
      rwa [e] at this
    have h3 : α * x * α⁻¹ * x⁻¹ ∈ L := L.mul_mem (hαL x hxL) (L.inv_mem hxL)
    have h4 : α * x * α⁻¹ * x⁻¹ = 1 :=
      eq_one_of_odd_orderOf_of_pGroup hL h3 (odd_orderOf_of_mem_odd hQodd h2)
    calc α * x = (α * x * α⁻¹ * x⁻¹) * x * α := by group
      _ = x * α := by rw [h4]; group
  have hcomm := fixes_of_fixes_centralizer hL hαL hzL hαz hm (pow_orderOf_eq_one α) hfix
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  exact (hcomm p (hPL hp)).symm

theorem oddCoreIn_top_eq_bot' (hO : classicalInvolutionOddCore G = ⊥) :
    Balance.oddCoreIn (⊤ : Subgroup G) = ⊥ := by
  have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant
    (Subgroup.topEquiv (G := G)).symm
  have h2 : componentClassificationOddCore G = ⊥ := hO
  rw [h2, Subgroup.map_bot] at h1
  unfold Balance.oddCoreIn
  rw [← h1, Subgroup.map_bot]

open Balance in
theorem oddCoreIn_centralizer_eq_bot_of_mem_normal (hO : classicalInvolutionOddCore G = ⊥)
    {P : Subgroup G} (hPn : P.Normal) (hP : IsPGroup 2 P) {z : G} (hzP : z ∈ P) :
    oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  have := hPn
  have hz : IsPGroup 2 (Subgroup.zpowers z) := hP.to_le (Subgroup.zpowers_le.mpr hzP)
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  set Q : Subgroup G := oddCoreIn C with hQ
  set Y : Subgroup G := Subgroup.centralizer (P : Set G) with hY
  have hQY : Q ≤ Y := oddCoreIn_centralizer_le_centralizer_of_normal hPn hP hz
  have hYC : Y ≤ C := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hy z hzP).symm)
  have hYn : Y.Normal := by
    refine ⟨fun y hy g p hp => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hy (g⁻¹ * p * g) (by
      have := hPn.conj_mem p hp g⁻¹
      simpa using this)
    calc p * (g * y * g⁻¹) = g * ((g⁻¹ * p * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
      _ = (g * y * g⁻¹) * p := by group
  have := hYn
  have hQn : (Q.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQY).mpr
      (fun y hy => normalizer_oddCoreIn C (hYC hy))
  have hsub : IsSubnormal Q ⊤ :=
    IsSubnormal.step hQY hQn (IsSubnormal.step le_top inferInstance (IsSubnormal.refl _))
  exact le_bot_iff.mp
    ((le_oddCoreIn_of_isSubnormal hsub (odd_card_oddCoreIn C)).trans
      (oddCoreIn_top_eq_bot' hO).le)

open Balance in
theorem oddCoreIn_centralizer_eq_bot_of_centralizer_le {P : Subgroup G} (hPn : P.Normal)
    (hP : IsPGroup 2 P) (hcen : Subgroup.centralizer (P : Set G) ≤ P) {z : G}
    (hz : IsPGroup 2 (Subgroup.zpowers z)) :
    oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  have hQ := oddCoreIn_centralizer_le_centralizer_of_normal hPn hP hz
  set Q : Subgroup G := oddCoreIn (Subgroup.centralizer ({z} : Set G)) with hQdef
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  exact eq_one_of_odd_orderOf_of_pGroup hP (hcen (hQ hy))
    (odd_orderOf_of_mem_odd (odd_card_oddCoreIn _) hy)

end Ambient

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
