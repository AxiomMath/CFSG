module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Three
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Inv

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7)
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem eq_setStabIn_of_setting_F4 (h526 : Stmt5_2_6_F4)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4)
    (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    H = setStabIn M2 π {5, 6} := by
  obtain ⟨-, -, -, -, hcardA⟩ := setting_K_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  exact (eq_setStabIn_of_card_map_F4 hQ hyp hM23 hS hcardA).1

theorem cycleType_map_eq_three_of_mem_oTwoUpper_F4
    (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {k : G}
    (hkK : k ∈ oTwoUpper H) (hk3 : orderOf k = 3) (hkM2 : k ∈ M2) :
    (π ⟨k, hkM2⟩).cycleType = {3} := by
  have hHstab := eq_setStabIn_of_setting_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hkH : k ∈ H := oTwoUpper_le H hkK
  rw [hHstab, mem_setStabIn] at hkH
  obtain ⟨hkM2', hp⟩ := hkH
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  exact cycleType_eq_three_of_smul_eq (orderOf_map_eq_three hS.ker_eq hU2 hkM2 hk3) hp

theorem eq_one_of_fixed_of_cycleType_eq_three_F4
    (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {π' : ↥M2 →* A7}
    {ρ : A7 →* MulAut ↥(pCoreOf 2 M2)} (hker : π'.ker = (pCoreOf 2 M2).subgroupOf M2)
    (hρ : ∀ (g : ↥M2) (u : ↥(pCoreOf 2 M2)),
      ((ρ (π' g) u : ↥(pCoreOf 2 M2)) : G) = g * u * (g : G)⁻¹)
    (hπ' : ∀ g : ↥M2, ((π' g : A7) : Equiv.Perm (Fin 7)) = π g) {σ : A7}
    (hσ : (σ : Equiv.Perm (Fin 7)).cycleType = {3}) {u : ↥(pCoreOf 2 M2)} (hu : ρ σ u = u) :
    u = 1 := by
  obtain ⟨k, hkK, hk3, hkfix⟩ :=
    exists_fpf_three_of_setting_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hkM2 : k ∈ M2 := hS.K_lt.le hkK
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hk3' : orderOf (π' ⟨k, hkM2⟩) = 3 := orderOf_map_eq_three hker hU2 hkM2 hk3
  have hct : ((π' ⟨k, hkM2⟩ : A7) : Equiv.Perm (Fin 7)).cycleType = {3} := by
    rw [hπ']
    exact cycleType_map_eq_three_of_mem_oTwoUpper_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hkK hk3
      hkM2
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_cycleType_eq_A7 hk3' (hct.trans hσ.symm))
  have hcc : ∀ v, ρ c (ρ c⁻¹ v) = v := fun v => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

  have hfix' : ρ (π' ⟨k, hkM2⟩) (ρ c⁻¹ u) = ρ c⁻¹ u := by
    have e : π' ⟨k, hkM2⟩ = c⁻¹ * σ * c := by rw [← hc]; group
    rw [e, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hcc, hu]
  have hk' : k * ((ρ c⁻¹ u : ↥(pCoreOf 2 M2)) : G) * k⁻¹ = ρ c⁻¹ u := by
    have := hρ ⟨k, hkM2⟩ (ρ c⁻¹ u)
    rw [hfix'] at this
    exact this.symm
  have hu'1 : ρ c⁻¹ u = 1 := Subtype.ext (hkfix _ (ρ c⁻¹ u).2 hk')
  calc u = ρ c (ρ c⁻¹ u) := (hcc u).symm
    _ = 1 := by rw [hu'1, map_one]

theorem exists_fixed_of_cycleType_eq_three_three_F4
    (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {π' : ↥M2 →* A7}
    {ρ : A7 →* MulAut ↥(pCoreOf 2 M2)} (hker : π'.ker = (pCoreOf 2 M2).subgroupOf M2)
    (hρ : ∀ (g : ↥M2) (u : ↥(pCoreOf 2 M2)),
      ((ρ (π' g) u : ↥(pCoreOf 2 M2)) : G) = g * u * (g : G)⁻¹)
    (hπ' : ∀ g : ↥M2, ((π' g : A7) : Equiv.Perm (Fin 7)) = π g)
    (hU16 : Nat.card ↥(pCoreOf 2 M2) = 16) {σ : A7}
    (hσ : (σ : Equiv.Perm (Fin 7)).cycleType = {3, 3}) :
    ∃ u : ↥(pCoreOf 2 M2), u ≠ 1 ∧ ρ σ u = u := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

  have ha3 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have hb3 : (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 3 5).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  let a : A7 := ⟨_, Equiv.Perm.mem_alternatingGroup.mpr ha3.sign⟩
  let b : A7 := ⟨_, Equiv.Perm.mem_alternatingGroup.mpr hb3.sign⟩
  have hdisj : Equiv.Perm.Disjoint (a : Equiv.Perm (Fin 7)) b := by
    show Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2)
      (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 3 5)
    intro x
    fin_cases x <;> decide
  have hab : Commute a b := Subtype.ext hdisj.commute.eq
  have hao : orderOf a = 3 := by rw [← Subgroup.orderOf_coe]; exact ha3.orderOf
  have hbo : orderOf b = 3 := by rw [← Subgroup.orderOf_coe]; exact hb3.orderOf

  have hcyc : ∀ (x : A7), (x : Equiv.Perm (Fin 7)).IsThreeCycle → ∀ c ∈ Subgroup.zpowers x,
      c ≠ 1 → (c : Equiv.Perm (Fin 7)).cycleType = {3} := by
    intro x hx c hc hc1
    have hxo : orderOf x = 3 := by rw [← Subgroup.orderOf_coe]; exact hx.orderOf
    have hco : orderOf c = 3 := by
      have hd := orderOf_dvd_of_mem_zpowers hc
      rw [hxo] at hd
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hc1
      · exact h1
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine cycleType_eq_three_of_card_support_lt (by rw [Subgroup.orderOf_coe]; exact hco) ?_
    have hle := Finset.card_le_card
      (Equiv.Perm.support_zpow_le (x : Equiv.Perm (Fin 7)) i)
    rw [Subgroup.coe_zpow]
    rw [hx.card_support] at hle
    omega
  have hfix : ∀ (x : A7), (x : Equiv.Perm (Fin 7)).IsThreeCycle → ∀ c ∈ Subgroup.zpowers x,
      c ≠ 1 → ∀ u : ↥(pCoreOf 2 M2), ρ c u = u → u = 1 := fun x hx c hc hc1 u hu =>
    eq_one_of_fixed_of_cycleType_eq_three_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hker hρ hπ'
      (hcyc x hx c hc hc1) hu
  have hfin : Finite ↥(pCoreOf 2 M2) := Nat.finite_of_card_ne_zero (by rw [hU16]; norm_num)
  obtain ⟨c, hc, d, hd, hc1, hd1, u, hu1, hu⟩ :=
    exists_fixed_of_commute ρ hU16 hao hbo hab (hfix a ha3) (hfix b hb3)

  have hcd : ((c * d : A7) : Equiv.Perm (Fin 7)).cycleType = {3, 3} := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hci := hcyc a ha3 _ hc hc1
    have hdj := hcyc b hb3 _ hd hd1
    rw [Subgroup.coe_mul]
    rw [Subgroup.coe_zpow] at hci hdj ⊢
    rw [Subgroup.coe_zpow, (hdisj.zpow_disjoint_zpow i j).cycleType_mul, hci, hdj]
    decide
  have hcdo : orderOf (c * d) = 3 := by
    rw [← Subgroup.orderOf_coe, ← Equiv.Perm.lcm_cycleType, hcd]
    decide
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_cycleType_eq_A7 hcdo (hcd.trans hσ.symm))
  have hgg : ∀ v, ρ g⁻¹ (ρ g v) = v := fun v => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  refine ⟨ρ g u, fun h => hu1 ?_, ?_⟩
  · rw [← hgg u, h, map_one]
  · rw [← hg, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hgg, hu]

theorem exists_involution_commute_of_mem_M2_F4
    (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {x : G} (hx : x ∈ M2)
    (hx3 : orderOf x = 3) : ∃ i : G, orderOf i = 2 ∧ i * x = x * i := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π', ρ, hsurj, hker, -, hρ, hU16, hU2', -, -, hπ'⟩ := exists_rho_of_setting_F4 hQ hyp hM23 hS
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hUN : M2 ≤ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)
  have hσ3 : orderOf (π' ⟨x, hx⟩) = 3 := orderOf_map_eq_three hker hU2 hx hx3
  rcases cycleType_of_orderOf_eq_three hσ3 with h3 | h33
  ·
    have ha3 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2).IsThreeCycle :=
      Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    let a : A7 := ⟨_, Equiv.Perm.mem_alternatingGroup.mpr ha3.sign⟩
    let t : A7 := ⟨Equiv.swap 3 4 * Equiv.swap 5 6, Equiv.Perm.mem_alternatingGroup.mpr (by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
      decide)⟩
    have hao : orderOf a = 3 := by rw [← Subgroup.orderOf_coe]; exact ha3.orderOf
    have hta : t * a = a * t := Subtype.ext (show
      (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 5 6) * (Equiv.swap 0 1 * Equiv.swap 0 2) =
        (Equiv.swap 0 1 * Equiv.swap 0 2) * (Equiv.swap 3 4 * Equiv.swap 5 6) by decide)
    have htt : t * t = 1 := Subtype.ext (show
      (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 5 6) * (Equiv.swap 3 4 * Equiv.swap 5 6) = 1 by decide)
    have ht1 : t ≠ 1 := fun h => by
      have h' := congrArg (fun s : A7 => (s : Equiv.Perm (Fin 7)) 3) h
      change (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 5 6 : Equiv.Perm (Fin 7)) 3 =
        (1 : Equiv.Perm (Fin 7)) 3 at h'
      exact absurd h' (by decide)
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_cycleType_eq_A7 hao (ha3.trans h3.symm))
    have hτσ : c * t * c⁻¹ * π' ⟨x, hx⟩ = π' ⟨x, hx⟩ * (c * t * c⁻¹) := by
      rw [← hc]
      calc c * t * c⁻¹ * (c * a * c⁻¹) = c * (t * a) * c⁻¹ := by group
        _ = c * (a * t) * c⁻¹ := by rw [hta]
        _ = c * a * c⁻¹ * (c * t * c⁻¹) := by group
    have hτ1 : c * t * c⁻¹ ≠ 1 := fun h => ht1 (conj_eq_one_iff.mp h)
    have hτ2 : c * t * c⁻¹ * (c * t * c⁻¹) = 1 := by
      calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    obtain ⟨g, hg⟩ := hsurj (c * t * c⁻¹)
    have hgU : (g : G) ∉ pCoreOf 2 M2 := fun h => hτ1 (by
      have hk : g ∈ π'.ker := by rw [hker]; exact Subgroup.mem_subgroupOf.mpr h
      rw [← hg]
      exact hk)
    have hg2 : (g : G) * g ∈ pCoreOf 2 M2 := by
      have hk : g * g ∈ π'.ker := by rw [MonoidHom.mem_ker, map_mul, hg, hτ2]
      rw [hker, Subgroup.mem_subgroupOf] at hk
      exact hk
    have hxg : (g : G)⁻¹ * (x * g * x⁻¹) ∈ pCoreOf 2 M2 := by
      have hk : g⁻¹ * (⟨x, hx⟩ * g * (⟨x, hx⟩ : ↥M2)⁻¹) ∈ π'.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hg]
        rw [← hτσ]
        group
      rw [hker, Subgroup.mem_subgroupOf] at hk
      exact hk
    exact exists_involution_commute_of_coset hU2 hx3 (hUN hx) (hUN g.2) hxg hgU hg2
  ·
    obtain ⟨u, hu1, hu⟩ := exists_fixed_of_cycleType_eq_three_three_F4 h526 h1284 hSz hU4 hsp hQ hyp
      hM23 hS hker hρ hπ' hU16 h33
    refine ⟨u, ?_, ?_⟩
    · have hu2 : (u : G) ^ 2 = 1 := by
        have := congrArg Subtype.val (hU2' u)
        simpa using this
      exact orderOf_eq_prime hu2 (fun h => hu1 (Subtype.ext h))
    · have hxu : x * (u : G) * x⁻¹ = u :=
        (hρ ⟨x, hx⟩ u).symm.trans (congrArg Subtype.val hu)
      calc (u : G) * x = x * u * x⁻¹ * x := by rw [hxu]
        _ = x * u := by group

theorem sec52G2_le_of_setting_F4 (h526 : Stmt5_2_6_F4)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4)
    (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H ≤ M2 := by
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hHM2 : H ≤ M2 :=
    (eq_oTwoUpper_sup_of_isSylowTwoOf' hTH).le.trans (sup_le hS.K_lt.le hS.T_le)
  obtain ⟨-, -, hQeq, -, -⟩ := setting_K_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hN := normalizer_pCoreOf_eq_F4 hQ h5211 hyp hM23 hS
  refine sup_le (sup_le ?_ ?_) hS.K_lt.le
  · calc D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hyp.D_le
      _ ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      _ = M2 := by rw [hQeq, hN]
  · exact inf_le_left.trans
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_right.trans hHM2))

theorem exists_conj_of_mem_sec52G2_F4
    (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4) (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {b x : G} (hb : b ∈ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H)
    (hx : x ∈ M ⊓ centralizerModO2 L) (hb3 : orderOf b = 3) (hx3 : orderOf x = 3) :
    ∃ c : G, c * b * c⁻¹ = x := by
  have hbM2 := sec52G2_le_of_setting_F4 h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hb
  have hbi := exists_involution_commute_of_mem_M2_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hbM2 hb3
  obtain ⟨-, hLin, -, -, -⟩ := setting_L_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hxi := exists_involution_commute_of_mem_centralizerModO2 hLin hx3 (Subgroup.mem_inf.mp hx).2
  exact stmt5_2_14_one_of_F4 hQ h5211 h526 h1284 hSz hU4 hsp hyp hM23 hS hb3 hx3 hbi hxi

theorem m23Fusion3_of_F4
    (hset : Stmt5_2_10_setting_F4) (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4) (h526 : Stmt5_2_6_F4)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) : M23Fusion3_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp hM23 b x hb hx hb3 hx3
  obtain ⟨M2, π, hS⟩ := hset G T M L V H B D L₂ n hyp hM23
  exact exists_conj_of_mem_sec52G2_F4 hQ h5211 h526 h1284 hSz hU4 hsp hyp hM23 hS hb hx hb3 hx3

end CFSG.Quasithin.H13
