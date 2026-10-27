module

public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Classes
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43 Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C

@[expose] def memOrd : List ℕ := [5, 120, 120, 720, 1920]

structure GFacts (M : ℕ → Subgroup G) (nc : ℕ → ℕ) (x : ℕ → ℕ → G) : Prop where
  card : Nat.card G = 51840
  card_member : ∀ i < 5, Nat.card (M i) = memOrd.getD i 0
  member_five : M 5 = ⊤
  exists_rep : ∀ i < 5, ∀ y : G, (∃ k, orderOf y = 3 ^ k) → y ≠ 1 →
    y ∈ M i ∨ ∃ r < nc i, ∃ n ∈ normalizer (M i : Set G), y = n * x i r * n⁻¹
  case_spec : ∀ i < 5, ∀ r < nc i, ∃ j < 6, ∃ g : G,
    M i ⊔ zpowers (x i r) = (M j).map (MulAut.conj g).toMonoidHom
  three : ∃ z ∈ M 3, z ∈ center G ∧ z ≠ 1 ∧ z ^ 2 = 1
  four : ∃ a ∈ M 4, a ^ 3 = 1 ∧ a ≠ 1 ∧ ∃ U : Subgroup G, U ≤ M 4 ∧ Nat.card U = 48 ∧
    ∀ u ∈ U, u * a * u⁻¹ ∈ zpowers a
  normD : ∃ D : Sylow 5 G, 40 ≤ Nat.card (normalizer (D : Set G))
  normP : ∃ P : Sylow 3 G, 324 ≤ Nat.card (normalizer (P : Set G))
  inf_le : ∀ (D : Sylow 5 G) (P : Sylow 3 G),
    Nat.card ↥(normalizer (D : Set G) ⊓ normalizer (P : Set G)) ≤ 2

variable {M : ℕ → Subgroup G} {nc : ℕ → ℕ} {x : ℕ → ℕ → G}

@[expose] def familyM (M : ℕ → Subgroup G) : Set (Subgroup G) :=
  {K | ∃ j < 6, ∃ g : G, K = (M j).map (MulAut.conj g).toMonoidHom}

theorem mem_familyM_conj {K : Subgroup G} (hK : K ∈ familyM M) (g : G) :
    K.map (MulAut.conj g).toMonoidHom ∈ familyM M := by
  obtain ⟨j, hj, g', rfl⟩ := hK
  exact ⟨j, hj, g * g', CFSG.Sp43.map_conj_map_conj _ g g'⟩

theorem member_mem_familyM {j : ℕ} (hj : j < 6) : M j ∈ familyM M :=
  ⟨j, hj, 1, (CFSG.Sp43.map_conj_one _).symm⟩

theorem GFacts.join_closed (F : GFacts M nc x) :
    ∀ K ∈ familyM M, ∀ σ : G, (∃ k, orderOf σ = 3 ^ k) → K ⊔ zpowers σ ∈ familyM M := by
  rintro K ⟨j, hj, g, rfl⟩ σ ⟨k, hk⟩
  obtain ⟨y, hσ⟩ : ∃ y, MulAut.conj g y = σ := ⟨_, CFSG.Sp43.conj_conj_inv_apply g σ⟩
  have hyk : orderOf y = 3 ^ k := by rw [← hk, ← hσ, MulEquiv.orderOf_eq]
  have hsup : (M j).map (MulAut.conj g).toMonoidHom ⊔ zpowers σ =
      (M j ⊔ zpowers y).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hσ]
  rw [hsup]
  refine mem_familyM_conj ?_ g
  by_cases hj5 : j = 5
  · subst hj5
    rw [F.member_five, top_sup_eq, ← F.member_five]
    exact member_mem_familyM (by norm_num)
  have hj5' : j < 5 := by omega
  by_cases hy1 : y = 1
  · rw [hy1, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    exact member_mem_familyM hj
  rcases F.exists_rep j hj5' y ⟨k, hyk⟩ hy1 with hmem | ⟨r, hr, n, hn, e⟩
  · rw [sup_eq_left.2 ((Subgroup.zpowers_le).2 hmem)]
    exact member_mem_familyM hj
  · obtain ⟨j', hj', g', hcase⟩ := F.case_spec j hj5' r hr
    have : M j ⊔ zpowers y = (M j ⊔ zpowers (x j r)).map (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.map_sup, CFSG.Sp43.map_conj_eq_of_mem_normalizer hn, MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← e]
    rw [this, hcase]
    exact mem_familyM_conj (mem_familyM_conj (member_mem_familyM hj') _) n

theorem GFacts.genProp_small (F : GFacts M nc x) {i : ℕ} (hi : i < 3) : GenProp (M i) := by
  have hc := F.card_member i (by omega)
  have h : Nat.card (M i) = 5 ∨ Nat.card (M i) = 120 := by
    interval_cases i
    · exact Or.inl hc
    · exact Or.inr hc
    · exact Or.inr hc
  apply genProp_of_index_ne
  · rcases h with h | h <;> rw [h] <;> norm_num
  · intro D P
    apply index_ne_of_not_dvd_card
    rcases h with h | h <;> rw [h] <;> norm_num

theorem GFacts.genProp_three (F : GFacts M nc x) : GenProp (M 3) := by
  have hc : Nat.card (M 3) = 720 := F.card_member 3 (by norm_num)
  obtain ⟨z, hz, hzc, hz1, hz2⟩ := F.three
  apply genProp_of_index_ne (by rw [hc]; norm_num)
  intro D P
  refine index_ne_of_center (z := ⟨z, hz⟩) ?_ ?_ ?_ (by rw [hc]; norm_num) D P
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 hzc) g)
  · intro h
    exact hz1 (congrArg Subtype.val h)
  · exact Subtype.ext (by rw [SubmonoidClass.coe_pow, hz2]; rfl)

theorem GFacts.genProp_four (F : GFacts M nc x) : GenProp (M 4) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card (M 4) = 1920 := F.card_member 4 (by norm_num)
  obtain ⟨a₀, haM, ha3, ha1, U, hle4, h48U, hconj⟩ := F.four
  set X := M 4
  set a : X := ⟨a₀, haM⟩
  have ha3' : a ^ 3 = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact ha3)
  have ha1' : a ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hao : orderOf a = 3 := orderOf_eq_prime ha3' ha1'
  have hcardA : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have hPA : IsPGroup 3 (zpowers a) := IsPGroup.of_card (n := 1) (by rw [hcardA]; norm_num)
  have hidx : (zpowers a).index = 640 := by
    have := Subgroup.card_mul_index (zpowers a)
    rw [hcardA, hc] at this
    omega
  set S : Sylow 3 X := hPA.toSylow (by rw [hidx]; norm_num)
  have hU : U.subgroupOf X ≤ normalizer (zpowers a : Set X) := by
    intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    apply mem_normalizer_of_conj_mem
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [← conj_zpow]
    apply zpow_mem
    obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.1 (hconj _ hu)
    have e : u * a * u⁻¹ = a ^ m' := by
      apply Subtype.ext
      rw [SubgroupClass.coe_zpow, MulMemClass.coe_mul, MulMemClass.coe_mul, InvMemClass.coe_inv]
      exact hm'.symm
    rw [e]
    exact zpow_mem (Subgroup.mem_zpowers a) _
  have h48 : Nat.card (U.subgroupOf X) = 48 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle4).toEquiv]
    exact h48U
  have h1648 : 16 ∣ 48 := by norm_num
  have h16 : 16 ∣ Nat.card (normalizer (zpowers a : Set X)) :=
    h1648.trans (h48 ▸ Subgroup.card_dvd_of_le hU)
  apply genProp_of_index_ne (by rw [hc]; norm_num)
  intro D P
  refine index_ne_of_dvd_normalizer (fun Q => ?_) (by rw [hc]; norm_num) D P
  rw [card_normalizer_sylow_eq Q S]
  exact h16

theorem GFacts.genProp_G (F : GFacts M nc x) : GenProp G := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D₀, hD₀⟩ := F.normD
  obtain ⟨P₀, hP₀⟩ := F.normP
  apply genProp_of_index_ne (by rw [F.card]; norm_num)
  intro D P
  apply index_ne_of_card_inf D P
  have h1 := F.inf_le D P
  have h2 : 40 ≤ Nat.card (normalizer (D : Set G)) := by
    rw [card_normalizer_sylow_eq D D₀]
    exact hD₀
  have h3 : 324 ≤ Nat.card (normalizer (P : Set G)) := by
    rw [card_normalizer_sylow_eq P P₀]
    exact hP₀
  rw [F.card]
  calc 51840 * Nat.card ↥(normalizer (D : Set G) ⊓ normalizer (P : Set G)) ≤ 51840 * 2 :=
        Nat.mul_le_mul_left _ h1
    _ < 16 * (40 * 324) := by norm_num
    _ ≤ 16 * (Nat.card (normalizer (D : Set G)) * Nat.card (normalizer (P : Set G))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3)

theorem GFacts.genProp_member (F : GFacts M nc x) {j : ℕ} (hj : j < 6) : GenProp (M j) := by
  interval_cases j
  · exact F.genProp_small (by norm_num)
  · exact F.genProp_small (by norm_num)
  · exact F.genProp_small (by norm_num)
  · exact F.genProp_three
  · exact F.genProp_four
  · exact genProp_of_mulEquiv
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr F.member_five.symm)) F.genProp_G

theorem GFacts.five_dvd_of_sylow (F : GFacts M nc x) {W : Subgroup G} {q : ℕ}
    [hq : Fact q.Prime] (hq2 : q ≠ 2) (hq3 : q ≠ 3) (D : Sylow q W)
    (hD : (D : Subgroup W) ≠ ⊥) : 5 ∣ Nat.card W := by
  have hqp : q.Prime := hq.out
  have hqD : q ∣ Nat.card (D : Subgroup W) := by
    obtain ⟨n, hn⟩ := D.isPGroup'.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hD
      rw [← Subgroup.card_eq_one]
      simpa using hn
    rw [hn]
    exact dvd_pow_self q hn0
  have hqW : q ∣ Nat.card W := hqD.trans (Subgroup.card_subgroup_dvd_card _)
  have hG : q ∣ 2 ^ 7 * 3 ^ 4 * 5 := by
    have := Subgroup.card_subgroup_dvd_card W
    rw [F.card] at this
    exact hqW.trans this
  rcases (Nat.Prime.dvd_mul hqp).1 hG with h | h
  · rcases (Nat.Prime.dvd_mul hqp).1 h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 (hqp.dvd_of_dvd_pow h)) hq2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).1 (hqp.dvd_of_dvd_pow h))
        hq3
  · rwa [← (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_five).1 h]

theorem GFacts.mem_family (F : GFacts M nc x) {W : Subgroup G} (hW : oPPrimeHull 3 W = W)
    (h5 : 5 ∣ Nat.card W) : W ∈ familyM M := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hyo : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe, hy]
  have hcY : Nat.card (zpowers (y : G)) = 5 := by rw [Nat.card_zpowers, hyo]
  have hpY : IsPGroup 5 (zpowers (y : G)) := IsPGroup.of_card (n := 1) (by rw [hcY]; norm_num)
  have hidxY : ¬ 5 ∣ (zpowers (y : G)).index := by
    have := Subgroup.card_mul_index (zpowers (y : G))
    rw [hcY, F.card] at this
    have h : (zpowers (y : G)).index = 10368 := by omega
    rw [h]
    norm_num
  have hc0 : Nat.card (M 0) = 5 := F.card_member 0 (by norm_num)
  have hp0 : IsPGroup 5 (M 0) := IsPGroup.of_card (n := 1) (by rw [hc0]; norm_num)
  have hidx0 : ¬ 5 ∣ (M 0).index := by
    have := Subgroup.card_mul_index (M 0)
    rw [hc0, F.card] at this
    have h : (M 0).index = 10368 := by omega
    rw [h]
    norm_num
  set D₀ : Sylow 5 G := hp0.toSylow hidx0
  have hD₀ : (D₀ : Subgroup G) = M 0 := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G D₀ (hpY.toSylow hidxY)
  have hK₀ : (M 0).map (MulAut.conj g).toMonoidHom ≤ W := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ (D₀ : Subgroup G) := by rw [hD₀]; exact ha
    have h1 : (MulAut.conj g).toMonoidHom a ∈ ((g • D₀ : Sylow 5 G) : Subgroup G) := by
      rw [mem_smul_sylow_iff]
      have e : g⁻¹ * (MulAut.conj g).toMonoidHom a * g = a := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact ha'
    rw [hg] at h1
    have h2 : (MulAut.conj g).toMonoidHom a ∈ zpowers (y : G) := h1
    exact (Subgroup.zpowers_le.2 y.2) h2
  exact mem_of_join_closed_pElt (familyM M) F.join_closed hW
    (mem_familyM_conj (member_mem_familyM (by norm_num)) g) hK₀

theorem GFacts.genProp (F : GFacts M nc x) {W : Subgroup G} (hW : oPPrimeHull 3 W = W) :
    GenProp W := by
  by_cases h5 : 5 ∣ Nat.card W
  · obtain ⟨j, hj, g, rfl⟩ := F.mem_family hW h5
    exact genProp_map_conj g (F.genProp_member hj)
  · intro q _ hq2 hq3 D P hD
    exact absurd (F.five_dvd_of_sylow hq2 hq3 D hD) h5

end CFSG.KC.Sp43K

end
