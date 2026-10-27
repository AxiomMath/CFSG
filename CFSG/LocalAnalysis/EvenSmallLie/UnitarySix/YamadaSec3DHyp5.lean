module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp2

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

@[expose] def j0W : List ℕ := [15, 1, 15, 0, 1, 15, 1]

theorem d_j₀_eq : (sec3DData e t).j₀ = gw e j0W := rfl

theorem d_j₀_pow : (sec3DData e t).j₀ ^ 3 = 1 := by
  rw [d_j₀_eq, pow_succ, pow_two, ← gw_append, ← gw_append,
    gw_eq_xId (b := []) (by decide) (by decide) (by decide), gw_nil]

theorem d_j₀_u₁ : (sec3DData e t).j₀ * (sec3DData e t).u₁ * (sec3DData e t).j₀⁻¹ =
    (sec3DData e t).u₂ := by
  show gw e j0W * gw e [0] * (gw e j0W)⁻¹ = gw e [1]
  rw [← gw_cjW (by decide)]
  exact gw_eq_xId (by decide) (by decide) (by decide)

theorem d_j₀_u₂ : (sec3DData e t).j₀ * (sec3DData e t).u₂ * (sec3DData e t).j₀⁻¹ =
    (sec3DData e t).u₁ * (sec3DData e t).u₂ := by
  show gw e j0W * gw e [1] * (gw e j0W)⁻¹ = gw e [0] * gw e [1]
  rw [← gw_cjW (by decide), ← gw_append]
  exact gw_eq_xId (by decide) (by decide) (by decide)

theorem d_j₀_norm_A₃ : (sec3DData e t).j₀ ∈ normalizer ((sec3DData e t).A₃ : Set G) :=
  gw_mem_normalizer_toG gensOK_chA3 (by decide) xNorm_spec.2.2.2.2

theorem d_j₀_comm_z : (sec3DData e t).j₀ * (sec3DData e t).z = (sec3DData e t).z * (sec3DData e t).j₀ := by
  show gw e j0W * gw e [14] = gw e [14] * gw e j0W
  rw [← gw_append, ← gw_append]
  exact gw_eq_xId (by decide) (by decide) (by decide)

theorem mem_zpowers_of_pow_three {g x : G} (hg : g ^ 3 = 1) (hx : x ∈ zpowers g) :
    x = 1 ∨ x = g ∨ x = g * g := by
  obtain ⟨n, rfl⟩ := hx
  show g ^ n = 1 ∨ g ^ n = g ∨ g ^ n = g * g
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
  · rw [orderOf_eq_one_iff.1 h]
    simp
  · rw [← zpow_mod_orderOf, h]
    have : n % ((3 : ℕ) : ℤ) = 0 ∨ n % ((3 : ℕ) : ℤ) = 1 ∨ n % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases this with h0 | h1 | h2
    · left; rw [h0, zpow_zero]
    · right; left; rw [h1, zpow_one]
    · right; right; rw [h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]

theorem mem_centralizer_zpowers {g x : G} (h : x * g = g * x) :
    x ∈ centralizer (zpowers g : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := hy
  exact ((Commute.zpow_left h.symm n).eq)

theorem d_comm_A₄_J : ⁅(sec3DData e t).A₄, (sec3DData e t).J⁆ = (sec3DData e t).X₈ := by
  apply le_antisymm
  · rw [commutator_le]
    intro a ha j hj
    obtain ⟨a', ha', rfl⟩ := mem_toG.1 ha
    have hj0 : (sec3DData e t).j₀ = iotaG e (tw j0W (by decide)) := gw_eq j0W (by decide)
    rcases mem_zpowers_of_pow_three d_j₀_pow hj with h | h | h
    · rw [h, commutatorElement_one_right]
      exact one_mem _
    · rw [h, hj0]
      exact iotaG_comm_mem (a4_spec _ ha').2.2.1
    · rw [h, hj0, ← map_mul]
      exact iotaG_comm_mem (a4_spec _ ha').2.2.2.1
  · refine toG_le_of_prodCheck gensOK_chX8 xWit_spec.2.2.2.1 (by decide) (by decide)
      fun p hp b hb => ?_
    have hl : ∀ p ∈ a4jData, ∀ b ∈ p.2, (∀ k ∈ b.1, k < 18 ∧ [k] ∈ chA4.gens) ∧ b.2 = j0W := by
      decide
    obtain ⟨h1, h2⟩ := hl p hp b hb
    rw [gw_cwW (fun k hk => (h1 k hk).1) (by rw [h2]; decide), h2]
    exact commutator_mem_commutator (gw_mem_ch h1) (mem_zpowers _)

theorem d_A₄_le_cent_J_sup : (sec3DData e t).A₄ ≤
    ((sec3DData e t).A₄ ⊓ centralizer ((sec3DData e t).J : Set G)) ⊔ (sec3DData e t).X₈ := by
  refine toG_le_of_gens gensOK_chA4 fun w hw => ?_
  have hw' : w = [11] ∨ w = [14] ∨ ∀ k ∈ w, k < 18 ∧ [k] ∈ chX8.gens := by
    revert w
    decide
  rcases hw' with rfl | rfl | h
  · refine mem_sup_left ⟨gw_mem_ch (by decide), mem_centralizer_zpowers ?_⟩
    show gw e [11] * gw e j0W = gw e j0W * gw e [11]
    rw [← gw_append, ← gw_append]
    exact (gw_eq_xId (a := j0W ++ [11]) (by decide) (by decide) (by decide)).symm
  · refine mem_sup_left ⟨gw_mem_ch (by decide), mem_centralizer_zpowers ?_⟩
    exact (d_j₀_comm_z (e := e) (t := t)).symm
  · exact mem_sup_right (gw_mem_ch h)

theorem d_card_X₈ : Nat.card (sec3DData e t).X₈ = 4 := by
  rw [show (sec3DData e t).X₈ = toG e chX8.grp from rfl, card_toG_ch gensOK_chX8, card_chX8]

theorem chX8_inf_chZ : chX8.grp ⊓ chZ.grp = ⊥ := by
  have hsup : chZ2S.grp = chX8.grp ⊔ chZ.grp := grp_append (by decide)
  have hdvd : Nat.card (chX8.grp ⊓ chZ.grp : Subgroup _) ∣ 2 := by
    rw [← card_chZ]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : chX8.grp ⊓ chZ.grp = chZ.grp :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, card_chZ])
    have hle : chZ.grp ≤ chX8.grp := heq ▸ inf_le_left
    have h8 := card_chZ2S
    rw [hsup, sup_eq_left.2 hle, card_chX8] at h8
    exact absurd h8 (by decide)

theorem d_X₈_inf_z : (sec3DData e t).X₈ ⊓ zpowers (sec3DData e t).z = ⊥ := by
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm,
    show (sec3DData e t).X₈ = toG e chX8.grp from rfl, ← toG_inf, chX8_inf_chZ, toG_bot]

theorem d_X₈_le_A₁ : (sec3DData e t).X₈ ≤ (sec3DData e t).A₁ := toG_ch_le (by decide)

theorem d_Z₂S_eq : (sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z = toG e chZ2S.grp := by
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm,
    show (sec3DData e t).X₈ = toG e chX8.grp from rfl,
    ← toG_sup (grp_le_T46 gensOK_chX8) (grp_le_T46 gensOK_chZ), ← grp_append (c := chZ2S) (by decide)]

theorem d_comm_X₁_Z₂ : ∀ x ∈ (sec3DData e t).X₁, ∀ b ∈ (sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z,
    x * b * x⁻¹ * b⁻¹ ∈ zpowers (sec3DData e t).z := by
  intro x hx b hb
  rw [d_Z₂S_eq] at hb
  obtain ⟨x', hx', rfl⟩ := mem_toG.1 hx
  obtain ⟨b', hb', rfl⟩ := mem_toG.1 hb
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm, ← commutatorElement_def]
  exact iotaG_comm_mem ((z2s_spec _ hb').1 _ hx')

theorem d_A₄_comm_X₁ : ∀ x ∈ (sec3DData e t).X₁, x ≠ 1 → ∀ a ∈ (sec3DData e t).A₄,
    x * a * x⁻¹ * a⁻¹ ∈ zpowers (sec3DData e t).z →
      a ∈ (sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z := by
  intro x hx hx1 a ha hxa
  rw [d_Z₂S_eq]
  obtain ⟨x', hx', rfl⟩ := mem_toG.1 hx
  obtain ⟨a', ha', rfl⟩ := mem_toG.1 ha
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm, ← commutatorElement_def,
    iotaG_comm, iotaG_mem_toG] at hxa
  refine iotaG_mem_toG.2 ((a4_spec _ ha').2.2.2.2 _ hx' (fun h => hx1 ?_)
    (by simpa [commutatorElement_def] using hxa))
  rw [show x' = 1 from Subtype.ext h, map_one]

theorem d_x₃_mem_K₁ : (sec3DData e t).x₃ ∈ (sec3DData e t).K₁ := gw_mem_ch (by decide)

theorem d_x₃_mem_Sig : (sec3DData e t).x₃ ∈ (sec3DData e t).Sig := gw_mem_ch (by decide)

theorem d_A₂_le_x₃ : (sec3DData e t).A₂ ≤ zpowers (sec3DData e t).x₃ ⊔ (sec3DData e t).A₃ := by
  refine toG_le_of_gens gensOK_chA2 fun w hw => ?_
  have hw' : w = [4] ∨ ∀ k ∈ w, k < 18 ∧ [k] ∈ chA3.gens := by
    revert w
    decide
  rcases hw' with rfl | h
  · exact mem_sup_left (mem_zpowers _)
  · exact mem_sup_right (gw_mem_ch h)

theorem d_A₄_le_orbit_z : (sec3DData e t).A₄ ≤
    closure ((fun l => l * (sec3DData e t).z * l⁻¹) '' ((sec3DData e t).Λ : Set G)) := by
  refine toG_le_of_prodCheck gensOK_chA4 xWit_spec.2.2.1 (by decide) (by decide) fun p hp b hb => ?_
  have hl : ∀ p ∈ a4zData, ∀ b ∈ p.2, (∀ k ∈ b.1, k < 18 ∧ [k] ∈ chLam.gens) ∧ b.2 = [14] := by
    decide
  obtain ⟨h1, h2⟩ := hl p hp b hb
  rw [gw_cjW (fun k hk => (h1 k hk).1), h2]
  exact subset_closure ⟨gw e b.1, gw_mem_ch h1, rfl⟩

theorem d_A₃_le_comm_e : (sec3DData e t).A₃ ≤
    ⁅(sec3DData e t).A₃, zpowers (sec3DData e t).e⁆ ⊔ (sec3DData e t).A₄ := by
  refine toG_le_of_gens gensOK_chA3 fun w hw => ?_
  have hw' : (∀ k ∈ w, k < 18 ∧ [k] ∈ chA4.gens) ∨ ∃ p ∈ a3eData, w = [p.1] := by
    revert w
    decide
  rcases hw' with h | ⟨p, hp, rfl⟩
  · exact mem_sup_right (gw_mem_ch h)
  · have hl : ∀ p ∈ a3eData, p.1 < 18 ∧ (∀ k ∈ p.2.1, k < 18 ∧ [k] ∈ chA3.gens) ∧
        ∀ k ∈ p.2.2, k < 18 ∧ [k] ∈ chA4.gens := by decide
    obtain ⟨h0, h1, h2⟩ := hl p hp
    have hlt : ∀ k ∈ cwW p.2.1 [4, 17] ++ p.2.2, k < 18 := by
      intro k hk
      simp only [cwW, List.mem_append, List.mem_reverse] at hk
      rcases hk with (((h | h) | h) | h) | h
      · exact (h1 k h).1
      · revert k; decide
      · exact (h1 k h).1
      · revert k; decide
      · exact (h2 k h).1
    have heq : wP [p.1] = wP (cwW p.2.1 [4, 17] ++ p.2.2) :=
      eq_of_eqA (rep_wA tabs_check _ (by simpa using h0)) (rep_wA tabs_check _ hlt)
        (xWit_spec.2.2.2.2.2.2.2.2 p hp)
    rw [gw_eq_gw (by simpa using h0) hlt heq, gw_append, gw_cwW (fun k hk => (h1 k hk).1)
      (by decide)]
    exact mul_mem (mem_sup_left (commutator_mem_commutator (gw_mem_ch h1) (mem_zpowers _)))
      (mem_sup_right (gw_mem_ch h2))

theorem normalizer_le_normalizer_inf_centralizer (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer ((B ⊓ centralizer (B : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have key : ∀ m ∈ normalizer (B : Set G), ∀ h ∈ B ⊓ centralizer (B : Set G),
      m * h * m⁻¹ ∈ B ⊓ centralizer (B : Set G) := by
    intro m hm h hh
    refine ⟨(mem_normalizer_iff.1 hm h).1 hh.1, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : m⁻¹ * y * m⁻¹⁻¹ ∈ B := (mem_normalizer_iff.1 (inv_mem hm) y).1 hy
    have hc := mem_centralizer_iff.1 hh.2 _ hy'
    simp only [inv_inv] at hc
    calc y * (m * h * m⁻¹) = m * ((m⁻¹ * y * m) * h) * m⁻¹ := by group
      _ = m * (h * (m⁻¹ * y * m)) * m⁻¹ := by rw [hc]
      _ = m * h * m⁻¹ * y := by group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key n hn h, fun hh => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hh
  simpa [mul_assoc] using this

theorem d_A₄_eq : (sec3DData e t).A₄ =
    (sec3DData e t).A₃ ⊓ centralizer ((sec3DData e t).A₃ : Set G) := by
  refine le_antisymm (le_inf d_A₄_le_A₃ ?_) d_center_A₃
  rw [le_centralizer_iff]
  exact d_A₃_le_cent_A₄

theorem d_NLA₃_le : (sec3DData e t).NLA₃ ≤ normalizer ((sec3DData e t).A₄ : Set G) := by
  intro n hn
  rw [d_A₄_eq]
  exact normalizer_le_normalizer_inf_centralizer _ hn.2

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
