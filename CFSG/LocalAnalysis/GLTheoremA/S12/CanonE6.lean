module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem dvd_two_cases {a : ℕ} (h : a ∣ 2) : a = 1 ∨ a = 2 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases a <;> simp_all

theorem split_five_n {lab : GLALabel} (hs : GLASplit 5 lab) (hdvd : lab.n ∣ 2) : lab.n = 2 := by
  rcases dvd_two_cases hdvd with h1 | h2
  · exfalso
    rcases hs with ⟨_, hd⟩ | ⟨_, _, hd⟩ | ⟨_, hd⟩ | ⟨_, hp3⟩
    all_goals first | (rw [h1] at hd; norm_num at hd) | omega
  · exact h2

theorem tag_of_split_five {lab : GLALabel} (hΛ : GLAInLambda2 lab) (hn : lab.n = 2)
    (hs : GLASplit 5 lab) : lab.tag = .twA ∨ lab.tag = .twD ∨ lab.tag = .twE6 := by
  obtain ⟨tag, rank, n⟩ := lab
  simp only at hn
  subst hn
  cases tag <;> simp [GLASplit, CFSG.Assembly.LargeEvenSplit, CFSG.Assembly.LargeEvenUntwisted,
    GLAInLambda2, CFSG.Assembly.LargeEvenInLambda2] at hs hΛ ⊢

section Glue

variable {G : Type} [Group G] [Finite G]

theorem canon_e6four_rank (F : E6FourFacts) {B : Subgroup G} {x y : G} {L D K J : Subgroup G}
    (h : CanonCfg G 5 B x L D K y J) {lab : GLALabel} (hlab : LabelOf J lab) (htag : lab.tag = .E6)
    (hn : lab.n = 2) (hZ : Subgroup.center ↥J = ⊥) : GLATwoLocalRank 5 G = 5 := by
  have hp : (5 : ℕ).Prime := by norm_num
  have hcard : Nat.card B = 5 ^ GLATwoLocalRank 5 G := h.card_B
  have hle : GLATwoLocalRank 5 G ≤ 5 := by
    have h1 := F.aut G J B lab hlab htag hn hZ h.BNJ h.elem
    rw [h.card_inf_centralizer_J hp, hcard] at h1
    have h2 : 5 ^ GLATwoLocalRank 5 G ≤ 5 ^ 5 := by
      calc 5 ^ GLATwoLocalRank 5 G ≤ 5 ^ 4 * 5 := h1
        _ = 5 ^ 5 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hge : 5 ≤ GLATwoLocalRank 5 G := by
    obtain ⟨E, U, hEJ, hUJ, hU, hU2, hEU, hE, hcardE⟩ := F.loc G J lab hlab htag hn hZ
    have h1 := card_mul_le_of_normalizes hp h.y_ne_one h.y_pow h.J_le_cy hEJ hU hU2 hUJ hE hEU
    rw [inf_centralizer_eq_bot_of_center hEJ hZ, Subgroup.card_bot, mul_one] at h1
    have h2 : 5 ^ 5 ≤ 5 ^ GLATwoLocalRank 5 G := by
      calc 5 ^ 5 = 5 ^ 4 * 5 := by norm_num
        _ ≤ Nat.card E * 5 := Nat.mul_le_mul_right 5 hcardE
        _ ≤ 5 ^ GLATwoLocalRank 5 G := h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  exact le_antisymm hle hge

theorem canon_e6four_of_facts (F : E6FourFacts) (B : Subgroup G) (x : G) (L D K : Subgroup G) (y : G)
    (J : Subgroup G) (hS : IsSStarMax 5 B x L) (hsplit : SplitInnerDiagMarking 5 B L)
    (hstd : GLAStdSub 5 B x L D K) (hshat : GLASHat 5 B y J) (hnb : GLANeighbor 5 x y J D K)
    (hKJ : K ≤ J) (hBN : B ≤ Subgroup.normalizer (J : Set G)) (hrank : 4 ≤ GLATwoLocalRank 5 G)
    (lab : GLALabel) (hlab : LabelOf J lab) (htag : lab.tag = .E6) (hn : lab.n = 2)
    (hZ : Subgroup.center ↥J = ⊥) : False := by
  have hp : (5 : ℕ).Prime := by norm_num
  have h : CanonCfg G 5 B x L D K y J := ⟨hS, hsplit, hstd, hshat, hnb, hKJ, hBN, hrank⟩
  have hm5 := canon_e6four_rank F h hlab htag hn hZ
  have hcard : Nat.card B = 5 ^ 5 := by rw [h.card_B, hm5]
  have hcardK : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G)) = 5 ^ 2 := by
    rw [← h.D_eq]
    exact h.card_D
  have hlab2 : 5 ^ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card B := by
    rw [hcardK, hcard]
    norm_num
  have hKlab := F.cent G J K B x lab hlab htag hn hZ hBN h.elem h.xB (h.x_notMem_centralizer_J hp)
    h.isComponent_K_J h.B_le_normalizer_K hlab2
  obtain ⟨labL, hΛ, hsp, -, hmark⟩ := split_label hsplit
  have hyL := h.y_notMem_centralizer_L hp
  have hLy : IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
    have := h.K_comp
    rwa [h.L_inf_centralizer_D] at this
  have hMy := hmark y h.yB
  have hdiv : labL.n ∣ 2 := by
    rcases hKlab with hk | hk
    · exact F.field G L K y labL ⟨.twD, 4, 2⟩ 5 hp (by norm_num) h.y_pow (h.BNL h.yB) hyL hMy hLy hk
        (fun _ => by norm_num)
    · exact F.field G L K y labL ⟨.A, 5, 2⟩ 5 hp (by norm_num) h.y_pow (h.BNL h.yB) hyL hMy hLy hk
        (fun h' => absurd h' (by decide))
  have hLn : labL.n = 2 := split_five_n hsp hdiv
  have hlabL : LabelOf L labL := labelOf_of_markedInnDiag hMy
  rcases tag_of_split_five hΛ hLn hsp with ht | ht | ht
  ·
    have := F.uni G L K y labL (h.BNL h.yB) h.y_pow hyL ht hLn hMy hLy
    rcases hKlab with hk | hk
    · exact this.1 hk
    · exact this.2 hk
  ·
    have hom := F.omega G L K y labL (h.BNL h.yB) h.y_pow hyL ht hLn hMy hLy
    rcases hKlab with hk | hk
    · obtain ⟨E, U, hEL, hUL, hU, hU2, hEU, hE, hcardE⟩ := F.omegaRank G L labL hlabL ht hLn (hom.1 hk)
      have h1 := card_mul_le_of_normalizes hp h.x_ne_one h.x_pow h.L_le_cx hEL hU hU2 hUL hE hEU
      rw [hm5] at h1
      have hpos : 0 < Nat.card E := Nat.card_pos
      norm_num at h1 hcardE
      omega
    · exact hom.2 hk
  ·
    obtain ⟨E, U, hEL, hUL, hU, hU2, hEU, hE, hcardE⟩ := F.twE6 G L labL hlabL ht hLn
    have h1 := card_mul_le_of_normalizes hp h.x_ne_one h.x_pow h.L_le_cx hEL hU hU2 hUL hE hEU
    rw [hm5] at h1
    have hpos : 0 < Nat.card E := Nat.card_pos
    norm_num at h1 hcardE
    omega

end Glue

end CFSG.LocalAnalysis.GLTheoremA
