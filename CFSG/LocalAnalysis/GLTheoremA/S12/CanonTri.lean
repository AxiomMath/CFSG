module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriAux
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Glue

variable {G : Type} [Group G] [Finite G]

theorem canon_tri_rank (F : TriFacts) {B : Subgroup G} {x y : G} {L D K J : Subgroup G}
    (h : CanonCfg G 3 B x L D K y J) {lab : GLALabel} (hlab : LabelOf J lab) (htag : lab.tag = .triD4)
    (hZ : Subgroup.center ↥J = ⊥) : GLATwoLocalRank 3 G = 4 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have h1 := (F.rank G J B lab hlab htag hZ h.BNJ h.elem).1
  rw [h.card_inf_centralizer_J hp, h.card_B] at h1
  have h2 : 3 ^ GLATwoLocalRank 3 G ≤ 3 ^ 4 := by
    calc 3 ^ GLATwoLocalRank 3 G ≤ 3 ^ 3 * 3 := h1
      _ = 3 ^ 4 := by norm_num
  have h3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have h4 := h.rank
  omega

theorem canon_tri_u3Setup {B : Subgroup G} {x y : G} {L D K J : Subgroup G}
    (h : CanonCfg G 3 B x L D K y J) (hm : GLATwoLocalRank 3 G = 4) {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hKlab : LabelOf K ⟨.twA, 2, n⟩) : U3Setup G L K B y n := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hcard : Nat.card B = 3 ^ 4 := by rw [h.card_B, hm]
  refine ⟨hn, hn3, h.split, h.elem, h.yB, h.y_notMem_centralizer_L hp, ?_, ?_, ?_, hKlab,
    h.B_le_normalizer_K, ?_, ?_⟩
  · rw [hcard, h.card_inf_centralizer_L hp]; norm_num
  · have := h.K_eq
    rwa [h.L_inf_centralizer_D] at this
  · have := h.K_comp
    rwa [h.L_inf_centralizer_D] at this
  · rw [← h.D_eq, h.card_D, hcard]; norm_num
  · intro E U hEL hUL hU hU2 hEU hE
    have h1 := card_mul_le_of_normalizes hp h.x_ne_one h.x_pow h.L_le_cx hEL hU hU2 hUL hE hEU
    rw [hm] at h1
    have h2 : Nat.card E * 3 ≤ (3 ^ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G))) * 3 :=
      calc Nat.card E * 3 ≤ 3 ^ 4 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) := h1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)

theorem canon_tri_inner_twA (F : TriFacts) {B : Subgroup G} {x y : G} {L D K J : Subgroup G}
    (h : CanonCfg G 3 B x L D K y J) {lab : GLALabel} (hlab : LabelOf J lab) (htag : lab.tag = .triD4)
    (hodd : Odd lab.n) (h3 : 3 ≤ lab.n) (hZ : Subgroup.center ↥J = ⊥)
    (hKlab : LabelOf K ⟨.twA, 2, lab.n⟩) (hxin : InnerOn J x) : False := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hm := canon_tri_rank F h hlab htag hZ
  have hcard : Nat.card B = 3 ^ 4 := by rw [h.card_B, hm]
  have hSetup := canon_tri_u3Setup h hm hodd h3 hKlab
  obtain ⟨a, haJ, haact⟩ := hxin
  have hx1 : x ∉ Subgroup.centralizer (J : Set G) := h.x_notMem_centralizer_J hp
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hx1
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have := haact j hj
    simp only [inv_one, mul_one, one_mul] at this
    calc j * x = x * j * x⁻¹ * x := by rw [this]
      _ = x * j := by group
  have ha3 : a ^ 3 = 1 := pow_eq_one_of_act hZ haJ haact h.x_pow
  have hKa : IsComponentOf K (J ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have := h.isComponent_K_J
    rwa [inf_centralizer_eq_of_act haact] at this
  obtain ⟨A, hA⟩ : ∃ A : Subgroup G, A = innerPart J B := ⟨_, rfl⟩
  have hmem : ∀ b, b ∈ A ↔ b ∈ B ∧ InnerOn J b := fun b => by rw [hA]; exact mem_innerPart
  have hAB : A ≤ B := fun b hb => ((hmem b).1 hb).1
  have hxA : x ∈ A := (hmem x).2 ⟨h.xB, a, haJ, haact⟩
  have hyA : y ∈ A := (hmem y).2 ⟨h.yB, innerOn_of_mem_centralizer
    (Subgroup.mem_centralizer_iff.mpr fun j hj => Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cy hj))⟩
  have hDA : B ⊓ Subgroup.centralizer (K : Set G) ≤ A := by
    rw [← h.D_eq, h.D_closure, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hxA
    · exact hyA
  have hAcard : Nat.card A ≤ 27 := by
    have h1 := (F.rank G J A lab hlab htag hZ (hAB.trans h.BNJ)
      (CFSG.Open.IsElemAbelian.mono h.elem hAB)).2 (fun b hb => ((hmem b).1 hb).2)
    have h2 : Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 := by
      have := Subgroup.card_le_of_le (inf_le_inf_right (Subgroup.centralizer (J : Set G)) hAB)
      rwa [h.card_inf_centralizer_J hp] at this
    calc Nat.card A ≤ 3 ^ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) := h1
      _ ≤ 3 ^ 2 * 3 := Nat.mul_le_mul_left _ h2
      _ = 27 := by norm_num
  have hBA : ¬ B ≤ A := fun hle => by
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨g₁, hg₁B, hg₁A⟩ := SetLike.not_le_iff_exists.mp hBA
  have hg₁D : g₁ ∉ B ⊓ Subgroup.centralizer (K : Set G) := fun hg => hg₁A (hDA hg)
  have hg : ∃ g ∈ B, g ∉ A ∧ ¬ IsSolvable ↥(K ⊓ Subgroup.centralizer ({g} : Set G)) := by
    by_cases hs : IsSolvable ↥(K ⊓ Subgroup.centralizer ({g₁} : Set G))
    · set D' := B ⊓ Subgroup.centralizer (K : Set G) with hD'
      have hD'card : Nat.card D' = 9 := by rw [hD', ← h.D_eq, h.card_D]; norm_num
      have hD'B : D' ≤ B := inf_le_left
      have hg₁1 : g₁ ≠ 1 := fun h1 => hg₁A (h1 ▸ A.one_mem)
      have hg₁p : g₁ ^ 3 = 1 := h.elem.2 g₁ hg₁B
      have hzp : Nat.card (Subgroup.zpowers g₁) = 3 := by
        haveI : Fact (Nat.Prime 3) := ⟨hp⟩
        rw [Nat.card_zpowers, orderOf_eq_prime hg₁p hg₁1]
      have hnorm : Subgroup.zpowers g₁ ≤ Subgroup.normalizer (D' : Set G) := by
        rw [Subgroup.zpowers_le]
        apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact CFSG.Open.IsElemAbelian.comm h.elem (hD'B hd) hg₁B
      have hM := card_sup_mul_card_inf_of_le_normalizer hnorm
      rw [hD'card, hzp] at hM
      have hMle : Nat.card ↥(D' ⊔ Subgroup.zpowers g₁) ≤ 27 := by
        have : 0 < Nat.card ↥(D' ⊓ Subgroup.zpowers g₁) := Nat.card_pos
        nlinarith
      have hBM : ¬ B ≤ D' ⊔ Subgroup.zpowers g₁ := fun hle => by
        have := Subgroup.card_le_of_le hle
        omega
      obtain ⟨g₂, hg₂B, hg₂A, hg₂M⟩ := exists_mem_not_mem_of_not_le hBA hBM
      refine ⟨g₂, hg₂B, hg₂A, fun hs₂ => ?_⟩
      exact F.u3Torus G L K B y lab.n hSetup g₁ g₂ hg₁B hg₂B hg₁D hg₂M ⟨hs, hs₂⟩
    · exact ⟨g₁, hg₁B, hg₁A, hs⟩
  obtain ⟨g, hgB, hgA, hgns⟩ := hg
  have hgout : ¬ InnerOn J g := fun hin => hgA ((hmem g).2 ⟨hgB, hin⟩)
  have hgcomm : g ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgx : g * x = x * g := CFSG.Open.IsElemAbelian.comm h.elem hgB h.xB
    exact comm_of_act hZ haJ haact (h.BNJ hgB) hgx
  have hJ := F.lemmaJ G J K a g lab hlab htag hodd h3 hZ haJ ha3 ha1 hKa hKlab (h.BNJ hgB)
    (h.elem.2 g hgB) hgout hgcomm
  rcases hJ with hc | hab
  · exact hgA (hDA ⟨hgB, hc⟩)
  · exact hgns (isSolvable_of_comm fun u v => hab.is_comm.comm u v)

theorem canon_tri_of_facts (F : TriFacts) {m : ℕ} (hc : S12Ctx G m 3) (h171 : I171OneAt G)
    (B : Subgroup G) (x : G) (L D K : Subgroup G) (y : G) (J : Subgroup G)
    (hS : IsSStarMax 3 B x L) (hsplit : SplitInnerDiagMarking 3 B L) (hstd : GLAStdSub 3 B x L D K)
    (hshat : GLASHat 3 B y J) (hnb : GLANeighbor 3 x y J D K) (hKJ : K ≤ J)
    (hBN : B ≤ Subgroup.normalizer (J : Set G)) (hrank : 4 ≤ GLATwoLocalRank 3 G)
    (lab : GLALabel) (hlab : LabelOf J lab) (htag : lab.tag = .triD4) (hodd : Odd lab.n)
    (h3 : 3 ≤ lab.n) : False := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have h : CanonCfg G 3 B x L D K y J := ⟨hS, hsplit, hstd, hshat, hnb, hKJ, hBN, hrank⟩
  have hZ := F.schur G J lab hlab htag
  have hm := canon_tri_rank F h hlab htag hZ
  have hcard : Nat.card B = 3 ^ 4 := by rw [h.card_B, hm]
  have hxJ := h.x_notMem_centralizer_J hp
  rcases F.cent G J K x lab hlab htag hodd h3 hZ (h.BNJ h.xB) h.x_pow hxJ h.isComponent_K_J with
    ⟨hout, hK | ⟨hKtw, hKZ⟩⟩ | ⟨hin, hK | hKtw⟩
  ·
    obtain ⟨labL, hΛ, hsp, -, hmark⟩ := split_label hsplit
    have hKy : IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
      have := h.K_comp
      rwa [h.L_inf_centralizer_D] at this
    exact F.noG2 G L K y labL 3 hp (by norm_num) h.y_pow (h.BNL h.yB) (h.y_notMem_centralizer_L hp)
      (hmark y h.yB) hKy lab.n hK
  ·
    have hSetup := canon_tri_u3Setup h hm hodd h3 hKtw
    have h1 := F.u3L G L K B y lab.n hSetup
    rw [hKZ, Subgroup.card_bot] at h1
    exact absurd h1 (by norm_num)
  ·
    have hq : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_of_marking hsplit
    have hIM : InnerDiagMarking B L :=
      CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨_, h2, h3⟩ => ⟨h2, h3⟩) hsplit
    have hchev : IsChevSimple 2 (PSimple 3 L) := hc.ctx.stage8.1 B x L hS
    have hKg : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
      kGroup_centralizer hc.toS6 h.x_ne_one
    have hInn := h171 3 B x L D K hp (by norm_num) hS (by rw [hcard]) hq hchev hKg hIM h.pre
    have hl := F.l2 G K B (3 * lab.n) hK h.elem hInn
    have h9 : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G)) = 3 ^ 2 := by
      rw [← h.D_eq]
      exact h.card_D
    rw [h9, hcard] at hl
    norm_num at hl
  · exact canon_tri_inner_twA F h hlab htag hodd h3 hZ hKtw hin

end Glue

end CFSG.LocalAnalysis.GLTheoremA
