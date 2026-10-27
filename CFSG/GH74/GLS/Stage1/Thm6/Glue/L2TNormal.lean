module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2TNormalAut
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Main

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

theorem zpow_cases_of_sq {M : Type*} [Group M] {u : M} (hu : u * u = 1) (k : ℤ) :
    u ^ k = 1 ∨ u ^ k = u := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, zpow_two, hu, one_zpow]
  · right; rw [zpow_add, zpow_mul, zpow_two, hu, one_zpow, one_mul, zpow_one]

theorem x_central (h : SitFacts x Kb e N T) (hx : x * x = 1) (hx1 : x ≠ 1)
    (hQ : Qg x Kb T = Subgroup.zpowers x) : ∀ t ∈ T, t * x = x * t := by
  intro t ht
  have hxQ : x ∈ Qg x Kb T := h.x_mem_Q hx hx1
  have h1 : t * x * t⁻¹ ∈ Qg x Kb T := (Qg_normal x Kb h.T_le_C).2 t ht x hxQ
  rw [hQ] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  rcases zpow_cases_of_sq hx k with h0 | h0
  · exfalso
    apply hx1
    have h2 : t * x * t⁻¹ = 1 := by rw [← hk, h0]
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h2]; group
  · calc t * x = (t * x * t⁻¹) * t := by group
      _ = x * t := by rw [← hk, h0]

theorem card_P_cases (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) :
    Nat.card (Pg x Kb T) = 4 ∨ 8 ≤ Nat.card (Pg x Kb T) := by
  obtain ⟨m, hm, ⟨e₀⟩⟩ := NP_dihedral (e := e) (N := N) h.hF h12c
  have hNZ : NeZero (2 ^ m) := ⟨by positivity⟩
  have hcard : Nat.card (Pg x Kb T) = 2 * 2 ^ m := by
    rw [Nat.card_congr (PgEquiv h).toEquiv, Nat.card_congr e₀.toEquiv, DihedralGroup.nat_card]
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · left
    have : m = 1 := by omega
    subst this
    rw [hcard]; norm_num
  · right
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2
    omega

theorem NR_eq_bot_of_card_four (h : SitFacts x Kb e N T) (h12f : IVK.IVK_1_2f)
    (hc : Nat.card (Pg x Kb T) = 4) : N.R = ⊥ := by
  have hcard : Nat.card ↥N.P = 2 ^ 2 := by
    rw [Nat.card_congr (PgEquiv h).symm.toEquiv, hc]; norm_num
  have := (h12f F h.hF ↥Kb e N).2 2 hcard
  apply Subgroup.eq_bot_of_card_le
  simpa using this

theorem cent_decomp_center (h : SitFacts x Kb e N T) (h14j : IVK.IVK_1_4j) {t : G}
    (htC : t ∈ Cx x) (hcent : ∀ p ∈ Pg x Kb T, t * p = p * t) :
    ∃ z₁ ∈ N.P, (∀ a ∈ N.P, z₁ * a = a * z₁) ∧ ∃ e₁ ∈ IVK.fieldAutSub e, ∃ M : ℕ, Odd M ∧
      orderOf e₁ ∣ 2 * M ∧ z₁ * e₁ = e₁ * z₁ ∧ phig x Kb t = z₁ * e₁ := by
  obtain ⟨E, -, hEF, ⟨M, hModd, hEcard⟩, hcentN, -, -⟩ := h14j F h.hF ↥Kb e N
  have hcN : phig x Kb t ∈ Subgroup.centralizer (N.P : Set (MulAut ↥Kb)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨p, hp, rfl⟩ := (h.hPN a).1 ha
    have hpC : p ∈ Cx x := h.T_le_C hp.1
    rw [← phig_mul x Kb hpC htC, ← phig_mul x Kb htC hpC, hcent p hp]
  rw [hcentN] at hcN
  set Z : Subgroup (MulAut ↥Kb) := (Subgroup.center ↥N.P).map N.P.subtype with hZ
  have hZP : Z ≤ N.P := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hEc : ∀ b ∈ E, ∀ a ∈ N.P, b * a = a * b := by
    intro b hb a ha
    have : b ∈ Subgroup.centralizer (N.P : Set (MulAut ↥Kb)) := by
      rw [hcentN]; exact mem_sup_right hb
    exact ((Subgroup.mem_centralizer_iff.1 this) a ha).symm
  have hcomm : ∀ a ∈ Z, ∀ b ∈ E, a * b = b * a := fun a ha b hb => (hEc b hb a (hZP ha)).symm
  obtain ⟨z₁, hz₁, e₁, he₁, hte⟩ := (mem_sup_iff_of_comm hcomm).1 hcN
  refine ⟨z₁, hZP hz₁, ?_, e₁, hEF he₁, M, hModd, ?_, hcomm z₁ hz₁ e₁ he₁, hte⟩
  · obtain ⟨z₀, hz₀, rfl⟩ := hz₁
    intro a ha
    have := (Subgroup.mem_center_iff.1 hz₀) ⟨a, ha⟩
    exact (congrArg Subtype.val this).symm
  · have h1 := Subgroup.orderOf_dvd_natCard E he₁
    rcases hEcard with hc | hc
    · rw [hc] at h1; exact h1.trans (Dvd.intro_left 2 rfl)
    · rw [hc] at h1; exact h1

omit [Finite G] in
theorem mem_zpowers_x_of_phig (hQ : Qg x Kb T = Subgroup.zpowers x) (hTC : T ≤ Cx x) {g : G}
    (hg : g ∈ T) (h1 : phig x Kb g = 1) : g ∈ Subgroup.zpowers x := by
  rw [← hQ]; exact ⟨hg, hTC hg, h1⟩

omit [Finite G] in
theorem gen_shift {Rd : Subgroup G} (hRd : NormalIn Rd T) {b n₀ s₀ : G} (hs₀T : s₀ ∈ T)
    (hn₀ : n₀ ∈ Rd) (hbs : b = n₀ * s₀) (hb : ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Rd) :
    ∀ t ∈ T, ∃ k : ℤ, (s₀ ^ k)⁻¹ * t ∈ Rd := by
  subst hbs
  have hn₀T : n₀ ∈ T := hRd.1 hn₀
  have hpow : ∀ k : ℤ, ∃ n ∈ Rd, (n₀ * s₀) ^ k = n * s₀ ^ k := by
    intro k
    refine Int.induction_on k ⟨1, one_mem _, by simp⟩ ?_ ?_
    · rintro i ⟨n, hn, hni⟩
      refine ⟨n * (s₀ ^ (i : ℤ) * n₀ * (s₀ ^ (i : ℤ))⁻¹),
        mul_mem hn (hRd.2 _ (T.zpow_mem hs₀T _) n₀ hn₀), ?_⟩
      rw [zpow_add_one (n₀ * s₀), hni, zpow_add_one s₀]
      group
    · rintro i ⟨n, hn, hni⟩
      refine ⟨n * (s₀ ^ (-(i : ℤ) - 1) * n₀⁻¹ * (s₀ ^ (-(i : ℤ) - 1))⁻¹),
        mul_mem hn (hRd.2 _ (T.zpow_mem hs₀T _) n₀⁻¹ (inv_mem hn₀)), ?_⟩
      rw [zpow_sub_one (n₀ * s₀), hni, zpow_sub_one s₀]
      group
  intro t ht
  obtain ⟨k, hk⟩ := hb t ht
  refine ⟨k, ?_⟩
  obtain ⟨n, hn, hnk⟩ := hpow k
  have hbkT : (n₀ * s₀) ^ k ∈ T := T.zpow_mem (T.mul_mem hn₀T hs₀T) k
  have hs : (s₀ ^ k)⁻¹ = ((n₀ * s₀) ^ k)⁻¹ * n := by rw [hnk]; group
  have h1 : (s₀ ^ k)⁻¹ * t =
      (((n₀ * s₀) ^ k)⁻¹ * n * ((n₀ * s₀) ^ k)⁻¹⁻¹) * (((n₀ * s₀) ^ k)⁻¹ * t) := by
    rw [hs]; group
  rw [h1]
  exact mul_mem (hRd.2 _ (T.inv_mem hbkT) n hn) hk

theorem ip_T_normal_split (h : SitFacts x Kb e N T) (hx : x * x = 1) (hx1 : x ≠ 1)
    (hQ : Qg x Kb T = Subgroup.zpowers x) (h12a : IVK.IVK_1_2a_struct) (h12c : IVK.IVK_1_2c)
    (h12d : IVK.IVK_1_2d) (h12f : IVK.IVK_1_2f) (h14j : IVK.IVK_1_4j) {z : G}
    (hz : HZ T (Pg x Kb T) z) {s : G} (hsT : s ∈ T) (hsR : phig x Kb s ∈ N.R) {m : ℕ}
    (hord : orderOf (phig x Kb s) = 2 ^ m) (hsx : s ^ (2 ^ m) = x)
    (hG : ∀ t ∈ T, ∃ k : ℤ, (s ^ k)⁻¹ * t ∈ Rdg x Kb e T) :
    ∃ F' : Subgroup G, F' ≤ T ∧ Subgroup.zpowers x ≤ F' ∧ IsCyclic ↥F' ∧
      F' ⊓ Rdg x Kb e T = Subgroup.zpowers x ∧ Rdg x Kb e T ⊔ F' = T ∧
      (∀ w ∈ F', w ^ 4 = 1 → (∀ p ∈ Pg x Kb T, w * p = p * w) ∧
        ∀ b ∈ Rdg x Kb e T, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z) ∧
      (Nat.card (Pg x Kb T) = 4 → F' = Subgroup.zpowers x) ∧
      (8 ≤ Nat.card (Pg x Kb T) → ∀ t ∈ T, (∀ p ∈ Pg x Kb T, t * p = p * t) →
        ∃ u ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, ∃ w ∈ F', w ^ 4 = 1 ∧ t = u * w) := by
  have hsC : s ∈ Cx x := h.T_le_C hsT
  have hxQ : x ∈ Qg x Kb T := h.x_mem_Q hx hx1
  have hDF := IVK.innDiagSub_inf_fieldAutSub e
  have hD : (IVK.innDiagSub e).Normal := IVK.innDiagSub_normal e
  have hQmem : ∀ g ∈ T, phig x Kb g = 1 → g ∈ Subgroup.zpowers x :=
    fun g hg h1 => mem_zpowers_x_of_phig hQ h.T_le_C hg h1
  have hxF : x ∈ Subgroup.zpowers s :=
    Subgroup.mem_zpowers_iff.2 ⟨((2 ^ m : ℕ) : ℤ), by rw [zpow_natCast]; exact hsx⟩
  have hsord : orderOf s = 2 ^ (m + 1) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime_pow
    · rw [hsx]; exact hx1
    · rw [pow_succ, pow_mul, hsx, pow_two]; exact hx
  have hτs : ∀ j : ℤ, phig x Kb (s ^ j) = (phig x Kb s) ^ j := fun j => phig_zpow hsC j
  have hsRj : ∀ j : ℤ, (phig x Kb s) ^ j ∈ N.R := fun j => zpow_mem hsR j
  have hw2 : ∀ j : ℤ, (s ^ j) ^ 4 = 1 → phig x Kb (s ^ j) * phig x Kb (s ^ j) = 1 := by
    intro j hj
    have h1 : s ^ (j * 4) = 1 := by
      rw [zpow_mul, show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact hj
    have h2 : ((orderOf s : ℕ) : ℤ) ∣ j * 4 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hsord] at h2
    obtain ⟨c, hc⟩ := h2
    have h3 : j * 2 = (2 : ℤ) ^ m * c := by
      push_cast at hc
      have h5 : (2 : ℤ) * (j * 2) = 2 * ((2 : ℤ) ^ m * c) := by
        calc (2 : ℤ) * (j * 2) = j * 4 := by ring
          _ = 2 ^ (m + 1) * c := hc
          _ = 2 * (2 ^ m * c) := by ring
      exact mul_left_cancel₀ (by norm_num) h5
    have h4 : (phig x Kb s) ^ (j * 2) = 1 := by
      apply orderOf_dvd_iff_zpow_eq_one.1
      rw [hord]
      exact ⟨c, by push_cast; exact h3⟩
    rw [hτs, ← zpow_add, show j + j = j * 2 by ring]
    exact h4
  refine ⟨Subgroup.zpowers s, Subgroup.zpowers_le.2 hsT, Subgroup.zpowers_le.2 hxF, inferInstance,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply le_antisymm
    · rintro g ⟨hgF, hgRd⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgF
      have hτ : (phig x Kb s) ^ j ∈ IVK.innDiagSub e := by
        rw [← hτs]; exact hgRd.2.2
      have h1 : (phig x Kb s) ^ j ∈ IVK.innDiagSub e ⊓ IVK.fieldAutSub e :=
        ⟨hτ, (hsRj j).2⟩
      rw [hDF] at h1
      have h2 : (phig x Kb s) ^ j = 1 := h1
      have h3 : ((2 ^ m : ℕ) : ℤ) ∣ j := by
        have := orderOf_dvd_iff_zpow_eq_one.2 h2
        rwa [hord] at this
      obtain ⟨j', hj'⟩ := h3
      refine Subgroup.mem_zpowers_iff.2 ⟨j', ?_⟩
      rw [hj', zpow_mul, zpow_natCast, hsx]
    · exact le_inf (Subgroup.zpowers_le.2 hxF) (Subgroup.zpowers_le.2 (SitFacts.Qg_le_Rd hxQ))
  ·
    apply le_antisymm
    · exact sup_le (fun g hg => hg.1) (Subgroup.zpowers_le.2 hsT)
    · intro t ht
      obtain ⟨k, hk⟩ := hG t ht
      have : t = s ^ k * ((s ^ k)⁻¹ * t) := by group
      rw [this]
      exact mul_mem (mem_sup_right (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩)) (mem_sup_left hk)
  ·
    rintro w hwF hw4
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwF
    have hf2 := hw2 j hw4
    have hwT : s ^ j ∈ T := T.zpow_mem hsT j
    have hwC : s ^ j ∈ Cx x := h.T_le_C hwT
    have hfR : phig x Kb (s ^ j) ∈ N.R := by rw [hτs]; exact hsRj j
    refine ⟨fun p hp => ?_, fun b hb => ?_⟩
    ·
      have hpC : p ∈ Cx x := h.T_le_C hp.1
      have hcentf : ∀ a ∈ N.P, a * phig x Kb (s ^ j) = phig x Kb (s ^ j) * a :=
        NR_inv_cent hfR hf2
      have hwpw : s ^ j * p * (s ^ j)⁻¹ ∈ Pg x Kb T := (Pg_normal x Kb h.T_le_C).2 _ hwT p hp
      have e1 : phig x Kb (s ^ j * p * (s ^ j)⁻¹) = phig x Kb p := by
        rw [phig_mul x Kb (mul_mem hwC hpC) (inv_mem hwC), phig_mul x Kb hwC hpC,
          phig_inv x Kb hwC, mul_inv_eq_iff_eq_mul]
        exact (hcentf _ ((h.hPN _).2 ⟨p, hp, rfl⟩)).symm
      have e2 := h.phig_inj_P hwpw hp e1
      calc s ^ j * p = (s ^ j * p * (s ^ j)⁻¹) * s ^ j := by group
        _ = p * s ^ j := by rw [e2]
    ·
      have hbC : b ∈ Cx x := hb.2.1
      have hbT : b ∈ T := hb.1
      have hbPt : phig x Kb b ∈ N.Pt := ⟨h.hTN b hbT, hb.2.2⟩
      obtain ⟨hu1, hu2⟩ := comm_mem_center h.hF h12a h12d hfR hf2 hbPt
      have hcT : s ^ j * b * (s ^ j)⁻¹ * b⁻¹ ∈ T :=
        T.mul_mem (T.mul_mem (T.mul_mem hwT hbT) (T.inv_mem hwT)) (T.inv_mem hbT)
      have hcphi : phig x Kb (s ^ j * b * (s ^ j)⁻¹ * b⁻¹) =
          phig x Kb (s ^ j) * phig x Kb b * (phig x Kb (s ^ j))⁻¹ * (phig x Kb b)⁻¹ := by
        rw [phig_mul x Kb (mul_mem (mul_mem hwC hbC) (inv_mem hwC)) (inv_mem hbC),
          phig_mul x Kb (mul_mem hwC hbC) (inv_mem hwC), phig_mul x Kb hwC hbC,
          phig_inv x Kb hwC, phig_inv x Kb hbC]
      have hxz : ∀ g ∈ T, (phig x Kb g = 1 ∨ phig x Kb g = phig x Kb z) →
          g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by
        intro g hg hgz
        rcases hgz with h1 | h1
        · exact mem_sup_left (hQmem g hg h1)
        · have hzC : z ∈ Cx x := ((mem_Kg x Kb).1 hz.z_mem_P.2).1
          have hzT : z ∈ T := hz.z_mem_P.1
          have h2 : phig x Kb (z⁻¹ * g) = 1 := by
            rw [phig_mul x Kb (inv_mem hzC) (h.T_le_C hg), phig_inv x Kb hzC, h1, inv_mul_cancel]
          have h3 := hQmem _ (T.mul_mem (T.inv_mem hzT) hg) h2
          have : g = z * (z⁻¹ * g) := by group
          rw [this]
          exact mul_mem (mem_sup_right (Subgroup.mem_zpowers z)) (mem_sup_left h3)
      apply hxz _ hcT
      rw [hcphi]
      rcases card_P_cases h h12c with h4 | h8
      ·
        have hR := NR_eq_bot_of_card_four h h12f h4
        have hf1 : phig x Kb (s ^ j) = 1 := by
          have : phig x Kb (s ^ j) ∈ (⊥ : Subgroup (MulAut ↥Kb)) := by
            rw [hR] at hfR; exact hfR
          exact this
        left
        rw [hf1]; group
      · rcases eq_one_or_phi_z h h12c hz h8 hu1 hu2 with h1 | h1
        · left; exact h1
        · right; exact h1
  ·
    intro h4
    have hR := NR_eq_bot_of_card_four h h12f h4
    have hf1 : phig x Kb s = 1 := by
      have : phig x Kb s ∈ (⊥ : Subgroup (MulAut ↥Kb)) := by
        rw [hR] at hsR; exact hsR
      exact this
    apply le_antisymm
    · exact Subgroup.zpowers_le.2 (hQmem s hsT hf1)
    · exact Subgroup.zpowers_le.2 hxF
  ·
    intro h8 t htT hcent
    have htC := h.T_le_C htT
    obtain ⟨z₁, hz₁P, hz₁c, e₁, he₁Fl, M, hM, hord1, hzc1, hte⟩ :=
      cent_decomp_center h h14j htC hcent
    have hz₁z : z₁ = 1 ∨ z₁ = phig x Kb z := eq_one_or_phi_z h h12c hz h8 hz₁P hz₁c
    have hzC : z ∈ Cx x := ((mem_Kg x Kb).1 hz.z_mem_P.2).1
    have hz₁2 : z₁ * z₁ = 1 := by
      rcases hz₁z with h1 | h1
      · rw [h1, one_mul]
      · rw [h1, ← phig_mul x Kb hzC hzC, hz.z_sq, phig_one]
    have he₁2 : e₁ * e₁ = 1 := by
      obtain ⟨n, hn⟩ := h.sylow.2.1 ⟨t, htT⟩
      have htn : t ^ (2 ^ (n + 1)) = 1 := by
        have : t ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
        rw [pow_succ, pow_mul, this, one_pow]
      have h1 : (phig x Kb t) ^ (2 ^ (n + 1)) = 1 := by
        rw [← phig_pow x Kb htC, htn, phig_one]
      rw [hte, (commute_of_mul_eq hzc1).mul_pow] at h1
      have hz1 : z₁ ^ (2 ^ (n + 1)) = 1 := by
        rw [pow_succ', pow_mul, pow_two, hz₁2, one_pow]
      rw [hz1, one_mul] at h1
      have hd : orderOf e₁ ∣ 2 :=
        dvd_two_of_dvd_pow_two_of_dvd_two_mul hM (orderOf_dvd_of_pow_eq_one h1) hord1
      have : e₁ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
      rwa [pow_two] at this
    obtain ⟨k, hk⟩ := hG t htT
    set n : G := (s ^ k)⁻¹ * t with hn
    have hnRd : n ∈ Rdg x Kb e T := hk
    have hnC : n ∈ Cx x := hnRd.2.1
    have hskC : s ^ k ∈ Cx x := zpow_mem hsC k
    have h1 : phig x Kb t = (phig x Kb s) ^ k * phig x Kb n := by
      have : t = s ^ k * n := by rw [hn]; group
      rw [this, phig_mul x Kb hskC hnC, hτs]
    have h2 : z₁ * e₁ = ((phig x Kb s) ^ k * phig x Kb n * ((phig x Kb s) ^ k)⁻¹) *
        (phig x Kb s) ^ k := by
      rw [← hte, h1]; group
    have h3 : (phig x Kb s) ^ k * phig x Kb n * ((phig x Kb s) ^ k)⁻¹ ∈ IVK.innDiagSub e :=
      hD.conj_mem _ hnRd.2.2 _
    have hz₁D : z₁ ∈ IVK.innDiagSub e := IVK.innAut_le_innDiagSub e (NP_mem_iff.1 hz₁P).2
    have h4 : ((phig x Kb s) ^ k * phig x Kb n * ((phig x Kb s) ^ k)⁻¹)⁻¹ * z₁ =
        (phig x Kb s) ^ k * e₁⁻¹ := by
      have h5 : z₁ = ((phig x Kb s) ^ k * phig x Kb n * ((phig x Kb s) ^ k)⁻¹) *
          (phig x Kb s) ^ k * e₁⁻¹ := by
        calc z₁ = z₁ * e₁ * e₁⁻¹ := by group
          _ = _ := by rw [h2]
      rw [h5]; group
    have h6a : (phig x Kb s) ^ k * e₁⁻¹ ∈ IVK.innDiagSub e := by
      rw [← h4]
      exact mul_mem (inv_mem h3) hz₁D
    have hskFl : (phig x Kb s) ^ k ∈ IVK.fieldAutSub e := (hsRj k).2
    have h6b : (phig x Kb s) ^ k * e₁⁻¹ ∈ IVK.fieldAutSub e := mul_mem hskFl (inv_mem he₁Fl)
    have h6 : (phig x Kb s) ^ k * e₁⁻¹ ∈ IVK.innDiagSub e ⊓ IVK.fieldAutSub e := ⟨h6a, h6b⟩
    rw [hDF] at h6
    have h7 : e₁ = (phig x Kb s) ^ k := by
      have : (phig x Kb s) ^ k * e₁⁻¹ = 1 := h6
      calc e₁ = ((phig x Kb s) ^ k * e₁⁻¹)⁻¹ * (phig x Kb s) ^ k := by group
        _ = (phig x Kb s) ^ k := by rw [this]; group
    have hwT : s ^ k ∈ T := T.zpow_mem hsT k
    have hwF : s ^ k ∈ Subgroup.zpowers s := Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    have hwphi : phig x Kb (s ^ k) = e₁ := by rw [hτs, h7]
    have hw4 : (s ^ k) ^ 4 = 1 := by
      have h8' : phig x Kb (s ^ k * s ^ k) = 1 := by
        rw [phig_mul x Kb hskC hskC, hwphi]; exact he₁2
      have h9 := hQmem _ (T.mul_mem hwT hwT) h8'
      have h10 := zpowers_sq_one hx _ h9
      calc (s ^ k) ^ 4 = (s ^ k * s ^ k) * (s ^ k * s ^ k) := by group
        _ = 1 := h10
    have hu₀T : t * (s ^ k)⁻¹ ∈ T := T.mul_mem htT (T.inv_mem hwT)
    have hu₀phi : phig x Kb (t * (s ^ k)⁻¹) = z₁ := by
      rw [phig_mul x Kb htC (inv_mem hskC), phig_inv x Kb hskC, hwphi, hte]; group
    have hu₀ : t * (s ^ k)⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by
      rcases hz₁z with h1' | h1'
      · exact mem_sup_left (hQmem _ hu₀T (by rw [hu₀phi, h1']))
      · have hzT : z ∈ T := hz.z_mem_P.1
        have h2' : phig x Kb (z⁻¹ * (t * (s ^ k)⁻¹)) = 1 := by
          rw [phig_mul x Kb (inv_mem hzC) (mul_mem htC (inv_mem hskC)), phig_inv x Kb hzC, hu₀phi,
            h1', inv_mul_cancel]
        have h3' := hQmem _ (T.mul_mem (T.inv_mem hzT) hu₀T) h2'
        have : t * (s ^ k)⁻¹ = z * (z⁻¹ * (t * (s ^ k)⁻¹)) := by group
        rw [this]
        exact mul_mem (mem_sup_right (Subgroup.mem_zpowers z)) (mem_sup_left h3')
    exact ⟨t * (s ^ k)⁻¹, hu₀, s ^ k, hwF, hw4, by group⟩

theorem ip_T_normal_twisted (h : SitFacts x Kb e N T) (hrk : Rank2Le (Cx x) 3) (hx : x * x = 1)
    (hx1 : x ≠ 1) (hQ : Qg x Kb T = Subgroup.zpowers x) (h12a : IVK.IVK_1_2a_struct)
    (_h12c : IVK.IVK_1_2c) (h12d : IVK.IVK_1_2d) (h13fa : IVK.IVK_1_3f_a) {b : G} (hbT : b ∈ T)
    {d₀ r : MulAut ↥Kb} (hd₀ : d₀ ∈ N.Pt) (hr : r ∈ N.R) (hbdr : phig x Kb b = d₀ * r)
    (hno : ∀ n ∈ Rdg x Kb e T, phig x Kb n ≠ d₀) :
    ∀ E E' : Subgroup G, E ≤ Rdg x Kb e T → E' ≤ Rdg x Kb e T → IsElemAb2 E → IsElemAb2 E' →
      Nat.card E = 8 → Nat.card E' = 8 → ∃ t ∈ T, E' = Hconj t E := by
  intro E E' hERd hE'Rd hE hE' hc hc'
  have hRdT : Rdg x Kb e T ≤ T := fun g hg => hg.1
  have hET : E ≤ T := hERd.trans hRdT
  have hE'T : E' ≤ T := hE'Rd.trans hRdT
  have hEC : E ≤ Cx x := hET.trans h.T_le_C
  have hE'C : E' ≤ Cx x := hE'T.trans h.T_le_C
  obtain ⟨hxE, hcharE, hEA, hcardE⟩ := elemAb8_data h hQ hrk hx hx1 hET hE hc
  obtain ⟨hxE', hcharE', hEA', hcardE'⟩ := elemAb8_data h hQ hrk hx hx1 hE'T hE' hc'
  have himg : imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) = N.P := by
    rcases imgRd_cases h with hc1 | hc1
    · exact hc1
    · exfalso
      have : d₀ ∈ imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) := by rw [hc1]; exact hd₀
      obtain ⟨n, hn, hnd⟩ := (mem_imgSub (Rd_le_C h)).1 this
      exact hno n hn hnd
  have hd₀P : d₀ ∉ N.P := by
    intro hP
    rw [← himg] at hP
    obtain ⟨n, hn, hnd⟩ := (mem_imgSub (Rd_le_C h)).1 hP
    exact hno n hn hnd
  have hVP : imgSub x Kb E hEC ≤ N.P := himg ▸ imgSub_mono hEC (Rd_le_C h) hERd
  have hV'P : imgSub x Kb E' hE'C ≤ N.P := himg ▸ imgSub_mono hE'C (Rd_le_C h) hE'Rd
  have h4 := isFourSubgroup_of_isEA hEA hcardE
  have h4' := isFourSubgroup_of_isEA hEA' hcardE'
  have hg : ∃ g ∈ T, (imgSub x Kb E hEC).map (MulAut.conj (phig x Kb g)).toMonoidHom =
      imgSub x Kb E' hE'C := by
    rcases fuse_twisted h.hF h12a h12d h13fa hd₀ hd₀P hr hVP hV'P h4 h4' with
      ⟨a, ha, hVa⟩ | ⟨a, ha, hVa⟩
    · obtain ⟨p, hp, rfl⟩ := (h.hPN a).1 ha
      exact ⟨p, hp.1, hVa⟩
    · obtain ⟨p, hp, rfl⟩ := (h.hPN a).1 ha
      refine ⟨p * b, T.mul_mem hp.1 hbT, ?_⟩
      rw [phig_mul x Kb (h.T_le_C hp.1) (h.T_le_C hbT), hbdr]
      exact hVa
  obtain ⟨g, hgT, hgV⟩ := hg
  refine ⟨g⁻¹, T.inv_mem hgT, ?_⟩
  have hgC := h.T_le_C hgT
  have hgiC : g⁻¹ ∈ Cx x := inv_mem hgC
  have hmemE' : ∀ y, y ∈ imgSub x Kb E' hE'C ↔
      ∃ v ∈ imgSub x Kb E hEC, phig x Kb g * v * (phig x Kb g)⁻¹ = y := by
    intro y
    rw [← hgV]
    simp [Subgroup.mem_map, MulAut.conj_apply]
  have hconjphi : ∀ a ∈ Cx x, phig x Kb (g⁻¹ * a * g⁻¹⁻¹) =
      (phig x Kb g)⁻¹ * phig x Kb a * (phig x Kb g) := by
    intro a ha
    rw [phig_mul x Kb (mul_mem hgiC ha) (inv_mem hgiC), phig_mul x Kb hgiC ha, phig_inv x Kb hgC,
      phig_inv x Kb hgiC, phig_inv x Kb hgC, inv_inv]
  ext a
  rw [mem_Hconj]
  constructor
  · intro ha
    have haT : a ∈ T := hE'T ha
    have haC := hE'C ha
    have hconjT : g⁻¹ * a * g⁻¹⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem (T.inv_mem hgT) haT) (T.inv_mem (T.inv_mem hgT))
    rw [hcharE _ hconjT]
    have h1 : phig x Kb a ∈ imgSub x Kb E' hE'C := (mem_imgSub hE'C).2 ⟨a, ha, rfl⟩
    obtain ⟨v, hv, hva⟩ := (hmemE' _).1 h1
    have : phig x Kb (g⁻¹ * a * g⁻¹⁻¹) = v := by
      rw [hconjphi a haC, ← hva]; group
    rw [this]; exact hv
  · intro ha
    have hraT : g⁻¹ * a * g⁻¹⁻¹ ∈ T := hET ha
    have haT : a ∈ T := by
      have : a = g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ := by group
      rw [this]; exact T.mul_mem (T.mul_mem hgT hraT) (T.inv_mem hgT)
    have haC := h.T_le_C haT
    rw [hcharE _ hraT, hconjphi a haC] at ha
    rw [hcharE' _ haT, hmemE']
    refine ⟨_, ha, ?_⟩
    group

omit [Finite G] [Kb.Normal] in
theorem orderOf_NT (a : MulAut ↥Kb) (ha : a ∈ (N.T : Subgroup (MulAut ↥Kb))) :
    ∃ m : ℕ, orderOf a = 2 ^ m := by
  have hp : IsPGroup 2 ↥(N.T : Subgroup (MulAut ↥Kb)) := N.T.isPGroup'
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hp) ⟨a, ha⟩
  exact ⟨m, by rw [← hm]; exact Subgroup.orderOf_coe (⟨a, ha⟩ : ↥(N.T : Subgroup _))⟩

theorem ip_T_normal_L2 (h : SitFacts x Kb e N T) (hrk : Rank2Le (Cx x) 3) (hx : x * x = 1)
    (hx1 : x ≠ 1) (h12a : IVK.IVK_1_2a_struct) (h12c : IVK.IVK_1_2c) (h12d : IVK.IVK_1_2d)
    (h12e : IVK.IVK_1_2e) (h12f : IVK.IVK_1_2f) (h13fa : IVK.IVK_1_3f_a) (h14j : IVK.IVK_1_4j)
    {z : G} (hz : HZ T (Pg x Kb T) z) (hQ : Qg x Kb T = Subgroup.zpowers x)
    (hΩ : omega1 T ≤ Rdg x Kb e T) :
    IP_T_normal x z T (Pg x Kb T) (Rdg x Kb e T) := by
  obtain ⟨b, hbT, hb⟩ := ip_Rd_cyclic h h12e
  have hbC := h.T_le_C hbT
  obtain ⟨d₀, hd₀, r, hr, hdr⟩ := decomp_NT (h.hTN b hbT)
  by_cases hcase : ∃ n₀ ∈ Rdg x Kb e T, phig x Kb n₀ = d₀
  · right
    obtain ⟨n₀, hn₀, hn₀d⟩ := hcase
    have hn₀C : n₀ ∈ Cx x := hn₀.2.1
    have hs₀T : n₀⁻¹ * b ∈ T := T.mul_mem (T.inv_mem hn₀.1) hbT
    have hs₀τ : phig x Kb (n₀⁻¹ * b) = r := by
      rw [phig_mul x Kb (inv_mem hn₀C) hbC, phig_inv x Kb hn₀C, hn₀d, ← hdr]
      group
    have hG₀ := gen_shift (SitFacts.Rd_normal h) hs₀T hn₀ (by group : b = n₀ * (n₀⁻¹ * b)) hb
    have hxC : x ∈ Cx x := x_mem_Cx x
    have hxT : x ∈ T := x_mem_of_sylow x h.sylow hx hx1
    have hxQ : x ∈ Qg x Kb T := h.x_mem_Q hx hx1
    by_cases hr1 : r = 1
    ·
      have hs₀x : n₀⁻¹ * b ∈ Subgroup.zpowers x := by
        apply mem_zpowers_x_of_phig hQ h.T_le_C hs₀T
        rw [hs₀τ, hr1]
      have hs₀Q : n₀⁻¹ * b ∈ Qg x Kb T := by rw [hQ]; exact hs₀x
      have hs₀Rd : ∀ k : ℤ, (n₀⁻¹ * b) ^ k ∈ Rdg x Kb e T := fun k =>
        zpow_mem (SitFacts.Qg_le_Rd hs₀Q) k
      have hTRd : ∀ t ∈ T, t ∈ Rdg x Kb e T := by
        intro t ht
        obtain ⟨k, hk⟩ := hG₀ t ht
        have : t = (n₀⁻¹ * b) ^ k * (((n₀⁻¹ * b) ^ k)⁻¹ * t) := by group
        rw [this]
        exact mul_mem (hs₀Rd k) hk
      exact ip_T_normal_split h hx hx1 hQ h12a h12c h12d h12f h14j hz (s := x) hxT
        (by rw [phig_x_eq_one x Kb]; exact one_mem _) (m := 0)
        (by rw [phig_x_eq_one x Kb]; simp) (by simp)
        (fun t ht => ⟨0, by simpa using hTRd t ht⟩)
    ·
      obtain ⟨m, hm⟩ := orderOf_NT r hr.1
      have hm1 : 1 ≤ m := by
        by_contra hcon
        have : m = 0 := by omega
        subst this
        exact hr1 (orderOf_eq_one_iff.1 (by simpa using hm))
      have hsm : (n₀⁻¹ * b) ^ (2 ^ m) ∈ Subgroup.zpowers x := by
        apply mem_zpowers_x_of_phig hQ h.T_le_C (T.pow_mem hs₀T _)
        rw [phig_pow x Kb (h.T_le_C hs₀T), hs₀τ, ← hm]
        exact pow_orderOf_eq_one r
      have hsm1 : (n₀⁻¹ * b) ^ (2 ^ m) ≠ 1 := by
        intro h1
        obtain ⟨v, hv⟩ : ∃ v : G, v = (n₀⁻¹ * b) ^ (2 ^ (m - 1)) := ⟨_, rfl⟩
        have hvv : v * v = 1 := by
          rw [hv, ← pow_add, ← two_mul, ← pow_succ' 2 (m - 1), Nat.sub_add_cancel hm1]
          exact h1
        have hvT : v ∈ T := by rw [hv]; exact T.pow_mem hs₀T _
        have hvRd : v ∈ Rdg x Kb e T :=
          hΩ (Subgroup.subset_closure ⟨hvT, hvv⟩)
        have hvτ : phig x Kb v = r ^ (2 ^ (m - 1)) := by
          rw [hv, phig_pow x Kb (h.T_le_C hs₀T), hs₀τ]
        have hD : r ^ (2 ^ (m - 1)) ∈ IVK.innDiagSub e ⊓ IVK.fieldAutSub e :=
          ⟨by rw [← hvτ]; exact hvRd.2.2, pow_mem hr.2 _⟩
        rw [IVK.innDiagSub_inf_fieldAutSub e] at hD
        have h2 : r ^ (2 ^ (m - 1)) = 1 := hD
        have h3 : 2 ^ m ∣ 2 ^ (m - 1) := by
          rw [← hm]; exact orderOf_dvd_of_pow_eq_one h2
        have h4 : 2 ^ m ≤ 2 ^ (m - 1) := Nat.le_of_dvd (by positivity) h3
        have h5 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have hsmx : (n₀⁻¹ * b) ^ (2 ^ m) = x := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hsm
        rcases zpow_cases_of_sq hx k with h0 | h0
        · exact absurd (by rw [← hk, h0]) hsm1
        · rw [← hk, h0]
      exact ip_T_normal_split h hx hx1 hQ h12a h12c h12d h12f h14j hz hs₀T (by rw [hs₀τ]; exact hr)
        (m := m) (by rw [hs₀τ]; exact hm) hsmx hG₀
  · left
    push Not at hcase
    exact ip_T_normal_twisted h hrk hx hx1 hQ h12a h12c h12d h13fa hbT hd₀ hr hdr.symm hcase

theorem sq_eq_one_of_orderOf_two {M : Type*} [Group M] {u : M} (hu : orderOf u = 2) :
    u * u = 1 ∧ u ≠ 1 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hu])
  · rw [h, orderOf_one] at hu
    omega

theorem ipTNormalLeaf_of_ivk (hIVK : IVKL2Facts) (x : G) (Kb : Subgroup (CentralizerBar x)) :
    IPTNormalLeaf x Kb := by
  intro c _ F _ _ e N T hsit z hz hQ hΩ
  obtain ⟨hx2, hx1⟩ := sq_eq_one_of_orderOf_two c.x_order
  exact ip_T_normal_L2 hsit (rank2Le_of_pRank_le x c.rankC.le) hx2 hx1 hIVK.h12a hIVK.h12c
    hIVK.h12d hIVK.h12e hIVK.h12f hIVK.h13fa hIVK.h14j hz hQ hΩ

end CFSG.GH74.GLS.Stage1.Thm6.Glue
