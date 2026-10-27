module

public import CFSG.GH74.Uniqueness.Section166C

public section

namespace CFSG.GH74.Uniqueness.Cor166

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem exists_involution_mem_zpowers {x : X} (hx : IsPGroup 2 (zpowers x)) (hx1 : x ≠ 1) :
    ∃ y ∈ zpowers x, orderOf y = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (zpowers x) := by
    rcases hx.card_eq_or_dvd with h | h
    · rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
      exact absurd h hx1
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem eq_bot_of_no_involution {A : Subgroup X} (hA : IsPGroup 2 A)
    (h : ∀ y ∈ A, orderOf y ≠ 2) : A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨y, hy, hy2⟩ := exists_involution_mem_zpowers (hA.to_le (zpowers_le.mpr hx)) hx1
  exact h y (zpowers_le.mpr hx hy) hy2

theorem exists_conj_mem_of_isSylowOf_pow {T K : Subgroup X} (hT : ABGLocalTools.IsSylowOf 2 T K)
    {y : X} (hyK : y ∈ K) {k : ℕ} (hy : y ^ 2 ^ k = 1) : ∃ g ∈ K, g * y * g⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', rfl⟩ := hT
  have hp : IsPGroup 2 (zpowers (⟨y, hyK⟩ : ↥K)) := by
    have hdvd : orderOf (⟨y, hyK⟩ : ↥K) ∣ 2 ^ k := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hy
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K R T'
  refine ⟨g, g.2, ?_⟩
  have hyR : y ∈ (R : Subgroup ↥K).map K.subtype := ⟨⟨y, hyK⟩, hR (mem_zpowers _), rfl⟩
  have := mem_map_smul R g hyR
  rwa [hg] at this

omit [Finite X] in
theorem eq_of_mem_zpowers_of_ne_one {u x : X} (hu2 : orderOf u = 2) (hx : x ∈ zpowers u)
    (hx1 : x ≠ 1) : x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hu2] at hx1 ⊢
  have h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h with h | h
  · rw [h, zpow_zero] at hx1
    exact absurd rfl hx1
  · rw [h, zpow_one]

omit [Finite X] in
theorem orderOf_conj_inv (g y : X) : orderOf (g⁻¹ * y * g) = orderOf y := by
  have := orderOf_conj' g⁻¹ y
  rwa [inv_inv] at this

section Conf

theorem isSylowOf_P_B0
    (S : ZDSetup X Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) :
    ABGLocalTools.IsSylowOf 2 c.P c.B0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hPp, hdvd⟩ := ABGLocalTools.isSylowOf_iff.mp c.hP
  refine ABGLocalTools.isSylowOf_iff.mpr ⟨P_le_B0 c, hPp, fun h => ?_⟩
  have hmul := Subgroup.relIndex_mul_relIndex c.P (c.B0 ⊓ M) c.B0 c.hP.le inf_le_left
  have hidx : (c.B0 ⊓ M).relIndex c.B0 = (2 ^ n) ^ i + 1 := by
    rw [inf_comm]
    exact hB.index_eq S
  have hni : 1 ≤ n ∧ 1 ≤ i := by
    rcases hB.bender.cases' with ⟨hi, -, hn⟩ | ⟨hi, -, a, ha, hn⟩ | ⟨hi, -, hn⟩ <;> omega
  have hodd : ¬ 2 ∣ (2 ^ n) ^ i + 1 := by
    have h2 : 2 ∣ (2 ^ n) ^ i := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
    omega
  rw [← hmul, hidx] at h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h1
  · exact hdvd h1
  · exact hodd h1

theorem mul_self_mem_J
    (S : ZDSetup X Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) {x : X}
    (hxN : x ∈ normalizer (c.B0 : Set X)) (hxP : ∀ p ∈ c.P, x * p = p * x) : x * x ∈ c.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := (isSylowOf_P_B0 S c hB).exists_sylow_eq_subgroupOf
  let Pbar : Sylow 2 (↥c.B0 ⧸ center ↥c.B0) :=
    P'.mapSurjective (QuotientGroup.mk'_surjective (center ↥c.B0))
  let g : ↥(normalizer (c.B0 : Set X)) := ⟨x, hxN⟩
  have hσ : ∀ k ∈ (Pbar : Subgroup (↥c.B0 ⧸ center ↥c.B0)), benderAut c.B0 g k = k := by
    intro k hk
    rw [Sylow.coe_mapSurjective] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    have hpP : (p : X) ∈ c.P := by
      rw [hP'] at hp
      exact Subgroup.mem_subgroupOf.mp hp
    rw [QuotientGroup.mk'_apply]
    refine benderAut_mk c.B0 g p p ?_
    change (p : X) = x * p * x⁻¹
    rw [hxP p hpP]
    group
  obtain ⟨r, hr, hσr⟩ := hB.bender.lemma_3_6_a Pbar (benderAut c.B0 g) hσ
  obtain ⟨t, hc⟩ := hB.bender.exists_benderCore Pbar
  have hr2 : r * r = 1 := hc.center_sq r hr
  have h1 : benderAut c.B0 (g * g) = 1 := by
    rw [map_mul]
    ext k
    rw [MulAut.mul_apply, hσr, hσr, MulAut.one_apply]
    calc r * (r * k * r⁻¹) * r⁻¹ = (r * r) * k * (r * r)⁻¹ := by group
      _ = k := by rw [hr2]; group
  exact benderSub_mem_centralizer_of_eq_one S.invariant hB h1

theorem T1_le_centralizer_uz (c : Conf16 Z M) : c.T1 ≤ centralizer ({c.u * c.z} : Set X) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxu := comm_u_of_mem_B c (T1_le_B c hx)
  have hxz := c.hz_T1.2 x hx
  symm
  calc c.u * c.z * x = c.u * (c.z * x) := by group
    _ = c.u * (x * c.z) := by rw [hxz]
    _ = (c.u * x) * c.z := by group
    _ = (x * c.u) * c.z := by rw [hxu]
    _ = x * (c.u * c.z) := by group

theorem exists_normalizer_conj_uz (c : Conf16 Z M) (h163 : Lemma163Stmt Z M)
    (hconj : IsConj c.u (c.u * c.z)) :
    ∃ g ∈ normalizer (c.T1 : Set X), g * c.u * g⁻¹ = c.u * c.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := isConj_iff.mp hconj
  set C := centralizer ({c.u * c.z} : Set X) with hCdef
  have hT1C : c.T1 ≤ C := T1_le_centralizer_uz c
  have hT1'C : conjugate c.T1 h⁻¹ ≤ C := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have hxu := comm_u_of_mem_B c (T1_le_B c hx)
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff, ← hh]
    symm
    calc h * c.u * h⁻¹ * x = h * (c.u * (h⁻¹ * x * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * x * h) * c.u) * h⁻¹ := by rw [hxu]
      _ = x * (h * c.u * h⁻¹) := by group
  have hCB : Nat.card C = Nat.card c.B := by
    apply le_antisymm
    · have hle : conjugate C h ≤ c.B := by
        intro x hx
        rw [mem_conjugate_iff, hCdef, Subgroup.mem_centralizer_singleton_iff, ← hh] at hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        symm
        calc c.u * x = h⁻¹ * (h * c.u * h⁻¹ * (h * x * h⁻¹)) * h := by group
          _ = h⁻¹ * (h * x * h⁻¹ * (h * c.u * h⁻¹)) * h := by rw [hx]
          _ = x * c.u := by group
      calc Nat.card C = Nat.card (conjugate C h) := (card_conjugate C h).symm
        _ ≤ Nat.card c.B := Subgroup.card_le_of_le hle
    · have hle : conjugate c.B h⁻¹ ≤ C := by
        intro x hx
        rw [mem_conjugate_iff, inv_inv, Subgroup.mem_centralizer_singleton_iff] at hx
        rw [hCdef, Subgroup.mem_centralizer_singleton_iff, ← hh]
        symm
        calc h * c.u * h⁻¹ * x = h * (c.u * (h⁻¹ * x * h)) * h⁻¹ := by group
          _ = h * ((h⁻¹ * x * h) * c.u) * h⁻¹ := by rw [hx]
          _ = x * (h * c.u * h⁻¹) := by group
      calc Nat.card c.B = Nat.card (conjugate c.B h⁻¹) := (card_conjugate c.B h⁻¹).symm
        _ ≤ Nat.card C := Subgroup.card_le_of_le hle
  have hT1syl : ABGLocalTools.IsSylowOf 2 c.T1 C := by
    apply ABGLocalTools.isSylowOf_of_card hT1C
    rw [(h163 c).2.2.1.card_eq, hCB]
  have hT1'syl : ABGLocalTools.IsSylowOf 2 (conjugate c.T1 h⁻¹) C := by
    apply ABGLocalTools.isSylowOf_of_card hT1'C
    rw [card_conjugate, (h163 c).2.2.1.card_eq, hCB]
  obtain ⟨w, hwC, hw⟩ := exists_conj_of_isSylowOf hT1'syl hT1syl
  rw [conjugate_conjugate] at hw
  have hN : h⁻¹ * w ∈ normalizer (c.T1 : Set X) := conjugate_eq_iff_mem_normalizer.mp hw
  refine ⟨(h⁻¹ * w)⁻¹, (normalizer (c.T1 : Set X)).inv_mem hN, ?_⟩
  rw [hCdef, Subgroup.mem_centralizer_singleton_iff] at hwC
  calc (h⁻¹ * w)⁻¹ * c.u * (h⁻¹ * w)⁻¹⁻¹ = w⁻¹ * (h * c.u * h⁻¹) * w := by group
    _ = w⁻¹ * (c.u * c.z) * w := by rw [hh]
    _ = w⁻¹ * (w * (c.u * c.z)) := by rw [mul_assoc, hwC]
    _ = c.u * c.z := by group

theorem mem_normalizer_J (S : ZDSetup X Z M) (c : Conf16 Z M) {x : X} (hx : x ∈ c.B) :
    x ∈ normalizer (c.J : Set X) := by
  have hxN := B_le_normalizer c S hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key : ∀ (a w : X), a ∈ normalizer (c.B0 : Set X) → w ∈ c.J → a * w * a⁻¹ ∈ c.J := by
    intro a y ha hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro b hb
    have hb' : a⁻¹ * b * a ∈ c.B0 := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) b).mp hb
      simpa using this
    have h1 := hy _ hb'
    calc b * (a * y * a⁻¹) = a * ((a⁻¹ * b * a) * y) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * b * a)) * a⁻¹ := by rw [h1]
      _ = a * y * a⁻¹ * b := by group
  constructor
  · exact key x y hxN
  · intro hy
    have := key x⁻¹ _ (inv_mem hxN) hy
    simpa [mul_assoc] using this

end Conf

section Main

theorem inf_J_le_zpowers
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h163 : Lemma163Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h165 : Prop165Stmt Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) : c.T1 ⊓ c.J ≤ zpowers c.u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgN, hgu⟩ := exists_normalizer_conj_uz c h163 (cor166c_conj S c h163 h164 h165 hB)
  set U := c.T1 ⊓ c.J with hUdef
  have hBzero : c.Bzero ≤ c.B0 := by
    rw [Conf16.Bzero, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.closure_mono (Set.inter_subset_inter_right Z
        (fun y hy => (Subgroup.mem_inf.mp hy).1)) hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact t_mem_B0 c
  have hUinv : ∀ y ∈ U, orderOf y = 2 → y = c.u := by
    intro y hy hy2
    refine (h164 c n i e hB).1.2 y (Subgroup.mem_inf.mpr ⟨T1_le_B c hy.1, ?_⟩) hy2
    exact Subgroup.centralizer_le hBzero hy.2
  have hgNi : g⁻¹ ∈ normalizer (c.T1 : Set X) := inv_mem hgN
  have hT1N : ∀ {a y : X}, a ∈ normalizer (c.T1 : Set X) → y ∈ c.T1 → a * y * a⁻¹ ∈ c.T1 :=
    fun ha hy => (Subgroup.mem_normalizer_iff.mp ha _).mp hy
  set V := conjugate U g⁻¹ with hVdef
  have hmemV : ∀ x : X, x ∈ V ↔ g⁻¹ * x * g ∈ U := fun x => by
    rw [hVdef, mem_conjugate_iff, inv_inv]
  have hVT1 : V ≤ c.T1 := by
    intro x hx
    have h1 := hT1N hgN ((hmemV x).mp hx).1
    simpa [mul_assoc] using h1
  have hVinv : ∀ x ∈ V, orderOf x = 2 → x = c.u * c.z := by
    intro x hx hx2
    have h1 := hUinv _ ((hmemV x).mp hx) (by rw [orderOf_conj_inv]; exact hx2)
    rw [← hgu, ← h1]
    group
  have hU2 : IsPGroup 2 U := c.hT1.isPGroup.to_le inf_le_left
  have hV2 : IsPGroup 2 V := c.hT1.isPGroup.to_le hVT1
  have huzB0 : c.u * c.z ∉ c.B0 := fun h => u_not_mem_B0 c S hB (by
    have := c.B0.mul_mem h (c.B0.inv_mem (z_mem_B0 c))
    simpa using this)
  have hVP : V ⊓ c.P = ⊥ := by
    refine eq_bot_of_no_involution (hV2.to_le inf_le_left) fun y hy hy2 => ?_
    have := hVinv y hy.1 hy2
    exact huzB0 (this ▸ P_le_B0 c hy.2)
  have hVU : V ⊓ U = ⊥ := by
    refine eq_bot_of_no_involution (hV2.to_le inf_le_left) fun y hy hy2 => ?_
    have h1 := hVinv y hy.1 hy2
    have h2 := hUinv y hy.2 hy2
    have hz1 : c.z = 1 := by
      have : c.u * c.z = c.u * 1 := by rw [mul_one, ← h1, h2]
      exact mul_left_cancel this
    have := S.invariant.1 c.z c.hz
    rw [hz1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hT1P : ∀ {a p : X}, a ∈ c.T1 → p ∈ c.P → a * p * a⁻¹ ∈ c.P := by
    intro a p ha hp
    rw [← inf_B0_eq_P c] at hp ⊢
    refine ⟨hT1N (Subgroup.le_normalizer ha) hp.1, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (B_le_normalizer c S (T1_le_B c ha)) _).mp hp.2
  have hT1U : ∀ {a y : X}, a ∈ c.T1 → y ∈ U → a * y * a⁻¹ ∈ U := by
    intro a y ha hy
    refine ⟨hT1N (Subgroup.le_normalizer ha) hy.1, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_J S c (T1_le_B c ha)) _).mp hy.2
  have hT1V : ∀ {a x : X}, a ∈ c.T1 → x ∈ V → a * x * a⁻¹ ∈ V := by
    intro a x ha hx
    rw [hmemV]
    have h1 := hT1U (hT1N hgNi ha) ((hmemV x).mp hx)
    have e : g⁻¹ * (a * x * a⁻¹) * g = g⁻¹ * a * g⁻¹⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * a * g⁻¹⁻¹)⁻¹ := by
      group
    rw [e]
    exact h1
  have hVcomm : ∀ x ∈ V, ∀ p ∈ c.P, x * p = p * x := by
    intro x hx p hp
    have hxT1 := hVT1 hx
    have h1 : x * p * x⁻¹ * p⁻¹ ∈ c.P := c.P.mul_mem (hT1P hxT1 hp) (c.P.inv_mem hp)
    have h2 : x * p * x⁻¹ * p⁻¹ ∈ V := by
      have := V.mul_mem hx (hT1V (c.hPT1 hp) (V.inv_mem hx))
      simpa [mul_assoc] using this
    have h3 : x * p * x⁻¹ * p⁻¹ ∈ V ⊓ c.P := ⟨h2, h1⟩
    rw [hVP, Subgroup.mem_bot] at h3
    calc x * p = x * p * x⁻¹ * p⁻¹ * (p * x) := by group
      _ = p * x := by rw [h3, one_mul]
  have hVsq : ∀ x ∈ V, x * x = 1 := by
    intro x hx
    have hxT1 := hVT1 hx
    have hJ := mul_self_mem_J S c hB (B_le_normalizer c S (T1_le_B c hxT1)) (hVcomm x hx)
    have h1 : x * x ∈ V ⊓ U := ⟨V.mul_mem hx hx, c.T1.mul_mem hxT1 hxT1, hJ⟩
    rw [hVU, Subgroup.mem_bot] at h1
    exact h1
  intro y hy
  have hgy : g * y * g⁻¹ ∈ V := by
    rw [hmemV]
    simpa [mul_assoc] using hy
  have hy2 : y * y = 1 := by
    have h1 := hVsq _ hgy
    calc y * y = g⁻¹ * (g * y * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = 1 := by rw [h1]; group
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  · rw [hUinv y hy (orderOf_eq_prime (by rw [sq]; exact hy2) hy1)]
    exact mem_zpowers _

theorem mem_zpowers_of_mem_J_B
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h163 : Lemma163Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h165 : Prop165Stmt Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) {s : X} (hsJ : s ∈ c.J) (hsB : s ∈ c.B) {k : ℕ}
    (hs : s ^ 2 ^ k = 1) : s ∈ zpowers c.u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ABGLocalTools.IsSylowOf 2 (c.T1 ⊓ (c.J ⊓ c.B)) (c.J ⊓ c.B) := by
    refine (h163 c).2.2.1.inf_of_le_normalizer inf_le_right fun x hx => ?_
    exact mem_normalizer_inf (mem_normalizer_J S c hx) (Subgroup.le_normalizer hx)
  obtain ⟨a, haJB, ha⟩ := exists_conj_mem_of_isSylowOf_pow hsyl ⟨hsJ, hsB⟩ hs
  have hle := inf_J_le_zpowers S c h163 h164 h165 hB
  have h1 : a * s * a⁻¹ ∈ zpowers c.u := hle ⟨ha.1, ha.2.1⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hcomm : Commute a (c.u ^ m) :=
    (show Commute a c.u from comm_u_of_mem_B c haJB.2).zpow_right m
  have hs' : s = c.u ^ m := by
    calc s = a⁻¹ * (a * s * a⁻¹) * a := by group
      _ = a⁻¹ * c.u ^ m * a := by rw [hm]
      _ = c.u ^ m := by rw [mul_assoc, ← hcomm.eq]; group
  rw [hs']
  exact zpow_mem (mem_zpowers c.u) m

theorem cor166b
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h163 : Lemma163Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h165 : Prop165Stmt Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) : ABGLocalTools.IsSylowOf 2 (zpowers c.u) c.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀, huS₀⟩ := exists_isSylowOf_ge_of_le (Subgroup.zpowers_le.mpr (u_mem_J c))
    (isPGroup_zpowers_of_mul_self (u_mul_self c))
  have hS₀2 := hS₀.isPGroup
  have hpow : ∀ x ∈ S₀, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hS₀2 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have huS : c.u ∈ S₀ := huS₀ (mem_zpowers _)
  obtain ⟨c₀, hc₀S, hc₀2, hc₀c⟩ := exists_central_involution hS₀2 huS c.hu2
  have hc₀B : c₀ ∈ c.B := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc₀c c.u huS).symm
  have hc₀u : c₀ = c.u := by
    obtain ⟨k, hk⟩ := hpow c₀ hc₀S
    have h1 := mem_zpowers_of_mem_J_B S c h163 h164 h165 hB (hS₀.le hc₀S) hc₀B hk
    refine eq_of_mem_zpowers_of_ne_one c.hu2 h1 fun h => ?_
    rw [h, orderOf_one] at hc₀2
    exact absurd hc₀2 (by norm_num)
  have hle : S₀ ≤ zpowers c.u := by
    intro x hx
    have hxB : x ∈ c.B := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hc₀c x hx
      rw [hc₀u] at this
      exact this
    obtain ⟨k, hk⟩ := hpow x hx
    exact mem_zpowers_of_mem_J_B S c h163 h164 h165 hB (hS₀.le hx) hxB hk
  rw [← le_antisymm hle huS₀]
  exact hS₀

end Main

end CFSG.GH74.Uniqueness.Cor166
