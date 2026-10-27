module

public import CFSG.GH74.Uniqueness.Section14Defs
public import CFSG.GH74.Uniqueness.Section14Primary
public import CFSG.GH74.Uniqueness.Bender.SuzukiOdd
public import CFSG.Walter.W67.Section5.Prop56N

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem eq_three_of_two_pow_sub_one_le {n : ℕ} (h3 : 3 ≤ n) (h : 2 ^ n - 1 ≤ 2 * n + 1) :
    n = 3 := by
  by_contra hne
  have h4 : 4 ≤ n := by omega
  have key : ∀ m : ℕ, 4 ≤ m → 2 * m + 2 < 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      rw [pow_succ]
      omega
  have := key n h4
  omega

theorem hom_mul_apply {G V : Type*} [Group G] [Group V] (ρ : G →* MulAut V) (a b : G) (v : V) :
    ρ (a * b) v = ρ a (ρ b v) := by simp

theorem frob149 (hFR : FrobRankStmt) : Frob149Stmt := by
  intro G V _ _ _ _ ρ K u n hGodd hV2 hρ hn hVcard hKcard hu1 hKu hCV hCK hCK' h7 g
  classical
  have hsolv : Group.IsSolvable G := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hGodd
  have hρne : ∀ f : G, ρ f u ≠ 1 := fun f h => hu1 (by
    have h1 : ρ f u = ρ f 1 := by rw [h, map_one]
    exact (ρ f).injective h1)
  have h2n : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hKne : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hKcard
    omega
  have hGtop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro h
    apply hKne
    rw [eq_bot_iff, ← h]
    exact le_top
  obtain ⟨B, hBn, hB1, hBcomm⟩ := Bender.exists_abelian_normal_of_solvable hGtop
  have hBcard : Nat.card B ≠ 1 := fun h => hB1 (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpB⟩ := Nat.exists_prime_and_dvd hBcard
  have : Fact p.Prime := ⟨hp⟩
  set F : Subgroup G := primaryComponent B hBcomm p with hFdef
  have hFn : F.Normal :=
    ⟨fun a ha g => primaryComponent_conj (fun b hb => hBn.conj_mem b hb g) ha⟩
  have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    hBcomm a (mem_primaryComponent.mp ha).1 b (mem_primaryComponent.mp hb).1
  have hFp : IsPGroup p F := isPGroup_primaryComponent hp
  have hFne : F ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpB
    intro hF
    have hxF : (x : G) ∈ F :=
      mem_primaryComponent_of_orderOf x.2 (m := 1) (by rw [Subgroup.orderOf_coe, hx, pow_one])
    rw [hF, Subgroup.mem_bot] at hxF
    have : x = 1 := Subtype.ext hxF
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hFodd : Odd (Nat.card F) := Odd.of_dvd_nat hGodd (Subgroup.card_subgroup_dvd_card F)
  by_cases hFK : F ⊓ K = ⊥
  ·
    exfalso
    have hfpf : ∀ b ∈ K, b ≠ 1 → ∀ a ∈ F, b * a = a * b → a = 1 := by
      intro b hb hb1 a ha hba
      obtain ⟨q, hq, hqb⟩ := Nat.exists_prime_and_dvd (n := orderOf b)
        (fun h => hb1 (orderOf_eq_one_iff.mp h))
      set b' : G := b ^ (orderOf b / q) with hb'
      have hb'K : b' ∈ K := K.pow_mem hb _
      have hb'ord : orderOf b' = q := orderOf_pow_orderOf_div (orderOf_pos b).ne' hqb
      have hab' : a * b' = b' * a := by
        have : Commute a b := hba.symm
        exact (this.pow_right _).eq
      have haN : a ∈ normalizer (K : Set G) := hCK b' hb'K (by rw [hb'ord]; exact hq)
        (Subgroup.mem_centralizer_singleton_iff.mpr hab')
      have hcomm : ∀ k ∈ K, a * k = k * a := by
        intro k hk
        have h1 : a * k * a⁻¹ * k⁻¹ ∈ K :=
          K.mul_mem ((Subgroup.mem_normalizer_iff.mp haN k).mp hk) (K.inv_mem hk)
        have h2 : a * k * a⁻¹ * k⁻¹ ∈ F := by
          have := F.mul_mem ha (hFn.conj_mem a⁻¹ (F.inv_mem ha) k)
          have e : a * (k * a⁻¹ * k⁻¹) = a * k * a⁻¹ * k⁻¹ := by group
          rwa [e] at this
        have h3 : a * k * a⁻¹ * k⁻¹ ∈ F ⊓ K := Subgroup.mem_inf.mpr ⟨h2, h1⟩
        rw [hFK, Subgroup.mem_bot] at h3
        calc a * k = (a * k * a⁻¹ * k⁻¹) * (k * a) := by group
          _ = k * a := by rw [h3, one_mul]
      have haK : a ∈ K := hCK' (Subgroup.mem_centralizer_iff.mpr (fun k hk => (hcomm k hk).symm))
      have : a ∈ F ⊓ K := Subgroup.mem_inf.mpr ⟨ha, haK⟩
      rw [hFK, Subgroup.mem_bot] at this
      exact this
    have hnontriv : ∃ a ∈ F, ∃ v : V, ρ a v ≠ v := by
      obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hFne)
      have hρa : ρ (a : G) ≠ 1 := fun h => ha1 (Subtype.ext (hρ (by simpa using h)))
      by_contra hall
      push Not at hall
      apply hρa
      ext v
      exact hall a a.2 v
    have hKN : K ≤ normalizer (F : Set G) := fun k _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact hFn.conj_mem h hh k
      · intro hh
        have := hFn.conj_mem _ hh k⁻¹
        simpa [mul_assoc] using this
    have hrank := hFR hV2 ρ F K hFcomm hFodd hKN hfpf hnontriv
    rw [hKcard, hVcard] at hrank
    have hle : 2 ^ n - 1 ≤ 2 * n + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hrank
    have hn3 : n = 3 := eq_three_of_two_pow_sub_one_le hn hle
    subst hn3
    have hFcard : ∃ a, 0 < a ∧ Nat.card F = p ^ a := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hFp
      refine ⟨a, ?_, ha⟩
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · exfalso
        rw [h0, pow_zero] at ha
        exact hFne (Subgroup.card_eq_one.mp ha)
      · exact h0
    obtain ⟨a, ha0, haF⟩ := hFcard
    let _ := CFSG.Walter.JT.conjAct K F hKN
    have hdvd : Nat.card K ∣ Nat.card F - 1 := by
      refine CFSG.Walter.W67.Sec56.card_dvd_card_sub_one_of_fpf (B := ↥K) (M := ↥F) 1
        (fun b => smul_one b) (fun b hb1 y hy => ?_)
      · have hy' : (b : G) * y * (b : G)⁻¹ = y := congrArg Subtype.val hy
        have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
        have := hfpf b b.2 hb1' y y.2 (by
          calc (b : G) * y = ((b : G) * y * (b : G)⁻¹) * b := by group
            _ = y * b := by rw [hy'])
        exact Subtype.ext this
    rw [hKcard, haF] at hdvd
    have h7' := h7 rfl p a hp ha0 (by rw [← haF]; exact Subgroup.card_subgroup_dvd_card F)
    have hpos : 0 < p ^ a := pow_pos hp.pos _
    have : p ^ a % 7 = 1 := by
      have h8 : (2 ^ 3 - 1 : ℕ) = 7 := by norm_num
      rw [h8] at hdvd
      omega
    exact h7' this
  ·
    have hFKne : Nat.card ↥(F ⊓ K) ≠ 1 := fun h => hFK (Subgroup.card_eq_one.mp h)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hFKne
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' q hqd
    set y : G := (y' : G) with hy
    have hyF : y ∈ F := (Subgroup.mem_inf.mp y'.2).1
    have hyK : y ∈ K := (Subgroup.mem_inf.mp y'.2).2
    have hyord : orderOf y = q := by rw [hy, Subgroup.orderOf_coe]; exact hy'
    have hyfix : ∀ v : V, ρ y v = v → v = 1 ∨ v = u := hCV y hyK (by rw [hyord]; exact hq)
    have hFu : ∀ f ∈ F, ρ f u = u := by
      intro f hf
      have hfy : f * y = y * f := hFcomm f hf y hyF
      have h1 : ρ y (ρ f u) = ρ f u := by
        calc ρ y (ρ f u) = ρ (y * f) u := (hom_mul_apply ρ y f u).symm
          _ = ρ (f * y) u := by rw [hfy]
          _ = ρ f (ρ y u) := hom_mul_apply ρ f y u
          _ = ρ f u := by rw [hKu y hyK]
      rcases hyfix _ h1 with h | h
      · exact absurd h (hρne f)
      · exact h
    have h2 : ρ y (ρ g u) = ρ g u := by
      have hg' : g⁻¹ * y * g ∈ F := by
        have := hFn.conj_mem y hyF g⁻¹
        simpa using this
      have e : y * g = g * (g⁻¹ * y * g) := by group
      calc ρ y (ρ g u) = ρ (y * g) u := (hom_mul_apply ρ y g u).symm
        _ = ρ (g * (g⁻¹ * y * g)) u := by rw [e]
        _ = ρ g (ρ (g⁻¹ * y * g) u) := hom_mul_apply ρ g _ u
        _ = ρ g u := by rw [hFu _ hg']
    rcases hyfix _ h2 with h | h
    · exact absurd h (hρne g)
    · exact h

end CFSG.GH74.Uniqueness
