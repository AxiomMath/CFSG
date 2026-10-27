module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenHyp

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

@[expose] def mulSub (K M : Subgroup (MulAut V)) (hc : ∀ a ∈ K, ∀ b ∈ M, a * b = b * a) :
    Subgroup (MulAut V) where
  carrier := {x | ∃ k ∈ K, ∃ m ∈ M, x = k * m}
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, a', ha', rfl⟩ ⟨b, hb, b', hb', rfl⟩
    refine ⟨a * b, mul_mem ha hb, a' * b', mul_mem ha' hb', ?_⟩
    have : a' * b = b * a' := (hc b hb a' ha').symm
    calc a * a' * (b * b') = a * (a' * b) * b' := by group
      _ = a * (b * a') * b' := by rw [this]
      _ = a * b * (a' * b') := by group
  inv_mem' := by
    rintro _ ⟨a, ha, a', ha', rfl⟩
    refine ⟨a⁻¹, inv_mem ha, a'⁻¹, inv_mem ha', ?_⟩
    have : a' * a = a * a' := (hc a ha a' ha').symm
    calc (a * a')⁻¹ = a'⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * a'⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, this]

theorem le_mulSub_left {K M : Subgroup (MulAut V)} {hc : ∀ a ∈ K, ∀ b ∈ M, a * b = b * a} :
    K ≤ mulSub K M hc := fun k hk => ⟨k, hk, 1, one_mem _, by simp⟩

theorem le_mulSub_right {K M : Subgroup (MulAut V)} {hc : ∀ a ∈ K, ∀ b ∈ M, a * b = b * a} :
    M ≤ mulSub K M hc := fun m hm => ⟨1, one_mem _, m, hm, by simp⟩

theorem mulSub_le {K M E : Subgroup (MulAut V)} {hc : ∀ a ∈ K, ∀ b ∈ M, a * b = b * a}
    (hK : K ≤ E) (hM : M ≤ E) : mulSub K M hc ≤ E := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mul_mem (hK ha) (hM hb)

theorem card_mulSub [Finite V] {K M : Subgroup (MulAut V)}
    {hc : ∀ a ∈ K, ∀ b ∈ M, a * b = b * a} (hd : K ⊓ M = ⊥) :
    Nat.card (mulSub K M hc) = Nat.card K * Nat.card M := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun km : ↥K × ↥M => (⟨(km.1 : MulAut V) * km.2, km.1, km.1.2, km.2, km.2.2, rfl⟩ :
      ↥(mulSub K M hc))) ⟨?_, ?_⟩)).symm
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    have h1 : (k : MulAut V) * m = k' * m' := congrArg Subtype.val h
    obtain ⟨a, ha⟩ := k
    obtain ⟨a', ha'⟩ := k'
    obtain ⟨b, hb⟩ := m
    obtain ⟨b', hb'⟩ := m'
    simp only at h1
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have h3 : a'⁻¹ * a ∈ K ⊓ M :=
      ⟨K.mul_mem (K.inv_mem ha') ha, h2 ▸ M.mul_mem hb' (M.inv_mem hb)⟩
    rw [hd, Subgroup.mem_bot, inv_mul_eq_one] at h3
    subst h3
    have : b = b' := mul_left_cancel h1
    subst this
    rfl
  · rintro ⟨_, k, hk, m, hm, rfl⟩
    exact ⟨(⟨k, hk⟩, ⟨m, hm⟩), rfl⟩

theorem card_mulSub_zpowers [Finite V] {K : Subgroup (MulAut V)} {g : MulAut V} {p : ℕ}
    (hp : p.Prime) (hg : g ^ p = 1) (hgK : g ∉ K)
    (hc : ∀ a ∈ K, ∀ b ∈ Subgroup.zpowers g, a * b = b * a) :
    Nat.card (mulSub K (Subgroup.zpowers g) hc) = p * Nat.card K := by
  have : Fact p.Prime := ⟨hp⟩
  have hg1 : g ≠ 1 := fun h => hgK (h ▸ one_mem K)
  have hord : orderOf g = p := orderOf_eq_prime hg hg1
  have hz : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hord]
  have hd : K ⊓ Subgroup.zpowers g = ⊥ := by
    have h1 : Nat.card ↥(K ⊓ Subgroup.zpowers g) ∣ p := by
      rw [← hz]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have h2 : K ⊓ Subgroup.zpowers g = Subgroup.zpowers g :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hz])
      have h3 : g ∈ K ⊓ Subgroup.zpowers g := by rw [h2]; exact Subgroup.mem_zpowers g
      exact hgK h3.1
  rw [card_mulSub hd, hz, mul_comm]

section RankTwo

theorem rank_two_identity {p : ℕ} [Fact p.Prime] (hp : Odd p) (hV : ∀ v : V, v ^ 2 = 1)
    (a b : MulAut V) (hab : a * b = b * a) (ha : a ^ p = 1) (w : V) :
    (∏ i : ZMod p, (a ^ i.val) w) * ∏ c : ZMod p, ∏ k : ZMod p, ((a ^ c.val * b) ^ k.val) w =
      w * ∏ j : ZMod p, ∏ i : ZMod p, (a ^ i.val * b ^ j.val) w := by
  classical
  have hcomm : Commute a b := hab
  have hpow : ∀ c k : ZMod p, (a ^ c.val * b) ^ k.val = a ^ (c * k).val * b ^ k.val := by
    intro c k
    rw [(hcomm.pow_left c.val).mul_pow, ← pow_mul, ZMod.val_mul, pow_eq_pow_mod (c.val * k.val) ha]
  simp only [hpow]
  rw [Finset.prod_comm]
  have hk0 : ∏ c : ZMod p, (a ^ (c * 0).val * b ^ (0 : ZMod p).val) w = w := by
    simp only [mul_zero, ZMod.val_zero, pow_zero, mul_one, MulAut.one_apply, Finset.prod_const,
      Finset.card_univ, ZMod.card]
    exact pow_odd_eq_self hV w hp
  have hkne : ∀ k : ZMod p, k ≠ 0 → ∏ c : ZMod p, (a ^ (c * k).val * b ^ k.val) w =
      ∏ i : ZMod p, (a ^ i.val * b ^ k.val) w := fun k hk =>
    Fintype.prod_equiv (Equiv.mulRight₀ k hk) _ _ fun c => rfl
  have h2 : ∏ k ∈ Finset.univ.erase (0 : ZMod p), ∏ c : ZMod p, (a ^ (c * k).val * b ^ k.val) w =
      ∏ k ∈ Finset.univ.erase (0 : ZMod p), ∏ i : ZMod p, (a ^ i.val * b ^ k.val) w :=
    Finset.prod_congr rfl fun k hk => hkne k (Finset.ne_of_mem_erase hk)
  have hL : ∏ k : ZMod p, ∏ c : ZMod p, (a ^ (c * k).val * b ^ k.val) w =
      w * ∏ k ∈ Finset.univ.erase (0 : ZMod p), ∏ i : ZMod p, (a ^ i.val * b ^ k.val) w := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k : ZMod p => ∏ c : ZMod p, (a ^ (c * k).val * b ^ k.val) w) (Finset.mem_univ 0), hk0,
      h2]
  have hR : ∏ j : ZMod p, ∏ i : ZMod p, (a ^ i.val * b ^ j.val) w =
      (∏ i : ZMod p, (a ^ i.val) w) *
        ∏ k ∈ Finset.univ.erase (0 : ZMod p), ∏ i : ZMod p, (a ^ i.val * b ^ k.val) w := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j : ZMod p => ∏ i : ZMod p, (a ^ i.val * b ^ j.val) w) (Finset.mem_univ 0)]
    simp only [ZMod.val_zero, pow_zero, mul_one]
  rw [hL, hR]
  ac_rfl

end RankTwo

section Cyc

@[expose] def cyc (p : ℕ) [NeZero p] (g : MulAut V) (u : V) : V := ∏ i : ZMod p, (g ^ i.val) u

theorem cyc_apply (p : ℕ) [NeZero p] (g : MulAut V) (u : V) :
    cyc p g u = ∏ i : ZMod p, (g ^ i.val) u := rfl

theorem pow_val_natCast {p : ℕ} [NeZero p] {g : MulAut V} (hg : g ^ p = 1) (n : ℕ) :
    g ^ (n : ZMod p).val = g ^ n := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hg]

theorem apply_cyc {p : ℕ} [NeZero p] {g : MulAut V} (hg : g ^ p = 1) (u : V) :
    g (cyc p g u) = cyc p g u := by
  rw [cyc_apply, map_prod]
  refine Fintype.prod_equiv (Equiv.addRight (1 : ZMod p)) _ _ fun i => ?_
  show g ((g ^ i.val) u) = (g ^ (i + 1 : ZMod p).val) u
  have h1 : (i + 1 : ZMod p) = ((i.val + 1 : ℕ) : ZMod p) := by simp
  rw [h1, pow_val_natCast hg, pow_succ']
  rfl

theorem apply_cyc_of_comm {p : ℕ} [NeZero p] {g x : MulAut V} (hxg : x * g = g * x) {u : V}
    (hu : x u = u) : x (cyc p g u) = cyc p g u := by
  rw [cyc_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : x * g ^ i.val = g ^ i.val * x :=
    (Commute.pow_right (show Commute x g from hxg) _).eq
  show (x * g ^ i.val) u = (g ^ i.val) u
  rw [h1]
  show (g ^ i.val) (x u) = (g ^ i.val) u
  rw [hu]

theorem normK_cyc (p : ℕ) [NeZero p] (E : Subgroup (MulAut V)) [Fintype ↥E] {g : MulAut V}
    (hg : g ∈ E) {u : V} (hu : normK E u = 1) : normK E (cyc p g u) = 1 := by
  rw [cyc_apply, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  exact (normK_apply_mem E (pow_mem hg _) u).trans hu

theorem prod_prod_eq_cyc_cyc (p : ℕ) [NeZero p] {a b : MulAut V} (hab : a * b = b * a) (w : V) :
    ∏ j : ZMod p, ∏ i : ZMod p, (a ^ i.val * b ^ j.val) w = cyc p b (cyc p a w) := by
  rw [cyc_apply, cyc_apply]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : a ^ i.val * b ^ j.val = b ^ j.val * a ^ i.val :=
    (Commute.pow_pow (show Commute a b from hab) _ _).eq
  rw [this]
  rfl

end Cyc

section Exists

theorem mem_fixV_sup_zpowers {H : Subgroup (MulAut V)} {g : MulAut V} {u : V}
    (hH : u ∈ fixV H) (hg : g u = u) : u ∈ fixV (H ⊔ Subgroup.zpowers g) := by
  have hle : H ⊔ Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut V) u := by
    refine sup_le (fun h hh => ?_) (Subgroup.zpowers_le.mpr ?_)
    · simpa [MulAction.mem_stabilizer_iff] using hH h hh
    · simpa [MulAction.mem_stabilizer_iff] using hg
  intro x hx
  simpa [MulAction.mem_stabilizer_iff] using hle hx

theorem fixV_bot : fixV (⊥ : Subgroup (MulAut V)) = ⊤ :=
  eq_top_iff.mpr fun v _ x hx => by rw [Subgroup.mem_bot.mp hx]; rfl

theorem ker_normK_ne_bot (hV : ∀ v : V, v ^ 2 = 1) (E : Subgroup (MulAut V)) [Fintype ↥E]
    (hoddE : Odd (Fintype.card ↥E)) (hE : E ≠ ⊥) : (normK E).ker ≠ ⊥ := by
  intro h
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have hv : ∃ v : V, (a : MulAut V) v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact ha (Subtype.ext (MulEquiv.ext hcon))
  obtain ⟨v, hv⟩ := hv
  have hsup := normK_ker_sup_fixV E hoddE hV
  rw [h, bot_sup_eq] at hsup
  exact hv (by
    have : v ∈ fixV E := by rw [hsup]; exact Subgroup.mem_top v
    exact this a a.2)

theorem exists_hyperplane_hypPart_ne_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (E : Subgroup (MulAut V)) [Fintype ↥E] (hoddE : Odd (Fintype.card ↥E)) {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ e ∈ E, e ^ p = 1) (hE : E ≠ ⊥) :
    ∃ H ≤ E, Nat.card E = p * Nat.card H ∧ hypPart E H ≠ ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let P : ℕ → Prop := fun n =>
    ∃ L : Subgroup (MulAut V), L ≤ E ∧ hypPart E L ≠ ⊥ ∧ Nat.card L = n
  have hbot_ne : hypPart E ⊥ ≠ ⊥ := by
    have : hypPart E ⊥ = (normK E).ker := by
      rw [hypPart, fixV_bot, top_inf_eq]
    rw [this]
    exact ker_normK_ne_bot hV E hoddE hE
  have hP1 : P 1 := ⟨⊥, bot_le, hbot_ne, Subgroup.card_bot⟩
  have hpos : 1 ≤ Nat.card E := Nat.card_pos
  obtain ⟨H, hHE, hHne, hHcard⟩ := Nat.findGreatest_spec (P := P) hpos hP1
  have hmax : ∀ L : Subgroup (MulAut V), H < L → L ≤ E → hypPart E L = ⊥ := by
    intro L hHL hLE
    by_contra hne
    have h1 : Nat.card H ≤ Nat.card L := Subgroup.card_le_of_le hHL.le
    have h2 : Nat.card H ≠ Nat.card L := fun h =>
      hHL.ne (Subgroup.eq_of_le_of_card_ge hHL.le (by rw [h]))
    have := Nat.le_findGreatest (P := P) (Subgroup.card_le_of_le hLE) ⟨L, hLE, hne, rfl⟩
    omega
  refine ⟨H, hHE, ?_, hHne⟩
  by_contra hcard
  have hEbot : hypPart E E = ⊥ := by
    rw [hypPart, inf_comm]
    exact normK_ker_inf_fixV E hoddE hV
  have hHE' : H ≠ E := fun h => hHne (h ▸ hEbot)
  have key : ∀ g ∈ E, g ∉ H → ∀ u : V, normK E u = 1 → (∀ h ∈ H, h u = u) → g u = u →
      u = 1 := by
    intro g hgE hgH u hu hHu hgu
    have hlt : H < H ⊔ Subgroup.zpowers g := lt_of_le_of_ne le_sup_left fun h =>
      hgH (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
    have hle : H ⊔ Subgroup.zpowers g ≤ E := sup_le hHE (Subgroup.zpowers_le.mpr hgE)
    have hmem : u ∈ hypPart E (H ⊔ Subgroup.zpowers g) :=
      ⟨mem_fixV_sup_zpowers hHu hgu, hu⟩
    rw [hmax _ hlt hle] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨a, haE, haH⟩ : ∃ a ∈ E, a ∉ H := by
    by_contra h
    push Not at h
    exact hHE' (le_antisymm hHE h)
  have hap : a ^ p = 1 := hexp a haE
  have hcomm_a : ∀ x ∈ H, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_right (show Commute x a from hcomm x (hHE hx) a haE) k)).eq
  have hH₁ : H ⊔ Subgroup.zpowers a = mulSub H (Subgroup.zpowers a) hcomm_a :=
    le_antisymm (sup_le le_mulSub_left le_mulSub_right) (mulSub_le le_sup_left le_sup_right)
  have hH₁card : Nat.card ↥(H ⊔ Subgroup.zpowers a) = p * Nat.card H := by
    rw [hH₁]
    exact card_mulSub_zpowers hp hap haH hcomm_a
  have hH₁E : H ⊔ Subgroup.zpowers a ≤ E := sup_le hHE (Subgroup.zpowers_le.mpr haE)
  have hH₁ne : H ⊔ Subgroup.zpowers a ≠ E := fun h => hcard (by rw [← h]; exact hH₁card)
  obtain ⟨b, hbE, hbH₁⟩ : ∃ b ∈ E, b ∉ H ⊔ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    exact hH₁ne (le_antisymm hH₁E h)
  have hbp : b ^ p = 1 := hexp b hbE
  have hab : a * b = b * a := hcomm a haE b hbE
  have hall : ∀ w ∈ hypPart E H, w = 1 := by
    intro w hw
    have hw1 : ∀ h ∈ H, h w = w := hw.1
    have hwn : normK E w = 1 := hw.2
    have hcommH : ∀ g ∈ E, ∀ h ∈ H, h * g = g * h := fun g hg h hh => hcomm h (hHE hh) g hg
    have hA : cyc p a w = 1 :=
      key a haE haH _ (normK_cyc p E haE hwn)
        (fun h hh => apply_cyc_of_comm (hcommH a haE h hh) (hw1 h hh)) (apply_cyc hap w)
    have hB : ∀ c : ZMod p, cyc p (a ^ c.val * b) w = 1 := by
      intro c
      have hgE : a ^ c.val * b ∈ E := mul_mem (pow_mem haE _) hbE
      have hgH : a ^ c.val * b ∉ H := by
        intro hg
        apply hbH₁
        have h1 : b = (a ^ c.val)⁻¹ * (a ^ c.val * b) := by group
        rw [h1]
        exact mul_mem (inv_mem (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers a) _)))
          (Subgroup.mem_sup_left hg)
      have hgp : (a ^ c.val * b) ^ p = 1 := by
        rw [(Commute.pow_left (show Commute a b from hab) c.val).mul_pow, ← pow_mul, mul_comm,
          pow_mul, hap, one_pow, hbp, one_mul]
      exact key _ hgE hgH _ (normK_cyc p E hgE hwn)
        (fun h hh => apply_cyc_of_comm (hcommH _ hgE h hh) (hw1 h hh)) (apply_cyc hgp w)
    have hid := rank_two_identity hpodd hV a b hab hap w
    have h1 : (∏ i : ZMod p, (a ^ i.val) w) = 1 := hA
    have h2 : ∏ c : ZMod p, ∏ k : ZMod p, ((a ^ c.val * b) ^ k.val) w = 1 :=
      Finset.prod_eq_one fun c _ => hB c
    have h3 : ∏ j : ZMod p, ∏ i : ZMod p, (a ^ i.val * b ^ j.val) w = 1 := by
      rw [prod_prod_eq_cyc_cyc p hab w, hA]
      simp [cyc_apply]
    rw [h1, h2, h3, one_mul, mul_one] at hid
    exact hid.symm
  exact hHne (eq_bot_iff.mpr fun w hw => Subgroup.mem_bot.mpr (hall w hw))

end Exists

end CFSG.CGT.PushingUpLit.CGT6
