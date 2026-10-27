module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section Rank

variable {G : Type} [Group G] [Finite G]

theorem t112m_two_le_twoLocalRank {T : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) {u v : G}
    (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u)
    (hvu : v ∉ Subgroup.zpowers u) (huN : u ∈ Subgroup.normalizer (T : Set G))
    (hvN : v ∈ Subgroup.normalizer (T : Set G)) :
    2 ≤ GLATwoLocalRank 3 G := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ (Subgroup.zpowers u).one_mem)
  have hou : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hov : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hEl : ∀ w : G, w ^ 3 = 1 → IsElemAbelian 3 (Subgroup.zpowers w) := by
    intro w hw
    refine isElemAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self w i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  have hcomm : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers v, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (huv : Commute u v) i j).eq
  have hinf : Subgroup.zpowers u ⊓ Subgroup.zpowers v ≤ ⊥ := by
    intro y hy
    obtain ⟨hyu, hyv⟩ := Subgroup.mem_inf.1 hy
    by_contra hy1
    have hcard : Nat.card (Subgroup.zpowers v) = 3 := by rw [Nat.card_zpowers, hov]
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers v := Subgroup.zpowers_le.2 hyv
    have hy3 : orderOf y = 3 := by
      have hdvd : orderOf y ∣ 3 := by
        rw [← Nat.card_zpowers, ← hcard]
        exact Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) (by simpa using hy1)
      · exact h
    have heq : Subgroup.zpowers y = Subgroup.zpowers v :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hy3, hov])
    exact hvu (Subgroup.zpowers_le.2 hyu (heq ▸ Subgroup.mem_zpowers v))
  have hW : CFSG.Open.pRank 3 (⊥ : Subgroup G) ≤ 0 := by
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => ?_
    rw [le_bot_iff.1 hE, Subgroup.card_bot]
    norm_num
  obtain ⟨hEa, hEc⟩ := card_mul_le_card_sup_mul_pow hp (hEl u hu3) (hEl v hv3) hcomm hinf hW
  obtain ⟨e, he⟩ := exists_card_eq_of_isElemAbelian hp hEa
  rw [Nat.card_zpowers, Nat.card_zpowers, hou, hov, he, pow_zero, mul_one,
    show (3 : ℕ) * 3 = 3 ^ 2 by norm_num] at hEc
  have he2 : 2 ≤ e := (Nat.pow_le_pow_iff_right hp.one_lt).1 hEc
  have hEN : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ Subgroup.normalizer (T : Set G) :=
    sup_le (Subgroup.zpowers_le.2 huN) (Subgroup.zpowers_le.2 hvN)
  exact he2.trans (le_glaTwoLocalRank_of_le_normalizer hp.one_lt hT hT2 hEa hEN he)

end Rank

section Cover

variable {K : Type} [Group K] [Finite K]

theorem t112m_cover_twoLocal (hZ : Nat.card (Subgroup.center K) = 3)
    (hexp : ∀ R : Sylow 3 K, ∀ r ∈ (R : Subgroup K), r ^ 3 = 1)
    {V : Subgroup (K ⧸ Subgroup.center K)} (hV1 : V ≠ ⊥) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    {x : K ⧸ Subgroup.center K} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxV : x ∈ Subgroup.normalizer (V : Set (K ⧸ Subgroup.center K))) :
    2 ≤ GLATwoLocalRank 3 K := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hZexp : ∀ z ∈ Subgroup.center K, z ^ 3 = 1 := by
    intro z hz
    have : orderOf (⟨z, hz⟩ : Subgroup.center K) ∣ 3 := hZ ▸ orderOf_dvd_natCard _
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 this)
  have hπZ : ∀ g : K, π g = 1 ↔ g ∈ Subgroup.center K := fun g => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set W : Subgroup K := V.comap π with hWdef
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have hab := hV2 (a * b) (V.mul_mem ha hb)
    have ha2 := hV2 a ha
    have hb2 := hV2 b hb
    rw [pow_two] at hab ha2 hb2
    calc a * b = a * (a * b * (a * b)) * b := by rw [hab]; group
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [ha2, hb2]; group
  have hWsq : ∀ a ∈ W, a ^ 2 ∈ Subgroup.center K := by
    intro a ha
    rw [← hπZ, map_pow]
    exact hV2 _ ha
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    set c : K := a * b * a⁻¹ * b⁻¹ with hc
    have hcZ : c ∈ Subgroup.center K := by
      rw [← hπZ]
      simp only [hc, map_mul, map_inv]
      rw [hVc (π a) ha (π b) hb]
      group
    have hcc := Subgroup.mem_center_iff.1 hcZ
    have ha2Z := hWsq a ha
    rw [pow_two] at ha2Z
    have ha2c := Subgroup.mem_center_iff.1 ha2Z
    have hab : a * b = c * (b * a) := by rw [hc]; group
    have h1 : a * a * b = c * c * (b * (a * a)) := by
      calc a * a * b = a * (a * b) := by group
        _ = a * (c * (b * a)) := by rw [hab]
        _ = (a * c) * (b * a) := by group
        _ = (c * a) * (b * a) := by rw [hcc a]
        _ = c * ((a * b) * a) := by group
        _ = c * ((c * (b * a)) * a) := by rw [hab]
        _ = c * c * (b * (a * a)) := by group
    have h2 : a * a * b = b * (a * a) := (ha2c b).symm
    have hc2 : c * c = 1 := by
      have := h1.symm.trans h2
      calc c * c = c * c * (b * (a * a)) * (b * (a * a))⁻¹ := by group
        _ = 1 := by rw [this, mul_inv_cancel]
    have hc1 : c = 1 := by
      have hc3 := hZexp c hcZ
      rw [pow_three'] at hc3
      calc c = c * c * c * (c * c)⁻¹ := by group
        _ = 1 := by rw [hc3, hc2, inv_one, one_mul]
    calc a * b = c * (b * a) := hab
      _ = b * a := by rw [hc1, one_mul]
  let T : Subgroup K :=
    { carrier := {w | w ∈ W ∧ w ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨W.mul_mem ha.1 hb.1, ?_⟩
        rw [(Commute.mul_pow (hWc a ha.1 b hb.1 : Commute a b) 2), ha.2, hb.2, one_mul]
      one_mem' := ⟨W.one_mem, one_pow 2⟩
      inv_mem' := fun {a} ha => ⟨W.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hmemT : ∀ w, w ∈ T ↔ w ∈ W ∧ w ^ 2 = 1 := fun w => Iff.rfl
  have hT2 : IsPGroup 2 T := fun g => ⟨1, Subtype.ext (by simpa using ((hmemT g).1 g.2).2)⟩
  have hT1 : T ≠ ⊥ := by
    obtain ⟨⟨ā, hāV⟩, hā1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) ā
    have haW : a ∈ W := hāV
    have ha6 : (a ^ 3) ^ 2 = 1 := by
      rw [← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul]
      exact hZexp _ (hWsq a haW)
    have hta : a ^ 3 ∈ T := (hmemT _).2 ⟨W.pow_mem haW 3, ha6⟩
    intro hTb
    rw [hTb, Subgroup.mem_bot] at hta
    apply hā1
    have h1 : π (a ^ 3) = 1 := by rw [hta, map_one]
    have h2 : π a ^ 2 = 1 := hV2 _ hāV
    have h3 : π a = 1 := by
      calc π a = π a ^ 3 * (π a ^ 2)⁻¹ := by group
        _ = 1 := by rw [← map_pow, h1, h2, inv_one, one_mul]
    exact Subtype.ext h3
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) x
  have hv9 : v ^ 9 = 1 := by
    have h1 : v ^ 3 ∈ Subgroup.center K := by rw [← hπZ, map_pow]; exact hx3
    rw [show 9 = 3 * 3 by norm_num, pow_mul]
    exact hZexp _ h1
  have hv3 : v ^ 3 = 1 := by
    have hdvd : orderOf v ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hv9)
    obtain ⟨k, -, hkv⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hvp : IsPGroup 3 (Subgroup.zpowers v) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hkv])
    obtain ⟨R, hR⟩ := hvp.exists_le_sylow
    exact hexp R v (hR (Subgroup.mem_zpowers v))
  obtain ⟨⟨u, huZ⟩, hu1⟩ : ∃ u : Subgroup.center K, u ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton (Subgroup.center K) := ⟨fun a b => (h a).trans (h b).symm⟩
    have := Nat.card_unique (α := Subgroup.center K)
    omega
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huv : u * v = v * u := (Subgroup.mem_center_iff.1 huZ v).symm
  have hvu : v ∉ Subgroup.zpowers u := by
    intro hv
    apply hx1
    exact (hπZ v).2 (Subgroup.zpowers_le.2 huZ hv)
  have huN : u ∈ Subgroup.normalizer (T : Set K) := Subgroup.center_le_normalizer _ huZ
  have hvW : v ∈ Subgroup.normalizer (W : Set K) := Subgroup.le_normalizer_comap π hxV
  have hvN : v ∈ Subgroup.normalizer (T : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hmemT, hmemT, ← Subgroup.mem_normalizer_iff.1 hvW w, conj_pow]
    constructor
    · rintro ⟨hw, hw2⟩
      exact ⟨hw, by rw [hw2, mul_one, mul_inv_cancel]⟩
    · rintro ⟨hw, hw2⟩
      refine ⟨hw, ?_⟩
      have := congrArg (fun g => v⁻¹ * g * v) hw2
      simpa [mul_assoc] using this
  exact t112m_two_le_twoLocalRank hT1 hT2 hu1' (hZexp u huZ) hv3 huv hvu huN hvN

end Cover

end CFSG.HardMathSupport.Solomon.Coordinator
