module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Step1

variable {G : Type*} [Group G] [Finite G]

theorem Sp48NCent.mem_zpowers_of_ne_one {a y : G} (ha : orderOf a = 3)
    (hy : y ∈ Subgroup.zpowers a) (hy1 : y ≠ 1) : a ∈ Subgroup.zpowers y := by
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hy
  have hdvd : orderOf y ∣ 3 := ha ▸ orderOf_dvd_of_mem_zpowers hy
  have hy3 : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have heq : Subgroup.zpowers y = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, hy3])
  rw [heq]
  exact Subgroup.mem_zpowers a

omit [Finite G] in
theorem Sp48NCent.commute_of_mem_zpowers {g y w : G} (h : Commute g y)
    (hw : w ∈ Subgroup.zpowers y) : Commute g w := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact h.zpow_right n

omit [Finite G] in
theorem Sp48NCent.conj_mem_centerOf {R : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) (hz : z ∈ centerOf R) :
    g * z * g⁻¹ ∈ centerOf R := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
  show g * z * g⁻¹ ∈ Subgroup.centralizer (R : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hr' : g⁻¹ * r * g ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) r).mp hr
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hr'
  calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * r := by group

omit [Finite G] in
theorem Sp48NCent.commute_of_sq_commute {Q : Subgroup G} (hQ : IsPGroup 3 Q) {x b : G}
    (hx : x ∈ Q) (h : Commute (x ^ 2) b) : Commute x b := by
  obtain ⟨n, hn⟩ := hQ ⟨x, hx⟩
  have hxn : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨j, hj⟩ : ∃ j, 3 ^ n + 1 = 2 * j := by
    have hodd : Odd (3 ^ n) := Odd.pow (by decide)
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  have hxe : x = (x ^ 2) ^ j := by
    rw [← pow_mul, ← hj, pow_succ, hxn, one_mul]
  rw [hxe]
  exact h.pow_left j

omit [Finite G] in
theorem Sp48NCent.mul_not_mem_zpowers {a b : G} (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hbot : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    a * b ∉ Subgroup.zpowers a ∧ a * b ∉ Subgroup.zpowers b := by
  constructor
  · intro h
    have hb : b ∈ Subgroup.zpowers a := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) h
      simpa using this
    have : b ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := ⟨hb, Subgroup.mem_zpowers b⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hb1 this
  · intro h
    have ha : a ∈ Subgroup.zpowers b := by
      have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
      simpa using this
    have : a ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := ⟨Subgroup.mem_zpowers a, ha⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this

omit [Finite G] in
theorem Sp48NCent.eq_inv_of_mem_zpowers {b w : G} (hb : orderOf b = 3)
    (hw : w ∈ Subgroup.zpowers b) (hw1 : w ≠ 1) (hwb : w ≠ b) : w = b⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hk : b ^ k = b ^ (k % 3) := by
    have := (zpow_mod_orderOf b k).symm
    rwa [hb, Nat.cast_ofNat] at this
  have h3 : b ^ (3 : ℤ) = 1 := by
    have := pow_orderOf_eq_one b
    rw [hb] at this
    exact_mod_cast this
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h
  · exact absurd (by rw [hk, h, zpow_zero]) hw1
  · exact absurd (by rw [hk, h, zpow_one]) hwb
  · rw [hk, h]
    have : b ^ (2 : ℤ) * b = 1 := by rw [← zpow_add_one]; exact h3
    exact eq_inv_of_mul_eq_one_left this

theorem Sp48NCent.exists_outside_of_le_centralizer {R Q : Subgroup G} {a b σ : G}
    (hQ : IsPGroup 3 Q) (hRQ : R < Q) (hQN : Q ≤ Subgroup.normalizer (R : Set G))
    (ha : a ∈ centerOf R) (hb : b ∈ centerOf R) (hoa : orderOf a = 3) (hob : orderOf b = 3)
    (hbot : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥)
    (hσ : σ ∈ Subgroup.normalizer (R : Set G)) (hσa : σ * a * σ⁻¹ ∈ Subgroup.zpowers b)
    (hQa : Q ≤ Subgroup.centralizer ({a} : Set G)) :
    ∃ d ∈ centerOf R, d ∉ Subgroup.zpowers a ∧ d ∉ Subgroup.zpowers b ∧
      ∃ Y : Subgroup G, IsPGroup 3 Y ∧ R < Y ∧ Y ≤ Subgroup.normalizer (R : Set G) ∧
        Y ≤ Subgroup.centralizer ({d} : Set G) := by
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at hoa; omega
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hob; omega
  by_cases hQb : Q ≤ Subgroup.centralizer ({b} : Set G)
  · obtain ⟨h1, h2⟩ := Sp48NCent.mul_not_mem_zpowers ha1 hb1 hbot
    refine ⟨a * b, Subgroup.mul_mem _ ha hb, h1, h2, Q, hQ, hRQ, hQN, fun q hq => ?_⟩
    have hqa := Subgroup.mem_centralizer_singleton_iff.mp (hQa hq)
    have hqb := Subgroup.mem_centralizer_singleton_iff.mp (hQb hq)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc q * (a * b) = (q * a) * b := by group
      _ = (a * q) * b := by rw [hqa]
      _ = a * (q * b) := by group
      _ = a * (b * q) := by rw [hqb]
      _ = a * b * q := by group
  · obtain ⟨x, hxQ, hxb⟩ := Set.not_subset.mp hQb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hxb
    have hxa : Commute x a := Subgroup.mem_centralizer_singleton_iff.mp (hQa hxQ)
    set w := x * b * x⁻¹ with hw
    have hwZ : w ∈ centerOf R := Sp48NCent.conj_mem_centerOf (hQN hxQ) hb
    have hwa : w ∉ Subgroup.zpowers a := by
      intro h
      have hc := Sp48NCent.commute_of_mem_zpowers hxa h
      have hbw : b = w := by
        calc b = x⁻¹ * w * x := by rw [hw]; group
          _ = w := by rw [mul_assoc, ← hc.eq]; group
      have : b ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := ⟨hbw ▸ h, Subgroup.mem_zpowers b⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hb1 this
    have hwb : w ∉ Subgroup.zpowers b := by
      intro h
      have hw1 : w ≠ 1 := fun h1 => hb1 (by
        have h1' : x * b * x⁻¹ = 1 := h1
        calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
          _ = 1 := by rw [h1']; group)
      have hwb' : w ≠ b := fun h' => hxb (by
        have h'' : x * b * x⁻¹ = b := h'
        calc x * b = x * b * x⁻¹ * x := by group
          _ = b * x := by rw [h''])
      have hinv := Sp48NCent.eq_inv_of_mem_zpowers hob h hw1 hwb'
      have hsq : Commute (x ^ 2) b := by
        show x ^ 2 * b = b * x ^ 2
        have e1 : x * b = b⁻¹ * x := by
          calc x * b = (x * b * x⁻¹) * x := by group
            _ = b⁻¹ * x := by rw [← hw, hinv]
        have e2 : x * b⁻¹ = b * x := by
          have hinv' : x * b * x⁻¹ = b⁻¹ := hinv
          have e3 : x * b⁻¹ * x⁻¹ = b := by
            calc x * b⁻¹ * x⁻¹ = (x * b * x⁻¹)⁻¹ := by group
              _ = b := by rw [hinv', inv_inv]
          calc x * b⁻¹ = (x * b⁻¹ * x⁻¹) * x := by group
            _ = b * x := by rw [e3]
        calc x ^ 2 * b = x * (x * b) := by rw [sq, mul_assoc]
          _ = x * (b⁻¹ * x) := by rw [e1]
          _ = (x * b⁻¹) * x := by group
          _ = (b * x) * x := by rw [e2]
          _ = b * x ^ 2 := by rw [sq, mul_assoc]
      exact hxb (Sp48NCent.commute_of_sq_commute hQ hxQ hsq).eq
    have hg : x * σ ∈ Subgroup.normalizer (R : Set G) := Subgroup.mul_mem _ (hQN hxQ) hσ
    refine ⟨w, hwZ, hwa, hwb, Q.map (MulAut.conj (x * σ)).toMonoidHom, hQ.map _, ?_, ?_, ?_⟩
    · have hle : R ≤ Q.map (MulAut.conj (x * σ)).toMonoidHom := by
        intro r hr
        have hr' : (x * σ)⁻¹ * r * (x * σ) ∈ R := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) r).mp hr
          simpa using this
        refine ⟨(x * σ)⁻¹ * r * (x * σ), hRQ.le hr', ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      refine lt_of_le_of_ne hle fun heq => ?_
      have hc : Nat.card (Q.map (MulAut.conj (x * σ)).toMonoidHom) = Nat.card Q :=
        Subgroup.card_map_of_injective (MulAut.conj (x * σ)).injective
      have hlt := Subgroup.card_lt_of_lt hRQ
      rw [← heq] at hc
      omega
    · rintro _ ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hQN hq)) (Subgroup.inv_mem _ hg)
    · rintro _ ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hqa : q * a = a * q := Subgroup.mem_centralizer_singleton_iff.mp (hQa hq)
      have ha'1 : σ * a * σ⁻¹ ≠ 1 := fun h1 => ha1 (by
        calc a = σ⁻¹ * (σ * a * σ⁻¹) * σ := by group
          _ = 1 := by rw [h1]; group)
      have hba := Sp48NCent.mem_zpowers_of_ne_one hob hσa ha'1
      have hca : Commute (σ * q * σ⁻¹) (σ * a * σ⁻¹) := by
        show σ * q * σ⁻¹ * (σ * a * σ⁻¹) = σ * a * σ⁻¹ * (σ * q * σ⁻¹)
        calc σ * q * σ⁻¹ * (σ * a * σ⁻¹) = σ * (q * a) * σ⁻¹ := by group
          _ = σ * (a * q) * σ⁻¹ := by rw [hqa]
          _ = σ * a * σ⁻¹ * (σ * q * σ⁻¹) := by group
      have hcb : (σ * q * σ⁻¹) * b = b * (σ * q * σ⁻¹) :=
        (Sp48NCent.commute_of_mem_zpowers hca hba).eq
      calc x * σ * q * (x * σ)⁻¹ * w = x * ((σ * q * σ⁻¹) * b) * x⁻¹ := by rw [hw]; group
        _ = x * (b * (σ * q * σ⁻¹)) * x⁻¹ := by rw [hcb]
        _ = w * (x * σ * q * (x * σ)⁻¹) := by rw [hw]; group

theorem Sp48NCent.exists_centerOf_le_centralizer {R Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hRQ : R ≤ Q) (hQN : Q ≤ Subgroup.normalizer (R : Set G)) {z : G} (hz : z ∈ centerOf R)
    (hz1 : z ≠ 1) :
    ∃ z₀ ∈ centerOf R, z₀ ≠ 1 ∧ Q ≤ Subgroup.centralizer ({z₀} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent Q := hQ.isNilpotent
  have hn : ((centerOf R).subgroupOf Q).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using Sp48NCent.conj_mem_centerOf (hQN g.2) hn
  have hne : (centerOf R).subgroupOf Q ≠ ⊥ := by
    intro hbot
    have hzQ : z ∈ Q := hRQ hz.1
    have : (⟨z, hzQ⟩ : Q) ∈ (centerOf R).subgroupOf Q := Subgroup.mem_subgroupOf.mpr hz
    rw [hbot, Subgroup.mem_bot] at this
    exact hz1 (congrArg Subtype.val this)
  have hi := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨w, hwi⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hi
  obtain ⟨hwZ, hwC⟩ := hwi
  refine ⟨(w : G), Subgroup.mem_subgroupOf.mp hwZ, fun h => hw1 ?_, fun q hq => ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp hwC ⟨q, hq⟩
    simpa using congrArg Subtype.val this

theorem Sp48NCent.exists_outside_le_centralizer {R Q : Subgroup G} {z₁ z₂ σ : G}
    (hQ : IsPGroup 3 Q) (hRQ : R < Q) (hQN : Q ≤ Subgroup.normalizer (R : Set G))
    (hz₁ : z₁ ∈ centerOf R) (hz₂ : z₂ ∈ centerOf R) (ho₁ : orderOf z₁ = 3)
    (ho₂ : orderOf z₂ = 3) (hbot : Subgroup.zpowers z₁ ⊓ Subgroup.zpowers z₂ = ⊥)
    (hσ : σ ∈ Subgroup.normalizer (R : Set G)) (hσ₁ : σ * z₁ * σ⁻¹ ∈ Subgroup.zpowers z₂)
    (hσ₂ : σ * z₂ * σ⁻¹ ∈ Subgroup.zpowers z₁) :
    ∃ d ∈ centerOf R, d ∉ Subgroup.zpowers z₁ ∧ d ∉ Subgroup.zpowers z₂ ∧
      ∃ Y : Subgroup G, IsPGroup 3 Y ∧ R < Y ∧ Y ≤ Subgroup.normalizer (R : Set G) ∧
        Y ≤ Subgroup.centralizer ({d} : Set G) := by
  have h11 : z₁ ≠ 1 := fun h => by rw [h, orderOf_one] at ho₁; omega
  obtain ⟨z₀, hz₀, hz₀1, hQz₀⟩ := Sp48NCent.exists_centerOf_le_centralizer hQ hRQ.le hQN hz₁ h11
  have hcomm : ∀ {a : G}, orderOf a = 3 → z₀ ∈ Subgroup.zpowers a →
      Q ≤ Subgroup.centralizer ({a} : Set G) := by
    intro a ha hza q hq
    have hq0 : Commute q z₀ := Subgroup.mem_centralizer_singleton_iff.mp (hQz₀ hq)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Sp48NCent.commute_of_mem_zpowers hq0 (Sp48NCent.mem_zpowers_of_ne_one ha hza hz₀1)).eq
  by_cases h1 : z₀ ∈ Subgroup.zpowers z₁
  · exact Sp48NCent.exists_outside_of_le_centralizer hQ hRQ hQN hz₁ hz₂ ho₁ ho₂ hbot hσ hσ₁
      (hcomm ho₁ h1)
  by_cases h2 : z₀ ∈ Subgroup.zpowers z₂
  · obtain ⟨d, hd, hd2, hd1, hY⟩ := Sp48NCent.exists_outside_of_le_centralizer hQ hRQ hQN hz₂ hz₁
      ho₂ ho₁ (by rw [inf_comm]; exact hbot) hσ hσ₂ (hcomm ho₂ h2)
    exact ⟨d, hd, hd1, hd2, hY⟩
  exact ⟨z₀, hz₀, h1, h2, Q, hQ, hRQ, hQN, hQz₀⟩

end Step1

end CFSG.AGLEmbedding
