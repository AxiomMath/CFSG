module

public import CFSG.Sporadic.Bridge.M11
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Sporadic.Bridge

section ThreeGroups

variable {G : Type*} [Group G]

theorem mem_zpowers_of_pow_three {b : G} (hb : b ^ 3 = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers b) : x = 1 ∨ x = b ∨ x = b * b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : b ^ (3 : ℤ) = 1 := by exact_mod_cast hb
  have hk : b ^ k = b ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3, zpow_add, zpow_mul]
    rw [h3, one_zpow, one_mul]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h3' : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h
  · left
    rw [hk, h]
    simp
  · right
    left
    rw [hk, h]
    simp
  · right
    right
    rw [hk, h]
    simp [sq]

theorem zpowers_inf_zpowers_eq_bot_of_three {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (h1 : a ≠ 1) (h2 : a * a ≠ 1) (h3 : b ≠ 1) (h4 : b * b ≠ 1) (h5 : a ≠ b)
    (h6 : a ≠ b * b) (h7 : a * a ≠ b) (h8 : a * a ≠ b * b) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hya, hyb⟩
  rcases mem_zpowers_of_pow_three ha hya with rfl | rfl | rfl <;>
    rcases mem_zpowers_of_pow_three hb hyb with h | h | h
  · exact Subgroup.one_mem _
  · exact absurd h.symm h3
  · exact absurd h.symm h4
  · exact absurd h h1
  · exact absurd h h5
  · exact absurd h h6
  · exact absurd h h2
  · exact absurd h h7
  · exact absurd h h8

theorem elemAbelian_sup_of_commute {a b : G} {p : ℕ} (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hab : a * b = b * a) :
    (∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b,
        x * y = y * x) ∧
      ∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, x ^ p = 1 := by
  have hab' : Commute a b := hab
  have hc : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hab'.zpow_zpow m n).eq
  have hmem : ∀ x : G, x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b ↔
      ∃ u ∈ Subgroup.zpowers a, ∃ v ∈ Subgroup.zpowers b, u * v = x := by
    intro x
    have hle : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
      intro u hu
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hc u hu v hv).symm
    have := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers a)
      (Subgroup.zpowers b) hle
    rw [← SetLike.mem_coe, this, Set.mem_mul]
    simp
  have hpowA : ∀ u ∈ Subgroup.zpowers a, u ^ p = 1 := by
    intro u hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have hpowB : ∀ v ∈ Subgroup.zpowers b, v ^ p = 1 := by
    intro v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  have hcomA : ∀ u u' : G, u ∈ Subgroup.zpowers a → u' ∈ Subgroup.zpowers a →
      u * u' = u' * u := by
    intro u u' hu hu'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    exact (Commute.zpow_zpow_self a m n).eq
  have hcomB : ∀ v v' : G, v ∈ Subgroup.zpowers b → v' ∈ Subgroup.zpowers b →
      v * v' = v' * v := by
    intro v v' hv hv'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    exact (Commute.zpow_zpow_self b m n).eq
  refine ⟨fun x hx y hy => ?_, ?_⟩
  · obtain ⟨u, hu, v, hv, rfl⟩ := (hmem x).mp hx
    obtain ⟨u', hu', v', hv', rfl⟩ := (hmem y).mp hy
    have c1 : Commute u u' := hcomA u u' hu hu'
    have c2 : Commute v v' := hcomB v v' hv hv'
    have c3 : Commute u v' := hc u hu v' hv'
    have c4 : Commute v u' := (hc u' hu' v hv).symm
    exact (((c1.mul_right c3).mul_left (c4.mul_right c2))).eq
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := (hmem x).mp hx
    have hcuv : Commute u v := hc u hu v hv
    rw [hcuv.mul_pow, hpowA u hu, hpowB v hv, one_mul]

theorem exists_elemAbelian_nine_of_commuting [Finite G] {a b : G} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : a * b = b * a) (h1 : a ≠ 1) (h2 : a * a ≠ 1) (h3 : b ≠ 1)
    (h4 : b * b ≠ 1) (h5 : a ≠ b) (h6 : a ≠ b * b) (h7 : a * a ≠ b) (h8 : a * a ≠ b * b) :
    ∃ E : Subgroup G, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      Nat.card E = 9 ∧ (∀ H : Subgroup G, a ∈ H → b ∈ H → E ≤ H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hab' : Commute a b := hab
  have hc : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hab'.zpow_zpow m n).eq
  obtain ⟨hcomm, hpow⟩ := elemAbelian_sup_of_commute ha hb hab
  refine ⟨Subgroup.zpowers a ⊔ Subgroup.zpowers b, hcomm, hpow, ?_,
    fun H haH hbH => sup_le (Subgroup.zpowers_le.mpr haH) (Subgroup.zpowers_le.mpr hbH)⟩
  rw [BenderBranch.card_sup_of_commute_of_inf_eq_bot hc
    (zpowers_inf_zpowers_eq_bot_of_three ha hb h1 h2 h3 h4 h5 h6 h7 h8),
    Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha h1, orderOf_eq_prime hb h3]

end ThreeGroups

section M11

private def wa : List (ℕ × Bool) :=
  [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true)]

private def wb : List (ℕ × Bool) :=
  [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
    (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
    (0, true), (1, false)]

private theorem wa_pow : wordProd CFSG.Sporadic.Bridge.M11.gen wa ^ 3 = 1 := by
  unfold wa
  decide +kernel

private theorem wb_pow : wordProd CFSG.Sporadic.Bridge.M11.gen wb ^ 3 = 1 := by
  unfold wb
  decide +kernel

private theorem wab_comm : wordProd CFSG.Sporadic.Bridge.M11.gen wa * wordProd CFSG.Sporadic.Bridge.M11.gen wb =
    wordProd CFSG.Sporadic.Bridge.M11.gen wb * wordProd CFSG.Sporadic.Bridge.M11.gen wa := by
  unfold wa wb
  decide +kernel

private theorem wab_ne : wordProd CFSG.Sporadic.Bridge.M11.gen wa ≠ 1 ∧ wordProd CFSG.Sporadic.Bridge.M11.gen wa * wordProd CFSG.Sporadic.Bridge.M11.gen wa ≠ 1 ∧
    wordProd CFSG.Sporadic.Bridge.M11.gen wb ≠ 1 ∧ wordProd CFSG.Sporadic.Bridge.M11.gen wb * wordProd CFSG.Sporadic.Bridge.M11.gen wb ≠ 1 ∧
    wordProd CFSG.Sporadic.Bridge.M11.gen wa ≠ wordProd CFSG.Sporadic.Bridge.M11.gen wb ∧
    wordProd CFSG.Sporadic.Bridge.M11.gen wa ≠ wordProd CFSG.Sporadic.Bridge.M11.gen wb * wordProd CFSG.Sporadic.Bridge.M11.gen wb ∧
    wordProd CFSG.Sporadic.Bridge.M11.gen wa * wordProd CFSG.Sporadic.Bridge.M11.gen wa ≠ wordProd CFSG.Sporadic.Bridge.M11.gen wb ∧
    wordProd CFSG.Sporadic.Bridge.M11.gen wa * wordProd CFSG.Sporadic.Bridge.M11.gen wa ≠ wordProd CFSG.Sporadic.Bridge.M11.gen wb * wordProd CFSG.Sporadic.Bridge.M11.gen wb := by
  unfold wa wb
  decide +kernel

theorem m11_exists_elemAbelian_nine :
    ∃ E : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11, CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := wab_ne
  obtain ⟨E₀, hcomm, hpow, hcard, hmin⟩ := exists_elemAbelian_nine_of_commuting wa_pow wb_pow
    wab_comm h1 h2 h3 h4 h5 h6 h7 h8
  have hle : E₀ ≤ CFSG.Blueprint.NativeSporadic.M11 :=
    hmin _ (CFSG.Sporadic.Bridge.M11.nativeWord_mem wa)
      (CFSG.Sporadic.Bridge.M11.nativeWord_mem wb)
  refine ⟨E₀.subgroupOf CFSG.Blueprint.NativeSporadic.M11, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩,
    ?_⟩
  · exact Subtype.ext (Subtype.ext (hcomm _ x.2 _ y.2))
  · apply Subtype.ext
    simpa using hpow _ hx
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem exists_elemAbelian_nine_of_iso
    {G : Type*} [Group G] {L : Subgroup G}
    (e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) :
    ∃ E : Subgroup G, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, hcard⟩ := m11_exists_elemAbelian_nine
  let f : ↥CFSG.Blueprint.NativeSporadic.M11 →* G :=
    L.subtype.comp (e.symm : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* ↥L).toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  refine ⟨E.map f, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  · exact CFSG.SectionRank.isElemAbelian_map hE f
  · rw [Subgroup.card_map_of_injective hf, hcard]

end M11

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem eq_one_of_central_of_iso_alt6 {G : Type*} [Group G] {K : Subgroup G}
    (φ : ↥K ≃* alternatingGroup (Fin 6)) {x : G} (hx : x ∈ K) (hc : ∀ w ∈ K, w * x = x * w) :
    x = 1 := by
  have hz : φ ⟨x, hx⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := hc (φ.symm g : K) (φ.symm g).2
    have h2 : (φ.symm g) * ⟨x, hx⟩ = ⟨x, hx⟩ * (φ.symm g) := Subtype.ext hg
    have h3 := congrArg φ h2
    simpa using h3
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz
  have : (⟨x, hx⟩ : K) = 1 := φ.injective (by rw [hz, map_one])
  exact congrArg Subtype.val this

end CFSG.QuasithinUnique.Unc25G2
