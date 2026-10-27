module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Int

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

section Sylow

theorem exists_conj_of_isSylowOf {P P' K : Subgroup G} (h : IsSylowOf 2 P K)
    (h' : IsSylowOf 2 P' K) : ∃ z ∈ K, cs z P' = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq_subgroupOf
  obtain ⟨Q', hQ'⟩ := h'.exists_sylow_eq_subgroupOf
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq K Q' Q
  refine ⟨z, z.2, ?_⟩
  have key : ∀ y : K,
      y ∈ ((z • Q' : Sylow 2 K) : Subgroup K) ↔ z⁻¹ * y * z ∈ (Q' : Subgroup K) := by
    intro y
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  rw [hz] at key
  ext x
  rw [mem_cs]
  constructor
  · intro hx
    have hxK : x ∈ K := by
      have h1 : z * (z⁻¹ * x * z) * z⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem z.2 (h'.le hx)) (K.inv_mem z.2)
      simpa [mul_assoc] using h1
    have h2 : z⁻¹ * (⟨x, hxK⟩ : K) * z ∈ (Q' : Subgroup K) := by
      rw [hQ']
      exact hx
    have h3 := (key ⟨x, hxK⟩).2 h2
    rw [hQ] at h3
    exact h3
  · intro hx
    have hxK : x ∈ K := h.le hx
    have h2 : (⟨x, hxK⟩ : K) ∈ (Q : Subgroup K) := by
      rw [hQ]
      exact hx
    have h3 := (key ⟨x, hxK⟩).1 h2
    rw [hQ'] at h3
    exact h3

theorem isSylowOf_two_of_card {X K : Subgroup G} {n j : ℕ} (hj : ¬ 2 ∣ j)
    (hK : Nat.card K = 2 ^ n * j) (hXK : X ≤ K) (hX : Nat.card X = 2 ^ n) : IsSylowOf 2 X K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨hXK, IsPGroup.of_card hX, ?_⟩
  have h := Subgroup.relIndex_mul_card X K
  rw [inf_eq_left.mpr hXK, hX, hK] at h
  have h2 : X.relIndex K = j := by
    have hpos : 0 < 2 ^ n := by positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  rw [h2]
  exact hj

end Sylow

section Order

omit [Finite G] in
theorem card_sup_dvd {G₁ G₂ : Subgroup G} (h : ⁅G₁, G₂⁆ = ⊥) :
    Nat.card ↥(G₁ ⊔ G₂) ∣ Nat.card G₁ * Nat.card G₂ := by
  have hc : ∀ (a : ↥G₁) (b : ↥G₂), Commute (G₁.subtype a) (G₂.subtype b) := by
    intro a b
    have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h) a.2
    exact (mem_centralizer_iff.1 h1 b.1 b.2).symm
  have hr : (G₁.subtype.noncommCoprod G₂.subtype hc).range = G₁ ⊔ G₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have := Subgroup.card_range_dvd (G₁.subtype.noncommCoprod G₂.subtype hc)
  rwa [hr, Nat.card_prod] at this

variable {A : Subgroup G} {d : Datum A} {G₁ G₂ S₀ W₁ W₂ : Subgroup G}

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.odd_center (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) :
    Odd (Nat.card (center ↥G₁)) := by
  have hle : (center ↥G₁).map G₁.subtype ≤ centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hyc : G₁ ⊔ G₂ ≤ centralizer ({(z : G)} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_center_iff.1 hz ⟨x, hx⟩)
      · rw [mem_centralizer_singleton_iff]
        have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 c.comm) z.2
        exact mem_centralizer_iff.1 h1 x hx
    exact mem_centralizer_singleton_iff.1 (hyc hy)
  have h1 : Nat.card ((center ↥G₁).map G₁.subtype) = Nat.card (center ↥G₁) :=
    Subgroup.card_map_of_injective G₁.subtype_injective
  have h2 := Subgroup.card_dvd_of_le hle
  rw [h1] at h2
  exact c.odd_centralizer.of_dvd_nat h2

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.card_G₁ (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) :
    ∃ m, Odd m ∧ Nat.card G₁ = 2 ^ 6 * m := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥G₁)
  rw [card_of_lieModel_psl_three_four c.model] at h1
  refine ⟨315 * Nat.card (center ↥G₁), (by decide : Odd 315).mul c.odd_center, ?_⟩
  rw [h1]
  ring

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.card_G₂ (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) :
    Nat.card G₂ = Nat.card G₁ := by
  rw [c.compData.G₂_eq, nat_card_cs]

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.card_G₀ (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) :
    ∃ j, ¬ 2 ∣ j ∧ Nat.card ↥(G₁ ⊔ G₂) = 2 ^ 12 * j := by
  obtain ⟨m, hm, h1⟩ := c.card_G₁
  have hdvd : Nat.card ↥(G₁ ⊔ G₂) ∣ Nat.card G₁ * Nat.card G₂ := card_sup_dvd c.comm
  rw [c.card_G₂, h1] at hdvd
  have h2 : 2 ^ 12 ∣ Nat.card ↥(G₁ ⊔ G₂) := by
    have := Subgroup.card_dvd_of_le c.S₀_le
    rwa [c.card_S₀] at this
  obtain ⟨j, hj⟩ := h2
  refine ⟨j, ?_, hj⟩
  have hjm : j ∣ m * m := by
    have e : 2 ^ 6 * m * (2 ^ 6 * m) = 2 ^ 12 * (m * m) := by ring
    rw [hj, e] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd
  intro h2j
  have := (Nat.Prime.dvd_mul Nat.prime_two).1 (h2j.trans hjm)
  have hm' := Nat.odd_iff.1 hm
  rcases this with h | h <;> omega

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.isSylowOf_S₀ (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) :
    IsSylowOf 2 S₀ (G₁ ⊔ G₂) := by
  obtain ⟨j, hj, hcard⟩ := c.card_G₀
  exact isSylowOf_two_of_card hj hcard c.S₀_le c.card_S₀

end Order

section U1

variable {A : Subgroup G} {d : Datum A} {G₁ G₂ S₀ W₁ W₂ : Subgroup G}

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.loc_conj (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) {g : G}
    (hS : S₀ ≤ cs g (G₁ ⊔ G₂)) {W : Subgroup G} (hWS : W ≤ S₀) (hWe : IsElemAbelian 2 W)
    (hWc : Nat.card W = 2 ^ 8) :
    S₀ ≤ perfectResidualOf (normalizer (W : Set G) ⊓ cs g (G₁ ⊔ G₂)) := by
  obtain ⟨j, hj, hcard⟩ := c.card_G₀
  have hS' : cs g⁻¹ S₀ ≤ G₁ ⊔ G₂ := by
    intro y hy
    rw [mem_cs] at hy
    have := hS hy
    rw [mem_cs] at this
    simpa [mul_assoc] using this
  have hsyl' : IsSylowOf 2 (cs g⁻¹ S₀) (G₁ ⊔ G₂) :=
    isSylowOf_two_of_card hj hcard hS' (by rw [nat_card_cs, c.card_S₀])
  obtain ⟨z, hz, hzS⟩ := exists_conj_of_isSylowOf c.isSylowOf_S₀ hsyl'
  have hx : cs (z * g⁻¹) S₀ = S₀ := by rw [cs_mul]; exact hzS
  have hxinv : cs (z * g⁻¹)⁻¹ S₀ = S₀ := by
    conv_lhs => rw [← hx]
    exact cs_inv_cs _ _
  have hWx : cs (z * g⁻¹) W ≤ S₀ := by
    have := cs_mono (z * g⁻¹) hWS
    rwa [hx] at this
  have hl := c.loc (cs (z * g⁻¹) W) hWx (isElemAbelian_cs _ hWe)
    (by rw [nat_card_cs, hWc])
  have h2 := cs_mono (z * g⁻¹)⁻¹ hl
  rw [hxinv, ← perfectResidualOf_cs, cs_inf, cs_normalizer, cs_inv_cs] at h2
  have hG : cs (z * g⁻¹)⁻¹ (G₁ ⊔ G₂) = cs g (G₁ ⊔ G₂) := by
    rw [mul_inv_rev, inv_inv, cs_mul, cs_self_of_mem (inv_mem hz)]
  rwa [hG] at h2

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.u1 (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) {g : G}
    (hS : S₀ ≤ cs g (G₁ ⊔ G₂)) : cs g (G₁ ⊔ G₂) = G₁ ⊔ G₂ := by
  have key : ∀ W : Subgroup G, W ≤ S₀ → IsElemAbelian 2 W → Nat.card W = 2 ^ 8 →
      (∀ Q : Subgroup G, Q ≤ perfectResidualOf (normalizer (W : Set G)) → ⁅Q, Q⁆ = Q →
        S₀ ≤ Q → Q = perfectResidualOf (normalizer (W : Set G))) →
      perfectResidualOf (normalizer (W : Set G)) ≤ cs g (G₁ ⊔ G₂) := by
    intro W hWS hWe hWc hq
    have hK1 : perfectResidualOf (normalizer (W : Set G) ⊓ cs g (G₁ ⊔ G₂)) ≤
        perfectResidualOf (normalizer (W : Set G)) := perfectResidualOf_mono inf_le_left
    have hK := hq _ hK1 (perfectResidualOf_perfect _) (c.loc_conj hS hWS hWe hWc)
    rw [← hK]
    exact (perfectResidualOf_le' _).trans inf_le_right
  have h1 := key W₁ c.W₁_le c.W₁_elem c.card_W₁ c.qmax₁
  have h2 := key W₂ c.W₂_le c.W₂_elem c.card_W₂ c.qmax₂
  have hG₀ : G₁ ⊔ G₂ ≤ cs g (G₁ ⊔ G₂) :=
    calc G₁ ⊔ G₂ = perfectResidualOf (normalizer (W₁ : Set G)) ⊔
          perfectResidualOf (normalizer (W₂ : Set G)) := c.G₀_eq
      _ ≤ cs g (G₁ ⊔ G₂) := sup_le h1 h2
  exact (Subgroup.eq_of_le_of_card_ge hG₀ (by rw [nat_card_cs])).symm

end U1

section OddIndex

variable {A : Subgroup G} {d : Datum A} {G₁ G₂ S₀ W₁ W₂ : Subgroup G} {Q : Type} [Group Q]
  [Finite Q] {MD : ModelData Q}

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.le_normalizer_of_sylow
    (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) (E : EmbSpec c.compData MD) (T : Sylow 2 G)
    (hST : S₀ ≤ (T : Subgroup G)) :
    (T : Subgroup G) ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
  classical
  by_contra hnot
  set Tsub : Subgroup G := (T : Subgroup G) with hTsub
  set R : Subgroup G := Tsub ⊓ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) with hR
  have hRT : R ≤ Tsub := inf_le_left
  have hlt : R.subgroupOf Tsub < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hnot fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Tsub) ∈ R.subgroupOf Tsub := by
      rw [htop]
      trivial
    exact (mem_subgroupOf.mp hx').2
  have : Group.IsNilpotent Tsub := T.isPGroup'.isNilpotent
  have hnc : NormalizerCondition Tsub := Group.normalizerCondition_of_isNilpotent (G := Tsub)
  obtain ⟨y, hyN, hyn⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  have hy : (y : G) ∈ normalizer (R : Set G) := by
    have hxsub : y ∈ (normalizer (R : Set G)).subgroupOf Tsub := by
      rw [subgroupOf_normalizer_eq hRT]
      exact hyN
    exact mem_subgroupOf.mp hxsub
  have hyR : (y : G) ∉ R := fun h => hyn (mem_subgroupOf.mpr h)
  apply hyR
  refine ⟨y.2, ?_⟩
  have hRp : IsPGroup 2 R := T.isPGroup'.to_inf_left
  have hRN : R ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := inf_le_right
  have hSR : S₀ ≤ R := fun s hs => ⟨hST hs, Subgroup.le_normalizer (c.S₀_le hs)⟩
  have hcsR : cs (y : G) R = R := mem_normalizer_iff_cs.1 hy
  have hW : ∀ W : Subgroup G, W ≤ S₀ → IsElemAbelian 2 W → Nat.card W = 2 ^ 8 →
      cs (y : G) W ≤ S₀ := by
    intro W hWS hWe hWc
    have h1 : cs (y : G) W ≤ R := by
      have := cs_mono (y : G) (hWS.trans hSR)
      rwa [hcsR] at this
    exact E.elem_le c.odd_centralizer hRp hRN hSR c.S₀_le c.card_S₀ h1 (isElemAbelian_cs _ hWe)
      (by rw [nat_card_cs, hWc])
  have hcsS : cs (y : G) S₀ = S₀ := by
    have hle : cs (y : G) S₀ ≤ S₀ :=
      calc cs (y : G) S₀ = cs (y : G) W₁ ⊔ cs (y : G) W₂ := by rw [← cs_sup, c.W_sup]
        _ ≤ S₀ := sup_le (hW W₁ c.W₁_le c.W₁_elem c.card_W₁)
          (hW W₂ c.W₂_le c.W₂_elem c.card_W₂)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [nat_card_cs])
  have hS : S₀ ≤ cs (y : G) (G₁ ⊔ G₂) := by
    have := cs_mono (y : G) c.S₀_le
    rwa [hcsS] at this
  exact mem_normalizer_iff_cs.2 (c.u1 hS)

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.exists_sylow (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂)
    (E : EmbSpec c.compData MD) :
    ∃ T : Sylow 2 G, d.P ≤ (T : Subgroup G) ∧ S₀ ≤ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀p : IsPGroup 2 S₀ := IsPGroup.of_card c.card_S₀
  have hPS : IsPGroup 2 ↥(d.P ⊔ S₀) :=
    IsPGroup.to_sup_of_normal_right' d.hP.isPGroup hS₀p c.P_le
  obtain ⟨T, hT⟩ := hPS.exists_le_sylow
  have hPT : d.P ≤ (T : Subgroup G) := le_sup_left.trans hT
  have hST : S₀ ≤ (T : Subgroup G) := le_sup_right.trans hT
  exact ⟨T, hPT, hST, c.le_normalizer_of_sylow E T hST⟩

end OddIndex

end CFSG.OddStandard.Seitz77.CaseB45
