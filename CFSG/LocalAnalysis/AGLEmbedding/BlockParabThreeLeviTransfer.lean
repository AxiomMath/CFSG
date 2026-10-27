module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Transfer

variable {W W₁ : Type*} [Group W] [Group W₁] [Finite W] {ρ : W →* W₁}

theorem exists_isPGroup_three_map_eq (hρ : Function.Surjective ρ) {U₁ : Subgroup W₁}
    (hU₁ : IsPGroup 3 U₁) : ∃ U : Subgroup W, U ≤ U₁.comap ρ ∧ IsPGroup 3 U ∧ U.map ρ = U₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := U₁.comap ρ
  let ρ' : C →* U₁ := (ρ.comp C.subtype).codRestrict U₁ fun x => x.2
  have hρ' : Function.Surjective ρ' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hρ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have : Finite U₁ := Finite.of_surjective ρ' hρ'
  obtain ⟨P⟩ : Nonempty (Sylow 3 C) := inferInstance
  have hPtop : ((P : Subgroup C).map ρ') = ⊤ := by
    rw [← Sylow.coe_mapSurjective hρ']
    obtain ⟨n, hn⟩ := hU₁.index ((P.mapSurjective hρ' : Sylow 3 U₁) : Subgroup U₁)
    have hnd := (P.mapSurjective hρ').not_dvd_index
    rcases n with _ | n
    · exact Subgroup.index_eq_one.1 (by simpa using hn)
    · exact absurd (hn ▸ dvd_pow_self 3 (Nat.succ_ne_zero n)) hnd
  refine ⟨(P : Subgroup C).map C.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  have e : ((P : Subgroup C).map C.subtype).map ρ = ((P : Subgroup C).map ρ').map U₁.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [e, hPtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem coprime_card_comap_three [Finite W₁] (hker : Nat.Coprime 3 (Nat.card ρ.ker))
    {V₁ : Subgroup W₁} (hV₁ : Nat.Coprime 3 (Nat.card V₁)) :
    Nat.Coprime 3 (Nat.card (V₁.comap ρ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have h1 : (x : W) ^ 3 = 1 := by
    rw [← Subgroup.orderOf_coe] at hx
    rw [← hx]
    exact pow_orderOf_eq_one _
  have h2 : ρ x = 1 := eq_one_of_mem_of_coprime_three hV₁ x.2 (e := 1)
    (by rw [pow_one, ← map_pow, h1, map_one])
  have h4 : (x : W) = 1 := eq_one_of_mem_of_coprime_three hker h2 (e := 1) (by simpa using h1)
  rw [← Subgroup.orderOf_coe, h4, orderOf_one] at hx
  norm_num at hx

omit [Finite W] in
theorem orderOf_map_eq_nine (hker : Nat.Coprime 3 (Nat.card ρ.ker)) {w : W}
    (hw : orderOf w = 9) : orderOf (ρ w) = 9 := by
  have hd : orderOf (ρ w) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hw]
    exact orderOf_map_dvd ρ w
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  rcases (show k ≤ 1 ∨ k = 2 by omega) with hk1 | rfl
  · exfalso
    have h3 : ρ (w ^ 3) = 1 := by
      rw [map_pow, ← orderOf_dvd_iff_pow_eq_one, hk']
      exact (pow_dvd_pow 3 hk1).trans (by norm_num)
    have h9 : (w ^ 3) ^ 3 ^ 1 = 1 := by
      rw [← pow_mul, show 3 * 3 ^ 1 = 9 by norm_num, ← hw, pow_orderOf_eq_one]
    have hw3 := eq_one_of_mem_of_coprime_three hker h3 h9
    have := orderOf_dvd_of_pow_eq_one hw3
    rw [hw] at this
    norm_num at this
  · rw [hk']
    norm_num

theorem ThreeDichotomy.of_map [Finite W₁] (hρ : Function.Surjective ρ) {J : Subgroup W}
    (hker : ρ.ker ≤ J) (hcop : Nat.Coprime 3 (Nat.card ρ.ker)) (h : ThreeDichotomy (J.map ρ)) :
    ThreeDichotomy J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk1 : ∀ x : W, ρ x = 1 → ∀ e : ℕ, x ^ 3 ^ e = 1 → x = 1 := fun x hx e he =>
    eq_one_of_mem_of_coprime_three hcop hx he
  have hcomapJ : ∀ {N₁ : Subgroup W₁}, N₁ ≤ J.map ρ → N₁.comap ρ ≤ J := fun hN =>
    (Subgroup.comap_mono hN).trans (by rw [Subgroup.comap_map_eq, sup_eq_left.2 hker])
  rcases h with hE | ⟨hnine, hpair, R₁, V₁, N₁, hRN, hVN, hNJ, hJV, hJN, hV3, hNV, hR3, a₁, ha₁,
    b₁, hb₁, hab⟩
  · left
    intro U hUJ hU
    have hU1 := hE (U.map ρ) (Subgroup.map_mono hUJ) (hU.map ρ)
    have hinj : ∀ x ∈ U, ρ x = 1 → x = 1 := fun x hx h1 => by
      obtain ⟨e, he⟩ := hU ⟨x, hx⟩
      exact hk1 x h1 e (by simpa using congrArg Subtype.val he)
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hc := hU1.1.is_comm.comm ⟨ρ x, x, x.2, rfl⟩ ⟨ρ y, y, y.2, rfl⟩
      have hc' : ρ ((x : W) * (y : W) * ((y : W) * (x : W))⁻¹) = 1 := by
        have := congrArg Subtype.val hc
        simp only [Subgroup.coe_mul] at this
        rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
      have := hinj _ (mul_mem (mul_mem x.2 y.2) (inv_mem (mul_mem y.2 x.2))) hc'
      simpa using mul_inv_eq_one.1 this
    · exact hinj _ (pow_mem hx 3) (by rw [map_pow]; exact hU1.2 _ ⟨x, hx, rfl⟩)
  · right
    refine ⟨fun u hu v hv hu9 hv9 huv => ?_, fun ⟨N, B, h1, h2, h3, h4, h5, h6, h7⟩ => ?_, ?_⟩
    · have hz := hnine (ρ u) ⟨u, hu, rfl⟩ (ρ v) ⟨v, hv, rfl⟩ (orderOf_map_eq_nine hcop hu9)
        (orderOf_map_eq_nine hcop hv9) (huv.map ρ)
      obtain ⟨⟨y, hyu, hyv⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hz
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyu
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hyv
      have hc : u ^ i * (v ^ j)⁻¹ = 1 := by
        refine hk1 _ ?_ 2 ?_
        · rw [map_mul, map_inv, map_zpow, map_zpow, hj, mul_inv_cancel]
        · have hcomm : Commute (u ^ i) (v ^ j)⁻¹ := ((huv.zpow_left i).zpow_right j).inv_right
          have hu1 : (u ^ i) ^ (9 : ℕ) = 1 := by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu9,
              pow_orderOf_eq_one, one_zpow]
          have hv1 : ((v ^ j)⁻¹) ^ (9 : ℕ) = 1 := by
            rw [inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hv9,
              pow_orderOf_eq_one, one_zpow, inv_one]
          rw [show (3 : ℕ) ^ 2 = 9 by norm_num, hcomm.mul_pow, hu1, hv1, one_mul]
      have hji : u ^ i = v ^ j := mul_inv_eq_one.1 hc
      refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨u ^ i, Subgroup.zpow_mem_zpowers u i,
        hji ▸ Subgroup.zpow_mem_zpowers v j⟩, fun h1 => hy1 ?_⟩
      have h1' : u ^ i = 1 := by simpa using congrArg Subtype.val h1
      have h2 : ρ u ^ i = 1 := by rw [← map_zpow, h1', map_one]
      exact Subtype.ext h2
    · refine hpair ⟨N.map ρ, B.map ρ, Subgroup.map_mono h1, Subgroup.map_mono h2,
        (Subgroup.map_mono h3).trans (Subgroup.le_normalizer_map ρ),
        (Subgroup.map_mono h4).trans (Subgroup.le_normalizer_map ρ),
        Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd N ρ) h5, ?_, ?_⟩
      · rintro _ ⟨b, hb, rfl⟩
        obtain ⟨e, he⟩ := h6 b hb
        exact ⟨e, ⟨_, he, map_pow ρ b _⟩⟩
      · rintro _ ⟨j, hj, rfl⟩
        obtain ⟨e, he⟩ := h7 j hj
        exact ⟨e, ⟨_, he, map_pow ρ j _⟩⟩
    · obtain ⟨R, hRle, hR, hRmap⟩ := exists_isPGroup_three_map_eq hρ hR3
      have hRN' : R ≤ N₁.comap ρ := hRle.trans (Subgroup.comap_mono hRN)
      have hJcomap : ∀ {X₁ : Subgroup W₁}, J.map ρ ≤ Subgroup.normalizer (X₁ : Set W₁) →
          J ≤ Subgroup.normalizer ((X₁.comap ρ : Subgroup W) : Set W) := fun hX x hx =>
        Subgroup.le_normalizer_comap ρ (hX ⟨x, hx, rfl⟩)
      refine ⟨R, V₁.comap ρ, N₁.comap ρ, hRN', Subgroup.comap_mono hVN, hcomapJ hNJ,
        hJcomap hJV, hJcomap hJN, coprime_card_comap_three hcop hV3, fun x hx => ?_, hR, ?_⟩
      · obtain ⟨e, he⟩ := hNV (ρ x) hx
        exact ⟨e, by rw [Subgroup.mem_comap, map_pow]; exact he⟩
      · rw [← hRmap] at ha₁ hb₁
        obtain ⟨a, ha, rfl⟩ := ha₁
        obtain ⟨b, hb, rfl⟩ := hb₁
        exact ⟨a, ha, b, hb, fun h => hab (by rw [← map_mul, h, map_mul])⟩

end Transfer

end CFSG.AGLEmbedding
