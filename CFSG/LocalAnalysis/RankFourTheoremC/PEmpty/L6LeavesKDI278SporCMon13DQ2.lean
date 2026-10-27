module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13DSL
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13DGen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalGL

theorem no_normalizer_thirteen_core {D : G33} (hD : orderOf D = 13) {T : Subgroup G33}
    (hT : Nat.card T = 27) (hnorm : ∀ t ∈ T, D * t * D⁻¹ ∈ T) : False := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite G33 := Nat.finite_of_card_ne_zero (by rw [card_G33]; norm_num)
  have hDN : D ∈ normalizer (T : Set G33) := mem_normalizer_of_orderOf_thirteen hD hnorm
  have hZN : zpowers D ≤ normalizer (T : Set G33) := Subgroup.zpowers_le.2 hDN
  let M : Subgroup G33 :=
    { carrier := {g | ∃ t ∈ T, ∃ k ∈ zpowers D, g = t * k}
      mul_mem' := by
        rintro _ _ ⟨t₁, ht₁, k₁, hk₁, rfl⟩ ⟨t₂, ht₂, k₂, hk₂, rfl⟩
        exact ⟨t₁ * (k₁ * t₂ * k₁⁻¹),
          T.mul_mem ht₁ ((mem_normalizer_iff.1 (hZN hk₁) t₂).1 ht₂), k₁ * k₂,
          Subgroup.mul_mem _ hk₁ hk₂, by group⟩
      one_mem' := ⟨1, T.one_mem, 1, Subgroup.one_mem _, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨t, ht, k, hk, rfl⟩
        exact ⟨k⁻¹ * t⁻¹ * k⁻¹⁻¹,
          (mem_normalizer_iff.1 (hZN (Subgroup.inv_mem _ hk)) t⁻¹).1 (T.inv_mem ht), k⁻¹,
          Subgroup.inv_mem _ hk, by group⟩ }
  have hTM : T ≤ M := fun t ht => ⟨t, ht, 1, Subgroup.one_mem _, (mul_one t).symm⟩
  have hMN : M ≤ normalizer (T : Set G33) := by
    rintro _ ⟨t, ht, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ht) (hZN hk)
  have hinter : ∀ w : G33, w ∈ T → w ∈ zpowers D → w = 1 := by
    intro w hwT hwZ
    have h1 : orderOf w ∣ 13 := by
      have := orderOf_dvd_of_mem_zpowers hwZ
      rwa [hD] at this
    have h2 : orderOf w ∣ 27 := by
      have := orderOf_dvd_natCard (⟨w, hwT⟩ : ↥T)
      rwa [Subgroup.orderOf_mk, hT] at this
    have h3 := Nat.dvd_gcd h1 h2
    have hg : Nat.gcd 13 27 = 1 := by norm_num
    rw [hg] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hMcard : Nat.card M = 351 := by
    let f : T × zpowers D → M := fun p => ⟨p.1.1 * p.2.1, p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨t, ht⟩, ⟨k, hk⟩⟩ ⟨⟨t', ht'⟩, ⟨k', hk'⟩⟩ h
      have h' : t * k = t' * k' := congrArg Subtype.val h
      have hw : t'⁻¹ * t = k' * k⁻¹ := by
        calc t'⁻¹ * t = t'⁻¹ * (t * k) * k⁻¹ := by group
          _ = t'⁻¹ * (t' * k') * k⁻¹ := by rw [h']
          _ = k' * k⁻¹ := by group
      have hw1 := hinter _ (T.mul_mem (T.inv_mem ht') ht)
        (by rw [hw]; exact Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk))
      have htt : t = t' := by
        have h2 : t = t' * (t'⁻¹ * t) := by group
        rw [h2, hw1, mul_one]
      have hkk : k = k' := by
        have h3 := h'
        rw [htt] at h3
        exact mul_left_cancel h3
      exact Prod.ext (Subtype.ext htt) (Subtype.ext hkk)
    have hsurj : Function.Surjective f := by
      rintro ⟨g, t, ht, k, hk, rfl⟩
      exact ⟨(⟨t, ht⟩, ⟨k, hk⟩), rfl⟩
    have h := Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
    rw [Nat.card_prod, hT, Nat.card_zpowers, hD] at h
    omega
  have hTnorm : (T.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hTM).2 hMN
  haveI := hTnorm
  have hTM27 : Nat.card (T.subgroupOf M) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT]
  have hfix : ∀ v : V3, v ≠ 0 → ∀ t ∈ T, t • v = v := by
    intro v hv
    set S : Subgroup ↥M := MulAction.stabilizer ↥M v with hSdef
    set O : Set V3 := MulAction.orbit ↥M v with hOdef
    have hidx : S.index = O.ncard := MulAction.index_stabilizer ↥M v
    have hSO : O.ncard * Nat.card S = 351 := by
      have h1 := Subgroup.card_mul_index S
      rw [hidx, hMcard] at h1
      rw [mul_comm]
      exact h1
    have h13S : ¬ 13 ∣ Nat.card S := by
      intro h
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 13 h
      have hfixv : ((x : ↥M) : G33) • v = v := MulAction.mem_stabilizer_iff.1 x.2
      have he : orderOf ((x : ↥M) : G33) = 13 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hx
      have hZS : zpowers ((x : ↥M) : G33) ≤ MulAction.stabilizer G33 v :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hfixv)
      have hcardZ : Nat.card (zpowers ((x : ↥M) : G33)) = 13 := by
        rw [Nat.card_zpowers, he]
      have hvfix : v ∈ fixSub (zpowers ((x : ↥M) : G33)) := fun g hg =>
        MulAction.mem_stabilizer_iff.1 (hZS hg)
      rw [fixSub_eq_bot hcardZ] at hvfix
      exact hv (AddSubgroup.mem_bot.1 hvfix)
    have h13O : 13 ∣ O.ncard := by
      have hcop : Nat.Coprime 13 (Nat.card S) :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h13S
      have h : 13 ∣ O.ncard * Nat.card S := by
        rw [hSO]
        norm_num
      exact hcop.dvd_of_dvd_mul_right h
    have hne : ∀ w ∈ O, w ≠ 0 := by
      intro w hw hw0
      obtain ⟨m, hm⟩ := hw
      have hm' : m • v = w := hm
      apply hv
      calc v = (m⁻¹ : ↥M) • (m • v) := (inv_smul_smul m v).symm
        _ = 0 := by rw [hm', hw0, smul_zero]
    have hO26 : O.ncard ≤ 26 := by
      rw [← Nat.card_coe_set_eq, ← card_V3_ne_zero]
      exact Nat.card_le_card_of_injective (fun w : O => (⟨w.1, hne w.1 w.2⟩ : {w : V3 // w ≠ 0}))
        (fun a b hab => Subtype.ext (congrArg (fun z : {w : V3 // w ≠ 0} => z.1) hab))
    have hOpos : 0 < O.ncard := (Set.ncard_pos (Set.toFinite O)).2 ⟨v, MulAction.mem_orbit_self v⟩
    have hO13 : O.ncard = 13 := by
      obtain ⟨k, hk⟩ := h13O
      rw [hk] at hSO hO26 hOpos ⊢
      rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
      · norm_num
      · omega
    have hS27 : Nat.card S = 27 := by
      rw [hO13] at hSO
      omega
    have hS3 : IsPGroup 3 S := IsPGroup.of_card (n := 3) (by rw [hS27]; norm_num)
    have hTM3 : IsPGroup 3 (T.subgroupOf M) := IsPGroup.of_card (n := 3) (by rw [hTM27]; norm_num)
    have hL : IsPGroup 3 ↥(S ⊔ T.subgroupOf M) := IsPGroup.to_sup_of_normal_right hS3 hTM3
    obtain ⟨n, hn⟩ := hL.exists_card_eq
    have hLdvd : Nat.card ↥(S ⊔ T.subgroupOf M) ∣ 351 := by
      have := Subgroup.card_subgroup_dvd_card (S ⊔ T.subgroupOf M)
      rwa [hMcard] at this
    have hLge : 27 ≤ Nat.card ↥(S ⊔ T.subgroupOf M) := by
      have h27 := Subgroup.card_dvd_of_le (le_sup_right : T.subgroupOf M ≤ S ⊔ T.subgroupOf M)
      rw [hTM27] at h27
      exact Nat.le_of_dvd Nat.card_pos h27
    have hL27 : Nat.card ↥(S ⊔ T.subgroupOf M) = 27 := by
      rw [hn] at hLdvd hLge ⊢
      have hn3 : n ≤ 3 := by
        by_contra hcon
        have h81 : 3 ^ 4 ∣ 3 ^ n := pow_dvd_pow 3 (show 4 ≤ n by omega)
        have := h81.trans hLdvd
        norm_num at this
      have hle : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
      exact le_antisymm (hle.trans (by norm_num)) hLge
    have h1 : T.subgroupOf M = S ⊔ T.subgroupOf M :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hL27, hTM27])
    have hSle : S ≤ T.subgroupOf M := by
      calc S ≤ S ⊔ T.subgroupOf M := le_sup_left
        _ = T.subgroupOf M := h1.symm
    have hSeq : S = T.subgroupOf M :=
      Subgroup.eq_of_le_of_card_ge hSle (by rw [hS27, hTM27])
    intro t ht
    have hmem : (⟨t, hTM ht⟩ : ↥M) ∈ T.subgroupOf M := Subgroup.mem_subgroupOf.2 ht
    rw [← hSeq] at hmem
    exact MulAction.mem_stabilizer_iff.1 hmem
  have hall : ∀ t ∈ T, t = 1 := by
    intro t ht
    apply eq_one_of_forall_smul
    intro v
    by_cases hv : v = 0
    · rw [hv, smul_zero]
    · exact hfix v hv t ht
  have hTbot : T = ⊥ := eq_bot_iff.2 fun t ht => Subgroup.mem_bot.2 (hall t ht)
  rw [hTbot, Subgroup.card_bot] at hT
  exact absurd hT (by norm_num)

theorem sl33_no_normalizer_thirteen : SL33Thirteen := by
  intro d hd T hT hnorm
  have hι : Function.Injective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) →* G33) :=
    Matrix.SpecialLinearGroup.toGL_injective
  refine no_normalizer_thirteen_core (D := Matrix.SpecialLinearGroup.toGL d)
    (by rw [orderOf_injective _ hι d, hd]) (T := T.map Matrix.SpecialLinearGroup.toGL) ?_ ?_
  · rw [Subgroup.card_map_of_injective hι]
    exact hT
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    refine Subgroup.mem_map.2 ⟨d * s * d⁻¹, hnorm s hs, ?_⟩
    simp [map_mul, map_inv]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
