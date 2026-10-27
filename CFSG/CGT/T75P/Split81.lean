module

public import CFSG.CGT.T75P.Ctx
public import CFSG.CGT.T75P.Mat3
public import CFSG.CGT.T75P.Split
public import CFSG.CGT.Timmesfeld75.Sec7Three
public import CFSG.CGT.Timmesfeld75.AltCover
import CFSG.GH74.M12.T1Nat

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem card_SL_three_two : Nat.card SL(3, GaloisField 2 1) = 168 :=
  CFSG.GH74.M12.Thm1.card_SL3_galois

theorem exists_lift_transvection {H : Subgroup G} [(T.subgroupOf H).Normal]
    (e : ↥H ⧸ T.subgroupOf H ≃* SL(3, GaloisField 2 1))
    {x₀ : G} (hx₀ : x₀ ∈ classD T) (hx₀H : x₀ ∈ H)
    (hu₀ : IsTransvection (e (QuotientGroup.mk (⟨x₀, hx₀H⟩ : ↥H))))
    {s : SL(3, GaloisField 2 1)} (hs : IsTransvection s) :
    ∃ x ∈ classD T, ∃ hxH : x ∈ H, e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H)) = s := by
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection hu₀ hs
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (e.symm W)
  have hwW : e (QuotientGroup.mk w) = W := by rw [hw]; exact e.apply_symm_apply W
  have hxH : (w : G) * x₀ * (w : G)⁻¹ ∈ H := H.mul_mem (H.mul_mem w.2 hx₀H) (H.inv_mem w.2)
  refine ⟨(w : G) * x₀ * (w : G)⁻¹, ?_, hxH, ?_⟩
  · have := classD_conj hx₀ (w : G)⁻¹
    simpa using this
  · have h1 : (⟨(w : G) * x₀ * (w : G)⁻¹, hxH⟩ : ↥H) = w * ⟨x₀, hx₀H⟩ * w⁻¹ := rfl
    rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hwW, hW]

theorem exists_complement_hSub81 (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (h66 : Sec66)
    (hc : Sec6Ctx T T₁ 3 1) (hnat : NaturalSL T (hSub T (normIn T₁ T)) 3 1) :
    ∃ K : Subgroup G, K ≤ hSub T (normIn T₁ T) ∧ T ⊓ K = ⊥ ∧ T ⊔ K = hSub T (normIn T₁ T) := by
  classical
  have : Finite G := hc.finite
  have hTab := hc.hy.pair.wc.1
  obtain ⟨hTH, hHN, hHnorm⟩ := hSub_data T T₁
  have hnat' := hnat
  set H := hSub T (normIn T₁ T) with hH
  obtain ⟨hN, e, φ, hcompat, htr⟩ := hc.sec67_transv h1 h63 (by omega) hnat'
  have hTabc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => elemAbelian_mul_comm hTab ha hb
  obtain ⟨x₀, hx₀D, hx₀N, hx₀T⟩ : ∃ x₀, x₀ ∈ classD T ∧ x₀ ∈ Subgroup.normalizer (T : Set G) ∧
      x₀ ∉ T := by
    have hL₁ : Nat.card (normIn T₁ T) ≠ 1 := by
      rw [hc.card_normIn_swap, hc.card_normIn]
      norm_num
    by_contra hcon
    push Not at hcon
    apply hL₁
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    by_contra hl1
    obtain ⟨s, hs⟩ := hc.hy.pair.conj
    have hlT₁ : l ∈ T₁ := (mem_normIn.1 hl).1
    have hlN : l ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hl).2
    have hlD : l ∈ classD T :=
      mem_classD_of_mem_conjSubgroup (k := s) (hs ▸ hlT₁) hl1
    have hlT := hcon l hlD hlN
    have : l ∈ T ⊓ T₁ := Subgroup.mem_inf.2 ⟨hlT, hlT₁⟩
    rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at this
    exact hl1 this
  have hx₀H : x₀ ∈ H := by
    obtain ⟨hx₀H, -⟩ := htr x₀ ⟨hx₀D, hx₀N⟩ hx₀T
    exact hx₀H
  obtain ⟨hx₀H', hu₀⟩ := htr x₀ ⟨hx₀D, hx₀N⟩ hx₀T
  obtain ⟨s₁, s₂, hs₁, hs₂, hs₁2, hs₂2, hs4, hs2⟩ := exists_transvection_pair (GaloisField 2 1)
  obtain ⟨x₁, hx₁D, hx₁H, hx₁s⟩ := exists_lift_transvection e hx₀D hx₀H' hu₀ hs₁
  obtain ⟨x₂, hx₂D, hx₂H, hx₂s⟩ := exists_lift_transvection e hx₀D hx₀H' hu₀ hs₂
  have hx₁2 : x₁ * x₁ = 1 := mul_self_eq_one_of_mem_classD hTab hx₁D
  have hx₂2 : x₂ * x₂ = 1 := mul_self_eq_one_of_mem_classD hTab hx₂D
  let a : ↥H := ⟨x₁, hx₁H⟩
  let b : ↥H := ⟨x₂, hx₂H⟩
  have ha2 : a * a = 1 := Subtype.ext hx₁2
  have hb2 : b * b = 1 := Subtype.ext hx₂2
  let π : ↥H →* SL(3, GaloisField 2 1) := e.toMonoidHom.comp (QuotientGroup.mk' (T.subgroupOf H))
  have hπa : π a = s₁ := hx₁s
  have hπb : π b = s₂ := hx₂s
  have hker : ∀ z : ↥H, π z = 1 ↔ (z : G) ∈ T := fun z => by
    show e (QuotientGroup.mk z) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff (N := T.subgroupOf H)]
    exact Subgroup.mem_subgroupOf
  have hπab : ∀ k : ℕ, π ((a * b) ^ k) = (s₁ * s₂) ^ k := fun k => by
    rw [map_pow, map_mul, hπa, hπb]
  have h4T : ((x₁ * x₂) ^ 4 : G) ∈ T := by
    have := (hker ((a * b) ^ 4)).1 (by rw [hπab, hs4])
    simpa [a, b] using this
  have h2T : ((x₁ * x₂) ^ 2 : G) ∉ T := by
    intro h
    have := (hker ((a * b) ^ 2)).2 (by simpa [a, b] using h)
    rw [hπab] at this
    exact hs2 this
  have h8 : (x₁ * x₂) ^ 8 = 1 := by
    have := elemAbelian_mul_self hTab h4T
    rw [← pow_add] at this
    exact this
  have h2ne : (x₁ * x₂) ^ 2 ≠ 1 := fun h => h2T (h ▸ T.one_mem)
  have ho4 : orderOf (x₁ * x₂) = 4 := by
    have hdvd : orderOf (x₁ * x₂) ∣ 8 := orderOf_dvd_of_pow_eq_one h8
    have hn1 : orderOf (x₁ * x₂) ≠ 1 := fun h => h2ne (by
      have := orderOf_eq_one_iff.1 h
      rw [this]; simp)
    have hn2 : orderOf (x₁ * x₂) ≠ 2 := fun h => h2ne (by
      rw [← h]; exact pow_orderOf_eq_one _)
    have hle : orderOf (x₁ * x₂) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf (x₁ * x₂) := orderOf_pos _
    have h73 := (hc.sec73 h1 h62 h63 h66 (by omega) hnat hx₁D hx₂D).1
    generalize orderOf (x₁ * x₂) = o at *
    interval_cases o
    · exact absurd rfl hn1
    · exact absurd rfl hn2
    · omega
    · rfl
    · omega
    · omega
    · omega
    · exfalso
      rcases h73 with h | h | ⟨k, hk, hk2⟩
      · omega
      · exact absurd h (by decide)
      · obtain ⟨c, hc⟩ := hk
        omega
  have hst : (x₁ * x₂) ^ 4 = 1 := by rw [← ho4]; exact pow_orderOf_eq_one _
  have hab4 : (a * b) ^ 4 = 1 := Subtype.ext (by simpa [a, b] using hst)
  have hab2 : (a * b) ^ 2 ≠ 1 := fun h => h2ne (by
    have := congrArg Subtype.val h
    simpa [a, b] using this)
  let K₀H : Subgroup ↥H := Subgroup.closure ({a, b} : Set ↥H)
  have hK₀Hcard : Nat.card K₀H = 8 := card_closure_pair_eq_eight ha2 hb2 hab4 hab2
  have hs12 : Nat.card (Subgroup.closure ({s₁, s₂} : Set SL(3, GaloisField 2 1))) = 8 :=
    card_closure_pair_eq_eight hs₁2 hs₂2 hs4 hs2
  let ρ : ↥K₀H →* SL(3, GaloisField 2 1) := π.comp K₀H.subtype
  have hρrange : ρ.range = Subgroup.closure ({s₁, s₂} : Set SL(3, GaloisField 2 1)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.map_closure, Set.image_pair,
      hπa, hπb]
  have hρker : ρ.ker = ⊥ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    have h2 : Nat.card (↥K₀H ⧸ ρ.ker) = Nat.card ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    have h3 : Nat.card ↥K₀H = 8 := hK₀Hcard
    rw [h2, hρrange, hs12, h3] at h1
    have h4 : Nat.card ρ.ker = 1 := by omega
    exact Subgroup.card_eq_one.1 h4
  let K₀ : Subgroup G := K₀H.map H.subtype
  have hK₀H : K₀ ≤ H := Subgroup.map_subtype_le K₀H
  have hK₀card : Nat.card K₀ = 8 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hK₀Hcard
  have hTK₀ : T ⊓ K₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, k, hk, rfl⟩
    have hk1 : (⟨k, hk⟩ : ↥K₀H) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact (hker k).2 hxT
    rw [hρker, Subgroup.mem_bot] at hk1
    have := congrArg (fun z : ↥K₀H => ((z : ↥H) : G)) hk1
    simpa using this
  have hcardT : Nat.card T = 8 := by rw [hc.hT]; norm_num
  have hcardH : Nat.card H = 1344 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf H)
    have h2 : Nat.card (↥H ⧸ T.subgroupOf H) = 168 := by
      rw [Nat.card_congr e.toEquiv, card_SL_three_two]
    have h3 : Nat.card (T.subgroupOf H) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, hcardT]
    rw [h2, h3] at h1
    omega
  have hge : 64 ≤ Nat.card ↥(T ⊔ K₀) := by
    have hinj : Function.Injective (fun p : ↥T × ↥K₀ =>
        (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(T ⊔ K₀))) := by
      rintro ⟨⟨t, ht⟩, ⟨k, hk⟩⟩ ⟨⟨t', ht'⟩, ⟨k', hk'⟩⟩ h
      have h' : t * k = t' * k' := congrArg Subtype.val h
      have h5 : t'⁻¹ * t = k' * k⁻¹ := by
        calc t'⁻¹ * t = t'⁻¹ * (t * k) * k⁻¹ := by group
          _ = t'⁻¹ * (t' * k') * k⁻¹ := by rw [h']
          _ = k' * k⁻¹ := by group
      have h6 : t'⁻¹ * t ∈ T ⊓ K₀ :=
        Subgroup.mem_inf.2 ⟨T.mul_mem (T.inv_mem ht') ht, h5 ▸ K₀.mul_mem hk' (K₀.inv_mem hk)⟩
      rw [hTK₀, Subgroup.mem_bot] at h6
      have h7 : t = t' := by
        calc t = t' * (t'⁻¹ * t) := by group
          _ = t' := by rw [h6, mul_one]
      subst h7
      have h8 : k = k' := by
        have : t⁻¹ * (t * k) = t⁻¹ * (t * k') := by rw [h']
        simpa using this
      subst h8
      rfl
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hcardT, hK₀card] at this
    exact this
  have hpg : IsPGroup 2 ↥(T ⊔ K₀) := by
    have hT2 : IsPGroup 2 ↥T := isPGroup_two_of_isElemAbelian hTab
    have hK2 : IsPGroup 2 ↥K₀ := IsPGroup.of_card (n := 3) (by rw [hK₀card]; norm_num)
    exact hT2.to_sup_of_normal_left' hK2 (hK₀H.trans hHN)
  have hle : T ⊔ K₀ ≤ H := sup_le hTH hK₀H
  have hcard64 : Nat.card ↥(T ⊔ K₀) = 64 := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hpg
    have hdvd : Nat.card ↥(T ⊔ K₀) ∣ 1344 := hcardH ▸ Subgroup.card_dvd_of_le hle
    have hm6 : m ≤ 6 := by
      by_contra hm7
      push Not at hm7
      have : 2 ^ 7 ∣ 2 ^ m := pow_dvd_pow 2 hm7
      rw [← hm] at this
      have := this.trans hdvd
      omega
    have : 2 ^ m ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hm6
    omega
  have hrel : (T ⊔ K₀).relIndex H = 21 := by
    have h1 := Subgroup.relIndex_mul_card (T ⊔ K₀) H
    rw [inf_eq_left.2 hle, hcard64, hcardH] at h1
    omega
  exact exists_complement_of_coprime_index hTH hK₀H hN hTabc hTK₀
    (by rw [hrel, hcardT]; norm_num)

end CFSG.CGT.T75P
