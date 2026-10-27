module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineRank

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SixNineRank

theorem eq_bot_or_eq_top_of_mul_mem {E : Type*} [Field E] [Finite E] {n : ℕ}
    (hE : Nat.card E = 2 ^ n) {p : ℕ} (hp : p.Prime)
    (hppd : ∀ k, 0 < k → k < n → ¬ p ∣ 2 ^ k - 1) {s : E} (hs : orderOf s = p)
    (M : AddSubgroup E) (hM : ∀ a ∈ M, s * a ∈ M) : M = ⊥ ∨ M = ⊤ := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hpow : ∀ c : E, (∀ a ∈ M, c * a ∈ M) → ∀ k : ℕ, ∀ a ∈ M, c ^ k * a ∈ M := by
    intro c hc k
    induction k with
    | zero => intro a ha; rwa [pow_zero, one_mul]
    | succ k ih => intro a ha; rw [pow_succ, mul_assoc]; exact ih _ (hc a ha)
  let F : Subfield E :=
    { carrier := {c | ∀ a ∈ M, c * a ∈ M}
      mul_mem' := fun {c d} hc hd a ha => by rw [mul_assoc]; exact hc _ (hd a ha)
      one_mem' := fun a ha => by rwa [one_mul]
      add_mem' := fun {c d} hc hd a ha => by rw [add_mul]; exact M.add_mem (hc a ha) (hd a ha)
      zero_mem' := fun a _ => by rw [zero_mul]; exact M.zero_mem
      neg_mem' := fun {c} hc a ha => by rw [neg_mul]; exact M.neg_mem (hc a ha)
      inv_mem' := fun c hc a ha => by
        by_cases hc0 : c = 0
        · rw [hc0, inv_zero, zero_mul]; exact M.zero_mem
        · have h1 := FiniteField.pow_card_sub_one_eq_one c hc0
          have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
          have h2 : c⁻¹ = c ^ (Fintype.card E - 2) := by
            refine inv_eq_of_mul_eq_one_right ?_
            rw [← pow_succ', show Fintype.card E - 2 + 1 = Fintype.card E - 1 by omega, h1]
          rw [h2]
          exact hpow c hc _ a ha }
  have hsF : s ∈ F := hM
  have hdvd : Nat.card F.toAddSubgroup ∣ 2 ^ n := hE ▸ AddSubgroup.card_addSubgroup_dvd_card _
  obtain ⟨m, hmn, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcardF : Nat.card F = 2 ^ m := hm
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one s
    rw [hs, h0, zero_pow hp.pos.ne'] at h1
    exact zero_ne_one h1
  have hspow : s ^ (2 ^ m - 1) = 1 := by
    have : Fintype F := Fintype.ofFinite F
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨s, hsF⟩ : F) (fun h => hs0 (by
      have := congrArg Subtype.val h; simpa using this))
    rw [← Nat.card_eq_fintype_card, hcardF] at h1
    have := congrArg Subtype.val h1
    simpa using this
  have hpm : p ∣ 2 ^ m - 1 := hs ▸ orderOf_dvd_of_pow_eq_one hspow
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exfalso
      rw [pow_zero, Nat.card_eq_one_iff_unique] at hcardF
      have h01 : (0 : F) = 1 := hcardF.1.elim _ _
      exact zero_ne_one (congrArg Subtype.val h01)
    · exact h
  have hmn' : m = n := by
    by_contra hne
    exact hppd m hm0 (lt_of_le_of_ne hmn hne) hpm
  have htop : F.toAddSubgroup = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [hm, hmn', hE])
  have hall : ∀ c : E, ∀ a ∈ M, c * a ∈ M := fun c => by
    have : c ∈ F.toAddSubgroup := by rw [htop]; exact AddSubgroup.mem_top c
    exact this
  by_cases hM0 : M = ⊥
  · exact Or.inl hM0
  · right
    obtain ⟨a, haM, ha0⟩ : ∃ a ∈ M, a ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hM0 (eq_bot_iff.mpr fun a ha => (AddSubgroup.mem_bot).mpr (hno a ha))
    refine eq_top_iff.mpr fun b _ => ?_
    have := hall (b * a⁻¹) _ haM
    rwa [mul_assoc, inv_mul_cancel₀ ha0, mul_one] at this

theorem card_modEq_one_of_fixedPointFree {E : Type*} [AddGroup E] [Finite E] (M : AddSubgroup E)
    {p n : ℕ} [Fact p.Prime] (g : E → E) (hgM : ∀ a ∈ M, g a ∈ M) (hg0 : g 0 = 0)
    (hgpow : ∀ a ∈ M, g^[p ^ n] a = a) (hfix : ∀ a ∈ M, g a = a → a = 0) :
    Nat.card M ≡ 1 [MOD p] := by
  classical
  have : Fintype M := Fintype.ofFinite M
  let F : Function.End M := fun a => ⟨g a, hgM a a.2⟩
  have hiter : ∀ (k : ℕ) (a : M), ((F^[k] a : M) : E) = g^[k] a := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih a]
  have hF : F ^ p ^ n = 1 := by
    funext a
    show F^[p ^ n] a = a
    exact Subtype.ext ((hiter _ a).trans (hgpow a a.2))
  have h1 := Equiv.Perm.card_fixedPoints_modEq (f := F) hF
  have h2 : Fintype.card (Function.fixedPoints F) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, Subtype.ext hg0⟩, ?_⟩
    rintro ⟨a, ha⟩
    have ha' : F a = a := ha
    have h0 : (a : E) = 0 := hfix a a.2 (congrArg Subtype.val ha')
    exact Subtype.ext (Subtype.ext h0)
  rw [Nat.card_eq_fintype_card]
  have h3 : Fintype.card M ≡ Fintype.card (Function.fixedPoints F) [MOD p] := h1
  rwa [h2] at h3

theorem eq_bot_or_eq_top_of_card_modEq {E : Type*} [AddGroup E] [Finite E]
    (hE : Nat.card E = 2 ^ 6) (M : AddSubgroup E) (h7 : Nat.card M ≡ 1 [MOD 7])
    (h3 : Nat.card M ≡ 1 [MOD 3]) : M = ⊥ ∨ M = ⊤ := by
  have hdvd : Nat.card M ∣ 2 ^ 6 := hE ▸ AddSubgroup.card_addSubgroup_dvd_card M
  obtain ⟨m, hm, hmM⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hmM] at h7 h3
  interval_cases m
  · left; exact AddSubgroup.eq_bot_of_card_eq M (by rw [hmM]; rfl)
  · exact absurd h3 (by decide)
  · exact absurd h7 (by decide)
  · exact absurd h3 (by decide)
  · exact absurd h7 (by decide)
  · exact absurd h3 (by decide)
  · right; exact AddSubgroup.eq_top_of_card_eq M (by rw [hmM, hE])

end SixNineRank

namespace U3Start

open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_ppd_torus_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hf3 : f ≠ 3) :
    ∃ ε ∈ L, ε ∈ normalizer (szT₁ L T : Set G) ∧ ε ∈ centralizer (szA₁ (szT₁ L T) : Set G) ∧
      CFSG.Timmesfeld.IsPrimitivePrimeDivisor (orderOf ε) (2 * f) ∧
      ∀ y ∈ szT₁ L T, ε * y * ε⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T) := by
  classical
  have hf2 := h.two_le
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hcore⟩ := hB.exists_benderCore Q
  have hA₁L : ∀ x ∈ szA₁ (szT₁ L T), x ∈ L := fun x hx => szT₁_le_right L T (szA₁_le _ hx)
  have he : e = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) := by
    rcases hB.cases' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, he, -⟩
    · omega
    · omega
    · exact he
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * f) (by omega)
    (by omega)
  have hpq : p ∣ 2 ^ f + 1 := (hp.dvd_add_one_iff (by omega) f).mpr
    ⟨dvd_refl _, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩
  have hp3 : ¬ p ∣ 3 := fun h3 => by have := hp.eq_two_of_dvd_three (by omega) h3; omega
  have hge : 2 ^ f + 1 = Nat.gcd 3 (2 ^ f + 1) * e := by
    rw [he]; exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right 3 _)).symm
  have hpe : p ∣ e := by
    rw [hge] at hpq
    rcases (Nat.Prime.dvd_mul hp.prime).mp hpq with h1 | h1
    · exact absurd (h1.trans (Nat.gcd_dvd_left 3 _)) hp3
    · exact h1
  have : Fact p.Prime := ⟨hp.prime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fixCartan (Q : Subgroup L) t₀) p
    (by rw [hcore.card_fixCartan]; exact hpe)
  have hxD : (x : L) ∈ cartan (Q : Subgroup L) t₀ := fixCartan_le_cartan _ _ x.2
  have hord : orderOf ((x : L) : G) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hx1 : (x : L) ≠ 1 := by
    intro h1
    have h2 : orderOf ((x : L) : G) = 1 := by rw [h1]; simp
    rw [hord] at h2
    exact hp.prime.one_lt.ne' h2
  have hkT : ((x : L) : G) ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) (x : L)).mp (cartan_le_borel _ _ hxD)
  have hkC : ((x : L) : G) ∈ centralizer (szA₁ (szT₁ L T) : Set G) := by
    refine mem_centralizer_iff.mpr fun z hz => ?_
    by_cases hz1 : z = 1
    · rw [hz1, one_mul, mul_one]
    have hzZ : (⟨z, hA₁L z hz⟩ : L) ∈ rootCenter (Q : Subgroup L) := (hmemZ _).mpr hz
    have hz1' : (⟨z, hA₁L z hz⟩ : L) ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
    have hxc : (x : L) ∈ cartan (Q : Subgroup L) t₀ ⊓
        centralizer ({(⟨z, hA₁L z hz⟩ : L)} : Set L) := by
      rw [hcore.cartan_inf_centralizer_eq hzZ hz1']; exact x.2
    have := mem_centralizer_singleton_iff.mp (mem_inf.mp hxc).2
    exact (congrArg Subtype.val this).symm
  refine ⟨(x : L), (x : L).2, hkT, hkC, hord ▸ hp, fun y hyT h1 => ?_⟩
  have hyL : y ∈ L := szT₁_le_right L T hyT
  have hfpf := hB.fixedPointFree_unitary Q hcore.sq_eq_one hcore.not_mem hxD hx1
    ((hmemQ ⟨y, hyL⟩).mpr hyT) ((hmemZ _).mpr (by simpa using h1))
  exact (hmemZ _).mp hfpf

theorem exists_seven_torus_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hf3 : f = 3) :
    ∃ ε ∈ L, ε ∈ normalizer (szT₁ L T : Set G) ∧ orderOf ε = 7 ∧
      ∀ y ∈ szT₁ L T, ε * y * ε⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T) := by
  classical
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hcore⟩ := hB.exists_benderCore Q
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := cartan (Q : Subgroup L) t₀) 7 (by
    rw [hcore.card_cartan, hf3]
    exact Dvd.dvd.mul_right (by norm_num) _)
  have hxD : (x : L) ∈ cartan (Q : Subgroup L) t₀ := x.2
  have hord : orderOf ((x : L) : G) = 7 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hx1 : (x : L) ≠ 1 := by
    intro h1
    have h2 : orderOf ((x : L) : G) = 1 := by rw [h1]; simp
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  have hkT : ((x : L) : G) ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) (x : L)).mp (cartan_le_borel _ _ hxD)
  refine ⟨(x : L), (x : L).2, hkT, hord, fun y hyT h1 => ?_⟩
  have hyL : y ∈ L := szT₁_le_right L T hyT
  have hfpf := hB.fixedPointFree_unitary Q hcore.sq_eq_one hcore.not_mem hxD hx1
    ((hmemQ ⟨y, hyL⟩).mpr hyT) ((hmemZ _).mpr (by simpa using h1))
  exact (hmemZ _).mp hfpf

end U3Start

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem eq_or_eq_of_stable_one (hR : U3R2 G L (szT₁ L T) R₂ t f) {E : Type*} [Field E]
    {σ : E →+* E} {u vc : G → E} (hc : U3RootCoords (szT₁ L T) σ u vc)
    (hA₁u : ∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) {P : Set G}
    (hPT : ∀ g ∈ P, g ∈ normalizer (szT₁ L T : Set G))
    (hirr : ∀ M : AddSubgroup E, (∀ g ∈ P, ∀ y ∈ szT₁ L T, u y ∈ M → u (g * y * g⁻¹) ∈ M) →
      M = ⊥ ∨ M = ⊤)
    {Y : Subgroup G} (hRY : R₂ ≤ Y) (hYX : Y ≤ szT₁ L T ⊔ R₂)
    (hPY : ∀ g ∈ P, g ∈ normalizer (Y : Set G)) : Y = R₂ ∨ Y = szT₁ L T ⊔ R₂ := by
  let M : AddSubgroup E :=
    { carrier := {a | ∃ y ∈ Y ⊓ szT₁ L T, u y = a}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨y, hy, rfl⟩ := ha
        obtain ⟨y', hy', rfl⟩ := hb
        exact ⟨y * y', mul_mem hy hy', hc.mul_u _ (mem_inf.mp hy).2 _ (mem_inf.mp hy').2⟩
      zero_mem' := ⟨1, one_mem _, hc.u_one⟩
      neg_mem' := fun {a} ha => by
        obtain ⟨y, hy, rfl⟩ := ha
        exact ⟨y⁻¹, inv_mem hy, hc.u_inv (mem_inf.mp hy).2⟩ }
  have hmemM : ∀ a, a ∈ M ↔ ∃ y ∈ Y ⊓ szT₁ L T, u y = a := fun a => Iff.rfl
  have hY : ∀ y ∈ szT₁ L T, u y ∈ M → y ∈ Y := by
    intro y hy hyM
    obtain ⟨y', hy', hy'y⟩ := (hmemM _).mp hyM
    obtain ⟨hy'Y, hy'T⟩ := mem_inf.mp hy'
    have hA : y'⁻¹ * y ∈ szA₁ (szT₁ L T) :=
      (hA₁u _ (mul_mem (inv_mem hy'T) hy)).mpr (by rw [hc.u_mul_inv hy'T hy, hy'y, sub_self])
    have := mul_mem hy'Y (hRY (hR.le hA))
    rwa [mul_inv_cancel_left] at this
  have hM : ∀ g ∈ P, ∀ y ∈ szT₁ L T, u y ∈ M → u (g * y * g⁻¹) ∈ M := by
    intro g hg y hy hyM
    exact (hmemM _).mpr ⟨g * y * g⁻¹, mem_inf.mpr ⟨(mem_normalizer_iff.mp (hPY g hg) y).mp
      (hY y hy hyM), (mem_normalizer_iff.mp (hPT g hg) y).mp hy⟩, rfl⟩
  rcases hirr M hM with hM0 | hM1
  · left
    refine le_antisymm (fun z hz => ?_) hRY
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp (hYX hz)
    have hwY : w ∈ Y := by
      have := mul_mem hz (inv_mem (hRY hr)); rwa [mul_inv_cancel_right] at this
    have hwM : u w ∈ M := (hmemM _).mpr ⟨w, mem_inf.mpr ⟨hwY, hw⟩, rfl⟩
    rw [hM0, AddSubgroup.mem_bot] at hwM
    exact mul_mem (hR.le ((hA₁u w hw).mpr hwM)) hr
  · right
    refine le_antisymm hYX (sup_le (fun w hw => hY w hw (by rw [hM1]; exact AddSubgroup.mem_top _))
      hRY)

theorem eq_or_eq_of_stable_two (hU : U3U1Data G L f t T R₂ U₁)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (htU : t ∈ normalizer (U₁ : Set G)) {E : Type*} [Field E]
    {σ : E →+* E} {u vc : G → E} (hc : U3RootCoords (szT₁ L T) σ u vc)
    (hA₁u : ∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) {P : Set G}
    (hPT : ∀ g ∈ P, g ∈ normalizer (szT₁ L T : Set G)) (hPt : ∀ g ∈ P, g * t = t * g)
    (hPR : ∀ g ∈ P, g ∈ normalizer (R₂ : Set G))
    (hirr : ∀ M : AddSubgroup E, (∀ g ∈ P, ∀ y ∈ szT₁ L T, u y ∈ M → u (g * y * g⁻¹) ∈ M) →
      M = ⊥ ∨ M = ⊤)
    {Y : Subgroup G} (hXY : szT₁ L T ⊔ R₂ ≤ Y) (hYU : Y ≤ U₁)
    (hPY : ∀ g ∈ P, g ∈ normalizer (Y : Set G)) : Y = szT₁ L T ⊔ R₂ ∨ Y = U₁ := by
  have htt : t * t = 1 := by rw [← sq, hR.t_sq]
  have hT₁U : ∀ w ∈ szT₁ L T, w ∈ U₁ := fun w hw => hU.le (mem_sup_left hw)
  have hNR : ∀ g ∈ U₁, g ∈ normalizer (R₂ : Set G) := fun g hg =>
    centralizer_le_normalizer _ (hU.le_centralizer hg)
  have hconj : ∀ g ∈ U₁, ∀ r ∈ R₂, g * r * g⁻¹ ∈ R₂ := fun g hg r hr =>
    (mem_normalizer_iff.mp (hNR g hg) r).mp hr
  have hconj' : ∀ g ∈ U₁, ∀ r ∈ R₂, g⁻¹ * r * g ∈ R₂ := fun g hg r hr => by
    have := hconj g⁻¹ (inv_mem hg) r hr; rwa [inv_inv] at this
  have hdec : ∀ z ∈ U₁, ∃ w ∈ szT₁ L T, w⁻¹ * (z * t * z⁻¹ * t⁻¹) ∈ R₂ := by
    intro z hz
    obtain ⟨w, hw, r, hr, hwr⟩ := hR.mem_sup_iff.mp (hU.comm_t_mem_sup hR htU hz)
    exact ⟨w, hw, by rw [← hwr, inv_mul_cancel_left]; exact hr⟩
  let M : AddSubgroup E :=
    { carrier := {a | ∃ z ∈ Y, ∃ w ∈ szT₁ L T, u w = a ∧ w⁻¹ * (z * t * z⁻¹ * t⁻¹) ∈ R₂}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨z, hz, w, hw, rfl, hr⟩ := ha
        obtain ⟨z', hz', w', hw', rfl, hr'⟩ := hb
        refine ⟨z * z', mul_mem hz hz', w' * w, mul_mem hw' hw,
          by rw [hc.mul_u _ hw' _ hw, add_comm], ?_⟩
        have e : (w' * w)⁻¹ * ((z * z') * t * (z * z')⁻¹ * t⁻¹) =
            (w⁻¹ * (w'⁻¹ * z * w'⁻¹⁻¹ * z⁻¹) * w) *
              (w⁻¹ * (z * (w'⁻¹ * (z' * t * z'⁻¹ * t⁻¹)) * z⁻¹) * w) *
              (w⁻¹ * (z * t * z⁻¹ * t⁻¹)) := by group
        rw [e]
        have hzU := hYU hz
        exact mul_mem (mul_mem
          (hconj' w (hT₁U w hw) _ (hU.comm_mem _ (inv_mem (hT₁U w' hw')) _ hzU))
          (hconj' w (hT₁U w hw) _ (hconj z hzU _ hr'))) hr
      zero_mem' := ⟨1, one_mem _, 1, one_mem _, hc.u_one, by simp⟩
      neg_mem' := fun {a} ha => by
        obtain ⟨z, hz, w, hw, rfl, hr⟩ := ha
        refine ⟨z⁻¹, inv_mem hz, w⁻¹, inv_mem hw, hc.u_inv hw, ?_⟩
        have e : w⁻¹⁻¹ * (z⁻¹ * t * z⁻¹⁻¹ * t⁻¹) =
            (w * z⁻¹ * w⁻¹ * z⁻¹⁻¹) *
              ((z⁻¹ * w) * (w⁻¹ * (z * t * z⁻¹ * t⁻¹))⁻¹ * (z⁻¹ * w)⁻¹) := by group
        rw [e]
        have hzU := hYU hz
        exact mul_mem (hU.comm_mem _ (hT₁U w hw) _ (inv_mem hzU))
          (hconj _ (mul_mem (inv_mem hzU) (hT₁U w hw)) _ (inv_mem hr)) }
  have hmemM : ∀ a, a ∈ M ↔
      ∃ z ∈ Y, ∃ w ∈ szT₁ L T, u w = a ∧ w⁻¹ * (z * t * z⁻¹ * t⁻¹) ∈ R₂ := fun a => Iff.rfl
  have hM : ∀ g ∈ P, ∀ y ∈ szT₁ L T, u y ∈ M → u (g * y * g⁻¹) ∈ M := by
    intro g hg w hw hwM
    obtain ⟨z, hz, w', hw', hww', hr⟩ := (hmemM _).mp hwM
    have hwA : w⁻¹ * w' ∈ R₂ := hR.le
      ((hA₁u _ (mul_mem (inv_mem hw) hw')).mpr (by rw [hc.u_mul_inv hw hw', hww', sub_self]))
    have hr2 : w⁻¹ * (z * t * z⁻¹ * t⁻¹) ∈ R₂ := by
      have := mul_mem hwA hr
      rwa [show w⁻¹ * w' * (w'⁻¹ * (z * t * z⁻¹ * t⁻¹)) = w⁻¹ * (z * t * z⁻¹ * t⁻¹) by group]
        at this
    have hgtg : g⁻¹ * t * g = t := by rw [mul_assoc, ← hPt g hg, inv_mul_cancel_left]
    refine (hmemM _).mpr ⟨g * z * g⁻¹, (mem_normalizer_iff.mp (hPY g hg) z).mp hz, g * w * g⁻¹,
      (mem_normalizer_iff.mp (hPT g hg) w).mp hw, rfl, ?_⟩
    have e : (g * w * g⁻¹)⁻¹ * ((g * z * g⁻¹) * t * (g * z * g⁻¹)⁻¹ * t⁻¹) =
        g * (w⁻¹ * (z * (g⁻¹ * t * g) * z⁻¹ * (g⁻¹ * t * g)⁻¹)) * g⁻¹ := by group
    rw [e, hgtg]
    exact (mem_normalizer_iff.mp (hPR g hg) _).mp hr2
  rcases hirr M hM with hM0 | hM1
  · left
    refine le_antisymm (fun z hz => ?_) hXY
    have hzU := hYU hz
    obtain ⟨w, hw, hr⟩ := hdec z hzU
    have hwM : u w ∈ M := (hmemM _).mpr ⟨z, hz, w, hw, rfl, hr⟩
    rw [hM0, AddSubgroup.mem_bot] at hwM
    have hwA := hR.le ((hA₁u w hw).mpr hwM)
    refine hU.mem_sup_of_comm_mem hR htt hzU ?_
    have := mul_mem hwA hr
    rwa [mul_inv_cancel_left] at this
  · right
    refine le_antisymm hYU (fun z₀ hz₀ => ?_)
    obtain ⟨w₀, hw₀, hr₀⟩ := hdec z₀ hz₀
    have hwM : u w₀ ∈ M := by rw [hM1]; exact AddSubgroup.mem_top _
    obtain ⟨z, hz, w, hw, hww, hr⟩ := (hmemM _).mp hwM
    have hzU := hYU hz
    have hwA : w⁻¹ * w₀ ∈ szA₁ (szT₁ L T) :=
      (hA₁u _ (mul_mem (inv_mem hw) hw₀)).mpr (by rw [hc.u_mul_inv hw hw₀, hww, sub_self])
    have hcomm : (z⁻¹ * z₀) * t * (z⁻¹ * z₀)⁻¹ * t⁻¹ ∈ R₂ := by
      have e : (z⁻¹ * z₀) * t * (z⁻¹ * z₀)⁻¹ * t⁻¹ =
          z⁻¹ * ((w * (w⁻¹ * w₀) * w⁻¹) *
            (w * ((w₀⁻¹ * (z₀ * t * z₀⁻¹ * t⁻¹)) * (w⁻¹ * (z * t * z⁻¹ * t⁻¹))⁻¹) * w⁻¹)) *
            z := by group
      rw [e]
      exact hconj' z hzU _ (mul_mem (hconj w (hT₁U w hw) _ (hR.le hwA))
        (hconj w (hT₁U w hw) _ (mul_mem hr₀ (inv_mem hr))))
    have hzz : z⁻¹ * z₀ ∈ Y :=
      hXY (hU.mem_sup_of_comm_mem hR htt (mul_mem (inv_mem hzU) hz₀) hcomm)
    have := mul_mem hz hzz
    rwa [mul_inv_cancel_left] at this

theorem mem_of_fixedPointFree (hU : U3U1Data G L f t T R₂ U₁)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (htU : t ∈ normalizer (U₁ : Set G)) {ε : G}
    (hεT : ε ∈ normalizer (szT₁ L T : Set G)) (hεt : ε * t = t * ε)
    (hεR : ε ∈ normalizer (R₂ : Set G))
    (hfpf : ∀ y ∈ szT₁ L T, ε * y * ε⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T))
    {a : G} (ha : a ∈ U₁) (hεa : ε * a * ε⁻¹ * a⁻¹ ∈ R₂) : a ∈ R₂ := by
  have htt : t * t = 1 := by rw [← sq, hR.t_sq]
  have hsup : ∀ b ∈ szT₁ L T ⊔ R₂, ε * b * ε⁻¹ * b⁻¹ ∈ R₂ → b ∈ R₂ := by
    intro b hb hεb
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hb
    have hwU : w ∈ U₁ := hU.le (mem_sup_left hw)
    have hwR : w ∈ normalizer (R₂ : Set G) := centralizer_le_normalizer _ (hU.le_centralizer hwU)
    have e : ε * (w * r) * ε⁻¹ * (w * r)⁻¹ =
        (ε * w * ε⁻¹ * w⁻¹) * (w * ((ε * r * ε⁻¹) * r⁻¹) * w⁻¹) := by group
    have hr' : w * ((ε * r * ε⁻¹) * r⁻¹) * w⁻¹ ∈ R₂ :=
      (mem_normalizer_iff.mp hwR _).mp (mul_mem ((mem_normalizer_iff.mp hεR r).mp hr) (inv_mem hr))
    rw [e] at hεb
    have hεb' : ε * w * ε⁻¹ * w⁻¹ ∈ R₂ := by
      have := mul_mem hεb (inv_mem hr')
      rwa [mul_inv_cancel_right] at this
    have hεw : ε * w * ε⁻¹ * w⁻¹ ∈ szA₁ (szT₁ L T) := by
      rw [← hR.inf]
      exact mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp hεT w).mp hw) (inv_mem hw), hεb'⟩
    exact mul_mem (hR.le (hfpf w hw hεw)) hr
  have hεtε : ε * t * ε⁻¹ = t := by rw [hεt, mul_inv_cancel_right]
  have hb := hU.comm_t_mem_sup hR htU ha
  have htR : t ∈ normalizer (R₂ : Set G) := hU.normalizer_le_normalizer_R₂ htU
  have hgR : a * t * a⁻¹ ∈ normalizer (R₂ : Set G) :=
    mul_mem (mul_mem (centralizer_le_normalizer _ (hU.le_centralizer ha)) htR)
      (inv_mem (centralizer_le_normalizer _ (hU.le_centralizer ha)))
  have hεb : ε * (a * t * a⁻¹ * t⁻¹) * ε⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ ∈ R₂ := by
    have e : ε * (a * t * a⁻¹ * t⁻¹) * ε⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ =
        (ε * a * ε⁻¹) * (ε * t * ε⁻¹) * (ε * a * ε⁻¹)⁻¹ * (ε * t * ε⁻¹)⁻¹ *
          (a * t * a⁻¹ * t⁻¹)⁻¹ := by group
    rw [e, hεtε]
    have e2 : (ε * a * ε⁻¹) * t * (ε * a * ε⁻¹)⁻¹ * t⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ =
        (ε * a * ε⁻¹ * a⁻¹) * ((a * t * a⁻¹) * (ε * a * ε⁻¹ * a⁻¹)⁻¹ * (a * t * a⁻¹)⁻¹) := by
      group
    rw [e2]
    exact mul_mem hεa ((mem_normalizer_iff.mp hgR _).mp (inv_mem hεa))
  have hbR := hsup _ hb hεb
  exact hsup _ (hU.mem_sup_of_comm_mem hR htt ha hbR) hεa

section Certificates

theorem exists_torus_of_ne_three (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hf3 : f ≠ 3) :
    ∃ ε ∈ normalizer (U₁ : Set G), ε * t = t * ε ∧ (orderOf ε).Prime ∧
      (∀ a ∈ U₁, ε * a * ε⁻¹ * a⁻¹ ∈ R₂ → a ∈ R₂) ∧
      ∀ x ∈ normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G), x * t = t * x →
        Odd (orderOf x) → (¬ ∀ a ∈ U₁, x * a * x⁻¹ * a⁻¹ ∈ R₂) →
        (∀ a ∈ U₁, (x * ε * x⁻¹ * ε⁻¹) * a * (x * ε * x⁻¹ * ε⁻¹)⁻¹ * a⁻¹ ∈ R₂) →
        (∀ Y : Subgroup G, R₂ ≤ Y → Y ≤ szT₁ L T ⊔ R₂ → ε ∈ normalizer (Y : Set G) →
          x ∈ normalizer (Y : Set G) → Y = R₂ ∨ Y = szT₁ L T ⊔ R₂) ∧
        (∀ Y : Subgroup G, szT₁ L T ⊔ R₂ ≤ Y → Y ≤ U₁ → ε ∈ normalizer (Y : Set G) →
          x ∈ normalizer (Y : Set G) → Y = szT₁ L T ⊔ R₂ ∨ Y = U₁) := by
  classical
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have htU : t ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR htT
  obtain ⟨ε, hεL, hεT, hεC, hppd, hfpf⟩ := h.exists_ppd_torus_of_card_sylow hS2 hf3
  obtain ⟨-, -, -, hNA, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hεA : ε ∈ normalizer (szA L T t : Set G) := h.inf_normalizer_le_normalizer_szA ⟨hεL, hεT⟩
  have hεN : ε ∈ normalizer (U₁ : Set G) := hU.normalizer_le (hNA hεA)
  have hεt : ε * t = t * ε := mem_centralizer_iff.mp h.mem ε hεL
  have hεR : ε ∈ centralizer (R₂ : Set G) :=
    h.mem_centralizer_of_mem_borel_of_card_sylow hS2 hR hεL hεT hεC
  set p := orderOf ε with hpdef
  have hp := hppd.prime
  have hf0 : 0 < 2 * f := by have := h.two_le; omega
  have hεodd : Odd p := hp.odd_of_ne_two (hppd.ne_two hf0)
  obtain ⟨E, _, _, _, σ, hEcard, -, -, u, vc, hc, hA₁u, -, hoddsc⟩ :=
    h.exists_rootCoords_scalar_of_card_sylow hS2
  obtain ⟨s, -, hs⟩ := hoddsc ε (mem_inf.mpr ⟨hεA, hεC⟩) hεodd
  have hE : Nat.card E = 2 ^ (2 * f) := by rw [hEcard, ← pow_mul, mul_comm]
  obtain ⟨y₁, hy₁, hu₁⟩ := hc.u_surj 1
  have hsp : orderOf s = p := by
    have : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime ?_ ?_
    · have h1 := U3RootCoords.u_conj_pow hεT hs p y₁ hy₁
      rw [hpdef, pow_orderOf_eq_one, one_mul, inv_one, mul_one, hu₁, mul_one] at h1
      exact h1.symm
    · intro hs1
      have h1 : ε * y₁ * ε⁻¹ * y₁⁻¹ ∈ szA₁ (szT₁ L T) := by
        have hεy : ε * y₁ * ε⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hεT y₁).mp hy₁
        refine (hA₁u _ (mul_mem hεy (inv_mem hy₁))).mpr ?_
        rw [hc.mul_u _ hεy _ (inv_mem hy₁), hc.u_inv hy₁, hs y₁ hy₁, hs1, one_mul,
          add_neg_cancel]
      have h2 := (hA₁u y₁ hy₁).mp (hfpf y₁ hy₁ h1)
      rw [hu₁] at h2
      exact one_ne_zero h2
  have hεRN : ε ∈ normalizer (R₂ : Set G) := centralizer_le_normalizer _ hεR
  have hirr : ∀ M : AddSubgroup E, (∀ g ∈ ({ε} : Set G), ∀ y ∈ szT₁ L T, u y ∈ M →
      u (g * y * g⁻¹) ∈ M) → M = ⊥ ∨ M = ⊤ := by
    intro M hM
    refine SixNineRank.eq_bot_or_eq_top_of_mul_mem hE hp hppd.2.2 hsp M fun a ha => ?_
    obtain ⟨y, hy, rfl⟩ := hc.u_surj a
    rw [← hs y hy]
    exact hM ε rfl y hy ha
  refine ⟨ε, hεN, hεt, hp, fun a ha hεa => hU.mem_of_fixedPointFree hR htU hεT hεt hεRN hfpf ha hεa,
    fun x _ _ _ _ _ => ⟨fun Y hRY hYX hεY _ => ?_, fun Y hXY hYU hεY _ => ?_⟩⟩
  · exact eq_or_eq_of_stable_one hR hc hA₁u (P := {ε}) (fun g hg => by rw [hg]; exact hεT) hirr
      hRY hYX (fun g hg => by rw [hg]; exact hεY)
  · exact hU.eq_or_eq_of_stable_two hR htU hc hA₁u (P := {ε}) (fun g hg => by rw [hg]; exact hεT)
      (fun g hg => by rw [hg]; exact hεt) (fun g hg => by rw [hg]; exact hεRN) hirr hXY hYU
      (fun g hg => by rw [hg]; exact hεY)

theorem exists_torus_of_three (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hf3 : f = 3) :
    ∃ ε ∈ normalizer (U₁ : Set G), ε * t = t * ε ∧ (orderOf ε).Prime ∧
      (∀ a ∈ U₁, ε * a * ε⁻¹ * a⁻¹ ∈ R₂ → a ∈ R₂) ∧
      ∀ x ∈ normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G), x * t = t * x →
        Odd (orderOf x) → (¬ ∀ a ∈ U₁, x * a * x⁻¹ * a⁻¹ ∈ R₂) →
        (∀ a ∈ U₁, (x * ε * x⁻¹ * ε⁻¹) * a * (x * ε * x⁻¹ * ε⁻¹)⁻¹ * a⁻¹ ∈ R₂) →
        (∀ Y : Subgroup G, R₂ ≤ Y → Y ≤ szT₁ L T ⊔ R₂ → ε ∈ normalizer (Y : Set G) →
          x ∈ normalizer (Y : Set G) → Y = R₂ ∨ Y = szT₁ L T ⊔ R₂) ∧
        (∀ Y : Subgroup G, szT₁ L T ⊔ R₂ ≤ Y → Y ≤ U₁ → ε ∈ normalizer (Y : Set G) →
          x ∈ normalizer (Y : Set G) → Y = szT₁ L T ⊔ R₂ ∨ Y = U₁) := by
  classical
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have htU : t ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR htT
  obtain ⟨ε, hεL, hεT, hε7, hfpf⟩ := h.exists_seven_torus_of_card_sylow hS2 hf3
  obtain ⟨-, -, -, hNA, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hεA : ε ∈ normalizer (szA L T t : Set G) := h.inf_normalizer_le_normalizer_szA ⟨hεL, hεT⟩
  have hεN : ε ∈ normalizer (U₁ : Set G) := hU.normalizer_le (hNA hεA)
  have hεt : ε * t = t * ε := mem_centralizer_iff.mp h.mem ε hεL
  have hεRN : ε ∈ normalizer (R₂ : Set G) := hNR hεA
  obtain ⟨E, _, _, _, σ, hEcard, hσ, -, u, vc, hc, hA₁u, -, hoddsc⟩ :=
    h.exists_rootCoords_scalar_of_card_sylow hS2
  have hE : Nat.card E = 2 ^ 6 := by rw [hEcard, hf3]; norm_num
  have hconjε : ∀ y ∈ szT₁ L T, ε * y * ε⁻¹ ∈ szT₁ L T := fun y hy =>
    (mem_normalizer_iff.mp hεT y).mp hy
  have hεA₁ : ε ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    CFSG.SeitzReduction.RankOne.normalizer_le_normalizer_inf_centralizer (szT₁ L T) hεT
  obtain ⟨φ, hφ⟩ := hc.exists_addEquiv_conj hεT
    (fun y hy hu => (hA₁u _ (hconjε y hy)).mp
      ((mem_normalizer_iff.mp hεA₁ y).mp ((hA₁u y hy).mpr hu)))
    (fun y hy hu => (hA₁u y hy).mp (by
      have h1 := (mem_normalizer_iff''.mp hεA₁ _).mp ((hA₁u _ (hconjε y hy)).mpr hu)
      rwa [show ε⁻¹ * (ε * y * ε⁻¹) * ε = y by group] at h1))
  have hφiter : ∀ k : ℕ, ∀ y ∈ szT₁ L T, u (ε ^ k * y * (ε ^ k)⁻¹) = (φ : E → E)^[k] (u y) := by
    intro k
    induction k with
    | zero => intro y hy; simp
    | succ k ih =>
      intro y hy
      have hk : ε ^ k * y * (ε ^ k)⁻¹ ∈ szT₁ L T :=
        (mem_normalizer_iff.mp (pow_mem hεT k) y).mp hy
      rw [Function.iterate_succ_apply', ← ih y hy, ← hφ _ hk]
      congr 1
      rw [pow_succ']
      group
  have hφ7 : ∀ a, (φ : E → E)^[7] a = a := by
    intro a
    obtain ⟨y, hy, rfl⟩ := hc.u_surj a
    rw [← hφiter 7 y hy, ← hε7, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  have hφfix : ∀ a, φ a = a → a = 0 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := hc.u_surj a
    rw [← hφ y hy] at ha
    have h1 : ε * y * ε⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
      refine (hA₁u _ (mul_mem (hconjε y hy) (inv_mem hy))).mpr ?_
      rw [hc.mul_u _ (hconjε y hy) _ (inv_mem hy), hc.u_inv hy, ha, add_neg_cancel]
    exact (hA₁u y hy).mp (hfpf y hy h1)
  refine ⟨ε, hεN, hεt, by rw [hε7]; norm_num,
    fun a ha hεa => hU.mem_of_fixedPointFree hR htU hεT hεt hεRN hfpf ha hεa,
    fun x hx hxt hodd hxnt _ => ?_⟩
  obtain ⟨hxN, hxR⟩ := mem_inf.mp hx
  have hxT : x ∈ normalizer (szT₁ L T : Set G) := hU.mem_normalizer_szT₁_of_comm hR hxN hxt
  have hxRN : x ∈ normalizer (R₂ : Set G) := centralizer_le_normalizer _ hxR
  have hxA : x ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G) := by
    have hxC : x ∈ centralizer (szA₁ (szT₁ L T) : Set G) :=
      mem_centralizer_iff.mpr fun a ha => mem_centralizer_iff.mp hxR a (hR.le ha)
    refine mem_inf.mpr ⟨centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz => ?_), hxC⟩
    have hle : szA L T t ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr
        (mem_centralizer_singleton_iff.mpr hxt.symm))
      exact mem_centralizer_iff.mp hxC a ha
    exact mem_centralizer_singleton_iff.mp (hle hz)
  obtain ⟨s, hs1, hs⟩ := hoddsc x hxA hodd
  have hs9 : s ^ 9 = 1 := by
    rw [hσ, hf3] at hs1
    rw [show (9 : ℕ) = 2 ^ 3 + 1 by norm_num, pow_succ, mul_comm]
    exact hs1
  have hsne : s ≠ 1 := by
    intro hs1'
    apply hxnt
    refine hU.forall_comm_mem_of_forall_comm_mem_szT₁ hR htU hxN hxR hxt hodd fun y hy => ?_
    have hxyT : x * y * x⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hxT y).mp hy
    exact hR.le ((hA₁u _ (mul_mem hxyT (inv_mem hy))).mpr (by
      rw [hc.mul_u _ hxyT _ (inv_mem hy), hc.u_inv hy, hs y hy, hs1', one_mul, add_neg_cancel]))
  have hsiter : ∀ (k : ℕ) (a : E), (fun b => s * b)^[k] a = s ^ k * a := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih => intro a; rw [Function.iterate_succ_apply', ih, pow_succ', mul_assoc]
  have hirr : ∀ M : AddSubgroup E, (∀ g ∈ ({ε, x} : Set G), ∀ y ∈ szT₁ L T, u y ∈ M →
      u (g * y * g⁻¹) ∈ M) → M = ⊥ ∨ M = ⊤ := by
    intro M hM
    have hMφ : ∀ a ∈ M, φ a ∈ M := fun a ha => by
      obtain ⟨y, hy, rfl⟩ := hc.u_surj a
      rw [← hφ y hy]
      exact hM ε (Set.mem_insert _ _) y hy ha
    have hMs : ∀ a ∈ M, s * a ∈ M := fun a ha => by
      obtain ⟨y, hy, rfl⟩ := hc.u_surj a
      rw [← hs y hy]
      exact hM x (Set.mem_insert_of_mem _ rfl) y hy ha
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have h7 := SixNineRank.card_modEq_one_of_fixedPointFree M (p := 7) (n := 1) φ hMφ
      (map_zero φ) (fun a _ => by rw [pow_one]; exact hφ7 a) (fun a _ ha => hφfix a ha)
    have h3 := SixNineRank.card_modEq_one_of_fixedPointFree M (p := 3) (n := 2)
      (fun b => s * b) hMs (mul_zero s) (fun a _ => by rw [hsiter, show 3 ^ 2 = 9 by norm_num,
        hs9, one_mul])
      (fun a _ ha => by
        have h0 : (s - 1) * a = 0 := by rw [sub_mul, one_mul]; exact sub_eq_zero.mpr ha
        rcases mul_eq_zero.mp h0 with h0 | h0
        · exact absurd (sub_eq_zero.mp h0) hsne
        · exact h0)
    exact SixNineRank.eq_bot_or_eq_top_of_card_modEq hE M h7 h3
  have hPT : ∀ g ∈ ({ε, x} : Set G), g ∈ normalizer (szT₁ L T : Set G) := by
    rintro g (rfl | rfl)
    · exact hεT
    · exact hxT
  refine ⟨fun Y hRY hYX hεY hxY => ?_, fun Y hXY hYU hεY hxY => ?_⟩
  · refine eq_or_eq_of_stable_one hR hc hA₁u hPT hirr hRY hYX ?_
    rintro g (rfl | rfl)
    · exact hεY
    · exact hxY
  · refine hU.eq_or_eq_of_stable_two hR htU hc hA₁u hPT ?_ ?_ hirr hXY hYU ?_
    · rintro g (rfl | rfl)
      · exact hεt
      · exact hxt
    · rintro g (rfl | rfl)
      · exact hεRN
      · exact hxRN
    · rintro g (rfl | rfl)
      · exact hεY
      · exact hxY

end Certificates

end U3U1Data

section Certificates

theorem u3SixNineTorusInput_holds : U3SixNineTorusInput := by
  intro G _ _ L f t T R₂ U₁ h hS2 hR hU
  by_cases hf3 : f = 3
  · exact hU.exists_torus_of_three h hS2 hR hf3
  · exact hU.exists_torus_of_ne_three h hS2 hR hf3

theorem u3SixNineRankInput_of_rankCountInput (hGI : SixNineRank.RankCountInput) :
    U3SixNineRankInput :=
  u3SixNineRankInput_of_rankCount hGI u3SixNineTorusInput_holds

end Certificates

section Certificates

theorem u3SixNineFourInput_of_rankCountInput (hGI : SixNineRank.RankCountInput) :
    U3SixNineFourInput :=
  u3SixNineFourInput_of_rank (u3SixNineRankInput_of_rankCountInput hGI)

end Certificates

end CFSG.SeitzReduction.RankOne
