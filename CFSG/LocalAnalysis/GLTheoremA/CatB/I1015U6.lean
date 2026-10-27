module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015SU6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti

namespace I1015

theorem three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) + 1 = 2 * 4 ^ k + 1 := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2]
  omega

theorem lieIndex_isU6n {S : Type} [Group S] {n : ℕ} (h : catalogIs S (S10.isU6n n)) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 5 q).Valid), q.p = 2 ∧ q.exponent = n ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP.1, hP.2, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem lieIndex_isTE6n {S : Type} [Group S] {n : ℕ} (h : catalogIs S (S10.isTE6n n)) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid), q.p = 2 ∧ q.exponent = n ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | twistedE6 q => exact ⟨q, hv, hP.1, hP.2, ⟨e⟩⟩
  | _ => exact hP.elim

theorem stated_su6_of_catalog {S : Type} [Group S] {n : ℕ} (h : catalogIs S (S10.isU6n n)) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = (2 ^ n) ^ 2 ∧
      Nonempty (S ≃* StatedProj (StatedSU 6 (2 ^ n) K₀)) := by
  obtain ⟨q, hv, hp, hf, ⟨e⟩⟩ := lieIndex_isU6n h
  have hm := lieModel_twistedA' 5 q hv e
  rw [hp, hf] at hm
  obtain ⟨-, K₀, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  exact ⟨K₀, inferInstance, inferInstance, hK, ⟨e'⟩⟩

section Table

open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem card_dvd_three_of_dvd {Z : Type} [Group Z] [Finite Z] (hZ : IsPGroup 3 Z) {m : ℕ}
    (hm : m ∣ 24) (hd : Nat.card Z ∣ m) : Nat.card Z ∣ 3 := by
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have h24 : 3 ^ k ∣ 24 := hk ▸ hd.trans hm
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ∣ 24 := (pow_dvd_pow 3 h).trans h24
    omega
  rw [hk]
  interval_cases k <;> simp

theorem orders_PSU6_dvd (f : ℕ) :
    (genericOrders .PSU 6 2 f).1 * (genericOrders .PSU 6 2 f).2 *
      ((exceptionalOrders .PSU 6 2 f).1 * (exceptionalOrders .PSU 6 2 f).2) ∣ 24 := by
  have h1 : (genericOrders .PSU 6 2 f).1 ∣ 6 := Nat.gcd_dvd_left _ _
  have h2 : (genericOrders .PSU 6 2 f).2 = 1 := rfl
  have h3 : (exceptionalOrders .PSU 6 2 f).1 ∣ 2 ∧ (exceptionalOrders .PSU 6 2 f).2 ∣ 2 := by
    by_cases hf : f = 1
    · subst hf
      exact ⟨by decide, by decide⟩
    · have : exceptionalOrders .PSU 6 2 f = (1, 1) := by
        unfold exceptionalOrders
        split <;> simp_all
      rw [this]
      exact ⟨one_dvd _, one_dvd _⟩
  rw [h2, mul_one]
  exact (Nat.mul_dvd_mul h1 (Nat.mul_dvd_mul h3.1 h3.2)).trans (by norm_num)

theorem orders_twistedE6_dvd (f : ℕ) :
    (genericOrders .twistedE6 0 2 f).1 * (genericOrders .twistedE6 0 2 f).2 *
      ((exceptionalOrders .twistedE6 0 2 f).1 * (exceptionalOrders .twistedE6 0 2 f).2) ∣ 24 := by
  have h1 : (genericOrders .twistedE6 0 2 f).1 ∣ 3 := Nat.gcd_dvd_left _ _
  have h2 : (genericOrders .twistedE6 0 2 f).2 = 1 := rfl
  have h3 : (exceptionalOrders .twistedE6 0 2 f).1 ∣ 2 ∧
      (exceptionalOrders .twistedE6 0 2 f).2 ∣ 2 := by
    by_cases hf : f = 1
    · subst hf
      exact ⟨by decide, by decide⟩
    · have : exceptionalOrders .twistedE6 0 2 f = (1, 1) := by
        unfold exceptionalOrders
        split <;> simp_all
      rw [this]
      exact ⟨one_dvd _, one_dvd _⟩
  rw [h2, mul_one]
  exact (Nat.mul_dvd_mul h1 (Nat.mul_dvd_mul h3.1 h3.2)).trans (by norm_num)

theorem card_center_dvd_three_PSU (hGA : GriessAllModelsStatement) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (hZ : IsPGroup 3 (Subgroup.center Q)) {f : ℕ}
    (hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSU 6 2 f) :
    Nat.card (Subgroup.center Q) ∣ 3 := by
  have hne : (genericOrders .PSU 6 2 f).1 * (genericOrders .PSU 6 2 f).2 *
      ((exceptionalOrders .PSU 6 2 f).1 * (exceptionalOrders .PSU 6 2 f).2) ≠ 0 := fun h0 => by
    have := orders_PSU6_dvd f
    rw [h0] at this
    exact absurd (Nat.eq_zero_of_zero_dvd this) (by norm_num)
  have hd := card_center_dvd_of_table hGA hQ hm (a := (genericOrders .PSU 6 2 f).1)
    (b := (genericOrders .PSU 6 2 f).2) (c := (exceptionalOrders .PSU 6 2 f).1)
    (d := (exceptionalOrders .PSU 6 2 f).2) rfl rfl hne
  exact card_dvd_three_of_dvd hZ (orders_PSU6_dvd f) hd

theorem card_center_dvd_three_E6 (hGA : GriessAllModelsStatement) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (hZ : IsPGroup 3 (Subgroup.center Q)) {f : ℕ}
    (hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .twistedE6 0 2 f) :
    Nat.card (Subgroup.center Q) ∣ 3 := by
  have hne : (genericOrders .twistedE6 0 2 f).1 * (genericOrders .twistedE6 0 2 f).2 *
      ((exceptionalOrders .twistedE6 0 2 f).1 * (exceptionalOrders .twistedE6 0 2 f).2) ≠ 0 :=
    fun h0 => by
      have := orders_twistedE6_dvd f
      rw [h0] at this
      exact absurd (Nat.eq_zero_of_zero_dvd this) (by norm_num)
  have hd := card_center_dvd_of_table hGA hQ hm (a := (genericOrders .twistedE6 0 2 f).1)
    (b := (genericOrders .twistedE6 0 2 f).2) (c := (exceptionalOrders .twistedE6 0 2 f).1)
    (d := (exceptionalOrders .twistedE6 0 2 f).2) rfl rfl hne
  exact card_dvd_three_of_dvd hZ (orders_twistedE6_dvd f) hd

end Table

section Component

variable {G : Type} [Group G] [Finite G]

theorem u6_exists_E_T (hGA : GriessAllModelsStatement) {X K : Subgroup G} {n : ℕ} (hn : Odd n)
    (hK : GLAPComponent 3 X K) (hcat : catalogIs (PSimple 3 K) (S10.isU6n n)) :
    ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧
      Nat.card E = 27 * Nat.card (Subgroup.center (PQuot 3 K)) ∧ T ≤ K ∧ IsPGroup 2 T ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨K₀, _, _, hK₀, ⟨θ⟩⟩ := stated_su6_of_catalog hcat
  have h3 : 3 ∣ 2 ^ n + 1 := three_dvd_two_pow_add_one hn
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  let β : PQuot 3 K →* StatedProj (StatedSU 6 (2 ^ n) K₀) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (PQuot 3 K)))
  have hker : β.ker = Subgroup.center (PQuot 3 K) := by
    rw [MonoidHom.ker_comp_of_injective _ θ.toMonoidHom θ.injective]
    exact QuotientGroup.ker_mk' _
  have hβ : Function.Surjective β := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hβp : IsPGroup 3 β.ker := by
    rw [hker]
    exact CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three K
  obtain ⟨Eb, s, hEb, hEbc, hs2, hβs, hc⟩ :=
    exists_Ebar_s_of_cover hGA h3 hK₀ ⟨hq.1⟩ β hβ hker.le hβp
  have hs1 : s ≠ 1 := fun h => hβs (by rw [h, map_one])
  obtain ⟨E, T, W, -, hEK, hEe, hEc, -, -, hTK, hT2, hTn, hEN⟩ := exists_E_T_pQuot K hEb hs2 hs1 hc
  exact ⟨E, T, hEK, hEe, by rw [hEc, hEbc, hker], hTK, hT2, hTn, hEN⟩

theorem card_center_pQuot_dvd_three (hGA : GriessAllModelsStatement) {X K : Subgroup G} {n : ℕ}
    (hK : GLAPComponent 3 X K)
    (hcat : catalogIs (PSimple 3 K) (S10.isU6n n) ∨ catalogIs (PSimple 3 K) (S10.isTE6n n)) :
    Nat.card (Subgroup.center (PQuot 3 K)) ∣ 3 := by
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hZ : IsPGroup 3 (Subgroup.center (PQuot 3 K)) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three K
  rcases hcat with hc | hc
  · obtain ⟨q, hv, hp, hf, ⟨e⟩⟩ := lieIndex_isU6n hc
    have hm := lieModel_twistedA' 5 q hv e
    rw [hp, hf] at hm
    exact card_center_dvd_three_PSU hGA hq hZ hm
  · obtain ⟨q, hv, hp, hf, ⟨e⟩⟩ := lieIndex_isTE6n hc
    have hm : CFSG.Models.LieModel (PSimple 3 K) .twistedE6 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e
    rw [hp, hf] at hm
    exact card_center_dvd_three_E6 hGA hq hZ hm

theorem exists_sub_card_pow {E : Subgroup G} (hE : IsElemAbelian 3 E) {k : ℕ}
    (h : 3 ^ k ∣ Nat.card E) :
    ∃ E' : Subgroup G, E' ≤ E ∧ IsElemAbelian 3 E' ∧ Nat.card E' = 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := ↥E) h
  refine ⟨K'.map E.subtype, Subgroup.map_subtype_le K', hE.mono (Subgroup.map_subtype_le K'), ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK']

theorem exists_E_T_of_pQuot_rank (K : Subgroup G) {k : ℕ}
    (h : ∃ Eb Wb : Subgroup (PQuot 3 K), IsElemAbelian 3 Eb ∧ Nat.card Eb = 3 ^ k ∧ IsPGroup 2 Wb ∧
      Wb ≠ ⊥ ∧ Eb ≤ Subgroup.normalizer (Wb : Set (PQuot 3 K))) :
    ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧ T ≤ K ∧ IsPGroup 2 T ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨Eb, Wb, hE, hc, hW2, hW1, hEW⟩ := h
  obtain ⟨E, T, W, -, hEK, hEe, hEc, -, -, hTK, hT2, hTn, hEN⟩ :=
    exists_E_T_pQuot_of_sub K hE hW2 hW1 hEW
  exact ⟨E, T, hEK, hEe, hEc.trans hc, hTK, hT2, hTn, hEN⟩

end Component

abbrev TE6Rank : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → IsPGroup 3 (Subgroup.center Q) →
    ∀ n : ℕ, Odd n → catalogIs (Q ⧸ Subgroup.center Q) (S10.isTE6n n) →
      ∃ Eb Wb : Subgroup Q, IsElemAbelian 3 Eb ∧ Nat.card Eb = 3 ^ 4 * Nat.card (Subgroup.center Q) ∧
        IsPGroup 2 Wb ∧ Wb ≠ ⊥ ∧ Eb ≤ Subgroup.normalizer (Wb : Set Q)

theorem te6_exists_E_T (hR : TE6Rank) {G : Type} [Group G] [Finite G] {X K : Subgroup G} {n : ℕ}
    (hn : Odd n) (hK : GLAPComponent 3 X K) (hcat : catalogIs (PSimple 3 K) (S10.isTE6n n)) :
    ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 * Nat.card (Subgroup.center (PQuot 3 K)) ∧ T ≤ K ∧ IsPGroup 2 T ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hZ : IsPGroup 3 (Subgroup.center (PQuot 3 K)) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three K
  obtain ⟨Eb, Wb, hE, hc, hW2, hW1, hEW⟩ := hR _ hq hZ n hn hcat
  obtain ⟨E, T, W, -, hEK, hEe, hEc, -, -, hTK, hT2, hTn, hEN⟩ :=
    exists_E_T_pQuot_of_sub K hE hW2 hW1 hEW
  exact ⟨E, T, hEK, hEe, hEc.trans hc, hTK, hT2, hTn, hEN⟩

end I1015

end CFSG.LocalAnalysis.GLTheoremA.CatB
