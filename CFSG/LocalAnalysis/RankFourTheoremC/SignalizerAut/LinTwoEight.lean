module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoL28

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.AGLEmbedding.KFactProofs.L28Local CFSG.Quasithin.F6.L28Res

open scoped Pointwise in
theorem exists_sylow_normalized_of_orderOf_prime {G : Type*} [Group G] [Finite G]
    {Y : Subgroup G} {a : G} {r : ℕ} [Fact r.Prime] (ha : orderOf a = r)
    (haY : a ∈ normalizer (Y : Set G)) (hr : ¬ r ∣ Nat.card Y) (q : ℕ) [Fact q.Prime] :
    ∃ Q : Subgroup G, Q ≤ Y ∧ IsPGroup q Q ∧ (q ∣ Nat.card Y → Q ≠ ⊥) ∧
      ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := by
  let n : normalizer (Y : Set G) := ⟨a, haY⟩
  have hn : orderOf n = r := by rw [Subgroup.orderOf_mk]; exact ha
  have hA : IsPGroup r (Subgroup.zpowers n) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hn, pow_one])
  have hcard : ¬ r ∣ Nat.card (Sylow q Y) := by
    intro h
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q Y))
    exact hr (h.trans ((P.card_dvd_index).trans (Subgroup.index_dvd_card _)))
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q Y) hcard
  have hnP : n • P = P := hP ⟨n, Subgroup.mem_zpowers n⟩
  have hnP' : n • (P : Subgroup Y) = P := by rw [← Sylow.pointwise_smul_def, hnP]
  refine ⟨(P : Subgroup Y).map Y.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _,
    fun hq => ?_, fun x hx => ?_⟩
  · exact fun h => P.ne_bot_of_dvd_card hq
      ((Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).1 h)
  · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨n • y, hnP' ▸ Subgroup.smul_mem_pointwise_smul y n _ hy, rfl⟩

set_option synthInstance.maxSize 1024 in
private theorem finite_check_seven :
    ∀ s ∈ T0list, s * s * s = 1 → s ≠ 1 → ∀ u : G8, u ≠ 1 → u ^ 7 = 1 →
      s * u * s⁻¹ * u = u * (s * u * s⁻¹) → False := by
  decide +kernel

private theorem not_commute_conj_seven {K : Type} [Group K] (ε : K ≃* G8) {t u : K}
    (ht : orderOf t = 3) (hu : orderOf u = 7) :
    t * u * t⁻¹ * u ≠ u * (t * u * t⁻¹) := by
  intro hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht3 : t * t * t = 1 := by simpa [pow_succ, mul_assoc, ht] using pow_orderOf_eq_one t
  have hu7 : u ^ 7 = 1 := by simpa [hu] using pow_orderOf_eq_one u
  have ht1 : t ≠ 1 := by rintro rfl; simp at ht
  have hu1 : u ≠ 1 := by rintro rfl; simp at hu
  have hp : IsPGroup 3 (Subgroup.zpowers (ε t)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ε.orderOf_eq, ht]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_of_card_nine card_G8 (card_sylow_three (MulEquiv.refl G8) Q)
    card_T0
  let φ : K ≃* G8 := ε.trans (MulAut.conj g)
  have hs : φ t ∈ T0list :=
    mem_T0_iff.1 ((hg (ε t)).1 (hQ (Subgroup.mem_zpowers (ε t))))
  refine finite_check_seven (φ t) hs ?_ ?_ (φ u) ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, ht3, map_one]
  · exact fun h => ht1 (φ.injective (h.trans (map_one φ).symm))
  · exact fun h => hu1 (φ.injective (h.trans (map_one φ).symm))
  · rw [← map_pow, hu7, map_one]
  · simpa only [map_mul, map_inv] using congrArg φ hc

private theorem nonempty_equiv_of_isLinTwoIndex {K : Type} [Group K]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex 2 3 d)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) : Nonempty (K ≃* G8) :=
  let ⟨q, hq, hqp, hqe⟩ := hd
  nonempty_equiv_G8 ⟨d, Or.inl ⟨rfl, q, hqp, hqe, hq⟩, he⟩

private theorem conj_injective_of_equiv {K : Type} [Group K] (ε : K ≃* G8) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : ∀ y : G8, ε g * y = y * ε g := fun y => by
    obtain ⟨x, rfl⟩ := ε.surjective y
    have h := congrArg (fun α : MulAut K => α x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [← map_mul, ← map_mul]
    congr 1
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  exact ε.injective (by rw [map_one]; exact eq_one_of_commute _ (hc ga) (hc gb))

private theorem eq_bot_of_normalizes {K : Type} [Group K] [Finite K]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex 2 3 d)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) {k : K} (hk : orderOf k = 3)
    {Y : Subgroup K} (hY : ¬ 3 ∣ Nat.card Y) (hkY : k ∈ normalizer (Y : Set K)) : Y = ⊥ := by
  obtain ⟨ε⟩ := nonempty_equiv_of_isLinTwoIndex hd he
  have hKcard : Nat.card K = 504 := by rw [Nat.card_congr ε.toEquiv, card_G8]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have h1 : Nat.card Y ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨r, hr, hrY⟩ := Nat.exists_prime_and_dvd h1
  have : Fact r.Prime := ⟨hr⟩
  have hr504 : r ∣ 2 ^ 3 * 3 ^ 2 * 7 := by
    have : r ∣ 504 := hKcard ▸ hrY.trans (Subgroup.card_subgroup_dvd_card Y)
    simpa using this
  have hr3 : r ≠ 3 := fun h => hY (h ▸ hrY)
  have hr' : r = 2 ∨ r = 7 := by
    rcases (Nat.Prime.dvd_mul hr).1 hr504 with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
          (hr.dvd_of_dvd_pow h)) hr3
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h)
  obtain ⟨Q, -, hQp, hQne', hQk⟩ := exists_sylow_normalized_of_orderOf_prime hk hkY hY r
  have hQne := hQne' hrY
  rcases hr' with rfl | rfl
  · haveI : Finite (MulAut K) :=
      Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
    have hU : IsPGroup 2 (Q.map (MulAut.conj : K →* MulAut K)) := hQp.map _
    have hN : MulAut.conj k ∈ normalizer
        ((Q.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) : Set (MulAut K)) := by
      refine Subgroup.mem_normalizer_fintype fun f hf => ?_
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hf
      exact ⟨k * x * k⁻¹, hQk x hx, by simp⟩
    obtain ⟨q, hq, hqp, hqe⟩ := hd
    have := kFactCaseTwoNoTwoL28 3 K ⟨rfl, d, ⟨q, hqp, hqe, hq⟩, he⟩ k hk _ hU hN
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective _ (conj_injective_of_equiv ε)).1 this)
  · obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hQp
    have hQ504 : Nat.card Q ∣ 504 := hKcard ▸ Subgroup.card_subgroup_dvd_card Q
    have hm1 : m = 1 := by
      rcases m with _ | _ | m
      · exact absurd (Subgroup.card_eq_one.1 (by simpa using hm)) hQne
      · rfl
      · exfalso
        have : 7 ^ 2 ∣ 504 := (pow_dvd_pow 7 (by omega)).trans (hm ▸ hQ504)
        omega
    have hQ7 : Nat.card Q = 7 := by rw [hm, hm1]; norm_num
    have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
      have := (isCyclic_of_prime_card hQ7).isMulCommutative
      intro x hx y hy
      exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    obtain ⟨⟨u, huQ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hu7 : u ^ 7 = 1 := by
      simpa [hQ7] using congrArg Subtype.val (pow_card_eq_one' (G := Q) (x := ⟨u, huQ⟩))
    exact not_commute_conj_seven ε hk (orderOf_eq_prime hu7 hu1')
      (hcomm u huQ _ (hQk u huQ)).symm

theorem signalizerAutAt_linTwoEight {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hp : p = 3)
    (hd : IsLinTwoIndex 2 3 d) : SignalizerAutAt p (.lie d) := by
  subst hp
  intro K _ _ he B Y hB hBc hY hBY _
  obtain ⟨ε⟩ := nonempty_equiv_of_isLinTwoIndex hd he
  have hKcard : Nat.card K = 504 := by rw [Nat.card_congr ε.toEquiv, card_G8]
  have hAut : Nat.card (MulAut K) = 1512 := by
    rw [Nat.card_congr (MulAut.congr ε).toEquiv]
    exact card_mulAut
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_equiv ε
  set I : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range
  haveI : I.Normal := L28Data.normal_range_conj K
  have hIcard : Nat.card I = 504 := by
    rw [← hKcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hIidx : I.index = 3 := by
    have h1 := I.card_mul_index
    rw [hIcard, hAut] at h1
    omega
  have hYI : Y ≤ I := by
    intro f hf
    have hcop : Nat.Coprime 3 (orderOf f) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Y hf) hY
    have hf3 : f ^ 3 ∈ I := by simpa [hIidx] using Subgroup.pow_index_mem I f
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact I.pow_mem hf3 m
  let φ : B →* MulAut K ⧸ I := (QuotientGroup.mk' I).comp B.subtype
  have hker : φ.ker ≠ ⊥ := by
    intro h
    have hinjφ : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
    have h1 := Nat.card_le_card_of_injective φ hinjφ
    rw [hBc] at h1
    have h3 : Nat.card (MulAut K ⧸ I) ≤ 3 := hIidx.le
    omega
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hker
  have hb1 : ((b : B) : MulAut K) ≠ 1 := fun h => hb (Subtype.ext (Subtype.ext h))
  obtain ⟨z, hz⟩ : ((b : B) : MulAut K) ∈ I := (QuotientGroup.eq_one_iff _).1 b.2
  have hz3 : z ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hz, map_one]
    exact hB.2 _ (b : B).2
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hb1 (by rw [← hz, map_one])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  set Y' : Subgroup K := Y.comap (MulAut.conj : K →* MulAut K)
  have hmapY : Y'.map (MulAut.conj : K →* MulAut K) = Y := Subgroup.map_comap_eq_self hYI
  have hY'card : Nat.card Y' = Nat.card Y := by
    have := Subgroup.card_map_of_injective (f := (MulAut.conj : K →* MulAut K)) (K := Y') hinj
    rw [hmapY] at this
    exact this.symm
  have hzY' : z ∈ normalizer (Y' : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hbN := Subgroup.mem_normalizer_iff.1 (hBY (b : B).2) (MulAut.conj w)
    have hconj : MulAut.conj (z * w * z⁻¹) =
        ((b : B) : MulAut K) * MulAut.conj w * ((b : B) : MulAut K)⁻¹ := by
      rw [← hz, map_mul, map_mul, map_inv]
    show MulAut.conj w ∈ Y ↔ MulAut.conj (z * w * z⁻¹) ∈ Y
    rw [hconj]
    exact hbN
  have hY'bot : Y' = ⊥ :=
    eq_bot_of_normalizes hd he hzord
      (by rw [hY'card]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hY) hzY'
  have hYbot : Y = ⊥ := by
    rw [← hmapY, hY'bot, Subgroup.map_bot]
  intro w _
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [hYbot] at hh
  rw [Subgroup.mem_bot.1 hh]
  simp

end CFSG.LocalAnalysis.RankFourTheoremC
