module

public import CFSG.GroupActions.PrimitiveNormal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOneAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open MulAction Subgroup

variable {X Ω : Type*} [Group X]

theorem exists_minimal_normal [Finite X] [Nontrivial X] :
    ∃ N : Subgroup X, N.Normal ∧ N ≠ ⊥ ∧
      ∀ M : Subgroup X, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
  classical
  have hne : ∃ n, ∃ N : Subgroup X, N.Normal ∧ N ≠ ⊥ ∧ Nat.card N = n :=
    ⟨_, ⊤, inferInstance, top_ne_bot, rfl⟩
  obtain ⟨N, hN, hN1, hNn⟩ := Nat.find_spec hne
  refine ⟨N, hN, hN1, fun M hM hMN => ?_⟩
  by_cases hMb : M = ⊥
  · exact Or.inl hMb
  · right
    have hle : Nat.find hne ≤ Nat.card M := Nat.find_min' hne ⟨M, hM, hMb, rfl⟩
    exact eq_of_le_of_card_ge hMN (hNn ▸ hle)

theorem card_mul_card_dvd_of_inf_eq_bot [Finite X] {N M : Subgroup X} [N.Normal]
    (h : N ⊓ M = ⊥) : Nat.card N * Nat.card M ∣ Nat.card X := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp M.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro m hm
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hm
    have hmem : (m : X) ∈ N ⊓ M := ⟨hm, m.2⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).2 (Subtype.ext hmem)
  have h1 : Nat.card M ∣ Nat.card (X ⧸ N) := Subgroup.card_dvd_of_injective _ hinj
  rw [← N.card_mul_index, Subgroup.index_eq_card]
  exact Nat.mul_dvd_mul_left _ h1

variable [MulAction X Ω]

theorem card_dvd_card_of_isPretransitive [Finite X] [Nonempty Ω] (N : Subgroup X)
    [IsPretransitive N Ω] : Nat.card Ω ∣ Nat.card N := by
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  rw [← index_stabilizer_of_transitive N ω]
  exact (stabilizer N ω).index_dvd_card

theorem card_eq_of_isMulCommutative [FaithfulSMul X Ω] [Nonempty Ω] (N : Subgroup X)
    [IsMulCommutative N] [IsPretransitive N Ω] : Nat.card N = Nat.card Ω := by
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hreg := ProperTwoGeneratedCore.LocalCriterionAffineRankOne.abelian_pretransitive_regular
    (F := X) (Λ := Ω) N
  refine Nat.card_congr (Equiv.ofBijective (fun n : N => n • ω) ⟨fun n n' hnn => ?_, fun b => ?_⟩)
  · obtain ⟨m, -, hm⟩ := hreg ω (n • ω)
    exact (hm n rfl).trans (hm n' hnn.symm).symm
  · obtain ⟨n, hn, -⟩ := hreg ω b
    exact ⟨n, hn⟩

theorem exists_simple_normal_of_isPreprimitive [Finite X] [Finite Ω] [Nonempty Ω]
    [FaithfulSMul X Ω] [IsPreprimitive X Ω] {p : ℕ} (hp : p.Prime) (hpΩ : p ∣ Nat.card Ω)
    (hp2 : ¬ p ^ 2 ∣ Nat.card X) (hΩ : ¬ IsPrimePow (Nat.card Ω)) :
    ∃ T : Subgroup X, T.Normal ∧ IsSimpleGroup T ∧ (∃ a b : T, a * b ≠ b * a) ∧
      Nat.card Ω ∣ Nat.card T ∧ (∀ N : Subgroup X, N.Normal → N ≠ ⊥ → T ≤ N) ∧
      centralizer (T : Set X) = ⊥ := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hΩ0 : Nat.card Ω ≠ 0 := Nat.card_pos.ne'
  have hΩ2 : 1 < Nat.card Ω := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hΩ0) hpΩ)
  have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩ2
  have : Nontrivial X := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
    obtain ⟨g, hg⟩ := exists_smul_eq X a b
    refine ⟨⟨g, 1, fun h => hab ?_⟩⟩
    rw [← hg, h, one_smul]
  obtain ⟨N, hN, hN1, hmin⟩ := exists_minimal_normal (X := X)
  have htrans : ∀ M : Subgroup X, M.Normal → M ≠ ⊥ → Nat.card Ω ∣ Nat.card M := by
    intro M hM hM1
    have := GroupActions.isPretransitive_of_normal_of_isPreprimitive (G := X) (X := Ω) hM1
    exact card_dvd_card_of_isPretransitive M
  have hpN : p ∣ Nat.card N := hpΩ.trans (htrans N hN hN1)
  have huniq : ∀ M : Subgroup X, M.Normal → M ≠ ⊥ → N ≤ M := by
    intro M hM hM1
    rcases hmin (N ⊓ M) (Subgroup.normal_inf_normal N M) inf_le_left with h | h
    · exfalso
      apply hp2
      rw [sq]
      exact (Nat.mul_dvd_mul hpN (hpΩ.trans (htrans M hM hM1))).trans
        (card_mul_card_dvd_of_inf_eq_bot h)
    · exact h ▸ inf_le_right
  have hnonab : ∃ a b : N, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative N := ⟨⟨fun a b => hcomm a b⟩⟩
    have := GroupActions.isPretransitive_of_normal_of_isPreprimitive (G := X) (X := Ω) hN1
    have hcardN : Nat.card N = Nat.card Ω := card_eq_of_isMulCommutative N
    have hN1' : Nat.card N ≠ 1 := by omega
    obtain ⟨q, hq, hqN⟩ := Nat.exists_prime_and_dvd hN1'
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨P⟩ : Nonempty (Sylow q N) := inferInstance
    have hPn : (P : Subgroup N).Normal :=
      ⟨fun x hx g => by rw [hcomm g x, mul_inv_cancel_right]; exact hx⟩
    have hPchar : (P : Subgroup N).Characteristic := Sylow.characteristic_of_normal P hPn
    have hPX : ((P : Subgroup N).map N.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hP1 : (P : Subgroup N).map N.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective]
      intro hb
      have h1 := P.dvd_card_of_dvd_card hqN
      rw [hb, Subgroup.card_bot] at h1
      exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
    rcases hmin _ hPX (map_subtype_le _) with h | h
    · exact hP1 h
    · have hPtop : (P : Subgroup N) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : (x : X) ∈ (P : Subgroup N).map N.subtype := by rw [h]; exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        rwa [← Subtype.ext hyx]
      have hqgrp : IsPGroup q N := fun x => by
        obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hPtop ▸ Subgroup.mem_top x⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hqgrp
      apply hΩ
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, pow_zero] at hk
          omega
        · exact h0
      exact ⟨q, k, hq.prime, hk0, by rw [← hk, hcardN]⟩
  have hsimple : IsSimpleGroup N := by
    obtain ⟨a, b, hab⟩ := hnonab
    have : Nontrivial N := ⟨⟨a * b, b * a, hab⟩⟩
    refine ⟨fun K hK => ?_⟩
    by_cases hK1 : K = ⊥
    · exact Or.inl hK1
    right
    by_cases hpK : p ∣ Nat.card K
    ·
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
      have hyN : orderOf (y : N) = p := by rw [Subgroup.orderOf_coe, hy]
      have hsyl : ∀ z : N, orderOf z = p →
          IsPGroup p (zpowers z) ∧ ¬ p ∣ (zpowers z).index := by
        intro z hz
        refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]),
          fun hdvd => hp2 ?_⟩
        have h1 := (zpowers z).card_mul_index
        rw [Nat.card_zpowers, hz] at h1
        rw [sq]
        exact (Nat.mul_dvd_mul_left p hdvd).trans (h1 ▸ Subgroup.card_subgroup_dvd_card N)
      have hconj : ∀ x : X, x * ((y : N) : X) * x⁻¹ ∈ K.map N.subtype := by
        intro x
        set c : N := ⟨x * ((y : N) : X) * x⁻¹, hN.conj_mem _ (y : N).2 x⟩ with hcdef
        have hc : orderOf c = p := by
          rw [hcdef, Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
            Subgroup.orderOf_coe, hyN]
        obtain ⟨hP, hPi⟩ := hsyl (y : N) hyN
        obtain ⟨hQ, hQi⟩ := hsyl c hc
        obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N (hQ.toSylow hQi) (hP.toSylow hPi)
        have h1 : n * c * n⁻¹ ∈ ((n • hQ.toSylow hQi : Sylow p N) : Subgroup N) := by
          rw [Sylow.coe_subgroup_smul]
          exact ⟨c, (IsPGroup.mem_toSylow hQ hQi).2 (mem_zpowers c), rfl⟩
        rw [hn] at h1
        have h2 : n * c * n⁻¹ ∈ zpowers (y : N) := (IsPGroup.mem_toSylow hP hPi).1 h1
        have h3 : n * c * n⁻¹ ∈ K := (zpowers_le.mpr y.2) h2
        have h4 : c ∈ K := by
          have := hK.conj_mem _ h3 n⁻¹
          simpa [mul_assoc] using this
        exact ⟨c, h4, rfl⟩
      have hcl : normalClosure ({((y : N) : X)} : Set X) ≤ K.map N.subtype := by
        refine (closure_le _).mpr ?_
        intro z hz
        obtain ⟨a, ha, haz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
        rw [Set.mem_singleton_iff] at ha
        subst ha
        obtain ⟨x, rfl⟩ := isConj_iff.mp haz
        exact hconj x
      have hcl1 : normalClosure ({((y : N) : X)} : Set X) ≠ ⊥ := by
        intro hb
        have hmem : ((y : N) : X) ∈ normalClosure ({((y : N) : X)} : Set X) :=
          subset_normalClosure rfl
        rw [hb, Subgroup.mem_bot] at hmem
        have : orderOf ((y : N) : X) = 1 := by rw [hmem, orderOf_one]
        rw [Subgroup.orderOf_coe, hyN] at this
        exact hp.one_lt.ne' this
      have hNle := huniq _ normalClosure_normal hcl1
      rw [eq_top_iff]
      intro k _
      obtain ⟨k', hk', hkk⟩ := (hNle.trans hcl) k.2
      rwa [← Subtype.ext hkk]
    · exfalso
      have hcop : Nat.Coprime p (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpK
      have hKle : K ≤ CFSG.pPrimeCore p N := le_sSup ⟨hK, hcop⟩
      have hOX : ((CFSG.pPrimeCore p N).map N.subtype).Normal :=
        ConjAct.normal_of_characteristic_of_normal
      have hO1 : (CFSG.pPrimeCore p N).map N.subtype ≠ ⊥ := by
        rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective]
        exact fun hb => hK1 (le_bot_iff.mp (hb ▸ hKle))
      have hNle := huniq _ hOX hO1
      have htop : CFSG.pPrimeCore p N = ⊤ := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨y, hy, hyx⟩ := hNle x.2
        rwa [← Subtype.ext hyx]
      have hcopN := CFSG.pPrimeCore_coprime_card (p := p) (G := N)
      rw [htop, Subgroup.card_top] at hcopN
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcopN hpN
  refine ⟨N, hN, hsimple, hnonab, htrans N hN hN1, huniq, ?_⟩
  by_contra hC
  have hCn : (centralizer (N : Set X)).Normal := inferInstance
  have hNC := huniq _ hCn hC
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (Subtype.ext (mem_centralizer_iff.mp (hNC b.2) a a.2))

end CFSG.EvenSmallLie.UnitarySix.Yamada
