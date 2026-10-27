module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OuterPlane
public import CFSG.LieType.SeitzGeneration.ExcRankVacuous
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Twelve
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Six
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.LieType.SeitzGeneration.ExcTorusCat
public import CFSG.LieType.SeitzGeneration.ExcTorusRankF4

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.TauCetiBridge
open CFSG.ComponentClassification.OuterAutomorphisms (inner congr_conj)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

theorem exists_inner_plane_of_hom {S N Q : Type*} [Group S] [Group N] [Group Q] [IsCyclic Q]
    (e : S ≃* N) (Θ : MulAut N →* Q) {p : ℕ} (hp : p.Prime)
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ (MulAut.conj : N →* MulAut N).range)
    {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E ≤ innerAut S ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 := by
  let φ : MulAut S →* MulAut N := (MulAut.congr e).toMonoidHom
  refine exists_plane_of_hom_cyclic hp (innerAut S) hD hcard ((Θ.comp φ).comp D.subtype)
    fun x hx => ?_
  obtain ⟨n, hn⟩ := hΘ (φ x) hx (by rw [← map_pow, hD.2 x x.2, map_one])
  refine ⟨e.symm n, (MulAut.congr e).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply]
  exact hn

theorem isLocallyBalancedAbs_of_rankLE1 {S N Q : Type*} [Group S] [Group N] [Group Q] [IsCyclic Q]
    (e : S ≃* N) (Θ : MulAut N →* Q) {p : ℕ} (hp : p.Prime)
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ (MulAut.conj : N →* MulAut N).range)
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) (hr : RankLE1 p S) :
    IsLocallyBalancedAbs p 3 S := by
  intro D hD hcard H _ _
  obtain ⟨E, -, hEin, hE, hEc⟩ := exists_inner_plane_of_hom e Θ hp hΘ hD hcard
  exact (false_of_inner_plane_of_rankLE1 hp hinj hr hE hEc hEin).elim

theorem isLocallyBalancedAbs_of_rankLE1_of_simple {S N Q : Type*} [Group S] [IsSimpleGroup S]
    [Group N] [Group Q] [IsCyclic Q] (e : S ≃* N) (Θ : MulAut N →* Q) {p : ℕ} (hp : p.Prime)
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ (MulAut.conj : N →* MulAut N).range)
    (hr : RankLE1 p S) : IsLocallyBalancedAbs p 3 S := by
  intro D hD hcard H _ _
  obtain ⟨E, -, hEin, hE, hEc⟩ := exists_inner_plane_of_hom e Θ hp hΘ hD hcard
  have hinj := conj_injective_of_simple_of_range_ne_bot (range_conj_ne_bot_of_inner hp hEc hEin)
  exact (false_of_inner_plane_of_rankLE1 hp hinj hr hE hEc hEin).elim

theorem le_innerAut_of_hom {S N Q : Type*} [Group S] [Group N] [Group Q]
    (e : S ≃* N) (Θ : MulAut N →* Q) {p : ℕ} (hQ : Nat.Coprime p (Nat.card Q))
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ (MulAut.conj : N →* MulAut N).range)
    {D : Subgroup (MulAut S)} (hD : ∀ x ∈ D, x ^ p = 1) : D ≤ innerAut S := by
  intro x hx
  let φ : MulAut S →* MulAut N := (MulAut.congr e).toMonoidHom
  have hφp : φ x ^ p = 1 := by rw [← map_pow, hD x hx, map_one]
  have h1 : Θ (φ x) = 1 := (pow_eq_one_iff_of_coprime hQ).1
    ⟨by rw [← map_pow, hφp, map_one], pow_card_eq_one'⟩
  obtain ⟨n, hn⟩ := hΘ (φ x) h1 hφp
  refine ⟨e.symm n, (MulAut.congr e).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply]
  exact hn

theorem false_of_inner_cube_of_rankLE2 {S : Type*} [Group S] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) (hr : RankLE2 p S)
    {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3)
    (hin : D ≤ innerAut S) : False := by
  have hmap : (D.comap (MulAut.conj : S →* MulAut S)).map (MulAut.conj : S →* MulAut S) = D :=
    Subgroup.map_comap_eq_self hin
  have hc : Nat.card (D.comap (MulAut.conj : S →* MulAut S)) = p ^ 3 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hcard]
  have h := hr _ (isElemAbelian_comap_of_injective _ hinj hD)
  rw [hc] at h
  exact absurd h (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

theorem isLocallyBalancedAbs_of_rankLE2 {S N Q : Type*} [Group S] [Group N] [Group Q]
    (e : S ≃* N) (Θ : MulAut N →* Q) {p : ℕ} (hp : p.Prime) (hQ : Nat.Coprime p (Nat.card Q))
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ (MulAut.conj : N →* MulAut N).range)
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) (hr : RankLE2 p S) :
    IsLocallyBalancedAbs p 3 S := fun _ hD hcard _ _ _ =>
  (false_of_inner_cube_of_rankLE2 hp hinj hr hD hcard (le_innerAut_of_hom e Θ hQ hΘ hD.2)).elim

theorem isLocallyBalancedAbs_of_rankLE2_of_simple {S N Q : Type*} [Group S] [IsSimpleGroup S]
    [Group N] [Group Q] (e : S ≃* N) (Θ : MulAut N →* Q) {p : ℕ} (hp : p.Prime)
    (hQ : Nat.Coprime p (Nat.card Q))
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ (MulAut.conj : N →* MulAut N).range)
    (hr : RankLE2 p S) : IsLocallyBalancedAbs p 3 S := by
  intro D hD hcard _ _ _
  have hin := le_innerAut_of_hom e Θ hQ hΘ hD.2
  have hne : (MulAut.conj : S →* MulAut S).range ≠ ⊥ := by
    intro hbot
    have hDbot : D = ⊥ := le_bot_iff.1 (hin.trans hbot.le)
    rw [hDbot, Subgroup.card_bot] at hcard
    exact absurd hcard (Nat.one_lt_pow (by norm_num) hp.one_lt).ne
  exact (false_of_inner_cube_of_rankLE2 hp (conj_injective_of_simple_of_range_ne_bot hne) hr hD
    hcard hin).elim

theorem CrossCharFamAt.or {k : LieFamily} {R₁ R₂ : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h₁ : CrossCharFamAt k R₁) (h₂ : CrossCharFamAt k R₂) :
    CrossCharFamAt k fun idx p => R₁ idx p ∨ R₂ idx p :=
  fun idx hk p hp hp2 hc hr => hr.elim (h₁ idx hk p hp hp2 hc) (h₂ idx hk p hp hp2 hc)

theorem rankLE1_of_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card G → CFSG.pRank p G ≤ 1) : RankLE1 p G := by
  intro F hF
  have : Fact p.Prime := ⟨hp⟩
  have hFp : IsPGroup p F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [hk, pow_zero]
    exact hp.one_lt.le
  · have hdvd : p ∣ Nat.card G :=
      (dvd_pow_self p hk0.ne').trans (hk ▸ Subgroup.card_subgroup_dvd_card F)
    have hE : CFSG.IsElementaryAbelian p F :=
      { toIsMulCommutative := hF.1
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by rw [Subgroup.coe_pow, hF.2 x x.2, Subgroup.coe_one]) }
    have h1 : k ≤ CFSG.pRank p G := by
      refine le_csSup ⟨Nat.card G, ?_⟩ ⟨F, hE, hk⟩
      rintro r ⟨B, -, hB⟩
      calc r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
        _ = Nat.card B := hB.symm
        _ ≤ Nat.card G := Subgroup.card_le_card_group B
    have h2 := h hdvd
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p

theorem orderOf_natCast_zmod_three {n : ℕ} (hn : ¬ 3 ∣ n) :
    orderOf ((n : ℕ) : ZMod 3) = 1 ∨ orderOf ((n : ℕ) : ZMod 3) = 2 := by
  have h0 : ((n : ℕ) : ZMod 3) ≠ 0 := fun h => hn ((ZMod.natCast_eq_zero_iff n 3).1 h)
  have h : ((n : ℕ) : ZMod 3) = 1 ∨ ((n : ℕ) : ZMod 3) = 2 := by
    generalize ((n : ℕ) : ZMod 3) = x at h0 ⊢
    revert x
    decide
  rcases h with h | h
  · exact Or.inl (by rw [h, orderOf_one])
  · exact Or.inr (by rw [h]; exact orderOf_eq_prime (by decide) (by decide))

theorem five_le_of_count_le {a : ℕ → ℕ} {k : ℕ} (ha : k < a 1 ∧ k < a 2) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : ¬ p ∣ n) (h : a (orderOf ((n : ℕ) : ZMod p)) ≤ k) :
    5 ≤ p := by
  rcases eq_three_or_five_le hp hp2 with rfl | h5
  · exfalso
    rcases orderOf_natCast_zmod_three hn with h1 | h1 <;> rw [h1] at h <;> omega
  · exact h5

theorem five_le_of_not_dvd_sq_sub_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : ¬ p ∣ n)
    (h : ¬ p ∣ n ^ 2 - 1) : 5 ≤ p := by
  rcases eq_three_or_five_le hp hp2 with rfl | h5
  · exfalso
    apply h
    have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero 3)
    have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn0)
    have h0 : ((n : ℕ) : ZMod 3) ≠ 0 := fun h => hn ((ZMod.natCast_eq_zero_iff n 3).1 h)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hn1]
    push_cast
    generalize ((n : ℕ) : ZMod 3) = x at h0 ⊢
    revert x
    decide
  · exact h5

theorem orderOf_dvd_two_of_dvd_sq_sub_one {p n : ℕ} (hn : ¬ p ∣ n) (h : p ∣ n ^ 2 - 1) :
    orderOf ((n : ℕ) : ZMod p) ∣ 2 := by
  apply orderOf_dvd_of_pow_eq_one
  have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero p)
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn0)
  have h1 := (ZMod.natCast_eq_zero_iff (n ^ 2 - 1) p).2 h
  rw [Nat.cast_sub hn1] at h1
  push_cast at h1
  exact sub_eq_zero.1 h1

theorem coprime_card_ringAut (q : TauCeti.PrimePower) (K : Type) [Field K]
    (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hf : ¬ p ∣ q.exponent) :
    Nat.Coprime p (Nat.card (K ≃+* K)) := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      q.prime_p q.exponent_pos (hK.trans (TauCeti.PrimePower.card_def q))
  rw [hcard]
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hf

@[expose] def regimeExc (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (a : ℕ → ℕ)
    (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = c q ∧ a (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1

@[expose] def regimeExcInner (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (a : ℕ → ℕ)
    (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = c q ∧ a (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∧
    ¬ p ∣ q.exponent

@[expose] def regimeExcVac (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (a : ℕ → ℕ)
    (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeExc c a idx p ∨ regimeExcInner c a idx p

section OuterE


theorem exists_hom_ringAut_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ Θ : MulAut (adjointGroup τ K) →* RingAut K, ∀ x ∈ Θ.ker, x ^ p = 1 →
      x ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨Φ, -, -, hΦ⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  refine ⟨(MonoidHom.fst _ _).comp (Φ.comp (QuotientGroup.mk' (inner (adjointGroup τ K)))), ?_⟩
  intro x hx hxp
  set y := QuotientGroup.mk' (inner (adjointGroup τ K)) x with hy
  have hyp : y ^ p = 1 := by rw [hy, ← map_pow, hxp, map_one]
  have h1 : (Φ y).1 = 1 := hx
  have hne : exactE τ ≠ 0 := by rcases hτ with rfl | rfl | rfl <;> simp [exactE]
  have hE2 : exactE τ ∣ 2 := by rcases hτ with rfl | rfl | rfl <;> simp [exactE]
  have h2 : (Φ y).2 = 1 := by
    have : NeZero (exactE τ) := ⟨hne⟩
    have hcard : Nat.card (Multiplicative (ZMod (exactE τ))) = exactE τ := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hz2 : (Φ y).2 ^ 2 = 1 := by
      have h0 : (Φ y).2 ^ Nat.card (Multiplicative (ZMod (exactE τ))) = 1 := pow_card_eq_one'
      rw [hcard] at h0
      obtain ⟨c, hc⟩ := hE2
      rw [hc, pow_mul, h0, one_pow]
    have hzp : (Φ y).2 ^ p = 1 := by
      have := congrArg Prod.snd (show Φ y ^ p = 1 by rw [← map_pow, hyp, map_one])
      simpa using this
    have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.2 (hp.odd_of_ne_two (by omega))
    exact (pow_eq_one_iff_of_coprime hcop).1 ⟨hz2, hzp⟩
  have hyk : y ∈ Φ.ker := Prod.ext h1 h2
  have hdet : 0 < τ.cartan.det.natAbs ∧ τ.cartan.det.natAbs ≤ 3 := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]; decide
    · rw [det_cartan_E7]; decide
    · rw [det_cartan_E8]; decide
  have hcop : Nat.Coprime (Nat.card Φ.ker) p :=
    Nat.Coprime.coprime_dvd_left hΦ (Nat.coprime_of_lt_prime hdet.1.ne' (by omega) hp).symm
  have hw : (⟨y, hyk⟩ : Φ.ker) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).1 ⟨pow_card_eq_one', Subtype.ext (by simpa using hyp)⟩
  exact (QuotientGroup.eq_one_iff (N := inner (adjointGroup τ K)) x).1 (congrArg Subtype.val hw)

end OuterE

section OuterF4


theorem exists_hom_cyclic_F4 (q : TauCeti.PrimePower) (K : Type) [Field K] [Finite K]
    [CharP K q.p] (hK : Nat.card K = q.card) :
    ∃ (Q : Type) (_ : Group Q) (_ : IsCyclic Q) (Θ : MulAut (adjointGroup .F4 K) →* Q),
      Nat.card Q ∣ 2 * q.exponent ∧
      Θ.ker = (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  by_cases h2 : q.p = 2
  · have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := by
      rw [show CFSG.LieType.Ree.ReeTag.F4.prime = 2 from rfl, ← h2]
      infer_instance
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
      even_F4_exact_automorphism_normal_form q.exponent_pos K (by rw [hK', h2])
    have : NeZero (2 * q.exponent) := ⟨by have := q.exponent_pos; omega⟩
    refine ⟨_, _, inferInstance, Θ, ?_, hker⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
      q.prime_p h2 q.exponent_pos K hK' .F4 (Or.inl rfl)
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        q.prime_p q.exponent_pos hK'
    exact ⟨_, _, fieldAut_isCyclic K, Θ, by rw [hcard]; exact Dvd.intro_left 2 rfl, hker⟩

end OuterF4

section RankTwo


theorem rankLE2_E8_of_degCount_eq_two (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    RankLE2 p (adjointGroup Tag.E8 K) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  rcases degCount_E8_eq_two hcnt with rfl | rfl | rfl | rfl
  · exact (sylowTorus_E8_five K hp he).rankLE2 hp le_rfl
  · exact (sylowTorus_E8_eight K hp he).rankLE2 hp le_rfl
  · exact (sylowTorus_E8_ten K hp he).rankLE2 hp le_rfl
  · exact (sylowTorus_E8_twelve K hp he).rankLE2 hp le_rfl

theorem rankLE2_E7_of_degCount_eq_two (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    RankLE2 p (adjointGroup Tag.E7 K) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  obtain rfl := degCount_E7_eq_two hcnt
  exact (sylowTorus_E7_four K hp he).rankLE2 hp le_rfl

theorem rankLE2_E6_of_degCount_eq_two (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    RankLE2 p (adjointGroup Tag.E6 K) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  rcases degCount_E6_eq_two hcnt with rfl | rfl
  · exact (sylowTorus_E6_four K hp he).rankLE2 hp le_rfl
  · exact (sylowTorus_E6_six K hp he).rankLE2 hp le_rfl

end RankTwo

section E


theorem rankLE2_cat_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hcnt : degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    RankLE2 p (Cat ⟨.E8 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at hcnt
  exact RankLE2.of_mulEquiv e.symm (rankLE2_E8_of_degCount_eq_two K hp hcnt)

theorem rankLE2_cat_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) {p : ℕ}
    (hp : p.Prime) (hcnt : degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    RankLE2 p (Cat ⟨.E7 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at hcnt
  exact RankLE2.of_mulEquiv e.symm (rankLE2_E7_of_degCount_eq_two K hp hcnt)

theorem rankLE2_cat_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) {p : ℕ}
    (hp : p.Prime) (hcnt : degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    RankLE2 p (Cat ⟨.E6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at hcnt
  exact RankLE2.of_mulEquiv e.symm (rankLE2_E6_of_degCount_eq_two K hp hcnt)

theorem crossCharFamAt_E8 :
    CrossCharFamAt .E8 (regimeExc TauCeti.LieTypeIndex.E8 (degCount Tag.E8)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 1) (by decide) hp hp2 (not_dvd_card_of_ne hp hpq) hcnt
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inr (Or.inr rfl)) K hp hp5
  have : IsCyclic (RingAut K) := fieldAut_isCyclic K
  exact isLocallyBalancedAbs_of_rankLE1 e Θ hp hΘ (conj_injective_cat_E8 q hv)
    (rankLE1_cat_E8 q hv hp hpq hcnt)

theorem crossCharFamAt_E8_inner :
    CrossCharFamAt .E8 (regimeExcInner TauCeti.LieTypeIndex.E8 (degCount Tag.E8)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hf⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 2) (by decide) hp hp2 (not_dvd_card_of_ne hp hpq)
    hcnt.le
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inr (Or.inr rfl)) K hp hp5
  exact isLocallyBalancedAbs_of_rankLE2 e Θ hp (coprime_card_ringAut q K hK hp hf) hΘ
    (conj_injective_cat_E8 q hv) (rankLE2_cat_E8 q hv hp hcnt)

theorem crossCharFamAt_E8_vac :
    CrossCharFamAt .E8 (regimeExcVac TauCeti.LieTypeIndex.E8 (degCount Tag.E8)) :=
  crossCharFamAt_E8.or crossCharFamAt_E8_inner

theorem crossCharFamAt_E7 :
    CrossCharFamAt .E7 (regimeExc TauCeti.LieTypeIndex.E7 (degCount Tag.E7)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 1) (by decide) hp hp2 (not_dvd_card_of_ne hp hpq) hcnt
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inr (Or.inl rfl)) K hp hp5
  have : IsCyclic (RingAut K) := fieldAut_isCyclic K
  exact isLocallyBalancedAbs_of_rankLE1 e Θ hp hΘ (conj_injective_cat_E7 q hv)
    (rankLE1_cat_E7 q hv hp hpq hcnt)

theorem crossCharFamAt_E7_inner :
    CrossCharFamAt .E7 (regimeExcInner TauCeti.LieTypeIndex.E7 (degCount Tag.E7)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hf⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 2) (by decide) hp hp2 (not_dvd_card_of_ne hp hpq)
    hcnt.le
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inr (Or.inl rfl)) K hp hp5
  exact isLocallyBalancedAbs_of_rankLE2 e Θ hp (coprime_card_ringAut q K hK hp hf) hΘ
    (conj_injective_cat_E7 q hv) (rankLE2_cat_E7 q hv hp hcnt)

theorem crossCharFamAt_E7_vac :
    CrossCharFamAt .E7 (regimeExcVac TauCeti.LieTypeIndex.E7 (degCount Tag.E7)) :=
  crossCharFamAt_E7.or crossCharFamAt_E7_inner

theorem crossCharFamAt_E6 :
    CrossCharFamAt .E6 (regimeExc TauCeti.LieTypeIndex.E6 (degCount Tag.E6)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 1) (by decide) hp hp2 (not_dvd_card_of_ne hp hpq) hcnt
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inl rfl) K hp hp5
  have : IsCyclic (RingAut K) := fieldAut_isCyclic K
  exact isLocallyBalancedAbs_of_rankLE1 e Θ hp hΘ (conj_injective_cat_E6 q hv)
    (rankLE1_cat_E6 q hv hp hpq hcnt)

theorem crossCharFamAt_E6_inner :
    CrossCharFamAt .E6 (regimeExcInner TauCeti.LieTypeIndex.E6 (degCount Tag.E6)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hf⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 2) (by decide) hp hp2 (not_dvd_card_of_ne hp hpq)
    hcnt.le
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inl rfl) K hp hp5
  exact isLocallyBalancedAbs_of_rankLE2 e Θ hp (coprime_card_ringAut q K hK hp hf) hΘ
    (conj_injective_cat_E6 q hv) (rankLE2_cat_E6 q hv hp hcnt)

theorem crossCharFamAt_E6_vac :
    CrossCharFamAt .E6 (regimeExcVac TauCeti.LieTypeIndex.E6 (degCount Tag.E6)) :=
  crossCharFamAt_E6.or crossCharFamAt_E6_inner

theorem crossCharFamAt_F4 :
    CrossCharFamAt .F4 (regimeExc TauCeti.LieTypeIndex.F4 (degCount Tag.F4)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, _, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  obtain ⟨Q, _, _, Θ, -, hker⟩ := exists_hom_cyclic_F4 q K hK
  exact isLocallyBalancedAbs_of_rankLE1 e Θ hp (fun x hx _ => hker ▸ hx)
    (conj_injective_cat_F4 q hv) (rankLE1_cat_F4 q hv hp hpq hcnt)

theorem crossCharFamAt_F4_inner :
    CrossCharFamAt .F4 (regimeExcInner TauCeti.LieTypeIndex.F4 (degCount Tag.F4)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hf⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, _, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  obtain ⟨Q, _, _, Θ, hQ, hker⟩ := exists_hom_cyclic_F4 q K hK
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hnd : ¬ p ∣ Nat.card K ^ 2 - 1 := by
    intro h
    have h2 := orderOf_dvd_two_of_dvd_sq_sub_one hpK h
    rw [hK] at h2
    rcases degCount_F4_eq_two hcnt with h3 | h3 | h3 <;> rw [h3] at h2 <;> omega
  have hcop : Nat.Coprime p (Nat.card Q) := Nat.Coprime.coprime_dvd_right hQ
    (Nat.Coprime.mul_right (Nat.coprime_two_right.2 (hp.odd_of_ne_two hp2))
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hf))
  exact isLocallyBalancedAbs_of_rankLE2 e Θ hp hcop (fun x hx _ => hker ▸ hx)
    (conj_injective_cat_F4 q hv)
    (RankLE2.of_mulEquiv e.symm (rankLE2_adjointGroup_F4 K hp hp2 hpK hnd))

theorem crossCharFamAt_F4_vac :
    CrossCharFamAt .F4 (regimeExcVac TauCeti.LieTypeIndex.F4 (degCount Tag.F4)) :=
  crossCharFamAt_F4.or crossCharFamAt_F4_inner

end E

end CFSG.HardMathSupport.Timmesfeld.CrossChar
