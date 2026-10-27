module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small
public import CFSG.Timmesfeld.Bridge.Asc72ZAlt
public import Certificates.Data.A5

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

theorem perm_five_pow_ten :
    ∀ x : Equiv.Perm (Fin 5), x ^ 10 = 1 → x ^ 5 = 1 ∨ x ^ 2 = 1 := by
  decide +kernel

theorem normalizer_le_centralizer_of_card_le_two {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} (hP : Nat.card P ≤ 2) :
    normalizer (P : Set G) ≤ centralizer (P : Set G) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro x hx
  have hgx : g * x * g⁻¹ ∈ P := (mem_normalizer_iff.mp hg x).mp hx
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  · by_contra hne
    have h1 : g * x * g⁻¹ ≠ 1 := by
      intro h
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h2 : x ≠ g * x * g⁻¹ := by
      intro h
      apply hne
      calc x * g = g * x * g⁻¹ * g := by rw [← h]
        _ = g * x := by group
    have hsub : ({1, x, g * x * g⁻¹} : Set G) ⊆ (P : Set G) := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact one_mem P
      · exact hx
      · exact hgx
    have h3 : ({1, x, g * x * g⁻¹} : Set G).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, x, g * x * g⁻¹, Ne.symm hx1, Ne.symm h1, h2, rfl⟩
    have hle : ({1, x, g * x * g⁻¹} : Set G).ncard ≤ Nat.card P := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    omega

theorem map_centralizer_singleton_eq_inf {S : Type*} [Group S] (C : Subgroup S) (a : C) :
    (centralizer {a} : Subgroup C).map C.subtype = C ⊓ centralizer {(a : S)} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine mem_inf.2 ⟨y.2, ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy
  · intro hx
    obtain ⟨hxC, hxa⟩ := mem_inf.1 hx
    refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff] at hxa
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact Subtype.ext hxa

@[expose] noncomputable def centralizerSingletonInfEquiv {S : Type*} [Group S] (C : Subgroup S)
    (a : C) : (centralizer {a} : Subgroup C) ≃* ↥(C ⊓ centralizer {(a : S)}) :=
  ((centralizer {a} : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_singleton_eq_inf C a))

theorem card_centralizer_le_two_of_oddCore {C : Type*} [Group C] [Finite C] {D : Subgroup C}
    [D.Normal]
    (h2 : ∀ U : Subgroup C, IsPGroup 2 U → U ≤ centralizer (D : Set C) → Nat.card U ≤ 2)
    {a : C} (haD : a ∈ D) (hcore : CFSG.oddCore (centralizer {a} : Subgroup C) = ⊥) :
    Nat.card (centralizer (D : Set C)) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ : ∃ K : Subgroup C, K = centralizer (D : Set C) := ⟨_, rfl⟩
  rw [← hK]
  have : K.Normal := by rw [hK]; infer_instance
  have hK2 : ∀ U : Subgroup K, IsPGroup 2 U → Nat.card U ≤ 2 := by
    intro U hU
    have h := h2 (U.map K.subtype) (hU.map K.subtype) (by
      rintro _ ⟨u, -, rfl⟩
      rw [← hK]
      exact u.2)
    rwa [card_map_of_injective K.subtype_injective] at h
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 K))
  have hP2 : Nat.card (P : Subgroup K) ≤ 2 := hK2 P P.isPGroup'
  obtain ⟨N, -, hN2, hNidx, -, hNchar, -⟩ := CFSG.GroupTheory.burnside_normal_complement P
    (normalizer_le_centralizer_of_card_le_two hP2)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup C, H = centralizer {a} := ⟨_, rfl⟩
  rw [← hH] at hcore
  set N' : Subgroup C := N.map K.subtype with hN'
  have hN'H : N' ≤ H := by
    rintro _ ⟨n, -, rfl⟩
    rw [hH, mem_centralizer_singleton_iff]
    have hn : (n : C) ∈ centralizer (D : Set C) := hK ▸ n.2
    exact (mem_centralizer_iff.mp hn a haD).symm
  have hnorm : (N'.subgroupOf H).Normal := by
    constructor
    intro x hx h
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨n, hn, hxn⟩ := hx
    set φ : MulAut K := MulAut.conjNormal (h : C) with hφ
    have hφn : φ n ∈ N := by
      have h1 : φ n ∈ N.map φ.toMonoidHom := mem_map_of_mem _ hn
      rwa [(characteristic_iff_map_eq.mp hNchar) φ] at h1
    refine ⟨φ n, hφn, ?_⟩
    have h2' : ((φ n : K) : C) = (h : C) * (n : C) * (h : C)⁻¹ := MulAut.conjNormal_apply _ n
    rw [coe_subtype, h2', coe_mul, coe_mul, coe_inv, ← hxn, coe_subtype]
  have hodd : Odd (Nat.card (N'.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hN'H).toEquiv, hN',
      card_map_of_injective K.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hN2)
  have hle : N'.subgroupOf H ≤ CFSG.oddCore H := le_sSup ⟨hnorm, hodd⟩
  rw [hcore] at hle
  have hNbot : N = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have hmem : (n : C) ∈ N' := ⟨n, hn, rfl⟩
    have h1 : (⟨(n : C), hN'H hmem⟩ : H) ∈ N'.subgroupOf H := hmem
    have h2' := hle h1
    rw [mem_bot] at h2'
    have h3 : (n : C) = 1 := congrArg Subtype.val h2'
    rw [mem_bot]
    exact Subtype.ext h3
  have hcard := N.index_mul_card
  rw [hNidx, hNbot, card_bot, mul_one] at hcard
  omega

theorem exists_hom_perm_five_of_lieModel {G : Type} [Group G]
    {D : Subgroup G} [D.Normal] (hDp : Group.IsPerfect D)
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 2) :
    ∃ ψ : G →* Equiv.Perm (Fin 5), ∀ g, ψ g = 1 → g ∈ centralizer (D : Set G) := by
  have : Group.IsPerfect D := hDp
  obtain ⟨e1⟩ := nonempty_mulEquiv_psl2Model_of_lieModel hDm
  obtain ⟨e2⟩ := CFSG.Timmesfeld.Bridge.Asc72.AltFive.nonempty_psl2Model_two_equiv
  have bij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  set c : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective _ bij with hc
  refine ⟨c.symm.toMonoidHom.comp ((MulAut.congr (e1.trans e2)).toMonoidHom.comp
    ((quotientCenterAutHom D).comp MulAut.conjNormal)), fun g hg => ?_⟩
  have h1 : MulAut.congr (e1.trans e2) (quotientCenterAutHom D (MulAut.conjNormal g)) = 1 := by
    have h := congrArg c hg
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      map_one] at h
    exact h
  have h2 : quotientCenterAutHom D (MulAut.conjNormal g) = 1 :=
    (MulAut.congr (e1.trans e2)).injective (h1.trans (map_one _).symm)
  have h3 : (MulAut.conjNormal g : MulAut D) = 1 :=
    quotientCenterAutHom_injective (h2.trans (map_one _).symm)
  rw [mem_centralizer_iff]
  intro d hd
  have h4 := congrArg (fun φ : MulAut D => ((φ ⟨d, hd⟩ : D) : G)) h3
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h4
  calc d * g = g * d * g⁻¹ * g := by rw [h4]
    _ = g * d := by group

theorem false_of_fixed_A5_component {S : Type} [Group S] [Finite S]
    {σ : MulAut S} {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 2) (h2 : FixedCentralizerTwoSmall σ D)
    (hcore : ∀ a : S, orderOf a = 2 → σ a = a →
      CFSG.oddCore ↥(fixedSubgroup σ ⊓ centralizer {a}) = ⊥)
    (hloc : ∀ t : S, orderOf t = 2 → σ t = t →
      168 ∣ Nat.card ↥(fixedSubgroup σ ⊓ centralizer {t}) ∨
        60 ∣ Nat.card ↥(fixedSubgroup σ ⊓ centralizer {t}) ∨
        72 ∣ Nat.card ↥(fixedSubgroup σ ⊓ centralizer {t}))
    (hV : ∃ V : Subgroup S, V ≤ fixedSubgroup σ ∧ CFSG.IsElementaryAbelian 2 V ∧
      Nat.card V = 4) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hN : D.Normal := normal_of_isComponent_of_twoSmall hD h2
  have hD60 : Nat.card (D ⧸ center D) = 60 := by
    rw [card_of_lieModel_PSL_two_two hDm]
    decide
  have h2D : 2 ∣ Nat.card D := by
    rw [card_eq_card_quotient_mul_card_subgroup (center D), hD60]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 h2D
  have h2C : ∀ U : Subgroup (fixedSubgroup σ), IsPGroup 2 U →
      U ≤ centralizer (D : Set (fixedSubgroup σ)) → Nat.card U ≤ 2 :=
    fun U hU hUD => card_le_two_of_le_centralizer h2 hU hUD
  have hcoreC : ∀ a : fixedSubgroup σ, orderOf a = 2 →
      CFSG.oddCore (centralizer {a} : Subgroup (fixedSubgroup σ)) = ⊥ := fun a ha =>
    ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      (centralizerSingletonInfEquiv _ a).symm
      (hcore (a : S) (by rw [Subgroup.orderOf_coe]; exact ha) a.2)
  have hKc : Nat.card (centralizer (D : Set (fixedSubgroup σ))) ≤ 2 :=
    card_centralizer_le_two_of_oddCore h2C (a := (d : fixedSubgroup σ)) d.2
      (hcoreC _ (by rw [Subgroup.orderOf_coe]; exact hd))
  obtain ⟨ψ, hψ⟩ := exists_hom_perm_five_of_lieModel hD.1.1 hDm
  obtain ⟨V, hVC, hVel, hV4⟩ := hV
  have : CFSG.IsElementaryAbelian 2 V := hVel
  set K' : Subgroup S := (centralizer (D : Set (fixedSubgroup σ))).map (fixedSubgroup σ).subtype
    with hK'
  have hK'c : Nat.card K' ≤ 2 := by
    rw [hK', card_map_of_injective (fixedSubgroup σ).subtype_injective]
    exact hKc
  have hVK : ¬ V ≤ K' := fun h => by
    have := Subgroup.card_le_of_le h
    omega
  obtain ⟨v, hvV, hvK⟩ := IsConcreteLE.not_le_iff_exists.mp hVK
  have hv1 : v ≠ 1 := fun h => hvK (h ▸ one_mem _)
  have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hvV
  have hvo : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  have hσv : σ v = v := hVC hvV
  set tC : fixedSubgroup σ := ⟨v, hVC hvV⟩ with htC
  have hψt : ψ tC ≠ 1 := fun h => hvK ⟨tC, hψ tC h, rfl⟩
  have htC2 : tC ^ 2 = 1 := Subtype.ext (by simpa using hv2)
  have hψt2 : ψ tC ^ 2 = 1 := by rw [← map_pow, htC2, map_one]
  set Z : Subgroup (fixedSubgroup σ) := centralizer {tC} with hZ
  have hZcard : Nat.card Z = Nat.card ↥(fixedSubgroup σ ⊓ centralizer {v}) :=
    Nat.card_congr (centralizerSingletonInfEquiv _ tC).toEquiv
  set ψZ := ψ.comp Z.subtype with hψZ
  have hkr := Subgroup.card_ker_mul_card_range ψZ
  have hker : Nat.card ψZ.ker ≤ 2 := by
    let ι : ψZ.ker → centralizer (D : Set (fixedSubgroup σ)) :=
      fun z => ⟨((z : Z) : fixedSubgroup σ), hψ _ z.2⟩
    have hι : Function.Injective ι := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact (Nat.card_le_card_of_injective ι hι).trans hKc
  have hkpos : 0 < Nat.card ψZ.ker := Nat.card_pos
  have hk12 : Nat.card ψZ.ker = 1 ∨ Nat.card ψZ.ker = 2 := by omega
  have hran : Nat.card ψZ.range ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card ψZ.range
    rwa [Nat.card_perm, Nat.card_fin] at h
  have h240 : Nat.card ψZ.ker * Nat.card ψZ.range ∣ 240 := by
    rcases hk12 with h | h <;> rw [h]
    · rw [one_mul]
      exact hran.trans (by norm_num)
    · exact Nat.mul_dvd_mul_left 2 hran
  rcases hloc v hvo hσv with h | h | h <;> rw [← hZcard, ← hkr] at h
  · have := h.trans h240
    norm_num at this
  ·
    have h5 : 5 ∣ Nat.card ψZ.range := by
      have h5' : 5 ∣ Nat.card ψZ.ker * Nat.card ψZ.range := (by norm_num : 5 ∣ 60).trans h
      rcases hk12 with hk | hk <;> rw [hk] at h5'
      · simpa using h5'
      · exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h5')
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ψZ.range) 5 h5
    obtain ⟨z, hz⟩ := g.2
    have hg' : orderOf (ψ (z : fixedSubgroup σ)) = 5 := by
      have h1 : ψ (z : fixedSubgroup σ) = (g : Equiv.Perm (Fin 5)) := hz
      rw [h1, Subgroup.orderOf_coe, hg]
    have hzt : (z : fixedSubgroup σ) * tC = tC * (z : fixedSubgroup σ) :=
      mem_centralizer_singleton_iff.mp z.2
    have hcomm : Commute (ψ (z : fixedSubgroup σ)) (ψ tC) := by
      change ψ (z : fixedSubgroup σ) * ψ tC = ψ tC * ψ (z : fixedSubgroup σ)
      rw [← map_mul, hzt, map_mul]
    have hg5 : ψ (z : fixedSubgroup σ) ^ 5 = 1 := by
      have h1 := pow_orderOf_eq_one (ψ (z : fixedSubgroup σ))
      rwa [hg'] at h1
    have ht5 : ψ tC ^ 5 = ψ tC := by
      have e : ψ tC ^ 5 = (ψ tC ^ 2) ^ 2 * ψ tC := by rw [← pow_mul, ← pow_succ]
      rw [e, hψt2, one_pow, one_mul]
    have h10 : (ψ (z : fixedSubgroup σ) * ψ tC) ^ 10 = 1 := by
      rw [hcomm.mul_pow]
      have e1 : ψ (z : fixedSubgroup σ) ^ 10 = (ψ (z : fixedSubgroup σ) ^ 5) ^ 2 := by
        rw [← pow_mul]
      have e2 : ψ tC ^ 10 = (ψ tC ^ 2) ^ 5 := by rw [← pow_mul]
      rw [e1, e2, hg5, hψt2, one_pow, one_pow, one_mul]
    rcases perm_five_pow_ten _ h10 with h' | h'
    · rw [hcomm.mul_pow, hg5, one_mul, ht5] at h'
      exact hψt h'
    · rw [hcomm.mul_pow, hψt2, mul_one] at h'
      have := orderOf_dvd_of_pow_eq_one h'
      rw [hg'] at this
      norm_num at this
  · have := h.trans h240
    norm_num at this

end CFSG.SeitzReduction.RankOne
