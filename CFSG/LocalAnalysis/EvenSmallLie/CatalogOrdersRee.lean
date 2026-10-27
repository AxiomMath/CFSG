module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLargeReeTits
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem card_dvd_card_quotient_center_of_injective {D Γ : Type*} [Group D] [Group Γ]
    (φ : D →* Γ) (hφ : Function.Injective φ) (hZ : Subgroup.center D = ⊥) :
    Nat.card D ∣ Nat.card (Γ ⧸ Subgroup.center Γ) := by
  refine Subgroup.card_dvd_of_injective ((QuotientGroup.mk' _).comp φ) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  refine Subgroup.mem_center_iff.2 fun y => hφ ?_
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 hx (φ y)

theorem dvd_card_commutator_reeFixed_two
    {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2) {m : ℕ} (hm : Odd m)
    (hdvd : m ∣ 35942400) : m ∣ Nat.card (commutator (reeFixed ReeTag.F4 K 0)) := by
  have hcard := CFSG.SectionRank.TitsOrder.Tits_card hK
  have : Finite (reeFixed ReeTag.F4 K 0) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_reeFixed_quotient (a := 0) rfl hK)
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (commutator (reeFixed ReeTag.F4 K 0))
  rw [hcard, hn] at h
  rw [h] at hdvd
  exact ((Nat.coprime_two_right.2 hm).pow_right n).dvd_of_dvd_mul_left hdvd

theorem exists_mulEquiv_of_reeTitsRelationModel_F4
    {T : Type} [Group T] {f a : ℕ}
    (h : ReeTitsRelationModel T .F4 reeF4Perm reeF4Long 2 f a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      Nat.card K = 2 ^ f ∧ Nonempty (T ≃* commutator (reeFixed ReeTag.F4 K a) ⧸
        Subgroup.center (commutator (reeFixed ReeTag.F4 K a))) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := hc
  exact ⟨K, inferInstance, inferInstance, this, hK,
    ⟨e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
      ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K a)).trans
        ((reeFixed ReeTag.F4 K a).equivMapOfInjective _ Subtype.val_injective).symm))⟩⟩

theorem card_commutator_reeFixed_zmod_two_dvd
    [CharP (ZMod 2) ReeTag.F4.prime] (a : ℕ)
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] :
    Nat.card (commutator (reeFixed ReeTag.F4 (ZMod 2) 0)) ∣
      Nat.card (reeFixed ReeTag.F4 K a ⧸ Subgroup.center (reeFixed ReeTag.F4 K a)) := by
  obtain ⟨ι⟩ : Nonempty (ZMod 2 →+* K) := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact ⟨ZMod.castHom (dvd_refl 2) K⟩
  obtain ⟨hinj, -, hle, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.large_Ree_prime_field_Tits_fixed_four_group a K ι
  set D := commutator (reeFixed ReeTag.F4 (ZMod 2) 0)
  have hΓ₂ : ReeTag.titsGamma = (reeFixed ReeTag.F4 (ZMod 2) 0).map
      (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype :=
    ReeTag.reeGamma_eq_reeFixedGroup.trans (reeFixedGroup_eq_map_reeFixed ReeTag.F4 (ZMod 2) 0)
  have hΓ : ReeTag.F4.reeGamma K a = (reeFixed ReeTag.F4 K a).map
      (adjointGroup ReeTag.F4.tag K).subtype :=
    ReeTag.reeGamma_eq_reeFixedGroup.trans (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K a)
  have hD : ⁅ReeTag.titsGamma, ReeTag.titsGamma⁆ =
      (D.map (reeFixed ReeTag.F4 (ZMod 2) 0).subtype).map
        (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype := by
    rw [hΓ₂, ← Subgroup.map_commutator, CFSG.LocalAnalysis.ComponentInitial.map_subtype_commutator]
  set f : D →* ModGL ReeTag.F4.tag K := (baseChangeGL ι).comp
    ((adjointGroup ReeTag.F4.tag (ZMod 2)).subtype.comp
      ((reeFixed ReeTag.F4 (ZMod 2) 0).subtype.comp D.subtype))
  have hf : ∀ x : D, f x ∈ (reeFixed ReeTag.F4 K a).map (adjointGroup ReeTag.F4.tag K).subtype :=
    fun x => by
      rw [← hΓ]
      refine hle ⟨_, ?_, rfl⟩
      rw [hD]
      exact ⟨_, ⟨x, x.2, rfl⟩, rfl⟩
  have hfinj : Function.Injective f :=
    hinj.comp (Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective))
  let f₁ : D →* adjointGroup ReeTag.F4.tag K := f.codRestrict _ fun x => by
    obtain ⟨y, -, hy⟩ := hf x
    exact hy ▸ y.2
  let φ : D →* reeFixed ReeTag.F4 K a := f₁.codRestrict _ fun x => by
    obtain ⟨y, hy, hyx⟩ := hf x
    rwa [show f₁ x = y from Subtype.ext hyx.symm]
  refine card_dvd_card_quotient_center_of_injective φ (fun x y hxy => hfinj ?_)
    (CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot (Nat.card_zmod 2))
  exact congrArg (fun z : reeFixed ReeTag.F4 K a =>
    ((z : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K)) hxy

theorem dvd_card_of_reeTitsModel_Tits
    {T : Type} [Group T] {p f m : ℕ}
    (h : ReeTitsModel T .Tits p f) (hm : Odd m) (hdvd : m ∣ 35942400) : m ∣ Nat.card T := by
  obtain ⟨⟨-, -, -, hp, hf1⟩, a, hf, hmodel⟩ := h
  subst hp hf1
  obtain rfl : a = 0 := by omega
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_of_reeTitsRelationModel_F4 hmodel
  rw [pow_one] at hK
  rw [Nat.card_congr (e.trans ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hK)).trans
      QuotientGroup.quotientBot)).toEquiv]
  exact dvd_card_commutator_reeFixed_two hK hm hdvd

theorem dvd_card_of_reeTitsModel_twistedF4
    {T : Type} [Group T] {p f m : ℕ}
    (h : ReeTitsModel T .twistedF4 p f) (hm : Odd m) (hdvd : m ∣ 35942400) :
    m ∣ Nat.card T := by
  obtain ⟨⟨-, -, -, hp, -, h3⟩, a, hf, hmodel⟩ := h
  subst hp
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_of_reeTitsRelationModel_F4 hmodel
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := by
    rw [hK, hf]
    rfl
  have hperf := CFSG.LieType.Simplicity.commutator_reeFixed_F4 a (by omega) hK'
  let eΓ : commutator (reeFixed ReeTag.F4 K a) ≃* reeFixed ReeTag.F4 K a :=
    (MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv
  rw [Nat.card_congr (e.trans (QuotientGroup.congr _ _ eΓ (Subgroup.map_center_eq _))).toEquiv]
  have : CharP (ZMod 2) ReeTag.F4.prime := ZMod.charP 2
  exact (dvd_card_commutator_reeFixed_two (Nat.card_zmod 2) hm hdvd).trans
    (card_commutator_reeFixed_zmod_two_dvd a K)

theorem thirteen_dvd_card_of_reeTitsModel_Tits
    {T : Type} [Group T] {p f : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel T .Tits p f) : 13 ∣ Nat.card T :=
  dvd_card_of_reeTitsModel_Tits h (by decide) (by norm_num)

theorem thirteen_dvd_card_of_reeTitsModel_twistedF4
    {T : Type} [Group T] {p f : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel T .twistedF4 p f) : 13 ∣ Nat.card T :=
  dvd_card_of_reeTitsModel_twistedF4 h (by decide) (by norm_num)

theorem twenty_five_dvd_card_of_reeTitsModel_Tits
    {T : Type} [Group T] {p f : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel T .Tits p f) : 25 ∣ Nat.card T :=
  dvd_card_of_reeTitsModel_Tits h (by decide) (by norm_num)

theorem twenty_five_dvd_card_of_reeTitsModel_twistedF4
    {T : Type} [Group T] {p f : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel T .twistedF4 p f) : 25 ∣ Nat.card T :=
  dvd_card_of_reeTitsModel_twistedF4 h (by decide) (by norm_num)

end CFSG.EvenSmallLie.CatalogOrders
