module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Shapes
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyOdd
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyG2
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyE
import CFSG.RankThree.Chevalley.SteinbergCFOddE8InnerField
import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace ExcUntwisted

section Generic

variable {p : ℕ} {S : Type} [Group S]

theorem mulAut_congr_self (δ φ : MulAut S) : MulAut.congr δ φ = δ * φ * δ⁻¹ := by
  ext x
  rfl

theorem mul_conj_mul_inv (φ : MulAut S) (z : S) :
    φ * MulAut.conj z * φ⁻¹ = MulAut.conj (φ z) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem fixSubgroup_le_pow (α : MulAut S) (n : ℕ) : fixSubgroup α ≤ fixSubgroup (α ^ n) := by
  intro x hx
  rw [mem_fixSubgroup] at hx ⊢
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx]; exact ih

theorem fixSubgroup_pow_eq {α : MulAut S} {r j : ℕ} (h : (α ^ r) ^ j = α) :
    fixSubgroup (α ^ r) = fixSubgroup α :=
  le_antisymm (by
    have := fixSubgroup_le_pow (α ^ r) j
    rwa [h] at this) (fixSubgroup_le_pow α r)

theorem outerCentData_of_pow {β : MulAut S} (r : ℕ) (h : OuterCentData p (β ^ r))
    (hfix : fixSubgroup (β ^ r) = fixSubgroup β) : OuterCentData p β where
  unique I J hI hJ := h.unique I J (hfix ▸ hI) (hfix ▸ hJ)
  chev I hI := h.chev I (hfix ▸ hI)
  core hexc := hfix ▸ h.core hexc
  cent hexc w hw hwβ hfixw :=
    h.cent hexc w hw (Commute.pow_right (show Commute w β from hwβ) r).eq
      (fun x hx => hfixw x (hfix ▸ hx))
  noHatSix hp3 I hI := h.noHatSix hp3 I (hfix ▸ hI)
  l227 hp3 I hI hL β' hβ3 hββ' hmap :=
    h.l227 hp3 I (hfix ▸ hI) hL β' hβ3 (Commute.pow_right (show Commute β' β from hββ') r).eq
      hmap

theorem outerCentData_of_conj (hp : p.Prime) [Finite S] {β : MulAut S} (δ : MulAut S)
    (h : OuterCentData p (δ * β * δ⁻¹)) : OuterCentData p β := by
  refine OuterCentData.of_congr hp δ ?_
  rw [mulAut_congr_self]
  exact h

theorem eq_one_of_conj_mem_zpowers [Finite S] (hp : p.Prime) {α : MulAut S} (hα : orderOf α = p)
    (hout : α ∉ innerAut S) (hZ : Subgroup.center S = ⊥) {x : S}
    (hx : MulAut.conj x ∈ Subgroup.zpowers α) : x = 1 := by
  by_contra hx1
  have hne : MulAut.conj x ≠ 1 := by
    intro h
    apply hx1
    have : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut S => f y) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rwa [hZ, Subgroup.mem_bot] at this
  have hdvd : orderOf (MulAut.conj x) ∣ p := hα ▸ orderOf_dvd_of_mem_zpowers hx
  have hord : orderOf (MulAut.conj x) = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have hle : Subgroup.zpowers (MulAut.conj x) ≤ Subgroup.zpowers α := Subgroup.zpowers_le.2 hx
  have hcard : Nat.card (Subgroup.zpowers α) ≤ Nat.card (Subgroup.zpowers (MulAut.conj x)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hα]
  have heq : Subgroup.zpowers (MulAut.conj x) = Subgroup.zpowers α :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hαm : α ∈ Subgroup.zpowers (MulAut.conj x) := by
    rw [heq]
    exact Subgroup.mem_zpowers α
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hαm
  apply hout
  refine ⟨x ^ k, ?_⟩
  rw [map_zpow]
  exact hk

theorem card_of_isLTwoTwentySeven {X : Type} [Group X] (h : IsLTwoTwentySeven X) :
    Nat.card X = 9828 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
  norm_num

end Generic

section Entrywise


theorem outerCentData_entrywise (τ : Tag) {ℓ : ℕ} (hℓ : ℓ.Prime) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (σ : K ≃+* K)
    (hσord : orderOf (entrywiseAdjointAut τ σ) = ℓ)
    (hσout : entrywiseAdjointAut τ σ ∉ innerAut (adjointGroup τ K))
    (hstab : ∀ w : MulAut (adjointGroup τ K),
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → w j = j) →
        w ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ))
    (hchev : IsChevSimple ℓ ↥(adjointGroup τ (fixSubfield σ)))
    (hdvd : ℓ ∣ Nat.card ↥(adjointGroup τ (fixSubfield σ)))
    (hL27 : ℓ = 3 → ¬ IsLTwoTwentySeven ↥(adjointGroup τ (fixSubfield σ))) :
    OuterCentData ℓ (entrywiseAdjointAut τ σ) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set β := entrywiseAdjointAut τ σ with hβ
  have hk2 : ringChar (fixSubfield σ) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : fixSubfield σ) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    apply Ring.two_ne_zero hK2
    have := congrArg (fixSubfield σ).subtype h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨hs, hnc, -⟩ := odd_pinned_Chevalley_p_components τ (fixSubfield σ) hk2
  obtain ⟨-, -, -, hJΓ, -, hnormal, -, hder⟩ :=
    Chevalley_coordinate_field_fixed_structure τ K hK2 σ
  have hJA : fixedFieldImage τ σ ≤ adjointGroup τ K := hJΓ.trans inf_le_left
  have hΓ : ∀ n : ↥(fixSubgroup β), ((n : ↥(adjointGroup τ K)) : ModGL τ K) ∈
      entrywiseFixedGroup τ σ := fun n =>
    ⟨(n : ↥(adjointGroup τ K)).2, by
      have h1 : β n = n := n.2
      have := congrArg Subtype.val h1
      rwa [coe_entrywiseAdjointAut] at this⟩
  set J : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
    with hJ
  have hmemJ : ∀ x : ↥(adjointGroup τ K), x ∈ J ↔ (x : ModGL τ K) ∈ fixedFieldImage τ σ :=
    fun x => Iff.rfl
  have hJC : J ≤ fixSubgroup β := fun x hx => by
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  haveI hJn : (J.subgroupOf (fixSubgroup β)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, hmemJ] at hn ⊢
    have h1 := hnormal.conj_mem ⟨((n : ↥(adjointGroup τ K)) : ModGL τ K), hΓ n⟩
      (Subgroup.mem_subgroupOf.2 hn) ⟨((g : ↥(adjointGroup τ K)) : ModGL τ K), hΓ g⟩
    simpa using Subgroup.mem_subgroupOf.1 h1
  let eJ : ↥J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv σ).symm
  haveI := hs
  have hsJ : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩
  have hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, Subgroup.mem_subgroupOf, hmemJ]
    have h2 : (((⁅y⁻¹, x⁻¹⁆ : ↥(fixSubgroup β)) : ↥(adjointGroup τ K)) : ModGL τ K) =
        ⁅(((y⁻¹ : ↥(fixSubgroup β)) : ↥(adjointGroup τ K)) : ModGL τ K),
          (((x⁻¹ : ↥(fixSubgroup β)) : ↥(adjointGroup τ K)) : ModGL τ K)⁆ := by
      simp [commutatorElement_def]
    rw [h2, ← hder]
    exact Subgroup.commutator_mem_commutator (hΓ _) (hΓ _)
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hstab' : ∀ w : MulAut (adjointGroup τ K), (∀ x ∈ J, w x = x) →
      w ∈ Subgroup.zpowers β := fun w hw => hstab w fun j hj => hw j hj
  have hcentr : ∀ x ∈ fixSubgroup β, (∀ m ∈ J, x * m = m * x) → x = 1 := by
    intro x _ hx
    refine eq_one_of_conj_mem_zpowers hℓ hσord hσout hZ (hstab' _ fun m hm => ?_)
    rw [MulAut.conj_apply, hx m hm]
    group
  refine OuterCentData.ofSimpleNormal hℓ
    ⟨hJC, hJn, hsJ, hncJ, hsol, hcentr,
      CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv eJ.symm hchev,
      by rw [Nat.card_congr eJ.toEquiv]; exact hdvd⟩ ?_ ?_
  ·
    intro _ w hw _ hfixw
    have hmem := hstab' w fun x hx => hfixw x (hJC hx)
    have hdvd' : orderOf w ∣ ℓ := hσord ▸ orderOf_dvd_of_mem_zpowers hmem
    have hone : orderOf w = 1 := (Nat.Coprime.symm hw).eq_one_of_dvd hdvd'
    rw [orderOf_eq_one_iff] at hone
    rw [hone]
    exact (innerAut _).one_mem
  · intro h3 hL
    exact absurd (CFSG.HardMathSupport.Dickson.I271.isLTwoTwentySeven_of_mulEquiv eJ hL)
      (hL27 h3)

end Entrywise

section Tags


theorem card_pow_six_dvd (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (k : Type) [Field k] [Finite k] : Nat.card k ^ 6 ∣ Nat.card ↥(adjointGroup τ k) := by
  have hN : 6 ≤ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    · rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2]
    · rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4]; norm_num
    · rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E6]; norm_num
    · rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E7]; norm_num
    · rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E8]; norm_num
  have h1 : Nat.card ↥(posUnipotent τ k) ∣ Nat.card ↥(adjointGroup τ k) :=
    Subgroup.card_dvd_of_le posUnipotent_le_adjointGroup
  rw [card_posUnipotent] at h1
  exact (pow_dvd_pow _ hN).trans h1

theorem stab_adjoint (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = ℓ) :
    ∀ w : MulAut (adjointGroup τ K),
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → w j = j) →
        w ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have hofNF : (∀ η : MulAut (adjointGroup τ K), ∃ gβ : adjointGroup τ K × (K ≃+* K),
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2) →
      ∀ w : MulAut (adjointGroup τ K),
        (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → w j = j) →
          w ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ) := by
    intro hNF w hw
    obtain ⟨η, hη, hwη⟩ :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.odd_hfixer_of_normalForm hℓ2 hNF σ w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
      (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hη)
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hwη, ← hn]
    exact (map_zpow (entrywiseAdjointAutHom (τ := τ)) σ n).symm
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  ·
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      obtain ⟨hdvd, hkcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hK σ
      rw [hσ] at hdvd hkcard
      have hd : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by norm_num)
      exact CFSG.SignalizerFunctorTheorem.CatalogBridge.threeG2_zpowers_of_fixes hf hd
        (Nat.div_dvd_of_dvd hdvd) K hK σ hkcard
    · exact hofNF fun η => (CFSG.RankThree.Chevalley.conj_normalForm_of_pointwise
        (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
          (Or.inr ⟨rfl, hℓ3⟩)).1 η).exists
  ·
    exact hofNF fun η => (CFSG.RankThree.Chevalley.conj_normalForm_of_pointwise
      (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .F4
        (Or.inl rfl)).1 η).exists
  ·
    intro w hw
    exact FieldGraphFieldPointwise.mem_zpowers_of_forall_fixedFieldImage σ hw
  ·
    exact CFSG.SignalizerFunctorTheorem.CatalogBridge.odd_E7_zpowers_of_fixes hℓ hℓ2 hf K hK σ
  ·
    exact hofNF fun η =>
      ((CFSG.RankThree.Chevalley.odd_E8_inner_field_automorphisms_and_noninner_prime_core hℓ hℓ2
        hf K hK).1 η).exists

theorem isChevSimple_adjoint
    (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hd : 1 ≤ d) (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = ℓ ^ d) : IsChevSimple ℓ ↥(adjointGroup τ k) := by
  let q₀ : TauCeti.PrimePower := ⟨ℓ, d, hℓ, hd⟩
  have hq₀ : Nat.card k = q₀.card := by rw [hk, TauCeti.PrimePower.card_def]
  have hZ : Subgroup.center (adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  let eQ : ↥(adjointGroup τ k) ≃* AdjointQuotient τ k :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hv0 : ∀ c : TauCeti.LieTypeIndex, c.InStandardRange → ¬ c.IsDuplicateRepresentative →
      c.Valid := fun c h1 h2 => (TauCeti.LieTypeIndex.valid_iff c).2 ⟨h1, h2⟩
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · have hv : (TauCeti.LieTypeIndex.G2 q₀).Valid := by
      refine hv0 _ ?_ ?_
      · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
        show 3 ≤ q₀.card
        rw [TauCeti.PrimePower.card_def]
        calc 3 ≤ ℓ := by have := hℓ.two_le; omega
          _ ≤ ℓ ^ d := Nat.le_self_pow (by omega) ℓ
      · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact fun h => h
    obtain ⟨φ⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q₀ hv hℓ2 k hq₀
    exact Or.inl ⟨.lie ⟨.G2 q₀, hv⟩, TauCeti.LieTypeIndex.characteristic_G2 q₀, ⟨eQ.trans φ⟩⟩
  · have hv : (TauCeti.LieTypeIndex.F4 q₀).Valid := by
      refine hv0 _ ?_ ?_
      · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
        trivial
      · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact fun h => h
    obtain ⟨φ⟩ := CFSG.TauCetiBridge.untwistedBridge_F4 q₀ hv hℓ2 k hq₀
    exact Or.inl ⟨.lie ⟨.F4 q₀, hv⟩, TauCeti.LieTypeIndex.characteristic_F4 q₀, ⟨eQ.trans φ⟩⟩
  · have hv : (TauCeti.LieTypeIndex.E6 q₀).Valid := by
      refine hv0 _ ?_ ?_
      · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
        trivial
      · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact fun h => h
    obtain ⟨φ⟩ := CFSG.TauCetiBridge.untwistedBridge_E6 q₀ hv hℓ2 k hq₀
    exact Or.inl ⟨.lie ⟨.E6 q₀, hv⟩, TauCeti.LieTypeIndex.characteristic_E6 q₀, ⟨eQ.trans φ⟩⟩
  · have hv : (TauCeti.LieTypeIndex.E7 q₀).Valid := by
      refine hv0 _ ?_ ?_
      · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
        trivial
      · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact fun h => h
    obtain ⟨φ⟩ := CFSG.TauCetiBridge.untwistedBridge_E7 q₀ hv hℓ2 k hq₀
    exact Or.inl ⟨.lie ⟨.E7 q₀, hv⟩, TauCeti.LieTypeIndex.characteristic_E7 q₀, ⟨eQ.trans φ⟩⟩
  · have hv : (TauCeti.LieTypeIndex.E8 q₀).Valid := by
      refine hv0 _ ?_ ?_
      · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
        trivial
      · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact fun h => h
    obtain ⟨φ⟩ := CFSG.TauCetiBridge.untwistedBridge_E8 q₀ hv hℓ2 k hq₀
    exact Or.inl ⟨.lie ⟨.E8 q₀, hv⟩, TauCeti.LieTypeIndex.characteristic_E8 q₀, ⟨eQ.trans φ⟩⟩

theorem outerCentData_adjoint
    (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup τ K)) (hα : orderOf α = ℓ)
    (hout : α ∉ innerAut (adjointGroup τ K)) : OuterCentData ℓ α := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have : Finite (ModGL τ K) := finite_modGL
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hαp : α ^ ℓ = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  obtain ⟨r, j, δ, σ, hσ, hrj, hδ⟩ : ∃ (r j : ℕ) (δ : MulAut (adjointGroup τ K)) (σ : K ≃+* K),
      orderOf σ = ℓ ∧ (α ^ r) ^ j = α ∧ δ * α ^ r * δ⁻¹ = entrywiseAdjointAut τ σ := by
    rcases hτ with rfl | rfl | hE
    ·
      obtain ⟨x, σ, hσp, hασ⟩ : ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
          orderOf σ = ℓ ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
        by_cases hℓ3 : ℓ = 3
        · subst hℓ3
          exact CFSG.HardMathSupport.Lang.E6Descent.G2_form_three hf K hK hℓ hℓ2 α hα hout
        · exact CFSG.HardMathSupport.Lang.E6Descent.G2_form_odd hℓ hℓ2 hℓ3 hf K hK hℓ α hα hout
      obtain ⟨δ, hδ⟩ :=
        CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_entrywiseAdjointAut_of_form
          Tag.G2 hℓ hf K hK hℓ α hα x σ hσp hασ
      exact ⟨1, 1, δ, σ, hσp, by rw [pow_one, pow_one], by rw [pow_one]; exact hδ⟩
    ·
      obtain ⟨x, σ, δ, hσp, -, hδ, -, -⟩ :=
        odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hℓ α hα hout
      exact ⟨1, 1, δ, σ, hσp, by rw [pow_one, pow_one], by rw [pow_one]; exact hδ⟩
    ·
      have hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
          α ≠ MulAut.conj g * rootDiagAut τ K a := by
        intro g a h
        have hdvd :=
          (CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hE K hℓ g a α h hαp
            hout).2
        rw [hK] at hdvd
        have h1 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
        have h2 : ℓ ∣ ℓ ^ f - (ℓ ^ f - 1) := Nat.dvd_sub h1 hdvd
        rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
        exact hℓ.one_lt.ne' (Nat.dvd_one.1 h2)
      obtain ⟨d, T, r, j, ψ, -, hTord, -, -, -, hαβ, hψ⟩ :=
        CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag τ hE hf K hK
          hℓ hℓ2 α hαp hnd
      exact ⟨r, j, ψ, T, hTord, hαβ, hψ⟩
  refine outerCentData_of_pow r ?_ (fixSubgroup_pow_eq hrj)
  refine outerCentData_of_conj hℓ δ ?_
  rw [hδ]
  have hσord : orderOf (entrywiseAdjointAut τ σ) = ℓ := by
    rw [CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut τ.rank_pos σ, hσ]
  have hσout : entrywiseAdjointAut τ σ ∉ innerAut (adjointGroup τ K) := by
    rintro ⟨y, hy⟩
    apply hout
    have h1 : α ^ r = MulAut.conj (δ⁻¹ y) := by
      rw [← mul_conj_mul_inv, hy, ← hδ]
      group
    refine ⟨(δ⁻¹ y) ^ j, ?_⟩
    rw [map_pow, ← h1, hrj]
  obtain ⟨hdvdf, hkcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hK σ
  rw [hσ] at hdvdf hkcard
  have hd : 1 ≤ f / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hdvdf) hℓ.pos
  have hsix := card_pow_six_dvd τ hτ (fixSubfield σ)
  rw [hkcard] at hsix
  refine outerCentData_entrywise τ hℓ hK2 σ hσord hσout (stab_adjoint τ hτ hℓ hℓ2 hf K hK σ hσ)
    (isChevSimple_adjoint τ hτ hℓ hℓ2 hd _ hkcard) ?_ ?_
  · exact ((dvd_pow_self ℓ (by omega)).trans (dvd_pow_self _ (by norm_num))).trans hsix
  · intro h3 hL
    rw [card_of_isLTwoTwentySeven hL] at hsix
    have h729 : ℓ ^ 6 ∣ 9828 := (pow_dvd_pow_of_dvd (dvd_pow_self ℓ (by omega)) 6).trans hsix
    rw [h3] at h729
    norm_num at h729

end Tags

end ExcUntwisted

theorem outerCentData_excUntwisted
    (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a)
    (idx : TauCeti.ValidLieTypeIndex)
    (htag : ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∨ idx.1 = .F4 q ∨ idx.1 = .E6 q ∨
      idx.1 = .E7 q ∨ idx.1 = .E8 q)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = idx.1.characteristic)
    (β : MulAut S) (hβ : orderOf β = p) (hout : β ∉ innerAut S) : OuterCentData p β := by
  obtain ⟨d, hv⟩ := idx
  obtain ⟨q, hq⟩ := htag
  obtain ⟨e⟩ := he
  have key : ∀ (τ : Tag), (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      UntwistedChevalleyModel S τ (q.p ^ q.exponent) → p = q.p → OuterCentData p β := by
    intro τ hτ hmodel hpq
    obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := hmodel
    let θ : S ≃* adjointGroup τ K := e'.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    refine OuterCentData.of_congr hp θ ?_
    subst hpq
    refine ExcUntwisted.outerCentData_adjoint τ hτ q.prime_p hp2 q.exponent_pos K hK
      (MulAut.congr θ β) (by rw [MulEquiv.orderOf_eq]; exact hβ) ?_
    rintro ⟨t, ht⟩
    apply hout
    refine ⟨θ.symm t, ?_⟩
    apply (MulAut.congr θ).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact ht
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_G2 q)
    exact key .G2 (Or.inl rfl) (CFSG.TauCetiBridge.untwistedModel_of_bridge
      CFSG.TauCetiBridge.untwistedBridge_G2 q hv (hpq ▸ hp2) e) hpq
  · have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_F4 q)
    exact key .F4 (Or.inr (Or.inl rfl)) (CFSG.TauCetiBridge.untwistedModel_of_bridge
      CFSG.TauCetiBridge.untwistedBridge_F4 q hv (hpq ▸ hp2) e) hpq
  · have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_E6 q)
    exact key .E6 (Or.inr (Or.inr (Or.inl rfl))) (CFSG.TauCetiBridge.untwistedModel_of_bridge
      CFSG.TauCetiBridge.untwistedBridge_E6 q hv (hpq ▸ hp2) e) hpq
  · have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_E7 q)
    exact key .E7 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_E7 q hv
        (hpq ▸ hp2) e) hpq
  · have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_E8 q)
    exact key .E8 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_E8 q hv
        (hpq ▸ hp2) e) hpq

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
