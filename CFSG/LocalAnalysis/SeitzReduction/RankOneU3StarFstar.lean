module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarGroups
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem eq_one_of_mem_simple_of_mem_normal_pGroup {K : Type*} [Group K] [Finite K]
    {D Q : Subgroup K} (hDs : IsSimpleGroup D) (hDnab : ∃ a b : D, a * b ≠ b * a)
    (hQn : Q.Normal) (hQp : IsPGroup 2 Q) {x : K} (hxD : x ∈ D) (hxQ : x ∈ Q) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hDs
  have := hQn.subgroupOf D
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.subgroupOf D) with h | h
  · have hx : (⟨x, hxD⟩ : D) ∈ Q.subgroupOf D := hxQ
    rw [h] at hx
    exact congrArg Subtype.val (mem_bot.mp hx)
  · exfalso
    have hDle : D ≤ Q := fun d hd => by
      have hd' : (⟨d, hd⟩ : D) ∈ Q.subgroupOf D := h ▸ mem_top _
      exact hd'
    have hDp : IsPGroup 2 D := hQp.to_le hDle
    have hnil : Group.IsNilpotent D := hDp.isNilpotent
    have hZ : center D = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D)).resolve_left
        (Group.IsNilpotent.center_ne_bot D)
    obtain ⟨a, b, hab⟩ := hDnab
    have ha : a ∈ center D := hZ ▸ mem_top a
    exact hab (mem_center_iff.mp ha b).symm

theorem pCore_le_zpowers_of_twoSmall {K : Type*} [Group K] [Finite K] {t : K}
    (ht : orderOf t = 2) {D : Subgroup K} (hDt : D ≤ centralizer ({t} : Set K))
    (hDn : ∀ c ∈ centralizer ({t} : Set K), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hDs : IsSimpleGroup D) (hDnab : ∃ a b : D, a * b ≠ b * a)
    (h2 : ∀ U : Subgroup K, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set K) ⊓ centralizer (D : Set K) → Nat.card U ≤ 2) :
    CFSG.pCore 2 K ≤ zpowers t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  have hQp : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
  have hyD : ∀ y ∈ CFSG.pCore 2 K, y * t = t * y → ∀ d ∈ D, y * d = d * y := by
    intro y hyQ hyt d hd
    have hyC : y ∈ centralizer ({t} : Set K) := mem_centralizer_singleton_iff.mpr hyt
    have h1 : d * y * d⁻¹ * y⁻¹ ∈ D := by
      have := mul_mem hd (hDn y hyC d⁻¹ (inv_mem hd))
      simpa only [mul_assoc] using this
    have h2' : d * y * d⁻¹ * y⁻¹ ∈ CFSG.pCore 2 K :=
      mul_mem (hQn.conj_mem y hyQ d) (inv_mem hyQ)
    have h3 := eq_one_of_mem_simple_of_mem_normal_pGroup hDs hDnab hQn hQp h1 h2'
    have hdy : d * y = y * d := by
      calc d * y = d * y * d⁻¹ * y⁻¹ * (y * d) := by group
        _ = y * d := by rw [h3]; group
    exact hdy.symm
  refine le_zpowers_of_isPGroup_of_centralizer hQp ht ?_ ?_
  · rw [normalizer_eq_top]
    exact mem_top t
  · intro U hU hUle hUt
    refine h2 U hU (le_inf hUt ?_)
    intro u hu
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_normal_left.mp (hUle hu)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hzt : t ^ k * t = t * t ^ k := (Commute.self_zpow t k).eq.symm
    have hut : y * t ^ k * t = t * (y * t ^ k) := mem_centralizer_singleton_iff.mp (hUt hu)
    have hyt : y * t = t * y := by
      have h' : y * t ^ k * t * (t ^ k)⁻¹ = t * (y * t ^ k) * (t ^ k)⁻¹ := by rw [hut]
      calc y * t = y * (t ^ k * t * (t ^ k)⁻¹) := by rw [hzt]; group
        _ = y * t ^ k * t * (t ^ k)⁻¹ := by group
        _ = t * (y * t ^ k) * (t ^ k)⁻¹ := h'
        _ = t * y := by group
    rw [mem_centralizer_iff]
    intro d hd
    have htd : t * d = d * t := (mem_centralizer_singleton_iff.mp (hDt hd)).symm
    have htkd : t ^ k * d = d * t ^ k := ((Commute.zpow_left htd k)).eq
    calc d * (y * t ^ k) = (d * y) * t ^ k := by group
      _ = (y * d) * t ^ k := by rw [hyD y hy hyt d hd]
      _ = y * (d * t ^ k) := by group
      _ = y * (t ^ k * d) := by rw [htkd]
      _ = y * t ^ k * d := by group

theorem mem_center_of_zpowers_normal {K : Type*} [Group K] {t : K} (ht : orderOf t = 2)
    (hn : (zpowers t).Normal) : t ∈ center K := by
  rw [mem_center_iff]
  intro g
  have hg : g * t * g⁻¹ ∈ zpowers t := hn.conj_mem t (mem_zpowers t) g
  have hcases : ∀ x ∈ zpowers t, x = 1 ∨ x = t := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have h2 : t ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← ht, pow_orderOf_eq_one]
    rw [zpow_eq_zpow_emod k h2]
    have h0 := Int.emod_nonneg k (by norm_num : (2 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 2)
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h <;> rw [h]
    · exact Or.inl (zpow_zero t)
    · exact Or.inr (zpow_one t)
  rcases hcases _ hg with h | h
  · exfalso
    have ht1 : t = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using this
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h]

theorem eq_bot_of_perfect_of_le_centralizer_of_twoSmall {K : Type} [Group K] [Finite K]
    {t : K} (ht : t ^ 2 = 1) {D : Subgroup K} (hDt : D ≤ centralizer ({t} : Set K))
    (h2 : ∀ U : Subgroup K, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set K) ⊓ centralizer (D : Set K) → Nat.card U ≤ 2)
    {E : Subgroup K} (hE : Group.IsPerfect E) (hED : E ≤ centralizer (D : Set K)) : E = ⊥ := by
  have htD : zpowers t ≤ centralizer (D : Set K) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro d hd
    exact mem_centralizer_singleton_iff.mp (hDt hd)
  exact eq_bot_of_perfect_of_centralizer_two_small hE ht fun U hU hUle hUt =>
    h2 U hU (le_inf hUt (hUle.trans (sup_le hED htD)))

theorem centralizer_layer_eq_bot_of_pCore_eq_bot {K : Type} [Group K] [Finite K]
    (hO : CFSG.pPrimeCore 2 K = ⊥) (h2 : CFSG.pCore 2 K = ⊥) :
    centralizer ((CFSG.layer K : Subgroup K) : Set K) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.fittingSubgroup K = ⊥ := (CFSG.Fitting_eq_pcore K 2 hO).trans h2
  have hgen : CFSG.generalizedFitting K = CFSG.layer K := by
    rw [CFSG.generalizedFitting, hF, bot_sup_eq]
  have hle : centralizer ((CFSG.layer K : Subgroup K) : Set K) ≤ CFSG.layer K :=
    hgen ▸ CFSG.centralizer_generalizedFitting_le K
  set Z := centralizer ((CFSG.layer K : Subgroup K) : Set K) with hZ
  have hEc : (CFSG.layer K).Characteristic := CFSG.LocalCores.layer_characteristic (G := K)
  have hEn : (CFSG.layer K).Normal := inferInstance
  have hZn : Z.Normal := inferInstance
  have hZc : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext <| by
    have hb : (b : K) ∈ CFSG.layer K := hle b.2
    exact (mem_centralizer_iff.mp a.2 b hb).symm⟩⟩
  have hZnil : Group.IsNilpotent Z := inferInstance
  have hZF : Z ≤ CFSG.fittingSubgroup K := le_sSup ⟨hZn, hZnil⟩
  rw [hF] at hZF
  exact le_bot_iff.mp hZF

theorem layer_eq_sup_orbit_of_twoSmall {K : Type} [Group K] [Finite K]
    (hO : CFSG.pPrimeCore 2 K = ⊥) {t : K} (ht : t ^ 2 = 1) {D : Subgroup K}
    (hDt : D ≤ centralizer ({t} : Set K))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set K))))
    (h2 : ∀ U : Subgroup K, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set K) ⊓ centralizer (D : Set K) → Nat.card U ≤ 2) :
    ∃ J : Subgroup K, IsComponent J ∧ D ≤ J ⊔ J.map (MulAut.conj t).toMonoidHom ∧
      (∀ L : Subgroup K, IsComponent L → L = J ∨ L = J.map (MulAut.conj t).toMonoidHom) ∧
      CFSG.layer K = J ⊔ J.map (MulAut.conj t).toMonoidHom ∧
      (J.map (MulAut.conj t).toMonoidHom = J → D ≤ J) ∧
      (J.map (MulAut.conj t).toMonoidHom ≠ J →
        ⁅J, J.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧ Nonempty (D ⧸ center D ≃* J ⧸ center J)) := by
  obtain ⟨-, J, hJ, -, hDJ, -, hcomp, hfix, hmove⟩ :=
    CFSG.SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer
      hO ht hDt hD
  have hall : ∀ L : Subgroup K, IsComponent L →
      L = J ∨ L = J.map (MulAut.conj t).toMonoidHom := by
    intro L hL
    refine (hcomp L hL).mp fun hDL => ?_
    have hLD : L ≤ centralizer (D : Set K) := by
      rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
      exact hDL
    have hbot : L = ⊥ :=
      eq_bot_of_perfect_of_le_centralizer_of_twoSmall ht hDt h2 hL.1.1 hLD
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    subst hbot
    exact (nontrivial_iff_ne_bot _).mp hnt rfl
  refine ⟨J, hJ, hDJ, hall, le_antisymm ?_ ?_, fun h => (hfix h).1, fun h =>
    ⟨(hmove h).1, (hmove h).2.2.2⟩⟩
  · refine sSup_le fun L hL => ?_
    rcases hall L hL with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (CFSG.LocalCores.component_le_layer hJ)
      (CFSG.LocalCores.component_le_layer
        (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hJ))

theorem trichotomy_of_twoSmall_component {K : Type} [Group K] [Finite K]
    (hO : CFSG.pPrimeCore 2 K = ⊥) {t : K} (ht : orderOf t = 2) {D : Subgroup K}
    (hDt : D ≤ centralizer ({t} : Set K))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set K))))
    (hDn : ∀ c ∈ centralizer ({t} : Set K), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hDs : IsSimpleGroup D) (hDnab : ∃ a b : D, a * b ≠ b * a)
    (h2 : ∀ U : Subgroup K, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set K) ⊓ centralizer (D : Set K) → Nat.card U ≤ 2) :
    t ∈ center K ∨
      ∃ J : Subgroup K, IsComponent J ∧ D ≤ J ⊔ J.map (MulAut.conj t).toMonoidHom ∧
        (∀ L : Subgroup K, IsComponent L → L = J ∨ L = J.map (MulAut.conj t).toMonoidHom) ∧
        CFSG.layer K = J ⊔ J.map (MulAut.conj t).toMonoidHom ∧
        centralizer ((CFSG.layer K : Subgroup K) : Set K) = ⊥ ∧
        (J.map (MulAut.conj t).toMonoidHom = J → D ≤ J) ∧
        (J.map (MulAut.conj t).toMonoidHom ≠ J →
          ⁅J, J.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
            Nonempty (D ⧸ center D ≃* J ⧸ center J)) := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hle := pCore_le_zpowers_of_twoSmall ht hDt hDn hDs hDnab h2
  have hz2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  have hdvd : Nat.card (CFSG.pCore 2 K) ∣ 2 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hz2] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
  · have hbot : CFSG.pCore 2 K = ⊥ := Subgroup.card_eq_one.mp h1
    obtain ⟨J, hJ, hDJ, hall, hlayer, hfix, hmove⟩ :=
      layer_eq_sup_orbit_of_twoSmall hO ht2 hDt hD h2
    exact Or.inr ⟨J, hJ, hDJ, hall, hlayer, centralizer_layer_eq_bot_of_pCore_eq_bot hO hbot,
      hfix, hmove⟩
  · left
    have heq : CFSG.pCore 2 K = zpowers t :=
      eq_of_le_of_card_ge hle (by rw [hz2, h2'])
    have hn : (zpowers t).Normal := heq ▸ CFSG.pCore_normal
    exact mem_center_of_zpowers_normal ht hn

end CFSG.SeitzReduction.RankOne
