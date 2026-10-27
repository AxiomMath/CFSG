module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarFstar
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarQuot
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarCat
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

theorem two_pow_padicValNat_lt {f : ℕ} (hf : 1 ≤ f) : 2 ^ padicValNat 2 f < 2 ^ f :=
  lt_of_le_of_lt (Nat.le_of_dvd (by omega) pow_padicValNat_dvd) f.lt_two_pow_self

theorem caseA_lt {f : ℕ} (hf : 1 ≤ f) :
    2 * 2 ^ f * 2 ^ padicValNat 2 f < 2 * (2 ^ f) ^ 4 := by
  have h1 := two_pow_padicValNat_lt hf
  have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h3 : 1 ≤ 2 ^ padicValNat 2 f := Nat.one_le_two_pow
  set a := 2 ^ f
  set b := 2 ^ padicValNat 2 f
  have : a * b < a * a := Nat.mul_lt_mul_of_pos_left h1 (by omega)
  have h4 : a * a ≤ a ^ 4 := by
    have e : a ^ 4 = (a * a) * (a * a) := by ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have e2 : 2 * a * b = 2 * (a * b) := by ring
  omega

theorem caseB_lt {f : ℕ} (hf : 1 ≤ f) :
    2 * ((2 ^ f * 2 ^ padicValNat 2 f) * (2 ^ f * 2 ^ padicValNat 2 f)) < 2 * (2 ^ f) ^ 4 := by
  have h1 := two_pow_padicValNat_lt hf
  have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  set a := 2 ^ f
  set b := 2 ^ padicValNat 2 f
  have h5 : a * b < a * a := Nat.mul_lt_mul_of_pos_left h1 (by omega)
  have h6 : (a * b) * (a * b) < (a * a) * (a * a) := Nat.mul_self_lt_mul_self h5
  have h7 : (a * a) * (a * a) = a ^ 4 := by ring
  omega

section Conj

variable {K : Type*} [Group K]

theorem map_conj_map_conj_eq (J : Subgroup K) (a b : K) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem mem_normalizer_iff_map_conj (J : Subgroup K) (g : K) :
    g ∈ normalizer (J : Set K) ↔ J.map (MulAut.conj g).toMonoidHom = J :=
  mem_normalizer_iff_map_conj_eq

end Conj

theorem card_le_two_mul_card_inf_of_forall_mem_or {K : Type*} [Group K] [Finite K]
    {N : Subgroup K} {s : K} (hN : ∀ g : K, g ∈ N ∨ s * g ∈ N) (P : Subgroup K) :
    Nat.card P ≤ 2 * Nat.card (P ⊓ N : Subgroup K) := by
  classical
  by_cases hPN : P ≤ N
  · rw [inf_of_le_left hPN]
    omega
  · obtain ⟨p₀, hp₀P, hp₀N⟩ := Set.not_subset.mp hPN
    have hsp₀ : s * p₀ ∈ N := (hN p₀).resolve_left hp₀N
    have hmem : ∀ p : P, (p : K) ∉ N → p₀⁻¹ * p ∈ P ⊓ N := fun p hp => by
      refine mem_inf.mpr ⟨mul_mem (inv_mem hp₀P) p.2, ?_⟩
      have hsp : s * p ∈ N := (hN p).resolve_left hp
      have e : (s * p₀)⁻¹ * (s * p) = p₀⁻¹ * p := by group
      rw [← e]
      exact mul_mem (inv_mem hsp₀) hsp
    let F : P → (P ⊓ N : Subgroup K) ⊕ (P ⊓ N : Subgroup K) := fun p =>
      if hp : (p : K) ∈ N then Sum.inl ⟨p, mem_inf.mpr ⟨p.2, hp⟩⟩ else Sum.inr ⟨_, hmem p hp⟩
    have hF : Function.Injective F := by
      intro p p' h
      by_cases hp : (p : K) ∈ N <;> by_cases hp' : (p' : K) ∈ N <;>
        simp [F, hp, hp'] at h <;> exact h
    have := Nat.card_le_card_of_injective F hF
    rw [Nat.card_sum] at this
    omega

theorem mem_normalizer_pair_or {K : Type*} [Group K] {s : K} (hs : s ^ 2 = 1) {J : Subgroup K}
    (hJ : IsComponent J) (hne : J.map (MulAut.conj s).toMonoidHom ≠ J)
    (hall : ∀ L : Subgroup K, IsComponent L → L = J ∨ L = J.map (MulAut.conj s).toMonoidHom)
    (g : K) :
    g ∈ normalizer (J : Set K) ⊓
        normalizer ((J.map (MulAut.conj s).toMonoidHom : Subgroup K) : Set K) ∨
      s * g ∈ normalizer (J : Set K) ⊓
        normalizer ((J.map (MulAut.conj s).toMonoidHom : Subgroup K) : Set K) := by
  set J' := J.map (MulAut.conj s).toMonoidHom with hJ'
  have hJ'c : IsComponent J' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hJ
  have key : ∀ x : K, J.map (MulAut.conj x).toMonoidHom = J →
      x ∈ normalizer (J : Set K) ⊓ normalizer (J' : Set K) := by
    intro x hx
    refine mem_inf.mpr ⟨(mem_normalizer_iff_map_conj J x).mpr hx, ?_⟩
    rcases hall _ (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hJ'c) with h | h
    · exfalso
      apply hne
      apply map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
      rw [hx]
      exact h
    · exact (mem_normalizer_iff_map_conj J' x).mpr h
  rcases hall _ (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ) with h | h
  · exact Or.inl (key g h)
  · refine Or.inr (key (s * g) ?_)
    rw [← map_conj_map_conj_eq, h, hJ']
    exact CentralizerComponents.map_conj_map_conj hs J

theorem card_le_of_le_normalizer_pair {K : Type*} [Group K] [Finite K] {J J' : Subgroup K}
    (hC : centralizer ((J ⊔ J' : Subgroup K) : Set K) = ⊥) {b : ℕ}
    (hJ : ∀ Q : Subgroup (MulAut J), IsPGroup 2 Q → Nat.card Q ≤ b)
    (hJ' : ∀ Q : Subgroup (MulAut J'), IsPGroup 2 Q → Nat.card Q ≤ b)
    {R : Subgroup K} (hR : IsPGroup 2 R)
    (hRN : R ≤ normalizer (J : Set K) ⊓ normalizer (J' : Set K)) : Nat.card R ≤ b * b := by
  have hRN₁ : R ≤ normalizer (J : Set K) := hRN.trans inf_le_left
  have hR₁N : R ⊓ centralizer (J : Set K) ≤ normalizer (J' : Set K) :=
    inf_le_left.trans (hRN.trans inf_le_right)
  rw [card_eq_card_inf_centralizer_mul_card_range hRN₁,
    card_eq_card_inf_centralizer_mul_card_range hR₁N]
  have hbot : R ⊓ centralizer (J : Set K) ⊓ centralizer (J' : Set K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxJ : x ∈ centralizer (J : Set K) := (mem_inf.mp (mem_inf.mp hx).1).2
    have hxJ' : x ∈ centralizer (J' : Set K) := (mem_inf.mp hx).2
    have hle : J ⊔ J' ≤ centralizer ({x} : Set K) := sup_le
      (fun y hy => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxJ y hy))
      (fun y hy => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxJ' y hy))
    have hxC : x ∈ centralizer ((J ⊔ J' : Subgroup K) : Set K) :=
      mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)
    rw [hC] at hxC
    exact hxC
  rw [hbot, card_bot, one_mul]
  have h1 := hJ' (J'.normalizerMonoidHom.comp (inclusion hR₁N)).range
    ((hR.to_le inf_le_left).of_surjective _ (MonoidHom.rangeRestrict_surjective _))
  have h2 := hJ (J.normalizerMonoidHom.comp (inclusion hRN₁)).range
    (hR.of_surjective _ (MonoidHom.rangeRestrict_surjective _))
  exact Nat.mul_le_mul h1 h2

theorem mem_centralizer_sup_of_mem {K : Type*} [Group K] {A B : Subgroup K} {x : K}
    (hA : x ∈ centralizer (A : Set K)) (hB : x ∈ centralizer (B : Set K)) :
    x ∈ centralizer ((A ⊔ B : Subgroup K) : Set K) := by
  have hle : A ⊔ B ≤ centralizer ({x} : Set K) := sup_le
    (fun y hy => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hA y hy))
    (fun y hy => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hB y hy))
  exact mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)

theorem card_le_of_two_components {K : Type} [Group K] [Finite K] {s : K} (hs : s ^ 2 = 1)
    {J : Subgroup K} (hJ : IsComponent J) (hne : J.map (MulAut.conj s).toMonoidHom ≠ J)
    (hall : ∀ L : Subgroup K, IsComponent L → L = J ∨ L = J.map (MulAut.conj s).toMonoidHom)
    (hcomm : ⁅J, J.map (MulAut.conj s).toMonoidHom⁆ = ⊥)
    (hC : centralizer ((J ⊔ J.map (MulAut.conj s).toMonoidHom : Subgroup K) : Set K) = ⊥)
    {f : ℕ} (hf : 2 ≤ f) (eJ : J ⧸ center J ≃* CFSG.Theory.Comparator.PSL2Model f)
    (U : Subgroup K) (hU : IsPGroup 2 U) :
    Nat.card U ≤ 2 * ((2 ^ f * 2 ^ padicValNat 2 f) * (2 ^ f * 2 ^ padicValNat 2 f)) := by
  set J' := J.map (MulAut.conj s).toMonoidHom with hJ'
  have hJJ' : J ≤ centralizer (J' : Set K) := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hZJ : center J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz1 : (z : K) ∈ centralizer (J : Set K) := mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
    have hz2 := mem_centralizer_sup_of_mem hz1 (hJJ' z.2)
    rw [hC, mem_bot] at hz2
    exact mem_bot.mpr (Subtype.ext hz2)
  let eJ₁ : J ≃* CFSG.Theory.Comparator.PSL2Model f := (quotientCenterMulEquiv hZJ).symm.trans eJ
  let eJ₂ : J' ≃* CFSG.Theory.Comparator.PSL2Model f :=
    (J.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective).symm.trans eJ₁
  have hb₁ := fun (Q : Subgroup (MulAut J)) (hQ : IsPGroup 2 Q) =>
    card_le_of_isPGroup_mulAut_psl2 hf eJ₁ hQ
  have hb₂ := fun (Q : Subgroup (MulAut J')) (hQ : IsPGroup 2 Q) =>
    card_le_of_isPGroup_mulAut_psl2 hf eJ₂ hQ
  have h1 := card_le_two_mul_card_inf_of_forall_mem_or (mem_normalizer_pair_or hs hJ hne hall) U
  have h2 := card_le_of_le_normalizer_pair hC hb₁ hb₂ (hU.to_le inf_le_left) inf_le_right
  calc Nat.card U ≤ 2 * Nat.card (U ⊓ (normalizer (J : Set K) ⊓ normalizer (J' : Set K)) :
      Subgroup K) := h1
    _ ≤ _ := Nat.mul_le_mul_left _ h2

theorem card_lt_of_one_component {K : Type} [Group K] [Finite K] {t : K} (ht : orderOf t = 2)
    {J : Subgroup K} [J.Normal] (hJq : IsQuasisimple J) (hC : centralizer (J : Set K) = ⊥)
    (hcatJ : IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) → Catalog J)
    {D : Subgroup K} (hDJ : D ≤ J) (hDt : D ≤ centralizer ({t} : Set K))
    (hDn : ∀ c ∈ centralizer ({t} : Set K), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    {f : ℕ} (hf : 2 ≤ f) (eD : D ≃* CFSG.Theory.Comparator.PSL2Model f)
    (h2 : ∀ U : Subgroup K, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set K) ⊓ centralizer (D : Set K) → Nat.card U ≤ 2)
    (hcat : CatSL2Bound f) (U : Subgroup K) (hU : IsPGroup 2 U) :
    Nat.card U < 2 * (2 ^ f) ^ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZJ : center J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz1 : (z : K) ∈ centralizer (J : Set K) := mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
    rw [hC, mem_bot] at hz1
    exact mem_bot.mpr (Subtype.ext hz1)
  let e₀ : J ⧸ center J ≃* J := quotientCenterMulEquiv hZJ
  have : IsSimpleGroup (J ⧸ center J) := hJq.2.1
  have hJs : IsSimpleGroup J := e₀.symm.isSimpleGroup
  have hJnab : ∃ a b : J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJq.2.2
    exact ⟨e₀ a, e₀ b, fun h => hab (e₀.injective (by rw [map_mul, map_mul, h]))⟩
  set τ : MulAut J := MulAut.conjNormal t with hτdef
  have hτapp : ∀ j : J, ((τ j : J) : K) = t * j * t⁻¹ := fun j => MulAut.conjNormal_apply t j
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hτ2 : τ ^ 2 = 1 := by
    rw [hτdef, ← map_pow, ht2, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h1
    have htC : t ∈ centralizer (J : Set K) := mem_centralizer_iff.mpr fun j hj => by
      have := congrArg (fun φ : MulAut J => ((φ ⟨j, hj⟩ : J) : K)) h1
      simp only [hτapp, MulAut.one_apply] at this
      calc j * t = t * j * t⁻¹ * t := by rw [this]
        _ = t * j := by group
    rw [hC, mem_bot] at htC
    rw [htC, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hτ : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ1
  have hfixiff : ∀ j : J, j ∈ fixedSubgroup τ ↔ (j : K) ∈ centralizer ({t} : Set K) := by
    intro j
    change τ j = j ↔ _
    rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, hτapp]
    constructor
    · intro h
      calc (j : K) * t = t * j * t⁻¹ * t := by rw [h]
        _ = t * j := by group
    · intro h
      calc t * (j : K) * t⁻¹ = j * t * t⁻¹ := by rw [h]
        _ = j := by group
  set DJ : Subgroup J := D.subgroupOf J with hDJdef
  have hDJfix : DJ ≤ fixedSubgroup τ := fun d hd => (hfixiff d).mpr (hDt hd)
  set D' : Subgroup (fixedSubgroup τ) := DJ.subgroupOf (fixedSubgroup τ) with hD'def
  let eD' : D' ≃* CFSG.Theory.Comparator.PSL2Model f :=
    ((subgroupOfEquivOfLe hDJfix).trans (subgroupOfEquivOfLe hDJ)).trans eD
  obtain ⟨hPs, a, b, hab⟩ := psl2Model_simple_nonabelian hf
  have hD's : IsSimpleGroup D' := eD'.isSimpleGroup
  have hD'nab : ∃ a b : D', a * b ≠ b * a :=
    ⟨eD'.symm a, eD'.symm b, fun h => hab (by
      have := congrArg eD' h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this)⟩
  have hD'n : D'.Normal := (normal_subgroupOf_iff hDJfix).mpr fun h k hh hk => by
    change ((k * h * k⁻¹ : J) : K) ∈ D
    exact hDn k ((hfixiff k).mp hk) h hh
  have hD' : IsComponent D' := isComponent_of_normal_of_simple hD'n hD's hD'nab
  have hZD' : center D' = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hD'nab).2
  have hLie : LieModel (D' ⧸ center D') .PSL 2 2 f :=
    lieModel_psl2_of_mulEquiv hf ((quotientCenterMulEquiv hZD').trans eD')
  have hsmall : FixedCentralizerTwoSmall τ D' := by
    intro V hV hVc hVfix
    have hle : V.map J.subtype ≤ centralizer ({t} : Set K) ⊓ centralizer (D : Set K) := by
      rintro _ ⟨v, hv, rfl⟩
      refine mem_inf.mpr ⟨(hfixiff v).mp (hVfix hv), mem_centralizer_iff.mpr fun d hd => ?_⟩
      have hdD' : (⟨⟨d, hDJ hd⟩, hDJfix hd⟩ : fixedSubgroup τ) ∈ D' := hd
      have h1 := mem_centralizer_iff.mp (hVc hv) _ ⟨_, hdD', rfl⟩
      exact congrArg Subtype.val h1
    have h1 := h2 _ (hV.map J.subtype) hle
    rwa [card_map_of_injective J.subtype_injective] at h1
  exact card_lt_of_centralizer_eq_bot hC hU
    (hcat J hJs hJnab (hcatJ hJs hJnab) τ hτ D' hD' hLie hsmall)

theorem card_lt_of_twoSmall_component {K : Type} [Group K] [Finite K]
    (hO : CFSG.pPrimeCore 2 K = ⊥) {t : K} (ht : orderOf t = 2) {D : Subgroup K}
    (hDt : D ≤ centralizer ({t} : Set K))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set K))))
    (hDn : ∀ c ∈ centralizer ({t} : Set K), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    {f : ℕ} (hf : 2 ≤ f) (eD : D ≃* CFSG.Theory.Comparator.PSL2Model f)
    (h2 : ∀ U : Subgroup K, IsPGroup 2 U →
      U ≤ centralizer ({t} : Set K) ⊓ centralizer (D : Set K) → Nat.card U ≤ 2)
    (h4 : ∀ U : Subgroup K, IsPGroup 2 U → U ≤ centralizer ({t} : Set K) →
      2 * Nat.card U ≤ 4 * 2 ^ f * 2 ^ padicValNat 2 f)
    (hcatK : ∀ T : Subgroup K, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) → Catalog T)
    (hcat : CatSL2Bound f) (U : Subgroup K) (hU : IsPGroup 2 U) :
    Nat.card U < 2 * (2 ^ f) ^ 4 := by
  classical
  obtain ⟨hPs, a, b, hab⟩ := psl2Model_simple_nonabelian hf
  have hDs : IsSimpleGroup D := eD.isSimpleGroup
  have hDnab : ∃ a b : D, a * b ≠ b * a :=
    ⟨eD.symm a, eD.symm b, fun h => hab (by
      have := congrArg eD h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this)⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  rcases trichotomy_of_twoSmall_component hO ht hDt hD hDn hDs hDnab h2 with
    hcen | ⟨J, hJ, -, hall, hlayer, hC, hfix, hmove⟩
  ·
    have htop : centralizer ({t} : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hcen g)
    have h := h4 U hU (htop ▸ le_top)
    have := caseA_lt (f := f) (by omega)
    have e1 : 4 * 2 ^ f * 2 ^ padicValNat 2 f = 2 * (2 * 2 ^ f * 2 ^ padicValNat 2 f) := by ring
    rw [e1] at h
    omega
  · by_cases hJt : J.map (MulAut.conj t).toMonoidHom = J
    ·
      rw [hJt, sup_idem] at hlayer
      have hEc : (CFSG.layer K).Characteristic := CFSG.LocalCores.layer_characteristic
      have hEn : (CFSG.layer K).Normal := inferInstance
      have hJn : J.Normal := hlayer ▸ hEn
      rw [hlayer] at hC
      exact card_lt_of_one_component ht hJ.1 hC (fun hs hnab => hcatK J hs hnab) (hfix hJt)
        hDt hDn hf eD h2 hcat U hU
    ·
      obtain ⟨hcomm, ⟨e⟩⟩ := hmove hJt
      have hZD : center D = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDnab).2
      let eJ : J ⧸ center J ≃* CFSG.Theory.Comparator.PSL2Model f :=
        e.symm.trans ((quotientCenterMulEquiv hZD).trans eD)
      rw [hlayer] at hC
      have h := card_le_of_two_components ht2 hJ hJt hall hcomm hC hf eJ U hU
      have := caseB_lt (f := f) (by omega)
      omega

theorem u3Star_quot {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L)
    {f : ℕ} (hf : 2 ≤ f) (hL : LieModel L .PSU 3 2 f)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {t : G} (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    {w : G} (hw : orderOf w = 2) (hwN : w ∈ normalizer (L : Set G))
    (hwout : ¬ ∃ l ∈ L, ∀ x ∈ L, w * x * w⁻¹ = l * x * l⁻¹)
    (h5 : ∀ g ∈ centralizer ({w} : Set G), g * t * g⁻¹ ≠ t * w)
    (w' t' : centralizer ({w} : Set G)) (hw' : (w' : G) = w) (ht' : (t' : G) = t)
    [(zpowers w').Normal] :
    CFSG.pPrimeCore 2 (centralizer ({w} : Set G) ⧸ zpowers w') = ⊥ ∧
    orderOf (QuotientGroup.mk' (zpowers w') t') = 2 ∧
    (∃ D : Subgroup (centralizer ({w} : Set G) ⧸ zpowers w'),
      D = ((L ⊓ centralizer ({w} : Set G)).subgroupOf (centralizer ({w} : Set G))).map
        (QuotientGroup.mk' (zpowers w')) ∧
      Nonempty (D ≃* CFSG.Theory.Comparator.PSL2Model f) ∧
      D ≤ centralizer ({QuotientGroup.mk' (zpowers w') t'} :
        Set (centralizer ({w} : Set G) ⧸ zpowers w')) ∧
      (∀ c ∈ centralizer ({QuotientGroup.mk' (zpowers w') t'} :
        Set (centralizer ({w} : Set G) ⧸ zpowers w')), ∀ d ∈ D, c * d * c⁻¹ ∈ D) ∧
      IsComponent (D.subgroupOf (centralizer ({QuotientGroup.mk' (zpowers w') t'} :
        Set (centralizer ({w} : Set G) ⧸ zpowers w')))) ∧
      ∀ U : Subgroup (centralizer ({w} : Set G) ⧸ zpowers w'), IsPGroup 2 U →
        U ≤ centralizer ({QuotientGroup.mk' (zpowers w') t'} :
          Set (centralizer ({w} : Set G) ⧸ zpowers w')) ⊓
          centralizer (D : Set (centralizer ({w} : Set G) ⧸ zpowers w')) → Nat.card U ≤ 2) ∧
    (∀ U : Subgroup (centralizer ({w} : Set G) ⧸ zpowers w'), IsPGroup 2 U →
      U ≤ centralizer ({QuotientGroup.mk' (zpowers w') t'} :
        Set (centralizer ({w} : Set G) ⧸ zpowers w')) →
      2 * Nat.card U ≤ 4 * 2 ^ f * 2 ^ padicValNat 2 f) ∧
    (∀ T : Subgroup (centralizer ({w} : Set G) ⧸ zpowers w'), IsSimpleGroup T →
      (∃ a b : T, a * b ≠ b * a) → Catalog T) ∧
    ∀ P : Subgroup G, P ≤ centralizer ({w} : Set G) →
      Nat.card P ≤ 2 * Nat.card ((P.subgroupOf (centralizer ({w} : Set G))).map
        (QuotientGroup.mk' (zpowers w'))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := hset.standardSetting
  obtain ⟨⟨eL⟩, -, -, -, hLwC, hnorm, hL4, hL5⟩ :=
    u3Star_local hset hf hL hS2 ht htC hw hwN hwout
  set Lw := L ⊓ centralizer ({w} : Set G) with hLw
  have hw'Z : w' ∈ center (centralizer ({w} : Set G)) := mem_center_iff.mpr fun g => Subtype.ext (by
    rw [coe_mul, coe_mul, hw']
    exact mem_centralizer_singleton_iff.mp g.2)
  have hw'o : orderOf w' = 2 := by
    rw [← orderOf_injective (centralizer ({w} : Set G)).subtype
      (centralizer ({w} : Set G)).subtype_injective w', Subgroup.coe_subtype, hw', hw]
  have hw'2 : w' ^ 2 = 1 := by rw [← hw'o]; exact pow_orderOf_eq_one w'
  have ht'o : orderOf t' = 2 := by
    rw [← orderOf_injective (centralizer ({w} : Set G)).subtype
      (centralizer ({w} : Set G)).subtype_injective t', Subgroup.coe_subtype, ht', ht]
  have ht'2 : t' ^ 2 = 1 := by rw [← ht'o]; exact pow_orderOf_eq_one t'
  have h5' : ∀ g : (centralizer ({w} : Set G)), g * t' * g⁻¹ ≠ t' * w' := fun g h => h5 g g.2 (by
    have := congrArg Subtype.val h
    simpa only [coe_mul, coe_inv, hw', ht'] using this)
  set π := QuotientGroup.mk' (zpowers w') with hπ
  set D : Subgroup (centralizer ({w} : Set G)) := Lw.subgroupOf (centralizer ({w} : Set G)) with hD
  have hLwY : Lw ≤ (centralizer ({w} : Set G)) := inf_le_right
  let eD₀ : D ≃* CFSG.Theory.Comparator.PSL2Model f := (subgroupOfEquivOfLe hLwY).trans eL
  obtain ⟨hPs, a, b, hab⟩ := psl2Model_simple_nonabelian hf
  have hDs : IsSimpleGroup D := eD₀.isSimpleGroup
  have hDnab : ∃ a b : D, a * b ≠ b * a :=
    ⟨eD₀.symm a, eD₀.symm b, fun h => hab (by
      have := congrArg eD₀ h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this)⟩
  have hcentY : ∀ c : (centralizer ({w} : Set G)),
      c ∈ centralizer ({t'} : Set (centralizer ({w} : Set G))) ↔
        (c : G) ∈ centralizer ({t} : Set G) := by
    intro c
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← Subtype.coe_inj,
      coe_mul, coe_mul, ht']
  have hDt : D ≤ centralizer ({t'} : Set (centralizer ({w} : Set G))) := fun d hd =>
    (hcentY d).mpr (mem_inf.mp (hLwC hd)).2
  have hDn : ∀ c ∈ centralizer ({t'} : Set (centralizer ({w} : Set G))), ∀ d ∈ D,
      c * d * c⁻¹ ∈ D := by
    intro c hc d hd
    exact hnorm c (mem_inf.mpr ⟨c.2, (hcentY c).mp hc⟩) d hd
  obtain ⟨⟨eDbar⟩, -, -, hDbt, hDbn, hDbc⟩ :=
    isComponent_map_mk hw'Z hw'2 h5' hDs hDnab hDt hDn
  have h4Y : ∀ Q : Subgroup (centralizer ({w} : Set G)), IsPGroup 2 Q →
      Q ≤ centralizer ({t'} : Set (centralizer ({w} : Set G))) ⊓
        centralizer (D : Set (centralizer ({w} : Set G))) → Nat.card Q ≤ 4 := by
    intro Q hQ hQle
    have hle : Q.map (centralizer ({w} : Set G)).subtype ≤
        centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (Lw : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨hq1, hq2⟩ := mem_inf.mp (hQle hq)
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨q.2, (hcentY q).mp hq1⟩,
        mem_centralizer_iff.mpr fun y hy => ?_⟩
      have := mem_centralizer_iff.mp hq2 ⟨y, hLwY hy⟩ hy
      exact congrArg Subtype.val this
    have := hL4 _ (hQ.map (centralizer ({w} : Set G)).subtype) hle
    rwa [card_map_of_injective (centralizer ({w} : Set G)).subtype_injective] at this
  have hNY : ∀ Q : Subgroup (centralizer ({w} : Set G)), IsPGroup 2 Q →
      Q ≤ centralizer ({t'} : Set (centralizer ({w} : Set G))) →
        Nat.card Q ≤ 4 * 2 ^ f * 2 ^ padicValNat 2 f := by
    intro Q hQ hQle
    have hle : Q.map (centralizer ({w} : Set G)).subtype ≤
        centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      exact mem_inf.mpr ⟨q.2, (hcentY q).mp (hQle hq)⟩
    have := hL5 _ (hQ.map (centralizer ({w} : Set G)).subtype) hle
    rwa [card_map_of_injective (centralizer ({w} : Set G)).subtype_injective] at this
  have htbar : orderOf (π t') = 2 := by
    refine orderOf_eq_prime (by rw [← map_pow, ht'2, map_one]) ?_
    intro h1
    have hmem : t' ∈ zpowers w' := by
      rw [← QuotientGroup.ker_mk' (zpowers w')]
      exact h1
    rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hw'2 hmem with h | h
    · have h' : t = 1 := by rw [← ht', h, coe_one]
      rw [h', orderOf_one] at ht
      exact absurd ht (by norm_num)
    · have h' : t = w := by rw [← ht', h, hw']
      exact not_mem_centralizer_of_not_inner hwout (h' ▸ htC)
  have hYtop : (centralizer ({w} : Set G)) ≠ ⊤ := by
    intro hYt
    have hwZ : w ∈ center G := mem_center_iff.mpr fun g => by
      have hg : g ∈ (centralizer ({w} : Set G)) := hYt ▸ mem_top g
      exact mem_centralizer_singleton_iff.mp hg
    rw [center_eq_bot_of_simple_nonabelian hst.simple hst.nonab, mem_bot] at hwZ
    rw [hwZ, orderOf_one] at hw
    exact absurd hw (by norm_num)
  refine ⟨pPrimeCore_quotient_zpowers_eq_bot hw'Z hw'2 (hst.core w hw), htbar,
    ⟨D.map π, rfl, ⟨eDbar.symm.trans eD₀⟩, hDbt, hDbn, hDbc,
      card_le_two_of_le_centralizer_map_mk hw'Z hw'o h5' hDs hDnab hDn h4Y⟩,
    two_mul_card_le_of_le_centralizer_mk hw'Z hw'o h5' hNY,
    fun T _ hnab => CFSG.EvenSmallLie.CatalogOrders.catalog_of_kProper_of_le_quotient
      hst.kProper hYtop π (QuotientGroup.mk'_surjective _) T hnab,
    fun P hPw => ?_⟩
  have hPY : Nat.card (P.subgroupOf (centralizer ({w} : Set G))) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe hPw).toEquiv
  have hlift : Nat.card (P.subgroupOf (centralizer ({w} : Set G))) ≤
      2 * Nat.card ((P.subgroupOf (centralizer ({w} : Set G))).map π) :=
    card_le_two_mul_card_map_mk hw'2 (P.subgroupOf (centralizer ({w} : Set G)))
  omega

theorem starPrime_of_catSL2 {f : ℕ} (hf : 2 ≤ f) (hcat : CatSL2Bound f) :
    StarPrimeStatement f := by
  intro G _ _ L hset hL hS2 t ht htC w hw hwt hwN hwout h5 P hP hPw
  have hwY : w ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have htY : t ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr hwt.symm
  set w' : centralizer ({w} : Set G) := ⟨w, hwY⟩ with hw'
  set t' : centralizer ({w} : Set G) := ⟨t, htY⟩ with ht'
  have hw'Z : w' ∈ center (centralizer ({w} : Set G)) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have : (zpowers w').Normal := zpowers_normal_of_mem_center hw'Z
  obtain ⟨hOK, htbar, ⟨D, -, ⟨eD⟩, hDbt, hDbn, hDbc, h2K⟩, h4K, hcatK, hlift⟩ :=
    u3Star_quot hset hf hL hS2 ht htC hw hwN hwout h5 w' t' rfl rfl
  have hK := card_lt_of_twoSmall_component hOK htbar hDbt hDbc hDbn hf eD h2K h4K hcatK hcat
  have h1 := hlift P hPw
  have h2 : Nat.card ((P.subgroupOf (centralizer ({w} : Set G))).map
      (QuotientGroup.mk' (zpowers w'))) < 2 * (2 ^ f) ^ 4 :=
    hK _ (hP.comap_subtype.map (QuotientGroup.mk' (zpowers w')))
  omega

end CFSG.SeitzReduction.RankOne
