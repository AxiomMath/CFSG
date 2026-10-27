module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterGood
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Lemma15Guarded

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

omit [Finite G] in
theorem layerIn_le_map_layer (X : Subgroup G) :
    layerIn X ≤ (CFSG.layer ↥X).map X.subtype := by
  refine sSup_le fun M hM => ?_
  have h1 : (M.subgroupOf X).map X.subtype = M := map_subgroupOf_eq_of_le hM.1
  rw [← h1]
  exact map_mono (CFSG.LocalCores.component_le_layer hM.2)

omit [Finite G] in
theorem mem_centralizer_tv_iff (x : G) :
    x ∈ centralizer ((zpowers t ⊔ zpowers v : Subgroup G) : Set G) ↔
      x * t = t * x ∧ x * v = v * x := by
  constructor
  · intro hx
    rw [mem_centralizer_iff] at hx
    have ht : t ∈ (zpowers t ⊔ zpowers v : Subgroup G) :=
      (show zpowers t ≤ zpowers t ⊔ zpowers v from le_sup_left) (mem_zpowers t)
    have hv : v ∈ (zpowers t ⊔ zpowers v : Subgroup G) :=
      (show zpowers v ≤ zpowers t ⊔ zpowers v from le_sup_right) (mem_zpowers v)
    exact ⟨(hx t ht).symm, (hx v hv).symm⟩
  · rintro ⟨h1, h2⟩
    have hle : (zpowers t ⊔ zpowers v : Subgroup G) ≤ centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · rw [zpowers_le]
        exact mem_centralizer_singleton_iff.2 h1.symm
      · rw [zpowers_le]
        exact mem_centralizer_singleton_iff.2 h2.symm
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.1 (hle hy)

omit [Finite G] in
theorem isPGroup_two_zpowers_of_mul_self {x : G} (hx : x * x = 1) : IsPGroup 2 (zpowers x) := by
  intro g
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hx2 : x ^ (2 : ℕ) = 1 := by rw [pow_two, hx]
  have : ((g : G)) ^ (2 : ℕ) = 1 := by
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  simpa using this

omit [Finite G] in
theorem isPGroup_two_zpowers_sup {t v : G} (ht : t * t = 1) (hv : v * v = 1)
    (htv : t * v = v * t) : IsPGroup 2 (zpowers t ⊔ zpowers v : Subgroup G) := by
  refine (isPGroup_two_zpowers_of_mul_self ht).to_sup_of_normal_right'
    (isPGroup_two_zpowers_of_mul_self hv) ?_
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [zpowers_le, mem_centralizer_iff]
  rintro y ⟨k, rfl⟩
  exact ((show Commute t v from htv).symm.zpow_left k).eq

theorem oddCore_eq_bot_of_simple_even (hs : IsSimpleGroup G) {t : G}
    (ht : orderOf t = 2) : CFSG.oddCore G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 G)) := CFSG.pPrimeCore_coprime_card
    rw [← oddCore_eq_pPrimeCore_two, h, Subgroup.card_top] at hc
    have h2 : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
    have := Nat.eq_one_of_dvd_coprimes hc (dvd_refl 2) h2
    omega

theorem isCompIn_derived_centralizer_tv (h : HSOuterSetup G L t S z n v s) :
    IsCompIn (derivedCentralizerIn L v)
      (centralizer ((zpowers t ⊔ zpowers v : Subgroup G) : Set G)) := by
  have hle : derivedCentralizerIn L v ≤
      centralizer ((zpowers t ⊔ zpowers v : Subgroup G) : Set G) := by
    intro x hx
    refine (mem_centralizer_tv_iff x).2 ⟨?_, ?_⟩
    · exact mem_centralizer_iff.1 h.t_mem x (derivedCentralizerIn_le L v hx)
    · exact mem_centralizer_singleton_iff.1 (derivedCentralizerIn_le_centralizer L v hx)
  have hq : CFSG.IsQuasisimple ↥(derivedCentralizerIn L v) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2
      (isQuasisimple_of_equiv_alt8 (derivedCentralizerIn_equiv h.ctx.v_cls).some)
  have hn : ((derivedCentralizerIn L v).subgroupOf
      (centralizer ((zpowers t ⊔ zpowers v : Subgroup G) : Set G))).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    obtain ⟨hgt, hgv⟩ := (mem_centralizer_tv_iff _).1 g.2
    exact conj_mem_derived' h hgt hgv ha
  exact isCompIn_of_normal hle hq hn

theorem derived_le_layerIn (h15 : FS79Lemma15Sec G) (h : HSOuterSetup G L t S z n v s) :
    derivedCentralizerIn L v ≤ layerIn (centralizer ({v} : Set G)) := by
  set V : Subgroup G := zpowers t ⊔ zpowers v with hV
  have ht2 : t * t = 1 := t_sq h
  have hv2 : v * v = 1 := h.ctx.v_sq
  have hVp : IsPGroup 2 V := isPGroup_two_zpowers_sup ht2 hv2 h.t_comm_v
  have hvp : IsPGroup 2 (zpowers v) := isPGroup_two_zpowers_of_mul_self hv2
  have hO : CFSG.oddCore G = ⊥ := oddCore_eq_bot_of_simple_even h.setting.1.simple h.t_two
  have hcomp := isCompIn_derived_centralizer_tv h
  have h2 : CFSG.IsPComponent 2 ((derivedCentralizerIn L v).subgroupOf
      (centralizer (V : Set G))) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hcomp.2
  have hΛ : derivedCentralizerIn L v ≤ twoLayerIn (centralizer (V : Set G)) := by
    have e1 : ((derivedCentralizerIn L v).subgroupOf (centralizer (V : Set G))).map
        (centralizer (V : Set G)).subtype = derivedCentralizerIn L v :=
      map_subgroupOf_eq_of_le hcomp.1
    rw [← e1]
    exact map_mono (le_sSup h2)
  have hkp := h.setting.1.kProper
  obtain ⟨hV1, -⟩ := h15.at hkp V hVp
  obtain ⟨-, hv2'⟩ := h15.at hkp (zpowers v) hvp
  have e3 := hV1 (zpowers v) (le_sup_right : zpowers v ≤ V)
  have e2 := hv2' hO
  have hcz : centralizer ((zpowers v : Subgroup G) : Set G) = centralizer ({v} : Set G) := by
    refine le_antisymm (Subgroup.centralizer_le ?_) (fun g hg => ?_)
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact mem_zpowers x
    · rw [mem_centralizer_singleton_iff] at hg
      rw [mem_centralizer_iff]
      rintro y ⟨k, rfl⟩
      exact ((Commute.zpow_left (show Commute v g from hg.symm) k)).eq
  rw [hcz] at e2 e3
  exact hΛ.trans (e3.trans e2.le)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
