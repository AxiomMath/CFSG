module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberTits
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporReduce

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType oPPrimeHull)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure IsBorelDLocal {G : Type} [Group G] [Finite G] (p d : ℕ) (Y : Subgroup G) : Prop where
  lt_top : Y < ⊤
  normalizer_sylow_le : ∃ P : Sylow p G, Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Y
  sylow_le : ∃ S : Sylow d G, (S : Subgroup G) ≤ Y
  normalizer_le : ∀ R : Subgroup G, IsPGroup d R → R ≠ ⊥ → R ≤ Y →
    Subgroup.normalizer (R : Set G) ≤ Y

@[expose] def ChevMemberFive (G : Type) [Group G] (p : ℕ) : Prop :=
  StatedClassicalModel G .PSL 2 p 2 ∨ StatedClassicalModel G .PSL 2 p 3 ∨
    IsPSLType 3 (ZMod p) G ∨ StatedClassicalModel G .PSU 3 p 1 ∨
    StatedClassicalModel G .PSp 2 p 1 ∨ ChevalleyExceptionalModel G .G2 p 1

@[expose] def ThreeNineDefOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p → ChevMemberFive G p →
    Subgroup.center G = ⊥ ∧ ¬ p ∣ Nat.card (Outer G) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Outer G) → q = 3) ∧ 3 ∣ Nat.card G ∧
      (IsPSLType 3 (ZMod p) G → Nat.card (Outer G) ∣ 2 * Nat.gcd 3 (p - 1))

@[expose] def ThreeNineDefRankOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p d : ℕ) (Y : Subgroup G), p.Prime → 5 ≤ p → d.Prime →
    d ≠ 2 → d ≠ p → d ∣ Nat.card G →
    (StatedClassicalModel G .PSL 2 p 2 ∨ StatedClassicalModel G .PSL 2 p 3 ∨
      StatedClassicalModel G .PSU 3 p 1) →
    IsBorelDLocal p d Y → False

@[expose] def ThreeNineDefRankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p d : ℕ) (Y : Subgroup G), p.Prime → 5 ≤ p → d.Prime →
    d ≠ 2 → d ≠ p → d ∣ Nat.card G →
    (StatedClassicalModel G .PSp 2 p 1 ∨ ChevalleyExceptionalModel G .G2 p 1) →
    IsBorelDLocal p d Y → False

@[expose] def ThreeNineDefL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p d : ℕ) (Y : Subgroup G), p.Prime → 5 ≤ p → d.Prime →
    d ≠ 2 → d ≠ p → d ∣ Nat.card G → IsPSLType 3 (ZMod p) G → IsBorelDLocal p d Y →
    d ∣ p + 1 ∧ IsPSLType 2 (ZMod p) (oPrimeModPrimeComplement d Y) ∧
      ∀ S : Subgroup G, IsPGroup d S → S ≤ Y → IsCyclic S

namespace IsBorelDLocal

variable {G : Type} [Group G] [Finite G] {p d : ℕ} {Y : Subgroup G}

theorem map_equiv {G' : Type} [Group G'] [Finite G'] (h : IsBorelDLocal p d Y) (e : G ≃* G') :
    IsBorelDLocal p d (Y.map e.toMonoidHom) := by
  have he : Function.Injective e.symm.toMonoidHom := e.symm.injective
  have hrange : ∀ {q : ℕ} (P : Sylow q G), (P : Subgroup G) ≤ e.symm.toMonoidHom.range := by
    intro q P
    rw [MonoidHom.range_eq_top_of_surjective e.symm.toMonoidHom e.symm.surjective]
    exact le_top
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact (Subgroup.map_lt_map_iff_of_injective e.injective).mpr h.lt_top
  · obtain ⟨P, hPY⟩ := h.normalizer_sylow_le
    let P' : Sylow p G' := P.comapOfInjective e.symm.toMonoidHom he (hrange P)
    have hP' : (P' : Subgroup G') = (P : Subgroup G).map e.toMonoidHom := by
      rw [Sylow.coe_comapOfInjective (hϕ := he) (h := hrange P)]
      rw [← Subgroup.map_equiv_eq_comap_symm' e]
    refine ⟨P', ?_⟩
    have hmap := Subgroup.map_mono (f := e.toMonoidHom) hPY
    rw [Subgroup.map_equiv_normalizer_eq (H := (P : Subgroup G)) e] at hmap
    rwa [hP']
  · obtain ⟨S, hSY⟩ := h.sylow_le
    let S' : Sylow d G' := S.comapOfInjective e.symm.toMonoidHom he (hrange S)
    have hS' : (S' : Subgroup G') = (S : Subgroup G).map e.toMonoidHom := by
      rw [Sylow.coe_comapOfInjective (hϕ := he) (h := hrange S)]
      rw [← Subgroup.map_equiv_eq_comap_symm' e]
    exact ⟨S', hS' ▸ Subgroup.map_mono (f := e.toMonoidHom) hSY⟩
  · intro R hR hRne hRY
    let R' : Subgroup G := R.comap e.toMonoidHom
    have he' : Function.Injective e.toMonoidHom := e.injective
    have hR'pg : IsPGroup d R' := hR.comap_of_injective e.toMonoidHom he'
    have hR'map : R'.map e.toMonoidHom = R :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective R
    have hR'ne : R' ≠ ⊥ := by
      intro hbot
      apply hRne
      rw [← hR'map, hbot, Subgroup.map_bot]
    have hR'Y : R' ≤ Y := by
      intro x hx
      obtain ⟨y, hyY, hyx⟩ := Subgroup.mem_map.mp (hRY (show e x ∈ R from hx))
      rwa [← e.injective hyx]
    have hmap := Subgroup.map_mono (f := e.toMonoidHom)
      (h.normalizer_le R' hR'pg hR'ne hR'Y)
    rwa [Subgroup.map_equiv_normalizer_eq (H := R') e, hR'map] at hmap

theorem normalizer_le_of_dvd (hd : d.Prime) (h : IsBorelDLocal p d Y) {H : Subgroup G}
    (hHY : H ≤ Y) (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hdH : d ∣ Nat.card H) :
    Subgroup.normalizer (H : Set G) ≤ Y := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow d ↥H))
  haveI : IsMulCommutative ↥H := ⟨⟨fun (x y : ↥H) => Subtype.ext (hH x x.2 y y.2)⟩⟩
  have hPchar : (P : Subgroup ↥H).Characteristic :=
    Sylow.characteristic_of_normal P inferInstance
  have hdvdP : d ∣ Nat.card (P : Subgroup ↥H) := by
    have hcard := Subgroup.card_mul_index (P : Subgroup ↥H)
    rw [← hcard] at hdH
    rcases (Nat.Prime.dvd_mul hd).mp hdH with h | h
    · exact h
    · exact absurd h P.not_dvd_index
  have hSne : (P : Subgroup ↥H).map H.subtype ≠ ⊥ := by
    intro hbot
    have hPbot : (P : Subgroup ↥H) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup ↥H) H.subtype_injective).mp hbot
    have hcardP : Nat.card (P : Subgroup ↥H) = 1 := by rw [hPbot, Subgroup.card_bot]
    rw [hcardP] at hdvdP
    exact hd.not_dvd_one hdvdP
  intro g hg
  exact h.normalizer_le ((P : Subgroup ↥H).map H.subtype) (P.isPGroup'.map H.subtype) hSne
    ((Subgroup.map_subtype_le _).trans hHY)
    (CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic hg)

theorem not_dvd_index (hd : d.Prime) (h : IsBorelDLocal p d Y) : ¬ d ∣ Y.index := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨S, hSY⟩ := h.sylow_le
  intro hdY
  exact S.not_dvd_index (hdY.trans (Subgroup.index_dvd_of_le hSY))

theorem index_modEq_one_of_dvd (hd : d.Prime) (h : IsBorelDLocal p d Y) (hdG : d ∣ Nat.card G) :
    Y.index ≡ 1 [MOD d] := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨S, hSY⟩ := h.sylow_le
  exact index_modEq_one_of_normalizer_le S
    (h.normalizer_le S S.isPGroup' (S.ne_bot_of_dvd_card hdG) hSY)

theorem exists_conj (hp : p.Prime) (h : IsBorelDLocal p d Y) (P₀ : Sylow p G) :
    ∃ g : G, IsBorelDLocal p d (Y.map (MulAut.conj g).toMonoidHom) ∧
      Subgroup.normalizer ((P₀ : Subgroup G) : Set G) ≤ Y.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPY⟩ := h.normalizer_sylow_le
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P₀
  refine ⟨g, h.map_equiv (MulAut.conj g), ?_⟩
  have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hPY
  rw [Subgroup.map_equiv_normalizer_eq (H := (P : Subgroup G)) (MulAut.conj g)] at hmap
  have hP : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (P₀ : Subgroup G) := by
    have h := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h
  rwa [hP] at hmap

end IsBorelDLocal

private theorem oPPrimeHull_top_map_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (d : ℕ) : (oPPrimeHull d (⊤ : Subgroup A)).map e.toMonoidHom =
      oPPrimeHull d (⊤ : Subgroup B) := by
  rw [oPPrimeHull, oPPrimeHull, MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ⟨-, k, hk⟩, rfl⟩
    exact ⟨trivial, k, by rwa [orderOf_injective e.toMonoidHom e.injective]⟩
  · rintro ⟨-, k, hk⟩
    refine ⟨e.symm b, ⟨trivial, k, ?_⟩, e.apply_symm_apply b⟩
    have hb : e.toMonoidHom (e.symm b) = b := e.apply_symm_apply b
    rw [← orderOf_injective e.toMonoidHom e.injective, hb]
    exact hk

theorem oPrimeModPrimeComplement_congr {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (d : ℕ) {Y : Subgroup G} {Y' : Subgroup G'} (e : ↥Y ≃* ↥Y') :
    Nonempty (oPrimeModPrimeComplement d Y ≃* oPrimeModPrimeComplement d Y') := by
  classical
  have hcore : (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d).map
        e.toMonoidHom =
      CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y') d := by
    have hle : (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d).map
          e.toMonoidHom ≤
        CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y') d := by
      rw [Subgroup.map_le_iff_le_comap]
      apply sSup_le
      rintro N ⟨hNn, hNc⟩
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup ⟨hNn.map e.toMonoidHom e.surjective,
        by rwa [Subgroup.card_map_of_injective e.injective]⟩
    have hle' : (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y') d).map
          e.symm.toMonoidHom ≤
        CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d := by
      rw [Subgroup.map_le_iff_le_comap]
      apply sSup_le
      rintro N ⟨hNn, hNc⟩
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup ⟨hNn.map e.symm.toMonoidHom e.symm.surjective,
        by rwa [Subgroup.card_map_of_injective e.symm.injective]⟩
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id ↥Y' := by
      ext x
      simpa using e.apply_symm_apply x
    have hle'' : CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y') d ≤
        (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d).map
          e.toMonoidHom := by
      have := Subgroup.map_mono (f := e.toMonoidHom) hle'
      rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at this
    exact le_antisymm hle hle''
  let qe : (↥Y ⧸ CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d) ≃*
      (↥Y' ⧸ CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y') d) :=
    QuotientGroup.congr _ _ e hcore
  have hO := oPPrimeHull_top_map_equiv qe d
  exact ⟨(MulEquiv.subgroupMap qe _).trans (MulEquiv.subgroupCongr hO)⟩

namespace ThreeNineHyp

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem exists_normalizer_sylow_le (h : ThreeNineHyp K E D X₁ p d)
    (hZ : Subgroup.center ↥K = ⊥) (hout : ¬ p ∣ Nat.card (Outer ↥K)) :
    ∃ P : Sylow p ↥K, Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K) ≤ X₁.subgroupOf K := by
  obtain ⟨Ebar, -, hcard, -, hR⟩ := h.exists_barE hZ hout
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hEP⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  exact ⟨P, hR P P.isPGroup' hEP⟩

private theorem normalizer_le_of_isBorelDLocal (h : ThreeNineHyp K E D X₁ p d)
    {R : Subgroup ↥K} (hR : IsPGroup d R) (hRne : R ≠ ⊥) (hRY : R ≤ X₁.subgroupOf K) :
    Subgroup.normalizer (R : Set ↥K) ≤ X₁.subgroupOf K := by
  haveI : Fact d.Prime := ⟨h.d_prime⟩
  set R' : Subgroup X := R.map K.subtype
  have hR'le : R' ≤ X₁ := by rintro x ⟨r, hr, rfl⟩; exact hRY hr
  have hR'ne : R' ≠ ⊥ := fun hbot =>
    hRne ((Subgroup.map_eq_bot_iff_of_injective R K.subtype_injective).mp hbot)
  have hR'pg : IsPGroup d R' :=
    (show IsPGroup d ↥R from hR).of_equiv (H := ↥R')
      (Subgroup.equivMapOfInjective R (K.subtype : ↥K →* X) K.subtype_injective)
  obtain ⟨S, hR₁S⟩ := hR'pg.comap_subtype (K := X₁) |>.exists_le_sylow
  have hR'P' : R' ≤ (S : Subgroup ↥X₁).map X₁.subtype := by
    have hmap : (R'.comap X₁.subtype).map X₁.subtype = R' := by
      change (R'.subgroupOf X₁).map X₁.subtype = R'
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR'le]
    have h := Subgroup.map_mono (f := X₁.subtype) hR₁S
    rwa [hmap] at h
  obtain ⟨k, hkX₁, hkconj⟩ :=
    (h.sylow.of_le h.D_le le_top).exists_mem_conj (⟨S, rfl⟩ :
      CFSG.ABGLocalTools.IsSylowOf d ((S : Subgroup ↥X₁).map X₁.subtype) X₁)
  set F : Subgroup X := R'.map (MulAut.conj k⁻¹).toMonoidHom
  have hFD : F ≤ D := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    simpa [MulAut.conj_apply] using (hkconj r).mp (hR'P' hr)
  have hFne : F ≠ ⊥ := by
    have hinj : Function.Injective (MulAut.conj k⁻¹).toMonoidHom :=
      (MulAut.conj k⁻¹).injective
    intro hbot
    exact hR'ne ((Subgroup.map_eq_bot_iff_of_injective R' hinj).mp (by simpa [F] using hbot))
  intro n hn
  show (n : X) ∈ X₁
  have hnN : (n : X) ∈ Subgroup.normalizer (R' : Set X) :=
    Subgroup.le_normalizer_map K.subtype ⟨n, hn, rfl⟩
  have hconjN : ((k : X)⁻¹ * (n : X) * (k : X)) ∈ Subgroup.normalizer (F : Set X) := by
    simpa [F, MulAut.conj_apply] using
      Subgroup.le_normalizer_map (MulAut.conj (k : X)⁻¹).toMonoidHom
        ⟨(n : X), hnN, rfl⟩
  have hmemKD : ((k : X)⁻¹ * (n : X) * (k : X)) ∈ K ⊔ D :=
    (le_sup_left : K ≤ K ⊔ D) (by
      have := h.normal.conj_mem (n : X) n.2 ((k : X)⁻¹)
      simpa using this)
  have hX₁mem : ((k : X)⁻¹ * (n : X) * (k : X)) ∈ X₁ :=
    h.normalizer_inf_le_of_le_D hFD hFne ⟨hconjN, hmemKD⟩
  have h1 : (k : X) * ((k : X)⁻¹ * (n : X) * (k : X)) * (k : X)⁻¹ = (n : X) := by
    group
  rw [← h1]
  exact X₁.mul_mem (X₁.mul_mem hkX₁ hX₁mem) (X₁.inv_mem hkX₁)

theorem isBorelDLocal (h : ThreeNineHyp K E D X₁ p d) (hZ : Subgroup.center ↥K = ⊥)
    (hout : ¬ p ∣ Nat.card (Outer ↥K)) : IsBorelDLocal p d (X₁.subgroupOf K) := by
  have hB := h.exists_normalizer_sylow_le hZ hout
  haveI : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : K.Normal)])
  refine ⟨?_, hB, ?_, ?_⟩
  · refine lt_top_iff_ne_top.mpr fun htop => h.not_K_le (Subgroup.subgroupOf_eq_top.mp htop)
  · obtain ⟨S, hS⟩ := hDsylK.exists_sylow_eq_subgroupOf
    exact ⟨S, hS ▸ Subgroup.subgroupOf_mono K (le_trans inf_le_left h.D_le)⟩
  · exact fun R hR hRne hRY => normalizer_le_of_isBorelDLocal h hR hRne hRY

theorem dvd_card_K (h : ThreeNineHyp K E D X₁ p d) (hZ : Subgroup.center ↥K = ⊥)
    (hout : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Outer ↥K) → q = 3)
    (h3 : 3 ∣ Nat.card ↥K) : d ∣ Nat.card ↥K := by
  by_cases hdo : d ∣ Nat.card (Outer ↥K)
  · rw [hout d h.d_prime h.d_ne_two hdo]
    exact h3
  · have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hdo
    haveI : Fact d.Prime := ⟨h.d_prime⟩
    have hdD : d ∣ Nat.card ↥D := by
      rcases h.isPGroup_D.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) h.D_ne_bot
      · exact h1
    exact hdD.trans (Subgroup.card_dvd_of_le hDK)

end ThreeNineHyp

private theorem conclusion_of_isPSLType_three {X : Type} [Group X] [Finite X]
    {K E D X₁ : Subgroup X} {p d : ℕ} (hL3 : ThreeNineDefL3)
    (h : ThreeNineHyp K E D X₁ p d) (hp5 : 5 ≤ p) (hK : IsPSLType 3 (ZMod p) ↥K)
    (hZ : Subgroup.center ↥K = ⊥)
    (houtL3 : Nat.card (Outer ↥K) ∣ 2 * Nat.gcd 3 (p - 1))
    (hdK : d ∣ Nat.card ↥K) (hY : IsBorelDLocal p d (X₁.subgroupOf K)) :
    ThreeNineConclusion K D X₁ p d := by
  obtain ⟨hdvd_p1, hPSL2, hcyclic⟩ :=
    hL3 ↥K p d (X₁.subgroupOf K) h.prime hp5 h.d_prime h.d_ne_two h.d_ne hdK hK hY
  have hnotdvdOut : ¬ d ∣ Nat.card (Outer ↥K) := by
    intro hdvd
    have h1 : d ∣ 2 * Nat.gcd 3 (p - 1) := hdvd.trans houtL3
    have h2 : d ∣ Nat.gcd 3 (p - 1) := by
      rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp h2) h.d_ne_two
      · exact h2
    have hd3 : d = 3 :=
      (Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
        (h2.trans (Nat.gcd_dvd_left 3 (p - 1)))
    have h3dvd1 : 3 ∣ p + 1 := hd3 ▸ hdvd_p1
    have h3dvd2 : 3 ∣ p - 1 := hd3 ▸ (h2.trans (Nat.gcd_dvd_right 3 (p - 1)))
    obtain ⟨a, ha⟩ := h3dvd1
    obtain ⟨b, hb⟩ := h3dvd2
    omega
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hnotdvdOut
  have hX₁K : X₁ ≤ K := by
    have := h.lt.le
    rwa [sup_eq_left.mpr hDK] at this
  have hcyc : IsCyclic ↥D :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hDK)).mp
      (hcyclic (D.subgroupOf K) (h.isPGroup_D.comap_subtype)
        (Subgroup.subgroupOf_mono K h.D_le))
  obtain ⟨eOC⟩ := oPrimeModPrimeComplement_congr d
    (Subgroup.subgroupOfEquivOfLe hX₁K).symm
  have hPSL2X₁ : IsPSLType 2 (ZMod p) (oPrimeModPrimeComplement d X₁) := by
    obtain ⟨ePSL⟩ := hPSL2
    exact ⟨eOC.trans ePSL⟩
  exact ⟨hcyc, hDK, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨hdvd_p1, hK, hPSL2X₁⟩)))))⟩

theorem threeNineFiveDef_of_members (hOut : ThreeNineDefOut) (hR1 : ThreeNineDefRankOne)
    (hR2 : ThreeNineDefRankTwo) (hL3 : ThreeNineDefL3) : ThreeNineFiveDef := by
  intro X _ _ K E D X₁ p d h hp5 hK
  obtain ⟨hZ, hpout, hout3, h3, hOutL3⟩ := hOut ↥K p h.prime hp5 hK
  have hY := h.isBorelDLocal hZ hpout
  have hdK := h.dvd_card_K hZ hout3 h3
  rcases hK with hK | hK | hK | hK | hK | hK
  · exact (hR1 ↥K p d (X₁.subgroupOf K) h.prime hp5 h.d_prime h.d_ne_two h.d_ne hdK
      (Or.inl hK) hY).elim
  · exact (hR1 ↥K p d (X₁.subgroupOf K) h.prime hp5 h.d_prime h.d_ne_two h.d_ne hdK
      (Or.inr (Or.inl hK)) hY).elim
  · exact conclusion_of_isPSLType_three hL3 h hp5 hK hZ (hOutL3 hK) hdK hY
  · exact (hR1 ↥K p d (X₁.subgroupOf K) h.prime hp5 h.d_prime h.d_ne_two h.d_ne hdK
      (Or.inr (Or.inr hK)) hY).elim
  · exact (hR2 ↥K p d (X₁.subgroupOf K) h.prime hp5 h.d_prime h.d_ne_two h.d_ne hdK
      (Or.inl hK) hY).elim
  · exact (hR2 ↥K p d (X₁.subgroupOf K) h.prime hp5 h.d_prime h.d_ne_two h.d_ne hdK
      (Or.inr hK) hY).elim

end CFSG.LocalAnalysis.AGL81I.Section3
