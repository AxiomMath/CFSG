module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.BkS4Prelim

public section

namespace CFSG.GH74.GLS.Th2.L627

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Bk
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mul_left' (x y z : G) : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

omit [Finite G] in
theorem le_pPrimeCoreOf_of_odd_normal {J D E : Subgroup G} (hDJ : D ≤ J) (hEJ : E ≤ J)
    (hEn : ∀ d ∈ D, ∀ e ∈ E, d * e * d⁻¹ ∈ E) (hEodd : Odd (Nat.card ↥E))
    (hcov : ∀ j ∈ J, ∃ d ∈ D, ∃ o ∈ pPrimeCoreOf 2 J, j = d * o)
    (hJs : IsSimpleGroup (kBar J)) (hJe : Even (Nat.card (kBar J))) :
    E ≤ pPrimeCoreOf 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥J →* kBar J := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hπ
  set E' : Subgroup ↥J := E.subgroupOf J with hE'
  set Ē : Subgroup (kBar J) := E'.map π with hĒ
  have hmemO : ∀ o ∈ pPrimeCoreOf 2 J, ∀ ho : o ∈ J, π ⟨o, ho⟩ = 1 := by
    intro o ho hoJ
    obtain ⟨o', ho', hoo⟩ := ho
    have : o' = ⟨o, hoJ⟩ := Subtype.ext hoo
    rw [← this]
    exact (QuotientGroup.eq_one_iff o').2 ho'
  have hĒn : Ē.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨d, hd, o, ho, hjdo⟩ := hcov (j : G) j.2
    have hdJ : d ∈ J := hDJ hd
    have hoJ : o ∈ J := (TwoThin.pPrimeCoreOf_le J) ho
    have hjeq : j = ⟨d, hdJ⟩ * ⟨o, hoJ⟩ := Subtype.ext hjdo
    have hπo : π ⟨o, hoJ⟩ = 1 := hmemO o ho hoJ
    have hπj : π j = π ⟨d, hdJ⟩ := by rw [hjeq, map_mul, hπo, mul_one]
    show (QuotientGroup.mk j) * π e * (QuotientGroup.mk j)⁻¹ ∈ Ē
    have : (QuotientGroup.mk j : kBar J) = π ⟨d, hdJ⟩ := hπj
    rw [this, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map.2 ⟨⟨d, hdJ⟩ * e * ⟨d, hdJ⟩⁻¹, ?_, rfl⟩
    have he' : (e : G) ∈ E := Subgroup.mem_subgroupOf.1 he
    exact Subgroup.mem_subgroupOf.2 (hEn d hd e he')
  rcases hJs.eq_bot_or_eq_top_of_normal Ē with hbot | htop
  · intro e he
    have h1 : π ⟨e, hEJ he⟩ = 1 := by
      have : π ⟨e, hEJ he⟩ ∈ Ē := Subgroup.mem_map.2 ⟨⟨e, hEJ he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    exact ⟨⟨e, hEJ he⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  · exfalso
    have hE'odd : Odd (Nat.card ↥E') := by
      rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv]
      exact hEodd
    have hsurj : Odd (Nat.card ↥Ē) := Odd.of_dvd_nat hE'odd (Subgroup.card_map_dvd E' π)
    rw [htop, Subgroup.card_top] at hsurj
    exact (Nat.not_even_iff_odd.2 hsurj) hJe

theorem not_balanced_of_commuting {t u v : G} {J : Subgroup G}
    (hunb : IsUnbalancingTriple t u J)
    (hN : ∀ c ∈ centralizer ({t} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hJs : IsSimpleGroup (kBar J)) (hJe : Even (Nat.card (kBar J)))
    (hv2 : orderOf v = 2) (hvC : v ∈ CxK t J) (hvu : v * u = u * v) :
    ¬ (pPrimeCoreOf 2 (centralizer ({u} : Set G)) ⊓ centralizer ({v} : Set G) ≤
        pPrimeCoreOf 2 (centralizer ({v} : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hle
  set O : Subgroup G := pPrimeCoreOf 2 J with hO
  have hv22 : v * v = 1 := by rw [← sq]; exact hv2 ▸ pow_orderOf_eq_one v
  have hvt : v ∈ centralizer ({t} : Set G) := hvC.1
  have hvcs : v ∈ centralizerSection J O := hvC.2
  have hvN : v ∈ normalizer (J : Set G) := hvcs.1
  have hgN : ∀ g ∈ centralizer ({t} : Set G), g ∈ normalizer (J : Set G) := fun g hg =>
    mem_normalizer_of_two_sided (hN g hg) (fun j hj => by simpa using hN g⁻¹ (Subgroup.inv_mem _ hg) j hj)
  set X : Subgroup G := pPrimeCoreOf 2 (centralizer ({u} : Set G)) ⊓ centralizer ({t} : Set G)
    with hX
  have hXodd : Odd (Nat.card ↥X) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) (Subgroup.card_dvd_of_le inf_le_left)
  have hvu' : v ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hvu
  have hvX : ∀ x ∈ X, v * x * v⁻¹ ∈ X := fun x hx =>
    ⟨TwoThin.pPrimeCoreOf_normalized _ hvu' hx.1,
      mul_mem (mul_mem hvt hx.2) (Subgroup.inv_mem _ hvt)⟩
  have hCnorm : ∀ g ∈ centralizer ({t} : Set G), ∀ c ∈ CxK t J, g * c * g⁻¹ ∈ CxK t J :=
    fun g hg c hc =>
      ⟨mul_mem (mul_mem hg hc.1) (Subgroup.inv_mem _ hg), PumpCalc.conj_mem_cSec (hgN g hg) hc.2⟩
  set O₁ : Subgroup G := X ⊓ CxK t J with hO₁
  have hO₁odd : Odd (Nat.card ↥O₁) :=
    Odd.of_dvd_nat hXodd (Subgroup.card_dvd_of_le inf_le_left)
  have hO₁v : ∀ o ∈ O₁, v * o * v⁻¹ ∈ O₁ := fun o ho =>
    ⟨hvX o ho.1, mul_mem (mul_mem hvC ho.2) (Subgroup.inv_mem _ hvC)⟩
  have hcomm₁ : ∀ x ∈ X, ⁅x, v⁆ ∈ O₁ := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have : ⁅x, v⁆ = x * (v * x⁻¹ * v⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem hx (hvX x⁻¹ (Subgroup.inv_mem _ hx))
    · have : ⁅x, v⁆ = (x * v * x⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
      rw [this]
      exact mul_mem (hCnorm x hx.2 v hvC) (Subgroup.inv_mem _ hvC)
  have hdecX := TwoThin.exists_commute_mul_mem_of_odd (K := X) (O := O₁) (t := v) hO₁odd
    inf_le_left hv22 hO₁v hcomm₁
  have hXnot : ∃ k ∈ X, k ∉ centralizerSection J O := by
    by_contra hcon
    push Not at hcon
    exact hunb.2.2.2.2 (fun k hk => hcon k hk)
  obtain ⟨k, hkX, hknot⟩ := hXnot
  obtain ⟨c, hcX, hvc, o, hoO₁, hkco⟩ := hdecX k hkX
  have hcnot : c ∉ centralizerSection J O := by
    intro hc
    apply hknot
    rw [hkco]
    exact mul_mem hc hoO₁.2.2
  have hcv : c ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 hvc.symm
  have hcYv : c ∈ pPrimeCoreOf 2 (centralizer ({v} : Set G)) := hle ⟨hcX.1, hcv⟩
  have hcN : c ∈ normalizer (J : Set G) := hgN c hcX.2
  have hcNO : c ∈ normalizer (O : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf hcN
  have hcov : ∀ j ∈ J, ∃ d ∈ J ⊓ centralizer ({v} : Set G), ∃ o ∈ O, j = d * o :=
    TwoThin.exists_centralizer_mul_pPrimeCore hvcs hv2
  have hkey : ∀ d ∈ J, d ∈ centralizer ({v} : Set G) → ⁅d, c⁆ ∈ O := by
    intro d hdJ hdv
    set D : Subgroup G := J ⊓ centralizer ({v} : Set G) with hD
    set E : Subgroup G := D ⊓ pPrimeCoreOf 2 (centralizer ({v} : Set G)) with hE
    have hEodd : Odd (Nat.card ↥E) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) (Subgroup.card_dvd_of_le inf_le_right)
    have hEn : ∀ d' ∈ D, ∀ e ∈ E, d' * e * d'⁻¹ ∈ E := fun d' hd' e he =>
      ⟨⟨mul_mem (mul_mem hd'.1 he.1.1) (Subgroup.inv_mem _ hd'.1),
        mul_mem (mul_mem hd'.2 he.1.2) (Subgroup.inv_mem _ hd'.2)⟩,
        TwoThin.pPrimeCoreOf_normalized _ hd'.2 he.2⟩
    have hEO : E ≤ O := le_pPrimeCoreOf_of_odd_normal (D := D) inf_le_left
      (inf_le_left.trans inf_le_left) hEn hEodd hcov hJs hJe
    refine hEO ⟨⟨?_, ?_⟩, ?_⟩
    · have : ⁅d, c⁆ = d * (c * d⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem hdJ (hN c hcX.2 d⁻¹ (Subgroup.inv_mem _ hdJ))
    · simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hdv hcv) (Subgroup.inv_mem _ hdv)) (Subgroup.inv_mem _ hcv)
    · have : ⁅d, c⁆ = (d * c * d⁻¹) * c⁻¹ := by simp only [commutatorElement_def]
      rw [this]
      exact mul_mem (TwoThin.pPrimeCoreOf_normalized _ hdv hcYv) (Subgroup.inv_mem _ hcYv)
  apply hcnot
  refine ⟨hcN, hcNO, fun k hk => ?_⟩
  obtain ⟨d, hd, o₂, ho₂, rfl⟩ := hcov k hk
  have hdJ : d ∈ J := hd.1
  have ho₂c : ⁅o₂, c⁆ ∈ O := by
    have : ⁅o₂, c⁆ = o₂ * (c * o₂⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem ho₂ ((Subgroup.mem_normalizer_iff.1 hcNO o₂⁻¹).1 (Subgroup.inv_mem _ ho₂))
  rw [commutator_mul_left']
  exact mul_mem (TwoThin.pPrimeCoreOf_normalized J hdJ ho₂c) (hkey d hdJ hd.2)

end CFSG.GH74.GLS.Th2.L627
