module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Hyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Centralizers
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Conjugation
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

section Counterexample

variable [Finite G]

theorem two_le (hC : Counterexample G D r Abar) : 2 ≤ r := by
  have h1 := hC.hyp.hr
  by_contra h
  exact hC.fails (Or.inl (by omega))

theorem not_mem_center (hC : Counterexample G D r Abar) {t : G} (ht : t ≠ 1) :
    t ∉ Subgroup.center G := by
  rw [hC.center, Subgroup.mem_bot]
  exact ht

theorem centralizer_le (hC : Counterexample G D r Abar) (i : Fin r) {t : G}
    (htwo : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht : t ≠ 1)
    (hcent : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) t) :
    Subgroup.centralizer {t} ≤ Subgroup.normalizer (D : Set G) :=
  centralizer_le_normalizer_of_control D r Abar hC.hyp.hi i t htwo (not_mem_center hC ht) hcent

theorem mem_normalizer_of_fusion (hC : Counterexample G D r Abar) (i j : Fin r) {t g : G}
    (htwo : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht : t ≠ 1)
    (hti : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) t)
    (htj : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar j)) (g⁻¹ * t * g)) :
    g ∈ Subgroup.normalizer (D : Set G) :=
  hC.hyp.hi i j t g htwo (not_mem_center hC ht) hti htj

theorem mem_normalizer_of_le_sup (hC : Counterexample G D r Abar) (i : Fin r) (g : G)
    (X : Subgroup G) (hXg : X ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hXH : X ≤ Subgroup.normalizer (D : Set G))
    (hA : aschbacherThm5Preimage D (Abar i) ≤ X ⊔ aschbacherThm5Core D) :
    g ∈ Subgroup.normalizer (D : Set G) := by
  apply hC.hyp.hii i g X hXg
  intro a ha
  have hnorm : X ≤ Subgroup.normalizer (aschbacherThm5Core D : Set G) := by
    intro x hx
    have hcore := core_conjugate_eq D ⟨x, hXH hx⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcore
  have hmem : a ∈ ((X ⊔ aschbacherThm5Core D : Subgroup G) : Set G) := hA ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X _ hnorm] at hmem
  obtain ⟨x, hx, o, ho, hxo⟩ := Set.mem_mul.mp hmem
  exact ⟨x, hx, o, ho, hxo.symm⟩

end Counterexample

theorem normalizer_le_normalizer_core (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (aschbacherThm5Core D : Set G) :=
  fun h hh => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (core_conjugate_eq D ⟨h, hh⟩)

theorem core_le_normalizer (D : Subgroup G) :
    aschbacherThm5Core D ≤ Subgroup.normalizer (D : Set G) :=
  (core_le D).trans Subgroup.le_normalizer

@[expose] def coreIn (D : Subgroup G) : Subgroup (Subgroup.normalizer (D : Set G)) :=
  (aschbacherThm5Core D).subgroupOf (Subgroup.normalizer (D : Set G))

instance coreIn_normal (D : Subgroup G) : (coreIn D).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (core_le_normalizer D)).mpr
    (normalizer_le_normalizer_core D)

abbrev Bar (D : Subgroup G) : Type := Subgroup.normalizer (D : Set G) ⧸ coreIn D

@[expose] def toBar (D : Subgroup G) : Subgroup.normalizer (D : Set G) →* Bar D :=
  QuotientGroup.mk' (coreIn D)

@[expose] def bar (D : Subgroup G) (Y : Subgroup G) : Subgroup (Bar D) :=
  (Y.subgroupOf (Subgroup.normalizer (D : Set G))).map (toBar D)

theorem toBar_surjective (D : Subgroup G) : Function.Surjective (toBar D) :=
  QuotientGroup.mk'_surjective _

theorem toBar_eq_one_iff (D : Subgroup G) (h : Subgroup.normalizer (D : Set G)) :
    toBar D h = 1 ↔ (h : G) ∈ aschbacherThm5Core D :=
  (QuotientGroup.eq_one_iff h).trans Subgroup.mem_subgroupOf

theorem ker_toBar (D : Subgroup G) : (toBar D).ker = coreIn D :=
  QuotientGroup.ker_mk' _

theorem mem_bar_iff (D : Subgroup G) (Y : Subgroup G) (x : Bar D) :
    x ∈ bar D Y ↔ ∃ h : Subgroup.normalizer (D : Set G), (h : G) ∈ Y ∧ toBar D h = x := by
  rw [bar, Subgroup.mem_map]
  exact exists_congr fun h => and_congr_left' Subgroup.mem_subgroupOf

theorem toBar_mem_bar (D : Subgroup G) {Y : Subgroup G} {h : Subgroup.normalizer (D : Set G)}
    (hY : (h : G) ∈ Y) : toBar D h ∈ bar D Y :=
  (mem_bar_iff D Y _).mpr ⟨h, hY, rfl⟩

theorem bar_mono (D : Subgroup G) {Y Z : Subgroup G} (h : Y ≤ Z) : bar D Y ≤ bar D Z :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem commutator_mem_core_iff (D : Subgroup G) (y a : Subgroup.normalizer (D : Set G)) :
    (y : G)⁻¹ * (a : G)⁻¹ * y * a ∈ aschbacherThm5Core D ↔
      toBar D y * toBar D a = toBar D a * toBar D y := by
  have hmem : ((y⁻¹ * a⁻¹ * y * a : Subgroup.normalizer (D : Set G)) : G) =
      (y : G)⁻¹ * (a : G)⁻¹ * y * a := rfl
  rw [← hmem, ← toBar_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv]
  constructor
  · intro h
    have h' := congrArg (fun z => toBar D a * toBar D y * z) h
    simp only [mul_one] at h'
    rw [← h']
    group
  · intro h
    calc (toBar D y)⁻¹ * (toBar D a)⁻¹ * toBar D y * toBar D a
        = (toBar D y)⁻¹ * (toBar D a)⁻¹ * (toBar D y * toBar D a) := by group
      _ = (toBar D y)⁻¹ * (toBar D a)⁻¹ * (toBar D a * toBar D y) := by rw [h]
      _ = 1 := by group

theorem centralizes_iff_mem_centralizer (D : Subgroup G) (Y : Subgroup G) (hYD : Y ≤ D)
    (y : Subgroup.normalizer (D : Set G)) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) Y y ↔
      toBar D y ∈ Subgroup.centralizer (bar D Y : Set (Bar D)) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hcent x hx
    obtain ⟨a, haY, rfl⟩ := (mem_bar_iff D Y x).mp hx
    exact ((commutator_mem_core_iff D y a).mp (hcent a haY)).symm
  · intro hcomm a ha
    let a' : Subgroup.normalizer (D : Set G) := ⟨a, Subgroup.le_normalizer (hYD ha)⟩
    exact (commutator_mem_core_iff D y a').mpr (hcomm _ (toBar_mem_bar D (Y := Y) ha)).symm

@[expose] def fromD (D : Subgroup G) : D →* Bar D :=
  (toBar D).comp (Subgroup.inclusion Subgroup.le_normalizer)

theorem fromD_ker (D : Subgroup G) : (fromD D).ker = aschbacherThm5OddCore D := by
  ext d
  rw [MonoidHom.mem_ker, fromD, MonoidHom.comp_apply, toBar_eq_one_iff]
  exact mem_core_iff D d

@[expose] noncomputable def quotientEmbedding (D : Subgroup G) :
    D ⧸ aschbacherThm5OddCore D →* Bar D :=
  QuotientGroup.lift (aschbacherThm5OddCore D) (fromD D) (fromD_ker D).ge

theorem quotientEmbedding_mk (D : Subgroup G) (d : D) :
    quotientEmbedding D (QuotientGroup.mk' (aschbacherThm5OddCore D) d) = fromD D d := rfl

theorem quotientEmbedding_injective (D : Subgroup G) :
    Function.Injective (quotientEmbedding D) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) q
  rw [MonoidHom.mem_ker, quotientEmbedding_mk, ← MonoidHom.mem_ker, fromD_ker] at hq
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff d).mpr hq

theorem map_quotientEmbedding (D : Subgroup G) (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Abar.map (quotientEmbedding D) = bar D (aschbacherThm5Preimage D Abar) := by
  ext x
  rw [mem_bar_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) q
    exact ⟨Subgroup.inclusion Subgroup.le_normalizer d, (mem_preimage_iff D Abar d).mpr hq, rfl⟩
  · rintro ⟨h, hY, rfl⟩
    have hD : (h : G) ∈ D := preimage_le D Abar hY
    refine ⟨QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨h, hD⟩,
      (mem_preimage_iff D Abar ⟨h, hD⟩).mp hY, ?_⟩
    rfl

@[expose] noncomputable def factorEquiv (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Abar ≃* bar D (aschbacherThm5Preimage D Abar) :=
  (Abar.equivMapOfInjective _ (quotientEmbedding_injective D)).trans
    (MulEquiv.subgroupCongr (map_quotientEmbedding D Abar))

variable [Finite G]

theorem bar_factor_perfect (hyp : Hyp61 G D r Abar) (i : Fin r) :
    Group.IsPerfect (bar D (aschbacherThm5Preimage D (Abar i))) := by
  have : Group.IsPerfect (Abar i) := semisimple_perfect (Abar i) (hyp.hsemisimple i)
  exact Group.IsPerfect.ofSurjective (f := (factorEquiv D (Abar i)).toMonoidHom)
    (factorEquiv D (Abar i)).surjective

theorem bar_factor_ne_bot (hyp : Hyp61 G D r Abar) (i : Fin r) :
    bar D (aschbacherThm5Preimage D (Abar i)) ≠ ⊥ := by
  rw [← map_quotientEmbedding]
  intro hbot
  apply semisimple_ne_bot (Abar i) (hyp.hsemisimple i)
  exact (Subgroup.map_eq_bot_iff_of_injective _ (quotientEmbedding_injective D)).mp hbot

theorem even_card_of_perfect {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    [Nontrivial P] : Even (Nat.card P) := by
  by_contra hodd
  exact Group.IsPerfect.not_isSolvable P
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd))

theorem factor_even (hyp : Hyp61 G D r Abar) (i : Fin r) :
    Even (Nat.card (aschbacherThm5Preimage D (Abar i))) := by
  let Q := bar D (aschbacherThm5Preimage D (Abar i))
  have : Group.IsPerfect Q := bar_factor_perfect hyp i
  have : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr (bar_factor_ne_bot hyp i)
  have hQ : Even (Nat.card Q) := even_card_of_perfect
  have hdvd : Nat.card Q ∣ Nat.card (aschbacherThm5Preimage D (Abar i)) := by
    have h1 : Nat.card Q ∣ Nat.card ((aschbacherThm5Preimage D (Abar i)).subgroupOf
        (Subgroup.normalizer (D : Set G))) := Subgroup.card_map_dvd _ _
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((preimage_le D _).trans Subgroup.le_normalizer)).toEquiv] at h1
  exact (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hQ).trans hdvd))

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
