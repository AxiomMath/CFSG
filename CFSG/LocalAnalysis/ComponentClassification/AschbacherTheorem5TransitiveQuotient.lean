module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveBasic

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] {D : Subgroup G}

theorem coreIn_odd [Finite G] (D : Subgroup G) : Odd (Nat.card (coreIn D)) := by
  rw [coreIn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (core_le_normalizer D)).toEquiv]
  exact core_odd D

theorem toBar_injOn_of_isPGroup [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {u v : Subgroup.normalizer (D : Set G)} (hu : (u : G) ∈ P) (hv : (v : G) ∈ P)
    (h : toBar D u = toBar D v) : u = v :=
  AschbacherToolkit.quotient_injective_on_of_isPGroup (coreIn D) (coreIn_odd D)
    (U := P.subgroupOf (Subgroup.normalizer (D : Set G))) hP.comap_subtype hu hv h

theorem bar_sup {Y Z : Subgroup G} (hY : Y ≤ Subgroup.normalizer (D : Set G))
    (hZ : Z ≤ Subgroup.normalizer (D : Set G)) : bar D (Y ⊔ Z) = bar D Y ⊔ bar D Z := by
  rw [bar, Subgroup.subgroupOf_sup hY hZ, Subgroup.map_sup]
  rfl

theorem bar_inf_of_core_le {Y Z : Subgroup G} (hO : aschbacherThm5Core D ≤ Z) :
    bar D (Y ⊓ Z) = bar D Y ⊓ bar D Z := by
  apply le_antisymm (le_inf (bar_mono D inf_le_left) (bar_mono D inf_le_right))
  rintro x ⟨hxY, hxZ⟩
  obtain ⟨y, hy, rfl⟩ := (mem_bar_iff D Y x).mp hxY
  obtain ⟨z, hz, hzy⟩ := (mem_bar_iff D Z _).mp hxZ
  have hmem : (z : G)⁻¹ * y ∈ aschbacherThm5Core D := by
    have h1 : z⁻¹ * y ∈ coreIn D := QuotientGroup.eq.mp hzy
    exact h1
  have hyZ : (y : G) ∈ Z := by
    have := Z.mul_mem hz (hO hmem)
    simpa using this
  exact toBar_mem_bar D ⟨hy, hyZ⟩

theorem isPGroup_bar {P : Subgroup G} (hP : IsPGroup 2 P) : IsPGroup 2 (bar D P) :=
  hP.comap_subtype.map _

theorem card_subgroupOf {X : Type*} [Group X] (Y K : Subgroup X) :
    Nat.card (Y.subgroupOf K) = Nat.card (Y ⊓ K : Subgroup X) := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_bar_dvd [Finite G] (Y : Subgroup G) : Nat.card (bar D Y) ∣ Nat.card Y := by
  refine (Subgroup.card_map_dvd _ _).trans ?_
  rw [card_subgroupOf]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem card_bar_of_isPGroup [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ Subgroup.normalizer (D : Set G)) : Nat.card (bar D P) = Nat.card P := by
  have hinj : Set.InjOn (toBar D) (P.subgroupOf (Subgroup.normalizer (D : Set G)) : Set _) :=
    fun u hu v hv h => toBar_injOn_of_isPGroup hP hu hv h
  have h1 : Nat.card (bar D P) =
      Nat.card (P.subgroupOf (Subgroup.normalizer (D : Set G))) := by
    rw [bar, ← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hinj]
    rfl
  rw [h1, card_subgroupOf, inf_eq_left.mpr hPH]

theorem bar_eq_bot_iff_of_isPGroup [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ Subgroup.normalizer (D : Set G)) : bar D P = ⊥ ↔ P = ⊥ := by
  rw [Subgroup.eq_bot_iff_card, Subgroup.eq_bot_iff_card, card_bar_of_isPGroup hP hPH]

theorem isSylowOf_bar [Finite G] {S K : Subgroup G} (h : IsSylowOf 2 S K)
    (hK : K ≤ Subgroup.normalizer (D : Set G)) : IsSylowOf 2 (bar D S) (bar D K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSK, hS2, hidx⟩ := isSylowOf_iff.mp h
  refine isSylowOf_iff.mpr ⟨bar_mono D hSK, isPGroup_bar hS2, fun hdvd => hidx ?_⟩
  have h1 := Subgroup.relIndex_mul_card (bar D S) (bar D K)
  rw [inf_eq_left.mpr (bar_mono D hSK), card_bar_of_isPGroup hS2 (hSK.trans hK)] at h1
  have h2 := Subgroup.relIndex_mul_card S K
  rw [inf_eq_left.mpr hSK] at h2
  have h3 := card_bar_dvd (D := D) K
  rw [← h1, ← h2] at h3
  exact hdvd.trans (Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h3)

theorem normalizer_bar [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTH : T ≤ Subgroup.normalizer (D : Set G)) :
    Subgroup.normalizer (bar D T : Set (Bar D)) = bar D (Subgroup.normalizer (T : Set G)) := by
  rw [bar, bar, Subgroup.subgroupOf_normalizer_eq hTH]
  exact AschbacherToolkit.normalizer_quotient_of_isPGroup (coreIn D) (coreIn_odd D)
    hT.comap_subtype

theorem bar_le_normalizer {Y Z : Subgroup G} (hYZ : Y ≤ Subgroup.normalizer (Z : Set G))
    (hZH : Z ≤ Subgroup.normalizer (D : Set G)) :
    bar D Y ≤ Subgroup.normalizer (bar D Z : Set (Bar D)) := by
  refine (bar_mono D hYZ).trans ?_
  rw [bar, Subgroup.subgroupOf_normalizer_eq hZH]
  exact Subgroup.le_normalizer_map _

theorem subgroupOf_rightConjugate {X : Type*} [Group X] {P K : Subgroup X} (y : K) :
    (rightConjugate P y).subgroupOf K = rightConjugate (P.subgroupOf K) y := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_rightConjugate_iff, mem_rightConjugate_iff,
    Subgroup.mem_subgroupOf]
  rfl

theorem map_rightConjugate' {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (P : Subgroup X)
    (g : X) : (rightConjugate P g).map f = rightConjugate (P.map f) (f g) := by
  ext y
  rw [Subgroup.mem_map, mem_rightConjugate_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_rightConjugate_iff] at hx
    exact ⟨g * x * g⁻¹, hx, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hx
    · rw [map_mul, map_mul, map_inv, hxy]
      group

theorem bar_rightConjugate (P : Subgroup G) (y : Subgroup.normalizer (D : Set G)) :
    bar D (rightConjugate P y) = rightConjugate (bar D P) (toBar D y) := by
  rw [bar, subgroupOf_rightConjugate, map_rightConjugate']
  rfl

theorem bar_D_eq_range (D : Subgroup G) : bar D D = (quotientEmbedding D).range := by
  ext x
  rw [mem_bar_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, hD, rfl⟩
    exact ⟨QuotientGroup.mk' _ ⟨h, hD⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨Subgroup.inclusion Subgroup.le_normalizer d, d.2, rfl⟩

theorem oddCore_bar_D [Finite G] (D : Subgroup G) : CFSG.oddCore (bar D D) = ⊥ := by
  let e : D ⧸ aschbacherThm5OddCore D ≃* bar D D :=
    (MonoidHom.ofInjective (quotientEmbedding_injective D)).trans
      (MulEquiv.subgroupCongr (bar_D_eq_range D).symm)
  have h := OddCore.equiv_invariant e
  have h0 : componentClassificationOddCore (D ⧸ aschbacherThm5OddCore D) = ⊥ :=
    quotient_oddCore_eq_bot D
  rw [h0, Subgroup.map_bot] at h
  exact h.symm

theorem oddCore_bar_eq_bot [Finite G] {Q : Subgroup G} (hQD : Q ≤ D)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) : CFSG.oddCore (bar D Q) = ⊥ := by
  set N : Subgroup (Bar D) := (CFSG.oddCore (bar D Q)).map (bar D Q).subtype with hN
  have hNQ : N ≤ bar D Q := Subgroup.map_subtype_le _
  have hQDbar : bar D Q ≤ bar D D := bar_mono D hQD
  have hnorm : bar D D ≤ Subgroup.normalizer (N : Set (Bar D)) := by
    intro x hx
    have hxQ : x ∈ Subgroup.normalizer (bar D Q : Set (Bar D)) :=
      bar_le_normalizer hDQ (hQD.trans Subgroup.le_normalizer) hx
    have hφ := Subgroup.characteristic_iff_map_eq.mp (oddCore_characteristic (bar D Q))
      (onD (bar D Q) ⟨x, hxQ⟩)
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change ((aschbacherThm5OddCore (bar D Q)).map (bar D Q).subtype).map _ = _
    rw [Subgroup.map_map, show (MulAut.conj x : Bar D →* Bar D).comp (bar D Q).subtype =
      (bar D Q).subtype.comp (onD (bar D Q) ⟨x, hxQ⟩).toMonoidHom from
      (onD_equivariant (bar D Q) ⟨x, hxQ⟩).symm, ← Subgroup.map_map, hφ]
    rfl
  have hNodd : Odd (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective (bar D Q).subtype_injective]
    exact OddCore.odd_card _
  have hle : N.subgroupOf (bar D D) ≤ CFSG.oddCore (bar D D) := by
    apply OddCore.maximal
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hNQ.trans hQDbar)).mpr hnorm
    · rwa [card_subgroupOf, inf_eq_left.mpr (hNQ.trans hQDbar)]
  rw [oddCore_bar_D, le_bot_iff] at hle
  have hNbot : N = ⊥ := by
    have hmap := congrArg (Subgroup.map (bar D D).subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot,
      inf_eq_left.mpr (hNQ.trans hQDbar)] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ (bar D Q).subtype_injective).mp hNbot

theorem tightlyEmbedded_subgroupOf_iff {X : Type*} [Group X] {R L : Subgroup X} (hRL : R ≤ L) :
    TightlyEmbedded (R.subgroupOf L) ↔ Even (Nat.card R) ∧ ∀ g ∈ L,
      g ∉ Subgroup.normalizer (R : Set X) →
        Odd (Nat.card (R ⊓ rightConjugate R g : Subgroup X)) :=
  StandardSubgroupAPI.tightlyEmbedded_subgroupOf_iff hRL

theorem le_rightConjugate_of_le_sup_core [Finite G] {M R : Subgroup G}
    (hMH : M ≤ Subgroup.normalizer (D : Set G)) (hR : IsPGroup 2 R)
    (hRM : R ≤ M ⊔ aschbacherThm5Core D) :
    ∃ o ∈ aschbacherThm5Core D, R ≤ rightConjugate M o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := aschbacherThm5Core D
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := hMH.trans (normalizer_le_normalizer_core D)
  obtain ⟨S, hS, -⟩ := AschbacherTheorem3.exists_isSylowOf_le (L := M) (R := ⊥)
    (IsPGroup.of_card (n := 0) (by simp)) bot_le
  have hindex : Odd (M.relIndex (M ⊔ O)) := by
    have h1 := Subgroup.relIndex_mul_card M (M ⊔ O)
    rw [inf_eq_left.mpr le_sup_left] at h1
    have h2 := Subgroup.relIndex_mul_card O (O ⊔ M)
    rw [inf_eq_left.mpr le_sup_left, AschbacherTheorem3.relIndex_sup_of_le_normalizer hMO] at h2
    have h3 := Subgroup.relIndex_mul_card O M
    rw [sup_comm] at h2
    rw [← h2, ← h3, mul_comm (O.relIndex M)] at h1
    have h4 : M.relIndex (M ⊔ O) * Nat.card (O ⊓ M : Subgroup G) = Nat.card O := by
      have hpos : 0 < O.relIndex M := by
        rcases Nat.eq_zero_or_pos (O.relIndex M) with h | h
        · rw [h, zero_mul] at h3
          exact absurd h3.symm Nat.card_pos.ne'
        · exact h
      have h5 : (M.relIndex (M ⊔ O) * Nat.card (O ⊓ M : Subgroup G)) * O.relIndex M =
          Nat.card O * O.relIndex M := by
        rw [mul_assoc, h1, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hpos h5
    exact (core_odd D).of_dvd_nat (Dvd.intro _ h4)
  have hSsup : IsSylowOf 2 S (M ⊔ O) := by
    obtain ⟨hSM, hS2, hSidx⟩ := isSylowOf_iff.mp hS
    refine isSylowOf_iff.mpr ⟨hSM.trans le_sup_left, hS2, fun hdvd => ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S M (M ⊔ O) hSM le_sup_left] at hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
    · exact hSidx h
    · exact (Nat.not_even_iff_odd.mpr hindex) (even_iff_two_dvd.mpr h)
  obtain ⟨c, hc, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hSsup hR hRM
  have hcinv : c⁻¹ ∈ ((M ⊔ O : Subgroup G) : Set G) := (M ⊔ O).inv_mem hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right M O hMO] at hcinv
  obtain ⟨m, hm, o, ho, hmo⟩ := Set.mem_mul.mp hcinv
  refine ⟨o, ho, ?_⟩
  have hRle : R ≤ rightConjugate M c⁻¹ := by
    have h2 : rightConjugate (rightConjugate R c) c⁻¹ ≤ rightConjugate M c⁻¹ :=
      Subgroup.map_mono (hle.trans hS.le)
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h2
  rwa [← hmo, ← rightConjugate_mul, (rightConjugate_eq_self_iff M m).mpr
    (Subgroup.le_normalizer hm)] at hRle

theorem bar_core (D : Subgroup G) : bar D (aschbacherThm5Core D) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, hO, rfl⟩ := (mem_bar_iff D _ x).mp hx
  exact (toBar_eq_one_iff D h).mpr hO

theorem bar_sup_core {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (D : Set G)) :
    bar D (Y ⊔ aschbacherThm5Core D) = bar D Y := by
  rw [bar_sup hY (core_le_normalizer D), bar_core, sup_bot_eq]

theorem toBar_mem_normalizer_bar {P : Subgroup G} (hPH : P ≤ Subgroup.normalizer (D : Set G))
    {n : Subgroup.normalizer (D : Set G)} (hn : (n : G) ∈ Subgroup.normalizer (P : Set G)) :
    toBar D n ∈ Subgroup.normalizer (bar D P : Set (Bar D)) :=
  bar_le_normalizer (Y := Subgroup.normalizer (P : Set G)) le_rfl hPH (toBar_mem_bar D hn)

theorem rightConjugate_le_normalizer {P : Subgroup G} (hPH : P ≤ Subgroup.normalizer (D : Set G))
    (y : Subgroup.normalizer (D : Set G)) :
    rightConjugate P y ≤ Subgroup.normalizer (D : Set G) := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ y.2) (hPH hx)) y.2
  simpa [mul_assoc] using h

theorem tightlyEmbedded_bar [Finite G] {P K : Subgroup G} (hPK : P ≤ K)
    (hKH : K ≤ Subgroup.normalizer (D : Set G)) (hOK : aschbacherThm5Core D ≤ K)
    (heven : Even (Nat.card P))
    (htight : ∀ y ∈ K, y ∉ Subgroup.normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G))) :
    TightlyEmbedded ((bar D P).subgroupOf (bar D K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPH : P ≤ Subgroup.normalizer (D : Set G) := hPK.trans hKH
  rw [tightlyEmbedded_subgroupOf_iff (bar_mono D hPK)]
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    have hZ2 : IsPGroup 2 (Subgroup.zpowers (t : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one])
    have hZP : Subgroup.zpowers (t : G) ≤ P := Subgroup.zpowers_le.mpr t.2
    have hcard := card_bar_of_isPGroup hZ2 (hZP.trans hPH)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht] at hcard
    exact even_iff_two_dvd.mpr (hcard ▸ Subgroup.card_dvd_of_le (bar_mono D hZP))
  · intro ybar hy hyN
    obtain ⟨y, hyK, rfl⟩ := (mem_bar_iff D K ybar).mp hy
    rw [← bar_rightConjugate]
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    set O := aschbacherThm5Core D
    have hPyH := rightConjugate_le_normalizer hPH y
    set W := (P ⊔ O) ⊓ (rightConjugate P y ⊔ O)
    have hWbar : bar D W = bar D P ⊓ bar D (rightConjugate P y) := by
      rw [bar_inf_of_core_le le_sup_right, bar_sup_core hPH, bar_sup_core hPyH]
    have hWeven : Even (Nat.card W) := by
      rw [← hWbar] at hodd
      exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hodd).trans (card_bar_dvd W))
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hWeven)
    set R := Subgroup.zpowers (w : G)
    have hR2 : IsPGroup 2 R :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw, pow_one])
    have hRW : R ≤ W := Subgroup.zpowers_le.mpr w.2
    obtain ⟨o₁, ho₁, h₁⟩ := le_rightConjugate_of_le_sup_core hPH hR2 (hRW.trans inf_le_left)
    obtain ⟨o₂, ho₂, h₂⟩ := le_rightConjugate_of_le_sup_core hPyH hR2 (hRW.trans inf_le_right)
    rw [rightConjugate_mul] at h₂
    set x := (y : G) * o₂ * o₁⁻¹
    have hxK : x ∈ K := K.mul_mem (K.mul_mem hyK (hOK ho₂)) (K.inv_mem (hOK ho₁))
    have hxN : x ∈ Subgroup.normalizer (P : Set G) := by
      by_contra hxN
      apply Nat.not_even_iff_odd.mpr (htight x hxK hxN)
      have hle : rightConjugate R o₁⁻¹ ≤ P ⊓ rightConjugate P x := by
        refine le_inf ?_ ?_
        · have := Subgroup.map_mono (f := (MulAut.conj o₁⁻¹⁻¹).toMonoidHom) h₁
          change rightConjugate R o₁⁻¹ ≤ rightConjugate (rightConjugate P o₁) o₁⁻¹ at this
          rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
        · have := Subgroup.map_mono (f := (MulAut.conj o₁⁻¹⁻¹).toMonoidHom) h₂
          change rightConjugate R o₁⁻¹ ≤ rightConjugate (rightConjugate P _) o₁⁻¹ at this
          rwa [rightConjugate_mul] at this
      have hcard : Nat.card (rightConjugate R o₁⁻¹) = 2 := by
        rw [rightConjugate_card, Nat.card_zpowers, Subgroup.orderOf_coe, hw]
      exact even_iff_two_dvd.mpr (hcard ▸ Subgroup.card_dvd_of_le hle)
    apply hyN
    have hx' : toBar D ⟨x, (Subgroup.normalizer (D : Set G)).mul_mem
        ((Subgroup.normalizer (D : Set G)).mul_mem y.2 (core_le_normalizer D ho₂))
        ((Subgroup.normalizer (D : Set G)).inv_mem (core_le_normalizer D ho₁))⟩ = toBar D y := by
      have h1 : toBar D ⟨o₂, core_le_normalizer D ho₂⟩ = 1 := (toBar_eq_one_iff D _).mpr ho₂
      have h2 : toBar D ⟨o₁, core_le_normalizer D ho₁⟩ = 1 := (toBar_eq_one_iff D _).mpr ho₁
      have hsplit : (⟨x, _⟩ : Subgroup.normalizer (D : Set G)) =
          y * ⟨o₂, core_le_normalizer D ho₂⟩ * ⟨o₁, core_le_normalizer D ho₁⟩⁻¹ := rfl
      rw [hsplit, map_mul, map_mul, map_inv, h1, h2]
      group
    rw [← hx']
    exact toBar_mem_normalizer_bar hPH hxN

theorem bar_inf_normalizer [Finite G] {K T S : Subgroup G}
    (hKH : K ≤ Subgroup.normalizer (D : Set G)) (hOK : aschbacherThm5Core D ≤ K)
    (hT2 : IsPGroup 2 T) (hTH : T ≤ Subgroup.normalizer (D : Set G)) (hSK : S ≤ K)
    (hS2 : IsPGroup 2 S)
    (hSN : IsSylowOf 2 (S ⊓ Subgroup.normalizer (T : Set G))
      (K ⊓ Subgroup.normalizer (T : Set G))) :
    bar D S ⊓ Subgroup.normalizer (bar D T : Set (Bar D)) =
      bar D (S ⊓ Subgroup.normalizer (T : Set G)) ∧
    IsSylowOf 2 (bar D S ⊓ Subgroup.normalizer (bar D T : Set (Bar D)))
      (bar D K ⊓ Subgroup.normalizer (bar D T : Set (Bar D))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbig : bar D K ⊓ Subgroup.normalizer (bar D T : Set (Bar D)) =
      bar D (K ⊓ Subgroup.normalizer (T : Set G)) := by
    rw [normalizer_bar hT2 hTH, inf_comm, ← bar_inf_of_core_le hOK, inf_comm]
  have hsyl : IsSylowOf 2 (bar D (S ⊓ Subgroup.normalizer (T : Set G)))
      (bar D K ⊓ Subgroup.normalizer (bar D T : Set (Bar D))) := by
    rw [hbig]
    exact isSylowOf_bar hSN (inf_le_left.trans hKH)
  have heq : bar D S ⊓ Subgroup.normalizer (bar D T : Set (Bar D)) =
      bar D (S ⊓ Subgroup.normalizer (T : Set G)) := by
    apply hsyl.eq_of_le
    · rw [normalizer_bar hT2 hTH]
      exact le_inf (bar_mono D inf_le_left) (bar_mono D inf_le_right)
    · exact inf_le_inf_right _ (bar_mono D hSK)
    · exact (isPGroup_bar hS2).to_inf_left
  exact ⟨heq, heq ▸ hsyl⟩

theorem hyp3_bar [Finite G] {Q T P S : Subgroup G}
    (hQD : Q ≤ D) (hOQ : aschbacherThm5Core D ≤ Q)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hTH : T ≤ Subgroup.normalizer (D : Set G))
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hTQb : T ⊓ Q = ⊥)
    (hPQT : P ≤ Q ⊔ T) (hTP : IsSylowOf 2 T P) (heven : Even (Nat.card P))
    (htight : ∀ y ∈ Q ⊔ T, y ∉ Subgroup.normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)))
    (hS : IsSylowOf 2 S (Q ⊔ T)) (hTS : T ≤ S)
    (hSN : IsSylowOf 2 (S ⊓ Subgroup.normalizer (T : Set G))
      ((Q ⊔ T) ⊓ Subgroup.normalizer (T : Set G)))
    (hidx : T.relIndex (S ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card T) :
    AschbacherTheorem3.Hyp3 (bar D Q) (bar D T) (bar D P) (bar D S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQH : Q ≤ Subgroup.normalizer (D : Set G) := hQD.trans Subgroup.le_normalizer
  have hKH : Q ⊔ T ≤ Subgroup.normalizer (D : Set G) := sup_le hQH hTH
  have hOK : aschbacherThm5Core D ≤ Q ⊔ T := hOQ.trans le_sup_left
  have hsup : bar D Q ⊔ bar D T = bar D (Q ⊔ T) := (bar_sup hQH hTH).symm
  obtain ⟨hSNeq, hSNsyl⟩ := bar_inf_normalizer hKH hOK hT2 hTH hS.le hS.isPGroup hSN
  refine ⟨?_, ⟨⟨?_, ?_, isPGroup_bar hT2⟩, ?_, ?_⟩, isSylowOf_bar hTP (hPQT.trans hKH), ?_, ?_,
    ?_, oddCore_bar_eq_bot hQD hDQ⟩
  · exact fun h => hT1 ((bar_eq_bot_iff_of_isPGroup hT2 hTH).mp h)
  · exact bar_le_normalizer hTQ hQH
  · rw [← bar_inf_of_core_le hOQ, hTQb, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  · rw [hsup]
    exact isSylowOf_bar hS hKH
  · rw [hsup]
    exact hSNsyl
  · rw [hsup]
    exact bar_mono D hPQT
  · rw [hsup]
    exact tightlyEmbedded_bar hPQT hKH hOK heven htight
  · have hSN2 : IsPGroup 2 (S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :=
      hS.isPGroup.to_inf_left
    have hTSN : T ≤ S ⊓ Subgroup.normalizer (T : Set G) := le_inf hTS Subgroup.le_normalizer
    rw [hSNeq]
    have h1 := Subgroup.relIndex_mul_card (bar D T) (bar D (S ⊓ Subgroup.normalizer (T : Set G)))
    have h2 := Subgroup.relIndex_mul_card T (S ⊓ Subgroup.normalizer (T : Set G))
    rw [inf_eq_left.mpr (bar_mono D hTSN), card_bar_of_isPGroup hT2 hTH,
      card_bar_of_isPGroup hSN2 (inf_le_left.trans (hS.le.trans hKH)), ← h2,
      inf_eq_left.mpr hTSN] at h1
    have h3 := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    rw [h3, card_bar_of_isPGroup hT2 hTH]
    exact hidx

theorem thm3_bar [Finite G] (h3 : AschbacherTheorem3.Theorem3Statement) {Q T P S : Subgroup G}
    (hQD : Q ≤ D) (hOQ : aschbacherThm5Core D ≤ Q)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hTH : T ≤ Subgroup.normalizer (D : Set G))
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hTQb : T ⊓ Q = ⊥)
    (hPQT : P ≤ Q ⊔ T) (hTP : IsSylowOf 2 T P) (heven : Even (Nat.card P))
    (htight : ∀ y ∈ Q ⊔ T, y ∉ Subgroup.normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)))
    (hS : IsSylowOf 2 S (Q ⊔ T)) (hTS : T ≤ S)
    (hSN : IsSylowOf 2 (S ⊓ Subgroup.normalizer (T : Set G))
      ((Q ⊔ T) ⊓ Subgroup.normalizer (T : Set G)))
    (hidx : T.relIndex (S ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card T) :
    AschbacherTheorem3.Thm3Conclusion (bar D Q) (bar D T) (bar D S) :=
  h3 (Bar D) _ _ _ _ (hyp3_bar hQD hOQ hDQ hTH hTQ hT2 hT1 hTQb hPQT hTP heven htight hS hTS
    hSN hidx)

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
