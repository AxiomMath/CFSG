module

public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_centralizer {a y : G} (hy : y ∈ Subgroup.centralizer ({a} : Set G)) :
    y ∈ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
  have hay : a * y = y * a := by
    exact Subgroup.mem_centralizer_iff.1 hy a (Set.mem_singleton a)
  have hy' : y⁻¹ * a = a * y⁻¹ := by
    calc y⁻¹ * a = y⁻¹ * (a * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * a) * y⁻¹ := by rw [hay]
      _ = a * y⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  have key1 : a * (y * h * y⁻¹) = y * (a * h) * y⁻¹ := by
    calc a * (y * h * y⁻¹) = (a * y) * h * y⁻¹ := by group
      _ = (y * a) * h * y⁻¹ := by rw [hay]
      _ = y * (a * h) * y⁻¹ := by group
  have key2 : (y * h * y⁻¹) * a = y * (h * a) * y⁻¹ := by
    calc (y * h * y⁻¹) * a = y * h * (y⁻¹ * a) := by group
      _ = y * h * (a * y⁻¹) := by rw [hy']
      _ = y * (h * a) * y⁻¹ := by group
  rw [key1, key2]
  constructor
  · intro e
    rw [e]
  · intro e
    have h2 := congrArg (fun z => y⁻¹ * z * y) e
    simpa [mul_assoc] using h2

theorem inf_le_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) {H X : Subgroup G} (hXH : X ≤ H) :
    GLAPPrimeCoreOf p H ⊓ X ≤ GLAPPrimeCoreOf p X := by
  intro x hx
  obtain ⟨hxO, hxX⟩ := hx
  set P : Subgroup G := GLAPPrimeCoreOf p H ⊓ X with hP
  set P' : Subgroup ↥X := P.subgroupOf X with hP'
  have hPX : P ≤ X := inf_le_right
  have hnorm : P'.Normal := by
    constructor
    intro n hn g
    rw [hP', Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnO, hnX⟩ := hn
    refine ⟨?_, ?_⟩
    · have hg : (g : G) ∈ H := hXH g.2
      have hmem := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p H hg) (n : G)).1 hnO
      simpa [mul_assoc] using hmem
    · exact X.mul_mem (X.mul_mem g.2 hnX) (X.inv_mem g.2)
  have hcop : Nat.Coprime p (Nat.card P') := by
    have hcard : Nat.card P' = Nat.card P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv
    have hdvd : Nat.card P ∣ Nat.card (GLAPPrimeCoreOf p H) := Subgroup.card_dvd_of_le inf_le_left
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => not_dvd_card_glaPPrimeCoreOf hp H (h.trans hdvd)
  have hmem : (⟨x, hxX⟩ : ↥X) ∈ P' := by
    rw [hP', Subgroup.mem_subgroupOf]
    exact ⟨hxO, hxX⟩
  have hle : P' ≤ CFSG.pPrimeCore p ↥X := le_sSup ⟨hnorm, hcop⟩
  exact ⟨⟨x, hxX⟩, hle hmem, rfl⟩

theorem ne_bot_of_isComponentOf_top {Q : Type} [Group Q] {A : Subgroup Q}
    (h : CFSG.Open.IsComponentOf A ⊤) : A ≠ ⊥ := by
  rintro rfl
  haveI := h.2.2.2
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥(⊥ : Subgroup Q) ⧸ Subgroup.center ↥(⊥ : Subgroup Q))
  apply hxy
  have hz : ∀ z : ↥(⊥ : Subgroup Q) ⧸ Subgroup.center ↥(⊥ : Subgroup Q), z = 1 := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
    have ha : a = 1 := Subtype.ext (show (a : Q) = 1 from Subgroup.mem_bot.1 a.2)
    rw [ha]
    rfl
  exact (hz x).trans (hz y).symm

theorem not_le_glaPPrimeCoreOf_of_component {p : ℕ} (hp : p.Prime) {X I J : Subgroup G}
    (hI : GLAPComponent p X I) (hXJ : X ≤ J) : ¬ I ≤ GLAPPrimeCoreOf p J := by
  intro hIO
  have hIX : I ≤ X := hI.1
  have hIOX : I ≤ GLAPPrimeCoreOf p X := fun i hi =>
    inf_le_glaPPrimeCoreOf hp hXJ ⟨hIO hi, hIX hi⟩
  apply ne_bot_of_isComponentOf_top hI.2.2.1
  rw [eq_bot_iff]
  rintro _ ⟨⟨i, hi⟩, hi', rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨z, hz, hzi⟩ := hIOX (Subgroup.mem_subgroupOf.1 hi')
  have hzeq : z = ⟨i, hi⟩ := Subtype.ext hzi
  rw [← hzeq]
  exact hz

theorem normalizer_of_centralized {p : ℕ} (hp : p.Prime) {H J I : Subgroup G} {y : G}
    (hJ : GLAPComponent p H J) (hyH : y ∈ Subgroup.normalizer (H : Set G))
    (hIJ : I ≤ J) (hIy : I ≤ Subgroup.centralizer ({y} : Set G))
    (hIperf : ⁅I, I⁆ = I) (hIn : ¬ I ≤ GLAPPrimeCoreOf p J) :
    y ∈ Subgroup.normalizer (J : Set G) := by
  classical
  by_contra hnot
  have hHy : GLBConj y H = H := mem_normalizer_iff_gLBConj_eq.1 hyH
  have hJ' : GLAPComponent p H (GLBConj y J) := by
    have h := glaPComponent_gLBConj hJ y
    rwa [hHy] at h
  have hne : GLBConj y J ≠ J := fun h => hnot (mem_normalizer_iff_gLBConj_eq.2 h)
  have hbar : barX p H J ≠ barX p H (GLBConj y J) := fun h =>
    hne (glaPComponent_unique hJ hJ' h).symm
  have hcomm : ⁅barX p H J, barX p H (GLBConj y J)⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hJ.2.2.1 hJ'.2.2.1 hbar
  have hJH : J ≤ H := hJ.1
  have hO : ∀ j ∈ J, ∀ i ∈ I, ⁅j, i⁆ ∈ GLAPPrimeCoreOf p H := by
    intro j hj i hi
    have hiJ : i ∈ J := hIJ hi
    have hiH : i ∈ H := hJH hiJ
    have hjH : j ∈ H := hJH hj
    have hiJ' : i ∈ GLBConj y J := by
      rw [mem_gLBConj]
      have hc : y * i = i * y := Subgroup.mem_centralizer_iff.1 (hIy hi) y (Set.mem_singleton y)
      have : y * i * y⁻¹ = i := by
        rw [hc]
        group
      rw [this]
      exact hiJ
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨j, hjH⟩ ∈ barX p H J :=
      Subgroup.mem_map.2 ⟨⟨j, hjH⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨i, hiH⟩ ∈ barX p H (GLBConj y J) :=
      Subgroup.mem_map.2 ⟨⟨i, hiH⟩, Subgroup.mem_subgroupOf.2 hiJ', rfl⟩
    have h3 : ⁅QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨j, hjH⟩,
        QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨i, hiH⟩⁆ ∈ (⊥ : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator h1 h2
    rw [Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h3
    refine ⟨⁅(⟨j, hjH⟩ : ↥H), ⟨i, hiH⟩⁆, h3, ?_⟩
    simp [commutatorElement_def]
  have hIO : ⁅I, I⁆ ≤ GLAPPrimeCoreOf p J := by
    refine Subgroup.commutator_le.2 fun i hi i' hi' => ?_
    have hmemO : ⁅i, i'⁆ ∈ GLAPPrimeCoreOf p H := hO i (hIJ hi) i' hi'
    have hmemJ : ⁅i, i'⁆ ∈ J :=
      (commutator_le_of_le' le_rfl le_rfl) (Subgroup.commutator_mem_commutator (hIJ hi) (hIJ hi'))
    exact inf_le_glaPPrimeCoreOf hp hJH ⟨hmemO, hmemJ⟩
  exact hIn (hIperf ▸ hIO)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
