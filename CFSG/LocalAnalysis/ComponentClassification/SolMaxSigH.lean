module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigAlt
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigBasic

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

@[expose] def SignalizerLemma35 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X) (n : ℕ), Sol78.IsSolomonPair t J n →
    ∀ (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E F : Subgroup X), E ≤ J → F ≤ J →
      Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      E ≤ centralizer (F : Set X) →
      ∀ DE DF : Finset (Fin n), DE.card = 4 → DF.card = 4 → Disjoint DE DF →
      (∀ x : J, (x : X) ∈ E → ∀ ω ∉ DE,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) →
      (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) →
      Sol78.signalizerCompletion E E = Sol78.signalizerCompletion F F

variable {X : Type} [Group X]

theorem card_sq_of_klein {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  obtain ⟨φ⟩ := hE
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  · have hsq : ∀ u : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u ^ 2 = 1 := by decide
    have h1 : φ (⟨x, hx⟩ ^ 2) = 1 := by
      rw [map_pow]
      exact hsq _
    have h2 : (⟨x, hx⟩ : E) ^ 2 = 1 := φ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2

theorem klein_of_card_sq {F : Subgroup X} (h4 : Nat.card F = 4) (hsq : ∀ x ∈ F, x * x = 1) :
    Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have := isKleinFour_of_card h4 fun g => Subtype.ext (hsq g g.2)
  have := isKleinFour_prod
  exact IsKleinFour.nonempty_mulEquiv

theorem not_mem_of_isAltTwoComponent [Finite X] {t : X} {J : Subgroup X} {n : ℕ} (hn : 4 ≤ n)
    (h : SolAltLit.IsAltTwoComponent t J n) : t ∉ J := by
  intro htJ
  obtain ⟨ht2, hJt, -, ⟨e⟩⟩ := h
  set T : J := ⟨t, htJ⟩
  have hTc : T ∈ center J := mem_center_iff.mpr fun j => Subtype.ext
    (mem_centralizer_singleton_iff.mp (hJt j.2))
  have hT1 : QuotientGroup.mk' (pPrimeCore 2 J) T = 1 := by
    have h1 : e (QuotientGroup.mk' (pPrimeCore 2 J) T) ∈ center (alternatingGroup (Fin n)) := by
      rw [← Subgroup.map_center_eq e]
      refine ⟨QuotientGroup.mk' (pPrimeCore 2 J) T, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro q
      obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective _ q
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hTc j)]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), mem_bot] at h1
    exact (map_eq_one_iff _ e.injective).mp h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hT1
  have hdvd : orderOf T ∣ Nat.card (pPrimeCore 2 J) := by
    rw [← Subgroup.orderOf_mk T hT1]
    exact orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, ht2] at hdvd
  exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
    (even_iff_two_dvd.mpr hdvd)

theorem mem_coreActionKernel_of_isAltTwoComponent {t : X} {J : Subgroup X} {n : ℕ}
    (h : SolAltLit.IsAltTwoComponent t J n) : t ∈ UnbalancedLayer.coreActionKernel J := by
  have hc : ∀ j ∈ J, t * j = j * t := fun j hj =>
    (mem_centralizer_singleton_iff.mp (h.2.1 hj)).symm
  refine ⟨Sol78.mem_normalizer_of_commute fun j hj => hc j hj, fun j hj => ?_⟩
  have h1 : j⁻¹ * t⁻¹ * j * t = 1 := by
    have h2 : t⁻¹ * j = j * t⁻¹ := by
      calc t⁻¹ * j = t⁻¹ * (j * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * j) * t⁻¹ := by rw [hc j hj]
        _ = j * t⁻¹ := by group
    calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * (t⁻¹ * j) * t := by group
      _ = j⁻¹ * (j * t⁻¹) * t := by rw [h2]
      _ = 1 := by group
  rw [h1]
  exact one_mem _

theorem pPrimeCore_le_of_isPComponent [Finite X] {C J : Subgroup X} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) :
    (pPrimeCore 2 J).map J.subtype ≤ (pPrimeCore 2 C).map C.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := J.subgroupOf C with hL
  have hsub : L.IsSubnormal := hJ.choose_spec.2.1
  have h1 := CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 L hsub
  let φ : L ≃* J := subgroupOfEquivOfLe hJC
  rw [← pPrimeCore_map_iso 2 φ, h1]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨(x : C), hx, rfl⟩

structure Sig36 (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (n : ℕ) (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X)
    (D : Finset (Fin n)) : Prop where
  nonab : ∃ a b : X, a * b ≠ b * a
  kProper : Assembly.KProper Blueprint.Catalog X
  unbal : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥
  notU : ¬ OutcomeLocal.UOutcome X
  pair : Sol78.IsSolomonPair t J n
  le : E ≤ J
  klein : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  card : D.card = 4
  supp : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
    ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem nine_le : 9 ≤ n := S.pair.2.2.1

theorem isPGroup : IsPGroup 2 E :=
  IsPGroup.of_card (n := 2) (by rw [(card_sq_of_klein S.klein).1]; norm_num)

theorem t_mem_centralizer : t ∈ centralizer (E : Set X) := by
  rw [mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.mp (S.pair.1.2.1 (S.le hx))

theorem t_mem_coreActionKernel : t ∈ UnbalancedLayer.coreActionKernel J :=
  mem_coreActionKernel_of_isAltTwoComponent S.pair.1

theorem t_not_mem : t ∉ J := not_mem_of_isAltTwoComponent (by have := S.nine_le; omega) S.pair.1

theorem completion_eq_completion_self (h33 : Sol78.BalanceLemmaInput) {y : X}
    (hy : orderOf y = 2) (hyE : y ∈ centralizer (E : Set X))
    (hyK : y ∈ UnbalancedLayer.coreActionKernel J) (hyJ : y ∉ J) :
    Sol78.signalizerCompletion E (E ⊔ zpowers y) = Sol78.signalizerCompletion E E :=
  (Sol78.signalizerCompletion_of_balanceLemma h33 X S.nonab S.kProper S.unbal S.notU S.pair e
    S.le S.klein ⟨D, S.card, S.supp⟩ hy hyE hyK hyJ).2.2 E le_sup_left
    (card_sq_of_klein S.klein).1

theorem odd_card_completion (h33 : Sol78.BalanceLemmaInput) :
    Odd (Nat.card (Sol78.signalizerCompletion E E)) := by
  rw [← S.completion_eq_completion_self h33 S.pair.1.1 S.t_mem_centralizer
    S.t_mem_coreActionKernel S.t_not_mem]
  exact (Sol78.signalizerCompletion_of_balanceLemma h33 X S.nonab S.kProper S.unbal S.notU
    S.pair e S.le S.klein ⟨D, S.card, S.supp⟩ S.pair.1.1 S.t_mem_centralizer
    S.t_mem_coreActionKernel S.t_not_mem).1

theorem core_le_normalizer (h33 : Sol78.BalanceLemmaInput) :
    (pPrimeCore 2 J).map J.subtype ≤
      normalizer (Sol78.signalizerCompletion E E : Set X) := by
  have hWt := S.completion_eq_completion_self h33 S.pair.1.1 S.t_mem_centralizer
    S.t_mem_coreActionKernel S.t_not_mem
  have hθ : SolAltLit.thetaFunctor E t ≤ Sol78.signalizerCompletion E E := by
    rw [← hWt]
    have ht1 : t ≠ 1 := by
      intro h
      have := S.pair.1.1
      rw [h, orderOf_one] at this
      omega
    exact le_iSup₂_of_le (f := fun (c : X) (_ : c ∈ E ⊔ zpowers t) =>
      ⨆ (_ : c ≠ 1), SolAltLit.thetaFunctor E c) t (mem_sup_right (mem_zpowers t))
      (le_iSup_of_le ht1 le_rfl)
  have hEt : E ≤ centralizer ({t} : Set X) := S.le.trans S.pair.1.2.1
  have hOt := oddCore_le_normalizer_of_theta S.isPGroup hEt hθ
    (normalizer_le_normalizer_signalizerCompletion_self E)
  exact (pPrimeCore_le_of_isPComponent S.pair.1.2.1 S.pair.1.2.2.1).trans hOt

theorem le_normalizer_completion (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35) :
    J ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  obtain ⟨hE4, hE2⟩ := card_sq_of_klein S.klein
  obtain ⟨F, D', hFJ, hF4, hFsq, hD', hdisj, hFs, hFE⟩ :=
    exists_commuting_four_subgroup S.nine_le e S.le S.isPGroup S.card S.supp
  have hFk := klein_of_card_sq hF4 hFsq
  have hEF : E ≤ centralizer (F : Set X) := le_centralizer_iff.mp hFE
  have hWF := h35 X S.nonab S.kProper S.unbal S.notU t J n S.pair e E F S.le hFJ S.klein hFk hEF
    D D' S.card hD' hdisj S.supp hFs
  have hNF : normalizer (F : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    hWF ▸ normalizer_le_normalizer_signalizerCompletion_self F
  have hF2 : ∀ x ∈ F, x ^ 2 = 1 := fun x hx => by rw [sq]; exact hFsq x hx
  have hgen := le_normalizer_sup_normalizer_sup_core S.nine_le e S.le hFJ hE4 hF4 hE2 hF2 S.card
    hD' hdisj S.supp hFs
  exact hgen.trans (sup_le (sup_le (normalizer_le_normalizer_signalizerCompletion_self E) hNF)
    (S.core_le_normalizer h33))

theorem normalizer_completion_ne_top (h33 : Sol78.BalanceLemmaInput)
    (hW : Sol78.signalizerCompletion E E ≠ ⊥) :
    normalizer (Sol78.signalizerCompletion E E : Set X) ≠ ⊤ := by
  intro htop
  have hnorm : (Sol78.signalizerCompletion E E).Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Sol78.signalizerCompletion E E) with h | h
  · exact hW h
  · have hodd := S.odd_card_completion h33
    rw [h, Subgroup.card_top] at hodd
    have h2 := orderOf_dvd_natCard t
    rw [S.pair.1.1] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end Sig36

end CFSG.ComponentClassification.SolMax
