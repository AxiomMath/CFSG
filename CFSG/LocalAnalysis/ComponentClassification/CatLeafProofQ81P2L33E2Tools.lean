module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33ReeTools

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.LieType.Chevalley
open scoped commutatorElement

theorem isPGroup_quot_of_equiv {A B : Type*} [Group A] [Group B] (E : A ≃* B)
    (h : IsPGroup 2 (A ⧸ pPrimeCore 2 A)) : IsPGroup 2 (B ⧸ pPrimeCore 2 B) :=
  h.of_equiv (QuotientGroup.congr _ _ E (pPrimeCore_map_iso 2 E))

theorem not_isPGroup_quot_of_perfect {T : Type*} [Group T] [Finite T]
    (hT : _root_.commutator T = ⊤) (heven : 2 ∣ Nat.card T) :
    ¬ IsPGroup 2 (T ⧸ pPrimeCore 2 T) := fun h =>
  Ree.not_isPGroup_of_perfect_equiv (F := (⊤ : Subgroup T)) le_rfl Subgroup.topEquiv hT heven
    (isPGroup_quot_of_equiv Subgroup.topEquiv.symm h)

theorem not_isPGroup_quot_of_le {M : Type*} [Group M] {A D : Subgroup M} [Finite A]
    (hDA : D ≤ A) (hD : ⁅D, D⁆ = D) (heven : 2 ∣ Nat.card D) :
    ¬ IsPGroup 2 (↥A ⧸ pPrimeCore 2 ↥A) := by
  intro h
  have hX : ⁅D.subgroupOf A, D.subgroupOf A⁆ = D.subgroupOf A := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDA, hD]
  apply not_isPGroup_of_perfect (G := ↥A) (F := ⊤) le_top hX
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hDA).toEquiv])
  exact isPGroup_quot_of_equiv Subgroup.topEquiv.symm h

theorem commutator_eq_top_of_simple_of_four_dvd {S : Type*} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (h4 : 4 ∣ Nat.card S) : _root_.commutator S = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (_root_.commutator S) with h | h
  · exfalso
    have hcomm : ∀ a b : S, a * b = b * a := fun a b => by
      have h1 : ⁅a, b⁆ ∈ _root_.commutator S := by
        rw [_root_.commutator_def]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have : Fintype S := Fintype.ofFinite S
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := S) 2
      (by rw [← Nat.card_eq_fintype_card]; exact (by norm_num : 2 ∣ 4).trans h4)
    have hn : (zpowers g).Normal :=
      ⟨fun n hn c => by rw [hcomm c n, mul_inv_cancel_right]; exact hn⟩
    rcases hs.eq_bot_or_eq_top_of_normal (zpowers g) with h1 | h1
    · rw [zpowers_eq_bot] at h1
      rw [h1, orderOf_one] at hg
      exact absurd hg (by norm_num)
    · have h2 := Nat.card_zpowers g
      rw [h1, card_top, hg] at h2
      rw [h2] at h4
      exact absurd h4 (by norm_num)
  · exact h

theorem not_isPGroup_of_conj {C : Type} [Group C] [Finite C] {β γ ψ : MulAut C}
    (hψ : ψ * β * ψ⁻¹ = γ)
    (hγ : ¬ IsPGroup 2 (↥(fixedPoints γ) ⧸ pPrimeCore 2 ↥(fixedPoints γ))) :
    ¬ IsPGroup 2 (↥(fixedPoints β) ⧸ pPrimeCore 2 ↥(fixedPoints β)) := by
  intro hP
  have h1 := isPGroup_fixedPoints_congr ψ β hP
  have hc : MulAut.congr ψ β = γ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ β = ψ * β * ψ⁻¹).trans hψ
  rw [hc] at h1
  exact hγ h1

noncomputable def centralizerEquiv {Y P : Type*} [Group Y] [Group P] (e : Y ≃* P) (c : Y) :
    ↥(centralizer ({c} : Set Y)) ≃* ↥(centralizer ({e c} : Set P)) :=
  (e.subgroupMap (centralizer ({c} : Set Y))).trans (MulEquiv.subgroupCongr (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
      rw [mem_centralizer_singleton_iff]
      have h1 := congrArg e hy
      simpa using h1
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [mem_centralizer_singleton_iff] at hx
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply e.injective
      simpa using hx))

theorem pPrimeCore_eq_bot_of_equiv {A B : Type*} [Group A] [Group B] (E : A ≃* B)
    (h : pPrimeCore 2 B = ⊥) : pPrimeCore 2 A = ⊥ := by
  have h1 := pPrimeCore_map_iso 2 E
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ E.injective).mp h1

theorem isCharacteristicP_centralizer
    {K : Type} [Field K] [Finite K] [CharP K 2] (D : RootWeightDatum K) {c : D.group}
    (hc2 : c ^ 2 = 1) (hc : c ≠ 1) :
    IsCharacteristicP 2 ↥(centralizer ({c} : Set D.group)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := zpowers c with hQ
  have hQp : IsPGroup 2 Q := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show ((2 : ℕ) : ℤ) = 2 from rfl, zpow_two, ← sq, hc2, one_zpow, Subgroup.coe_one]
  have hQ1 : Q ≠ ⊥ := fun h => hc (by
    have : c ∈ Q := Subgroup.mem_zpowers c
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hcent : centralizer (Q : Set D.group) = centralizer ({c} : Set D.group) := by
    rw [hQ, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨hchar, -⟩ := D.defining_characteristic_root_local_groups_component_free 2 Q hQp hQ1
    (centralizer (Q : Set D.group)) (Or.inr rfl)
  rw [hcent] at hchar
  exact hchar

theorem inner_not_isPGroup {Y C : Type} [Group Y] [Group C] [Finite Y] [Finite C] (e : Y ≃* C)
    (hchar : ∀ c : C, c ^ 2 = 1 → c ≠ 1 → IsCharacteristicP 2 ↥(centralizer ({c} : Set C)))
    (hopen : ∀ c : Y, orderOf c = 2 → ¬ IsPGroup 2 ↥(centralizer ({c} : Set Y)))
    (c : Y) (hc : orderOf c = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints (MulAut.conj c)) ⧸
      pPrimeCore 2 ↥(fixedPoints (MulAut.conj c))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Ree.fixedPoints_conj]
  intro hP
  apply hopen c hc
  have hc2 : e c ^ 2 = 1 := by rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
  have hc1 : e c ≠ 1 := by
    intro h
    have h1 : c = 1 := e.injective (h.trans (map_one e).symm)
    rw [h1, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have hO := pPrimeCore_eq_bot_of_isCharacteristicP _ 2 (hchar (e c) hc2 hc1)
  exact isPGroup_of_pPrimeCore_eq_bot (pPrimeCore_eq_bot_of_equiv (centralizerEquiv e c) hO) hP

end CFSG.ComponentClassification.HarrisLit.L33.E2
