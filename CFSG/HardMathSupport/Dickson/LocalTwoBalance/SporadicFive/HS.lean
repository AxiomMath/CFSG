module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveHSMcL

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.RankThree.Native CFSG.Sporadic.SmallOddCore

set_option linter.unusedSectionVars false

theorem ltbFive_conj_bot {p : ℕ} {M : Type*} [Group M] {R : Subgroup M} {k : M} (hk : k ∈ R)
    {x : M} (h : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set M) ⊓ R) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({k * x * k⁻¹} : Set M) ⊓ R) = ⊥ := by
  set ψ : M →* M := (MulAut.conj k).toMonoidHom with hψdef
  have hψ : Function.Injective ψ := (MulAut.conj k).injective
  have hR : R.map ψ = R := by
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact R.mul_mem (R.mul_mem hk hr) (R.inv_mem hk)
    · intro hy
      refine ⟨k⁻¹ * y * k, R.mul_mem (R.mul_mem (R.inv_mem hk) hy) hk, ?_⟩
      show k * (k⁻¹ * y * k) * k⁻¹ = y
      group
  have h1 : GLAPPrimeCoreOf p (R ⊓ Subgroup.centralizer ({x} : Set M)) = ⊥ := by
    rw [inf_comm]
    exact h
  have h2 : (GLAPPrimeCoreOf p (R ⊓ Subgroup.centralizer ({x} : Set M))).map ψ = ⊥ := by
    rw [h1, Subgroup.map_bot]
  rw [map_glaPPrimeCoreOf_of_injective p ψ hψ, map_inf_centralizer_of_injective ψ hψ R x, hR]
    at h2
  rw [inf_comm]
  exact h2

theorem ltbFive_three_of_mem {r : Fin 31} (h : (r : ℕ) ∈ ({0, 2, 23} : Finset ℕ)) :
    r = 0 ∨ r = 2 ∨ r = 23 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem ltbFive_two_of_mem {r : Fin 31} (h : (r : ℕ) ∈ ({0, 1} : Finset ℕ)) :
    r = 0 ∨ r = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem ltbFive_witness_of_lines {M : Type*} [Group M] [Finite M] {P R Q : Subgroup M}
    (hA : AutModel P R) (hQP : Q ≤ P)
    (hQsyl : ∃ S : Sylow 5 P, (S : Subgroup P) = Q.subgroupOf P)
    (hQc : Nat.card Q = 5 ^ 3) (hQe : Monoid.exponent Q = 5)
    {lines k : Fin 31 → M} {rec : Fin 31 → Fin 31}
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = 5} =
      Set.range fun j => Subgroup.zpowers (lines j))
    (htrans : ∀ j, k j ∈ R ∧ k j * lines (rec j) * (k j)⁻¹ = lines j)
    (hrec : ∀ j, GLAPPrimeCoreOf 5 (Subgroup.centralizer ({lines (rec j)} : Set M) ⊓ R) = ⊥)
    (hC0 : Nat.card (Subgroup.centralizer ({lines 0} : Set M) ⊓ R : Subgroup M) < 5 ^ 3) :
    ∀ E : Subgroup P, IsElemAbelian 5 E → Nat.card E = 5 ^ 2 →
      ∃ d ∈ E, d ≠ 1 ∧
        GLAPPrimeCoreOf 5 (Subgroup.centralizer ({(d : M)} : Set M) ⊓ R) = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hlineQ : ∀ j, lines j ∈ Q := fun j => by
    have hm : Subgroup.zpowers (lines j) ∈ {H : Subgroup M | H ≤ Q ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨j, rfl⟩
    exact Subgroup.zpowers_le.1 hm.1
  have hlineO : ∀ j, GLAPPrimeCoreOf 5 (Subgroup.centralizer ({lines j} : Set M) ⊓ R) = ⊥ := by
    intro j
    obtain ⟨hkR, hkc⟩ := htrans j
    rw [← hkc]
    exact ltbFive_conj_bot hkR (hrec j)
  have hall : ∀ x ∈ Q, orderOf x = 5 →
      GLAPPrimeCoreOf 5 (Subgroup.centralizer ({x} : Set M) ⊓ R) = ⊥ := by
    intro x hxQ hxo
    have hm : Subgroup.zpowers x ∈ {H : Subgroup M | H ≤ Q ∧ Nat.card H = 5} :=
      ⟨Subgroup.zpowers_le.2 hxQ, by rw [Nat.card_zpowers, hxo]⟩
    rw [hlines] at hm
    obtain ⟨j, hj⟩ := hm
    rw [centralizer_singleton_eq_of_zpowers hj.symm]
    exact hlineO j
  obtain ⟨Q', hQ'⟩ := hQsyl
  have hmemQ' : ∀ y : P, y ∈ (Q' : Subgroup P) ↔ (y : M) ∈ Q := fun y => by
    rw [hQ', Subgroup.mem_subgroupOf]
  have hQ'c : Nat.card (Q' : Subgroup P) = 5 ^ 3 := by
    rw [hQ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQc]
  have hexp : ∀ x ∈ Q, x ^ 5 = 1 := fun x hx => by
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : Q)
    rw [hQe] at h
    simpa using congrArg Subtype.val h
  haveI : Nontrivial (Q' : Subgroup P) :=
    (Finite.one_lt_card_iff_nontrivial).1 (by rw [hQ'c]; norm_num)
  have hbot := IsPGroup.bot_lt_center Q'.isPGroup'
  obtain ⟨c, hcC, hc⟩ := SetLike.exists_of_lt hbot
  have hc1 : (c : P) ≠ 1 := fun h => hc (Subgroup.mem_bot.2 (Subtype.ext h))
  set z : P := (c : P) with hzdef
  have hzQ' : z ∈ Q' := c.2
  have hzM : (z : M) ∈ Q := (hmemQ' z).1 c.2
  have hzc : ∀ g ∈ Q', g * z = z * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hcC ⟨g, hg⟩)
  have hz5 : z ^ 5 = 1 := Subtype.ext (by simpa using hexp (z : M) hzM)
  have hzo : orderOf z = 5 := orderOf_eq_prime hz5 hc1
  have hzMo : orderOf (z : M) = 5 := (Subgroup.orderOf_coe z).trans hzo
  have hz : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({(z : M)} : Set M) ⊓ R) = ⊥ :=
    hall (z : M) hzM hzMo
  have hnc : ∃ a ∈ Q', ∃ b ∈ Q', a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : Q ≤ Subgroup.centralizer ({lines 0} : Set M) ⊓ R := by
      intro y hy
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hA.le (hQP hy)⟩
      exact (congrArg Subtype.val
        (hcon ⟨lines 0, hQP (hlineQ 0)⟩ ((hmemQ' _).2 (hlineQ 0)) ⟨y, hQP hy⟩
          ((hmemQ' _).2 hy))).symm
    have h1 := Subgroup.card_le_of_le hcomm
    rw [hQc] at h1
    exact lt_irrefl _ (lt_of_le_of_lt h1 hC0)
  have hΦ : ∀ (g d : P), GLAPPrimeCoreOf 5 (Subgroup.centralizer ({(d : M)} : Set M) ⊓ R) = ⊥ →
      GLAPPrimeCoreOf 5 (Subgroup.centralizer ({((g * d * g⁻¹ : P) : M)} : Set M) ⊓ R) = ⊥ := by
    intro g d hd
    have e : ((g * d * g⁻¹ : P) : M) = (g : M) * (d : M) * (g : M)⁻¹ := by simp
    rw [e]
    exact ltbFive_conj_bot (hA.le g.2) hd
  intro E hE hEc
  exact exists_plane_witness_of_sylow_card_cube' Nat.prime_five Q' hQ'c hzQ' hzo hzc hnc
    (fun d : P => GLAPPrimeCoreOf 5 (Subgroup.centralizer ({(d : M)} : Set M) ⊓ R) = ⊥) hΦ hz
    E hE hEc

section HS


theorem sporadicTwoBalanceFive_HS : SporadicTwoBalanceFive .HS := by
  intro S _ _ hS hnab he
  obtain ⟨eB⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  obtain ⟨e0⟩ := he
  let θ : S ≃* hs100P := e0.trans (eB.symm.trans hs100Equiv)
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 :=
    (Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence θ).toEquiv).le.trans
      outer_card_hs100P
  obtain ⟨⟨⟨hQP, hQsyl, hQc, hQe⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hC0c⟩, -, -, -, -, -⟩,
    -⟩ := R3E_HS_McL_full_five_centralizer_structures
  have hC0' : Nat.card (Subgroup.centralizer ({hs100FiveLine 0} : Set (Equiv.Perm (Fin 100))) ⊓
      hs100R : Subgroup (Equiv.Perm (Fin 100))) < 5 ^ 3 := by
    rw [← hC0, hC0c]
    norm_num
  exact CFSG.HardMathSupport.Timmesfeld.Coordinator.isLocallyBalancedAbs_two_of_autModel
    Nat.prime_five (by norm_num) CFSG.RankThree.PartOne.hs_autModel θ hcen hout
    (ltbFive_witness_of_lines CFSG.RankThree.PartOne.hs_autModel hQP hQsyl
      (hQc.trans (by norm_num)) hQe hlines htrans
      (fun j => gLAPPrimeCoreOf_hs100FiveRecord_eq_bot _ (ltbFive_three_of_mem (hrecmem j))) hC0')

end HS

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
