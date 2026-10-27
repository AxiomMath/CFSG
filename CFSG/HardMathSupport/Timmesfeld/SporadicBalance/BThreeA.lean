module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.Monster.B.TwoA.Amalgam.FischerNodes
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTT
public import CFSG.Monster.B.TwoA.Amalgam.OrderThree
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster CFSG.Monster.B
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G]

theorem mem_pow_mul_of_card_le [Finite G] {C Q : Subgroup G} {s : G} (hsC : s ∈ C)
    (hQC : Q ≤ C) (hs3 : s * s * s = 1) (hsQ : s ∉ Q) (hcard : Nat.card C ≤ 3 * Nat.card Q) :
    ∀ g ∈ C, ∃ k : ℕ, ∃ q ∈ Q, g = s ^ k * q := by
  have hs3' : s ^ 3 = 1 := by rw [pow_three']; exact hs3
  have hsq : ∀ k : Fin 3, s ^ (k : ℕ) * 1 ∈ C := fun k => C.mul_mem (C.pow_mem hsC _) C.one_mem
  let f : Fin 3 × Q → C := fun p => ⟨s ^ (p.1 : ℕ) * p.2, C.mul_mem (C.pow_mem hsC _) (hQC p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨k, q⟩ ⟨k', q'⟩ h
    have h1 : s ^ (k : ℕ) * (q : G) = s ^ (k' : ℕ) * q' := congrArg Subtype.val h
    have h2 : (s ^ (k' : ℕ))⁻¹ * s ^ (k : ℕ) = q' * (q : G)⁻¹ := by
      calc (s ^ (k' : ℕ))⁻¹ * s ^ (k : ℕ) = (s ^ (k' : ℕ))⁻¹ * (s ^ (k : ℕ) * q) * (q : G)⁻¹ := by
            group
        _ = (s ^ (k' : ℕ))⁻¹ * (s ^ (k' : ℕ) * q') * (q : G)⁻¹ := by rw [h1]
        _ = q' * (q : G)⁻¹ := by group
    have hmem : (s ^ (k' : ℕ))⁻¹ * s ^ (k : ℕ) ∈ Q := by
      rw [h2]; exact Q.mul_mem q'.2 (Q.inv_mem q.2)
    have hpow : ∀ m : ℕ, s ^ m ∈ Q → m % 3 = 0 := by
      intro m hm
      have e : s ^ m = s ^ (m % 3) := by
        conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hs3', one_pow, one_mul]
      rw [e] at hm
      have h012 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases h012 with h | h | h
      · exact h
      · rw [h, pow_one] at hm
        exact absurd hm hsQ
      · exfalso
        apply hsQ
        rw [h] at hm
        have h4 : s = s ^ 2 * s ^ 2 := by
          rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hs3', one_mul, pow_one]
        rw [h4]
        exact Q.mul_mem hm hm
    have hinv : (s ^ (k' : ℕ))⁻¹ = s ^ (2 * (k' : ℕ)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show (k' : ℕ) + 2 * k' = 3 * k' by ring, pow_mul, hs3', one_pow]
    rw [hinv, ← pow_add] at hmem
    have h3 := hpow _ hmem
    have hk := k.2
    have hk' := k'.2
    have hkk : k = k' := Fin.ext (by omega)
    subst hkk
    have hq : (q : G) = q' := by
      have := h1
      simpa using this
    exact Prod.ext rfl (Subtype.ext hq)
  have hcardf : Nat.card (Fin 3 × Q) = 3 * Nat.card Q := by
    rw [Nat.card_prod, Nat.card_fin]
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hcardf]; exact hcard)
  intro g hg
  obtain ⟨⟨k, q⟩, hkq⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨k, q, q.2, (congrArg Subtype.val hkq).symm⟩

theorem gLAPPrimeCoreOf_eq_bot_of_pow_mul [Finite G] {C Q H : Subgroup G} {s : G}
    (hs3 : s * s * s = 1) (hqs : ∀ q ∈ Q, q * s = s * q) (hHQ : H ≤ Q) (hQC : Q ≤ C)
    (hdecomp : ∀ g ∈ C, ∃ k : ℕ, ∃ q ∈ Q, g = s ^ k * q)
    (hHn : ∀ q ∈ Q, ∀ h ∈ H, q * h * q⁻¹ ∈ H) (hsimp : IsSimpleGroup H)
    (hcomm : commutator H = ⊤) (hcenter : Subgroup.center H = ⊥) (h3 : 3 ∣ Nat.card H)
    (hCQH : ∀ q ∈ Q, (∀ h ∈ H, q * h = h * q) → q = 1) :
    GLAPPrimeCoreOf 3 C = ⊥ := by
  have hs3' : s ^ 3 = 1 := by rw [pow_three']; exact hs3
  refine gLAPPrimeCoreOf_eq_bot_of_isQuasisimple Nat.prime_three (L := H)
    (le_trans hHQ hQC) ?_ ?_ h3 ?_
  · intro g hg h hh
    obtain ⟨k, q, hq, rfl⟩ := hdecomp g hg
    have hqh := hHn q hq h hh
    have hc : Commute s (q * h * q⁻¹) := (hqs _ (hHQ hqh)).symm
    have hcomm' : s ^ k * (q * h * q⁻¹) = q * h * q⁻¹ * s ^ k := (hc.pow_left k).eq
    have e : s ^ k * q * h * (s ^ k * q)⁻¹ = q * h * q⁻¹ := by
      calc s ^ k * q * h * (s ^ k * q)⁻¹ = s ^ k * (q * h * q⁻¹) * (s ^ k)⁻¹ := by group
        _ = q * h * q⁻¹ := by rw [hcomm', mul_inv_cancel_right]
    rw [e]
    exact hqh
  · refine ⟨hcomm, ?_⟩
    have e : (↥H ⧸ Subgroup.center ↥H) ≃* ↥H :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact MulEquiv.isSimpleGroup e
  · refine IsPGroup.iff_orderOf.2 fun g => ?_
    obtain ⟨hgC, hgH⟩ := Subgroup.mem_inf.1 g.2
    obtain ⟨k, q, hq, hgq⟩ := hdecomp _ hgC
    have hq1 : q = 1 := by
      refine hCQH q hq fun h hh => ?_
      have hgh : (g : G) * h = h * g :=
        (Subgroup.mem_centralizer_iff.1 hgH h hh).symm
      have hsh : s ^ k * h = h * s ^ k :=
        ((Commute.pow_left (show Commute s h from (hqs h (hHQ hh)).symm) k)).eq
      have : s ^ k * (q * h) = s ^ k * (h * q) := by
        calc s ^ k * (q * h) = (g : G) * h := by rw [hgq, mul_assoc]
          _ = h * g := hgh
          _ = h * s ^ k * q := by rw [hgq, mul_assoc]
          _ = s ^ k * (h * q) := by rw [← hsh, mul_assoc]
      exact mul_left_cancel this
    rw [hq1, mul_one] at hgq
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hgq, ← pow_mul, mul_comm, pow_mul, hs3', one_pow, Subgroup.coe_one]
    have hdvd : orderOf g ∣ 3 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hg3)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨j, hj⟩

end Generic

section Labels


@[expose] def BThreeABound : Prop :=
  ∀ v w : CVert, w ∈ sphereThree v →
    Nat.card (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) ≤
      3 * Nat.card (vStab v ⊓ vStab w : Subgroup Shat)

theorem commute_of_mem_vStab {v : CVert} {q : Shat} (hq : q ∈ vStab v) :
    q * clabelS v = clabelS v * q := by
  have h := clabelS_cvMul v q
  rw [mem_vStab.1 hq] at h
  calc q * clabelS v = q * (q⁻¹ * clabelS v * q) := by rw [← h]
    _ = clabelS v * q := by group

end Labels

section ThreeA


theorem gLAPPrimeCoreOf_typeThree_eq_bot (hB : BThreeABound) {v w : CVert}
    (hw : w ∈ sphereThree v) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) = ⊥ := by
  have hfacts : cnGroup v w ≤ vStab v ⊓ vStab w ∧
      ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).Normal ∧
      Subgroup.center (cnGroup v w) = ⊥ ∧
      (∀ q ∈ vStab v ⊓ vStab w, (∀ h ∈ cnGroup v w, q * h = h * q) → q = 1) := by
    obtain ⟨θ₀, -, hTT⟩ := native_order_three_common_neighbor_three_transposition_group
    obtain ⟨h1, h2, -, -, -, -, -, -, -, h10, -, -, -, h14, -⟩ := hTT v w hw
    exact ⟨h1, h2, h10, h14⟩
  have hsimple : IsSimpleGroup (cnGroup v w) ∧ Nat.card (cnGroup v w) = 64561751654400 ∧
      commutator (cnGroup v w) = ⊤ := by
    obtain ⟨h1, -, h3, h4, -⟩ := native_three_transposition_group_simple v w hw
    exact ⟨h1, h3, h4⟩
  have h3 : orderOf (clabel v * clabel w) = 3 :=
    ((native_order_three_label_products_and_dihedral_triples v).1 w hw).1
  obtain ⟨hHQ, hHnorm, hcenter, hCQH⟩ := hfacts
  obtain ⟨hsimp, hcardH, hcomm⟩ := hsimple
  have hd2 : clabelS v * clabelS v = 1 := by
    have := pow_orderOf_eq_one (clabelS v)
    rwa [orderOf_clabelS, sq] at this
  have he2 : clabelS w * clabelS w = 1 := by
    have := pow_orderOf_eq_one (clabelS w)
    rwa [orderOf_clabelS, sq] at this
  have hso : orderOf (clabelS v * clabelS w) = 3 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, coe_clabelS, coe_clabelS]
    exact h3
  have hs3 : clabelS v * clabelS w * (clabelS v * clabelS w) * (clabelS v * clabelS w) = 1 := by
    have := pow_orderOf_eq_one (clabelS v * clabelS w)
    rwa [hso, pow_three'] at this
  have hqs : ∀ q ∈ vStab v ⊓ vStab w, q * (clabelS v * clabelS w) =
      clabelS v * clabelS w * q := by
    intro q hq
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).1
    have h2 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).2
    calc q * (clabelS v * clabelS w) = q * clabelS v * clabelS w := by rw [mul_assoc]
      _ = clabelS v * q * clabelS w := by rw [h1]
      _ = clabelS v * (q * clabelS w) := by rw [mul_assoc]
      _ = clabelS v * (clabelS w * q) := by rw [h2]
      _ = clabelS v * clabelS w * q := by rw [mul_assoc]
  have hQC : vStab v ⊓ vStab w ≤ Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat) :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hqs q hq)
  have hsQ : clabelS v * clabelS w ∉ vStab v ⊓ vStab w := by
    intro hsQ
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hsQ).1
    have h2 : clabelS v * clabelS w * (clabelS v * clabelS w) = 1 := by
      have e1 : clabelS v * clabelS w * clabelS v = clabelS v * (clabelS v * clabelS w) := h1
      calc clabelS v * clabelS w * (clabelS v * clabelS w)
          = clabelS v * clabelS w * clabelS v * clabelS w := by simp only [mul_assoc]
        _ = clabelS v * (clabelS v * clabelS w) * clabelS w := by rw [e1]
        _ = 1 := by rw [← mul_assoc, hd2, one_mul, he2]
    have h4 : clabelS v * clabelS w = 1 := by
      calc clabelS v * clabelS w = clabelS v * clabelS w * (clabelS v * clabelS w) *
            (clabelS v * clabelS w) * (clabelS v * clabelS w * (clabelS v * clabelS w))⁻¹ := by
            group
        _ = 1 := by rw [hs3, h2, inv_one, one_mul]
    rw [h4, orderOf_one] at hso
    exact absurd hso (by norm_num)
  have hdecomp := mem_pow_mul_of_card_le (Subgroup.mem_centralizer_singleton_iff.2 rfl) hQC hs3
    hsQ (hB v w hw)
  have hHn : ∀ q ∈ vStab v ⊓ vStab w, ∀ h ∈ cnGroup v w, q * h * q⁻¹ ∈ cnGroup v w := by
    intro q hq h hh
    have := hHnorm.conj_mem ⟨h, hHQ hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨q, hq⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  exact gLAPPrimeCoreOf_eq_bot_of_pow_mul hs3 hqs hHQ hQC hdecomp hHn hsimp hcomm hcenter
    (by rw [hcardH]; norm_num) hCQH

@[expose] def BThreeCensus : Prop :=
  ∀ s : Shat, orderOf s = 3 →
    (∃ v w : CVert, w ∈ sphereThree v ∧ IsConj s (clabelS v * clabelS w)) ∨
      3 ^ 13 ∣ Nat.card (Subgroup.centralizer ({s} : Set Shat))

@[expose] def BThreeCentral : Prop :=
  ∀ s : Shat, orderOf s = 3 → 3 ^ 13 ∣ Nat.card (Subgroup.centralizer ({s} : Set Shat)) →
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set Shat)) = ⊥

theorem oPrimeCoreTrivialAt_Shat_three_of (hA : BThreeABound) (hC : BThreeCensus)
    (hB : BThreeCentral) : OPrimeCoreTrivialAt 3 Shat := by
  intro s hs
  rcases hC s hs with ⟨v, w, hw, hc⟩ | h13
  · obtain ⟨g, hg⟩ := isConj_iff.1 hc
    refine (gLAPPrimeCoreOf_centralizer_conj g s).1 ?_
    rw [hg]
    exact gLAPPrimeCoreOf_typeThree_eq_bot hA hw
  · exact hB s hs h13

theorem oPrimeCoreTrivialAt_B_three_of
    (hA : BThreeABound)
    (hC : BThreeCensus) (hB : BThreeCentral) :
    OPrimeCoreTrivialAt 3 CFSG.Blueprint.NativeSporadic.B :=
  OPrimeCoreTrivialAt.of_mulEquiv (CTIB.iotaEquiv.trans CTIB.sEquiv)
    (oPrimeCoreTrivialAt_Shat_three_of hA hC hB)

end ThreeA

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
