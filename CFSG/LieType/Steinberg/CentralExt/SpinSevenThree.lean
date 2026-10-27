module

public import CFSG.LieType.Steinberg.CentralExt.SpinOddThree
public import CFSG.LieType.Multipliers.O73
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort shortElt_eq)
open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed (single_add_single_apply_of_ne'
  negPair_swap single_add_single_add_not two_mul_boolSign not_isLong_single_two swapPair_swap
  not_isLong_add_disjoint)
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

variable {n : ℕ} {K : Type} [Field K]

@[expose] def IsOrthPair (γ δ : Fin n → ℤ) : Prop :=
  ∃ (i j k : Fin n) (s t u : Bool), i ≠ j ∧ k ≠ i ∧ k ≠ j ∧
    toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) ∧
    toStdB n δ = Pi.single k (boolSign u)

theorem commute_x_of_isOrthPair {γ δ : Fin n → ℤ} (h : IsOrthPair γ δ) (a b : K) :
    SpinOdd.x n K γ a * SpinOdd.x n K δ b = SpinOdd.x n K δ b * SpinOdd.x n K γ a := by
  obtain ⟨i, j, k, s, t, u, hij, hki, hkj, he, he'⟩ := h
  simp only [SpinOdd.x]
  rw [he, he', elt_of_isLong _ (isLong_single_add_single hij s t),
    elt_of_isShort _ (isShort_single k u), rootElt_eq _ hij rfl, shortElt_eq _ rfl]
  exact ((oddFrame n K).commute_longRoot_shortRoot_of_ne hij hki hkj s t u _ _).eq

theorem odd_boolSign (s : Bool) : Odd (boolSign s) := by
  cases s
  · exact ⟨-1, by norm_num [boolSign]⟩
  · exact ⟨0, by norm_num [boolSign]⟩

theorem even_boolSign_add (s t : Bool) : Even (boolSign s + boolSign t) := by
  cases s <;> cases t
  · exact ⟨-1, by norm_num [boolSign]⟩
  · exact ⟨0, by norm_num [boolSign]⟩
  · exact ⟨0, by norm_num [boolSign]⟩
  · exact ⟨1, by norm_num [boolSign]⟩

theorem exists_sep_of_parity (h2 : (2 : K) ≠ 0) {i j : Fin n} (hij : i ≠ j) {γ δ : Fin n → ℤ}
    (hγ : Even (toStdB n γ i + toStdB n γ j)) (hδ : Odd (toStdB n δ i + toStdB n δ j)) :
    ∃ p : TorIdx n K, chi p γ = 1 ∧ chi p δ ≠ 1 := by
  have hdot : ∀ e : Fin n → ℤ, chi (.long i j hij true true (-1)) e =
      (((-1 : Kˣ) ^ (toStdB n e i + toStdB n e j) : Kˣ) : K) := fun e => by
    rw [chi_long_neg_one, dotProduct_comm, SpinTorus.single_add_single_dotProduct, one_mul,
      one_mul]
  refine ⟨.long i j hij true true (-1), ?_, ?_⟩
  · rw [hdot, hγ.neg_one_zpow, Units.val_one]
  · rw [hdot, hδ.neg_one_zpow]
    exact neg_one_ne_one_of_two h2

theorem commute_of_swap_rootLift [Finite K] (hK : Nat.card K = 3) {E : Type*} [Group E]
    {π : E →* spinGroup (quadOdd n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {γ δ : Fin n → ℤ} {Y Y' : K → E}
    (hY : IsRootLift π γ Y) (hY' : IsRootLift π δ Y')
    (hγl : IsLong (toStdB n γ)) (hδl : IsLong (toStdB n δ))
    (hl : ¬IsLong (toStdB n γ + toStdB n δ)) (h0 : toStdB n γ + toStdB n δ ≠ 0)
    {g : spinGroup (quadOdd n K)} {a : K} (ha : a * a = 1)
    (h1 : ∀ c, g * rootElt (oddFrame n K).toHypFrame (toStdB n γ) c * g⁻¹ =
      rootElt (oddFrame n K).toHypFrame (toStdB n δ) (a * c))
    (h2 : ∀ c, g * rootElt (oddFrame n K).toHypFrame (toStdB n δ) c * g⁻¹ =
      rootElt (oddFrame n K).toHypFrame (toStdB n γ) (a * c)) (s t : K) :
    Y s * Y' t = Y' t * Y s := by
  have hxγ : ∀ c, SpinOdd.x n K γ c = rootElt (oddFrame n K).toHypFrame (toStdB n γ) c :=
    fun c => elt_of_isLong _ hγl c
  have hxδ : ∀ c, SpinOdd.x n K δ c = rootElt (oddFrame n K).toHypFrame (toStdB n δ) c :=
    fun c => elt_of_isLong _ hδl c
  refine WeylLift.commute_of_swap_lift hK hcen hπ hY.1 hY'.1 hY.2.1 hY'.2.1 (fun s t => ?_)
    (g := g) ha (fun c => ?_) (fun c => ?_) s t
  · rw [hxγ, hxδ]
    exact (commute_rootElt (oddFrame n K).toHypFrame hγl hδl h0 hl s t).eq
  · rw [hxγ, hxδ]
    exact h1 c
  · rw [hxγ, hxδ]
    exact h2 c

theorem sep_or_comm_orth [Finite K] (hK : Nat.card K = 3) (hn : 3 ≤ n) {E : Type*} [Group E]
    {π : E →* spinGroup (quadOdd n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {Y : (Fin n → ℤ) → K → E}
    (hY : ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, IsRootLift π γ (Y γ))
    (horth : ∀ γ δ, IsOrthPair γ δ → ∀ a b, Y γ a * Y δ b = Y δ b * Y γ a) {γ δ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) (hδ : δ ∈ roots (isFiniteType_cartanB n) ∅)
    (hli : LinIndepPair γ δ) :
    (∃ p : TorIdx n K, chi p γ = 1 ∧ chi p δ ≠ 1) ∨
      ∀ a b, Y γ a * Y δ b * (Y γ a)⁻¹ ∈ ⨆ (ε : Fin n → ℤ)
        (_ : ε ∈ roots (isFiniteType_cartanB n) ∅ ∧
          (ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ)), chevRoot Y ε := by
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  obtain ⟨hne, hne'⟩ := toStdB_ne_of_linIndepPair hli
  have hmem : (∀ a b, Y γ a * Y δ b = Y δ b * Y γ a) → ∀ a b, Y γ a * Y δ b * (Y γ a)⁻¹ ∈
      ⨆ (ε : Fin n → ℤ) (_ : ε ∈ roots (isFiniteType_cartanB n) ∅ ∧
        (ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ)), chevRoot Y ε :=
    fun hc a b => by
      rw [hc, mul_inv_cancel_right]
      exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, Or.inl rfl⟩
        (CFSG.LieType.Steinberg.xh_mem_chevRoot δ b))
  rcases isRootVec_of_mem hγ with ⟨i, j, hij, s, t, he⟩ | ⟨i, s, he⟩ <;>
    rcases isRootVec_of_mem hδ with ⟨k, l, hkl, u, v, he'⟩ | ⟨k, u, he'⟩
  ·
    have hγe : Even (toStdB n γ i + toStdB n γ j) := by
      rw [he, single_add_single_apply_left hij, single_add_single_apply_right hij]
      exact even_boolSign_add s t
    by_cases hk : k ≠ i ∧ k ≠ j
    · by_cases hl : l ≠ i ∧ l ≠ j
      ·
        right
        have hγl : IsLong (toStdB n γ) := by rw [he]; exact isLong_single_add_single hij s t
        have hδl : IsLong (toStdB n δ) := by rw [he']; exact isLong_single_add_single hkl u v
        obtain ⟨a, ha, h1, h2'⟩ := swapPair_swap (oddFrame n K).toHypFrame hij hk.1.symm
          hl.1.symm hk.2.symm hl.2.symm hkl s t u v
        rw [← he, ← he'] at h1 h2'
        have hnl : ¬IsLong (toStdB n γ + toStdB n δ) := by
          rw [he, he']
          exact not_isLong_add_disjoint hij hk.1.symm hl.1.symm hk.2.symm hl.2.symm hkl s t u v
        have hn0 : toStdB n γ + toStdB n δ ≠ 0 := by
          rw [he, he']
          intro h0
          have := congrFun h0 i
          simp [hij, hk.1.symm, hl.1.symm, boolSign] at this
          cases s <;> simp at this
        exact hmem (commute_of_swap_rootLift hK hπ hcen (hY γ hγ) (hY δ hδ) hγl hδl hnl hn0 ha
          h1 h2')
      ·
        left
        refine exists_sep_of_parity h2 hij hγe ?_
        have hl' : l = i ∨ l = j := by tauto
        rw [he']
        rcases hl' with rfl | rfl
        · rw [single_add_single_apply_right hkl,
            single_add_single_apply_of_ne' hk.2.symm hij.symm, add_zero]
          exact odd_boolSign v
        · rw [single_add_single_apply_of_ne' hk.1.symm hij, single_add_single_apply_right hkl,
            zero_add]
          exact odd_boolSign v
    by_cases hl : l ≠ i ∧ l ≠ j
    ·
      left
      refine exists_sep_of_parity h2 hij hγe ?_
      have hk' : k = i ∨ k = j := by tauto
      rw [he']
      rcases hk' with rfl | rfl
      · rw [single_add_single_apply_left hkl,
          single_add_single_apply_of_ne' hij.symm hl.2.symm, add_zero]
        exact odd_boolSign u
      · rw [single_add_single_apply_of_ne' hij hl.1.symm, single_add_single_apply_left hkl,
          zero_add]
        exact odd_boolSign u
    right
    obtain ⟨u', v', he''⟩ : ∃ u' v' : Bool,
        toStdB n δ = Pi.single i (boolSign u') + Pi.single j (boolSign v') := by
      have hk' : k = i ∨ k = j := by tauto
      have hl' : l = i ∨ l = j := by tauto
      rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
      · exact absurd rfl hkl
      · exact ⟨u, v, he'⟩
      · exact ⟨v, u, by rw [he', add_comm]⟩
      · exact absurd rfl hkl
    obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne hn i j
    have hγl : IsLong (toStdB n γ) := by rw [he]; exact isLong_single_add_single hij s t
    have hδl : IsLong (toStdB n δ) := by rw [he'']; exact isLong_single_add_single hij u' v'
    refine hmem ?_
    have hcase : (u' = s ∧ v' = !t) ∨ (u' = !s ∧ v' = t) := by
      have hnot : ∀ b c : Bool, b ≠ c → b = !c := by decide
      by_cases hu : u' = s <;> by_cases hv : v' = t
      · exact absurd (by rw [he'', he, hu, hv]) hne
      · exact Or.inl ⟨hu, hnot _ _ hv⟩
      · exact Or.inr ⟨hnot _ _ hu, hv⟩
      · exfalso
        apply hne'
        rw [he'', he, SpinTorus.neg_single_add_single, hnot _ _ hu, hnot _ _ hv, boolSign_not,
          boolSign_not]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨a, ha, h1, h2'⟩ := negPair_swap (oddFrame n K).toHypFrame hij hmi hmj u' t
      rw [← he, ← he''] at h1 h2'
      refine commute_of_swap_rootLift hK hπ hcen (hY γ hγ) (hY δ hδ) hγl hδl ?_ ?_ ha h1 h2'
      · rw [he, he'', single_add_single_add_not]
        exact not_isLong_single_two (two_mul_boolSign u')
      · rw [he, he'', single_add_single_add_not]
        intro h0
        have := congrFun h0 i
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        rcases two_mul_boolSign u' with h' | h' <;> omega
    · obtain ⟨a, ha, h1, h2'⟩ := negPair_swap (oddFrame n K).toHypFrame hij.symm hmj hmi v' s
      have ehe : toStdB n γ = Pi.single j (boolSign v') + Pi.single i (boolSign s) := by
        rw [he, add_comm]
      have ehe' : toStdB n δ = Pi.single j (boolSign v') + Pi.single i (boolSign (!s)) := by
        rw [he'', add_comm]
      rw [← ehe, ← ehe'] at h1 h2'
      refine commute_of_swap_rootLift hK hπ hcen (hY γ hγ) (hY δ hδ) hγl hδl ?_ ?_ ha h1 h2'
      · rw [ehe, ehe', single_add_single_add_not]
        exact not_isLong_single_two (two_mul_boolSign v')
      · rw [ehe, ehe', single_add_single_add_not]
        intro h0
        have := congrFun h0 j
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        rcases two_mul_boolSign v' with h' | h' <;> omega
  ·
    by_cases hk : k ≠ i ∧ k ≠ j
    · right
      exact hmem (horth γ δ ⟨i, j, k, s, t, u, hij, hk.1, hk.2, he, he'⟩)
    · left
      refine exists_sep_of_parity h2 hij ?_ ?_
      · rw [he, single_add_single_apply_left hij, single_add_single_apply_right hij]
        exact even_boolSign_add s t
      · have hk' : k = i ∨ k = j := by tauto
        rw [he']
        rcases hk' with rfl | rfl
        · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, add_zero]
          exact odd_boolSign u
        · rw [Pi.single_eq_of_ne hij, Pi.single_eq_same, zero_add]
          exact odd_boolSign u
  ·
    by_cases hk : i ≠ k ∧ i ≠ l
    · right
      exact hmem fun a b => (horth δ γ ⟨k, l, i, u, v, s, hkl, hk.1, hk.2, he', he⟩ b a).symm
    · left
      have hk' : i = k ∨ i = l := by tauto
      rcases hk' with rfl | rfl
      · obtain ⟨m, hmi, hml⟩ := exists_ne_and_ne hn i l
        refine exists_sep_of_parity h2 hml.symm ?_ ?_
        · rw [he, Pi.single_eq_of_ne hkl.symm, Pi.single_eq_of_ne hmi, add_zero]
          exact ⟨0, rfl⟩
        · rw [he', single_add_single_apply_right hkl, single_add_single_apply_of_ne' hmi hml,
            add_zero]
          exact odd_boolSign v
      · obtain ⟨m, hmi, hmk⟩ := exists_ne_and_ne hn i k
        refine exists_sep_of_parity h2 hmk.symm ?_ ?_
        · rw [he, Pi.single_eq_of_ne hkl, Pi.single_eq_of_ne hmi, add_zero]
          exact ⟨0, rfl⟩
        · rw [he', single_add_single_apply_left hkl, single_add_single_apply_of_ne' hmk hmi,
            add_zero]
          exact odd_boolSign u
  ·
    have hki : k ≠ i := by
      rintro rfl
      cases u <;> cases s
      · exact hne (by rw [he, he'])
      · apply hne'
        rw [he, he', ← Pi.single_neg]
        simp [boolSign]
      · apply hne'
        rw [he, he', ← Pi.single_neg]
        simp [boolSign]
      · exact hne (by rw [he, he'])
    left
    obtain ⟨m, hmi, hmk⟩ := exists_ne_and_ne hn i k
    refine exists_sep_of_parity h2 hmk.symm ?_ ?_
    · rw [he, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hmi, add_zero]
      exact ⟨0, rfl⟩
    · rw [he', Pi.single_eq_same, Pi.single_eq_of_ne hmk, add_zero]
      exact odd_boolSign u

theorem isRootLift_X_three [Finite K] (hK : Nat.card K = 3) (hn : 3 ≤ n) {E : Type*} [Group E]
    {π : E →* spinGroup (quadOdd n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) : IsRootLift π γ (X π γ) := by
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  have hm1 := neg_one_ne_one_of_two h2
  have h0 : TorusLift.commPairing hcen hπ (x_add (K := K) γ) = 0 := by
    rcases isRootVec_of_mem hγ with h | h
    · exact commPairing_eq_zero_long hcen hπ hn h
    · exact commPairing_eq_zero_short hcen hπ hn (by omega) hγ h
  obtain ⟨p, hp⟩ : ∃ p : TorIdx n K, chi p γ ≠ 1 := by
    rcases isRootVec_of_mem hγ with ⟨i, j, hij, s, t, he⟩ | ⟨i, s, he⟩
    · obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne hn i j
      refine ⟨.long i m hmi.symm true true (-1), ?_⟩
      rw [chi_long_neg_one, he, SpinTorus.single_add_single_dotProduct,
        single_add_single_apply_left hmi.symm, single_add_single_apply_of_ne' hij.symm hmj.symm,
        mul_one, mul_zero, add_zero, SpinPlusClosed.neg_one_zpow_boolSign]
      exact hm1
    · obtain ⟨m, hmi, -⟩ := exists_ne_and_ne hn i i
      refine ⟨.long i m hmi.symm true true (-1), ?_⟩
      rw [chi_long_neg_one, he, single_dotProduct, single_add_single_apply_left hmi.symm,
        mul_one, SpinPlusClosed.neg_one_zpow_boolSign]
      exact hm1
  exact X_isRootLift (exists_isRootLift hcen hπ h0 hγ hp)

theorem exists_section_of_orth [Finite K] (hK : Nat.card K = 3) (hn : 3 ≤ n) {E : Type*}
    [Group E] {π : E →* spinGroup (quadOdd n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {Y : (Fin n → ℤ) → K → E}
    (hY : ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, IsRootLift π γ (Y γ))
    (horth : ∀ γ δ, IsOrthPair γ δ → ∀ a b, Y γ a * Y δ b = Y δ b * Y γ a) :
    ∃ σ : spinGroup (quadOdd n K) →* E, ∀ g, π (σ g) = g := by
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (oddDatum n K).isFiniteType
    (Dv := (oddDatum n K).divisible) rfl
  exact HalfSpaceLift.exists_section_of_lift' hcen rfl
    (SpinOdd.chevalleyExtras (by omega) O SpinOdd.commC (SpinOdd.commutatorFormula O))
    (SpinOdd.presentationB h2 hn) (X := Y)
    (tor := fun p : TorIdx n K => TorusLift.lift hπ (tor K p))
    (χ := fun p γ => chi p γ) (fun γ hγ => (hY γ hγ).1)
    (fun γ hγ => (hY γ hγ).2.1)
    (fun p γ hγ c => (hY γ hγ).2.2 p _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => sep_or_comm_orth hK hn hπ hcen hY horth hγ hδ hli

theorem commutator_mem_zpowers_of_add [Finite K] (hK : Nat.card K = 3) {E : Type*} [Group E]
    {Y Y' : K → E} (hY : ∀ s t, Y (s + t) = Y s * Y t) (hY' : ∀ s t, Y' (s + t) = Y' s * Y' t)
    (hc : ∀ s t, ⁅Y s, Y' t⁆ ∈ Subgroup.center E) :
    ⁅Y 1, Y' 1⁆ ^ 3 = 1 ∧ ∀ s t, ⁅Y s, Y' t⁆ ∈ Subgroup.zpowers ⁅Y 1, Y' 1⁆ := by
  have hY0 : Y 0 = 1 := by
    have h := hY 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hY'0 : Y' 0 = 1 := by
    have h := hY' 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hadd1 : ∀ s s' t, ⁅Y (s + s'), Y' t⁆ = ⁅Y s, Y' t⁆ * ⁅Y s', Y' t⁆ := fun s s' t => by
    rw [hY, TorusLift.commutatorElement_mul_left_of_central (hc s' t)]
  have hadd2 : ∀ s t t', ⁅Y s, Y' (t + t')⁆ = ⁅Y s, Y' t⁆ * ⁅Y s, Y' t'⁆ := fun s t t' => by
    rw [hY', TorusLift.commutatorElement_mul_right_of_central (hc s t')]
  have hc0 : ∀ t, ⁅Y 0, Y' t⁆ = 1 := fun t => by
    rw [hY0, commutatorElement_one_left]
  have hc0' : ∀ s, ⁅Y s, Y' 0⁆ = 1 := fun s => by
    rw [hY'0, commutatorElement_one_right]
  have hneg1 : ∀ t, ⁅Y (-1), Y' t⁆ = ⁅Y 1, Y' t⁆⁻¹ := fun t => by
    have h := hadd1 1 (-1) t
    rw [add_neg_cancel, hc0] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hneg2 : ∀ s, ⁅Y s, Y' (-1)⁆ = ⁅Y s, Y' 1⁆⁻¹ := fun s => by
    have h := hadd2 s 1 (-1)
    rw [add_neg_cancel, hc0'] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  refine ⟨?_, fun s t => ?_⟩
  · rw [pow_three, ← mul_assoc, ← hadd1, ← hadd1, show (1 : K) + 1 + 1 = 3 by norm_num,
      WeylLift.three_eq_zero hK, hc0]
  · set c := ⁅Y 1, Y' 1⁆
    have hc1 : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
    rcases WeylLift.eq_zero_or_one_or_neg_one hK s with rfl | rfl | rfl <;>
      rcases WeylLift.eq_zero_or_one_or_neg_one hK t with rfl | rfl | rfl <;>
      (try simp only [hc0, hc0', hneg1, hneg2, inv_inv]) <;>
      first
        | exact Subgroup.one_mem _
        | exact hc1
        | exact Subgroup.inv_mem _ hc1

theorem commutator_mem_of_reflection {E : Type*} [Group E] {π : E →* spinGroup (quadOdd n K)}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    {Y : (Fin n → ℤ) → K → E}
    (hY : ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, ∀ c, π (Y γ c) = SpinOdd.x n K γ c)
    {Z : Subgroup E} (hZ : Z ≤ Subgroup.center E) (k : Fin n) {γ δ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) (hδ : δ ∈ roots (isFiniteType_cartanB n) ∅)
    (h : ∀ a b, ⁅Y γ a, Y δ b⁆ ∈ Z) (a b : K) :
    ⁅Y (reflection (cartanB n) k γ) a, Y (reflection (cartanB n) k δ) b⁆ ∈ Z := by
  obtain ⟨ε, hε, hγw⟩ := SpinOdd.weylB_conj_x (K := K) k hγ
  obtain ⟨ε', hε', hδw⟩ := SpinOdd.weylB_conj_x (K := K) k hδ
  have hrγ : reflection (cartanB n) k γ ∈ roots (isFiniteType_cartanB n) ∅ :=
    (SpinOdd.Φ n K).refl_mem k γ hγ
  have hrδ : reflection (cartanB n) k δ ∈ roots (isFiniteType_cartanB n) ∅ :=
    (SpinOdd.Φ n K).refl_mem k δ hδ
  have hsq : ∀ e : ℤ, (e = 1 ∨ e = -1) → (e : K) * e = 1 := fun e he => by
    rcases he with rfl | rfl <;> simp
  set ñ := TorusLift.lift hπ (weylB K k)
  have key : ⁅Y (reflection (cartanB n) k γ) a, Y (reflection (cartanB n) k δ) b⁆ =
      ñ * ⁅Y γ (ε * a), Y δ (ε' * b)⁆ * ñ⁻¹ := by
    have e1 : ñ * ⁅Y γ (ε * a), Y δ (ε' * b)⁆ * ñ⁻¹ =
        ⁅ñ * Y γ (ε * a) * ñ⁻¹, ñ * Y δ (ε' * b) * ñ⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    refine TorusLift.commutatorElement_eq_of_map_eq hcen ?_ ?_
    · rw [hY _ hrγ, map_mul, map_mul, map_inv, TorusLift.map_lift, hY γ hγ, hγw, ← mul_assoc,
        hsq ε hε, one_mul]
    · rw [hY _ hrδ, map_mul, map_mul, map_inv, TorusLift.map_lift, hY δ hδ, hδw, ← mul_assoc,
        hsq ε' hε', one_mul]
  rw [key, (Subgroup.mem_center_iff.1 (hZ (h _ _))) ñ, mul_inv_cancel_right]
  exact h _ _

theorem isOrthPair_induction {P : (Fin 3 → ℤ) → (Fin 3 → ℤ) → Prop}
    (hbase : P (ofStdB 3 (Pi.single 0 1 + Pi.single 1 1)) (ofStdB 3 (Pi.single 2 1)))
    (hstep : ∀ (k : Fin 3) (γ δ : Fin 3 → ℤ), P γ δ →
      P (reflection (cartanB 3) k γ) (reflection (cartanB 3) k δ))
    {γ δ : Fin 3 → ℤ} (h : IsOrthPair γ δ) : P γ δ := by
  set Q : (Fin 3 → ℤ) → (Fin 3 → ℤ) → Prop := fun e e' => P (ofStdB 3 e) (ofStdB 3 e')
    with hQ
  have hrefl : ∀ (k : Fin 3) (e : Fin 3 → ℤ),
      reflection (cartanB 3) k (ofStdB 3 e) = ofStdB 3 (stdReflB 3 k e) := fun k e => by
    rw [← toStdB_eq_iff, toStdB_reflection, toStdB_ofStdB]
  have hr : ∀ (k : Fin 3) {e e' f f' : Fin 3 → ℤ}, stdReflB 3 k e = f → stdReflB 3 k e' = f' →
      Q e e' → Q f f' := fun k e e' f f' hf hf' hq => by
    have := hstep k _ _ hq
    rw [hrefl, hrefl, hf, hf'] at this
    exact this
  set v : Fin 3 → Bool → Fin 3 → ℤ := fun i s => Pi.single i (boolSign s) with hv
  have hU : ∀ s t u, Q (v 0 s + v 1 t) (v 2 u) → Q (v 0 s + v 1 t) (v 2 (!u)) :=
    fun s t u => hr 2 (by cases s <;> cases t <;> decide) (by cases u <;> decide)
  have hT : ∀ s t u, Q (v 0 s + v 1 t) (v 2 u) → Q (v 0 s + v 1 (!t)) (v 2 u) :=
    fun s t u hq => hr 1 (e := v 0 s + v 2 (!t)) (e' := v 1 u)
      (by cases s <;> cases t <;> decide) (by cases u <;> decide)
      (hr 2 (e := v 0 s + v 2 t) (e' := v 1 u) (by cases s <;> cases t <;> decide)
        (by cases u <;> decide)
        (hr 1 (by cases s <;> cases t <;> decide) (by cases u <;> decide) hq))
  have hS : ∀ s t u, Q (v 0 s + v 1 t) (v 2 u) → Q (v 0 t + v 1 s) (v 2 u) :=
    fun s t u => hr 0 (by cases s <;> cases t <;> decide) (by cases u <;> decide)
  have hb : Q (v 0 true + v 1 true) (v 2 true) := hbase
  have h1 : ∀ t, Q (v 0 true + v 1 t) (v 2 true) := fun t => by
    cases t
    · exact hT _ _ _ hb
    · exact hb
  have h2 : ∀ s t, Q (v 0 s + v 1 t) (v 2 true) := fun s t => by
    have h' := hS _ _ _ (h1 s)
    cases t
    · exact hT _ _ _ h'
    · exact h'
  have h012 : ∀ s t u, Q (v 0 s + v 1 t) (v 2 u) := fun s t u => by
    cases u
    · exact hU _ _ _ (h2 s t)
    · exact h2 s t
  have h021 : ∀ s t u, Q (v 0 s + v 2 t) (v 1 u) := fun s t u =>
    hr 1 (by cases s <;> cases t <;> decide) (by cases u <;> decide) (h012 s t u)
  have h120 : ∀ s t u, Q (v 1 s + v 2 t) (v 0 u) := fun s t u =>
    hr 0 (by cases s <;> cases t <;> decide) (by cases u <;> decide) (h021 s t u)
  obtain ⟨i, j, k, s, t, u, hij, hki, hkj, he, he'⟩ := h
  have hγ : γ = ofStdB 3 (v i s + v j t) := by rw [← toStdB_eq_iff, he]
  have hδ : δ = ofStdB 3 (v k u) := by rw [← toStdB_eq_iff, he']
  rw [hγ, hδ]
  change Q (v i s + v j t) (v k u)
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | exact absurd rfl hij
      | exact absurd rfl hki
      | exact absurd rfl hkj
      | exact h012 s t u
      | exact h021 s t u
      | exact h120 s t u
      | (rw [add_comm]; exact h012 t s u)
      | (rw [add_comm]; exact h021 t s u)
      | (rw [add_comm]; exact h120 t s u)

theorem mem_roots_of_isOrthPair {γ δ : Fin n → ℤ} (h : IsOrthPair γ δ) :
    γ ∈ roots (isFiniteType_cartanB n) ∅ ∧ δ ∈ roots (isFiniteType_cartanB n) ∅ := by
  obtain ⟨i, j, k, s, t, u, hij, -, -, he, he'⟩ := h
  exact ⟨SpinOdd.mem_roots_iff.2 (Or.inl ⟨i, j, hij, s, t, he⟩),
    SpinOdd.mem_roots_iff.2 (Or.inr ⟨k, u, he'⟩)⟩

theorem spinSeven_three_ker_le_zpowers [Finite K] (hK : Nat.card K = 3) {E : Type*} [Group E]
    [Group.IsPerfect E] {π : E →* spinGroup (quadOdd 3 K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ c : E, c ^ 3 = 1 ∧ π.ker ≤ Subgroup.zpowers c := by
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanB 3) ∅, IsRootLift π γ (X π γ) :=
    fun γ hγ => isRootLift_X_three hK le_rfl hπ hcen hγ
  set γ₀ := ofStdB 3 (Pi.single 0 1 + Pi.single 1 1) with hγ₀
  set δ₀ := ofStdB 3 (Pi.single 2 1) with hδ₀
  have h₀ : IsOrthPair γ₀ δ₀ :=
    ⟨0, 1, 2, true, true, true, by decide, by decide, by decide,
      by rw [hγ₀, toStdB_ofStdB]; rfl, by rw [hδ₀, toStdB_ofStdB]; rfl⟩
  have hker : ∀ γ δ, IsOrthPair γ δ → ∀ a b, ⁅X π γ a, X π δ b⁆ ∈ π.ker := fun γ δ h a b => by
    obtain ⟨hγ, hδ⟩ := mem_roots_of_isOrthPair h
    rw [MonoidHom.mem_ker, map_commutatorElement, (hspec γ hγ).2.1, (hspec δ hδ).2.1,
      commutatorElement_eq_one_iff_mul_comm]
    exact commute_x_of_isOrthPair h a b
  obtain ⟨hγ₀r, hδ₀r⟩ := mem_roots_of_isOrthPair h₀
  obtain ⟨hc3, hc⟩ := commutator_mem_zpowers_of_add hK (hspec γ₀ hγ₀r).1 (hspec δ₀ hδ₀r).1
    fun s t => hcen (hker γ₀ δ₀ h₀ s t)
  set c := ⁅X π γ₀ 1, X π δ₀ 1⁆ with hcdef
  set Z := Subgroup.zpowers c with hZdef
  have hZk : Z ≤ π.ker := Subgroup.zpowers_le.2 (hker γ₀ δ₀ h₀ 1 1)
  have hZc : Z ≤ Subgroup.center E := hZk.trans hcen
  have hall : ∀ γ δ, IsOrthPair γ δ → ∀ a b, ⁅X π γ a, X π δ b⁆ ∈ Z := fun γ δ h =>
    (isOrthPair_induction (P := fun γ δ => γ ∈ roots (isFiniteType_cartanB 3) ∅ ∧
        δ ∈ roots (isFiniteType_cartanB 3) ∅ ∧ ∀ a b, ⁅X π γ a, X π δ b⁆ ∈ Z)
      ⟨hγ₀r, hδ₀r, hc⟩
      (fun k γ δ ⟨hγ, hδ, h⟩ => ⟨(SpinOdd.Φ 3 K).refl_mem k γ hγ, (SpinOdd.Φ 3 K).refl_mem k δ hδ,
        commutator_mem_of_reflection hπ hcen (fun γ hγ => (hspec γ hγ).2.1) hZc k hγ hδ h⟩)
      h).2.2
  have : Z.Normal := Subgroup.normal_of_le_center hZc
  set π' : E ⧸ Z →* spinGroup (quadOdd 3 K) := QuotientGroup.lift Z π hZk with hπ'def
  have hπ'mk : ∀ e : E, π' e = π e := fun e => rfl
  have hπ' : Function.Surjective π' := fun g => by
    obtain ⟨e, he⟩ := hπ g
    exact ⟨e, by rw [hπ'mk, he]⟩
  have hcen' : π'.ker ≤ Subgroup.center (E ⧸ Z) := fun x hx => by
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    have he : e ∈ Subgroup.center E := hcen (by rw [MonoidHom.mem_ker, ← hπ'mk]; exact hx)
    refine Subgroup.mem_center_iff.2 fun y => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 he) y]
  set Y : (Fin 3 → ℤ) → K → E ⧸ Z := fun γ a => ((X π γ a : E) : E ⧸ Z) with hYdef
  have hY : ∀ γ ∈ roots (isFiniteType_cartanB 3) ∅, IsRootLift π' γ (Y γ) := fun γ hγ => by
    refine ⟨fun s t => ?_, fun s => ?_, fun p e he s => ?_⟩
    · simp only [hYdef, (hspec γ hγ).1, QuotientGroup.mk_mul]
    · rw [hYdef, hπ'mk, (hspec γ hγ).2.1]
    · obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective e
      have he' : π e = tor K p := by rw [← hπ'mk]; exact he
      simp only [hYdef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
        (hspec γ hγ).2.2 p e he' s]
  have horth : ∀ γ δ, IsOrthPair γ δ → ∀ a b, Y γ a * Y δ b = Y δ b * Y γ a := fun γ δ h a b => by
    have h1 : (QuotientGroup.mk' Z) ⁅X π γ a, X π δ b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hall γ δ h a b)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  obtain ⟨σ, hσ⟩ := exists_section_of_orth hK le_rfl hπ' hcen' hY horth
  have : Group.IsPerfect (E ⧸ Z) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective Z)
  have hbot := SL2Closed.ker_eq_bot_of_section π' hcen' σ hσ
  refine ⟨c, hc3, fun e he => ?_⟩
  have h1 : (e : E ⧸ Z) ∈ π'.ker := by
    rw [MonoidHom.mem_ker, hπ'mk]
    exact he
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem card_ker_le_three_of_spinSeven [Finite K] (hK : Nat.card K = 3) {E : Type*} [Group E]
    [Group.IsPerfect E] {π : E →* spinGroup (quadOdd 3 K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : Finite π.ker ∧ Nat.card π.ker ≤ 3 := by
  obtain ⟨c, hc3, hle⟩ := spinSeven_three_ker_le_zpowers hK hπ hcen
  have hfo : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hc3⟩
  have hord : orderOf c ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hc3
  have : Finite (Subgroup.zpowers c) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact hfo.orderOf_pos.ne')
  refine ⟨Finite.of_injective _ (Subgroup.inclusion_injective hle), ?_⟩
  calc Nat.card π.ker ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hle
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 3 := hord

theorem spinOdd_exists_section_of_coprime
    [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {E : Type*} [Group E] [Finite E]
    {π : E →* spinGroup (quadOdd n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : p.Coprime (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadOdd n K) →* E, ∀ g, π (σ g) = g := by
  have hC' : ¬ p ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hC
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (oddDatum n K).isFiniteType
    (Dv := (oddDatum n K).divisible) rfl
  have hE := SpinOdd.chevalleyExtras (by omega) O SpinOdd.commC (SpinOdd.commutatorFormula O)
  exact (existsUnique_section_of_sl2_lift (SpinOdd.isCTGroupDatum h2 hn)
    (oddDatum_steinbergExtras h2) hE.param hE.rankOne hπ hcen hC' fun ρ => by
      obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC' ρ
      exact ⟨ρ', fun g => congrArg (· g) hρ'⟩).exists

theorem lieModel_pomegaOdd_three_three [Finite K] (hK : Nat.card K = 3) :
    CFSG.Blueprint.LieModel (StatedProj (StatedOmega (StatedQuadOdd 3 K))) .POmegaOdd 3 3 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩, K, inferInstance,
    inferInstance, by rw [hK, pow_one], ⟨MulEquiv.refl _⟩⟩

open CFSG.RankThree.PerfectCover in
theorem pomegaOdd_three_three_hopfMultiplier
    [Finite K]
    (hK : Nat.card K = 3) :
    commutator (StatedProj (StatedOmega (StatedQuadOdd 3 K))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadOdd 3 K))) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 3)) := by
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  have hn : 3 ≤ 3 := le_rfl
  set X := StatedProj (StatedOmega (StatedQuadOdd 3 K)) with hXdef
  set q := spinToStatedProj (quadOdd 3 K) (range_spinMatrix_quadOdd h2 hn)
  obtain ⟨hq, -, hker⟩ := spinToStatedProj_quadOdd h2 hn
  have : Group.IsPerfect (spinGroup (quadOdd 3 K)) := isPerfect_spinGroup_quadOdd h2 hn
  have hperf : Group.IsPerfect X := Group.IsPerfect.ofSurjective hq
  have : Finite (spinGroup (quadOdd 3 K)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Finite X := Finite.of_surjective q hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have : Finite (HopfCover X) := finite_hopfCover hperf
  have : Group.IsPerfect (HopfCover X) := hopfCover_isPerfect
  set l := hopfLift q hq hker.le with hl
  have hls : Function.Surjective l := hopfLift_surjective q hq hker.le
  have hlM : l.ker ≤ hopfMultiplier X := fun u hu => by
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [← comp_hopfLift q hq hker.le, MonoidHom.comp_apply, ← hl, hu, map_one]
  have hlc : l.ker ≤ Subgroup.center (HopfCover X) := hlM.trans hopfMultiplier_le_center
  obtain ⟨-, hl3⟩ := card_ker_le_three_of_spinSeven hK hls hlc
  have hq2 := card_ker_spinToStatedProj_quadOdd h2 hn
  have hcardM : Nat.card (hopfMultiplier X) = 2 * Nat.card l.ker := by
    set f := l.domRestrict (hopfMultiplier X)
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
      MonoidHom.domRestrict_range, hl, map_hopfMultiplier_hopfLift, hq2,
      MonoidHom.ker_domRestrict, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlM).toEquiv]
      at h1
    exact h1
  obtain ⟨E₃, _, _, p, ⟨⟨hp, hpker⟩, hpperf⟩, hp3⟩ :=
    CFSG.LieType.Multipliers.O73.exists_perfectCentralExtension_card_ker_three X
      (lieModel_pomegaOdd_three_three hK)
  have : Group.IsPerfect E₃ := ⟨hpperf⟩
  have h3 : 3 ∣ Nat.card (hopfMultiplier X) := by
    have h := Subgroup.card_map_dvd (hopfMultiplier X) (hopfLift p hp hpker)
    rwa [map_hopfMultiplier_hopfLift, hp3] at h
  have hpos : 0 < Nat.card (hopfMultiplier X) := Nat.card_pos
  have h6 : Nat.card (hopfMultiplier X) = 6 := by
    obtain ⟨k, hk⟩ := h3
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := hopfMultiplier X) 2 (by rw [h6]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := hopfMultiplier X) 3 (by rw [h6]; norm_num)
  have hab : Commute a b :=
    Subtype.ext ((Subgroup.mem_center_iff.1 (hopfMultiplier_le_center b.2)) a)
  have hcyc : IsCyclic (hopfMultiplier X) := by
    refine isCyclic_of_orderOf_eq_card (a * b) ?_
    rw [hab.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hb]; norm_num), ha, hb, h6]
  exact ⟨(hopfMultiplierEquivGriess X).trans ((zmodCyclicMulEquiv hcyc).symm.trans
    ((AddEquiv.toMultiplicative ((ZMod.ringEquivCongr (h6.trans (by norm_num : 6 = 2 * 3))).trans
      (ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 3))).toAddEquiv).trans
      (MulEquiv.prodMultiplicative _ _)))⟩

end CFSG.LieType.Steinberg.CentralExt.SpinOddClosed
