module

public import CFSG.LieType.Steinberg.CentralExt.POmegaOddMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusThree

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort shortElt_eq)
open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed (exists_ne_three single_add_single_apply_of_ne'
  neg_one_zpow_boolSign negPair negPair_swap single_add_single_add_not two_mul_boolSign
  not_isLong_single_two swapPair swapPair_swap not_isLong_add_disjoint)
open CFSG.LieType.Steinberg.CentralExt.SpinTorus (single_add_single_dotProduct)
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

variable {n : ℕ} {K : Type} [Field K]

theorem neg_one_zpow_boolSign_add (s t : Bool) :
    ((-1 : Kˣ) ^ (boolSign s + boolSign t) : Kˣ) = 1 := by
  cases s <;> cases t <;> simp [boolSign]

theorem chi_long_neg_one {k m : Fin n} (hkm : k ≠ m) (γ : Fin n → ℤ) :
    chi (.long k m hkm true true (-1)) γ =
      ((((-1 : Kˣ) ^ (toStdB n γ ⬝ᵥ (Pi.single k 1 + Pi.single m 1)) : Kˣ)) : K) := by
  rfl

theorem neg_one_ne_one_of_two (h2 : (2 : K) ≠ 0) : ((-1 : Kˣ) : K) ≠ 1 := fun h => by
  apply h2
  rw [Units.val_neg, Units.val_one] at h
  linear_combination -h

theorem exists_sep_out (h2 : (2 : K) ≠ 0) {γ δ : Fin n → ℤ} {i j k l : Fin n}
    (hS : ∀ x, x ≠ i → x ≠ j → toStdB n γ x = 0) (hδk : toStdB n δ k = boolSign true ∨
      toStdB n δ k = boolSign false) (hδ0 : ∀ x, x ≠ k → x ≠ l → toStdB n δ x = 0)
    (hki : k ≠ i) (hkj : k ≠ j) (hm : ∃ m : Fin n, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l) :
    ∃ p : TorIdx n K, chi p γ = 1 ∧ chi p δ ≠ 1 := by
  obtain ⟨m, hmi, hmj, hmk, hml⟩ := hm
  refine ⟨.long k m hmk.symm true true (-1), ?_, ?_⟩
  · rw [chi_long_neg_one, dotProduct_comm, SpinTorus.single_add_single_dotProduct, hS k hki hkj,
      hS m hmi hmj]
    simp
  · rw [chi_long_neg_one, dotProduct_comm, SpinTorus.single_add_single_dotProduct, hδ0 m hmk hml, mul_zero,
      add_zero, one_mul]
    rcases hδk with h | h <;> rw [h, neg_one_zpow_boolSign, Units.val_neg, Units.val_one] <;>
      intro h' <;> apply h2 <;> linear_combination -h'

theorem commute_X_of_swap [Finite K] (hK : Nat.card K = 3) {E : Type*} [Group E]
    {π : E →* spinGroup (quadOdd n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {γ δ : Fin n → ℤ}
    (hγ : IsRootLift π γ (X π γ)) (hδ : IsRootLift π δ (X π δ))
    (hγl : IsLong (toStdB n γ)) (hδl : IsLong (toStdB n δ))
    (hl : ¬IsLong (toStdB n γ + toStdB n δ)) (h0 : toStdB n γ + toStdB n δ ≠ 0)
    {g : spinGroup (quadOdd n K)} {a : K} (ha : a * a = 1)
    (h1 : ∀ c, g * rootElt (oddFrame n K).toHypFrame (toStdB n γ) c * g⁻¹ =
      rootElt (oddFrame n K).toHypFrame (toStdB n δ) (a * c))
    (h2 : ∀ c, g * rootElt (oddFrame n K).toHypFrame (toStdB n δ) c * g⁻¹ =
      rootElt (oddFrame n K).toHypFrame (toStdB n γ) (a * c)) (s t : K) :
    X π γ s * X π δ t = X π δ t * X π γ s := by
  have hxγ : ∀ c, SpinOdd.x n K γ c = rootElt (oddFrame n K).toHypFrame (toStdB n γ) c :=
    fun c => elt_of_isLong _ hγl c
  have hxδ : ∀ c, SpinOdd.x n K δ c = rootElt (oddFrame n K).toHypFrame (toStdB n δ) c :=
    fun c => elt_of_isLong _ hδl c
  refine WeylLift.commute_of_swap_lift hK hcen hπ hγ.1 hδ.1 hγ.2.1 hδ.2.1 (fun s t => ?_)
    (g := g) ha (fun c => ?_) (fun c => ?_) s t
  · rw [hxγ, hxδ]
    exact (commute_rootElt (oddFrame n K).toHypFrame hγl hδl h0 hl s t).eq
  · rw [hxγ, hxδ]
    exact h1 c
  · rw [hxγ, hxδ]
    exact h2 c

theorem sep_or_comm_three [Finite K] (hK : Nat.card K = 3) (hn4 : 4 ≤ n) {E : Type*} [Group E]
    {π : E →* spinGroup (quadOdd n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E)
    (hspec : ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, IsRootLift π γ (X π γ)) {γ δ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) (hδ : δ ∈ roots (isFiniteType_cartanB n) ∅)
    (hli : LinIndepPair γ δ) :
    (∃ p : TorIdx n K, chi p γ = 1 ∧ chi p δ ≠ 1) ∨
      ∀ a b, X π γ a * X π δ b * (X π γ a)⁻¹ ∈ ⨆ (ε : Fin n → ℤ)
        (_ : ε ∈ roots (isFiniteType_cartanB n) ∅ ∧
          (ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ)), chevRoot (X π) ε := by
  have hn : 3 ≤ n := by omega
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  have hm1 := neg_one_ne_one_of_two h2
  obtain ⟨hne, hne'⟩ := toStdB_ne_of_linIndepPair hli
  have hbs : ∀ u : Bool, boolSign u = boolSign true ∨ boolSign u = boolSign false := fun u => by
    cases u <;> simp
  rcases isRootVec_of_mem hγ with ⟨i, j, hij, s, t, he⟩ | ⟨i, s, he⟩ <;>
    rcases isRootVec_of_mem hδ with ⟨k, l, hkl, u, v, he'⟩ | ⟨k, u, he'⟩
  ·
    have hS : ∀ x, x ≠ i → x ≠ j → toStdB n γ x = 0 := fun x hxi hxj => by
      rw [he, single_add_single_apply_of_ne' hxi hxj]
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
          simp [Pi.single_apply, hij, hk.1.symm, hl.1.symm, boolSign] at this
          cases s <;> simp at this
        have hcomm := commute_X_of_swap hK hπ hcen (hspec γ hγ) (hspec δ hδ) hγl hδl hnl hn0 ha
          h1 h2'
        intro a' b
        rw [hcomm, mul_inv_cancel_right]
        exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, Or.inl rfl⟩
          (CFSG.LieType.Steinberg.xh_mem_chevRoot δ b))
      · have hl' : l = i ∨ l = j := by tauto
        obtain ⟨m, hmi, hmj, hmk⟩ := exists_ne_three hn4 i j k
        refine Or.inl (exists_sep_out h2 hS (l := l) ?_ (fun x hxk hxl => ?_) hk.1 hk.2
          ⟨m, hmi, hmj, hmk, by rcases hl' with rfl | rfl <;> assumption⟩)
        · rw [he', single_add_single_apply_left hkl]
          exact hbs u
        · rw [he', single_add_single_apply_of_ne' hxk hxl]
    by_cases hl : l ≠ i ∧ l ≠ j
    · have hk' : k = i ∨ k = j := by tauto
      obtain ⟨m, hmi, hmj, hml⟩ := exists_ne_three hn4 i j l
      refine Or.inl (exists_sep_out h2 hS (l := k) ?_ (fun x hxl hxk => ?_) hl.1 hl.2
        ⟨m, hmi, hmj, hml, by rcases hk' with rfl | rfl <;> assumption⟩)
      · rw [he', single_add_single_apply_right hkl]
        exact hbs v
      · rw [he', single_add_single_apply_of_ne' hxk hxl]
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
    have hcomm : ∀ a b, X π γ a * X π δ b = X π δ b * X π γ a := by
      have hcase : (u' = s ∧ v' = !t) ∨ (u' = !s ∧ v' = t) := by
        have hnot : ∀ b c : Bool, b ≠ c → b = !c := fun b c h => by
          cases b <;> cases c <;> simp_all
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
        refine commute_X_of_swap hK hπ hcen (hspec γ hγ) (hspec δ hδ) hγl hδl ?_ ?_ ha h1 h2'
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
        refine commute_X_of_swap hK hπ hcen (hspec γ hγ) (hspec δ hδ) hγl hδl ?_ ?_ ha h1 h2'
        · rw [ehe, ehe', single_add_single_add_not]
          exact not_isLong_single_two (two_mul_boolSign v')
        · rw [ehe, ehe', single_add_single_add_not]
          intro h0
          have := congrFun h0 j
          rw [Pi.single_eq_same, Pi.zero_apply] at this
          rcases two_mul_boolSign v' with h' | h' <;> omega
    intro a b
    rw [hcomm, mul_inv_cancel_right]
    exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, Or.inl rfl⟩
      (CFSG.LieType.Steinberg.xh_mem_chevRoot δ b))
  ·
    have hS : ∀ x, x ≠ i → x ≠ j → toStdB n γ x = 0 := fun x hxi hxj => by
      rw [he, single_add_single_apply_of_ne' hxi hxj]
    by_cases hk : k ≠ i ∧ k ≠ j
    · obtain ⟨m, hmi, hmj, hmk⟩ := exists_ne_three hn4 i j k
      refine Or.inl (exists_sep_out h2 hS (l := k) ?_ (fun x hxk _ => ?_) hk.1 hk.2
        ⟨m, hmi, hmj, hmk, hmk⟩)
      · rw [he', Pi.single_eq_same]
        exact hbs u
      · rw [he', Pi.single_eq_of_ne hxk]
    · left
      refine ⟨.long i j hij true true (-1), ?_, ?_⟩
      · rw [chi_long_neg_one, he, SpinTorus.single_add_single_dotProduct,
          single_add_single_apply_left hij, single_add_single_apply_right hij, mul_one, mul_one,
          neg_one_zpow_boolSign_add, Units.val_one]
      · rw [chi_long_neg_one, he', single_dotProduct]
        have hk' : k = i ∨ k = j := by tauto
        rcases hk' with rfl | rfl
        · rw [single_add_single_apply_left hij, mul_one, neg_one_zpow_boolSign]
          exact hm1
        · rw [single_add_single_apply_right hij, mul_one, neg_one_zpow_boolSign]
          exact hm1
  ·
    have hS : ∀ x, x ≠ i → x ≠ i → toStdB n γ x = 0 := fun x hxi _ => by
      rw [he, Pi.single_eq_of_ne hxi]
    by_cases hk : k ≠ i
    · obtain ⟨m, hmi, hmk, hml⟩ := exists_ne_three hn4 i k l
      refine Or.inl (exists_sep_out h2 hS (l := l) ?_ (fun x hxk hxl => ?_) hk hk
        ⟨m, hmi, hmi, hmk, hml⟩)
      · rw [he', single_add_single_apply_left hkl]
        exact hbs u
      · rw [he', single_add_single_apply_of_ne' hxk hxl]
    · push Not at hk
      subst hk
      obtain ⟨m, hmk, hml, -⟩ := exists_ne_three hn4 k l l
      refine Or.inl (exists_sep_out h2 hS (l := k) ?_ (fun x hxl hxk => ?_) hkl.symm hkl.symm
        ⟨m, hmk, hmk, hml, hmk⟩)
      · rw [he', single_add_single_apply_right hkl]
        exact hbs v
      · rw [he', single_add_single_apply_of_ne' hxk hxl]
  ·
    by_cases hk : k = i
    · exfalso
      subst hk
      cases u <;> cases s
      · exact hne (by rw [he, he'])
      · apply hne'
        rw [he, he', ← Pi.single_neg]
        simp [boolSign]
      · apply hne'
        rw [he, he', ← Pi.single_neg]
        simp [boolSign]
      · exact hne (by rw [he, he'])
    · have hS : ∀ x, x ≠ i → x ≠ i → toStdB n γ x = 0 := fun x hxi _ => by
        rw [he, Pi.single_eq_of_ne hxi]
      obtain ⟨m, hmi, hmk, -⟩ := exists_ne_three hn4 i k k
      refine Or.inl (exists_sep_out h2 hS (l := k) ?_ (fun x hxk _ => ?_) hk hk
        ⟨m, hmi, hmi, hmk, hmk⟩)
      · rw [he', Pi.single_eq_same]
        exact hbs u
      · rw [he', Pi.single_eq_of_ne hxk]

theorem spinOdd_three_exists_section_of_central [Finite K] (hK : Nat.card K = 3) (hn4 : 4 ≤ n)
    {E : Type*} [Group E] {π : E →* spinGroup (quadOdd n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : spinGroup (quadOdd n K) →* E, ∀ g, π (σ g) = g := by
  have hn : 3 ≤ n := by omega
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  have hm1 := neg_one_ne_one_of_two h2
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, IsRootLift π γ (X π γ) := fun γ hγ => by
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
          mul_one, mul_zero, add_zero, neg_one_zpow_boolSign]
        exact hm1
      · obtain ⟨m, hmi, -⟩ := exists_ne_and_ne hn i i
        refine ⟨.long i m hmi.symm true true (-1), ?_⟩
        rw [chi_long_neg_one, he, single_dotProduct, single_add_single_apply_left hmi.symm,
          mul_one, neg_one_zpow_boolSign]
        exact hm1
    exact X_isRootLift (exists_isRootLift hcen hπ h0 hγ hp)
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (oddDatum n K).isFiniteType
    (Dv := (oddDatum n K).divisible) rfl
  refine HalfSpaceLift.exists_section_of_lift' hcen rfl
    (SpinOdd.chevalleyExtras (by omega) O SpinOdd.commC (SpinOdd.commutatorFormula O))
    (SpinOdd.presentationB h2 hn) (X := X π)
    (tor := fun p : TorIdx n K => TorusLift.lift hπ (tor K p))
    (χ := fun p γ => chi p γ) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1)
    (fun p γ hγ c => (hspec γ hγ).2.2 p _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => ?_
  exact sep_or_comm_three hK hn4 hπ hcen hspec hγ hδ hli

theorem pomegaOdd_three_hopfMultiplier [Finite K] (hK : Nat.card K = 3) (hn4 : 4 ≤ n) :
    commutator (StatedProj (StatedOmega (StatedQuadOdd n K))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadOdd n K))) ≃*
        Multiplicative (ZMod 2)) := by
  have hn : 3 ≤ n := by omega
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  set q := spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn)
  obtain ⟨hq, -, hker⟩ := spinToStatedProj_quadOdd h2 hn
  have : Group.IsPerfect (spinGroup (quadOdd n K)) := isPerfect_spinGroup_quadOdd h2 hn
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadOdd n K))) :=
    Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadOdd n K))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => spinOdd_three_exists_section_of_central hK hn4 hπ hcen)
  have hcard := card_ker_spinToStatedProj_quadOdd h2 hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic q.ker := isCyclic_of_prime_card hcard
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv)))⟩

end CFSG.LieType.Steinberg.CentralExt.SpinOddClosed
