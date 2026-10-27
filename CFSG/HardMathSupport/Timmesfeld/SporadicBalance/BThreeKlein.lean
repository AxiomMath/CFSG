module

public import CFSG.Monster.Existence.MilestoneInputs
public import Certificates.Certificate13623
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23SylowBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G]

theorem orderOf_dvd_card_of_mem {H : Subgroup G} {y : G} (hy : y ∈ H) :
    orderOf y ∣ Nat.card H := by
  have := orderOf_dvd_natCard (⟨y, hy⟩ : H)
  rwa [Subgroup.orderOf_mk] at this

theorem commute_of_conj {y x : G} (h : y * x * y⁻¹ = x) : y * x = x * y := by
  calc y * x = y * x * y⁻¹ * y := by group
    _ = x * y := by rw [h]

end Generic

section Baby


theorem babyInv_zero_of_dvd {x : B} (hx : orderOf x = 2)
    (h11 : 11 ∣ Nat.card (Subgroup.centralizer ({x} : Set B)))
    (h13 : 13 ∣ Nat.card (Subgroup.centralizer ({x} : Set B))) : BabyInv 0 x := by
  obtain ⟨k, hk⟩ := babyTableIII.1 x hx
  rw [hk.2] at h11 h13
  fin_cases k
  · exact hk
  · exact absurd h13 (by norm_num [babyCentOrder])
  · exact absurd h11 (by norm_num [babyCentOrder])
  · exact absurd h11 (by norm_num [babyCentOrder])

theorem babyInv_one_mul_of_dvd {r s : B} (hr : BabyInv 0 r) (hs : BabyInv 0 s) (hne : s ≠ r)
    (hrs : r * s = s * r) (h11 : 11 ∣ Nat.card (Subgroup.centralizer ({r * s} : Set B))) :
    BabyInv 1 (r * s) := by
  obtain ⟨k, hk⟩ := (babyTableIV r hr).1 s hs hne
  have hr2 : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hr.1, sq] at this
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs.1, sq] at this
  have h2 : (r * s) ^ 2 = 1 := by
    rw [sq]
    calc r * s * (r * s) = r * (s * r) * s := by group
      _ = r * (r * s) * s := by rw [hrs]
      _ = (r * r) * (s * s) := by group
      _ = 1 := by rw [hr2, hs2, one_mul]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  fin_cases k
  · exact hk
  · exfalso
    have hc : Nat.card (Subgroup.centralizer ({r * s} : Set B)) = babyCentOrder 3 := hk.2
    rw [hc] at h11
    exact absurd h11 (by norm_num [babyCentOrder])
  · exfalso
    have ho : orderOf (r * s) = 3 := hk
    rw [ho] at hdvd
    exact absurd hdvd (by norm_num)
  · exfalso
    have ho : orderOf (r * s) = 4 := hk.1
    rw [ho] at hdvd
    exact absurd hdvd (by norm_num)

end Baby

section Fi23


@[expose] noncomputable def kleinY (k : ℕ) : CFSG.Sporadic.Fi23.J := ((kleinWords[k]!).map (pairG gs)).prod

@[expose] noncomputable def kleinZJ : CFSG.Sporadic.Fi23.J := (kleinZ.map (pairG gs)).prod

@[expose] noncomputable def kleinD (i : ℕ) : CFSG.Sporadic.Fi23.J := conjPt kleinPts[i]!

theorem klein_parts :
    (∀ i < 3, ∀ j < 3, i ≠ j → treeAct orb.par orb.lab orb.alpha orb.beta (dTable orb)
      (genTables orb (-2)) kleinPts[i]! kleinPts[j]! = kleinPts[j]!) ∧
    (∀ k < 5, ∀ z ∈ kleinWords[k]!, z < letters.size) ∧
    (∀ k < 5, baseFixed (powT 31671 kleinOrders[k]! (qLettersT letters kleinWords[k]!)) = true ∧
      baseFixed (qLettersT letters kleinWords[k]!) = false ∧
      ∀ p ∈ kleinFix[k]!, ap (qLettersT letters kleinWords[k]!) p = p) ∧
    (∀ z ∈ kleinZ, z < letters.size) ∧
    (∀ i < 3, ap (qLettersT letters kleinZ) kleinPts[i]! = kleinPts[i]!) := by
  have h := Certificates.certificate13623
  unfold kleinOK kleinCheckL at h
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_eq_true, Bool.or_eq_true, List.all_eq_true,
    Array.all_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hc, -⟩, hw⟩, hy⟩, hz⟩, hzf⟩ := h
  refine ⟨fun i hi j hj hij => ?_, fun k hk z hz' => ?_, fun k hk => ?_,
    fun z hz' => hz z hz', fun i hi => hzf i (Nat.zero_le _) hi⟩
  · rcases hc i (Nat.zero_le _) hi j (Nat.zero_le _) hj with h1 | h1
    · exact absurd h1 hij
    · exact h1
  · have hk' : k < kleinWords.size := by simpa [kleinWords] using hk
    rw [getElem!_pos kleinWords k hk'] at hz'
    exact hw k hk' z hz'
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hy k (Nat.zero_le _) hk
    exact ⟨h1, h2, h3⟩

theorem kleinPts_lt {i : ℕ} (hi : i < 3) : kleinPts[i]! < 31671 := by
  interval_cases i <;> decide

theorem rep_kleinY {k : ℕ} (hk : k < 5) :
    Rep 31671 (qLettersT letters kleinWords[k]!) (kleinY k) :=
  Fi23Sylow.rep_qLettersT _ (klein_parts.2.1 k hk)

theorem conj_conjPt_of_fix {y : CFSG.Sporadic.Fi23.J} {T : Table} (hT : Rep 31671 T y) {p : ℕ} (hp : p < 31671)
    (h : ap T p = p) : y * conjPt p * y⁻¹ = conjPt p := by
  rw [hT p hp] at h
  exact (idx_eq_iff hp hp).1 h

theorem kleinD_commute {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    kleinD i * kleinD j = kleinD j * kleinD i := by
  by_cases hij : i = j
  · rw [hij]
  have h := klein_parts.1 i hi j hj hij
  have hD : Rep 31671 (dTable orb) d := Rep.powT (by norm_num) (rep_dWordTab dWord) 7
  have hB : Rep 31671 (genTables orb (-2)) b⁻¹ := by
    have := rep_gen (-2)
    simpa [genG] using this
  have hspec := treeAct_spec rep_alpha rep_beta hB hD a_inv conjPt conjPt_eq
  rw [hspec _ _ (kleinPts_lt hj)] at h
  have hc := (idx_eq_iff (kleinPts_lt hj) (kleinPts_lt hj)).1 h
  unfold kleinD
  calc conjPt kleinPts[i]! * conjPt kleinPts[j]!
      = conjPt kleinPts[i]! * conjPt kleinPts[j]! * (conjPt kleinPts[i]!)⁻¹ *
          conjPt kleinPts[i]! := by group
    _ = conjPt kleinPts[j]! * conjPt kleinPts[i]! := by rw [hc]

theorem kleinD_ne {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) : kleinD i ≠ kleinD j := by
  intro h
  have hlt : ∀ {k : ℕ}, k < 3 → kleinPts[k]! < orb.keys.size := fun hk => by
    rw [orb_size]
    exact kleinPts_lt hk
  have := conjPt_inj (hlt hi) (hlt hj) h
  interval_cases i <;> interval_cases j <;> simp_all [kleinPts]

theorem isConj_d_kleinD {i : ℕ} (hi : i < 3) : IsConj d (kleinD i) :=
  (isConj_d_iff _).2 ⟨⟨kleinPts[i]!, kleinPts_lt hi⟩, rfl⟩

theorem orderOf_kleinY {k : ℕ} (hk : k < 5) : orderOf (kleinY k) = kleinOrders[k]! := by
  obtain ⟨h1, h2, -⟩ := klein_parts.2.2.1 k hk
  have hrep := rep_kleinY hk
  have hpow : kleinY k ^ kleinOrders[k]! = 1 := by
    have hr := Rep.powT (by norm_num) hrep kleinOrders[k]!
    refine Fi23Sylow.eq_of_base fun t ht => ?_
    unfold baseFixed at h1
    rw [allIn_eq_true] at h1
    have := h1 t (Nat.zero_le _) ht
    rw [beq_iff_eq, hr t (by omega)] at this
    rw [this, idx_one]
  have hne : kleinY k ≠ 1 := by
    intro h
    unfold baseFixed at h2
    have h2' : ¬ allIn 0 6 (fun t => ap (qLettersT letters kleinWords[k]!) t == t) = true := by
      rw [h2]
      exact Bool.false_ne_true
    apply h2'
    rw [allIn_eq_true]
    intro t _ ht
    rw [beq_iff_eq, hrep t (by omega), h, idx_one]
  have hp : (kleinOrders[k]!).Prime := by
    interval_cases k <;> norm_num [kleinOrders]
  have : Fact (kleinOrders[k]!).Prime := ⟨hp⟩
  exact orderOf_eq_prime hpow hne

theorem kleinY_fix {k : ℕ} (hk : k < 5) {p : ℕ} (hp : p ∈ kleinFix[k]!) :
    kleinY k * conjPt p * (kleinY k)⁻¹ = conjPt p := by
  have hlt : p < 31671 := by
    interval_cases k <;> simp [kleinFix] at hp <;> omega
  exact conj_conjPt_of_fix (rep_kleinY hk) hlt ((klein_parts.2.2.1 k hk).2.2 p hp)

theorem kleinZJ_fix {i : ℕ} (hi : i < 3) :
    kleinZJ * kleinD i * kleinZJ⁻¹ = kleinD i :=
  conj_conjPt_of_fix (Fi23Sylow.rep_qLettersT _ klein_parts.2.2.2.1) (kleinPts_lt hi)
    (klein_parts.2.2.2.2 i hi)

theorem orderOf_dvd_card_centralizer_map (φ : CFSG.Sporadic.Fi23.J →* B)
    {x y : CFSG.Sporadic.Fi23.J} (hxy : y * x = x * y) :
    orderOf (φ y) ∣ Nat.card (Subgroup.centralizer ({φ x} : Set B)) := by
  refine orderOf_dvd_card_of_mem (Subgroup.mem_centralizer_singleton_iff.2 ?_)
  rw [← map_mul, ← map_mul, hxy]

end Fi23

section Main


theorem commute_of_conj_J {y x : CFSG.Sporadic.Fi23.J} (h : y * x * y⁻¹ = x) : y * x = x * y := by
  calc y * x = y * x * y⁻¹ * y := by group
    _ = x * y := by rw [h]

theorem kleinY_commute_kleinD {k i : ℕ} (hk : k < 5)
    (hp : kleinPts[i]! ∈ kleinFix[k]!) : kleinY k * kleinD i = kleinD i * kleinY k := by
  have h := kleinY_fix hk hp
  unfold kleinD
  calc kleinY k * conjPt kleinPts[i]! = kleinY k * conjPt kleinPts[i]! * (kleinY k)⁻¹ * kleinY k :=
        by group
    _ = conjPt kleinPts[i]! * kleinY k := by rw [h]


theorem babyInv_zero_map_d (φ : CFSG.Sporadic.Fi23.J →* B) (hφ : Function.Injective φ) :
    BabyInv 0 (φ d) := by
  have h2 : orderOf (φ d) = 2 := by
    have e : orderOf (φ d) = orderOf d := by
      with_reducible_and_instances exact orderOf_injective φ hφ d
    rw [e]
    exact orderOf_d
  have hf0 : kleinY 0 * conjPt 0 * (kleinY 0)⁻¹ = conjPt 0 :=
    kleinY_fix (by norm_num) (by decide)
  have hf1 : kleinY 1 * conjPt 0 * (kleinY 1)⁻¹ = conjPt 0 :=
    kleinY_fix (by norm_num) (by decide)
  rw [conjPt_zero] at hf0 hf1
  have h11 := orderOf_dvd_card_centralizer_map φ (commute_of_conj_J hf0)
  have h13 := orderOf_dvd_card_centralizer_map φ (commute_of_conj_J hf1)
  have e0 : orderOf (φ (kleinY 0)) = orderOf (kleinY 0) := by
    with_reducible_and_instances exact orderOf_injective φ hφ _
  have e1 : orderOf (φ (kleinY 1)) = orderOf (kleinY 1) := by
    with_reducible_and_instances exact orderOf_injective φ hφ _
  rw [e0, orderOf_kleinY (by norm_num)] at h11
  rw [e1, orderOf_kleinY (by norm_num)] at h13
  exact babyInv_zero_of_dvd h2 h11 h13

theorem babyInv_zero_map_of_isConj_d (φ : CFSG.Sporadic.Fi23.J →* B)
    (hφ : Function.Injective φ) {x : CFSG.Sporadic.Fi23.J} (hx : IsConj d x) :
    BabyInv 0 (φ x) :=
  (babyInv_zero_map_d φ hφ).of_isConj (φ.map_isConj hx)

theorem babyInv_zero_map_kleinD (φ : CFSG.Sporadic.Fi23.J →* B) (hφ : Function.Injective φ)
    {i : ℕ} (hi : i < 3) : BabyInv 0 (φ (kleinD i)) :=
  babyInv_zero_map_of_isConj_d φ hφ (isConj_d_kleinD hi)

theorem babyInv_one_map_kleinD_mul (φ : CFSG.Sporadic.Fi23.J →* B) (hφ : Function.Injective φ)
    {i j k : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) (hk : k < 5) (hk11 : kleinOrders[k]! = 11)
    (hpi : kleinPts[i]! ∈ kleinFix[k]!) (hpj : kleinPts[j]! ∈ kleinFix[k]!) :
    BabyInv 1 (φ (kleinD i) * φ (kleinD j)) := by
  have hne : φ (kleinD j) ≠ φ (kleinD i) := fun h => kleinD_ne hj hi (Ne.symm hij) (hφ h)
  have hc : φ (kleinD i) * φ (kleinD j) = φ (kleinD j) * φ (kleinD i) := by
    rw [← map_mul, ← map_mul, kleinD_commute hi hj]
  have hy : kleinY k * (kleinD i * kleinD j) = kleinD i * kleinD j * kleinY k := by
    rw [← mul_assoc, kleinY_commute_kleinD hk hpi, mul_assoc, kleinY_commute_kleinD hk hpj,
      mul_assoc]
  have h11 := orderOf_dvd_card_centralizer_map φ hy
  have e : orderOf (φ (kleinY k)) = orderOf (kleinY k) := by
    with_reducible_and_instances exact orderOf_injective φ hφ _
  rw [e, orderOf_kleinY hk, hk11, map_mul] at h11
  exact babyInv_one_mul_of_dvd (babyInv_zero_map_kleinD φ hφ hi) (babyInv_zero_map_kleinD φ hφ hj)
    hne hc h11

theorem exists_twoB_four_of_fixes (φ : CFSG.Sporadic.Fi23.J →* B) (hφ : Function.Injective φ)
    {s : CFSG.Sporadic.Fi23.J}
    (hs : ∀ i < 3, s * kleinD i * s⁻¹ = kleinD i) :
    ∃ a b : B, a ∈ Subgroup.centralizer ({φ s} : Set B) ∧
      b ∈ Subgroup.centralizer ({φ s} : Set B) ∧ BabyInv 1 a ∧ BabyInv 1 b ∧ BabyInv 1 (a * b) := by
  have hcs : ∀ i < 3, φ (kleinD i) * φ s = φ s * φ (kleinD i) := fun i hi => by
    rw [← map_mul, ← map_mul, (commute_of_conj_J (hs i hi)).symm]
  have hmem : ∀ i < 3, ∀ j < 3, φ (kleinD i) * φ (kleinD j) ∈
      Subgroup.centralizer ({φ s} : Set B) := fun i hi j hj => by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc φ (kleinD i) * φ (kleinD j) * φ s = φ (kleinD i) * (φ (kleinD j) * φ s) := by group
      _ = φ (kleinD i) * (φ s * φ (kleinD j)) := by rw [hcs j hj]
      _ = (φ (kleinD i) * φ s) * φ (kleinD j) := by group
      _ = (φ s * φ (kleinD i)) * φ (kleinD j) := by rw [hcs i hi]
      _ = φ s * (φ (kleinD i) * φ (kleinD j)) := by group
  have hdd : kleinD 1 * kleinD 1 = 1 := by
    have h1 := pow_orderOf_eq_one (kleinD 1)
    have h2 : orderOf (kleinD 1) = 2 := orderOf_of_isConj (isConj_d_kleinD (by norm_num))
    rw [h2, sq] at h1
    exact h1
  have hd1 : φ (kleinD 1) * φ (kleinD 1) = 1 := by
    rw [← map_mul, hdd, map_one]
  refine ⟨φ (kleinD 0) * φ (kleinD 1), φ (kleinD 1) * φ (kleinD 2), hmem 0 (by norm_num) 1
    (by norm_num), hmem 1 (by norm_num) 2 (by norm_num), ?_, ?_, ?_⟩
  · exact babyInv_one_map_kleinD_mul φ hφ (k := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide) (by decide) (by decide)
  · exact babyInv_one_map_kleinD_mul φ hφ (k := 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide) (by decide) (by decide)
  · have e : φ (kleinD 0) * φ (kleinD 1) * (φ (kleinD 1) * φ (kleinD 2)) =
        φ (kleinD 0) * φ (kleinD 2) := by
      calc φ (kleinD 0) * φ (kleinD 1) * (φ (kleinD 1) * φ (kleinD 2))
          = φ (kleinD 0) * (φ (kleinD 1) * φ (kleinD 1)) * φ (kleinD 2) := by group
        _ = φ (kleinD 0) * φ (kleinD 2) := by rw [hd1, mul_one]
    rw [e]
    exact babyInv_one_map_kleinD_mul φ hφ (k := 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide) (by decide) (by decide)

theorem exists_twoB_four_kleinZ (φ : CFSG.Sporadic.Fi23.J →* B) (hφ : Function.Injective φ) :
    ∃ a b : B, a ∈ Subgroup.centralizer ({φ kleinZJ} : Set B) ∧
      b ∈ Subgroup.centralizer ({φ kleinZJ} : Set B) ∧ BabyInv 1 a ∧ BabyInv 1 b ∧
        BabyInv 1 (a * b) :=
  exists_twoB_four_of_fixes φ hφ fun _ hi => kleinZJ_fix hi

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
