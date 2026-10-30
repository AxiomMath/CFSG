module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUCos
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUCover
public import Certificates.Certificate27827
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUOut

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.EvenSporadicStandard.M24Std.CU43

section Counting

@[expose] def vIx : Fin 4 → ℕ := ![0, 2, 5, 7]

theorem vIx_lt (i : Fin 4) : vIx i < 8 := by fin_cases i <;> simp [vIx]

theorem vIx_inV (i : Fin 4) : InV (vIx i) := by fin_cases i <;> simp [vIx, InV]

theorem vIx_inj {i i' : Fin 4} (h : vIx i = vIx i') : i = i' := by
  fin_cases i <;> fin_cases i' <;> simp_all [vIx]

@[expose] noncomputable def ksEquiv : (Fin 4 × ↥P) ≃ ↥U43ExtStar :=
  Equiv.ofBijective
    (fun p => ⟨(p.2 : Equiv.Perm (Fin 820)) * tP (vIx p.1), p.2, p.2.2, vIx p.1, vIx_lt _,
      vIx_inV _, rfl⟩)
    ⟨by
      rintro ⟨i, g⟩ ⟨i', g'⟩ h
      have h1 : (g : Equiv.Perm (Fin 820)) * tP (vIx i) = g' * tP (vIx i') := congrArg Subtype.val h
      have hii : vIx i = vIx i' := by
        by_contra hne
        apply tP_mul_inv_not_mem (vIx_lt i) (vIx_lt i') hne
        have e : tP (vIx i) * (tP (vIx i'))⁻¹ = (g : Equiv.Perm (Fin 820))⁻¹ * g' := by
          calc tP (vIx i) * (tP (vIx i'))⁻¹
              = (g : Equiv.Perm (Fin 820))⁻¹ * ((g : Equiv.Perm (Fin 820)) * tP (vIx i)) *
                (tP (vIx i'))⁻¹ := by group
            _ = (g : Equiv.Perm (Fin 820))⁻¹ * (g' * tP (vIx i')) * (tP (vIx i'))⁻¹ := by rw [h1]
            _ = _ := by group
        rw [e]
        exact P.mul_mem (P.inv_mem g.2) g'.2
      obtain rfl := vIx_inj hii
      have : (g : Equiv.Perm (Fin 820)) = g' := mul_right_cancel h1
      exact Prod.ext rfl (Subtype.ext this),
    by
      rintro ⟨x, g, hg, k, hk, hkV, rfl⟩
      have : ∃ i : Fin 4, vIx i = k := by
        rcases hkV with rfl | rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
      obtain ⟨i, rfl⟩ := this
      exact ⟨(i, ⟨g, hg⟩), rfl⟩⟩

theorem card_Ks_pred (Pr : Equiv.Perm (Fin 820) → Prop) :
    Nat.card {x : ↥U43ExtStar // Pr x} =
      Nat.card {g : ↥P // Pr (g * tP 0)} + Nat.card {g : ↥P // Pr (g * tP 2)} +
        Nat.card {g : ↥P // Pr (g * tP 5)} + Nat.card {g : ↥P // Pr (g * tP 7)} := by
  let q : Fin 4 × ↥P → Prop := fun p => Pr ((ksEquiv p : ↥U43ExtStar) : Equiv.Perm (Fin 820))
  have e1 : {x : ↥U43ExtStar // Pr x} ≃ {p : Fin 4 × ↥P // q p} :=
    Equiv.subtypeEquiv ksEquiv.symm (fun x => by simp [q])
  have e2 : {p : Fin 4 × ↥P // q p} ≃ Σ i : Fin 4, {g : ↥P // Pr (g * tP (vIx i))} :=
    Equiv.subtypeProdEquivSigmaSubtype (fun (i : Fin 4) (g : ↥P) =>
      Pr ((ksEquiv (i, g) : ↥U43ExtStar) : Equiv.Perm (Fin 820)))
  rw [Nat.card_congr (e1.trans e2), Nat.card_sigma, Fin.sum_univ_four]
  simp [vIx]

end Counting

section Specs

theorem base_lt : ∀ b ∈ baseArr.toList, b < 820 := by
  have hQb : Q.base.toList.map Fin.val = baseArr.toList := rfl
  rw [← hQb]
  intro b hb
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb
  exact y.2

theorem orderOf_eq_eight_iff {α : Type*} [Group α] (x : α) :
    orderOf x = 8 ↔ x ^ 8 = 1 ∧ x ^ 4 ≠ 1 := by
  constructor
  · intro h
    exact ⟨by rw [← h]; exact pow_orderOf_eq_one x,
      pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h]; norm_num)⟩
  · rintro ⟨h8, h4⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using h4) (by simpa using h8)
    simpa using this

theorem ord8W_iff {k : ℕ} (hk : k < 8) (hV : InV k) {w : List (Array ℕ)}
    {g : Equiv.Perm (Fin 820)} (hw : RepW 820 w g) (hg : g ∈ P) :
    ord8W baseArr.toList (tArr k) w = true ↔ orderOf (g * tP k) = 8 := by
  have hx : g * tP k ∈ U43ExtStar := ⟨g, hg, k, hk, hV, rfl⟩
  have hv : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
  have key : ∀ e : ℕ, (g * tP k) ^ e ∈ P →
      (fixB baseArr.toList (tArr k :: w) e = true ↔ (g * tP k) ^ e = 1) := by
    intro e he
    rw [fixB_iff base_lt hv e]
    constructor
    · exact baseFaithful_P _ he
    · intro h y _
      rw [h]
      rfl
  unfold ord8W
  rw [orderOf_eq_eight_iff]
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨h8', h4'⟩ := h
    refine ⟨(key 8 (pow_eight_mem_P hx)).1 h8', fun h4'' => ?_⟩
    rw [(key 4 (pow_four_mem_P hx)).2 h4''] at h4'
    exact absurd h4' (by decide)
  · rintro ⟨h8', h4'⟩
    rw [Bool.and_eq_true]
    refine ⟨(key 8 (pow_eight_mem_P hx)).2 h8', ?_⟩
    cases hb : fixB baseArr.toList (tArr k :: w) 4
    · rfl
    · exact absurd ((key 4 (pow_four_mem_P hx)).1 hb) h4'

theorem card_ord8_coset {k : ℕ} (hk : k < 8) (hV : InV k) :
    Nat.card {g : ↥P // orderOf ((g : Equiv.Perm (Fin 820)) * tP k) = 8} =
      countW (ord8W baseArr.toList (tArr k)) blocks [] := by
  classical
  exact card_eq_countW_P (f := ord8W baseArr.toList (tArr k))
    (Pr := fun g => orderOf (g * tP k) = 8) fun w g hw hg => ord8W_iff hk hV hw hg

theorem card_cent_Ks {r : Array ℕ} {R : Equiv.Perm (Fin 820)} (hr : Rep 820 r R) :
    Nat.card {x : ↥U43ExtStar // (x : Equiv.Perm (Fin 820)) * R = R * x} = centKs r := by
  classical
  rw [card_Ks_pred (fun x => x * R = R * x)]
  have h : ∀ k, k < 8 → Nat.card {g : ↥P // (g : Equiv.Perm (Fin 820)) * tP k * R =
      R * ((g : Equiv.Perm (Fin 820)) * tP k)} =
      countW (commW (tArr k) [r]) blocks [] := by
    intro k hk
    rw [card_eq_countW_P (f := commW (tArr k) [r])
      (Pr := fun g => g * tP k * R = R * (g * tP k))]
    intro w g hw _
    have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
    simp only [commW, List.all_cons, List.all_nil, Bool.and_true]
    exact allLt_comm_iff hH hr
  rw [h 0 (by norm_num), h 2 (by norm_num), h 5 (by norm_num), h 7 (by norm_num)]
  rw [centKs, vIxL, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_nil, Nat.zero_add]

end Specs

section Classes

theorem ks8_facts : ∀ j < 8,
    isInvA 820 ks8Reps[j]! (invCand 820 ks8Reps[j]!) = true ∧
    inP (compA 820 ks8Reps[j]! (invCand 820 (tArr ks8Coset[j]!))) = true ∧
    eqA 820 (powA 820 ks8Reps[j]! 8) (idA 820) = true ∧
    eqA 820 (powA 820 ks8Reps[j]! 4) (idA 820) = false ∧
    centKs ks8Reps[j]! = ks8Cent[j]! := by
  have h := Certificates.certificate27827.1
  simp only [ks8Check, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  intro j hj
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h j hj
  exact ⟨h1, h2, h3, h4, h5⟩

theorem ks8_counts_facts : ∀ i < 4,
    countW (ord8W baseArr.toList (tArr vIxL[i]!)) blocks [] = ks8Count[i]! := by
  have h := Certificates.certificate27827.2
  simp only [ks8Counts, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

@[expose] noncomputable def ks8Perm (j : ℕ) : Equiv.Perm (Fin 820) := permOfArr 820 ks8Reps[j]!

theorem rep_ks8 {j : ℕ} (hj : j < 8) : Rep 820 ks8Reps[j]! (ks8Perm j) :=
  (rep_permOfArr (ks8_facts j hj).1).1

theorem ks8_coset_lt : ∀ j < 8, ks8Coset[j]! < 8 ∧ InV ks8Coset[j]! := by decide +kernel

theorem ks8_inCos {j : ℕ} (hj : j < 8) : InCos ks8Coset[j]! (ks8Perm j) :=
  (inP_iff (rep_compA (rep_ks8 hj) (rep_tArr_inv (ks8_coset_lt j hj).1))).1
    (ks8_facts j hj).2.1

theorem ks8_mem {j : ℕ} (hj : j < 8) : ks8Perm j ∈ U43ExtStar :=
  mem_Ks_iff.2 ⟨_, (ks8_coset_lt j hj).1, (ks8_coset_lt j hj).2, ks8_inCos hj⟩

theorem ks8_orderOf {j : ℕ} (hj : j < 8) : orderOf (ks8Perm j) = 8 := by
  obtain ⟨-, -, h3, h4, -⟩ := ks8_facts j hj
  rw [orderOf_eq_eight_iff]
  refine ⟨(eqA_iff (rep_powA (rep_ks8 hj) 8) rep_idA).1 h3, fun h => ?_⟩
  have := (eqA_iff (rep_powA (rep_ks8 hj) 4) rep_idA).2 h
  rw [this] at h4
  exact Bool.noConfusion h4

@[expose] noncomputable def ks8Elt (j : ℕ) (hj : j < 8) : ↥U43ExtStar := ⟨ks8Perm j, ks8_mem hj⟩

theorem card_centralizer_ks8 {j : ℕ} (hj : j < 8) :
    Nat.card ↥(centralizer ({ks8Elt j hj} : Set ↥U43ExtStar)) = ks8Cent[j]! := by
  have h := card_cent_Ks (rep_ks8 hj)
  rw [(ks8_facts j hj).2.2.2.2] at h
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

@[expose] def Ord8Cos (k : ℕ) : Set ↥U43ExtStar :=
  {x | orderOf (x : Equiv.Perm (Fin 820)) = 8 ∧ InCos k x}

theorem card_Ord8Cos {k : ℕ} (hk : k < 8) (hV : InV k) :
    Nat.card ↥(Ord8Cos k) = countW (ord8W baseArr.toList (tArr k)) blocks [] := by
  rw [← card_ord8_coset hk hV]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨(x.1 : Equiv.Perm (Fin 820)) * (tP k)⁻¹, x.2.2⟩, by
        have := x.2.1
        simpa [mul_assoc] using this⟩
      invFun := fun g => ⟨⟨(g.1 : Equiv.Perm (Fin 820)) * tP k, g.1.1,
        g.1.2, k, hk, hV, rfl⟩, by simpa using g.2, inCos_mul_tP g.1.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simp
      right_inv := fun g => by
        apply Subtype.ext
        apply Subtype.ext
        simp }

theorem cover_ks8_gen {n : ℕ} (js : Fin n → ℕ) {k : ℕ} (hk : k < 8) (hV : InV k) {N : ℕ}
    (hN : countW (ord8W baseArr.toList (tArr k)) blocks [] = N)
    (hjs : ∀ a, js a < 8 ∧ ks8Coset[js a]! = k)
    (hdist : ∀ a b, ks8Cent[js a]! = ks8Cent[js b]! → a = b)
    (hsum : ∑ a, 13063680 / ks8Cent[js a]! = N) :
    ∀ x ∈ U43ExtStar, orderOf x = 8 → InCos k x →
      ∃ a, ∃ c ∈ U43ExtStar, x = c * ks8Perm (js a) * c⁻¹ := by
  classical
  have hcardKs : Nat.card ↥U43ExtStar = 13063680 := by
    rw [card_U43ExtStar, card_P]
  let r : Fin n → ↥U43ExtStar := fun a => ks8Elt (js a) (hjs a).1
  have hcr : ∀ a, Nat.card ↥(centralizer ({r a} : Set ↥U43ExtStar)) = ks8Cent[js a]! :=
    fun a => card_centralizer_ks8 (hjs a).1
  have key := cover_by_classes (G := ↥U43ExtStar) (Ord8Cos k)
    (fun c g hg => by
      refine ⟨?_, ?_⟩
      · have h1 : ((c * g * c⁻¹ : ↥U43ExtStar) : Equiv.Perm (Fin 820)) =
          (MulAut.conj (c : Equiv.Perm (Fin 820))) (g : Equiv.Perm (Fin 820)) := rfl
        rw [h1, MulEquiv.orderOf_eq]
        exact hg.1
      · exact inCos_conj hk hV c.2 hg.2)
    r (fun a => ⟨by
        show orderOf (ks8Perm (js a)) = 8
        exact ks8_orderOf (hjs a).1, by
        show InCos k (ks8Perm (js a))
        have := ks8_inCos (hjs a).1
        rwa [(hjs a).2] at this⟩)
    (fun x => Nat.card ↥(centralizer ({x} : Set ↥U43ExtStar)))
    (fun c g => card_centralizer_conj c g)
    (fun a b hab => hdist a b (by rw [← hcr a, ← hcr b]; exact hab))
    (by
      rw [card_Ord8Cos hk hV, hN, hcardKs]
      rw [← hsum]
      exact Finset.sum_congr rfl fun a _ => by rw [hcr a])
  intro x hx h8 hxk
  obtain ⟨a, c, hc⟩ := key ⟨x, hx⟩ ⟨h8, hxk⟩
  refine ⟨a, c, c.2, ?_⟩
  exact congrArg Subtype.val hc

theorem cover_ks8_coset_zero :
    ∀ x ∈ U43ExtStar, orderOf x = 8 → InCos 0 x →
      ∃ a : Fin 1, ∃ c ∈ U43ExtStar, x = c * ks8Perm (![0] a) * c⁻¹ :=
  cover_ks8_gen (![0] : Fin 1 → ℕ) (by norm_num) (by decide)
    (N := 408240) (by simpa [vIxL, ks8Count] using ks8_counts_facts 0 (by norm_num))
    (by decide) (by decide) (by decide)

theorem cover_ks8_coset_two :
    ∀ x ∈ U43ExtStar, orderOf x = 8 → InCos 2 x →
      ∃ a : Fin 1, ∃ c ∈ U43ExtStar, x = c * ks8Perm (![1] a) * c⁻¹ :=
  cover_ks8_gen (![1] : Fin 1 → ℕ) (by norm_num) (by decide)
    (N := 408240) (by simpa [vIxL, ks8Count] using ks8_counts_facts 1 (by norm_num))
    (by decide) (by decide) (by decide)

theorem cover_ks8_coset_five :
    ∀ x ∈ U43ExtStar, orderOf x = 8 → InCos 5 x →
      ∃ a : Fin 3, ∃ c ∈ U43ExtStar, x = c * ks8Perm (![2, 3, 4] a) * c⁻¹ :=
  cover_ks8_gen (![2, 3, 4] : Fin 3 → ℕ) (by norm_num) (by decide)
    (N := 1088640) (by simpa [vIxL, ks8Count] using ks8_counts_facts 2 (by norm_num))
    (by decide) (by decide) (by decide)

theorem cover_ks8_coset_seven :
    ∀ x ∈ U43ExtStar, orderOf x = 8 → InCos 7 x →
      ∃ a : Fin 3, ∃ c ∈ U43ExtStar, x = c * ks8Perm (![5, 6, 7] a) * c⁻¹ :=
  cover_ks8_gen (![5, 6, 7] : Fin 3 → ℕ) (by norm_num) (by decide)
    (N := 1088640) (by simpa [vIxL, ks8Count] using ks8_counts_facts 3 (by norm_num))
    (by decide) (by decide) (by decide)

theorem ks8_classes {y : Equiv.Perm (Fin 820)} (hy : y ∈ U43ExtStar) (h8 : orderOf y = 8) :
    ∃ j, ∃ hj : j < 8, InCos ks8Coset[j]! y ∧ ∃ c ∈ U43ExtStar, y = c * ks8Perm j * c⁻¹ ∧
      Nat.card ↥(centralizer ({⟨y, hy⟩} : Set ↥U43ExtStar)) = ks8Cent[j]! := by
  obtain ⟨k, hk, hV, hyk⟩ := mem_Ks_iff.1 hy
  have hfin : ∀ (j : ℕ) (hj : j < 8), ks8Coset[j]! = k → ∀ c ∈ U43ExtStar,
      y = c * ks8Perm j * c⁻¹ → ∃ j, ∃ hj : j < 8, InCos ks8Coset[j]! y ∧
        ∃ c ∈ U43ExtStar, y = c * ks8Perm j * c⁻¹ ∧
          Nat.card ↥(centralizer ({⟨y, hy⟩} : Set ↥U43ExtStar)) = ks8Cent[j]! := by
    intro j hj hjk c hc hyc
    refine ⟨j, hj, by rw [hjk]; exact hyk, c, hc, hyc, ?_⟩
    have h1 : (⟨y, hy⟩ : ↥U43ExtStar) = ⟨c, hc⟩ * ks8Elt j hj * ⟨c, hc⟩⁻¹ := Subtype.ext hyc
    rw [h1, card_centralizer_conj, card_centralizer_ks8 hj]
  rcases hV with rfl | rfl | rfl | rfl
  · obtain ⟨a, c, hc, hyc⟩ := cover_ks8_coset_zero y hy h8 hyk
    exact hfin _ (by fin_cases a; decide) (by fin_cases a; decide) c hc hyc
  · obtain ⟨a, c, hc, hyc⟩ := cover_ks8_coset_two y hy h8 hyk
    exact hfin _ (by fin_cases a; decide) (by fin_cases a; decide) c hc hyc
  · obtain ⟨a, c, hc, hyc⟩ := cover_ks8_coset_five y hy h8 hyk
    exact hfin _ (by fin_cases a <;> decide) (by fin_cases a <;> decide) c hc hyc
  · obtain ⟨a, c, hc, hyc⟩ := cover_ks8_coset_seven y hy h8 hyk
    exact hfin _ (by fin_cases a <;> decide) (by fin_cases a <;> decide) c hc hyc

theorem ks8Cent_not_dvd_128 : ∀ j < 8, ¬ 128 ∣ ks8Cent[j]! := by decide +kernel

theorem ks8Cent_not_dvd_64 : ∀ j < 8, ks8Coset[j]! = 2 → ¬ 64 ∣ ks8Cent[j]! := by decide +kernel

theorem ks_cent8_two_le {y : Equiv.Perm (Fin 820)} (hy : y ∈ U43ExtStar) (h8 : orderOf y = 8)
    {R : Subgroup (Equiv.Perm (Fin 820))} (hR : R ≤ U43ExtStar)
    (hc : ∀ r ∈ R, r * y = y * r) (hR2 : IsPGroup 2 R) :
    Nat.card ↥R ≤ 64 ∧ (InCos 2 y → Nat.card ↥R ≤ 32) := by
  obtain ⟨j, hj, hcos, c, hc', hyc, hcent⟩ := ks8_classes hy h8
  have hdvd : Nat.card ↥R ∣ ks8Cent[j]! := by
    rw [← hcent]
    have hle : R.subgroupOf U43ExtStar ≤ centralizer ({⟨y, hy⟩} : Set ↥U43ExtStar) := by
      intro r hr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hc r (Subgroup.mem_subgroupOf.1 hr))
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hR2
  rw [ha] at hdvd ⊢
  refine ⟨?_, fun h2 => ?_⟩
  · by_contra hlt
    push Not at hlt
    have h7 : 7 ≤ a := by
      by_contra h
      push Not at h
      have : 2 ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ks8Cent_not_dvd_128 j hj (dvd_trans (Nat.pow_dvd_pow 2 h7) hdvd)
  · by_contra hlt
    push Not at hlt
    have hjc : ks8Coset[j]! = 2 := inCos_unique (ks8_coset_lt j hj).1 (by norm_num) hcos h2
    have h6 : 6 ≤ a := by
      by_contra h
      push Not at h
      have : 2 ^ a ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ks8Cent_not_dvd_64 j hj hjc (dvd_trans (Nat.pow_dvd_pow 2 h6) hdvd)

end Classes

end CFSG.EvenSporadicStandard.Fin76b.U16
