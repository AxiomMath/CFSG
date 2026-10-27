module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem10
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem false_of_sumTwo_F4 (h311 : Theorem311Stmt) (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (h : Hyp611 G T M L V n) (hsum : IsSumOfTwo L V (fun W => IsNatModCh5 L W n)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, W', hTW, hLW, hLW', hdisj, hsup, hW, hW'⟩ := h.exists_invariant_sum hsum
  have hV := h.isElemAbelian
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hV ha hb
  have hWV : W ≤ V := hsup ▸ le_sup_left
  have hW'V : W' ≤ V := hsup ▸ le_sup_right
  have hker := h.iff_of_nat hW hW' hWV hW'V
  have hWnat := h.hyp611Nat_of_nat hW hWV hTW
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun _ ht => h.normal (h.T_le ht)
  set q := 2 ^ n with hq
  have hq4 : 4 ≤ q :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hcardV : Nat.card V = (q * q) * (q * q) := by
    have := card_sup_eq_mul hdisj (fun a ha b hb => hVc a (hWV ha) b (hW'V hb))
    rwa [hsup, hW.card_eq, hW'.card_eq] at this

  have hJ : thompsonJk 1 T ≤ ch6Q T V := by
    unfold thompsonJk
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, hAe, hAmax⟩ := hA
    refine le_inf hAT ?_
    intro a haA
    by_contra haC

    obtain ⟨E, hET, hEe, hEc⟩ := H.exists_isElemAbelian_card_pRank T
    have hAE := hAmax E hET hEe
    have hAle := H.card_le_two_pow_pRank hAT hAe
    obtain ⟨k, hk⟩ := H.exists_card_eq_two_pow_of_isElemAbelian hAe
    set m := CFSG.Open.pRank 2 T with hm
    have hkm : k ≤ m := by
      rw [hk] at hAle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hAle
    have hmk : m ≤ k + 1 := by
      have h2 : 2 ^ m ≤ 2 ^ (k + 1) :=
        calc 2 ^ m ≤ 2 ^ 1 * 2 ^ k := by rw [← hEc, ← hk]; exact hAE
          _ = 2 ^ (k + 1) := by ring
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    have hcor : IsElemAbelianCorank T (m - k) A :=
      ⟨hAT, hAe, by rw [hk, ← pow_add]; congr 1; omega⟩
    have hB24 := card_le_relIndex_mul_card_mul_two_pow hV h.le_T hcor

    have hQ : ch6Q T W = ch6Q T V := hWnat.toHyp611.centralizer_eq.trans h.centralizer_eq.symm
    have hAW : A ⊓ Subgroup.centralizer (W : Set G) = A ⊓ Subgroup.centralizer (V : Set G) := by
      ext x
      constructor
      · rintro ⟨hxA, hxW⟩
        have hx : x ∈ ch6Q T W := ⟨hAT hxA, hxW⟩
        rw [hQ] at hx
        exact ⟨hxA, hx.2⟩
      · rintro ⟨hxA, hxV⟩
        have hx : x ∈ ch6Q T V := ⟨hAT hxA, hxV⟩
        rw [← hQ] at hx
        exact ⟨hxA, hx.2⟩
    have hcardA := hWnat.card_le_two_pow_mul hAT hAe
    rw [hAW] at hcardA
    have hrel := card_mul_relIndex_of_le
      (inf_le_left : A ⊓ Subgroup.centralizer (V : Set G) ≤ A)
    have hrelle : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ q := by
      have hpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      rw [hrel, mul_comm]
      exact hcardA

    have hfix : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ q * q := by
      refine le_trans (Subgroup.card_le_of_le (inf_le_inf_left V
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)))) ?_
      exact card_fixed_le_of_sum_ch6 hVc hLW hLW' hdisj hsup hW hW' hker (hTL (hAT haA))
        (hTW (hAT haA)) ⟨1, by simpa using hAe.2 a haA⟩ haC
    have hj : 2 ^ (m - k) ≤ 2 :=
      calc 2 ^ (m - k) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have hle := hB24.trans (Nat.mul_le_mul (Nat.mul_le_mul hrelle hfix) hj)
    rw [hcardV] at hle
    have hq3 : 0 < q * (q * q) := by positivity
    nlinarith

  have hr : rParam V = 1 :=
    ((stmt6_1_3_F4 h331 h432) G T M L V n h).2.resolve_right (not_not.mpr hJ)

  obtain ⟨U, hUV, hUi, hCU⟩ : ∃ U : Subgroup G, U ≤ V ∧ U.relIndex V = 2 ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    by_contra hno
    push Not at hno
    have h2 : (2 : ℕ∞) ≤ rParam V := by
      unfold rParam
      refine le_iInf₂ fun U hU => ?_
      obtain ⟨hUV, hCU⟩ := hU
      have hrel : U.relIndex V ∣ 2 ^ (4 * n) := by
        have : Nat.card V = 2 ^ (4 * n) := by rw [hcardV, hq]; ring
        rw [← this]
        exact Subgroup.relIndex_dvd_card _ _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel
      have hmq : mQuot V U = j := by
        unfold mQuot
        rw [hj, padicValNat.prime_pow]
      rw [hmq]
      by_contra hlt
      push Not at hlt
      have hj2 : j < 2 := by exact_mod_cast hlt
      interval_cases j
      · have hVU : V ≤ U := Subgroup.relIndex_eq_one.mp (by rw [hj]; rfl)
        rw [le_antisymm hUV hVU] at hCU
        exact hCU (Subgroup.centralizer_le_normalizer _)
      · exact hCU (hno U hUV (by rw [hj]; rfl))
    rw [hr] at h2
    exact absurd h2 (by norm_num)

  have hcardU : Nat.card U * 2 = Nat.card V := by
    have := card_mul_relIndex_of_le hUV
    rwa [hUi] at this
  have hinter : ∀ X : Subgroup G, X ≤ V →
      Nat.card X ≤ 2 * Nat.card ↥(U ⊓ X) := by
    intro X hXV
    have h1 := B2F.card_sup_mul_card_inf_of_commute
      (fun a ha b hb => hVc a (hUV ha) b (hXV hb) : ∀ a ∈ U, ∀ b ∈ X, a * b = b * a)
    have h2 : Nat.card ↥(U ⊔ X) ≤ Nat.card V := Subgroup.card_le_of_le (sup_le hUV hXV)
    have hpos : 0 < Nat.card U := Nat.card_pos
    have h3 : Nat.card U * Nat.card X ≤ Nat.card U * (2 * Nat.card ↥(U ⊓ X)) := by
      rw [← h1]
      calc Nat.card ↥(U ⊔ X) * Nat.card ↥(U ⊓ X) ≤ Nat.card V * Nat.card ↥(U ⊓ X) :=
            Nat.mul_le_mul_right _ h2
        _ = Nat.card U * (2 * Nat.card ↥(U ⊓ X)) := by rw [← hcardU]; ring
    exact Nat.le_of_mul_le_mul_left h3 hpos
  have hne : ∀ X : Subgroup G, X ≤ V → Nat.card X = q * q → U ⊓ X ≠ ⊥ := by
    intro X hXV hX h0
    have := hinter X hXV
    rw [h0, Subgroup.card_bot, hX] at this
    nlinarith

  have hCUM : ¬ Subgroup.centralizer (U : Set G) ≤ M := by
    intro hCM
    apply hCU
    intro c hc
    have hcM := hCM hc
    have hcN : ∀ X : Subgroup G, IsNatModCh5 L X n → X ≤ V →
        c ∈ Subgroup.normalizer (X : Set G) := by
      intro X hX hXV
      refine normalizer_le_of_isNatModCh5_ch6 hX h.normal (hne X hXV hX.card_eq) inf_le_right
        ⟨hcM, Subgroup.centralizer_le_normalizer _ ?_⟩
      exact Subgroup.centralizer_le (fun x hx => hx.1) hc
    apply mem_normalizer_of_map_conj_eq_natSum
    rw [← hsup, Subgroup.map_sup, map_conj_eq_of_mem_normalizer_ch6 (hcN W hW hWV),
      map_conj_eq_of_mem_normalizer_ch6 (hcN W' hW' hW'V)]

  have hWe : IsElemAbelian 2 W := B2F.isElemAbelian_mono hWV hV
  have hWne : W ≠ ⊥ := hWnat.toHyp611.ne_bot
  have hNW : Subgroup.normalizer (W : Set G) ≤ M :=
    le_of_isUniqueM_of_le_twoLocal (h.isUniqueM_F4 h432) (sup_le hLW hTW)
      ⟨W, hWne, B2F.isPGroup_of_isElemAbelian hWe, rfl⟩
  have hrW : rParam W ≤ 1 := by
    unfold rParam
    refine (iInf₂_le (U ⊓ W) ⟨inf_le_right, fun hle => hCUM
      ((Subgroup.centralizer_le (fun x hx => hx.1)).trans (hle.trans hNW))⟩).trans ?_
    have hrel : (U ⊓ W).relIndex W ∣ 2 ^ (2 * n) := by
      have : Nat.card W = 2 ^ (2 * n) := by rw [hW.card_eq]; ring
      rw [← this]
      exact Subgroup.relIndex_dvd_card _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel
    have hmq : mQuot W (U ⊓ W) = j := by
      unfold mQuot
      rw [hj, padicValNat.prime_pow]
    rw [hmq]
    have h1 := card_mul_relIndex_of_le (inf_le_right : U ⊓ W ≤ W)
    have h2 := hinter W hWV
    rw [← h1, hj] at h2
    have hpos : 0 < Nat.card ↥(U ⊓ W) := Nat.card_pos
    have h3 : 2 ^ j ≤ 2 := by
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      linarith
    have hj1 : j ≤ 1 := by
      by_contra hj1
      push Not at hj1
      have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
      omega
    exact_mod_cast hj1

  have h2W := Hyp611Nat.two_le_rParam_F4 h311 h432 hWnat
  have := h2W.trans hrW
  exact absurd this (by norm_num)

end Hyp611

end CFSG.Quasithin.H13
