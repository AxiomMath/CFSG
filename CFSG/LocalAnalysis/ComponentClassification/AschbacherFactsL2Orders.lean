module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Triple
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter

theorem pgl2_orderOf_le (F : Type) [Field F] [Finite F] (x : PGL2 F) :
    orderOf x ≤ Nat.card F + 1 := by
  classical
  let : Fintype (PSL2ProjectiveLine F) := Fintype.ofFinite _
  have hX : Nat.card (PSL2ProjectiveLine F) = Nat.card F + 1 :=
    Projectivization.card_of_finrank_two F _ (by simp)
  let : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have huniq : ∀ y : PGL2 F, ∀ a b c : PSL2ProjectiveLine F, a ≠ b → a ≠ c → b ≠ c →
      y • a = a → y • b = b → y • c = c → y = 1 := by
    intro y a b c hab hac hbc ha hb hc
    obtain ⟨g, -, hg⟩ := pgl2_sharply_three_transitive F a b c a b c hab hac hbc hab hac hbc
    rw [hg y ⟨ha, hb, hc⟩, hg 1 ⟨one_smul _ a, one_smul _ b, one_smul _ c⟩]
  have hiter : ∀ (a : PSL2ProjectiveLine F) (n : ℕ), (x • ·)^[n] a = x ^ n • a := by
    intro a n
    rw [smul_iterate]
  have hper : ∀ a : PSL2ProjectiveLine F, 0 < Function.minimalPeriod (x • ·) a := by
    intro a
    apply Function.IsPeriodicPt.minimalPeriod_pos (orderOf_pos x)
    change (x • ·)^[orderOf x] a = a
    rw [hiter, pow_orderOf_eq_one, one_smul]
  by_cases h3 : ∃ a : PSL2ProjectiveLine F, 3 ≤ Function.minimalPeriod (x • ·) a
  · obtain ⟨a, ha⟩ := h3
    set k := Function.minimalPeriod (x • ·) a with hk
    have hka : x ^ k • a = a := by
      rw [← hiter]
      exact Function.iterate_minimalPeriod
    have hfix : ∀ j : ℕ, x ^ k • (x ^ j • a) = x ^ j • a := by
      intro j
      rw [smul_smul, ← pow_add, add_comm, pow_add, mul_smul, hka]
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (x • ·)) (x := a)
    have hne : ∀ i j : ℕ, i < k → j < k → i ≠ j → x ^ i • a ≠ x ^ j • a := by
      intro i j hi hj hij h
      apply hij
      apply hinj (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj)
      simp only [hiter]
      exact h
    have hxk : x ^ k = 1 := by
      apply huniq _ (x ^ 0 • a) (x ^ 1 • a) (x ^ 2 • a) (hne 0 1 (by omega) (by omega) (by omega))
        (hne 0 2 (by omega) (by omega) (by omega)) (hne 1 2 (by omega) (by omega) (by omega))
        (hfix 0) (hfix 1) (hfix 2)
    have hkle : k ≤ Nat.card (PSL2ProjectiveLine F) := by
      rw [Nat.card_eq_fintype_card]
      exact Function.minimalPeriod_le_card
    calc orderOf x ≤ k := orderOf_le_of_pow_eq_one (hper a) hxk
      _ ≤ Nat.card F + 1 := hX ▸ hkle
  · push Not at h3
    have h2 : ∀ a : PSL2ProjectiveLine F, x ^ 2 • a = a := by
      intro a
      have hpa := hper a
      have hle := h3 a
      have hk : x ^ Function.minimalPeriod (x • ·) a • a = a := by
        rw [← hiter]
        exact Function.iterate_minimalPeriod
      interval_cases h : Function.minimalPeriod (x • ·) a
      · rw [pow_one] at hk
        rw [pow_two, mul_smul, hk, hk]
      · exact hk
    have hF : 1 < Nat.card F := Finite.one_lt_card
    have h3pts : 2 < (Finset.univ : Finset (PSL2ProjectiveLine F)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hX]
      omega
    obtain ⟨a, b, c, -, -, -, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h3pts
    have hx2 : x ^ 2 = 1 := huniq _ a b c hab hac hbc (h2 a) (h2 b) (h2 c)
    calc orderOf x ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hx2
      _ ≤ Nat.card F + 1 := by omega

theorem psl2_orderOf_le (F : Type) [Field F] [Finite F] (x : PSL2 F) :
    orderOf x ≤ Nat.card F + 1 := by
  rw [← orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective x]
  exact pgl2_orderOf_le F _

theorem alternating_four_pow : ∀ y : alternatingGroup (Fin 4), y ^ 2 = 1 ∨ y ^ 3 = 1 := by
  decide

theorem perm_four_pow : ∀ y : Equiv.Perm (Fin 4), y ^ 3 = 1 ∨ y ^ 4 = 1 := by
  decide

theorem alternating_five_pow :
    ∀ y : alternatingGroup (Fin 5), y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 5 = 1 := by
  decide +kernel

theorem orderOf_dvd_of_equiv_alternating_four {M : Type*} [Group M]
    (e : M ≃* alternatingGroup (Fin 4)) (x : M) : orderOf x ∣ 2 ∨ orderOf x ∣ 3 := by
  rw [← MulEquiv.orderOf_eq e x]
  rcases alternating_four_pow (e x) with h | h
  · exact Or.inl (orderOf_dvd_of_pow_eq_one h)
  · exact Or.inr (orderOf_dvd_of_pow_eq_one h)

theorem orderOf_dvd_of_equiv_perm_four {M : Type*} [Group M]
    (e : M ≃* Equiv.Perm (Fin 4)) (x : M) : orderOf x ∣ 3 ∨ orderOf x ∣ 4 := by
  rw [← MulEquiv.orderOf_eq e x]
  rcases perm_four_pow (e x) with h | h
  · exact Or.inl (orderOf_dvd_of_pow_eq_one h)
  · exact Or.inr (orderOf_dvd_of_pow_eq_one h)

theorem orderOf_dvd_of_equiv_alternating_five {M : Type*} [Group M]
    (e : M ≃* alternatingGroup (Fin 5)) (x : M) :
    orderOf x ∣ 2 ∨ orderOf x ∣ 3 ∨ orderOf x ∣ 5 := by
  rw [← MulEquiv.orderOf_eq e x]
  rcases alternating_five_pow (e x) with h | h | h
  · exact Or.inl (orderOf_dvd_of_pow_eq_one h)
  · exact Or.inr (Or.inl (orderOf_dvd_of_pow_eq_one h))
  · exact Or.inr (Or.inr (orderOf_dvd_of_pow_eq_one h))

theorem commute_of_equiv_dihedral {M : Type*} [Group M] {z : ℕ} (e : M ≃* DihedralGroup z)
    {x y : M} (hx : 2 < orderOf x) (hy : 2 < orderOf y) : x * y = y * x := by
  have hr : ∀ a : M, 2 < orderOf a → ∃ i, e a = DihedralGroup.r i := by
    intro a ha
    rw [← MulEquiv.orderOf_eq e a] at ha
    rcases h : e a with i | i
    · exact ⟨i, rfl⟩
    · rw [h, DihedralGroup.orderOf_sr] at ha
      omega
  obtain ⟨i, hi⟩ := hr x hx
  obtain ⟨j, hj⟩ := hr y hy
  apply e.injective
  rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]

theorem mem_of_pow_eq_one_of_sup {M : Type*} [Group M] [Finite M] {p : ℕ} (N C : Subgroup M)
    [N.Normal] (hsup : N ⊔ C = ⊤) (hC : Nat.Coprime (Nat.card C) p) {x : M}
    (hx : x ^ p = 1) : x ∈ N := by
  let π : M →* M ⧸ N := QuotientGroup.mk' N
  have hsurj : Function.Surjective (π.comp C.subtype) := by
    intro m
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N m
    have hm : m ∈ N ⊔ C := hsup ▸ Subgroup.mem_top m
    obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hm
    refine ⟨⟨c, hc⟩, ?_⟩
    change (QuotientGroup.mk c : M ⧸ N) = QuotientGroup.mk (n * c)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have hdvd : Nat.card (M ⧸ N) ∣ Nat.card C := Subgroup.card_dvd_of_surjective hsurj
  have h1 : orderOf (π x) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h2 : orderOf (π x) ∣ Nat.card C := (orderOf_dvd_natCard (π x)).trans hdvd
  have h3 : orderOf (π x) = 1 := Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hC ▸ Nat.dvd_gcd h2 h1)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).mp h3

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
