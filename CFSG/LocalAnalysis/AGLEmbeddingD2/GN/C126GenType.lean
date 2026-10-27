module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Quasithin.Background.C126Split

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.E2

theorem padicValNat_factorial_two_pow (m : ℕ) :
    padicValNat 2 (2 ^ m).factorial = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [e, padicValNat_factorial_mul, ih]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

theorem padicValNat_factorial_two_pow_succ {m : ℕ} (hm : 1 ≤ m) :
    padicValNat 2 (2 ^ m + 1).factorial = 2 ^ m - 1 := by
  have hodd : ¬ 2 ∣ 2 ^ m + 1 := by
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _),
    padicValNat_factorial_two_pow, padicValNat.eq_zero_of_not_dvd hodd, zero_add]

theorem two_pow_mul_ne_factorial {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) :
    2 ^ n * (4 ^ n - 1) ≠ (2 ^ m + 1).factorial := by
  intro h
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hev : 2 ∣ 4 ^ n := by
    have : 2 ∣ 4 := by norm_num
    exact this.trans (dvd_pow_self 4 (by omega))
  have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hodd : ¬ 2 ∣ 4 ^ n - 1 := by omega
  have hv : n = 2 ^ m - 1 := by
    have hv1 := congrArg (padicValNat 2) h
    rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hodd, add_zero,
      padicValNat_factorial_two_pow_succ (by omega)] at hv1
    exact hv1
  have hnodd : n % 2 = 1 := by
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have h5 : (4 ^ n) % 5 = 4 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hdvd : 5 ∣ 2 ^ n * (4 ^ n - 1) := by
    rw [h]
    exact (Nat.Prime.dvd_factorial (by norm_num)).2 (by omega)
  have hp : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h2 | h2
  · have := hp.dvd_of_dvd_pow h2
    omega
  · omega

theorem card_of_isSymCoreModule {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {N : ℕ}
    (h : IsSymCoreModule L N) : Nat.card ↥L = N.factorial := by
  obtain ⟨θ, -⟩ := h
  rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin]

theorem uniform_type {W : Type*} [CommGroup W] {I : Finset (Subgroup (MulAut W))}
    {C : Subgroup W}
    (htrans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t : MulAut W, B1.conjAut t L = L')
    (htype : ∀ L ∈ I, (∃ n : ℕ, IsL2Natural L C n) ∨
      ∃ m : ℕ, 2 ≤ m ∧ IsSymCoreModule L (2 ^ m + 1)) :
    (∀ L ∈ I, ∃ n : ℕ, IsL2Natural L C n) ∨
      ∃ m : ℕ, 2 ≤ m ∧ ∀ L ∈ I, IsSymCoreModule L (2 ^ m + 1) := by
  by_cases hall : ∀ L ∈ I, ∃ n : ℕ, IsL2Natural L C n
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨L₀, hL₀, hn0⟩ := hall
  obtain ⟨m₀, hm₀, hS₀⟩ := (htype L₀ hL₀).resolve_left (by simpa using hn0)
  refine ⟨m₀, hm₀, fun L hL => ?_⟩
  obtain ⟨t, ht⟩ := htrans L₀ hL₀ L hL
  have hc : Nat.card ↥L = (2 ^ m₀ + 1).factorial := by
    rw [← ht, B1.card_conjAut, card_of_isSymCoreModule hS₀]
  rcases htype L hL with ⟨n, hn⟩ | ⟨m, hm, hS⟩
  · exfalso
    rw [C126.card_of_isL2Natural hn] at hc
    exact two_pow_mul_ne_factorial hn.1 hm₀ hc
  · have hcm : (2 ^ m + 1).factorial = (2 ^ m₀ + 1).factorial := by
      rw [← card_of_isSymCoreModule hS, hc]
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hm1 : 2 ^ m + 1 = 2 ^ m₀ + 1 := (Nat.factorial_inj (by omega)).1 hcm
    have h2 : 2 ^ m = 2 ^ m₀ := by omega
    have : m = m₀ := Nat.pow_right_injective (le_refl 2) h2
    rw [this] at hS
    exact hS

theorem isSolvable_biSup_of_commuting {X : Type*} [Group X] (I : Finset (Subgroup X))
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hsolv : ∀ L ∈ I, Group.IsSolvable ↥L) : Group.IsSolvable ↥(⨆ L ∈ I, L) := by
  classical
  have key : ∀ J : Finset (Subgroup X), J ⊆ I → Group.IsSolvable ↥(⨆ L ∈ J, L) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      have e : (⨆ L ∈ (∅ : Finset (Subgroup X)), L) = ⊥ := by simp
      rw [e]
      infer_instance
    | insert L₀ J hL₀J ih =>
      intro hJI
      have hL₀I : L₀ ∈ I := hJI (Finset.mem_insert_self _ _)
      have hJI' : J ⊆ I := fun y hy => hJI (Finset.mem_insert_of_mem hy)
      rw [Finset.iSup_insert, sup_comm]
      have h1 := ih hJI'
      have h2 := hsolv L₀ hL₀I
      refine C126.isSolvable_sup_of_le_normalizer' (fun b hb => ?_) h1 h2
      have hle : (⨆ L ∈ J, L) ≤ Subgroup.centralizer (L₀ : Set X) := by
        refine iSup₂_le fun L hL c hc => Subgroup.mem_centralizer_iff.2 fun d hd => ?_
        have hne : L₀ ≠ L := fun he => hL₀J (he ▸ hL)
        exact hcomm L₀ hL₀I L (hJI' hL) hne d hd c hc
      exact (le_normalizer_of_commute (A := L₀) (B := ⨆ L ∈ J, L) fun a ha c hc =>
        (Subgroup.mem_centralizer_iff.1 (hle hc) a ha)) hb
  exact key I le_rfl

section

variable {G : Type} [Group G] [Finite G]

theorem case_split_gen {H V : Subgroup G} (hV : IsElemAbelian 2 V) (T : Subgroup G)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hc : E23ConclGen H T V hV) :
    perfectCore H ≤ Subgroup.centralizer (V : Set G) ∨ NatCaseGen H T V hV ∨
      SymCaseGen H T V hV := by
  obtain ⟨hKJ, I, hfam⟩ := hc
  have hfam' := hfam
  obtain ⟨hne, hJeq, hcomm, hconj, htype, -, -⟩ := hfam
  have hcardeq : ∀ L₀ ∈ I, ∀ L ∈ I, Nat.card ↥L = Nat.card ↥L₀ := fun L₀ hL₀ L hL => by
    obtain ⟨t, -, ht⟩ := hconj L₀ hL₀ L hL
    rw [← ht, B1.card_conjAut]
  rcases uniform_type (fun L hL L' hL' => (hconj L hL L' hL').imp fun t ht => ht.2) htype with
    hall | ⟨m, hm, hallS⟩
  · obtain ⟨L₀, hL₀⟩ := hne
    obtain ⟨n₀, hn₀⟩ := hall L₀ hL₀
    have hall' : ∀ L ∈ I, IsL2Natural L (fixV (autI hV (twoResidual H))) n₀ := by
      intro L hL
      obtain ⟨n, hn⟩ := hall L hL
      have hnn : n = n₀ := C126.strictMono_two_pow_mul.injective
        ((C126.card_of_isL2Natural hn).symm.trans
          ((hcardeq L₀ hL₀ L hL).trans (C126.card_of_isL2Natural hn₀)))
      subst hnn
      exact hn
    by_cases hn2 : 2 ≤ n₀
    · exact Or.inr (Or.inl ⟨hKJ, I, hfam', fun L hL => ⟨n₀, hn2, hall' L hL⟩⟩)
    · left
      have hn1 : n₀ = 1 := by
        have := hn₀.1
        omega
      subst hn1
      refine C126.perfectCore_le_centralizer_of_J hV hHN hKJ ?_
      rw [hJeq]
      refine isSolvable_biSup_of_commuting I hcomm fun L hL => ?_
      have h6 : Nat.card ↥L = 6 := by
        rw [C126.card_of_isL2Natural (hall' L hL)]
        norm_num
      have : Finite ↥L := Nat.finite_of_card_ne_zero (by omega)
      exact CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)
  · exact Or.inr (Or.inr ⟨hKJ, I, hfam', m, hm, hallS⟩)

end

end CFSG.AGLEmbeddingD2.GN
