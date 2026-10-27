module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Local
public import CFSG.CharacterTheory.Semidihedral.ElementOrders
public import CFSG.CharacterTheory.Wreathed.Coordinates

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

@[expose] def HasFourInvolutions (P : Type*) [Group P] : Prop :=
  ∃ f : Fin 4 → P, Function.Injective f ∧ ∀ i, f i ^ 2 = 1 ∧ f i ≠ 1

theorem HasFourInvolutions.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : HasFourInvolutions Q) : HasFourInvolutions P := by
  obtain ⟨f, hf, hinv⟩ := h
  refine ⟨fun i => e.symm (f i), e.symm.injective.comp hf, fun i => ⟨?_, ?_⟩⟩
  · rw [← map_pow, (hinv i).1, map_one]
  · intro h1
    change e.symm (f i) = 1 at h1
    apply (hinv i).2
    rw [← e.apply_symm_apply (f i), h1, map_one]

theorem HasFourInvolutions.false {P : Type*} [Group P] [Finite P] (h : HasFourInvolutions P)
    {V : Subgroup P} (hV : Nat.card V ≤ 4) (hinv : ∀ g : P, g ^ 2 = 1 → g ∈ V) : False := by
  classical
  obtain ⟨f, hf, hfi⟩ := h
  let F : Option (Fin 4) → V := fun o => match o with
    | none => 1
    | some i => ⟨f i, hinv _ (hfi i).1⟩
  have hF : Function.Injective F := by
    intro o₁ o₂ h
    rcases o₁ with _ | i <;> rcases o₂ with _ | j
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (hfi j).2
    · exact absurd (congrArg Subtype.val h) (hfi i).2
    · exact congrArg some (hf (congrArg Subtype.val h))
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card (α := Option (Fin 4)), Fintype.card_option, Fintype.card_fin]
    at this
  omega

theorem dihedral_center_sq {N : ℕ} {g : DihedralGroup N} (hg : g ∈ center (DihedralGroup N)) :
    g ^ 2 = 1 := by
  rcases g with i | i
  · have h := mem_center_iff.1 hg (DihedralGroup.sr 0)
    simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq] at h
    rw [DihedralGroup.r_pow, DihedralGroup.one_def]
    congr 1
    push_cast
    linear_combination h
  · rw [pow_two, DihedralGroup.sr_mul_self]

theorem dihedral_four_involutions {N : ℕ} (hN : 4 ≤ N) :
    HasFourInvolutions (DihedralGroup N) := by
  refine ⟨fun i => DihedralGroup.sr ((i : ℕ) : ZMod N), fun i j h => ?_, fun i => ⟨?_, ?_⟩⟩
  · simp only [DihedralGroup.sr.injEq] at h
    have hv := congrArg ZMod.val h
    have : NeZero N := ⟨by omega⟩
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv
  · rw [pow_two, DihedralGroup.sr_mul_self]
  · rw [DihedralGroup.one_def]
    intro h
    cases h

theorem semidihedral_center_sq {n : ℕ} (hn : 4 ≤ n) {g : CFSG.Open.SemidihedralGroup n}
    (hg : g ∈ center (CFSG.Open.SemidihedralGroup n)) : g ^ 2 = 1 := by
  rw [CFSG.Semidihedral.center_eq_zpowers n hn] at hg
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    CFSG.Semidihedral.z_sq n (by omega), one_zpow]

theorem semidihedral_four_involutions {n : ℕ} (hn : 4 ≤ n) :
    HasFourInvolutions (CFSG.Open.SemidihedralGroup n) := by
  have hm : 8 ≤ CFSG.Semidihedral.modulus n := by
    rw [CFSG.Semidihedral.modulus]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨fun i => CFSG.Semidihedral.r n ^ (2 * (i : ℕ)) * CFSG.Semidihedral.s n,
    fun i j h => ?_, fun i => ?_⟩
  · have h' := mul_right_cancel h
    rw [pow_eq_pow_iff_modEq, CFSG.Semidihedral.orderOf_r n (by omega)] at h'
    have hi := i.isLt
    have hj := j.isLt
    have := Nat.ModEq.eq_of_lt_of_lt h' (by omega) (by omega)
    exact Fin.ext (by omega)
  · have ho := CFSG.Semidihedral.even_reflection_order n (by omega) ((i : ℕ) : ℤ)
    rw [show (2 : ℤ) * ((i : ℕ) : ℤ) = ((2 * (i : ℕ) : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast] at ho
    refine ⟨?_, fun h1 => ?_⟩
    · have := pow_orderOf_eq_one
        (CFSG.Semidihedral.r n ^ (2 * (i : ℕ)) * CFSG.Semidihedral.s n)
      rwa [ho] at this
    · change CFSG.Semidihedral.r n ^ (2 * (i : ℕ)) * CFSG.Semidihedral.s n = 1 at h1
      rw [h1, orderOf_one] at ho
      omega

theorem wreath_pow_eq_one (n : ℕ) (g : CFSG.Open.WreathedTwoGroup n) : g ^ 2 ^ (n + 1) = 1 := by
  have h := CFSG.Wreathed.element_pow_twice_modulus (2 ^ n) g
  rwa [show 2 * 2 ^ n = 2 ^ (n + 1) by rw [pow_succ, mul_comm]] at h

theorem wreath_card (n : ℕ) : Nat.card (CFSG.Open.WreathedTwoGroup n) = 2 ^ (2 * n + 1) := by
  have h := CFSG.Wreathed.card_wreath (2 ^ n)
  rw [← pow_mul, ← pow_succ', mul_comm n 2] at h
  exact h

theorem wreath_four_involutions {n : ℕ} (hn : 1 ≤ n) :
    HasFourInvolutions (CFSG.Open.WreathedTwoGroup n) := by
  set m := 2 ^ n with hmdef
  set h : ZMod m := ((2 ^ (n - 1) : ℕ) : ZMod m) with hh
  have hh0 : h ≠ 0 := by
    rw [hh, Ne, ZMod.natCast_eq_zero_iff, hmdef]
    intro hdvd
    have := Nat.le_of_dvd (by positivity) hdvd
    have : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h2h : 2 • h = 0 := by
    rw [hh, nsmul_eq_mul, ← Nat.cast_ofNat, ← Nat.cast_mul, ← pow_succ',
      Nat.sub_add_cancel hn, ZMod.natCast_self]
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  clear_value h
  clear hh
  have hinj : ∀ a b c a' b' c', CFSG.Wreathed.element m a b c =
      CFSG.Wreathed.element m a' b' c' → a = a' ∧ b = b' ∧ c = c' := by
    intro a b c a' b' c' heq
    have := CFSG.Wreathed.element_injective m (a₁ := (a, b, c)) (a₂ := (a', b', c')) heq
    simpa using this
  let f : Fin 4 → CFSG.Open.WreathedTwoGroup n := fun i =>
    CFSG.Wreathed.element m (if i.val = 0 ∨ i.val = 2 then h else 0)
      (if i.val = 1 ∨ i.val = 2 then h else 0) (if i.val = 3 then 1 else 0)
  refine ⟨f, fun i j hij => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hinj _ _ _ _ _ _ hij
    clear hinj hij
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    apply Fin.ext
    simp only at h1 h2 h3 ⊢
    interval_cases i <;> interval_cases j <;> simp [hh0, hh0.symm] at h1 h2 h3 ⊢
  · intro i
    have hb : ∀ a b : ZMod m, a ≠ 0 ∨ b ≠ 0 → 2 • a = 0 → 2 • b = 0 →
        CFSG.Wreathed.element m a b 0 ^ 2 = 1 ∧ CFSG.Wreathed.element m a b 0 ≠ 1 := by
      intro a b hab ha hb
      refine ⟨by rw [CFSG.Wreathed.element_base_pow, ha, hb, CFSG.Wreathed.element_zero],
        fun h1 => ?_⟩
      rw [← CFSG.Wreathed.element_zero] at h1
      have := hinj _ _ _ _ _ _ h1
      tauto
    rcases i with ⟨i, hi⟩
    interval_cases i
    · exact hb h 0 (Or.inl hh0) h2h (by simp)
    · exact hb 0 h (Or.inr hh0) (by simp) h2h
    · exact hb h h (Or.inl hh0) h2h h2h
    · refine ⟨?_, fun h1 => ?_⟩
      · change CFSG.Wreathed.element m 0 0 1 ^ 2 = 1
        rw [CFSG.Wreathed.element_swap_sq, add_zero, CFSG.Wreathed.element_zero]
      · change CFSG.Wreathed.element m 0 0 1 = 1 at h1
        rw [← CFSG.Wreathed.element_zero] at h1
        exact h01 (hinj _ _ _ _ _ _ h1).2.2.symm

theorem wreath_element_inj {m : ℕ} {a b a' b' : ZMod m} {c c' : ZMod 2}
    (h : CFSG.Wreathed.element m a b c = CFSG.Wreathed.element m a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have := CFSG.Wreathed.element_injective m (a₁ := (a, b, c)) (a₂ := (a', b', c')) h
  simpa using this

theorem wreath_two_commuting_involution {a b : CFSG.Open.WreathedTwoGroup 2}
    (hab : a * b = b * a) (hb : b ^ 2 = 1) (ha : a ^ 4 ≠ 1) : b ∈ zpowers a := by
  obtain ⟨⟨a₁, a₂, c⟩, rfl⟩ := (CFSG.Wreathed.coordinateEquiv (2 ^ 2)).symm.surjective a
  obtain ⟨⟨b₁, b₂, d⟩, rfl⟩ := (CFSG.Wreathed.coordinateEquiv (2 ^ 2)).symm.surjective b
  change CFSG.Wreathed.element (2 ^ 2) a₁ a₂ c * CFSG.Wreathed.element (2 ^ 2) b₁ b₂ d =
    CFSG.Wreathed.element (2 ^ 2) b₁ b₂ d * CFSG.Wreathed.element (2 ^ 2) a₁ a₂ c at hab
  change CFSG.Wreathed.element (2 ^ 2) b₁ b₂ d ^ 2 = 1 at hb
  change CFSG.Wreathed.element (2 ^ 2) a₁ a₂ c ^ 4 ≠ 1 at ha
  change CFSG.Wreathed.element (2 ^ 2) b₁ b₂ d ∈
    zpowers (CFSG.Wreathed.element (2 ^ 2) a₁ a₂ c)
  rcases CFSG.Wreathed.swap_exponent_cases c with rfl | rfl
  · exact absurd (CFSG.Wreathed.element_base_pow_modulus (2 ^ 2) a₁ a₂) ha
  have ha2 := CFSG.Wreathed.element_swap_sq (2 ^ 2) a₁ a₂
  have ha4 : CFSG.Wreathed.element (2 ^ 2) a₁ a₂ 1 ^ 4 =
      CFSG.Wreathed.element (2 ^ 2) (2 • (a₁ + a₂)) (2 • (a₁ + a₂)) 0 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, ha2, CFSG.Wreathed.element_base_pow]
  have hs : 2 • (a₁ + a₂) ≠ 0 := by
    intro h0
    rw [ha4, h0, CFSG.Wreathed.element_zero] at ha
    exact ha rfl
  rcases CFSG.Wreathed.swap_exponent_cases d with rfl | rfl
  · rw [CFSG.Wreathed.element_swap_mul, CFSG.Wreathed.element_base_mul] at hab
    obtain ⟨h1, -, -⟩ := wreath_element_inj hab
    rw [CFSG.Wreathed.element_base_pow, ← CFSG.Wreathed.element_zero] at hb
    obtain ⟨hb1, -, -⟩ := wreath_element_inj hb
    have hb₂ : b₂ = b₁ := by linear_combination h1
    subst hb₂
    have key : ∀ s x : ZMod (2 ^ 2), 2 • s ≠ 0 → 2 • x = 0 → x = 0 ∨ x = 2 • s := by decide
    rcases key _ _ hs hb1 with rfl | rfl
    · rw [CFSG.Wreathed.element_zero]
      exact one_mem _
    · rw [← ha4]
      exact pow_mem (mem_zpowers _) 4
  · rw [CFSG.Wreathed.element_swap_mul, CFSG.Wreathed.element_swap_mul] at hab
    obtain ⟨h1, -, -⟩ := wreath_element_inj hab
    rw [CFSG.Wreathed.element_swap_sq, ← CFSG.Wreathed.element_zero] at hb
    obtain ⟨hb1, -, -⟩ := wreath_element_inj hb
    have key : ∀ x y u v : ZMod (2 ^ 2), u + v = 0 → x + v = u + y → 2 • (x + y) = 0 := by
      decide
    exact absurd (key _ _ _ _ hb1 h1) hs

theorem unitary_center_sq {K : Type} [Field K] {hK : Nat.card K = 16}
    {w : CFSG.RankTwoShapes.unitaryFourW K hK}
    (hw : w ∈ center (CFSG.RankTwoShapes.unitaryFourW K hK)) : w ^ 2 = 1 :=
  (CFSG.RankTwoShapes.UnitaryFourW.sq_eq_one_iff_mem_center w).2 hw

theorem unitary_pow_four {K : Type} [Field K] {hK : Nat.card K = 16}
    (w : CFSG.RankTwoShapes.unitaryFourW K hK) : w ^ 4 = 1 := by
  have h := unitary_center_sq (CFSG.RankTwoShapes.UnitaryFourW.sq_mem_center w)
  rwa [← pow_mul] at h

theorem unitary_sylow_equiv {H : Type} [Group H]
    (hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2) (U : Sylow 2 H) :
    ∃ hK : Nat.card (GaloisField 2 4) = 16,
      Nonempty ((U : Subgroup H) ≃* CFSG.RankTwoShapes.unitaryFourW (GaloisField 2 4) hK) := by
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  exact ⟨hK, CFSG.RankTwoShapes.nonempty_sylow_equiv_unitaryFourW hH U _ hK⟩

@[expose] def IsRankTwoSylowShape (P : Type*) [Group P] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ (n - 1)))) ∨
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* CFSG.Open.SemidihedralGroup n)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* CFSG.Open.WreathedTwoGroup n)) ∨
    (∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
        Nonempty (P ≃* (U : Subgroup H)))

theorem false_of_shape_few_involutions {P : Type*} [Group P] [Finite P]
    (hshape : IsRankTwoSylowShape P) {V : Subgroup P} (hV : Nat.card V ≤ 4)
    (hinv : ∀ g : P, g ^ 2 = 1 → g ∈ V) (h8 : 8 ≤ Nat.card P)
    (h64 : Nat.card P = 64 → ∃ g : P, g ^ 4 ≠ 1) : False := by
  rcases hshape with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨H, _, U, hH, ⟨e⟩⟩
  · have hcard : Nat.card P = 2 * 2 ^ (n - 1) := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h4 : 4 ≤ 2 ^ (n - 1) := by omega
    exact ((dihedral_four_involutions h4).of_mulEquiv e).false hV hinv
  · exact ((semidihedral_four_involutions hn).of_mulEquiv e).false hV hinv
  · exact ((wreath_four_involutions (by omega)).of_mulEquiv e).false hV hinv
  · obtain ⟨hK, ⟨eW⟩⟩ := unitary_sylow_equiv hH U
    have hcard : Nat.card P = 64 := by
      rw [Nat.card_congr (e.trans eW).toEquiv, CFSG.RankTwoShapes.UnitaryFourW.natCard_unitaryFourW]
    obtain ⟨g, hg⟩ := h64 hcard
    apply hg
    apply (e.trans eW).injective
    rw [map_pow, map_one, unitary_pow_four]

theorem false_of_shape_central_four {P : Type*} [Group P] [Finite P]
    (hshape : IsRankTwoSylowShape P) {c : P} (hc : c ∈ center P) (hc2 : c ^ 2 ≠ 1)
    {a b : P} (hab : a * b = b * a) (hb : b ^ 2 = 1) (hba : b ∉ zpowers a)
    (hcard : Nat.card P = 4 * orderOf a) : False := by
  have hsq : ∀ {Q : Type} [Group Q] (e : P ≃* Q), (∀ q ∈ center Q, q ^ 2 = 1) → False := by
    intro Q _ e hQ
    apply hc2
    apply e.injective
    rw [map_pow, map_one]
    exact hQ _ ((CFSG.LyonsUnitaryFour.mem_center_iff_of_mulEquiv e c).2 hc)
  rcases hshape with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨H, _, U, hH, ⟨e⟩⟩
  · exact hsq e fun q hq => dihedral_center_sq hq
  · exact hsq e fun q hq => semidihedral_center_sq hn hq
  ·
    have hdvd : orderOf a ∣ 2 ^ (n + 1) := by
      rw [← MulEquiv.orderOf_eq e]
      exact orderOf_dvd_of_pow_eq_one (wreath_pow_eq_one n _)
    obtain ⟨j, hj, hja⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hcard' : 2 ^ (j + 2) = 2 ^ (2 * n + 1) := by
      rw [← wreath_card, ← Nat.card_congr e.toEquiv, hcard, hja, pow_add]
      ring
    have hj' := Nat.pow_right_injective (le_refl 2) hcard'
    have hn2 : n = 2 := by omega
    subst hn2
    have ha8 : orderOf (e a) = 8 := by
      rw [MulEquiv.orderOf_eq, hja, show j = 3 by omega]
      norm_num
    have ha4 : e a ^ 4 ≠ 1 := by
      intro h4
      have := orderOf_dvd_of_pow_eq_one h4
      rw [ha8] at this
      norm_num at this
    have hmem := wreath_two_commuting_involution (a := e a) (b := e b)
      (by rw [← map_mul, ← map_mul, hab]) (by rw [← map_pow, hb, map_one]) ha4
    apply hba
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    exact mem_zpowers_iff.2 ⟨k, e.injective (by rw [map_zpow, hk])⟩
  · obtain ⟨hK, ⟨eW⟩⟩ := unitary_sylow_equiv hH U
    exact hsq (e.trans eW) fun q hq => unitary_center_sq hq

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
