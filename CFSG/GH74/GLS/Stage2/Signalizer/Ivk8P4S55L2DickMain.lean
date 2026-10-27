module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Dick
public import CFSG.Dihedral.Glauberman.DicksonMaxUp

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Dick

open Subgroup CFSG CFSG.Glauberman.Dickson CFSG.BenderSuzuki.MatrixGroups

@[expose] noncomputable def pglSq (K : Type) [Field K] :
    Matrix.ProjGenLinGroup (Fin 2) K →* Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range :=
  QuotientGroup.lift (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K))
    ((QuotientGroup.mk' (powMonoidHom 2 : Kˣ →* Kˣ).range).comp Matrix.GeneralLinearGroup.det)
    (by
      intro z hz
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨a, rfl⟩ := hz
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact ⟨a, by ext; simp [pow_two]⟩)

theorem sqrQuot_sq {K : Type} [Field K] (q : Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) :
    q ^ 2 = 1 := by
  induction q using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨u, rfl⟩

theorem pglSq_nontrivial (K : Type) [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    ∃ w : Matrix.ProjGenLinGroup (Fin 2) K, pglSq K w ≠ 1 := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hK
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  let g : Matrix.GeneralLinearGroup (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![a, 1]) (by
      simp [ha0])
  refine ⟨QuotientGroup.mk g, fun h => ?_⟩
  have h' : (QuotientGroup.mk (Matrix.GeneralLinearGroup.det g) :
      Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) = 1 := h
  obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff _).mp h'
  apply ha
  refine ⟨(v : K), ?_⟩
  have := congrArg (fun u : Kˣ => (u : K)) hv
  simp [g, pow_two] at this
  rw [← this]

theorem card_psl2_F' {F' : Type} [Field F'] [Finite F'] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF' : (∃ n : ℕ, 1 ≤ n ∧ Nat.card F' = p ^ n) ∨ (p = 3 ∧ Nat.card F' = 5)) :
    Nat.card (PSL2MatrixGroup F') = Nat.card F' * (Nat.card F' ^ 2 - 1) / 2 := by
  rcases hF' with ⟨n, -, hn⟩ | ⟨-, h5⟩
  · have : Fact p.Prime := ⟨hp⟩
    rw [MaxUp.card_psl2_odd hn hp2, hn]
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have := MaxUp.card_psl2_odd (F := F') (p := 5) (f := 1) (by simpa using h5) (by norm_num)
    rw [this, h5]
    simp

theorem eq_of_psl_card {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a * (a ^ 2 - 1) / 2 = b * (b ^ 2 - 1) / 2) : a = b := by
  have key : ∀ x y : ℕ, 2 ≤ x → x < y → x * (x ^ 2 - 1) / 2 < y * (y ^ 2 - 1) / 2 := by
    intro x y hx hxy
    have h1 : x * (x ^ 2 - 1) + 2 ≤ y * (y ^ 2 - 1) := by
      have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
      have hy2 : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (by omega)
      have hxz : (2 : ℤ) ≤ x := by exact_mod_cast hx
      have hyz : (x : ℤ) + 1 ≤ y := by exact_mod_cast hxy
      zify [hx2, hy2]
      nlinarith [mul_nonneg (sub_nonneg.mpr hyz) (sub_nonneg.mpr hxz),
        mul_pos (by linarith : (0 : ℤ) < y) (by linarith : (0 : ℤ) < x)]
    calc x * (x ^ 2 - 1) / 2 < (x * (x ^ 2 - 1) + 2) / 2 := by omega
      _ ≤ y * (y ^ 2 - 1) / 2 := Nat.div_le_div_right h1
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (key a b ha hab).ne
  · exact hab
  · exact absurd h.symm (key b a hb hab).ne

theorem no_five_of_orders {J G : Type*} [Group J] [Group G] (ι : J →* G)
    (h : ∀ x : J, ι x ^ 2 = 1 ∨ ι x ^ 3 = 1) : ¬ ∃ x : J, ι x ^ 5 = 1 ∧ ι x ≠ 1 := by
  rintro ⟨x, h5, hne⟩
  rcases h x with h2 | h3
  · exact hne (eq_one_of_pow_odd_sq (by decide : Odd 5) h5 h2)
  · exact hne (by simpa using (pow_gcd_eq_one (a := ι x)).mpr ⟨h5, h3⟩)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Dick
