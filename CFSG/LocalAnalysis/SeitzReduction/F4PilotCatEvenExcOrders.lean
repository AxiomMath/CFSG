module

public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.GH74.Orders.LieType
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.SeitzReduction.F4Pilot.EvenExc

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders

theorem profile_ordBC_three {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordBC 3 (2 ^ f)) (f * 9) (fun k => k ∣ f * 2 ∨ k ∣ f * 4 ∨ k ∣ f * 6) := by
  have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    Nat.coprime_two_left.mpr (odd_two_pow_sub_one (by omega))
  have hm : ordBC 3 (2 ^ f) =
      2 ^ (f * 9) * (((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1))) := by
    rw [ordBC, hgcd, Nat.div_one, show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
      ← pow_mul]
  refine Profile.of_eq hm ((odd_pow_sub_one (by omega) (by norm_num)).mul
    ((odd_pow_sub_one (by omega) (by norm_num)).mul (odd_pow_sub_one (by omega) (by norm_num))))
    (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk]

theorem profile_ordG2' {e : ℕ} (he : 1 ≤ e) :
    Profile (ordG2 (2 ^ e)) (e * 6) (fun k => k ∣ e * 6 ∨ k ∣ e * 2) := by
  refine Profile.of_eq (ordG2_eq e)
    ((odd_pow_sub_one (by omega) (by norm_num)).mul (odd_pow_sub_one (by omega) (by norm_num)))
    (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk, PrimDiv.dvd_pow_sub_one_iff hp hk]

theorem profile_ordF4' {e : ℕ} (he : 1 ≤ e) : Profile (ordF4 (2 ^ e)) (e * 24)
    (fun k => k ∣ e * 12 ∨ k ∣ e * 8 ∨ k ∣ e * 6 ∨ k ∣ e * 2) := by
  have hm : ordF4 (2 ^ e) = 2 ^ (e * 24) * (((2 ^ e) ^ 12 - 1) * (((2 ^ e) ^ 8 - 1) *
      (((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 2 - 1)))) := by
    rw [ordF4, pow_mul]; ring
  refine Profile.of_eq hm (by
    repeat' apply Odd.mul
    all_goals exact odd_pow_sub_one (by omega) (by norm_num)) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk]

theorem profile_ordE6' {e : ℕ} (he : 1 ≤ e) : Profile (ordE6 (2 ^ e)) (e * 36)
    (fun k => k ∣ e * 12 ∨ k ∣ e * 9 ∨ k ∣ e * 8 ∨ k ∣ e * 6 ∨ k ∣ e * 5 ∨ k ∣ e * 2) := by
  set q := 2 ^ e with hq
  have hm : ordE6 q = 2 ^ (e * 36) * ((q ^ 12 - 1) * ((q ^ 9 - 1) * ((q ^ 8 - 1) *
      ((q ^ 6 - 1) * ((q ^ 5 - 1) * (q ^ 2 - 1)))))) / Nat.gcd 3 (q - 1) := by
    rw [ordE6, hq, pow_mul]; ring_nf
  refine Profile.of_div hm (by
    repeat' apply Odd.mul
    all_goals exact odd_pow_sub_one (by omega) (by norm_num)) (Nat.gcd_dvd_right _ _) ?_
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (fun p k hp hk => ?_)
  · exact ⟨_, by
      rw [show (q - 1) * (q - 1) * ((q ^ 12 - 1) / (q - 1) * ((q ^ 9 - 1) / (q - 1)) *
        ((q ^ 8 - 1) * ((q ^ 6 - 1) * ((q ^ 5 - 1) * (q ^ 2 - 1))))) =
        ((q - 1) * ((q ^ 12 - 1) / (q - 1))) * (((q - 1) * ((q ^ 9 - 1) / (q - 1))) *
        ((q ^ 8 - 1) * ((q ^ 6 - 1) * ((q ^ 5 - 1) * (q ^ 2 - 1))))) by ring,
        Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one q 12),
        Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one q 9)]⟩
  · simp only [hp.prime.dvd_mul, hq, PrimDiv.dvd_pow_sub_one_iff hp hk]

theorem profile_ordTwistedE6' {e : ℕ} (he : 1 ≤ e) : Profile (ordTwistedE6 (2 ^ e)) (e * 36)
    (fun k => k ∣ e * 12 ∨ (k ∣ 2 * (e * 9) ∧ ¬ k ∣ e * 9) ∨ k ∣ e * 8 ∨ k ∣ e * 6 ∨
      (k ∣ 2 * (e * 5) ∧ ¬ k ∣ e * 5) ∨ k ∣ e * 2) := by
  set q := 2 ^ e with hq
  have hm : ordTwistedE6 q = 2 ^ (e * 36) * ((q ^ 12 - 1) * ((q ^ 9 + 1) * ((q ^ 8 - 1) *
      ((q ^ 6 - 1) * ((q ^ 5 + 1) * (q ^ 2 - 1)))))) / Nat.gcd 3 (q + 1) := by
    rw [ordTwistedE6, hq, pow_mul]; ring_nf
  refine Profile.of_div hm (by
    refine Odd.mul (odd_pow_sub_one (by omega) (by norm_num))
      (Odd.mul (odd_pow_add_one (by omega) (by norm_num))
      (Odd.mul (odd_pow_sub_one (by omega) (by norm_num))
      (Odd.mul (odd_pow_sub_one (by omega) (by norm_num))
      (Odd.mul (odd_pow_add_one (by omega) (by norm_num))
        (odd_pow_sub_one (by omega) (by norm_num))))))
    ) (Nat.gcd_dvd_right _ _) ?_ (Nat.gcd_pos_of_pos_left _ (by norm_num)) (fun p k hp hk => ?_)
  · have h9 := add_one_dvd_pow_add_one q (by decide : Odd 9)
    have h5 := add_one_dvd_pow_add_one q (by decide : Odd 5)
    exact (mul_dvd_mul h9 h5).trans ⟨(q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1),
      by ring⟩
  · simp only [hp.prime.dvd_mul, hq, PrimDiv.dvd_pow_sub_one_iff hp hk,
      PrimDiv.dvd_pow_add_one_iff hp hk]

theorem profile_ordE7' {e : ℕ} (he : 1 ≤ e) : Profile (ordE7 (2 ^ e)) (e * 63)
    (fun k => k ∣ e * 18 ∨ k ∣ e * 14 ∨ k ∣ e * 12 ∨ k ∣ e * 10 ∨ k ∣ e * 8 ∨ k ∣ e * 6 ∨
      k ∣ e * 2) := by
  have hm : ordE7 (2 ^ e) = 2 ^ (e * 63) * (((2 ^ e) ^ 18 - 1) * (((2 ^ e) ^ 14 - 1) *
      (((2 ^ e) ^ 12 - 1) * (((2 ^ e) ^ 10 - 1) * (((2 ^ e) ^ 8 - 1) * (((2 ^ e) ^ 6 - 1) *
      ((2 ^ e) ^ 2 - 1))))))) := by
    rw [ordE7, Nat.coprime_two_left.mpr (odd_two_pow_sub_one (by omega)), Nat.div_one, pow_mul]
    ring
  refine Profile.of_eq hm (by
    repeat' apply Odd.mul
    all_goals exact odd_pow_sub_one (by omega) (by norm_num)) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk]

theorem profile_ordE8' {e : ℕ} (he : 1 ≤ e) : Profile (ordE8 (2 ^ e)) (e * 120)
    (fun k => k ∣ e * 30 ∨ k ∣ e * 24 ∨ k ∣ e * 20 ∨ k ∣ e * 18 ∨ k ∣ e * 14 ∨ k ∣ e * 12 ∨
      k ∣ e * 8 ∨ k ∣ e * 2) := by
  have hm : ordE8 (2 ^ e) = 2 ^ (e * 120) * (((2 ^ e) ^ 30 - 1) * (((2 ^ e) ^ 24 - 1) *
      (((2 ^ e) ^ 20 - 1) * (((2 ^ e) ^ 18 - 1) * (((2 ^ e) ^ 14 - 1) * (((2 ^ e) ^ 12 - 1) *
      (((2 ^ e) ^ 8 - 1) * ((2 ^ e) ^ 2 - 1)))))))) := by
    rw [ordE8, pow_mul]; ring
  refine Profile.of_eq hm (by
    repeat' apply Odd.mul
    all_goals exact odd_pow_sub_one (by omega) (by norm_num)) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk]

theorem profile_ordTrialityD4' {e : ℕ} (he : 1 ≤ e) : Profile (ordTrialityD4 (2 ^ e)) (e * 12)
    (fun k => (k ∣ e * 12 ∧ ¬ k ∣ e * 4) ∨ k ∣ e * 6 ∨ k ∣ e * 2) := by
  have hm : ordTrialityD4 (2 ^ e) = 2 ^ (e * 12) *
      (((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) * (((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 2 - 1))) := by
    rw [ordTrialityD4, pow_mul]; ring
  have h1 : Odd ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) := by
    have hev : Even ((2 ^ e) ^ 8 + (2 ^ e) ^ 4) := by
      rw [← pow_mul, ← pow_mul]
      exact ((Nat.even_pow' (by omega)).mpr even_two).add
        ((Nat.even_pow' (by omega)).mpr even_two)
    exact hev.add_one
  refine Profile.of_eq hm (h1.mul ((odd_pow_sub_one (by omega) (by norm_num)).mul
    (odd_pow_sub_one (by omega) (by norm_num)))) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk,
    PrimDiv.dvd_pow_sub_one_iff hp hk]
  constructor
  · rintro (h | h | h)
    · rcases PrimDiv.index_of_dvd_triality hp hk e h with h' | rfl
      · exact Or.inl h'
      · exact Or.inr (Or.inr ⟨e, by ring⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (PrimDiv.dvd_triality_of hp hk e h.1 h.2)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem profile_ordSuzuki' {e : ℕ} (he : 1 ≤ e) : Profile (ordSuzuki (2 ^ e)) (e * 2)
    (fun k => (k ∣ 2 * (e * 2) ∧ ¬ k ∣ e * 2) ∨ k ∣ e) := by
  have hm : ordSuzuki (2 ^ e) = 2 ^ (e * 2) * (((2 ^ e) ^ 2 + 1) * (2 ^ e - 1)) := by
    rw [ordSuzuki, pow_mul, mul_assoc]
  refine Profile.of_eq hm ((odd_pow_add_one (by omega) (by norm_num)).mul
    (odd_two_pow_sub_one (by omega))) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_add_one_iff hp hk, hp.dvd_sub_one_iff hk]

theorem profile_ordTwistedF4' {e : ℕ} (he : 1 ≤ e) : Profile (ordTwistedF4 (2 ^ e)) (e * 12)
    (fun k => (k ∣ 2 * (e * 6) ∧ ¬ k ∣ e * 6) ∨ k ∣ e * 4 ∨ (k ∣ 2 * (e * 3) ∧ ¬ k ∣ e * 3) ∨
      k ∣ e) := by
  have hm : ordTwistedF4 (2 ^ e) = 2 ^ (e * 12) * (((2 ^ e) ^ 6 + 1) * (((2 ^ e) ^ 4 - 1) *
      (((2 ^ e) ^ 3 + 1) * (2 ^ e - 1)))) := by
    rw [ordTwistedF4, pow_mul]; ring
  refine Profile.of_eq hm ((odd_pow_add_one (by omega) (by norm_num)).mul
    ((odd_pow_sub_one (by omega) (by norm_num)).mul ((odd_pow_add_one (by omega) (by norm_num)).mul
    (odd_two_pow_sub_one (by omega))))) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_add_one_iff hp hk,
    PrimDiv.dvd_pow_sub_one_iff hp hk, hp.dvd_sub_one_iff hk]

theorem ne_ordBC_three_of_profile {m N w : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hw : Z w)
    (hw2 : 2 ≤ w) (hw6 : w ≠ 6) (hle : ∀ k, Z k → k ≤ w) (hrel : 2 * N ≠ 3 * w) (h9 : N ≠ 9)
    {f : ℕ} (hf : 1 ≤ f) : m ≠ ordBC 3 (2 ^ f) := by
  intro hm
  have hS := profile_ordBC_three hf
  rw [← hm] at hS
  obtain ⟨hN, hZZ⟩ := h.transfer hS
  have hf2 : 2 ≤ f := by
    by_contra hlt
    exact h9 (by omega)
  have h1 : f * 6 ≤ w := hle _ ((hZZ _ (by omega) (by omega)).mpr (Or.inr (Or.inr dvd_rfl)))
  have h2 : w ≤ f * 6 := by
    rcases (hZZ w hw2 hw6).mp hw with h | h | h <;>
      exact (Nat.le_of_dvd (by omega) h).trans (by omega)
  omega

theorem le_mul_of_dvd_mul {k e a b : ℕ} (he : 1 ≤ e) (ha : 1 ≤ a) (hab : a ≤ b)
    (h : k ∣ e * a) : k ≤ e * b :=
  (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) h).trans (Nat.mul_le_mul_left _ hab)

theorem not_two_mul_dvd_self {a : ℕ} (ha : 0 < a) : ¬ 2 * a ∣ a := fun h => by
  have := Nat.le_of_dvd ha h
  omega

theorem ordG2_ne_ordBC_three {e f : ℕ} (he : 2 ≤ e) (hf : 1 ≤ f) :
    ordG2 (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordG2' (by omega)) (w := e * 6) (Or.inl dvd_rfl) (by omega)
    (by omega) (fun k hk => by
      rcases hk with h | h <;> exact le_mul_of_dvd_mul (by omega) (by norm_num) (by norm_num) h)
    (by omega) (by omega) hf

theorem ordF4_ne_ordBC_three {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    ordF4 (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordF4' he) (w := e * 12) (Or.inl dvd_rfl) (by omega)
    (by omega) (fun k hk => by
      rcases hk with h | h | h | h <;>
        exact le_mul_of_dvd_mul he (by norm_num) (by norm_num) h)
    (by omega) (by omega) hf

theorem ordE6_ne_ordBC_three {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    ordE6 (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordE6' he) (w := e * 12) (Or.inl dvd_rfl) (by omega)
    (by omega) (fun k hk => by
      rcases hk with h | h | h | h | h | h <;>
        exact le_mul_of_dvd_mul he (by norm_num) (by norm_num) h)
    (by omega) (by omega) hf

theorem ordTwistedE6_ne_ordBC_three {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    ordTwistedE6 (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordTwistedE6' he) (w := 2 * (e * 9))
    (Or.inr (Or.inl ⟨dvd_rfl, not_two_mul_dvd_self (by omega)⟩)) (by omega) (by omega)
    (fun k hk => by
      rcases hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h
      · exact (le_mul_of_dvd_mul he (by norm_num) (le_refl 12) h).trans (by omega)
      · exact Nat.le_of_dvd (by omega) h
      · exact (le_mul_of_dvd_mul he (by norm_num) (le_refl 8) h).trans (by omega)
      · exact (le_mul_of_dvd_mul he (by norm_num) (le_refl 6) h).trans (by omega)
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
      · exact (le_mul_of_dvd_mul he (by norm_num) (le_refl 2) h).trans (by omega))
    (by omega) (by omega) hf

theorem ordE7_ne_ordBC_three {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    ordE7 (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordE7' he) (w := e * 18) (Or.inl dvd_rfl) (by omega)
    (by omega) (fun k hk => by
      rcases hk with h | h | h | h | h | h | h <;>
        exact le_mul_of_dvd_mul he (by norm_num) (by norm_num) h)
    (by omega) (by omega) hf

theorem ordE8_ne_ordBC_three {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    ordE8 (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordE8' he) (w := e * 30) (Or.inl dvd_rfl) (by omega)
    (by omega) (fun k hk => by
      rcases hk with h | h | h | h | h | h | h | h <;>
        exact le_mul_of_dvd_mul he (by norm_num) (by norm_num) h)
    (by omega) (by omega) hf

theorem ordTrialityD4_ne_ordBC_three {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordTrialityD4' he) (w := e * 12)
    (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩) (by omega)
    (by omega) (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | h <;>
        exact le_mul_of_dvd_mul he (by norm_num) (by norm_num) h)
    (by omega) (by omega) hf

theorem ordSuzuki_ne_ordBC_three {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordSuzuki' he) (w := 2 * (e * 2))
    (Or.inl ⟨dvd_rfl, not_two_mul_dvd_self (by omega)⟩) (by omega) (by omega)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h
      · exact Nat.le_of_dvd (by omega) h
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) (by omega) hf

theorem ordTwistedF4_ne_ordBC_three {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ e) ≠ ordBC 3 (2 ^ f) :=
  ne_ordBC_three_of_profile (profile_ordTwistedF4' he) (w := 2 * (e * 6))
    (Or.inl ⟨dvd_rfl, not_two_mul_dvd_self (by omega)⟩) (by omega) (by omega)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | ⟨h, -⟩ | h
      · exact Nat.le_of_dvd (by omega) h
      · exact (le_mul_of_dvd_mul he (by norm_num) (le_refl 4) h).trans (by omega)
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) (by omega) hf

theorem ordTits_ne_ordBC_three {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordBC 3 (2 ^ f) := by
  rw [ordTits_eq]
  exact ((profile_ordBC_three hf).ne_of_ne (by decide) (by omega)).symm

theorem ordTwistedA_two_three : ordTwistedA 2 3 = 2 ^ 5 * 189 := by decide

theorem ordTwistedA_two_three_ne_ordBC_three {f : ℕ} (hf : 1 ≤ f) :
    ordTwistedA 2 3 ≠ ordBC 3 (2 ^ f) := by
  rw [ordTwistedA_two_three]
  exact ((profile_ordBC_three hf).ne_of_ne (by decide) (by omega)).symm

end CFSG.SeitzReduction.F4Pilot.EvenExc

namespace CFSG.SeitzReduction.F4Pilot

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders

@[expose] def ExcEvenType (X : Type) [Group X] : Prop :=
  (∃ (τ : StatedLieTag) (e : ℕ), τ ∉ classicalTags ∧ StatedLieAdmissible τ 0 2 e ∧
      LieModel X τ 0 2 e) ∨
    LieModel X .PSU 3 3 1

namespace EvenExc

theorem card_eq_ordBC_three_of_lieModel {D : Type} [Group D] {f : ℕ}
    (h : LieModel D .PSp 3 2 f) : 1 ≤ f ∧ Nat.card D = ordBC 3 (2 ^ f) := by
  have hcl := GH74.statedClassicalModel_of_lieModel (by norm_num) h
  exact ⟨hcl.1.2.1, (Timmesfeld.card_statedClassicalModel_two hcl).2.2.1 rfl⟩

section Cards


theorem card_of_reeTitsModel_twistedF4' {G : Type} [Group G]
    {f : ℕ} (h : ReeTitsModel G .twistedF4 2 f) : Nat.card G = ordTwistedF4 (2 ^ f) := by
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier G 2 f h
  obtain ⟨-, a, hfa, hmodel⟩ := h
  subst hfa
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow
    (f := 2 * a + 1) (by
      rw [← Nat.card_eq_fintype_card, hK]
      rfl)
  obtain ⟨E⟩ := hS.2.2.2.2.2 a K rfl hK ⟨e⟩
  have hord :=
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K
      hK).1
  rw [Nat.card_congr E.toEquiv, hord, ordTwistedF4]
  set q := 2 ^ (2 * a + 1) with hq
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h4]
  ring

theorem card_of_reeTitsModel_tits
    {G : Type} [Group G] {p f : ℕ}
    (h : ReeTitsModel G .Tits p f) : Nat.card G = ordTits := by
  obtain ⟨E⟩ := Sporadic.Schreier.Tits.titsModelEquiv G p f h
  rw [Nat.card_congr E.toEquiv, Sporadic.Schreier.Tits.card_titsD, ordTits]
  norm_num

theorem card_ne_ordBC_three_of_lieModel
    {X : Type} [Group X] {τ : StatedLieTag} {e : ℕ} (hτ : τ ∉ classicalTags)
    (hadm : StatedLieAdmissible τ 0 2 e) (hX : LieModel X τ 0 2 e) {f : ℕ} (hf : 1 ≤ f) :
    Nat.card X ≠ ordBC 3 (2 ^ f) := by
  have he : 1 ≤ e := hadm.2.1
  cases τ
  case G2 =>
    have hq : 3 ≤ 2 ^ e := hadm.2.2.2
    have he2 : 2 ≤ e := by
      by_contra h
      have h1 : e = 1 := by omega
      subst h1
      norm_num at hq
    rw [show Nat.card X = ordG2 (2 ^ e) from Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hX)]
    exact ordG2_ne_ordBC_three he2 hf
  case F4 =>
    rw [show Nat.card X = ordF4 (2 ^ e) from Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hX)]
    exact ordF4_ne_ordBC_three he hf
  case E6 =>
    rw [show Nat.card X = ordE6 (2 ^ e) from Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hX)]
    exact ordE6_ne_ordBC_three he hf
  case E7 =>
    rw [show Nat.card X = ordE7 (2 ^ e) from Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hX)]
    exact ordE7_ne_ordBC_three he hf
  case E8 =>
    rw [show Nat.card X = ordE8 (2 ^ e) from Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hX)]
    exact ordE8_ne_ordBC_three he hf
  case twistedE6 =>
    rw [show Nat.card X = ordTwistedE6 (2 ^ e) from Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hX)]
    exact ordTwistedE6_ne_ordBC_three he hf
  case trialityD4 =>
    rw [show Nat.card X = ordTrialityD4 (2 ^ e) from
      Timmesfeld.card_chevalleyExceptionalModel_two
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hX)]
    exact ordTrialityD4_ne_ordBC_three he hf
  case twistedB2 =>
    rcases hX with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hsz⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact absurd hrt (by decide)
    · obtain ⟨-, -, -, -, hc⟩ := GH74.card_of_suzukiModel hsz
      rw [hc]
      exact ordSuzuki_ne_ordBC_three he hf
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  case twistedF4 =>
    rcases hX with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · rw [card_of_reeTitsModel_twistedF4' hrt]
      exact ordTwistedF4_ne_ordBC_three he hf
    · exact absurd hsz (by decide)
  case Tits =>
    rcases hX with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · rw [card_of_reeTitsModel_tits hrt]
      exact ordTits_ne_ordBC_three hf
    · exact absurd hsz (by decide)
  all_goals exact absurd (by decide) hτ

end Cards

end EvenExc

theorem card_ne_of_excEvenType_of_lieModel_PSp_three
    {X Y : Type} [Group X] [Group Y] (hX : ExcEvenType X) {f : ℕ}
    (hY : LieModel Y .PSp 3 2 f) : Nat.card X ≠ Nat.card Y := by
  obtain ⟨hf, hcard⟩ := EvenExc.card_eq_ordBC_three_of_lieModel hY
  rw [hcard]
  rcases hX with ⟨τ, e, hτ, hadm, hm⟩ | hU
  · exact EvenExc.card_ne_ordBC_three_of_lieModel hτ hadm hm hf
  · rw [GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) hU]
    exact EvenExc.ordTwistedA_two_three_ne_ordBC_three hf

end CFSG.SeitzReduction.F4Pilot
