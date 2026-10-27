module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltYNine

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Equiv Equiv.Perm CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] noncomputable def autEquivPerm (n : ℕ) (hn5 : 5 ≤ n) (hn6 : n ≠ 6) :
    Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6)

theorem autEquivPerm_coe {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (a : alternatingGroup (Fin n)) :
    autEquivPerm n hn5 hn6 (a : Perm (Fin n)) = MulAut.conj a :=
  MulAut.conjNormal_val

@[expose] noncomputable def autTransport {Y : Type} [Group Y] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : Y ≃* alternatingGroup (Fin n)) : MulAut Y ≃* Perm (Fin n) :=
  (MulAut.congr e).trans (autEquivPerm n hn5 hn6).symm

theorem autTransport_conj {Y : Type} [Group Y] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : Y ≃* alternatingGroup (Fin n)) (y : Y) :
    autTransport hn5 hn6 e (MulAut.conj y) = ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  show (autEquivPerm n hn5 hn6).symm (MulAut.congr e (MulAut.conj y)) = _
  rw [MulEquiv.symm_apply_eq, autEquivPerm_coe]
  ext a
  simp [MulAut.congr_apply]

theorem innSub_map_autTransport {Y : Type} [Group Y] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : Y ≃* alternatingGroup (Fin n)) :
    (innSub Y).map (autTransport hn5 hn6 e).toMonoidHom = alternatingGroup (Fin n) := by
  ext σ
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    show autTransport hn5 hn6 e (MulAut.conj y) ∈ alternatingGroup (Fin n)
    rw [autTransport_conj]
    exact (e y).2
  · intro hσ
    obtain ⟨y, hy⟩ := e.surjective ⟨σ, hσ⟩
    exact ⟨MulAut.conj y, ⟨y, rfl⟩, by
      show autTransport hn5 hn6 e (MulAut.conj y) = σ
      rw [autTransport_conj, hy]⟩

theorem factorization_two_pow_mul_odd (e m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ e * m).factorization 2 = e := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem card_alt_fin {n : ℕ} (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem sylow_exp {n e : ℕ} (h : (n = 5 ∧ e = 2) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨
    (n = 10 ∧ e = 7)) : (Nat.card ↥(alternatingGroup (Fin n))).factorization 2 = e := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [card_alt_fin (by norm_num), show (5 : ℕ).factorial / 2 = 2 ^ 2 * 15 by decide]
    exact factorization_two_pow_mul_odd 2 15 (by norm_num)
  · rw [card_alt_fin (by norm_num), show (8 : ℕ).factorial / 2 = 2 ^ 6 * 315 by decide]
    exact factorization_two_pow_mul_odd 6 315 (by norm_num)
  · rw [card_alt_fin (by norm_num), show (9 : ℕ).factorial / 2 = 2 ^ 6 * 2835 by decide]
    exact factorization_two_pow_mul_odd 6 2835 (by norm_num)
  · rw [card_alt_fin (by norm_num), show (10 : ℕ).factorial / 2 = 2 ^ 7 * 14175 by decide]
    exact factorization_two_pow_mul_odd 7 14175 (by norm_num)

theorem altY_not_sylCfg' (n : ℕ) (h : n = 5 ∨ (8 ≤ n ∧ n ≤ 10)) (Y : Type) [Group Y]
    (e : Y ≃* alternatingGroup (Fin n)) : ¬ SylCfgOf Y := by
  rintro ⟨T, W, hcfg⟩
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  obtain ⟨P, hPT, hPinn, hPsyl⟩ := hcfg.syl
  let Φ := autTransport hn5 hn6 e
  have hinn := innSub_map_autTransport hn5 hn6 e
  have : Finite (MulAut Y) := Finite.of_equiv (Perm (Fin n)) Φ.symm.toEquiv
  obtain ⟨Q, rfl⟩ := hPsyl
  have hQcard := Sylow.card_eq_multiplicity Q
  rw [← Subgroup.card_map_of_injective (innSub Y).subtype_injective (K := (Q : Subgroup _))]
    at hQcard
  have hinncard : Nat.card ↥(innSub Y) = Nat.card ↥(alternatingGroup (Fin n)) := by
    rw [← hinn, Subgroup.card_map_of_injective Φ.injective]
  rw [hinncard] at hQcard
  set P₀ : Subgroup (MulAut Y) := (Q : Subgroup ↥(innSub Y)).map (innSub Y).subtype with hP₀
  have hPA : P₀.map Φ.toMonoidHom ≤ alternatingGroup (Fin n) := by
    rw [← hinn]
    exact Subgroup.map_mono hPinn
  have hPc : Nat.card ↥(P₀.map Φ.toMonoidHom) =
      2 ^ (Nat.card ↥(alternatingGroup (Fin n))).factorization 2 := by
    rw [Subgroup.card_map_of_injective Φ.injective]
    exact hQcard
  have hW3 : IsPGroup 3 ↥(W.map Φ.toMonoidHom) := hcfg.w3.map Φ.toMonoidHom
  have hN : P₀.map Φ.toMonoidHom ≤ normalizer ((W.map Φ.toMonoidHom : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) :=
    (Subgroup.map_mono (hPT.trans hcfg.t_norm)).trans (Subgroup.le_normalizer_map Φ.toMonoidHom)
  obtain ⟨e', hne⟩ : ∃ e', (n = 5 ∧ e' = 2) ∨ (n = 8 ∧ e' = 6) ∨ (n = 9 ∧ e' = 6) ∨
      (n = 10 ∧ e' = 7) := by
    rcases h with h | ⟨h8, h10⟩
    · exact ⟨2, Or.inl ⟨h, rfl⟩⟩
    · have : n = 8 ∨ n = 9 ∨ n = 10 := by omega
      rcases this with h | h | h
      · exact ⟨6, Or.inr (Or.inl ⟨h, rfl⟩)⟩
      · exact ⟨6, Or.inr (Or.inr (Or.inl ⟨h, rfl⟩))⟩
      · exact ⟨7, Or.inr (Or.inr (Or.inr ⟨h, rfl⟩))⟩
  rw [sylow_exp hne] at hPc
  have hW0 : W.map Φ.toMonoidHom = ⊥ := AltY.three_group_trivial_alt hne hPA hPc hW3 hN
  exact hcfg.w_ne ((Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).1 hW0)

theorem altY_not_sylCfg (n : ℕ) (h8 : 8 ≤ n) (h10 : n ≤ 10) (Y : Type) [Group Y]
    (e : Y ≃* alternatingGroup (Fin n)) : ¬ SylCfgOf Y :=
  altY_not_sylCfg' n (Or.inr ⟨h8, h10⟩) Y e

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
