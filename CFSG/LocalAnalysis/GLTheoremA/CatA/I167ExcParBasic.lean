module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcLabel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Timmesfeld

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exc_type167J_clause_c {p : ℕ} {J : Subgroup Ω} (h : Type167J p J) (hp3 : p ≠ 3) :
    ∃ n k : ℕ, Odd n ∧ 3 ≤ n ∧ (k = 1 → 5 ≤ n) ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
      catalogIs (PSimple p J) (isOmPA n (2 ^ k)) := by
  rcases h with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨n, k, hn, hn3, hk1, hk, hpk, hJ⟩
  · exact absurd h3 hp3
  · exact absurd h3 hp3
  · exact ⟨n, k, hn, hn3, hk1, hk, hpk, hJ⟩

theorem exc_catalog_data {S : Type} [Group S] (h : catalogIs S ExcParIdx) :
    ∃ (kf : DefChar.LieFamily) (qc : TauCeti.PrimePower) (hv : (LocalTwo.excIndex kf qc).Valid),
      (kf = .F4 ∨ kf = .twistedE6 ∨ kf = .E7 ∨ kf = .E8) ∧ qc.p = 2 ∧
      Nonempty (S ≃* LocalTwo.CatT ⟨LocalTwo.excIndex kf qc, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    cases d with
    | F4 q => exact ⟨.F4, q, hv, Or.inl rfl, hi, ⟨e⟩⟩
    | twistedE6 q => exact ⟨.twistedE6, q, hv, Or.inr (Or.inl rfl), hi, ⟨e⟩⟩
    | E7 q => exact ⟨.E7, q, hv, Or.inr (Or.inr (Or.inl rfl)), hi, ⟨e⟩⟩
    | E8 q => exact ⟨.E8, q, hv, Or.inr (Or.inr (Or.inr rfl)), hi, ⟨e⟩⟩
    | _ => exact hi.elim

theorem exc_halfSplit_arith {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {lab : GLALabel} {c : Prop}
    (htag : lab.tag = .F4 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hhs : CFSG.Assembly.LargeEvenHalfSplit16 p lab c) {k : ℕ} (hpk : p ∣ 2 ^ k + 1)
    (hek : lab.n ∣ k) : p ∣ 2 ^ lab.n + 1 := by
  have hminus : ¬ p ∣ 2 ^ lab.n - 1 := by
    intro h
    have h1 : 2 ^ lab.n - 1 ∣ 2 ^ k - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hek
    have h2 : p ∣ 2 ^ k - 1 := dvd_trans h h1
    have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h4 : p ∣ (2 ^ k + 1) - (2 ^ k - 1) := Nat.dvd_sub hpk h2
    have h5 : (2 ^ k + 1) - (2 ^ k - 1) = 2 := by omega
    rw [h5] at h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)
  rcases hhs with hs | hb | hb | hb | hb | hb
  · rcases hs with ⟨hu, h⟩ | ⟨hu, -, -, h⟩ | ⟨ht, h⟩ | ⟨-, h3⟩
    · exact absurd h hminus
    · exact h
    · rcases htag with h' | h' | h' | h' <;> rw [h'] at ht <;> simp at ht
    · exact absurd h3 hp3
  · exact hb.2
  · exact absurd hb.2 hminus
  · rcases htag with h' | h' | h' | h' <;> rw [h'] at hb <;> simp at hb
  · rcases htag with h' | h' | h' | h' <;> rw [h'] at hb <;> simp at hb
  · rcases htag with h' | h' | h' | h' <;> rw [h'] at hb <;> simp at hb

section Certs


theorem exc_pSimple_nontrivial {S : Type} [Group S] {kf : DefChar.LieFamily}
    (hkf : kf = .F4 ∨ kf = .twistedE6 ∨ kf = .E7 ∨ kf = .E8) {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    {hv : (LocalTwo.excIndex kf qc).Valid}
    (hcat : Nonempty (S ≃* LocalTwo.CatT ⟨LocalTwo.excIndex kf qc, hv⟩)) : Nontrivial S := by
  obtain ⟨e⟩ := hcat
  have hd : CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcIdx (LocalTwo.excIndex kf qc) := by
    rcases hkf with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl trivial)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl trivial)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))
  have hc : (LocalTwo.excIndex kf qc).characteristic = 2 := by
    rcases hkf with rfl | rfl | rfl | rfl
    · exact (TauCeti.LieTypeIndex.characteristic_F4 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_twistedE6 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_E7 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_E8 qc).trans hqc
  obtain ⟨t, f, -, hm⟩ := CFSG.LocalAnalysis.GLTheoremA.K1419E.exists_excLieModel
    (d := ⟨LocalTwo.excIndex kf qc, hv⟩) hd hc e
  exact (CFSG.LieType.Catalog.lieModel_finite_simple S t 0 2 f hm).2.1

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I167

end
