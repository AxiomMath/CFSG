module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Design

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

namespace Prop1116Design

theorem alt_iso_degree {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n)
    (f : alternatingGroup (Fin m) ≃* alternatingGroup (Fin n)) : m = n := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h1 : Nat.card (alternatingGroup (Fin m)) = Nat.card (alternatingGroup (Fin n)) :=
    Nat.card_congr f.toEquiv
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_alternatingGroup,
    card_alternatingGroup] at h1
  simp only [Fintype.card_fin] at h1
  have h2 : 2 ∣ Nat.factorial m := Nat.dvd_factorial (by norm_num) (by omega)
  have h3 : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
  have h4 : Nat.factorial m = Nat.factorial n := by
    rw [← Nat.div_mul_cancel h2, ← Nat.div_mul_cancel h3, h1]
  exact (Nat.factorial_inj (by omega)).mp h4

@[expose] def InputAltNotLie : Prop :=
  ∀ (m : ℕ) (idx : TauCeti.ValidLieTypeIndex), 5 ≤ m →
    IsEmpty (alternatingGroup (Fin m) ≃* (TauCeti.CFSGIndex.lie idx).Group)

theorem alt_chev_cases (hnl : InputAltNotLie) {q m : ℕ} (hq2 : q ≠ 2) (hm : 5 ≤ m) {S : Type} [Group S]
    (hS : IsAltType m S) (hch : IsChevSimple q S) : (m = 5 ∧ q = 5) ∨ (m = 6 ∧ q = 3) := by
  obtain ⟨f⟩ := hS
  rcases hch with ⟨i, hi, ⟨g⟩⟩ | ⟨i, hi, ⟨g⟩⟩
  · rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | idx | s
    · exact hi.elim
    · exact hi.elim
    · exact ((hnl m idx hm).false (f.symm.trans g)).elim
    · exact hi.elim
  · rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | idx | s
    · exact hi.elim
    · have hmn : m = n := alt_iso_degree hm hn (f.symm.trans g)
      subst hmn
      rcases hi with ⟨h5, h2 | h5'⟩ | ⟨h6, h2 | h3⟩ | ⟨h8, h2⟩
      · exact absurd h2 hq2
      · exact Or.inl ⟨h5, h5'⟩
      · exact absurd h2 hq2
      · exact Or.inr ⟨h6, h3⟩
      · exact absurd h2 hq2
    · exact ((hnl m idx hm).false (f.symm.trans g)).elim
    · exact hi.elim


@[expose] def InputSchurAltComp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ}, p.Prime → p ≠ 2 → ∀ {X L : Subgroup G},
    GLAPComponent p X L → ∀ n : ℕ, IsAltType n (barOf p L ⧸ Subgroup.center (barOf p L)) →
      Subgroup.center (barOf p L) = ⊥ ∨ (p = 3 ∧ (n = 6 ∨ n = 7))

@[expose] def Input14_4_AltDown : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ}, p.Prime → p ≠ 2 → ∀ {e a : G} {J0 J1 : Subgroup G},
    a * e = e * a → a ^ p = 1 → GLAPComponent p (Cg e) J1 →
    GLAPComponent p (GLAPLayer p (Kx p J0 e ⊓ Cg a)) J0 →
    Kx p J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 →
    ∀ n : ℕ, IsAltType n (barOf p J1 ⧸ Subgroup.center (barOf p J1)) →
      ∃ m : ℕ, 5 ≤ m ∧ IsAltType m (barOf p J0 ⧸ Subgroup.center (barOf p J0)) ∧ m % p = n % p

theorem prime_dvd_threesixty {p : ℕ} (hp : p.Prime) (h : p ∣ 360) : p = 2 ∨ p = 3 ∨ p = 5 := by
  have h1 : p ∣ 2 * 2 * 2 * 3 * 3 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
      · rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
        · rcases (Nat.Prime.dvd_mul hp).mp h5 with h6 | h6
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h6)
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h6)
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h4))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h2))

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide


theorem gLBConj_cg_eq {G : Type} [Group G] {g e : G} (h : g * e = e * g) :
    GLBConj g (Cg e) = Cg e := by
  have h1 : g⁻¹ * e * g = e := by rw [mul_assoc, ← h, inv_mul_cancel_left]
  have h2 : g * e * g⁻¹ = e := by rw [h, mul_inv_cancel_right]
  ext x
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro H
    calc x * e = g⁻¹ * (g * x * g⁻¹ * e) * g := by
          calc x * e = x * (g⁻¹ * e * g) := by rw [h1]
            _ = g⁻¹ * (g * x * g⁻¹ * e) * g := by group
      _ = g⁻¹ * (e * (g * x * g⁻¹)) * g := by rw [H]
      _ = (g⁻¹ * e * g) * x := by group
      _ = e * x := by rw [h1]
  · intro H
    calc g * x * g⁻¹ * e = g * x * g⁻¹ * (g * e * g⁻¹) := by rw [h2]
      _ = g * (x * e) * g⁻¹ := by group
      _ = g * (e * x) * g⁻¹ := by rw [H]
      _ = (g * e * g⁻¹) * (g * x * g⁻¹) := by group
      _ = e * (g * x * g⁻¹) := by rw [h2]


end Prop1116Design

open Prop1116Design

theorem prop1116_alt_of_inputs (hnl : InputAltNotLie) (hschur : InputSchurAltComp)
    (hdown : Input14_4_AltDown) (h116 : Lemma116Statement) : Prop1116AltStatement := by
  intro G _ _ m p B M E A a K q e J0 J1 P n hn
  have hS : GLStanding G m p := P.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  have hAel : IsElemAbelian p A := sec11_isElemAbelian_A P.toSec11
  have ha : a ∈ A := P.ha.1
  have heA : e ∈ A := (Subgroup.mem_inf.1 P.he.1).2
  have hea : a * e = e * a := elemAbelian_comm hAel ha heA
  have hap : a ^ p = 1 := hAel.2 a ha
  obtain ⟨m', hm5, hm', hmod⟩ := hdown hp hp2 hea hap P.hJ1 P.hJ0' P.hJstar n hn
  have hcases := alt_chev_cases hnl P.hq.2.1 hm5 hm' P.hJ0chev
  have hZ0 : Subgroup.center (barOf p J0) = ⊥ := by
    rcases hschur hp hp2 P.hJ0 m' hm' with h | ⟨hp3, hm67⟩
    · exact h
    · exfalso
      rcases hcases with ⟨h5, _⟩ | ⟨_, hq3⟩
      · omega
      · exact P.hq.2.2 (hq3.trans hp3.symm)
  have hcard : Nat.card (barOf p J0) = Nat.card (alternatingGroup (Fin m')) := by
    obtain ⟨f⟩ := hm'
    rw [card_eq_card_quot_center hZ0]
    exact Nat.card_congr f.toEquiv
  have hpm : (m' = 5 ∧ p = 3) ∨ (m' = 6 ∧ p = 5) := by
    have hdvd := P.hJ0p
    rw [hcard] at hdvd
    rcases hcases with ⟨h5, hq5⟩ | ⟨h6, hq3⟩
    · subst h5
      rw [card_alt_five] at hdvd
      rcases prime_dvd_sixty hp hdvd with h | h | h
      · exact absurd h hp2
      · exact Or.inl ⟨rfl, h⟩
      · exact absurd (h.trans hq5.symm) P.hq.2.2.symm
    · subst h6
      rw [card_alt_six] at hdvd
      rcases prime_dvd_threesixty hp hdvd with h | h | h
      · exact absurd h hp2
      · exact absurd (h.trans hq3.symm) P.hq.2.2.symm
      · exact Or.inr ⟨rfl, h⟩
  have hpn : ¬ p ∣ n := by
    rw [Nat.dvd_iff_mod_eq_zero, ← hmod]
    rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hZ1 : Subgroup.center (barOf p J1) = ⊥ := by
    rcases hschur hp hp2 P.hJ1 n hn with h | ⟨hp3, hn67⟩
    · exact h
    · exfalso
      rcases hpm with ⟨hm5', _⟩ | ⟨_, hp5⟩
      · subst hm5'
        rw [hp3] at hmod
        omega
      · omega
  have hn1 : IsAltType n (barOf p J1) := by
    obtain ⟨f⟩ := hn
    exact ⟨(mulEquivQuotCenterOfEqBot hZ1).trans f⟩
  have hconj : ∀ g ∈ Subgroup.zpowers a, GLBConj g J1 ≤ M ⊓ Cg e := by
    intro g hg
    have hgA : g ∈ A := (Subgroup.zpowers_le.mpr ha) hg
    have hgcomm : g * e = e * g := elemAbelian_comm hAel hgA heA
    have hK : GLAPComponent p (Cg e) (GLBConj g J1) := by
      have := glaPComponent_gLBConj P.hJ1 g
      rwa [gLBConj_cg_eq hgcomm] at this
    have hnK : IsAltType n (barOf p (GLBConj g J1)) := by
      obtain ⟨f⟩ := hn1
      exact ⟨(conjQuotEquiv p g J1).symm.trans f⟩
    refine le_inf ?_ hK.1
    rcases h116 P.toSec11 ha P.ha.2 P.he.1 P.he.2 hK hnK hpn with h | ⟨A1, hA1, haA1⟩
    · exact h
    · exact absurd ⟨A1, hA1, haA1⟩ P.notD
  have hle : Kx p J0 e ≤ M ⊓ Cg e := by
    rw [P.hJstar]
    exact iSup₂_le hconj
  exact P.hcov (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hle))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
