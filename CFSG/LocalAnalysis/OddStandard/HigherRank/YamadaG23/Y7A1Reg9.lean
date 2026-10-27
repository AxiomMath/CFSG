module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.FixedPoints

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma y7a_nat_no_small (n c m : ℕ) (hn : n ≤ 3) (hlt : c < 2 ^ n)
    (hmod : c % 3 = (2 ^ n) % 3) (hburn : 2 ^ n + 8 * c = 9 * m) : False := by
  have hpow8 : 2 ^ n ≤ 8 := by
    have h : 2 ^ n ≤ 2 ^ 3 := (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mpr hn
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h
    exact h
  have hc8 : c ≤ 8 := by omega
  interval_cases c <;> interval_cases n <;> omega

private lemma y7a_nat_eq_of_facts (n a b : ℕ) (hn : n ≤ 3) (ha : a ∣ 2 ^ n) (ha' : a < 2 ^ n)
    (ham : a % 3 = (2 ^ n) % 3) (hb : b ∣ 2 ^ n) (hb' : b < 2 ^ n)
    (hbm : b % 3 = (2 ^ n) % 3) : a = b := by
  have hpow8 : 2 ^ n ≤ 8 := by
    have h : 2 ^ n ≤ 2 ^ 3 := (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mpr hn
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h
    exact h
  have ha8 : a ≤ 8 := by omega
  have hb8 : b ≤ 8 := by omega
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  interval_cases a <;> interval_cases b <;> interval_cases n <;> omega

theorem y7a_no_order9_small {P Q : Type} [Group P] [Finite P] [Group Q] [Finite Q]
    (hP : IsPGroup 2 P) (hcard : Nat.card P ≤ 8) (hQ : Nat.card Q = 9)
    (φ : Q →* MulAut P) (hφ : Function.Injective φ) : False := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype Q := Fintype.ofFinite Q
  letI : MulAction Q P := MulAction.compHom P φ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hn_le : n ≤ 3 := by
    have hle : 2 ^ n ≤ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hn]
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hle
  have hQ9 : Fintype.card Q = 9 := by rw [← Nat.card_eq_fintype_card]; exact hQ
  haveI : Nontrivial Q :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
  obtain ⟨g, hg⟩ := exists_ne (1 : Q)
  have hkey : ∀ h : Q, h ≠ 1 →
      (Nat.card ↥(MulAction.fixedBy P h) ∣ Nat.card P ∧
       Nat.card ↥(MulAction.fixedBy P h) < Nat.card P ∧
       Nat.card ↥(MulAction.fixedBy P h) % 3 = Nat.card P % 3) := by
    intro h hh
    have hφh : φ h ≠ 1 := fun hc => hh (hφ (by rw [hc, map_one]))
    have hex : ∃ x : P, (φ h) x ≠ x := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hφh (MulEquiv.ext (fun x => by simpa using hcon x))
    have hproper : MulAction.fixedBy P h ≠ Set.univ := by
      obtain ⟨x, hx⟩ := hex
      intro hcontra
      exact hx (by
        have : x ∈ MulAction.fixedBy P h := by rw [hcontra]; exact Set.mem_univ x
        simpa [MulAction.mem_fixedBy, MulAction.compHom_smul_def, MulAut.smul_def] using this)
    have hlt : Nat.card ↥(MulAction.fixedBy P h) < Nat.card P := by
      rw [Nat.card_coe_set_eq]
      exact Set.ncard_lt_card hproper
    have hmod : Nat.card ↥(MulAction.fixedBy P h) ≡ Nat.card P [MOD 3] := by
      let A : Subgroup Q := Subgroup.zpowers h
      have hA : IsPGroup 3 ↥A := by
        apply IsPGroup.of_card_dvd_pow (n := 2)
        rw [Nat.card_zpowers]
        have hdiv := orderOf_dvd_natCard h
        rw [hQ] at hdiv
        simpa using hdiv
      have hfix : MulAction.fixedPoints ↥A P = MulAction.fixedBy P h := by
        ext x
        rw [MulAction.mem_fixedPoints, MulAction.mem_fixedBy]
        constructor
        · intro hx
          simpa using hx ⟨h, Subgroup.mem_zpowers h⟩
        · intro hx a
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
          show (a : Q) • x = x
          rw [← hk]
          exact MulAction.mem_fixedBy_zpow hx k
      have hcard : Nat.card ↥(MulAction.fixedPoints ↥A P)
          = Nat.card ↥(MulAction.fixedBy P h) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [hfix]))
      have h3 := hA.card_modEq_card_fixedPoints P
      rw [hcard] at h3
      exact h3.symm
    let C : Subgroup P :=
      { carrier := MulAction.fixedBy P h
        one_mem' := by
          rw [MulAction.mem_fixedBy, MulAction.compHom_smul_def, MulAut.smul_def, map_one]
        mul_mem' := by
          intro x y hx hy
          rw [MulAction.mem_fixedBy] at hx hy ⊢
          rw [MulAction.compHom_smul_def, MulAut.smul_def] at hx hy ⊢
          rw [map_mul, hx, hy]
        inv_mem' := by
          intro x hx
          rw [MulAction.mem_fixedBy] at hx ⊢
          rw [MulAction.compHom_smul_def, MulAut.smul_def] at hx ⊢
          rw [map_inv, hx] }
    have hCmem : ∀ x : P, x ∈ MulAction.fixedBy P h ↔ x ∈ C := fun _ => Iff.rfl
    refine ⟨?_, hlt, hmod⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hCmem)]
    exact Subgroup.card_subgroup_dvd_card C
  set c : ℕ := Nat.card ↥(MulAction.fixedBy P g) with hc
  have hgc : c ∣ Nat.card P ∧ c < Nat.card P ∧ c % 3 = Nat.card P % 3 := by
    rw [hc]; exact hkey g hg
  have huniq : ∀ h : Q, h ≠ 1 → Nat.card ↥(MulAction.fixedBy P h) = c := by
    intro h hh
    obtain ⟨hdvd, hlt, hmod⟩ := hkey h hh
    obtain ⟨hcdvd, hclt, hcmod⟩ := hgc
    rw [hn] at hdvd hlt hmod hcdvd hclt hcmod
    exact y7a_nat_eq_of_facts n _ _ hn_le hdvd hlt hmod hcdvd hclt hcmod
  have hburn : (∑ h : Q, Nat.card ↥(MulAction.fixedBy P h))
      = 9 * Nat.card (Quotient (MulAction.orbitRel Q P)) := by
    have h1 : Nat.card (Σ h : Q, ↥(MulAction.fixedBy P h))
        = Nat.card (Quotient (MulAction.orbitRel Q P) × Q) :=
      Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup Q P)
    rw [Nat.card_sigma, Nat.card_prod, hQ] at h1
    exact h1.trans (mul_comm _ _)
  have hburnsum : (∑ h : Q, Nat.card ↥(MulAction.fixedBy P h)) = 2 ^ n + 8 * c := by
    rw [← Finset.add_sum_erase (Finset.univ)
      (fun h : Q => Nat.card ↥(MulAction.fixedBy P h)) (Finset.mem_univ (1 : Q))]
    have hone : Nat.card ↥(MulAction.fixedBy P (1 : Q)) = Nat.card P := by
      rw [show MulAction.fixedBy P (1 : Q) = Set.univ by
        ext x; simp [MulAction.mem_fixedBy]]
      simp
    have herase : (∑ h ∈ Finset.univ.erase (1 : Q),
        Nat.card ↥(MulAction.fixedBy P h)) = 8 * c := by
      rw [Finset.sum_const_nat (s := Finset.univ.erase (1 : Q)) (m := c)
        (f := fun h : Q => Nat.card ↥(MulAction.fixedBy P h))
        (fun h hh => huniq h (Finset.mem_erase.mp hh).1)]
      rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : Q)), Finset.card_univ, hQ9]
    rw [hone, hn, herase]
  have hmain : 2 ^ n + 8 * c = 9 * Nat.card (Quotient (MulAction.orbitRel Q P)) :=
    hburnsum.symm.trans hburn
  obtain ⟨_, hclt, hcmod⟩ := hgc
  rw [hn] at hclt hcmod
  exact y7a_nat_no_small n c (Nat.card (Quotient (MulAction.orbitRel Q P))) hn_le hclt hcmod hmain

end CFSG.OddStandard.HigherRank.YamadaG23
