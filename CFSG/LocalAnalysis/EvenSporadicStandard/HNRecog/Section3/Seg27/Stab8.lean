module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Tools
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Six
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.PairStab

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma seg27_stabilizer_pair (p q : Fin 8) (hpq : p ≠ q) :
    MulAction.stabilizer (Equiv.Perm (Fin 8)) ({p, q} : Finset (Fin 8)) =
      seg27PairStab p q := by
  ext g
  rw [MulAction.mem_stabilizer_iff, seg27_mem_pairStab]
  constructor
  · intro h
    have hp : g p ∈ ({p, q} : Finset (Fin 8)) := by
      rw [← h]
      exact Finset.mem_smul_finset.mpr ⟨p, by simp, by simp [Equiv.Perm.smul_def]⟩
    have hq : g q ∈ ({p, q} : Finset (Fin 8)) := by
      rw [← h]
      exact Finset.mem_smul_finset.mpr ⟨q, by simp, by simp [Equiv.Perm.smul_def]⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exfalso
      exact hpq (g.injective (by rw [hp, hq]))
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hq⟩
    · exfalso
      exact hpq (g.injective (by rw [hp, hq]))
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [Finset.smul_finset_def]
      simp only [Finset.image_insert, Finset.image_singleton, Equiv.Perm.smul_def, h1, h2]
    · rw [Finset.smul_finset_def]
      simp only [Finset.image_insert, Finset.image_singleton, Equiv.Perm.smul_def, h1, h2]
      exact Finset.pair_comm q p

private lemma seg27_fix_of_sq_fix {g : Equiv.Perm (Fin 8)} {r : Fin 8}
    (hodd : Odd (orderOf g)) (h2 : (g * g) r = r) : g r = r := by
  obtain ⟨k, hk⟩ := hodd
  have h2k : 2 * (k + 1) = orderOf g + 1 := by rw [hk]; ring
  have hgg : (g * g) ^ (k + 1) = g := by
    rw [← pow_two, ← pow_mul, h2k, pow_succ, pow_orderOf_eq_one, one_mul]
  have hfix : ∀ m : ℕ, ((g * g) ^ m) r = r := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, Equiv.Perm.mul_apply, h2, ih]
  calc g r = ((g * g) ^ (k + 1)) r := by rw [hgg]
    _ = r := hfix (k + 1)

theorem seg27_le_pairStab {S X : Subgroup (Equiv.Perm (Fin 8))} {p q : Fin 8}
    (h : Seg27Six X p q) (hX : X ≤ S) (hc : Nat.card S = 120) : S ≤ seg27PairStab p q := by
  intro s hs
  rw [seg27_mem_pairStab]
  have hc2 : Nat.card S = 2 * Nat.card X := by rw [hc, h.card]
  have hfix_sp : ∀ x ∈ X, x (s p) = s p := by
    intro x hx
    have hconj : s⁻¹ * x * s ∈ X := by
      simpa using seg27_conj_mem_of_card_eq_two_mul hX hc2 (S.inv_mem hs) hx
    calc x (s p) = (x * s) p := (Equiv.Perm.mul_apply x s p).symm
      _ = (s * (s⁻¹ * x * s)) p := by
            rw [show s * (s⁻¹ * x * s) = x * s by group]
      _ = s ((s⁻¹ * x * s) p) := Equiv.Perm.mul_apply s _ p
      _ = s p := by rw [h.fix_p _ hconj]
  have hfix_sq : ∀ x ∈ X, x (s q) = s q := by
    intro x hx
    have hconj : s⁻¹ * x * s ∈ X := by
      simpa using seg27_conj_mem_of_card_eq_two_mul hX hc2 (S.inv_mem hs) hx
    calc x (s q) = (x * s) q := (Equiv.Perm.mul_apply x s q).symm
      _ = (s * (s⁻¹ * x * s)) q := by
            rw [show s * (s⁻¹ * x * s) = x * s by group]
      _ = s ((s⁻¹ * x * s) q) := Equiv.Perm.mul_apply s _ q
      _ = s q := by rw [h.fix_q _ hconj]
  have hsp := h.eq_or_eq_of_fixed hfix_sp
  have hsq := h.eq_or_eq_of_fixed hfix_sq
  rcases hsp with hp | hp <;> rcases hsq with hq | hq
  · exfalso
    exact h.ne (s.injective (by rw [hp, hq]))
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exfalso
    exact h.ne (s.injective (by rw [hp, hq]))

theorem seg27_card_inf_pairStab {S X : Subgroup (Equiv.Perm (Fin 8))} {p₀ q₀ p₁ q₁ : Fin 8}
    (h02 : p₀ ≠ p₁) (h03 : p₀ ≠ q₁) (h12 : q₀ ≠ p₁) (h13 : q₀ ≠ q₁) (h23 : p₁ ≠ q₁)
    (h : Seg27Six X p₀ q₀) (hc : Nat.card S = 120) (hX : X ≤ S) :
    Nat.card (S ⊓ seg27PairStab p₁ q₁ : Subgroup (Equiv.Perm (Fin 8))) = 8 := by
  classical
  set St : Subgroup (Equiv.Perm (Fin 8)) := S ⊓ seg27PairStab p₁ q₁ with hSt
  set x : Finset (Fin 8) := {p₁, q₁} with hx
  set O : Finset (Fin 8) := Finset.univ \ ({p₀, q₀} : Finset (Fin 8)) with hO
  have hpair : S ≤ seg27PairStab p₀ q₀ := seg27_le_pairStab h hX hc
  have hpairStab : MulAction.stabilizer (Equiv.Perm (Fin 8)) x = seg27PairStab p₁ q₁ := by
    rw [hx]
    exact seg27_stabilizer_pair p₁ q₁ h23
  have hcard_stab : Nat.card (MulAction.stabilizer ↥S x) = Nat.card St := by
    rw [hSt]
    have hstab_eq : MulAction.stabilizer ↥S x = (seg27PairStab p₁ q₁).subgroupOf S := by
      rw [← MulAction.stabilizer_subgroupOf S x, hpairStab]
    rw [hstab_eq, ← Subgroup.card_subtype S ((seg27PairStab p₁ q₁).subgroupOf S),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hOcard : O.card = 6 := by
    have h1 : ({p₀, q₀} : Finset (Fin 8)).card = 2 := by simp [h.ne]
    rw [hO, Finset.card_sdiff_of_subset (Finset.subset_univ _), h1]
    norm_num
  have horbit_sub :
      MulAction.orbit ↥S x ⊆ (Finset.powersetCard 2 O : Set (Finset (Fin 8))) := by
    intro y hy
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨s, rfl⟩ := hy
    change s • x ∈ Finset.powersetCard 2 O
    rw [Finset.mem_powersetCard]
    constructor
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.mp hz
      have ha' : a = p₁ ∨ a = q₁ := by
        rw [hx] at ha
        simpa using ha
      have hanot : a ∉ ({p₀, q₀} : Finset (Fin 8)) := by
        rcases ha' with ha' | ha'
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun hh => h02 (hh.symm.trans ha'), fun hh => h12 (hh.symm.trans ha')⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun hh => h03 (hh.symm.trans ha'), fun hh => h13 (hh.symm.trans ha')⟩
      have hpres : (s : ↥S) • ({p₀, q₀} : Finset (Fin 8)) = {p₀, q₀} := by
        change (s : Equiv.Perm (Fin 8)) • ({p₀, q₀} : Finset (Fin 8)) = {p₀, q₀}
        have hs' : (s : Equiv.Perm (Fin 8)) ∈
            MulAction.stabilizer (Equiv.Perm (Fin 8)) ({p₀, q₀} : Finset (Fin 8)) := by
          rw [seg27_stabilizer_pair p₀ q₀ h.ne]
          exact hpair s.2
        exact MulAction.mem_stabilizer_iff.mp hs'
      have hiff : (s : ↥S) • a ∈ ({p₀, q₀} : Finset (Fin 8)) ↔
          a ∈ ({p₀, q₀} : Finset (Fin 8)) := by
        have hh := Finset.smul_mem_smul_finset_iff (s : ↥S)
          (s := ({p₀, q₀} : Finset (Fin 8))) (b := a)
        rw [hpres] at hh
        exact hh
      simp only [hO, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hmem => hanot (hiff.mp hmem)
    · rw [Finset.card_smul_finset]
      rw [hx]
      simp [h23]
  have horbit_le : (MulAction.orbit ↥S x).ncard ≤ 15 := by
    calc (MulAction.orbit ↥S x).ncard
        ≤ ((Finset.powersetCard 2 O : Finset (Finset (Fin 8))) :
            Set (Finset (Fin 8))).ncard := Set.ncard_le_ncard horbit_sub
      _ = (Finset.powersetCard 2 O).card := Set.ncard_coe_finset _
      _ = Nat.choose O.card 2 := Finset.card_powersetCard 2 O
      _ = 15 := by rw [hOcard]; decide
  have hcardSt : Nat.card St * (MulAction.orbit ↥S x).ncard = 120 := by
    calc Nat.card St * (MulAction.orbit ↥S x).ncard
        = Nat.card (MulAction.stabilizer ↥S x) * (MulAction.stabilizer ↥S x).index := by
          rw [hcard_stab, MulAction.index_stabilizer]
      _ = Nat.card ↥S := Subgroup.card_mul_index _
      _ = 120 := hc
  have hge8 : 8 ≤ Nat.card St := by
    have hmain : 15 * 8 ≤ 15 * Nat.card St := by
      calc (15 * 8 : ℕ) = 120 := by norm_num
        _ = Nat.card St * (MulAction.orbit ↥S x).ncard := hcardSt.symm
        _ ≤ Nat.card St * 15 := Nat.mul_le_mul_left _ horbit_le
        _ = 15 * Nat.card St := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left hmain (by norm_num)
  have h3 : ¬ 3 ∣ Nat.card St := by
    intro hdvd
    obtain ⟨y, hySt, hyord⟩ := seg27_exists_orderOf_prime St Nat.prime_three hdvd
    rw [hSt, Subgroup.mem_inf] at hySt
    have hyS : y ∈ S := hySt.1
    have hypair : y ∈ seg27PairStab p₁ q₁ := hySt.2
    have hyX : y ∈ X :=
      seg27_mem_of_card_eq_two_mul_of_odd hX (by rw [hc, h.card]) hyS
        (by rw [hyord]; exact ⟨1, by norm_num⟩)
    rw [seg27_mem_pairStab] at hypair
    rcases hypair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hy_mem : y ∈ (X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) p₁ :
          Subgroup (Equiv.Perm (Fin 8))) :=
        ⟨hyX, MulAction.mem_stabilizer_iff.mpr (by simpa [Equiv.Perm.smul_def] using h1)⟩
      have hcard10 := h.card_stab p₁ h02.symm h12.symm
      have hdvd10 : orderOf y ∣ Nat.card (X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) p₁ :
          Subgroup (Equiv.Perm (Fin 8))) := Subgroup.orderOf_dvd_natCard _ hy_mem
      rw [hcard10, hyord] at hdvd10
      norm_num at hdvd10
    · have h2fix : (y * y) p₁ = p₁ := by rw [Equiv.Perm.mul_apply, h1, h2]
      have hfix : y p₁ = p₁ :=
        seg27_fix_of_sq_fix (by rw [hyord]; exact ⟨1, by norm_num⟩) h2fix
      exact h23 (hfix.symm.trans h1)
  have h5 : ¬ 5 ∣ Nat.card St := by
    intro hdvd
    obtain ⟨y, hySt, hyord⟩ := seg27_exists_orderOf_prime St Nat.prime_five hdvd
    rw [hSt, Subgroup.mem_inf] at hySt
    have hyS : y ∈ S := hySt.1
    have hypair : y ∈ seg27PairStab p₁ q₁ := hySt.2
    have hyX : y ∈ X :=
      seg27_mem_of_card_eq_two_mul_of_odd hX (by rw [hc, h.card]) hyS
        (by rw [hyord]; exact ⟨2, by norm_num⟩)
    rw [seg27_mem_pairStab] at hypair
    rcases hypair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact seg27_not_fix_four_of_orderOf_five hyord h.ne h02 h03 h12 h13 h23
        (h.fix_p y hyX) (h.fix_q y hyX) h1 h2
    · have h2fix : (y * y) p₁ = p₁ := by rw [Equiv.Perm.mul_apply, h1, h2]
      have hfix : y p₁ = p₁ :=
        seg27_fix_of_sq_fix (by rw [hyord]; exact ⟨2, by norm_num⟩) h2fix
      exact h23 (hfix.symm.trans h1)
  have hdvd120 : Nat.card St ∣ 120 := by
    have hle : St ≤ S := by rw [hSt]; exact inf_le_left
    have hh : Nat.card St ∣ Nat.card S := Subgroup.card_dvd_of_le hle
    rwa [hc] at hh
  have hcop3 : Nat.Coprime 3 (Nat.card St) :=
    (Nat.prime_three.coprime_iff_not_dvd).2 h3
  have hcop5 : Nat.Coprime 5 (Nat.card St) :=
    (Nat.prime_five.coprime_iff_not_dvd).2 h5
  have hcop15 : Nat.Coprime (Nat.card St) 15 := by
    have h15 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h15]
    exact Nat.coprime_mul_iff_right.mpr ⟨hcop3.symm, hcop5.symm⟩
  have hdvd8 : Nat.card St ∣ 8 := by
    have h120 : (120 : ℕ) = 8 * 15 := by norm_num
    rw [h120] at hdvd120
    exact (Nat.Coprime.dvd_mul_right hcop15).mp hdvd120
  exact le_antisymm (Nat.le_of_dvd (by norm_num : 0 < 8) hdvd8) hge8

end CFSG.EvenSporadicStandard.HNRecog.Section3
