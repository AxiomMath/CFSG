module

public import CFSG.Quasithin.Recognition.F112J2Ext
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4.M8bAux

open scoped commutatorElement
open Finset

theorem card_filter_eq_natCard {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (univ.filter p).card = Nat.card {g // p g} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_split_p {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    (univ.filter (fun g => p g ∧ q g)).card + (univ.filter (fun g => ¬ p g ∧ q g)).card
      = (univ.filter q).card := by
  have h1 : univ.filter (fun g => p g ∧ q g) = (univ.filter q).filter p := by
    ext g; simp only [mem_filter, mem_univ, true_and]; tauto
  have h2 : univ.filter (fun g => ¬ p g ∧ q g) = (univ.filter q).filter (fun g => ¬ p g) := by
    ext g; simp only [mem_filter, mem_univ, true_and]; tauto
  rw [h1, h2, Finset.card_filter_add_card_filter_not]

theorem card_split_q {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    (univ.filter (fun g => q g ∧ p g)).card + (univ.filter (fun g => q g ∧ ¬ p g)).card
      = (univ.filter q).card := by
  have h1 : univ.filter (fun g => q g ∧ p g) = (univ.filter q).filter p := by
    rw [Finset.filter_filter]
  have h2 : univ.filter (fun g => q g ∧ ¬ p g) = (univ.filter q).filter (fun g => ¬ p g) := by
    rw [Finset.filter_filter]
  rw [h1, h2, Finset.card_filter_add_card_filter_not]

open scoped Classical in
theorem card_xtrans {P : Type*} [Group P] [Fintype P] (x y z : P)
    (hPR : ∀ g h k : P, ⁅g, h * k⁆ = ⁅g, h⁆ * ⁅g, k⁆)
    (hxx : x * x = 1) (hyx : ⁅y, x⁆ = z) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hcy : ∀ g : P, ⁅y, g⁆ = 1 ∨ ⁅y, g⁆ = z) (R : P → Prop) [DecidablePred R]
    (hR : ∀ g : P, ⁅x, g⁆ = 1 → (R (x * g) ↔ R g)) :
    (univ.filter (fun g => (⁅x, g⁆ = 1 ∧ R g) ∧ ⁅y, g⁆ = 1)).card =
      (univ.filter (fun g => (⁅x, g⁆ = 1 ∧ R g) ∧ ¬ ⁅y, g⁆ = 1)).card := by
  have hxc : ∀ g : P, ⁅x, g⁆ = 1 → ⁅x, x * g⁆ = 1 := fun g hg => by
    rw [hPR, commutatorElement_self, one_mul, hg]
  apply Finset.card_nbij' (fun g => x * g) (fun g => x * g)
  · intro g hg
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
    refine ⟨⟨hxc g hg.1.1, (hR g hg.1.1).mpr hg.1.2⟩, ?_⟩
    rw [hPR, hyx, hg.2, mul_one]
    exact hz1
  · intro g hg
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
    have hyg : ⁅y, g⁆ = z := (hcy g).resolve_left hg.2
    refine ⟨⟨hxc g hg.1.1, (hR g hg.1.1).mpr hg.1.2⟩, ?_⟩
    rw [hPR, hyx, hyg, hzz]
  · intro g _
    show x * (x * g) = g
    rw [← mul_assoc, hxx, one_mul]
  · intro g _
    show x * (x * g) = g
    rw [← mul_assoc, hxx, one_mul]

theorem core_isQ8D8 {P : Type*} [Group P] [Finite P] (Z : Subgroup P)
    (hZ : Nat.card Z = 2) (hsq : ∀ g : P, g ^ 2 ∈ Z) (hcm : ∀ g h : P, ⁅g, h⁆ ∈ Z)
    (hcen : ∀ g : P, (∀ h : P, h * g = g * h) → g ∈ Z)
    (hP : Nat.card P = 32) (hT : Nat.card {g : P | g ^ 2 = 1} = 12) :
    CFSG.Quasithin.IsQ8D8 P := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  obtain ⟨z, hzZ, hz1, hZel⟩ : ∃ z : P, z ∈ Z ∧ z ≠ 1 ∧ ∀ c ∈ Z, c = 1 ∨ c = z := by
    obtain ⟨w, hw, huniq⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
    refine ⟨w, w.2, fun h => hw (Subtype.ext h), fun c hc => ?_⟩
    by_cases h : c = 1
    · exact Or.inl h
    · exact Or.inr (congrArg Subtype.val (huniq ⟨c, hc⟩ (fun h' => h (congrArg Subtype.val h'))))
  have hz2 : z ^ 2 = 1 := by
    rcases hZel _ (hsq z) with h | h
    · exact h
    · exfalso
      apply hz1
      have h' : z * z = z * 1 := by rw [mul_one, ← pow_two, h]
      exact mul_left_cancel h'
  have hzz : z * z = 1 := by rw [← pow_two, hz2]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hcsq : ∀ c ∈ Z, c * c = 1 := by
    intro c hc
    rcases hZel c hc with h | h
    · rw [h, mul_one]
    · rw [h]; exact hzz
  have hzc : ∀ g : P, g * z = z * g := by
    intro g
    rcases hZel _ (hcm g z) with h | h
    · exact commutatorElement_eq_one_iff_mul_comm.mp h
    · exfalso
      apply hz1
      have h2 : g * z * g⁻¹ = z * z := by
        calc g * z * g⁻¹ = (g * z * g⁻¹ * z⁻¹) * z := by group
          _ = z * z := by rw [← commutatorElement_def, h]
      have h3 : g * z * g⁻¹ = 1 := by rw [h2, hzz]
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
  have hcc : ∀ g h k : P, k * ⁅g, h⁆ = ⁅g, h⁆ * k := by
    intro g h k
    rcases hZel _ (hcm g h) with h' | h'
    · rw [h', mul_one, one_mul]
    · rw [h']; exact hzc k
  have hcinv : ∀ g h : P, ⁅g, h⁆⁻¹ = ⁅g, h⁆ :=
    fun g h => inv_eq_of_mul_eq_one_right (hcsq _ (hcm g h))
  have hPR : ∀ g h k : P, ⁅g, h * k⁆ = ⁅g, h⁆ * ⁅g, k⁆ := by
    intro g h k
    have hc : h * ⁅g, k⁆ * h⁻¹ = ⁅g, k⁆ := by
      rw [hcc g k h, mul_assoc, mul_inv_cancel, mul_one]
    calc ⁅g, h * k⁆ = ⁅g, h⁆ * (h * ⁅g, k⁆ * h⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅g, h⁆ * ⁅g, k⁆ := by rw [hc]
  have hSR : ∀ g h : P, (g * h) ^ 2 = ⁅g, h⁆ * g ^ 2 * h ^ 2 := by
    intro g h
    have hhg : h * g = ⁅g, h⁆⁻¹ * (g * h) := by
      simp only [commutatorElement_def]; group
    rw [hcinv] at hhg
    calc (g * h) ^ 2 = g * (h * g) * h := by simp only [pow_two, mul_assoc]
      _ = g * (⁅g, h⁆ * (g * h)) * h := by rw [hhg]
      _ = (g * ⁅g, h⁆) * g * h * h := by group
      _ = (⁅g, h⁆ * g) * g * h * h := by rw [hcc g h g]
      _ = ⁅g, h⁆ * g ^ 2 * h ^ 2 := by simp only [pow_two, mul_assoc]
  have hcard_T : (univ.filter (fun g : P => g ^ 2 = 1)).card = 12 := by
    rw [card_filter_eq_natCard]; exact hT
  have hcard_Z : (univ.filter (fun g : P => g ∈ Z)).card = 2 := by
    rw [card_filter_eq_natCard]; exact hZ
  have hcard_P : (univ : Finset P).card = 32 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hP]
  obtain ⟨x, hxT, hxZ⟩ : ∃ x : P, x ^ 2 = 1 ∧ x ∉ Z := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hsub : univ.filter (fun g : P => g ^ 2 = 1) ⊆ univ.filter (fun g : P => g ∈ Z) := by
      intro g hg
      rw [mem_filter] at hg ⊢
      exact ⟨mem_univ _, hcon g hg.2⟩
    have hle := Finset.card_le_card hsub
    rw [hcard_T, hcard_Z] at hle
    omega
  obtain ⟨y0, hy0⟩ : ∃ g : P, ⁅x, g⁆ ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hxZ
    apply hcen x
    intro h
    have h' := hcon h
    rw [commutatorElement_eq_one_iff_mul_comm] at h'
    exact h'.symm
  have hxy0 : ⁅x, y0⁆ = z := (hZel _ (hcm x y0)).resolve_left hy0
  obtain ⟨y, hyT, hxy⟩ : ∃ y : P, y ^ 2 = 1 ∧ ⁅x, y⁆ = z := by
    rcases hZel _ (hsq y0) with h | h
    · exact ⟨y0, h, hxy0⟩
    · refine ⟨x * y0, ?_, ?_⟩
      · rw [hSR, hxy0, hxT, h, mul_one, ← pow_two, hz2]
      · rw [hPR, commutatorElement_self, one_mul, hxy0]
  have hxx : x * x = 1 := by rw [← pow_two, hxT]
  have hyy : y * y = 1 := by rw [← pow_two, hyT]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyx : ⁅y, x⁆ = z := by rw [← commutatorElement_inv, hxy, hzinv]
  have hcx : ∀ g : P, ⁅x, g⁆ = 1 ∨ ⁅x, g⁆ = z := fun g => hZel _ (hcm x g)
  have hcy : ∀ g : P, ⁅y, g⁆ = 1 ∨ ⁅y, g⁆ = z := fun g => hZel _ (hcm y g)
  have hxy2 : (x * y) ^ 2 = z := by
    rw [hSR, hxy, hxT, hyT]; simp
  have hsumM : (univ.filter (fun g : P => ⁅x, g⁆ = 1)).card
      + (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1)).card = 32 := by
    rw [Finset.card_filter_add_card_filter_not, hcard_P]
  have hMN : (univ.filter (fun g : P => ⁅x, g⁆ = 1)).card
      = (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1)).card := by
    apply Finset.card_nbij' (fun g => y * g) (fun g => y * g)
    · intro g hg
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
      rw [hPR, hxy, hg, mul_one]
      exact hz1
    · intro g hg
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
      rw [hPR, hxy]
      rcases hcx g with h | h
      · exact absurd h hg
      · rw [h, hzz]
    · intro g _
      show y * (y * g) = g
      rw [← mul_assoc, hyy, one_mul]
    · intro g _
      show y * (y * g) = g
      rw [← mul_assoc, hyy, one_mul]
  have hM16 : (univ.filter (fun g : P => ⁅x, g⁆ = 1)).card = 16 := by omega
  have hN16 : (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1)).card = 16 := by omega
  have hNT : (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1 ∧ g ^ 2 = 1)).card = 8 := by
    have hsplit : (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1 ∧ g ^ 2 = 1)).card
        + (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1 ∧ ¬ g ^ 2 = 1)).card
        = (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1)).card :=
      card_split_q (fun g : P => g ^ 2 = 1) (fun g : P => ¬ ⁅x, g⁆ = 1)
    have hxtr : (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1 ∧ g ^ 2 = 1)).card
        = (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1 ∧ ¬ g ^ 2 = 1)).card := by
      apply Finset.card_nbij' (fun g => x * g) (fun g => x * g)
      · intro g hg
        simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
        have hc : ⁅x, g⁆ = z := (hcx g).resolve_left hg.1
        refine ⟨?_, ?_⟩
        · rw [hPR, commutatorElement_self, one_mul]; exact hg.1
        · rw [hSR, hc, hxT, hg.2]; simpa using hz1
      · intro g hg
        simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
        have hc : ⁅x, g⁆ = z := (hcx g).resolve_left hg.1
        have hsqz : g ^ 2 = z := (hZel _ (hsq g)).resolve_left hg.2
        refine ⟨?_, ?_⟩
        · rw [hPR, commutatorElement_self, one_mul]; exact hg.1
        · rw [hSR, hc, hxT, hsqz, mul_one]; exact hzz
      · intro g _
        show x * (x * g) = g
        rw [← mul_assoc, hxx, one_mul]
      · intro g _
        show x * (x * g) = g
        rw [← mul_assoc, hxx, one_mul]
    omega
  have hMT : (univ.filter (fun g : P => ⁅x, g⁆ = 1 ∧ g ^ 2 = 1)).card = 4 := by
    have hsplit : (univ.filter (fun g : P => ⁅x, g⁆ = 1 ∧ g ^ 2 = 1)).card
        + (univ.filter (fun g : P => ¬ ⁅x, g⁆ = 1 ∧ g ^ 2 = 1)).card
        = (univ.filter (fun g : P => g ^ 2 = 1)).card :=
      card_split_p (fun g : P => ⁅x, g⁆ = 1) (fun g : P => g ^ 2 = 1)
    omega
  have hAT2 : (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ g ^ 2 = 1) ∧ ⁅y, g⁆ = 1)).card = 2 := by
    have hsplit : (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ g ^ 2 = 1) ∧ ⁅y, g⁆ = 1)).card
        + (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ g ^ 2 = 1) ∧ ¬ ⁅y, g⁆ = 1)).card
        = (univ.filter (fun g : P => ⁅x, g⁆ = 1 ∧ g ^ 2 = 1)).card :=
      card_split_q (fun g : P => ⁅y, g⁆ = 1) (fun g : P => ⁅x, g⁆ = 1 ∧ g ^ 2 = 1)
    have hx' : (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ g ^ 2 = 1) ∧ ⁅y, g⁆ = 1)).card
        = (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ g ^ 2 = 1) ∧ ¬ ⁅y, g⁆ = 1)).card :=
      card_xtrans x y z hPR hxx hyx hz1 hzz hcy (fun g : P => g ^ 2 = 1) (fun g hg => by
        show ((x * g) ^ 2 = 1 ↔ g ^ 2 = 1)
        rw [hSR, hg, hxT, one_mul, one_mul])
    omega
  have hA8' : (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ True) ∧ ⁅y, g⁆ = 1)).card = 8 := by
    have hx' : (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ True) ∧ ⁅y, g⁆ = 1)).card
        = (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ True) ∧ ¬ ⁅y, g⁆ = 1)).card :=
      card_xtrans x y z hPR hxx hyx hz1 hzz hcy (fun _ => True) (fun _ _ => Iff.rfl)
    have hsplit : (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ True) ∧ ⁅y, g⁆ = 1)).card
        + (univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ True) ∧ ¬ ⁅y, g⁆ = 1)).card
        = (univ.filter (fun g : P => ⁅x, g⁆ = 1 ∧ True)).card :=
      card_split_q (fun g : P => ⁅y, g⁆ = 1) (fun g : P => ⁅x, g⁆ = 1 ∧ True)
    have hT' : (univ.filter (fun g : P => ⁅x, g⁆ = 1 ∧ True)).card = 16 := by
      rw [← hM16]; congr 1; ext g; simp
    omega
  obtain ⟨Asub, hAsub⟩ : ∃ A : Subgroup P, ∀ g, g ∈ A ↔ ⁅x, g⁆ = 1 ∧ ⁅y, g⁆ = 1 := by
    refine ⟨Subgroup.centralizer ({x, y} : Set P), fun g => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
      commutatorElement_eq_one_iff_mul_comm]
  have hAcard : (univ.filter (fun g : P => g ∈ Asub)).card = 8 := by
    have hA_eq : (univ.filter (fun g : P => g ∈ Asub))
        = univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ True) ∧ ⁅y, g⁆ = 1) :=
      Finset.filter_congr (fun g _ => by rw [hAsub]; simp)
    rw [hA_eq, hA8']
  have hA8 : Nat.card Asub = 8 := by
    rw [← hAcard, card_filter_eq_natCard]

  have hT1z : ({1, z} : Finset P)
      = univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ g ^ 2 = 1) ∧ ⁅y, g⁆ = 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      rw [Finset.mem_insert, Finset.mem_singleton] at hg
      rw [mem_filter]
      rcases hg with h | h <;> rw [h]
      · exact ⟨mem_univ _, ⟨⟨by rw [commutatorElement_one_right], by rw [one_pow]⟩,
          by rw [commutatorElement_one_right]⟩⟩
      · exact ⟨mem_univ _, ⟨⟨commutatorElement_eq_one_iff_mul_comm.mpr (hzc x), hz2⟩,
          commutatorElement_eq_one_iff_mul_comm.mpr (hzc y)⟩⟩
    · rw [hAT2, Finset.card_pair (Ne.symm hz1)]
  have hAT : ∀ g : P, g ∈ Asub → g ^ 2 = 1 → g = 1 ∨ g = z := by
    intro g hg hg2
    have hmem : g ∈ univ.filter (fun g : P => (⁅x, g⁆ = 1 ∧ g ^ 2 = 1) ∧ ⁅y, g⁆ = 1) := by
      rw [mem_filter]
      exact ⟨mem_univ _, ⟨⟨((hAsub g).mp hg).1, hg2⟩, ((hAsub g).mp hg).2⟩⟩
    rw [← hT1z, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem
  have hsqz : ∀ g : P, g ∈ Asub → g ∉ Z → g ^ 2 = z := by
    intro g hg hgZ
    rcases hZel _ (hsq g) with h | h
    · exfalso
      apply hgZ
      rcases hAT g hg h with h1 | h1
      · rw [h1]; exact Z.one_mem
      · rw [h1]; exact hzZ
    · exact h
  obtain ⟨a, haA, haZ⟩ : ∃ a : P, a ∈ Asub ∧ a ∉ Z := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hsub : univ.filter (fun g : P => g ∈ Asub) ⊆ univ.filter (fun g : P => g ∈ Z) := by
      intro g hg
      rw [mem_filter] at hg ⊢
      exact ⟨mem_univ _, hcon g hg.2⟩
    have hle := Finset.card_le_card hsub
    rw [hAcard, hcard_Z] at hle
    omega
  obtain ⟨b, hbA, hbnot⟩ : ∃ b : P, b ∈ Asub ∧ b ∉ ({1, z, a, a * z} : Finset P) := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hsub : univ.filter (fun g : P => g ∈ Asub) ⊆ ({1, z, a, a * z} : Finset P) := by
      intro g hg
      rw [mem_filter] at hg
      exact hcon g hg.2
    have hle := Finset.card_le_card hsub
    have h4 : ({1, z, a, a * z} : Finset P).card ≤ 4 := Finset.card_le_four
    rw [hAcard] at hle
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbnot
  obtain ⟨hb1, hbz, hba, hbaz⟩ := hbnot
  have hbZ : b ∉ Z := by
    intro h
    rcases hZel b h with h' | h'
    · exact hb1 h'
    · exact hbz h'
  have ha2 : a ^ 2 = z := hsqz a haA haZ
  have hb2 : b ^ 2 = z := hsqz b hbA hbZ
  have hainv : a⁻¹ = a * z :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_two, ha2, hzz])
  have hcab : ⁅a, b⁆ = z := by
    rcases hZel _ (hcm a b) with h | h
    · exfalso
      have hab2 : (a * b) ^ 2 = 1 := by
        rw [hSR, h, ha2, hb2, one_mul, hzz]
      have hab_mem : a * b ∈ Asub := Asub.mul_mem haA hbA
      rcases hAT (a * b) hab_mem hab2 with h1 | h1
      · apply hbaz
        calc b = a⁻¹ * (a * b) := by group
          _ = a * z := by rw [h1, mul_one, hainv]
      · apply hba
        calc b = a⁻¹ * (a * b) := by group
          _ = a := by rw [h1, hainv, mul_assoc, hzz, mul_one]
    · exact h
  have hQ : a * b = z * (b * a) := by
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = z * (b * a) := by rw [← commutatorElement_def, hcab]
  obtain ⟨eQ⟩ := CFSG.Quasithin.F112J2.quat_closure hz1 hz2 ha2 hb2 hQ
  have hQle : Subgroup.closure ({a, b} : Set P) ≤ Asub := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h
    · rw [h]; exact haA
    · rw [h]; exact hbA
  have hQcard : Nat.card (Subgroup.closure ({a, b} : Set P)) = 8 := by
    rw [← Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQA : Subgroup.closure ({a, b} : Set P) = Asub :=
    Subgroup.eq_of_le_of_card_ge hQle (by rw [hQcard, hA8])
  have eA : QuaternionGroup 2 ≃* ↥Asub := eQ.trans (MulEquiv.subgroupCongr hQA)
  have hu4 : orderOf (x * y) = 4 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : ¬ (x * y) ^ 2 ^ 1 = 1 := by
      rw [show (2 : ℕ) ^ 1 = 2 from rfl, hxy2]; exact hz1
    have h2 : (x * y) ^ 2 ^ (1 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hxy2, hz2]
    have h3 := orderOf_eq_prime_pow h1 h2
    rw [h3]; norm_num
  have hxnot : x ∉ Subgroup.zpowers (x * y) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hc : Commute ((x * y) ^ k) (x * y) := (Commute.refl (x * y)).zpow_left k
    rw [hk] at hc
    have h1 : ⁅x, x * y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
    rw [hPR, commutatorElement_self, one_mul, hxy] at h1
    exact hz1 h1
  have hxu : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxinv, hyinv, ← mul_assoc, hxx, one_mul]
  obtain ⟨eB⟩ := CFSG.Quasithin.F112J2.dih_closure hu4 hxnot hxT hxu
  have hxB : x ∈ Subgroup.closure ({x * y, x} : Set P) := Subgroup.subset_closure (by simp)
  have huB : x * y ∈ Subgroup.closure ({x * y, x} : Set P) := Subgroup.subset_closure (by simp)
  have hyB : y ∈ Subgroup.closure ({x * y, x} : Set P) := by
    have h : x * (x * y) ∈ Subgroup.closure ({x * y, x} : Set P) := Subgroup.mul_mem _ hxB huB
    rwa [← mul_assoc, hxx, one_mul] at h
  have hAB : Asub ≤ Subgroup.centralizer ((Subgroup.closure ({x * y, x} : Set P) : Subgroup P) : Set P) := by
    intro g hg
    obtain ⟨hgx, hgy⟩ := (hAsub g).mp hg
    have cx : Commute g x := (commutatorElement_eq_one_iff_mul_comm.mp hgx).symm
    have cy : Commute g y := (commutatorElement_eq_one_iff_mul_comm.mp hgy).symm
    have cxy : Commute g (x * y) := cx.mul_right cy
    have hsub : Subgroup.closure ({x * y, x} : Set P) ≤ Subgroup.centralizer ({g} : Set P) := by
      rw [Subgroup.closure_le]
      intro k hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      rcases hk with h | h
      · rw [h]; exact cxy
      · rw [h]; exact cx
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.mp (hsub hh)) g (Set.mem_singleton g)).symm
  have hsup : Asub ⊔ Subgroup.closure ({x * y, x} : Set P) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    have key : ∀ g : P, ⁅x, g⁆ = 1 → g ∈ Asub ⊔ Subgroup.closure ({x * y, x} : Set P) := by
      intro g hg
      by_cases hgy : ⁅y, g⁆ = 1
      · exact Subgroup.mem_sup_left ((hAsub g).mpr ⟨hg, hgy⟩)
      · have hyg : ⁅y, g⁆ = z := (hcy g).resolve_left hgy
        have hxgA : x * g ∈ Asub := by
          rw [hAsub]
          refine ⟨?_, ?_⟩
          · rw [hPR, commutatorElement_self, one_mul, hg]
          · rw [hPR, hyx, hyg, hzz]
        have h : x * (x * g) ∈ Asub ⊔ Subgroup.closure ({x * y, x} : Set P) :=
          Subgroup.mul_mem _ (Subgroup.mem_sup_right hxB) (Subgroup.mem_sup_left hxgA)
        rwa [← mul_assoc, hxx, one_mul] at h
    intro g
    by_cases hgx : ⁅x, g⁆ = 1
    · exact key g hgx
    · have hyg' : ⁅x, y * g⁆ = 1 := by
        rw [hPR, hxy]
        rcases hcx g with h | h
        · exact absurd h hgx
        · rw [h, hzz]
      have h := key (y * g) hyg'
      have h2 : y * (y * g) ∈ Asub ⊔ Subgroup.closure ({x * y, x} : Set P) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right hyB) h
      rwa [← mul_assoc, hyy, one_mul] at h2
  unfold CFSG.Quasithin.IsQ8D8
  refine ⟨hP, Asub, Subgroup.closure ({x * y, x} : Set P), ⟨hAB, hsup⟩, ⟨eA.symm⟩, ⟨eB.symm⟩⟩

end CFSG.GH74.QTGen4.DSGen4.M8bAux

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem leafM8b : LeafM8b := by
  intro G _ _ V Z hs hZ hc hz hV hn
  refine M8bAux.core_isQ8D8 (Z.subgroupOf V) ?_ ?_ ?_ ?_ hV hn
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.1).toEquiv, hZ]
  · intro g
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hs.2.2 _ g.2
  · intro g h
    rw [Subgroup.mem_subgroupOf]
    have h1 : ⁅(g : G), (h : G)⁆ ∈ ⁅V, V⁆ := Subgroup.commutator_mem_commutator g.2 h.2
    rw [hc] at h1
    have h2 : ((⁅g, h⁆ : ↥V) : G) = ⁅(g : G), (h : G)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2]
    exact h1
  · intro g hg
    rw [Subgroup.mem_subgroupOf]
    apply hz
    show (g : G) ∈ V ⊓ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_inf]
    refine ⟨g.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hg ⟨h, hh⟩)

end CFSG.GH74.QTGen4.DSGen4
