module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup Equiv.Perm.OnCycleFactors

open scoped commutatorElement

structure QuatPermData (n : ℕ) where
  τ : Perm (Fin n)
  W : Subgroup (Perm (Fin n))
  R : Subgroup (Perm (Fin n))
  y : Perm (Fin n)
  w : Perm (Fin n)
  c : Perm (Fin n)
  τ_sq : τ * τ = 1
  τ_ne : τ ≠ 1
  card_W : Nat.card W = 8
  W_zpowers : ∀ g ∈ W, g ≠ 1 → τ ∈ zpowers g
  W_comm : ∀ g ∈ W, g * τ = τ * g
  W_le_R : W ≤ R
  not_dvd_card_R : ¬ 16 ∣ Nat.card R
  R_comm : ∀ r ∈ R, r * τ = τ * r
  y_mem : y ∈ R
  y_sq : y * y = τ
  alt_lift : ∀ π ∈ alternatingGroup τ.cycleFactorsFinset, ∃ g : Perm (Fin n),
    ∃ hg : g ∈ centralizer ({τ} : Set (Perm (Fin n))),
      (∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧ toPermHom τ ⟨g, hg⟩ = π
  w_three : IsPGroup 3 ↥(zpowers w)
  w_comm : w * τ = τ * w
  c_comm : c * τ = τ * c
  w_comm_c : w * c = c * w
  c_sq : c * c = τ
  w_nontriv : ∃ r ∈ R, τ ∈ zpowers ⁅w, r⁆

structure QuatPermDataM (n : ℕ) where
  τ : Perm (Fin n)
  W : Subgroup (Perm (Fin n))
  R : Subgroup (Perm (Fin n))
  O : Subgroup (Perm (Fin n))
  y : Perm (Fin n)
  τ_sq : τ * τ = 1
  τ_ne : τ ≠ 1
  fix_le : fixCount τ ≤ 4
  card_W : Nat.card W = 8
  W_zpowers : ∀ g ∈ W, g ≠ 1 → τ ∈ zpowers g
  W_comm : ∀ g ∈ W, g * τ = τ * g
  W_le_R : W ≤ R
  O_le : O ≤ R
  O_odd : Odd (Nat.card O)
  O_normal : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O
  R_two : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ O
  R_comm : ∀ r ∈ R, r * τ = τ * r
  y_mem : y ∈ R
  y_sq : y * y = τ
  alt_lift : ∀ π ∈ alternatingGroup τ.cycleFactorsFinset, ∃ g : Perm (Fin n),
    ∃ hg : g ∈ centralizer ({τ} : Set (Perm (Fin n))),
      (∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧ toPermHom τ ⟨g, hg⟩ = π

private theorem apply_mem_support_iff_of_comm {n : ℕ} {τ g : Perm (Fin n)}
    (hg : g * τ = τ * g) (x : Fin n) : g x ∈ τ.support ↔ x ∈ τ.support := by
  have h : τ (g x) = g (τ x) := by
    simpa using (congrArg (fun h : Perm (Fin n) => h x) hg).symm
  simp only [Equiv.Perm.mem_support, h]
  exact not_congr g.injective.eq_iff

private theorem card_filter_fixed_modEq {α : Type*} [Fintype α] [DecidableEq α] {S : Finset α}
    {f : Perm α} {p k : ℕ} [Fact p.Prime] (hf : f ^ p ^ k = 1) (hS : ∀ x, f x ∈ S ↔ x ∈ S) :
    (S.filter fun x => f x = x).card ≡ S.card [MOD p] := by
  classical
  set f' : Perm {x // x ∈ S} := f.subtypePerm hS with hf'def
  have hf' : f' ^ p ^ k = 1 := by
    ext x
    rw [hf'def, Equiv.Perm.subtypePerm_pow]
    simp [Equiv.Perm.subtypePerm_apply, hf]
  have h1 := Equiv.Perm.card_compl_support_modEq hf'
  rw [Fintype.card_coe] at h1
  have h2 : f'.supportᶜ.card = (S.filter fun x => f x = x).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext x
    simp only [Finset.mem_map, Finset.mem_compl, Equiv.Perm.mem_support, not_not,
      Function.Embedding.coe_subtype, Finset.mem_filter]
    constructor
    · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
      exact ⟨hy, by simpa [f', Subtype.ext_iff] using hfy⟩
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x, hx⟩, by simp [f', Subtype.ext_iff, hfx], rfl⟩
  rwa [h2] at h1

theorem eight_dvd_card_support {n : ℕ} {τ : Perm (Fin n)} (_hτ : τ ≠ 1)
    {W : Subgroup (Perm (Fin n))} (hW8 : Nat.card W = 8)
    (hWτ : ∀ g ∈ W, g ≠ 1 → τ ∈ zpowers g) (hWc : ∀ g ∈ W, g * τ = τ * g) :
    8 ∣ τ.support.card := by
  classical
  let X := {x : Fin n // x ∈ τ.support}
  letI : MulAction W X :=
    { smul := fun g x =>
        ⟨(g : Perm (Fin n)) x.1, (apply_mem_support_iff_of_comm (hWc g g.2) x.1).2 x.2⟩
      one_smul := fun x => Subtype.ext rfl
      mul_smul := fun g h x => Subtype.ext rfl }
  have hstab : ∀ x : X, MulAction.stabilizer W x = ⊥ := by
    intro x
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    by_contra hg1
    have hg1' : (g : Perm (Fin n)) ≠ 1 := fun h => hg1 (Subtype.ext h)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hWτ g g.2 hg1')
    have hfix : (g : Perm (Fin n)) x.1 = x.1 :=
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hg)
    have h2 : ((g : Perm (Fin n)) ^ j) x.1 = x.1 :=
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix j
    rw [hj] at h2
    exact (Equiv.Perm.mem_support.1 x.2) h2
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod, hW8] at hcard
  have hX : Nat.card X = τ.support.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [← hX, hcard]
  exact dvd_mul_left 8 _

theorem false_of_card_support_eq_eight {n : ℕ} {τ w c r : Perm (Fin n)} (hτ2 : τ * τ = 1)
    (h8 : τ.support.card = 8) (hw3 : IsPGroup 3 ↥(zpowers w)) (hwτ : w * τ = τ * w)
    (hcτ : c * τ = τ * c) (hwc : w * c = c * w) (hcc : c * c = τ) (hrτ : r * τ = τ * r)
    (hwr : τ ∈ zpowers ⁅w, r⁆) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hw3 ⟨w, mem_zpowers w⟩
  have hk' : w ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    simpa using congrArg (fun h : Perm (Fin n) => h x) hτ2
  set F : Finset (Fin n) := τ.support.filter fun x => w x = x with hF
  have hF3 : F.card ≡ 8 [MOD 3] := by
    have := card_filter_fixed_modEq (S := τ.support) hk' (apply_mem_support_iff_of_comm hwτ)
    rwa [h8] at this
  have hFτ : ∀ x, τ x ∈ F ↔ x ∈ F := by
    intro x
    have hwx : w (τ x) = τ (w x) := by
      simpa using congrArg (fun h : Perm (Fin n) => h x) hwτ
    simp only [hF, Finset.mem_filter, Equiv.Perm.apply_mem_support, hwx]
    exact and_congr_right fun _ => τ.injective.eq_iff
  have hF2 : (F.filter fun x => τ x = x).card ≡ F.card [MOD 2] :=
    card_filter_fixed_modEq (p := 2) (k := 1) (by rw [pow_one, sq]; exact hτ2) hFτ
  have hempty : F.filter (fun x => τ x = x) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun x hx => ?_
    exact Equiv.Perm.mem_support.1 (Finset.mem_filter.1 hx).1
  rw [hempty, Finset.card_empty] at hF2
  have hFle : F.card ≤ 8 := h8 ▸ Finset.card_filter_le _ _
  have hcases : F.card = 2 ∨ F.card = 8 := by
    unfold Nat.ModEq at hF3 hF2
    omega
  rcases hcases with h2 | h8'
  · obtain ⟨a, b, hab, hFab⟩ := Finset.card_eq_two.1 h2
    have haF : a ∈ F := by rw [hFab]; simp
    have hna : τ a ≠ a := Equiv.Perm.mem_support.1 (Finset.mem_filter.1 haF).1
    have hτa : τ a = b := by
      have h1 : τ a ∈ F := (hFτ a).2 haF
      rw [hFab] at h1
      simpa [hna] using h1
    have hca : c a ∈ F := by
      simp only [hF, Finset.mem_filter]
      refine ⟨(apply_mem_support_iff_of_comm hcτ a).2 (Finset.mem_filter.1 haF).1, ?_⟩
      have hwa : w a = a := (Finset.mem_filter.1 haF).2
      have : w (c a) = c (w a) := by
        simpa using congrArg (fun h : Perm (Fin n) => h a) hwc
      rw [this, hwa]
    have hcc' : c (c a) = τ a := by
      simpa using congrArg (fun h : Perm (Fin n) => h a) hcc
    have hcτa : c (τ a) = τ (c a) := by
      simpa using congrArg (fun h : Perm (Fin n) => h a) hcτ
    rw [hFab] at hca
    refine hna ?_
    rcases Finset.mem_insert.1 hca with h | h
    · rw [← hcc', h]
      exact h
    · rw [Finset.mem_singleton] at h
      have hca_eq : c a = τ a := by rw [h, hτa]
      calc τ a = c (c a) := hcc'.symm
        _ = c (τ a) := by rw [hca_eq]
        _ = τ (c a) := hcτa
        _ = τ (τ a) := by rw [hca_eq]
        _ = a := hττ a
  · have hFS : F = τ.support :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [h8', h8])
    have hwfix : ∀ x ∈ τ.support, w x = x := fun x hx => by
      have : x ∈ F := hFS ▸ hx
      exact (Finset.mem_filter.1 this).2
    have hr' : r⁻¹ * τ = τ * r⁻¹ := (Commute.inv_left (show Commute r τ from hrτ))
    have hcomm_fix : ∀ x ∈ τ.support, ⁅w, r⁆ x = x := by
      intro x hx
      have h1 : r⁻¹ x ∈ τ.support := (apply_mem_support_iff_of_comm hr' x).2 hx
      have h2 : w⁻¹ (r⁻¹ x) = r⁻¹ x := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact (hwfix _ h1).symm
      have h3 : ⁅w, r⁆ x = w (r (w⁻¹ (r⁻¹ x))) := by
        simp only [commutatorElement_def, Equiv.Perm.mul_apply]
      have h4 : r (r⁻¹ x) = x := Equiv.apply_symm_apply r x
      rw [h3, h2, h4, hwfix x hx]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hwr
    obtain ⟨x, hx⟩ : ∃ x, x ∈ τ.support := Finset.card_pos.1 (by rw [h8]; norm_num)
    have h3 : (⁅w, r⁆ ^ j) x = x :=
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (hcomm_fix x hx) j
    rw [hj] at h3
    exact (Equiv.Perm.mem_support.1 hx) h3

private theorem eq_one_of_commute_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    (h4 : 4 ≤ Fintype.card α) {b : Perm α} (hb : ∀ π ∈ alternatingGroup α, π * b = b * π) :
    b = 1 := by
  ext a
  by_contra hba
  have hba' : b a ≠ a := by simpa using hba
  obtain ⟨x, -, hx⟩ : ∃ x ∈ (Finset.univ : Finset α), x ∉ ({a, b a} : Finset α) :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      calc ({a, b a} : Finset α).card ≤ 2 := Finset.card_le_two
        _ < (Finset.univ : Finset α).card := by rw [Finset.card_univ]; omega)
  obtain ⟨y, -, hy⟩ : ∃ y ∈ (Finset.univ : Finset α), y ∉ ({a, b a, x} : Finset α) :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      calc ({a, b a, x} : Finset α).card ≤ 3 := Finset.card_le_three
        _ < (Finset.univ : Finset α).card := by rw [Finset.card_univ]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hya, hyb, hyx⟩ := hy
  have hgA : swap (b a) x * swap x y ∈ alternatingGroup α := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hxb),
      Equiv.Perm.sign_swap (Ne.symm hyx)]
    decide
  have h1 : swap x y a = a := Equiv.swap_apply_of_ne_of_ne (Ne.symm hxa) (Ne.symm hya)
  have h2 : swap (b a) x a = a := Equiv.swap_apply_of_ne_of_ne (Ne.symm hba') (Ne.symm hxa)
  have h3 : swap x y (b a) = b a := Equiv.swap_apply_of_ne_of_ne (Ne.symm hxb) (Ne.symm hyb)
  have h5 := congrArg (fun h : Perm α => h a) (hb _ hgA)
  simp only [Equiv.Perm.mul_apply, h1, h2] at h5
  rw [h3, Equiv.swap_apply_left] at h5
  exact hxb h5

section AltCycles

variable {n : ℕ} {τ : Perm (Fin n)}

private theorem two_mul_card_cycleFactorsFinset (hτ2 : τ * τ = 1) :
    2 * τ.cycleFactorsFinset.card = τ.support.card := by
  have hpow : τ ^ 2 = 1 := by rw [sq]; exact hτ2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
  have hsum := Equiv.Perm.sum_cycleType τ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk : τ.cycleType.card = τ.cycleFactorsFinset.card := by
    rw [Equiv.Perm.cycleType_def, Multiset.card_map]
    rfl
  rw [hk] at hsum
  omega

private noncomputable def cycImage (τ : Perm (Fin n)) (R : Subgroup (Perm (Fin n))) :
    Subgroup (Perm τ.cycleFactorsFinset) :=
  (R.subgroupOf (centralizer ({τ} : Set (Perm (Fin n))))).map (toPermHom τ)

private theorem mem_cycImage {R : Subgroup (Perm (Fin n))} {b : Perm τ.cycleFactorsFinset} :
    b ∈ cycImage τ R ↔ ∃ r ∈ R, ∃ hr : r ∈ centralizer ({τ} : Set (Perm (Fin n))),
      toPermHom τ ⟨r, hr⟩ = b := by
  simp only [cycImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨r, hr⟩, hrR, rfl⟩
    exact ⟨r, hrR, hr, rfl⟩
  · rintro ⟨r, hrR, hr, rfl⟩
    exact ⟨⟨r, hr⟩, hrR, rfl⟩

private theorem conj_mem_cycImage {R : Subgroup (Perm (Fin n))}
    (halt : ∀ π ∈ alternatingGroup τ.cycleFactorsFinset, ∃ g : Perm (Fin n),
      ∃ hg : g ∈ centralizer ({τ} : Set (Perm (Fin n))),
        (∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧ toPermHom τ ⟨g, hg⟩ = π)
    {π : Perm τ.cycleFactorsFinset} (hπ : π ∈ alternatingGroup τ.cycleFactorsFinset)
    {b : Perm τ.cycleFactorsFinset} (hb : b ∈ cycImage τ R) : π * b * π⁻¹ ∈ cycImage τ R := by
  obtain ⟨r, hrR, hrC, rfl⟩ := mem_cycImage.1 hb
  obtain ⟨g, hgC, hgR, rfl⟩ := halt π hπ
  refine mem_cycImage.2 ⟨g * r * g⁻¹, hgR r hrR, mul_mem (mul_mem hgC hrC) (inv_mem hgC), ?_⟩
  have : (⟨g * r * g⁻¹, mul_mem (mul_mem hgC hrC) (inv_mem hgC)⟩ :
      ↥(centralizer ({τ} : Set (Perm (Fin n))))) = ⟨g, hgC⟩ * ⟨r, hrC⟩ * ⟨g, hgC⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

private theorem alt_le_or_inf_eq_bot {R : Subgroup (Perm (Fin n))}
    (halt : ∀ π ∈ alternatingGroup τ.cycleFactorsFinset, ∃ g : Perm (Fin n),
      ∃ hg : g ∈ centralizer ({τ} : Set (Perm (Fin n))),
        (∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧ toPermHom τ ⟨g, hg⟩ = π)
    (h5 : 5 ≤ Nat.card τ.cycleFactorsFinset) :
    alternatingGroup τ.cycleFactorsFinset ≤ cycImage τ R ∨
      ∀ b ∈ cycImage τ R, b ∈ alternatingGroup τ.cycleFactorsFinset → b = 1 := by
  let N : Subgroup (alternatingGroup τ.cycleFactorsFinset) :=
    (cycImage τ R).subgroupOf (alternatingGroup τ.cycleFactorsFinset)
  haveI : N.Normal := ⟨fun m hm g => by
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact conj_mem_cycImage halt g.2 hm⟩
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top h5 (N := N) with hN | hN
  · right
    intro b hb hbA
    have h1 : (⟨b, hbA⟩ : alternatingGroup τ.cycleFactorsFinset) ∈ N := hb
    rw [hN] at h1
    exact congrArg Subtype.val (Subgroup.mem_bot.1 h1)
  · left
    intro a ha
    have h1 : (⟨a, ha⟩ : alternatingGroup τ.cycleFactorsFinset) ∈ N := by rw [hN]; trivial
    exact h1

private theorem cycImage_eq_one_of_inf_eq_bot {R : Subgroup (Perm (Fin n))}
    (halt : ∀ π ∈ alternatingGroup τ.cycleFactorsFinset, ∃ g : Perm (Fin n),
      ∃ hg : g ∈ centralizer ({τ} : Set (Perm (Fin n))),
        (∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧ toPermHom τ ⟨g, hg⟩ = π)
    (h4 : 4 ≤ Nat.card τ.cycleFactorsFinset)
    (hbot : ∀ b ∈ cycImage τ R, b ∈ alternatingGroup τ.cycleFactorsFinset → b = 1) :
    ∀ b ∈ cycImage τ R, b = 1 := by
  intro b hb
  refine eq_one_of_commute_alternatingGroup (by simpa [Nat.card_eq_fintype_card] using h4)
    fun π hπ => ?_
  have h1 : π * b * π⁻¹ * b⁻¹ ∈ cycImage τ R :=
    mul_mem (conj_mem_cycImage halt hπ hb) (inv_mem hb)
  have h2 : π * b * π⁻¹ * b⁻¹ ∈ alternatingGroup τ.cycleFactorsFinset := by
    have : π * b * π⁻¹ * b⁻¹ = π * (b * π⁻¹ * b⁻¹) := by group
    rw [this]
    exact mul_mem hπ (Subgroup.Normal.conj_mem inferInstance _ (inv_mem hπ) b)
  have h3 := hbot _ h1 h2
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)

private theorem false_of_commute_cycles (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) {y : Perm (Fin n)}
    (hyτ : y * τ = τ * y) (hyy : y * y = τ)
    (hy : ∀ c ∈ τ.cycleFactorsFinset, Commute y c) : False := by
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    simpa using congrArg (fun h : Perm (Fin n) => h x) hτ2
  have hyτ' : ∀ x, y (τ x) = τ (y x) := fun x => by
    simpa using congrArg (fun h : Perm (Fin n) => h x) hyτ
  obtain ⟨x, hx⟩ : ∃ x, τ x ≠ x := by
    by_contra h
    push_neg at h
    exact hτ1 (Equiv.ext h)
  have hcT : swap x (τ x) ∈ τ.cycleFactorsFinset := by
    rw [Equiv.Perm.mem_cycleFactorsFinset_iff]
    refine ⟨Equiv.Perm.isCycle_swap (Ne.symm hx), fun a ha => ?_⟩
    rw [Equiv.Perm.support_swap (Ne.symm hx)] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp
    · simp [hττ]
  have hcomm := congrArg (fun h : Perm (Fin n) => h x) (hy _ hcT).eq
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at hcomm
  have hyx : y x = x ∨ y x = τ x := by
    by_contra hcon
    push_neg at hcon
    have h1 : swap x (τ x) (y x) = y x := Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2
    rw [h1, hyτ'] at hcomm
    have h2 : τ (y x) = y x := hcomm
    have h3 : y x ∈ τ.support :=
      (apply_mem_support_iff_of_comm hyτ x).2 (Equiv.Perm.mem_support.2 hx)
    exact (Equiv.Perm.mem_support.1 h3) h2
  have hyyx : y (y x) = τ x := by
    simpa using congrArg (fun h : Perm (Fin n) => h x) hyy
  apply hx
  rcases hyx with h | h
  · rw [← hyyx, h, h]
  · rw [← hyyx, h, hyτ', h, hττ]

private theorem factorial_div_two_dvd_card_alternatingGroup {α : Type*} [Fintype α]
    [DecidableEq α] {m : ℕ} (hm : 2 ≤ m) (hmt : m ≤ Fintype.card α) :
    m.factorial / 2 ∣ Nat.card (alternatingGroup α) := by
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hmt
  have h2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) hm
  rw [hq, mul_comm, Nat.mul_div_assoc _ h2]
  exact dvd_mul_left _ _

private theorem alt_le_cycImage {R : Subgroup (Perm (Fin n))} (hτ2 : τ * τ = 1)
    (h10 : 10 ≤ τ.support.card) (hRc : ∀ r ∈ R, r * τ = τ * r) {y : Perm (Fin n)} (hyR : y ∈ R)
    (hyy : y * y = τ)
    (halt : ∀ π ∈ alternatingGroup τ.cycleFactorsFinset, ∃ g : Perm (Fin n),
      ∃ hg : g ∈ centralizer ({τ} : Set (Perm (Fin n))),
        (∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧ toPermHom τ ⟨g, hg⟩ = π) :
    alternatingGroup τ.cycleFactorsFinset ≤ cycImage τ R := by
  have h2 := two_mul_card_cycleFactorsFinset hτ2
  have hcard : 5 ≤ Nat.card τ.cycleFactorsFinset := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    omega
  rcases alt_le_or_inf_eq_bot halt hcard with h | h
  · exact h
  · exfalso
    have hall := cycImage_eq_one_of_inf_eq_bot halt (by omega) h
    have hyC : y ∈ centralizer ({τ} : Set (Perm (Fin n))) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hRc y hyR)
    have hy1 : toPermHom τ ⟨y, hyC⟩ = 1 := hall _ (mem_cycImage.2 ⟨y, hyR, hyC, rfl⟩)
    have hker : (⟨y, hyC⟩ : ↥(centralizer ({τ} : Set (Perm (Fin n))))) ∈ (toPermHom τ).ker :=
      hy1
    have hτ1 : τ ≠ 1 := by
      intro h1
      rw [h1] at h10
      simp at h10
    exact false_of_commute_cycles hτ2 hτ1 (hRc y hyR) hyy ((mem_ker_toPermHom_iff τ _).1 hker)

end AltCycles

theorem false_of_alt_cycles {n : ℕ} {τ : Perm (Fin n)} (hτ2 : τ * τ = 1)
    (h16 : 16 ≤ τ.support.card) {R : Subgroup (Perm (Fin n))} (hR16 : ¬ 16 ∣ Nat.card R)
    (hRc : ∀ r ∈ R, r * τ = τ * r) {y : Perm (Fin n)} (hyR : y ∈ R) (hyy : y * y = τ)
    (halt : ∀ π ∈ alternatingGroup τ.cycleFactorsFinset, ∃ g : Perm (Fin n),
      ∃ hg : g ∈ centralizer ({τ} : Set (Perm (Fin n))),
        (∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧ toPermHom τ ⟨g, hg⟩ = π) : False := by
  have hle := alt_le_cycImage hτ2 (by omega) hRc hyR hyy halt
  have h2 := two_mul_card_cycleFactorsFinset hτ2
  apply hR16
  have hRC : R ≤ centralizer ({τ} : Set (Perm (Fin n))) :=
    fun r hr => Subgroup.mem_centralizer_singleton_iff.2 (hRc r hr)
  have h1 : Nat.card (alternatingGroup τ.cycleFactorsFinset) ∣ Nat.card (cycImage τ R) :=
    Subgroup.card_dvd_of_le hle
  have h3 : Nat.card (cycImage τ R) ∣ Nat.card R := by
    have h4 : Nat.card (R.subgroupOf (centralizer ({τ} : Set (Perm (Fin n))))) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
    rw [← h4]
    exact Subgroup.card_map_dvd _ _
  have h4 : 16 ∣ Nat.card (alternatingGroup τ.cycleFactorsFinset) := by
    have h8 : 8 ≤ Fintype.card τ.cycleFactorsFinset := by
      rw [Fintype.card_coe]
      omega
    have := factorial_div_two_dvd_card_alternatingGroup (α := τ.cycleFactorsFinset) (m := 8)
      (by norm_num) h8
    exact (by decide : 16 ∣ Nat.factorial 8 / 2).trans this
  exact h4.trans (h1.trans h3)

theorem false_of_alt_cycles_oddTwo {n : ℕ} {τ : Perm (Fin n)} (hτ2 : τ * τ = 1)
    (h10 : 10 ≤ τ.support.card) {R O : Subgroup (Perm (Fin n))} (hOR : O ≤ R)
    (hOodd : Odd (Nat.card O)) (hOn : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O)
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ O)
    (hRc : ∀ r ∈ R, r * τ = τ * r) {y : Perm (Fin n)} (hyR : y ∈ R) (hyy : y * y = τ)
    (halt : ∀ π ∈ alternatingGroup τ.cycleFactorsFinset, ∃ g : Perm (Fin n),
      ∃ hg : g ∈ centralizer ({τ} : Set (Perm (Fin n))),
        (∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧ toPermHom τ ⟨g, hg⟩ = π) : False := by
  have hle := alt_le_cycImage hτ2 h10 hRc hyR hyy halt
  have h2 := two_mul_card_cycleFactorsFinset hτ2
  have hcard : 5 ≤ Nat.card τ.cycleFactorsFinset := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    omega
  have hRC : R ≤ centralizer ({τ} : Set (Perm (Fin n))) :=
    fun r hr => Subgroup.mem_centralizer_singleton_iff.2 (hRc r hr)
  let N : Subgroup (alternatingGroup τ.cycleFactorsFinset) :=
    (cycImage τ O).subgroupOf (alternatingGroup τ.cycleFactorsFinset)
  haveI : N.Normal := ⟨fun m hm g => by
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨o, hoO, hoC, hom⟩ := mem_cycImage.1 hm
    obtain ⟨r, hrR, hrC, hrg⟩ := mem_cycImage.1 (hle g.2)
    refine mem_cycImage.2 ⟨r * o * r⁻¹, hOn r hrR o hoO,
      mul_mem (mul_mem hrC hoC) (inv_mem hrC), ?_⟩
    have : (⟨r * o * r⁻¹, mul_mem (mul_mem hrC hoC) (inv_mem hrC)⟩ :
        ↥(centralizer ({τ} : Set (Perm (Fin n))))) = ⟨r, hrC⟩ * ⟨o, hoC⟩ * ⟨r, hrC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hrg, hom]
    rfl⟩
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top hcard (N := N) with hN | hN
  · have hA2 : IsPGroup 2 (alternatingGroup τ.cycleFactorsFinset) := by
      intro a
      obtain ⟨r, hrR, hrC, hra⟩ := mem_cycImage.1 (hle a.2)
      obtain ⟨k, hk⟩ := hR2 r hrR
      refine ⟨k, ?_⟩
      have h1 : (a ^ 2 ^ k : alternatingGroup τ.cycleFactorsFinset) ∈ N := by
        rw [Subgroup.mem_subgroupOf]
        refine mem_cycImage.2 ⟨r ^ 2 ^ k, hk, pow_mem hrC _, ?_⟩
        have : (⟨r ^ 2 ^ k, pow_mem hrC _⟩ : ↥(centralizer ({τ} : Set (Perm (Fin n))))) =
            ⟨r, hrC⟩ ^ 2 ^ k := rfl
        rw [this, map_pow, hra, Subgroup.coe_pow]
      rw [hN] at h1
      exact Subgroup.mem_bot.1 h1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e, he⟩ := (IsPGroup.iff_card).1 hA2
    have h3 : 3 ∣ Nat.card (alternatingGroup τ.cycleFactorsFinset) := by
      have := factorial_div_two_dvd_card_alternatingGroup (α := τ.cycleFactorsFinset) (m := 3)
        (by norm_num) (by rw [Fintype.card_coe]; omega)
      exact (by decide : 3 ∣ Nat.factorial 3 / 2).trans this
    rw [he] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · have hAO : alternatingGroup τ.cycleFactorsFinset ≤ cycImage τ O := fun a ha => by
      have h1 : (⟨a, ha⟩ : alternatingGroup τ.cycleFactorsFinset) ∈ N := by rw [hN]; trivial
      exact h1
    have h1 : Nat.card (alternatingGroup τ.cycleFactorsFinset) ∣ Nat.card (cycImage τ O) :=
      Subgroup.card_dvd_of_le hAO
    have h3 : Nat.card (cycImage τ O) ∣ Nat.card O := by
      have h4 : Nat.card (O.subgroupOf (centralizer ({τ} : Set (Perm (Fin n))))) =
          Nat.card O :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOR.trans hRC)).toEquiv
      rw [← h4]
      exact Subgroup.card_map_dvd _ _
    have h4 : 2 ∣ Nat.card (alternatingGroup τ.cycleFactorsFinset) := by
      have := factorial_div_two_dvd_card_alternatingGroup (α := τ.cycleFactorsFinset) (m := 4)
        (by norm_num) (by rw [Fintype.card_coe]; omega)
      exact (by decide : 2 ∣ Nat.factorial 4 / 2).trans this
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 (h4.trans (h1.trans h3)))

theorem QuatPermData.false {n : ℕ} (d : QuatPermData n) : False := by
  have h8 := eight_dvd_card_support d.τ_ne d.card_W d.W_zpowers d.W_comm
  have hpos : 0 < d.τ.support.card := by
    rw [Finset.card_pos, Finset.nonempty_iff_ne_empty, Ne, Equiv.Perm.support_eq_empty_iff]
    exact d.τ_ne
  by_cases h88 : d.τ.support.card = 8
  · obtain ⟨r, hr, hrz⟩ := d.w_nontriv
    exact false_of_card_support_eq_eight d.τ_sq h88 d.w_three d.w_comm d.c_comm d.w_comm_c
      d.c_sq (d.R_comm r hr) hrz
  · obtain ⟨k, hk⟩ := h8
    refine false_of_alt_cycles d.τ_sq (by omega) d.not_dvd_card_R d.R_comm d.y_mem d.y_sq
      d.alt_lift

theorem QuatPermDataM.false {n : ℕ} (d : QuatPermDataM n) (hn : 13 ≤ n) : False := by
  have h8 := eight_dvd_card_support d.τ_ne d.card_W d.W_zpowers d.W_comm
  have hadd := fixCount_add_support d.τ
  have hfix := d.fix_le
  obtain ⟨k, hk⟩ := h8
  exact false_of_alt_cycles_oddTwo d.τ_sq (by omega) d.O_le d.O_odd d.O_normal d.R_two d.R_comm
    d.y_mem d.y_sq d.alt_lift

theorem sign_eq_neg_one_of_transCount_three {n : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (h3 : transCount σ = 3) : sign σ = -1 := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two, hσ]
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk : σ.cycleType.card = 3 := by
    unfold transCount at h3
    omega
  have hs : σ.support.card = 6 := by omega
  rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType, hk, hs]
  decide

end CFSG.OddStandard.Solomon75
