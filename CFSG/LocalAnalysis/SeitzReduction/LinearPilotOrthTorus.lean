module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresTori

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {n : ℕ} {K : Type*} [Field K]

section PairTorus

@[expose] noncomputable def pairTorus (a b : Fin n) : Subgroup (projectiveSL n K) :=
  blockTorus ({a, b} : Finset (Fin n)) ⊓ blockTorus ({a, b}ᶜ : Finset (Fin n))

theorem mem_pairTorus {a b : Fin n} {x : projectiveSL n K} :
    x ∈ pairTorus a b ↔ ∃ d : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      d.1 ∈ blockTorusParam ({a, b} : Finset (Fin n)) ∧
        d.1 ∈ blockTorusParam ({a, b}ᶜ : Finset (Fin n)) ∧ proj n K (torusDiagSL d) = x := by
  constructor
  · rintro ⟨hx₁, hx₂⟩
    obtain ⟨d, hd, rfl⟩ := mem_blockTorus.1 hx₁
    obtain ⟨d', hd', hdd'⟩ := mem_blockTorus.1 hx₂
    obtain ⟨s, hs⟩ := exists_eq_mul_of_proj_torusDiagSL_eq hdd'
    refine ⟨d, hd, ⟨d.2.1, fun i hi j hj => ?_⟩, rfl⟩
    rw [hs i, hs j, hd'.2 i hi j hj]
  · rintro ⟨d, hd₁, hd₂, rfl⟩
    exact ⟨proj_torusDiagSL_mem_blockTorus hd₁, proj_torusDiagSL_mem_blockTorus hd₂⟩

theorem proj_torusDiagSL_mem_pairTorus {a b : Fin n}
    {d : blockTorusParam (K := K) (∅ : Finset (Fin n))}
    (hd₁ : d.1 ∈ blockTorusParam ({a, b} : Finset (Fin n)))
    (hd₂ : d.1 ∈ blockTorusParam ({a, b}ᶜ : Finset (Fin n))) :
    proj n K (torusDiagSL d) ∈ pairTorus a b :=
  mem_pairTorus.2 ⟨d, hd₁, hd₂, rfl⟩

theorem pairTorus_le_blockTorus (a b : Fin n) :
    pairTorus (K := K) a b ≤ blockTorus ({a, b} : Finset (Fin n)) :=
  inf_le_left

theorem pairTorus_le_blockTorus_compl (a b : Fin n) :
    pairTorus (K := K) a b ≤ blockTorus ({a, b}ᶜ : Finset (Fin n)) :=
  inf_le_right

theorem blockTorus_le_centralizer_blockSL (I : Finset (Fin n)) :
    blockTorus (K := K) I ≤
      centralizer (blockSL (K := K) I : Set (projectiveSL n K)) :=
  le_centralizer_iff.1 (blockSL_le_centralizer_blockTorus I)

theorem pairTorus_le_centralizer_blockSL_compl (a b : Fin n) :
    pairTorus (K := K) a b ≤
      centralizer (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) : Set (projectiveSL n K)) :=
  (pairTorus_le_blockTorus_compl a b).trans (blockTorus_le_centralizer_blockSL _)

theorem pairTorus_le_centralizer_blockSL_pair (a b : Fin n) :
    pairTorus (K := K) a b ≤
      centralizer (blockSL (K := K) ({a, b} : Finset (Fin n)) : Set (projectiveSL n K)) :=
  (pairTorus_le_blockTorus a b).trans (blockTorus_le_centralizer_blockSL _)

theorem pairTorus_le_centralizer_rootGroup {a b : Fin n} (hab : a ≠ b) :
    pairTorus (K := K) a b ≤ centralizer (rootGroup (K := K) hab : Set (projectiveSL n K)) :=
  (pairTorus_le_centralizer_blockSL_pair a b).trans
    (centralizer_le (rootGroup_le_blockSL hab (by simp) (by simp)))

theorem pairTorus_le_centralizer_xab {a b : Fin n} (hab : a ≠ b) (c : K) :
    pairTorus (K := K) a b ≤ centralizer ({xab hab c} : Set (projectiveSL n K)) :=
  (pairTorus_le_centralizer_rootGroup hab).trans
    (centralizer_le (Set.singleton_subset_iff.2 (xab_mem_rootGroup hab c)))

end PairTorus

section Radical

theorem InvPlacement.torusDiagSL_mem_parabolic {k : ℕ} (P : InvPlacement n k)
    (d : blockTorusParam (K := K) (∅ : Finset (Fin n))) : torusDiagSL d ∈ P.parabolic K := by
  intro i j hij
  have hne : i ≠ j := by
    rintro rfl
    exact lt_irrefl _ hij
  exact torusDiagSL_apply_of_ne d hne

theorem InvPlacement.blockTorus_le_normalizer_radicalP {k : ℕ} (P : InvPlacement n k)
    (I : Finset (Fin n)) :
    blockTorus (K := K) I ≤ normalizer (P.radicalP K : Set (projectiveSL n K)) := by
  intro x hx
  obtain ⟨d, -, rfl⟩ := mem_blockTorus.1 hx
  exact Subgroup.le_normalizer_map (proj n K)
    ⟨torusDiagSL d, P.parabolic_le_normalizer_radical (P.torusDiagSL_mem_parabolic d), rfl⟩

theorem pairTorus_le_normalizer_radicalP {a b : Fin n} (hab : a ≠ b) :
    pairTorus (K := K) a b ≤
      normalizer ((pairPlacement hab).radicalP K : Set (projectiveSL n K)) :=
  (pairTorus_le_blockTorus a b).trans ((pairPlacement hab).blockTorus_le_normalizer_radicalP _)

theorem transvection_mem_radical_pairPlacement {a b : Fin n} (hab : a ≠ b) (c : K) :
    SpecialLinearGroup.transvection hab c ∈ (pairPlacement hab).radical K := by
  intro i j hij
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply, ite_eq_right, add_zero]
  rintro ⟨rfl, rfl⟩
  rw [pairPlacement_level_left, pairPlacement_level_right] at hij
  omega

theorem rootGroup_le_radicalP {a b : Fin n} (hab : a ≠ b) :
    rootGroup (K := K) hab ≤ (pairPlacement hab).radicalP K := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootGroup hab).1 hx
  exact ⟨_, transvection_mem_radical_pairPlacement hab c, rfl⟩

theorem pairPlacement_outer {a b : Fin n} (hab : a ≠ b) :
    (pairPlacement hab).outer = ({a, b} : Finset (Fin n)) := by
  ext i
  rw [InvPlacement.mem_outer, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨s | s, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Sum.inl 0, rfl⟩
    · exact ⟨Sum.inr 0, rfl⟩

theorem eq_transvection_of_mem_radical_of_mem_blockSpecialLinear {a b : Fin n} (hab : a ≠ b)
    {r : SpecialLinearGroup (Fin n) K} (hr : r ∈ (pairPlacement hab).radical K)
    (hr' : r ∈ blockSpecialLinear ({a, b} : Finset (Fin n))) :
    r = SpecialLinearGroup.transvection hab ((r : Matrix (Fin n) (Fin n) K) a b) := by
  ext i j
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [one_apply_ne hab, zero_add, ite_eq_left ⟨rfl, rfl⟩]
  · rw [ite_eq_right h, add_zero]
    by_cases hij : i ∈ ({a, b} : Finset (Fin n)) ∧ j ∈ ({a, b} : Finset (Fin n))
    · obtain ⟨hi, hj⟩ := hij
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      refine hr i j ?_
      rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst hi hj
      · exact le_rfl
      · exact absurd ⟨rfl, rfl⟩ h
      · rw [pairPlacement_level_left, pairPlacement_level_right]
        omega
      · exact le_rfl
    · exact hr' i j (not_and_or.1 hij)

theorem rootGroup_eq_commutator_radicalP {a b : Fin n} (hab : a ≠ b) (hn : 3 ≤ n) :
    rootGroup (K := K) hab =
      ⁅(pairPlacement hab).radicalP K, (pairPlacement hab).radicalP K⁆ := by
  have hJ : (pairPlacement hab).free.Nonempty := by
    rw [pairPlacement_free, ← Finset.card_pos, Finset.card_compl, Finset.card_pair hab,
      Fintype.card_fin]
    omega
  rw [InvPlacement.radicalP, ← Subgroup.map_commutator]
  apply le_antisymm
  · intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup hab).1 hx
    exact ⟨_, (pairPlacement hab).transvection_u_w_mem_commutator hJ 0 0 c, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    have hrR : r ∈ (pairPlacement hab).radical K :=
      (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)) hr
    have hrB := (pairPlacement hab).commutator_radical_le hr
    rw [pairPlacement_outer] at hrB
    rw [eq_transvection_of_mem_radical_of_mem_blockSpecialLinear hab hrR hrB]
    exact xab_mem_rootGroup hab _

theorem proj_torusDiagSL_mem_centralizer_rootGroup {a b : Fin n} (hab : a ≠ b)
    {d : blockTorusParam (K := K) (∅ : Finset (Fin n))} (hd : d.1 a = d.1 b) :
    proj n K (torusDiagSL d) ∈
      centralizer (rootGroup (K := K) hab : Set (projectiveSL n K)) := by
  have hd' : d.1 ∈ blockTorusParam ({a, b} : Finset (Fin n)) := ⟨d.2.1, fun i hi j hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    exacts [rfl, hd, hd.symm, rfl]⟩
  exact blockTorus_le_centralizer_blockSL _ (proj_torusDiagSL_mem_blockTorus hd')
    |> fun h => centralizer_le (rootGroup_le_blockSL hab (by simp) (by simp)) h

theorem eq_transvection_of_mem_radical_of_commute {a b : Fin n} (hab : a ≠ b)
    {r : SpecialLinearGroup (Fin n) K} (hr : r ∈ (pairPlacement hab).radical K) {d : Fin n → K}
    (hdab : d a = d b) (hsep : ∀ j, j ≠ a → j ≠ b → d j ≠ d a)
    (hcomm : ∀ i j, d i * (r : Matrix (Fin n) (Fin n) K) i j =
      (r : Matrix (Fin n) (Fin n) K) i j * d j) :
    r = SpecialLinearGroup.transvection hab ((r : Matrix (Fin n) (Fin n) K) a b) := by
  have hzero : ∀ i j, d i ≠ d j → (r : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro i j hij
    have h := hcomm i j
    have h' : (r : Matrix (Fin n) (Fin n) K) i j * (d i - d j) = 0 := by
      linear_combination h
    exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 hij)
  ext i j
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply]
  by_cases hia : i = a
  · subst hia
    by_cases hjb : j = b
    · subst hjb
      rw [one_apply_ne hab, zero_add, ite_eq_left ⟨rfl, rfl⟩]
    · rw [ite_eq_right (fun h => hjb h.2.symm), add_zero]
      by_cases hja : j = i
      · subst hja
        exact hr _ _ le_rfl
      · rw [one_apply_ne (Ne.symm hja)]
        exact hzero _ _ fun h => hsep j hja hjb h.symm
  · rw [ite_eq_right (fun h => hia h.1.symm), add_zero]
    by_cases hib : i = b
    · subst hib
      exact hr _ _ (by rw [pairPlacement_level_right]; exact InvPlacement.level_le_two _ _)
    · by_cases hjb : j = b
      · subst hjb
        rw [one_apply_ne hib]
        exact hzero _ _ fun h => hsep i hia hib (h.trans hdab.symm)
      · refine hr _ _ ?_
        rw [pairPlacement_level_of_ne hab hia hib]
        by_cases hja : j = a
        · subst hja
          rw [pairPlacement_level_left]
          omega
        · rw [pairPlacement_level_of_ne hab hja hjb]

theorem radicalP_inf_centralizer_eq_rootGroup {a b : Fin n} (hab : a ≠ b)
    {d : blockTorusParam (K := K) (∅ : Finset (Fin n))} (hdab : d.1 a = d.1 b)
    (hsep : ∀ j, j ≠ a → j ≠ b → d.1 j ≠ d.1 a) :
    (pairPlacement hab).radicalP K ⊓
        centralizer ({proj n K (torusDiagSL d)} : Set (projectiveSL n K)) =
      rootGroup hab := by
  apply le_antisymm
  · rintro x ⟨⟨r, hr, rfl⟩, hx⟩
    have hx' := mem_centralizer_singleton_iff.1 hx
    rw [← map_mul, ← map_mul, proj_eq_proj_iff] at hx'
    obtain ⟨s, -, hs⟩ := mem_scalars.1 hx'
    obtain ⟨w, hw⟩ : ∃ w, w = (r * torusDiagSL d)⁻¹ * (torusDiagSL d * r) := ⟨_, rfl⟩
    rw [← hw] at hs
    have h2 : torusDiagSL d * r = r * torusDiagSL d * w := by rw [hw]; group
    have hentry : ∀ i j, (d.1 i : K) * (r : Matrix (Fin n) (Fin n) K) i j =
        (r : Matrix (Fin n) (Fin n) K) i j * (d.1 j : K) * (s : K) := by
      intro i j
      have h3 := congrArg
        (fun X : SpecialLinearGroup (Fin n) K => (X : Matrix (Fin n) (Fin n) K) i j) h2
      simp only [Matrix.SpecialLinearGroup.coe_mul] at h3
      rwa [hs, coe_torusDiagSL, diagonal_mul, scalar_apply, mul_diagonal, mul_diagonal] at h3
    have hraa : (r : Matrix (Fin n) (Fin n) K) a a = 1 := (hr a a le_rfl).trans (one_apply_eq a)
    have hs1 : (s : K) = 1 := by
      have h := hentry a a
      rw [hraa, mul_one, one_mul] at h
      exact mul_left_cancel₀ (Units.ne_zero (d.1 a)) (h.symm.trans (mul_one _).symm)
    have hcomm : ∀ i j, (d.1 i : K) * (r : Matrix (Fin n) (Fin n) K) i j =
        (r : Matrix (Fin n) (Fin n) K) i j * (d.1 j : K) := fun i j => by
      rw [hentry i j, hs1, mul_one]
    rw [eq_transvection_of_mem_radical_of_commute hab hr (d := fun i => (d.1 i : K))
      (congrArg Units.val hdab) (fun j hja hjb h => hsep j hja hjb (Units.ext h)) hcomm]
    exact xab_mem_rootGroup hab _
  · exact le_inf (rootGroup_le_radicalP hab) fun x hx =>
      mem_centralizer_singleton_iff.2
        ((mem_centralizer_iff.1 (proj_torusDiagSL_mem_centralizer_rootGroup hab hdab)) x hx)

end Radical

section Separating

@[expose] def pairTorusParam (a b : Fin n) (κ : Kˣ) : Fin n → Kˣ :=
  fun i => if i = a ∨ i = b then κ⁻¹ ^ (n - 2) else κ ^ 2

theorem pairTorusParam_left (a b : Fin n) (κ : Kˣ) : pairTorusParam a b κ a = κ⁻¹ ^ (n - 2) :=
  ite_eq_left (Or.inl rfl)

theorem pairTorusParam_right (a b : Fin n) (κ : Kˣ) : pairTorusParam a b κ b = κ⁻¹ ^ (n - 2) :=
  ite_eq_left (Or.inr rfl)

theorem pairTorusParam_of_ne {a b i : Fin n} (hia : i ≠ a) (hib : i ≠ b) (κ : Kˣ) :
    pairTorusParam a b κ i = κ ^ 2 :=
  ite_eq_right (by rintro (h | h) <;> contradiction)

theorem pairTorusParam_of_mem {a b i : Fin n} (hi : i ∈ ({a, b} : Finset (Fin n))) (κ : Kˣ) :
    pairTorusParam a b κ i = κ⁻¹ ^ (n - 2) :=
  ite_eq_left (by simpa using hi)

theorem pairTorusParam_of_mem_compl {a b i : Fin n} (hi : i ∈ ({a, b}ᶜ : Finset (Fin n)))
    (κ : Kˣ) : pairTorusParam a b κ i = κ ^ 2 :=
  ite_eq_right (by simpa using hi)

theorem prod_pairTorusParam {a b : Fin n} (hab : a ≠ b) (κ : Kˣ) :
    ∏ i, pairTorusParam a b κ i = 1 := by
  rw [← Finset.prod_mul_prod_compl ({a, b} : Finset (Fin n)), Finset.prod_pair hab,
    pairTorusParam_left, pairTorusParam_right,
    Finset.prod_congr rfl (g := fun _ => κ ^ 2) fun i hi => pairTorusParam_of_mem_compl hi κ,
    Finset.prod_const, Finset.card_compl, Finset.card_pair hab, Fintype.card_fin, ← mul_pow,
    ← mul_pow]
  have h : κ⁻¹ * κ⁻¹ * κ ^ 2 = 1 := by group
  rw [h, one_pow]

theorem pairTorusParam_mem_pair {a b : Fin n} (hab : a ≠ b) (κ : Kˣ) :
    pairTorusParam a b κ ∈ blockTorusParam ({a, b} : Finset (Fin n)) :=
  ⟨prod_pairTorusParam hab κ, fun i hi j hj => by
    rw [pairTorusParam_of_mem hi, pairTorusParam_of_mem hj]⟩

theorem pairTorusParam_mem_compl {a b : Fin n} (hab : a ≠ b) (κ : Kˣ) :
    pairTorusParam a b κ ∈ blockTorusParam ({a, b}ᶜ : Finset (Fin n)) :=
  ⟨prod_pairTorusParam hab κ, fun i hi j hj => by
    rw [pairTorusParam_of_mem_compl hi, pairTorusParam_of_mem_compl hj]⟩

theorem pairTorusParam_ne {a b : Fin n} (hab : a ≠ b) {κ : Kˣ} (hκ : κ ^ n ≠ 1) {j : Fin n}
    (hja : j ≠ a) (hjb : j ≠ b) : pairTorusParam a b κ j ≠ pairTorusParam a b κ a := by
  have hn : 2 ≤ n := by
    have h1 := Finset.card_le_univ ({a, b} : Finset (Fin n))
    rw [Finset.card_pair hab, Fintype.card_fin] at h1
    exact h1
  rw [pairTorusParam_of_ne hja hjb, pairTorusParam_left]
  intro h
  apply hκ
  have h' : κ ^ 2 * κ ^ (n - 2) = 1 := by rw [h, inv_pow, inv_mul_cancel]
  rwa [← pow_add, Nat.add_sub_cancel' hn] at h'

theorem exists_pairTorus_centralizer_radical_eq (hκ : ∃ κ : Kˣ, κ ^ n ≠ 1) {a b : Fin n}
    (hab : a ≠ b) :
    ∃ y ∈ pairTorus (K := K) a b,
      (pairPlacement hab).radicalP K ⊓ centralizer ({y} : Set (projectiveSL n K)) =
        rootGroup hab := by
  obtain ⟨κ, hκ⟩ := hκ
  set d : blockTorusParam (K := K) (∅ : Finset (Fin n)) :=
    ⟨pairTorusParam a b κ, blockTorusParam_le_empty _ (pairTorusParam_mem_pair hab κ)⟩
  refine ⟨proj n K (torusDiagSL d),
    proj_torusDiagSL_mem_pairTorus (pairTorusParam_mem_pair hab κ)
      (pairTorusParam_mem_compl hab κ), ?_⟩
  exact radicalP_inf_centralizer_eq_rootGroup hab
    ((pairTorusParam_left a b κ).trans (pairTorusParam_right a b κ).symm)
    fun j hja hjb => pairTorusParam_ne hab hκ hja hjb

end Separating

section Odd

theorem pow_card_sub_one_eq_one_of_mem_blockTorus [Finite K] {I : Finset (Fin n)}
    {x : projectiveSL n K} (hx : x ∈ blockTorus I) : x ^ (Nat.card K - 1) = 1 := by
  obtain ⟨d, -, rfl⟩ := mem_blockTorus.1 hx
  rw [← map_pow, ← map_pow]
  have hd : d ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    funext i
    rw [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply, ← Nat.card_units,
      pow_card_eq_one']
  rw [hd, map_one, map_one]

theorem odd_card_sub_one_of_charTwo [Finite K] [CharP K 2] : Odd (Nat.card K - 1) := by
  have := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hm]
  have hpos : 0 < (m : ℕ) := m.pos
  have heven : Even (2 ^ (m : ℕ)) := (Nat.even_pow' hpos.ne').2 even_two
  have h1 : 1 ≤ 2 ^ (m : ℕ) := Nat.one_le_two_pow
  exact Nat.Even.sub_odd h1 heven odd_one

end Odd

end CFSG.SeitzReduction.LinearPilot
