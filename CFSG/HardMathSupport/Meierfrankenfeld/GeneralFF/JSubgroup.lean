module

public import CFSG.RankThree.FFModules.ElemBestOffender

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules
open scoped commutatorElement

section Defs

variable {X : Type*} [Group X] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def bestOffenderSub (ρ : Representation (ZMod 2) X W) : Subgroup X :=
  ⨆ (A : Subgroup X) (_ : IsElemBestOffender ρ A), A

@[expose] def IsJComponent (J K : Subgroup X) : Prop :=
  K ≤ J ∧ K ≠ ⊥ ∧ ⁅K, J⁆ = K ∧
    ∀ K₁ : Subgroup X, K₁ ≤ K → K₁ ≠ ⊥ → ⁅K₁, J⁆ = K₁ → K₁ = K

theorem le_bestOffenderSub {ρ : Representation (ZMod 2) X W} {A : Subgroup X}
    (hA : CFSG.IsElementaryAbelian 2 A) (hb : IsBestOffender ρ A) :
    A ≤ bestOffenderSub ρ :=
  le_iSup₂_of_le A ⟨hA, hb⟩ le_rfl

theorem bestOffenderSub_le {ρ : Representation (ZMod 2) X W} {C : Subgroup X}
    (h : ∀ A : Subgroup X, CFSG.IsElementaryAbelian 2 A → IsBestOffender ρ A → A ≤ C) :
    bestOffenderSub ρ ≤ C :=
  iSup₂_le fun A hA => h A hA.1 hA.2

theorem bestOffenderSub_normal (ρ : Representation (ZMod 2) X W) :
    (bestOffenderSub ρ).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : bestOffenderSub ρ ≤ (bestOffenderSub ρ).comap (MulAut.conj g).toMonoidHom := by
    refine bestOffenderSub_le fun A hA hb => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨hA', hb'⟩ := IsElemBestOffender.conj ⟨hA, hb⟩ g
    exact le_bestOffenderSub hA' hb'
  exact hle hn

theorem bestOffenderSub_eq_iSup_ne_bot (ρ : Representation (ZMod 2) X W) :
    bestOffenderSub ρ = ⨆ (A : Subgroup X) (_ : A ≠ ⊥ ∧ IsElemBestOffender ρ A), A := by
  refine le_antisymm (bestOffenderSub_le fun A hA hb => ?_)
    (iSup₂_le fun A hA => le_bestOffenderSub hA.2.1 hA.2.2)
  by_cases h : A = ⊥
  · exact (le_of_eq h).trans bot_le
  · exact le_iSup₂_of_le A ⟨h, hA, hb⟩ le_rfl

theorem bestOffenderSub_eq_normalClosure (ρ : Representation (ZMod 2) X W) :
    bestOffenderSub ρ =
      Subgroup.normalClosure (⋃ (A : Subgroup X) (_ : IsElemBestOffender ρ A), (A : Set X)) := by
  have hS : (⋃ (A : Subgroup X) (_ : IsElemBestOffender ρ A), (A : Set X)) ⊆ bestOffenderSub ρ := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨A, hA, hxA⟩ := hx
    exact le_bestOffenderSub hA.1 hA.2 hxA
  refine le_antisymm (bestOffenderSub_le fun A hA hb x hx => ?_) ?_
  · exact Subgroup.subset_normalClosure (Set.mem_biUnion (x := A) ⟨hA, hb⟩ hx)
  · have := bestOffenderSub_normal ρ
    exact Subgroup.normalClosure_le_normal hS

theorem commutator_conj_mem {J K : Subgroup X} {x y : X} (hx : x ∈ J)
    (hy : y ∈ ⁅K, J⁆) : x * y * x⁻¹ ∈ ⁅K, J⁆ := by
  have h : ⁅K, J⁆ ≤ (⁅K, J⁆).comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro k hk j hj
    have key : x * ⁅k, j⁆ * x⁻¹ = ⁅k, x⁆⁻¹ * ⁅k, x * j⁆ := by
      simp only [commutatorElement_def]
      group
    change (MulAut.conj x) ⁅k, j⁆ ∈ ⁅K, J⁆
    rw [MulAut.conj_apply, key]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hk hx))
      (Subgroup.commutator_mem_commutator hk (Subgroup.mul_mem _ hx hj))
  have := h hy
  simpa [MulAut.conj_apply] using this

end Defs

section TwoElements

variable {X : Type*} [Group X]

theorem comm_pow_of_commute {y t z : X} (hz : ⁅y, t⁆ = z) (hzt : z * t = t * z) (m : ℕ) :
    ⁅y, t ^ m⁆ = z ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : Commute t (z ^ m) := Commute.pow_right (Commute.symm hzt) m
    have h1 : t * z ^ m * t⁻¹ = z ^ m := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc.eq
    have h2 : ⁅y, t * t ^ m⁆ = ⁅y, t⁆ * (t * ⁅y, t ^ m⁆ * t⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [pow_succ', h2, hz, ih, h1, pow_succ']

theorem eq_one_of_central_two_power {J : Subgroup X} (hJ : J.Normal)
    (hX : CFSG.pCore 2 X = ⊥) {z : X} (hz : z ∈ J) (hc : ∀ j ∈ J, z * j = j * z)
    (hn : ∃ n : ℕ, z ^ (2 ^ n) = 1) : z = 1 := by
  let Q : X → Prop := fun w => w ∈ J ∧ (∀ j ∈ J, w * j = j * w) ∧ ∃ n : ℕ, w ^ (2 ^ n) = 1
  have hQ : ∀ w ∈ Subgroup.normalClosure ({z} : Set X), Q w := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ => Q w) ?_ ?_ ?_ ?_ hw
    · intro x hx
      obtain ⟨n, hn⟩ := hn
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      have haz : a = z := ha
      rw [haz] at hconj
      obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
      refine ⟨?_, ?_, n, ?_⟩
      · have := hJ.conj_mem z hz g
        simpa using this
      · intro j hj
        have hj' : g⁻¹ * j * g ∈ J := by
          have := hJ.conj_mem j hj g⁻¹
          simpa using this
        have := hc _ hj'
        calc g * z * g⁻¹ * j = g * (z * (g⁻¹ * j * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * j * g) * z) * g⁻¹ := by rw [this]
          _ = j * (g * z * g⁻¹) := by group
      · have : (g * z * g⁻¹) ^ (2 ^ n) = g * z ^ (2 ^ n) * g⁻¹ := by
          rw [conj_pow]
        rw [this, hn]
        simp
    · exact ⟨J.one_mem, fun j _ => by simp, 0, by simp⟩
    · rintro x y - - ⟨hxJ, hxc, n, hn⟩ ⟨hyJ, hyc, m, hm⟩
      refine ⟨J.mul_mem hxJ hyJ, fun j hj => ?_, n + m, ?_⟩
      · rw [mul_assoc, hyc j hj, ← mul_assoc, hxc j hj, mul_assoc]
      · have hcomm : Commute x y := hxc y hyJ
        have h1 : x ^ (2 ^ (n + m)) = 1 := by rw [pow_add, pow_mul, hn, one_pow]
        have h2 : y ^ (2 ^ (n + m)) = 1 := by
          rw [pow_add, mul_comm (2 ^ n), pow_mul, hm, one_pow]
        rw [hcomm.mul_pow, h1, h2, one_mul]
    · rintro x - ⟨hxJ, hxc, n, hn⟩
      refine ⟨J.inv_mem hxJ, fun j hj => ?_, n, ?_⟩
      · have := hxc j hj
        calc x⁻¹ * j = x⁻¹ * (j * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * j) * x⁻¹ := by rw [← this]
          _ = j * x⁻¹ := by group
      · rw [inv_pow, hn, inv_one]
  have hP : IsPGroup 2 (Subgroup.normalClosure ({z} : Set X)) := fun g => by
    obtain ⟨-, -, n, hn⟩ := hQ g.1 g.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hle : Subgroup.normalClosure ({z} : Set X) ≤ CFSG.pCore 2 X :=
    le_sSup ⟨inferInstance, hP⟩
  rw [hX] at hle
  have : z ∈ (⊥ : Subgroup X) := hle (Subgroup.subset_normalClosure rfl)
  simpa using this

theorem commutes_of_two_power_commutators {J : Subgroup X} (hJ : J.Normal)
    (hX : CFSG.pCore 2 X = ⊥)
    (hgen : ∀ C : Subgroup X, (∀ j ∈ J, (∃ n : ℕ, j ^ (2 ^ n) = 1) → j ∈ C) → J ≤ C)
    {Y : Set X}
    (hY : ∀ y ∈ Y, ∀ j ∈ J, ⁅y, j⁆ ∈ J ∧ ∀ j' ∈ J, ⁅y, j⁆ * j' = j' * ⁅y, j⁆) :
    ∀ y ∈ Y, ∀ j ∈ J, ⁅y, j⁆ = 1 := by
  intro y hy
  have hle : J ≤ Subgroup.centralizer ({y} : Set X) := by
    refine hgen _ fun t ht ⟨n, hn⟩ => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    obtain ⟨hzJ, hzc⟩ := hY h hy t ht
    have hz1 : ⁅h, t⁆ = 1 := by
      refine eq_one_of_central_two_power hJ hX hzJ (fun j hj => hzc j hj) ⟨n, ?_⟩
      rw [← comm_pow_of_commute rfl (hzc t ht) (2 ^ n), hn]
      simp
    have : h * t * h⁻¹ * t⁻¹ = 1 := by simpa [commutatorElement_def] using hz1
    calc h * t = (h * t * h⁻¹ * t⁻¹) * (t * h) := by group
      _ = t * h := by rw [this, one_mul]
  intro j hj
  have := Subgroup.mem_centralizer_iff.mp (hle hj) y rfl
  have h2 : y * j * y⁻¹ * j⁻¹ = 1 := by
    calc y * j * y⁻¹ * j⁻¹ = (j * y) * y⁻¹ * j⁻¹ := by rw [this]
      _ = 1 := by group
  simpa [commutatorElement_def] using h2

theorem commutator_eq_one_iff {a b : X} : ⁅a, b⁆ = 1 ↔ a * b = b * a := by
  constructor
  · intro h
    have h' : a * b * a⁻¹ * b⁻¹ = 1 := by simpa [commutatorElement_def] using h
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h', one_mul]
  · intro h
    simp only [commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [h]
      _ = 1 := by group

theorem commutator_eq_bot_iff {K J : Subgroup X} :
    ⁅K, J⁆ = ⊥ ↔ ∀ k ∈ K, ∀ j ∈ J, ⁅k, j⁆ = 1 := by
  rw [← le_bot_iff, Subgroup.commutator_le]
  simp

theorem exists_jComponent_le [Finite X] {J N : Subgroup X} (hJ : J.Normal)
    (hX : CFSG.pCore 2 X = ⊥)
    (hgen : ∀ C : Subgroup X, (∀ j ∈ J, (∃ n : ℕ, j ^ (2 ^ n) = 1) → j ∈ C) → J ≤ C)
    (hNJ : N ≤ J) (hNn : ∀ j ∈ J, ∀ k ∈ N, j * k * j⁻¹ ∈ N) (hne : ⁅N, J⁆ ≠ ⊥) :
    ∃ K : Subgroup X, IsJComponent J K ∧ K ≤ N := by
  classical
  let S : Set (Subgroup X) :=
    {K | K ≤ N ∧ (∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K) ∧ ⁅K, J⁆ ≠ ⊥}
  have hSne : S.Nonempty := ⟨N, le_rfl, hNn, hne⟩
  obtain ⟨K, hKS, hmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min S hSne
  obtain ⟨hKN, hKn, hKne⟩ := hKS
  have hKJ : K ≤ J := hKN.trans hNJ
  have hbot : ∀ {K' : Subgroup X}, ⁅K', J⁆ = ⊥ ↔ ∀ k ∈ K', ∀ j ∈ J, ⁅k, j⁆ = 1 :=
    commutator_eq_bot_iff
  have hKK : ⁅K, J⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk j hj
    have : ⁅k, j⁆ = k * (j * k⁻¹ * j⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact K.mul_mem hk (hKn j hj k⁻¹ (K.inv_mem hk))
  have hKeq : ⁅K, J⁆ = K := by
    refine le_antisymm hKK ?_
    by_contra hlt
    have hlt' : ⁅K, J⁆ < K := lt_of_le_of_ne hKK (fun h => hlt (le_of_eq h.symm))
    have hK1n : ∀ j ∈ J, ∀ k ∈ ⁅K, J⁆, j * k * j⁻¹ ∈ ⁅K, J⁆ := fun j hj k hk =>
      commutator_conj_mem hj hk
    have hK1 : ⁅⁅K, J⁆, J⁆ = ⊥ := by
      by_contra hne1
      exact hmin ⁅K, J⁆ ⟨hKK.trans hKN, hK1n, hne1⟩ hlt'
    rw [hbot] at hK1
    have hcomm := commutes_of_two_power_commutators (J := J) (Y := (K : Set X)) hJ hX hgen
      (fun y hy j hj => ⟨hKJ (hKK (Subgroup.commutator_mem_commutator hy hj)),
        fun j' hj' => (commutator_eq_one_iff.mp
          (hK1 _ (Subgroup.commutator_mem_commutator hy hj) j' hj'))⟩)
    exact hKne ((hbot).mpr fun k hk j hj => hcomm k hk j hj)
  refine ⟨K, ⟨hKJ, ?_, hKeq, ?_⟩, hKN⟩
  · rintro rfl
    exact hKne (by simp)
  · intro K₁ hK₁K hK₁bot hK₁eq
    have hK₁n : ∀ j ∈ J, ∀ k ∈ K₁, j * k * j⁻¹ ∈ K₁ := fun j hj k hk => by
      rw [← hK₁eq] at hk ⊢
      exact commutator_conj_mem hj hk
    have hK₁S : K₁ ∈ S := ⟨hK₁K.trans hKN, hK₁n, by rwa [hK₁eq]⟩
    by_contra hne'
    exact hmin K₁ hK₁S (lt_of_le_of_ne hK₁K hne')

end TwoElements

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
