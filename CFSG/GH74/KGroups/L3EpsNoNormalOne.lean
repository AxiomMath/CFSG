module

public import CFSG.GH74.KGroups.L3EpsLinAut

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

section Omega

variable {F : Type} [Field F]

theorem entryMap_pow_aux (σ : F ≃+* F) (ε : ℕ) (w : F) (n : ℕ) :
    entryMap σ ε (w ^ n) = entryMap σ ε w ^ n := by
  induction n with
  | zero => simp [entryMap_one]
  | succ n ih => rw [pow_succ, entryMap_mul, ih, pow_succ]

theorem entryMap_inv_aux (σ : F ≃+* F) (ε : ℕ) (x : F) : entryMap σ ε x⁻¹ = (entryMap σ ε x)⁻¹ := by
  unfold entryMap
  split_ifs
  · exact map_inv₀ σ x
  · rw [map_inv₀, inv_inv]

theorem exists_neg_of_moved (σ : F ≃+* F) (ε : ℕ) {w : F} {N : ℕ} (hw : w ^ (2 ^ N) = 1)
    (hmv : entryMap σ ε w ≠ w) :
    ∃ u : F, u ≠ 0 ∧ u ^ (2 ^ N) = 1 ∧ entryMap σ ε u = -u := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  set t : F := entryMap σ ε w * w⁻¹ with ht
  have ht1 : t ≠ 1 := by
    intro h
    apply hmv
    have : entryMap σ ε w = w := by
      calc entryMap σ ε w = (entryMap σ ε w * w⁻¹) * w := by field_simp
        _ = w := by rw [← ht, h, one_mul]
    exact this
  have htN : t ^ (2 ^ N) = 1 := by
    rw [ht, mul_pow, ← entryMap_pow_aux, hw, entryMap_one, inv_pow, hw]
    simp
  have hord : orderOf t ∣ 2 ^ N := orderOf_dvd_of_pow_eq_one htN
  obtain ⟨e, he, hoe⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at hoe
    exact ht1 hoe
  set s : F := t ^ (2 ^ (e - 1)) with hs
  have hs2 : s * s = 1 := by
    rw [hs, ← pow_add, ← two_mul, ← pow_succ']
    have : e - 1 + 1 = e := by omega
    rw [this, ← hoe]
    exact pow_orderOf_eq_one t
  have hs1 : s ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hoe] at this
    have h3 : 2 ^ e ≤ 2 ^ (e - 1) := Nat.le_of_dvd (by positivity) this
    have h4 : 2 ^ (e - 1) < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hsm : s = -1 := by
    rcases mul_self_eq_one_iff.1 hs2 with h | h
    · exact absurd h hs1
    · exact h
  refine ⟨w ^ (2 ^ (e - 1)), pow_ne_zero _ hw0, ?_, ?_⟩
  · calc (w ^ (2 ^ (e - 1))) ^ (2 ^ N) = (w ^ (2 ^ N)) ^ (2 ^ (e - 1)) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [hw, one_pow]
  · rw [entryMap_pow_aux]
    have : entryMap σ ε w = t * w := by rw [ht]; field_simp
    rw [this, mul_pow, ← hs, hsm]
    ring

end Omega

section Final

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem bracket_eInv2 {σ : F ≃+* F} {ε : ℕ} (α : MulAut (projectiveSL 3 F))
    (hα : ∀ (a b c : F) (h : a * b * c = 1), ∃ h' : entryMap σ ε a * entryMap σ ε b * entryMap σ ε c = 1,
      α (proj 3 F (diagSL a b c h)) =
        proj 3 F (diagSL (entryMap σ ε a) (entryMap σ ε b) (entryMap σ ε c) h'))
    {u : F} (hu0 : u ≠ 0) (hgu : entryMap σ ε u = -u) (hu : u * 1 * u⁻¹ = 1) :
    α (proj 3 F (diagSL u 1 u⁻¹ hu)) * (proj 3 F (diagSL u 1 u⁻¹ hu))⁻¹ = eInv2 := by
  obtain ⟨h', he⟩ := hα u 1 u⁻¹ hu
  rw [he, ← map_inv, diagSL_inv', ← map_mul, diagSL_mul]
  unfold eInv2
  congr 1
  refine diagSL_congr ?_ ?_ ?_
  · rw [hgu]; field_simp
  · rw [entryMap_one]; simp
  · rw [entryMap_inv_aux, hgu, inv_neg]
    field_simp

omit [Finite F] in
theorem bracket_eInv1 {σ : F ≃+* F} {ε : ℕ} (α : MulAut (projectiveSL 3 F))
    (hα : ∀ (a b c : F) (h : a * b * c = 1), ∃ h' : entryMap σ ε a * entryMap σ ε b * entryMap σ ε c = 1,
      α (proj 3 F (diagSL a b c h)) =
        proj 3 F (diagSL (entryMap σ ε a) (entryMap σ ε b) (entryMap σ ε c) h'))
    {u : F} (hu0 : u ≠ 0) (hgu : entryMap σ ε u = -u) (hu : 1 * u * u⁻¹ = 1) :
    α (proj 3 F (diagSL 1 u u⁻¹ hu)) * (proj 3 F (diagSL 1 u u⁻¹ hu))⁻¹ = eInv1 := by
  obtain ⟨h', he⟩ := hα 1 u u⁻¹ hu
  rw [he, ← map_inv, diagSL_inv', ← map_mul, diagSL_mul]
  unfold eInv1
  congr 1
  refine diagSL_congr ?_ ?_ ?_
  · rw [entryMap_one]; simp
  · rw [hgu]; field_simp
  · rw [entryMap_inv_aux, hgu, inv_neg]
    field_simp

end Final

section Assembly

variable {F : Type} [Field F] [Finite F]

theorem no_normal_minus_one {r : ℕ} (hc : LinCtx F r) (A : Subgroup (MulAut (projectiveSL 3 F)))
    (hA : IsPGroup 2 A)
    (hAP : A ⊓ inner (projectiveSL 3 F) = (Pexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _))
    (M : Subgroup (MulAut (projectiveSL 3 F))) (hMA : M ≤ A)
    (hMn : ∀ a ∈ A, ∀ n ∈ M, a * n * a⁻¹ ∈ M)
    {m : ℕ} {k : ℤ} (hm : 3 ≤ m) (hk1 : ¬ (2 : ℤ) ^ m ∣ (k - 1) ^ 2)
    (hk2 : ¬ (2 : ℤ) ^ m ∣ 2 * (k - 1)) (hpres : SD.Pres M m k) (hrm : r = 2 ^ (m - 1)) : False := by
  classical
  have hr3 := hc.r3
  have hr2 := hc.r2
  have h2 := hc.h2
  have hconjA : ∀ x ∈ Pexp (F := F) r, MulAut.conj x ∈ A := fun x hx => by
    have : MulAut.conj x ∈ (Pexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _) := ⟨x, hx, rfl⟩
    rw [← hAP] at this
    exact this.1
  have hnormA := hMn
  let Vs : Finset (projectiveSL 3 F) := {eInv1, eInv2, eInv3}
  have hinv : ∀ α ∈ M, ∀ x ∈ Vs, α x ∈ Vs := by
    intro α hα x hx
    have hαA := hMA hα
    have hxJ : x ∈ Jexp (F := F) r ∧ x ≠ 1 ∧ x * x = 1 := by
      simp only [Vs, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨eInv1_mem hr2, eInv1_ne_one hr3 hr2 h2, eInv1_mul_self⟩
      · exact ⟨eInv2_mem hr2, eInv2_ne_one hr3 hr2 h2, eInv2_mul_self⟩
      · exact ⟨eInv3_mem hr2, eInv3_ne_one hr3 hr2 h2, eInv3_mul_self⟩
    have hαxJ := aut_preserves_J hr3 hc.hmu hc.r4' A hAP hαA hxJ.1
    have hαxx : α x * α x = 1 := by rw [← map_mul, hxJ.2.2, map_one]
    rcases Jexp_invol hr3 hαxJ hαxx with h | h | h | h
    · exfalso
      apply hxJ.2.1
      apply α.injective
      rw [h, map_one]
    · simp [Vs, h]
    · simp [Vs, h]
    · simp [Vs, h]
  obtain ⟨Y, hYidx, hYfix⟩ := exists_fixing_subgroup M (hA.to_le hMA) Vs (Finset.card_le_three) hinv
  have hY1 : ∀ α ∈ Y, (α : MulAut (projectiveSL 3 F)) eInv1 = eInv1 := fun α hα =>
    hYfix α hα eInv1 (by simp [Vs])
  have hY2 : ∀ α ∈ Y, (α : MulAut (projectiveSL 3 F)) eInv2 = eInv2 := fun α hα =>
    hYfix α hα eInv2 (by simp [Vs])
  have key : ∀ α ∈ Y, ∃ w ∈ Jexp (F := F) r, (α : MulAut (projectiveSL 3 F)) = MulAut.conj w := by
    intro α hα
    by_cases hfix : ∀ j ∈ Jexp (F := F) r, (α : MulAut (projectiveSL 3 F)) j = j
    · exact centralizer_J_inner hc A hA hAP (hMA α.2) hfix
    · exfalso
      push Not at hfix
      obtain ⟨j, hjJ, hjne⟩ := hfix
      obtain ⟨σ, ε, hε, hform⟩ := aut_formula_ker hc A hAP (hMA α.2) (hY1 α hα) (hY2 α hα)
      obtain ⟨a, b, c, h, ha, hb, hcc, rfl⟩ := exists_diag_of_mem_Jexp hjJ
      have hmoved : ∃ w : F, w ^ r = 1 ∧ entryMap σ ε w ≠ w := by
        by_contra hcon
        push Not at hcon
        apply hjne
        obtain ⟨h', he⟩ := hform a b c h
        rw [he]
        exact proj_diagSL_congr (hcon a ha) (hcon b hb) (hcon c hcc)
      obtain ⟨w, hw, hmv⟩ := hmoved
      obtain ⟨u, hu0, hu, hgu⟩ := exists_neg_of_moved σ ε (N := m - 1) (by rw [← hrm]; exact hw) hmv
      rw [← hrm] at hu
      have hu1 : u * 1 * u⁻¹ = 1 := by field_simp
      have hu2 : 1 * u * u⁻¹ = 1 := by field_simp
      have hj2J : proj 3 F (diagSL u 1 u⁻¹ hu1) ∈ Jexp (F := F) r :=
        proj_diagSL_mem_Jexp hu1 hu (one_pow r)
      have hj1J : proj 3 F (diagSL 1 u u⁻¹ hu2) ∈ Jexp (F := F) r :=
        proj_diagSL_mem_Jexp hu2 (one_pow r) hu
      have hcomm : ∀ β ∈ M, ∀ j ∈ Jexp (F := F) r, MulAut.conj (β j * j⁻¹) ∈ M := by
        intro β hβ j hj
        have hjA : MulAut.conj j ∈ A := hconjA j (Jexp_le_Pexp r hj)
        have h1 : MulAut.conj (β j * j⁻¹) =
            β * (MulAut.conj j * β⁻¹ * (MulAut.conj j)⁻¹) := by
          rw [map_mul, map_inv, ← mulAut_conj_conj β j]
          group
        rw [h1]
        exact M.mul_mem hβ (hnormA _ hjA _ (M.inv_mem hβ))
      have he2 : MulAut.conj (eInv2 : projectiveSL 3 F) ∈ M := by
        have := hcomm α α.2 _ hj2J
        rwa [bracket_eInv2 (α : MulAut (projectiveSL 3 F)) hform hu0 hgu hu1] at this
      have he1 : MulAut.conj (eInv1 : projectiveSL 3 F) ∈ M := by
        have := hcomm α α.2 _ hj1J
        rwa [bracket_eInv1 (α : MulAut (projectiveSL 3 F)) hform hu0 hgu hu2] at this
      obtain ⟨a₁, ha₁⟩ : ∃ a₁ : M, (a₁ : MulAut (projectiveSL 3 F)) = MulAut.conj eInv1 := ⟨⟨_, he1⟩, rfl⟩
      obtain ⟨b₁, hb₁⟩ : ∃ b₁ : M, (b₁ : MulAut (projectiveSL 3 F)) = MulAut.conj eInv2 := ⟨⟨_, he2⟩, rfl⟩
      have hinjc := conj_injective_projectiveSL (F := F)
      refine SD.no_normal_four hm hk1 hpres ⟨a₁, b₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h1
        apply eInv1_ne_one hr3 hr2 h2
        apply hinjc
        rw [← ha₁, h1, map_one]
        rfl
      · intro h1
        apply eInv2_ne_one hr3 hr2 h2
        apply hinjc
        rw [← hb₁, h1, map_one]
        rfl
      · intro h1
        apply eInv1_ne_eInv2 hr3 hr2 h2
        apply hinjc
        rw [← ha₁, ← hb₁, h1]
      · apply Subtype.ext
        rw [Subgroup.coe_mul, ha₁, ← map_mul, eInv1_mul_self, map_one]
        rfl
      · apply Subtype.ext
        rw [Subgroup.coe_mul, hb₁, ← map_mul, eInv2_mul_self, map_one]
        rfl
      · apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ha₁, hb₁, ← map_mul, ← map_mul, eInv_comm12]
      · intro g
        have hab : ((a₁ * b₁ : M) : MulAut (projectiveSL 3 F)) = MulAut.conj eInv3 := by
          rw [Subgroup.coe_mul, ha₁, hb₁, ← map_mul, eInv1_mul_eInv2]
        have hconj1 : ∀ x ∈ Vs, x = eInv1 ∨ x = eInv2 ∨ x = eInv3 := by
          intro x hx
          simpa [Vs] using hx
        have hgx : ∀ c : M, ∀ x : projectiveSL 3 F, (c : MulAut (projectiveSL 3 F)) x ∈ Vs →
            (c : MulAut (projectiveSL 3 F)) * MulAut.conj x * (c : MulAut (projectiveSL 3 F))⁻¹ ∈
              ({(a₁ : MulAut (projectiveSL 3 F)), (b₁ : MulAut (projectiveSL 3 F)),
                ((a₁ * b₁ : M) : MulAut (projectiveSL 3 F))} : Set (MulAut (projectiveSL 3 F))) := by
          intro c x hx
          rw [mulAut_conj_conj]
          rcases hconj1 _ hx with h | h | h
          · left; rw [h, ha₁]
          · right; left; rw [h, hb₁]
          · right; right; rw [h, hab]; exact Set.mem_singleton _
        constructor
        · have := hgx g eInv1 (hinv g g.2 eInv1 (by simp [Vs]))
          rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
          have e : ((g * a₁ * g⁻¹ : M) : MulAut (projectiveSL 3 F)) =
              (g : MulAut (projectiveSL 3 F)) * MulAut.conj eInv1 * (g : MulAut (projectiveSL 3 F))⁻¹ := by
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha₁]
          rcases this with h | h | h
          · left; exact Subtype.ext (e.trans h)
          · right; left; exact Subtype.ext (e.trans h)
          · right; right; exact Subtype.ext (e.trans h)
        · have := hgx g eInv2 (hinv g g.2 eInv2 (by simp [Vs]))
          rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
          have e : ((g * b₁ * g⁻¹ : M) : MulAut (projectiveSL 3 F)) =
              (g : MulAut (projectiveSL 3 F)) * MulAut.conj eInv2 * (g : MulAut (projectiveSL 3 F))⁻¹ := by
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hb₁]
          rcases this with h | h | h
          · left; exact Subtype.ext (e.trans h)
          · right; left; exact Subtype.ext (e.trans h)
          · right; right; exact Subtype.ext (e.trans h)
  let B : Subgroup M := ((Jexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _)).subgroupOf M
  have hYB : Y ≤ B := by
    intro α hα
    obtain ⟨w, hw, hαw⟩ := key α hα
    exact Subgroup.mem_subgroupOf.2 ⟨w, hw, hαw.symm⟩
  have hBidx : B.index ≤ 2 := by
    have h1 : B.index ∣ Y.index := Subgroup.index_dvd_of_le hYB
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1).trans hYidx
  refine SD.no_abelian_index_two hm hk2 hpres ⟨B, hBidx, ?_, ?_⟩
  · intro α hα β hβ
    obtain ⟨w, hw, hαw⟩ := Subgroup.mem_subgroupOf.1 hα
    obtain ⟨w', hw', hβw⟩ := Subgroup.mem_subgroupOf.1 hβ
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hαw, ← hβw, ← map_mul, ← map_mul,
      Jexp_comm r w hw w' hw']
  · intro α hα
    obtain ⟨w, hw, hαw⟩ := Subgroup.mem_subgroupOf.1 hα
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hαw, ← map_pow, ← hrm, Jexp_pow r w hw, map_one]
    rfl

end Assembly

end CFSG.GH74.KGroups.L3Eps
