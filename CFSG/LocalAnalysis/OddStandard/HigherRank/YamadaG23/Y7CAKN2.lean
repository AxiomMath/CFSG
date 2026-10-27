module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

private lemma mem_sup_of_commute {H L : Subgroup Γ}
    (hcomm : ∀ a ∈ H, ∀ b ∈ L, a * b = b * a) {x : Γ} :
    x ∈ H ⊔ L ↔ ∃ a ∈ H, ∃ b ∈ L, a * b = x := by
  let S : Subgroup Γ :=
    { carrier := {y | ∃ a ∈ H, ∃ b ∈ L, a * b = y}
      one_mem' := ⟨1, H.one_mem, 1, L.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine ⟨a * c, H.mul_mem ha hc, b * d, L.mul_mem hb hd, ?_⟩
        calc a * c * (b * d) = a * (c * b) * d := by group
          _ = a * (b * c) * d := by rw [hcomm c hc b hb]
          _ = a * b * (c * d) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, L.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
              rw [← mul_inv_rev a b, ← mul_inv_rev b a, hcomm a ha b hb]
          _ = (a * b)⁻¹ := (mul_inv_rev a b).symm }
  have hS : ∀ y, y ∈ S ↔ ∃ a ∈ H, ∃ b ∈ L, a * b = y := fun _ => Iff.rfl
  have hEq : H ⊔ L = S := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · intro a ha; exact ⟨a, ha, 1, L.one_mem, mul_one a⟩
    · intro b hb; exact ⟨1, H.one_mem, b, hb, one_mul b⟩
    · rintro y ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  rw [hEq]
  exact hS x

private lemma conjSub_central {g z : Γ} {H : Subgroup Γ}
    (hz : ∀ h ∈ H, z * h = h * z) :
    ∀ m ∈ conjSub g H, (g * z * g⁻¹) * m = m * (g * z * g⁻¹) := by
  intro m hm
  have hm' : g⁻¹ * m * g ∈ H := y7c_mem_conjSub.mp hm
  have h := hz (g⁻¹ * m * g) hm'
  calc (g * z * g⁻¹) * m = g * (z * (g⁻¹ * m * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * m * g) * z) * g⁻¹ := by rw [h]
    _ = m * (g * z * g⁻¹) := by group

theorem y7c_exists_y7 (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) :
    ∃ y ∈ K, (∃ k ∈ K, y * k ≠ k * y) ∧ ∀ k ∈ K, y ^ 7 * k = k * y ^ 7 := by
  obtain ⟨x, hxJ, hx7, hxne⟩ := y7c_J_exists_order7 c
  by_cases hfix : conjSub t K = K
  · have hJleK : J ≤ K := by
      intro j hj
      have hj' := hJK hj
      rwa [hfix, sup_idem] at hj'
    have hxK : x ∈ K := hJleK hxJ
    refine ⟨x, hxK, ?_, ?_⟩
    · by_contra h
      have hcent : ∀ j ∈ J, x * j = j * x := by
        intro j hj
        by_contra hjne
        exact h ⟨j, hJleK hj, hjne⟩
      exact hxne (y7c_J_center c hxJ hcent)
    · intro k _
      simp [hx7]
  · have hKt : CFSG.IsComponent (conjSub t K) := y7c_isComponent_conjSub hK t
    have hcommKL : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a :=
      y7c_comm_of_components hK hKt (fun h => hfix h.symm)
    obtain ⟨a, haK, b, hbL, hab⟩ :=
      (mem_sup_of_commute (H := K) (L := conjSub t K) hcommKL).mp (hJK hxJ)
    have hxab : x = a * b := hab.symm
    have hab_comm : a * b = b * a := hcommKL a haK b hbL
    have hpow : (a * b) ^ 7 = a ^ 7 * b ^ 7 :=
      Commute.mul_pow ((commute_iff_eq a b).mpr hab_comm) 7
    have h1 : a ^ 7 * b ^ 7 = 1 := by rw [← hpow, ← hxab, hx7]
    have ha7_eq : a ^ 7 = (b ^ 7)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hb7_eq : b ^ 7 = (a ^ 7)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have ha7L : a ^ 7 ∈ conjSub t K := by
      rw [ha7_eq]; exact (conjSub t K).inv_mem (pow_mem hbL 7)
    have ha7K : a ^ 7 ∈ K := pow_mem haK 7
    have hb7K : b ^ 7 ∈ K := by
      rw [hb7_eq]; exact K.inv_mem ha7K
    have ha7_cent : ∀ m ∈ K, a ^ 7 * m = m * a ^ 7 :=
      fun m hm => (hcommKL m hm (a ^ 7) ha7L).symm
    have hb7_cent : ∀ m ∈ conjSub t K, b ^ 7 * m = m * b ^ 7 :=
      fun m hm => hcommKL (b ^ 7) hb7K m hm
    have hnotboth : ¬ ((∀ m ∈ K, a * m = m * a) ∧
        (∀ m ∈ conjSub t K, b * m = m * b)) := by
      rintro ⟨hac, hbc⟩
      have hxK : ∀ m ∈ K, x * m = m * x := by
        intro m hm
        rw [hxab]
        calc a * b * m = a * (b * m) := by group
          _ = a * (m * b) := by rw [(hcommKL m hm b hbL).symm]
          _ = (a * m) * b := by group
          _ = (m * a) * b := by rw [hac m hm]
          _ = m * (a * b) := by group
      have hxL : ∀ m ∈ conjSub t K, x * m = m * x := by
        intro m hm
        rw [hxab]
        calc a * b * m = a * (b * m) := by group
          _ = a * (m * b) := by rw [hbc m hm]
          _ = (a * m) * b := by group
          _ = (m * a) * b := by rw [hcommKL a haK m hm]
          _ = m * (a * b) := by group
      have hxJcomm : ∀ j ∈ J, x * j = j * x := by
        intro j hj
        obtain ⟨m, hm, n, hn, hmn⟩ :=
          (mem_sup_of_commute (H := K) (L := conjSub t K) hcommKL).mp (hJK hj)
        rw [← hmn]
        calc x * (m * n) = (x * m) * n := by group
          _ = (m * x) * n := by rw [hxK m hm]
          _ = m * (x * n) := by group
          _ = m * (n * x) := by rw [hxL n hn]
          _ = (m * n) * x := by group
      exact hxne (y7c_J_center c hxJ hxJcomm)
    by_cases hac : ∀ m ∈ K, a * m = m * a
    · have hbc : ¬ ∀ m ∈ conjSub t K, b * m = m * b :=
        fun hbc => hnotboth ⟨hac, hbc⟩
      push Not at hbc
      obtain ⟨l, hlL, hbl⟩ := hbc
      refine ⟨t * b * t⁻¹, ?_, ?_, ?_⟩
      · have hmem : t * b * t⁻¹ ∈ conjSub t (conjSub t K) := y7c_mul_mem_conjSub hbL
        simpa [y7c_conjSub_conjSub_of_sq c.t_sq K] using hmem
      · refine ⟨t * l * t⁻¹, ?_, ?_⟩
        · have hmem : t * l * t⁻¹ ∈ conjSub t (conjSub t K) := y7c_mul_mem_conjSub hlL
          simpa [y7c_conjSub_conjSub_of_sq c.t_sq K] using hmem
        · intro heq
          apply hbl
          have h := congrArg (fun z => t⁻¹ * z * t) heq
          simpa [mul_assoc] using h
      · intro m hm
        have hy7 : (t * b * t⁻¹) ^ 7 = t * b ^ 7 * t⁻¹ := conj_pow
        rw [hy7]
        have hcentral :=
          conjSub_central (g := t) (z := b ^ 7) (H := conjSub t K) hb7_cent
        rw [y7c_conjSub_conjSub_of_sq c.t_sq K] at hcentral
        exact hcentral m hm
    · push Not at hac
      obtain ⟨k, hkK, hak⟩ := hac
      exact ⟨a, haK, ⟨k, hkK, hak⟩, ha7_cent⟩

theorem y7c_exists_y7_conj (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (g : Γ) :
    ∃ y ∈ conjSub g K, (∃ k ∈ conjSub g K, y * k ≠ k * y) ∧
      ∀ k ∈ conjSub g K, y ^ 7 * k = k * y ^ 7 := by
  obtain ⟨y, hyK, hnc, hcent⟩ := y7c_exists_y7 c hK hJK
  refine ⟨g * y * g⁻¹, y7c_mul_mem_conjSub hyK, ?_, ?_⟩
  · obtain ⟨k, hkK, hne⟩ := hnc
    refine ⟨g * k * g⁻¹, y7c_mul_mem_conjSub hkK, ?_⟩
    intro heq
    apply hne
    have h := congrArg (fun z => g⁻¹ * z * g) heq
    simpa [mul_assoc] using h
  · intro k hk
    rw [conj_pow]
    have hk' : g⁻¹ * k * g ∈ K := y7c_mem_conjSub.mp hk
    have h := hcent (g⁻¹ * k * g) hk'
    calc (g * y ^ 7 * g⁻¹) * k = g * (y ^ 7 * (g⁻¹ * k * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * k * g) * y ^ 7) * g⁻¹ := by rw [h]
      _ = k * (g * y ^ 7 * g⁻¹) := by group

end CFSG.OddStandard.HigherRank.YamadaG23
