module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnRed
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer

namespace U4InnU5

theorem pPrimeCore_centralizer_yM5 :
    CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({yM5} : Set M5)) = ⊥ := by
  obtain ⟨Kb, hKbC, hsup, -, hsimp, hnc, h3, -⟩ := m5_u4_layer
  haveI := hsimp
  have hK : ∀ k ∈ Kb, k * yM5 = yM5 * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKbC hk)
  have hdec : ∀ x ∈ Subgroup.centralizer ({yM5} : Set M5),
      ∃ k ∈ Kb, ∃ n : ℤ, x = k * yM5 ^ n := by
    intro x hx
    have hle : Subgroup.centralizer ({yM5} : Set M5) ≤ decompSub Kb yM5 hK := by
      rw [hsup]
      apply sup_le
      · intro k hk
        exact ⟨k, hk, 0, by simp⟩
      · rw [Subgroup.zpowers_le]
        exact ⟨1, Kb.one_mem, 1, by simp⟩
    obtain ⟨k, hk, n, rfl⟩ := hle hx
    exact ⟨k, hk, n, rfl⟩
  have hcomm : ∀ k ∈ Kb, ∀ n : ℤ, k * yM5 ^ n = yM5 ^ n * k := fun k hk n =>
    ((show Commute k yM5 from hK k hk).zpow_right n).eq
  have hZ : Subgroup.center ↥Kb = ⊥ :=
    center_eq_bot_of_simple_of_not_comm (fun h => hnc ⟨⟨h⟩⟩)
  have hCK : Kb ≤ Subgroup.centralizer ({yM5} : Set M5) := hKbC
  refine pPrimeCore_eq_bot_of_normal (ι := Unit)
    (fun _ => Kb.subgroupOf (Subgroup.centralizer ({yM5} : Set M5))) ?_ ?_ ?_
  · intro _
    refine (Subgroup.normal_subgroupOf_iff hCK).2 fun h k hh hk => ?_
    obtain ⟨k₀, hk₀, n, rfl⟩ := hdec k hk
    have h1 : k₀ * yM5 ^ n * h * (k₀ * yM5 ^ n)⁻¹ = k₀ * h * k₀⁻¹ := by
      have hc := hcomm h hh n
      calc k₀ * yM5 ^ n * h * (k₀ * yM5 ^ n)⁻¹
          = k₀ * (yM5 ^ n * h) * (yM5 ^ n)⁻¹ * k₀⁻¹ := by group
        _ = k₀ * (h * yM5 ^ n) * (yM5 ^ n)⁻¹ * k₀⁻¹ := by rw [← hc]
        _ = k₀ * h * k₀⁻¹ := by group
    rw [h1]
    exact Kb.mul_mem (Kb.mul_mem hk₀ hh) (Kb.inv_mem hk₀)
  · intro _
    exact pPrimeCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCK)
      (pPrimeCore_eq_bot_of_simple h3)
  · intro g hg
    obtain ⟨k₀, hk₀, n, hgn⟩ := hdec g.1 g.2
    have hk₀c : ∀ k' ∈ Kb, k₀ * k' = k' * k₀ := by
      intro k' hk'
      have h1 := hg () ⟨k', hCK hk'⟩ hk'
      have h2 : (g : M5) * k' = k' * (g : M5) := congrArg Subtype.val h1
      rw [hgn] at h2
      have hc := hcomm k' hk' n
      calc k₀ * k' = k₀ * (yM5 ^ n * k' * (yM5 ^ n)⁻¹) := by
            rw [← hc]; group
        _ = (k₀ * yM5 ^ n * k') * (yM5 ^ n)⁻¹ := by group
        _ = (k' * (k₀ * yM5 ^ n)) * (yM5 ^ n)⁻¹ := by rw [h2]
        _ = k' * k₀ := by group
    have hk₀1 : k₀ = 1 := by
      have : (⟨k₀, hk₀⟩ : ↥Kb) ∈ Subgroup.center ↥Kb := by
        rw [Subgroup.mem_center_iff]
        intro b
        exact (Subtype.ext (hk₀c b.1 b.2)).symm
      rw [hZ, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    refine ⟨1, ?_⟩
    show g ^ 3 = 1
    apply Subtype.ext
    show (g : M5) ^ 3 = 1
    rw [hgn, hk₀1, one_mul]
    rw [← zpow_natCast (yM5 ^ n) 3, ← zpow_mul, mul_comm, zpow_mul]
    simp [zpow_natCast, yM5_pow_three]

theorem u4InnModel_M5 : U4InnModel M5 := by
  intro hS u hu3 hq
  obtain ⟨s, rfl⟩ := exists_conj_of_pow_three u hu3
  have hs3 : s ^ 3 = 1 := by
    have h1 : MulAut.conj (s ^ 3) = 1 := by rw [map_pow]; exact hu3
    have h2 := (conj_eq_conj_iff (s ^ 3) 1).1 (by rw [h1, map_one])
    rw [center_M5_eq_bot, Subgroup.mem_bot] at h2
    simpa using h2
  show CFSG.pPrimeCore 3 ↥(u4Fix (MulAut.conj s)) = ⊥
  rw [u4Fix_conj] at hq ⊢
  rcases normal_form s hs3 with h1 | ⟨τ, hτ⟩ | ⟨τ, d, hd, hcnt⟩
  · subst h1
    have h3 : 3 ∣ Nat.card M5 := by
      have h25 := hq.dvd_card
      have : Subgroup.centralizer ({(1 : M5)} : Set M5) = ⊤ := by
        ext x
        rw [Subgroup.mem_centralizer_singleton_iff]
        simp
      rw [this, Subgroup.card_top] at h25
      exact (show 3 ∣ 25920 by norm_num).trans h25
    have := pPrimeCore_u4Fix_one (M := M5) h3
    rw [← u4Fix_conj (1 : M5), map_one]
    exact this
  · refine pPrimeCore_centralizer_of_equiv τ s ?_
    rcases hτ with h | h
    · rw [h]
      exact pPrimeCore_centralizer_yM5
    · rw [h, centralizer_inv_eq]
      exact pPrimeCore_centralizer_yM5
  · exfalso
    exact hq.not_isSolvable
      (isSolvable_centralizer_of_equiv τ s (centralizer_diag_solvable (τ s) d hd hcnt))

end U4InnU5

theorem u4InnAt_u5two : U4InnAt S9.isU5two := by
  intro S _ _ hcat
  obtain ⟨e⟩ := U52Layer.bridge_u5two_stated hcat
  exact U4InnModel.of_mulEquiv e U4InnU5.u4InnModel_M5

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
