module

public import CFSG.CharacterTheory.BrauerLinearThree.TenSetting
public import CFSG.CharacterTheory.BrauerLinearThree.TenThirtyOne
public import CFSG.CharacterTheory.Semidihedral.Principal.PureFivePowerNontrivialOddCore

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage (N Gamma barKappa nu)
open CFSG.Semidihedral.Principal

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem cube_dvd_card_of_u_eq_one
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hu : Nat.card F - 1 = 2 * Nat.card Z) : Nat.card F ^ 3 ∣ Nat.card G := by
  have : Fintype G := Fintype.ofFinite G
  have : Group.IsPerfect G :=
    CFSG.Semidihedral.CoreFreeDihedral.isPerfect_of_simple_nonabelian hnonab
  obtain ⟨hn4, S, fS, hJr, -⟩ := exists_centered_semidihedral_sylow φ hZ hZodd h2 hJ hq
  obtain ⟨hsimp, hnonabL, hcentral, hnc, hmodel⟩ :=
    layer_hypotheses φ hZ hZodd h2 hJ hq p f hp hf hF (by omega)
  have := hsimp
  have hN : N J = ⊥ := oddCore_eq_bot_of_u_eq_one φ hZ hZodd h2 hJ hq (by omega) hu
  have hY := layer_preimage_index_two φ hZ hZodd h2 hJ hq p f hp hf hF (by omega)
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have hqodd := odd_card_F h2
      rw [hF, h] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
    · exact h
  have hq3 : 3 < p ^ f := by omega
  have hq4 : p ^ f % 4 = 3 := by omega
  set s₀ : G := (fS (CFSG.Semidihedral.s _) : G) with hs₀def
  set V : Subgroup G := Subgroup.zpowers J ⊔ Subgroup.zpowers s₀ with hVdef
  set D : Subgroup G := Subgroup.centralizer (V : Set G) with hDdef
  set W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype with hWdef
  set K : Subgroup G := Subgroup.centralizer (W : Set G) with hKdef
  have hdvd : Nat.card W ∣ (W.subgroupOf K).index :=
    card_torus_dvd_index _ hn4 S fS J hJr hnonabL hcentral hnc p f hp hpodd hf hq3 hq4 hmodel hN
      hY
  obtain ⟨-, -, hWcyc, hWodd, hWcard, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      ⟨hcases, -⟩, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients _ hn4 S fS J
      hJr hnonabL hcentral hnc p f hp hpodd hf hq3 hmodel hN hY
  have hWcyc : IsCyclic W := hWcyc
  have hWodd : Odd (Nat.card W) := hWodd
  have hqW : p ^ f = 2 * Nat.card W + 1 := by
    have h : (Nat.card W : ℤ) = (((p ^ f : ℕ) : ℤ) + if p ^ f % 4 = 1 then 1 else -1) / 2 :=
      hWcard
    have he : (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = -1 := by
      simp [show ¬ p ^ f % 4 = 1 by omega]
    rw [he] at h
    omega
  have hcases : Nat.card K = 12 * Nat.card W ∨ Nat.card K = 60 * Nat.card W := by
    rcases hcases with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWK : W ≤ K := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hWcomm x hx w hw
  have hindex : Nat.card K = (W.subgroupOf K).index * Nat.card W := by
    have h := Subgroup.card_mul_index (W.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv] at h
    rw [← h, mul_comm]
  have hW15 : Nat.card W ∣ 15 := by
    have hW0 : 0 < Nat.card W := Nat.card_pos
    have h60 : (W.subgroupOf K).index ∣ 2 ^ 2 * 15 := by
      rcases hcases with h | h
      · rw [h] at hindex
        rw [← Nat.eq_of_mul_eq_mul_right hW0 hindex]
        norm_num
      · rw [h] at hindex
        rw [← Nat.eq_of_mul_eq_mul_right hW0 hindex]
        norm_num
    exact Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hWodd)) (hdvd.trans h60)
  have hqcases : p ^ f = 7 ∨ p ^ f = 11 ∨ p ^ f = 31 := by
    have hle := Nat.le_of_dvd (by norm_num) hW15
    obtain ⟨m, hm⟩ : ∃ m, Nat.card W = m := ⟨_, rfl⟩
    rw [hm] at hle hW15 hqW
    interval_cases m <;> omega
  rcases hqcases with h7 | h11 | h31
  ·
    obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h7
    obtain ⟨-, -, -, hGcard, -⟩ :=
      perfect_local_parameter_seven_with_five_free_odd_core_is_regular _ hn4 S fS J hJr hnonabL
        hcentral hnc hmodel (by rw [hN]; simp)
    rw [hF, hGcard]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by norm_num) _) _
  ·
    exact absurd hN (perfect_field_factor_one_pure_five_power_parameter_has_nontrivial_odd_core _
      hn4 S fS J hJr hnonabL hcentral hnc p f hp hpodd hf hq3 hmodel hY 1 le_rfl
      (by rw [h11]; norm_num))
  ·
    exact (false_of_field_card_thirtyone _ hn4 S fS J hJr hnonabL hcentral hnc p f hp hpodd hf
      h31 hmodel hN hY).elim

end CFSG.BrauerLinearThree
