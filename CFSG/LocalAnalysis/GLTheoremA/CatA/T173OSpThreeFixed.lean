module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
  CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LieType.SeitzGeneration
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

local notation "V" => (Fin ℓ ⊕ Fin ℓ → F)

private theorem cube_one_of_mul_pow {A : Subgroup ↥(StatedSp ℓ F)}
    {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A) (hd : IsStdElt 3 A d)
    {x : ↥(StatedSp ℓ F)} (hx : x ∈ A) (hxd : x * d = d * x) {j : ℕ} (hj3 : j < 3) :
    (x * d ^ (3 - j)) ^ 3 = 1 := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hAexp : ∀ g ∈ A, g ^ 3 = 1 := hA.1.2
  have hcomm : Commute x (d ^ (3 - j)) :=
    (commute_iff_eq x d).mpr hxd |>.pow_right (3 - j)
  rw [Commute.mul_pow hcomm, hAexp x hx, one_mul]
  rw [← pow_mul, show (3 - j) * 3 = 3 * (3 - j) by ring, pow_mul, hd3, one_pow]

private theorem mem_fixedFactor_of_fixes [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (blocks : SpPrimaryBlocks 2 1 3 d
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d))
    {s : ℕ} (hs : spFixedDim d = 2 * s) (h2s : 2 ≤ s) {g : ↥(StatedSp ℓ F)}
    (hcommd : g * d = d * g) {W : Submodule F V}
    (hfix : ∀ w ∈ W, spEnd g w = w)
    (hperp : ∀ v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
      (∀ r ∈ W, spForm ℓ F v r = 0) → v ∈ W)
    (hb3 : g ^ 3 = 1) : g ∈ spFixedFactor d := by
  rw [spFixedFactor, mem_spSupported]
  refine ⟨hcommd, ?_⟩
  intro k hk hkO
  by_cases hk1 : k = X - 1
  · exact (hkO (by rw [Set.mem_singleton_iff]; exact hk1)).elim
  · have hkq : k = X ^ 2 + X + 1 := eq_quad_of_mem_primaryFactors hF hd3 hk hk1
    rw [hkq]
    have hbY : ∀ v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
        spEnd g v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) := by
      intro v hv
      have hsg : Commute (spEnd g) (spEnd d) := by
        show spEnd g * spEnd d = spEnd d * spEnd g
        rw [← spEnd_mul, ← spEnd_mul, hcommd]
      exact apply_mem_primaryComponent hsg hv
    exact eqOn_of_fixes_flag hb3 hbY hfix hperp

private theorem mul_pow_mem_fixedFactor [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (blocks : SpPrimaryBlocks 2 1 3 d
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d))
    {s : ℕ} (hs : spFixedDim d = 2 * s) (h2s : 2 ≤ s) {W : Submodule F V}
    (hWA : ∀ a ∈ A, ∀ w ∈ W, spEnd a w ∈ W)
    (hperp : ∀ v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
      (∀ r ∈ W, spForm ℓ F v r = 0) → v ∈ W)
    {x : ↥(StatedSp ℓ F)} (hx : x ∈ A) {j : ℕ} (hj3 : j < 3)
    (hj : ∀ w ∈ W, spEnd x w = spEnd (d ^ j) w) :
    x * d ^ (3 - j) ∈ spFixedFactor d := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have had : ∀ a ∈ A, a * d = d * a := fun a ha => by
    have hAel : CFSG.Open.IsElemAbelian 3 A := hA.1
    exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨d, hd.1⟩)
  have hxd : x * d = d * x := had x hx
  have hcommd : (x * d ^ (3 - j)) * d = d * (x * d ^ (3 - j)) := by
    have hdcomm : d ^ (3 - j) * d = d * d ^ (3 - j) :=
      (Commute.refl d).pow_left (3 - j) |>.eq
    calc (x * d ^ (3 - j)) * d = x * (d ^ (3 - j) * d) := by rw [mul_assoc]
      _ = x * (d * d ^ (3 - j)) := by rw [hdcomm]
      _ = (x * d) * d ^ (3 - j) := by rw [mul_assoc]
      _ = (d * x) * d ^ (3 - j) := by rw [hxd]
      _ = d * (x * d ^ (3 - j)) := by rw [mul_assoc]
  have hWd_pow : ∀ n : ℕ, ∀ w ∈ W, spEnd (d ^ n) w ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; rwa [pow_zero, spEnd_one, Module.End.one_apply]
    | succ n ih =>
      intro w hw
      rw [pow_succ, spEnd_mul, Module.End.mul_apply]
      exact ih _ (hWA d hd.1 w hw)
  have hfix : ∀ w ∈ W, spEnd (x * d ^ (3 - j)) w = w := by
    intro w hw
    have h1 : spEnd (d ^ (3 - j)) w ∈ W := hWd_pow _ w hw
    rw [spEnd_mul, Module.End.mul_apply, hj _ h1]
    rw [← Module.End.mul_apply, ← spEnd_mul, ← pow_add,
      show j + (3 - j) = 3 by omega, hd3, spEnd_one, Module.End.one_apply]
  have hb3 : (x * d ^ (3 - j)) ^ 3 = 1 :=
    cube_one_of_mul_pow hA hd hx hxd hj3
  exact mem_fixedFactor_of_fixes hF hd3 blocks hs h2s hcommd hfix hperp hb3

private theorem exists_decomp_mul_pow [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆)
    (blocks : SpPrimaryBlocks 2 1 3 d
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d))
    {s : ℕ} (hs : spFixedDim d = 2 * s) (h2s : 2 ≤ s) {W : Submodule F V}
    (hWA : ∀ a ∈ A, ∀ w ∈ W, spEnd a w ∈ W)
    (hperp : ∀ v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
      (∀ r ∈ W, spForm ℓ F v r = 0) → v ∈ W)
    (haction : ∀ x ∈ A, ∃ j : ℕ, j < 3 ∧ ∀ w ∈ W, spEnd x w = spEnd (d ^ j) w) :
    ∀ x ∈ A, ∃ j : ℕ, j < 3 ∧ ∃ b ∈ A ⊓ stdLayer d, x = b * d ^ j := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hdA : d ∈ A := hd.1
  intro x hx
  obtain ⟨j, hj3, hj⟩ := haction x hx
  have hxd : x * d = d * x := by
    have hAel : CFSG.Open.IsElemAbelian 3 A := hA.1
    exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨d, hdA⟩)
  have hbF1 : x * d ^ (3 - j) ∈ spFixedFactor d :=
    mul_pow_mem_fixedFactor hF hA hd blocks hs h2s hWA hperp hx hj3 hj
  have hb3 : (x * d ^ (3 - j)) ^ 3 = 1 := cube_one_of_mul_pow hA hd hx hxd hj3
  refine ⟨j, hj3, x * d ^ (3 - j), ⟨A.mul_mem hx (A.pow_mem hdA (3 - j)), ?_⟩, ?_⟩
  · rw [hK]
    exact mem_commutator_fixed_of_cube_one hF hd3 blocks hs h2s hbF1 hb3
  · have hpow : d ^ (3 - j) * d ^ j = 1 := by
      rw [← pow_add, show 3 - j + j = 3 by omega, hd3]
    calc x = x * 1 := (mul_one x).symm
      _ = x * (d ^ (3 - j) * d ^ j) := by rw [hpow]
      _ = x * d ^ (3 - j) * d ^ j := by group

private theorem eq_sup_inf_centralizer {A : Subgroup ↥(StatedSp ℓ F)}
    {d : ↥(StatedSp ℓ F)} (hdA : d ∈ A)
    (hdCK : d ∈ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)))
    (hdecomp : ∀ x ∈ A, ∃ j : ℕ, j < 3 ∧ ∃ b ∈ A ⊓ stdLayer d, x = b * d ^ j) :
    A = (A ⊓ stdLayer d) ⊔ (A ⊓ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F))) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  obtain ⟨j, hj3, b, hb, rfl⟩ := hdecomp x hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right (show d ^ j ∈ A ⊓
      Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) from
      ⟨A.pow_mem hdA j, Subgroup.pow_mem
        (Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F))) hdCK j⟩))

private theorem exists_isotropic_quad_vector [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hdimW3' : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 4) :
    ∃ w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1), spForm ℓ F w (spEnd d w) = 1 := by
  have hW3ne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdimW3'
    simp at hdimW3'
  exact exists_spForm_self_eq_one hF hd3 hW3ne

private theorem rotation_facts [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆)
    {w : V} {y : ↥(StatedSp ℓ F)}
    (hw3 : w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQw : spForm ℓ F w (spEnd d w) = 1)
    (hydef : y = ⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆) :
    y ∈ spSupported d ({X ^ 2 + X + 1} : Set F[X]) ∧ y ^ 3 = 1 ∧
      y ∈ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) ∧
      y * d = d * y ∧ spEnd y w = w + spEnd d w := by
  have hyF3 : y ∈ spSupported d ({X ^ 2 + X + 1} : Set F[X]) := by
    rw [hydef]
    exact rotation_mem_spSupported_unitary hF hd3 hw3 hQw
  have hy3 : y ^ 3 = 1 := by
    rw [hydef]
    exact commutator_transvection_pow_three hQw
  have hyK : y ∈ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) := by
    rw [hK]
    exact spSupported_unitary_le_centralizer_fixed_commutator hd3 hyF3
  have hyd : y * d = d * y := (mem_spSupported.mp hyF3).1
  have hyw : spEnd y w = w + spEnd d w := by
    rw [hydef, spEnd_commutator_transvection hQw]
    rw [spForm_isAlt w, zero_smul, zero_add, hQw, one_smul, add_zero]
  exact ⟨hyF3, hy3, hyK, hyd, hyw⟩

private theorem rotation_moves [CharP F 2] {d : ↥(StatedSp ℓ F)}
    {w : V} {y : ↥(StatedSp ℓ F)} (hQw : spForm ℓ F w (spEnd d w) = 1)
    (hydef : y = ⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆) :
    spEnd y w = w + spEnd d w ∧ y ≠ 1 := by
  have hyw : spEnd y w = w + spEnd d w := by
    rw [hydef, spEnd_commutator_transvection hQw]
    rw [spForm_isAlt w, zero_smul, zero_add, hQw, one_smul, add_zero]
  refine ⟨hyw, ?_⟩
  intro h
  rw [h, spEnd_one, Module.End.one_apply] at hyw
  have hdw0 : spEnd d w ≠ 0 := by
    intro h0
    rw [h0] at hQw
    simp at hQw
  exact hdw0 (add_left_cancel (show w + spEnd d w = w + 0 by simpa using hyw))

private theorem exists_fixed_vector_of_rotation [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hdimW3' : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 4)
    {w : V} {y : ↥(StatedSp ℓ F)} (hQw : spForm ℓ F w (spEnd d w) = 1)
    (hydef : y = ⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆) :
    ∃ u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1), u ≠ 0 ∧
      spEnd y u = u ∧ spEnd d u ≠ u := by
  let φ : ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1)) →ₗ[F] (F × F) :=
    { toFun := fun u => (spForm ℓ F u.1 w, spForm ℓ F u.1 (spEnd d w))
      map_add' := by intro p q; simp [map_add]
      map_smul' := by intro c p; simp [map_smul] }
  have hker : φ.ker ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hdimW3'] at hle
    have h2 : Module.finrank F (F × F) = 2 := by
      simp [Module.finrank_prod]
    rw [h2] at hle
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hu1 : spForm ℓ F u.1 w = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp hu)
  have hu2 : spForm ℓ F u.1 (spEnd d w) = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp hu)
  have hyu : spEnd y u.1 = u.1 := by
    rw [hydef, spEnd_commutator_transvection hQw, hu1, hu2]
    simp
  have hdu : spEnd d u.1 ≠ u.1 := by
    intro h
    have huW1 : u.1 ∈ primaryComponent (spEnd d) (X - 1) := by
      rw [primaryComponent_sub_one_eq_fixSub, CFSG.LieType.SeitzGeneration.mem_fixSub]
      exact h
    have hbot : primaryComponent (spEnd d) (X ^ 2 + X + 1) ⊓
        primaryComponent (spEnd d) (X - 1) = ⊥ := by
      rw [primaryComponent_quad_eq_normKer, primaryComponent_sub_one_eq_fixSub, inf_comm]
      exact fixSub_inf_normKer (three_ne_zero_of_charP_two (F := F)) d
    have hin : (u : V) ∈ (⊥ : Submodule F V) := by
      rw [← hbot]
      exact Submodule.mem_inf.mpr ⟨u.2, huW1⟩
    rw [Submodule.mem_bot] at hin
    exact hu0 (Subtype.ext hin)
  exact ⟨u.1, u.2, fun h => hu0 (Subtype.ext h), hyu, hdu⟩

private theorem rotation_not_mem [CharP F 2] {A : Subgroup ↥(StatedSp ℓ F)}
    {d y : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hstep1 : A ⊓ spSupported d ({X ^ 2 + X + 1} : Set F[X]) ≤ Subgroup.zpowers d)
    (hyF3 : y ∈ spSupported d ({X ^ 2 + X + 1} : Set F[X])) (hy1 : y ≠ 1)
    {u : V} (hu3 : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1)) (hu0 : u ≠ 0)
    (hyu3 : spEnd y u = u) (hdu3 : spEnd d u ≠ u) : y ∉ A := by
  intro hyA
  have hyPow : y ∈ Subgroup.zpowers d := hstep1 ⟨hyA, hyF3⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyPow
  have hk3 : y = d ^ ((k % 3).toNat) := by
    rw [← hk, ← zpow_natCast]
    rw [show (((k % 3).toNat : ℤ)) = k % (3 : ℤ) from
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact zpow_eq_zpow_emod' k hd3
  have hkm : (k % 3).toNat < 3 := by
    have := Int.emod_lt_of_pos k (show (0 : ℤ) < 3 by norm_num)
    omega
  have hfixu : spEnd (d ^ ((k % 3).toNat)) u = u := by rw [← hk3]; exact hyu3
  interval_cases h : (k % 3).toNat
  · exact hy1 (by rw [hk3, pow_zero])
  · rw [pow_one] at hfixu
    exact hdu3 hfixu
  · rw [CFSG.LieType.SeitzGeneration.spEnd_pow d 2, pow_two,
      Module.End.mul_apply] at hfixu
    rw [spEnd_sq_apply_of_mem_primary hu3] at hfixu
    have hdu0 : spEnd d u = 0 := add_left_cancel (show u + spEnd d u = u + 0 by
      simpa using hfixu)
    have h2 := congrArg (spEnd (d ^ 2)) hdu0
    rw [← Module.End.mul_apply, ← spEnd_mul, show d ^ 2 * d = d ^ 3 by group, hd3,
      spEnd_one, Module.End.one_apply, map_zero] at h2
    exact hu0 h2

private theorem rotation_centralizes {A : Subgroup ↥(StatedSp ℓ F)}
    {d y : ↥(StatedSp ℓ F)}
    (hdecomp : ∀ x ∈ A, ∃ j : ℕ, j < 3 ∧ ∃ b ∈ A ⊓ stdLayer d, x = b * d ^ j)
    (hyK' : ∀ k ∈ stdLayer d, k * y = y * k) (hyd : y * d = d * y) :
    y ∈ Subgroup.centralizer (A : Set ↥(StatedSp ℓ F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨j, hj3, b, hb, rfl⟩ := hdecomp x hx
  have hyb : b * y = y * b := hyK' b hb.2
  have hydj : y * d ^ j = d ^ j * y := (commute_iff_eq y d).mpr hyd |>.pow_right j
  calc b * d ^ j * y = b * (d ^ j * y) := by rw [mul_assoc]
    _ = b * (y * d ^ j) := by rw [← hydj]
    _ = (b * y) * d ^ j := by rw [← mul_assoc]
    _ = (y * b) * d ^ j := by rw [hyb]
    _ = y * (b * d ^ j) := by rw [mul_assoc]

private theorem exists_centralizing_rotation [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆)
    (hstep1 : A ⊓ spSupported d ({X ^ 2 + X + 1} : Set F[X]) ≤ Subgroup.zpowers d)
    (hdimW3' : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 4)
    (hdecomp : ∀ x ∈ A, ∃ j : ℕ, j < 3 ∧ ∃ b ∈ A ⊓ stdLayer d, x = b * d ^ j) :
    ∃ y : ↥(StatedSp ℓ F), y ∈ Subgroup.centralizer (A : Set ↥(StatedSp ℓ F)) ∧
      y ∈ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) ∧ y ^ 3 = 1 ∧ y ∉ A := by
  obtain ⟨w, hw3, hQw⟩ := exists_isotropic_quad_vector hF hd3 hdimW3'
  set y : ↥(StatedSp ℓ F) :=
    ⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆ with hydef
  have hfacts := rotation_facts hF hd3 hK hw3 hQw hydef
  obtain ⟨hyF3, hy3, hyK, hyd, -⟩ := hfacts
  obtain ⟨-, hy1⟩ := rotation_moves hQw hydef
  obtain ⟨u, hu3, hu0, hyu3, hdu3⟩ :=
    exists_fixed_vector_of_rotation hF hd3 hdimW3' hQw hydef
  have hyK' : ∀ k ∈ stdLayer d, k * y = y * k := by
    rw [Subgroup.mem_centralizer_iff] at hyK
    exact fun k hk => hyK k hk
  have hy_notA := rotation_not_mem hd3 hstep1 hyF3 hy1 hu3 hu0 hyu3 hdu3
  exact ⟨y, rotation_centralizes hdecomp hyK' hyd, hyK, hy3, hy_notA⟩

private theorem stdLayer_le_centralizer_zpowers {d : ↥(StatedSp ℓ F)} :
    stdLayer d ≤ Subgroup.centralizer ({d} : Set ↥(StatedSp ℓ F)) := by
  rw [stdLayer, CFSG.Open.GLALayer]
  exact sSup_le fun K hK => hK.1

private theorem mem_centralizer_stdLayer {d : ↥(StatedSp ℓ F)} :
    d ∈ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' := stdLayer_le_centralizer_zpowers hy
  rw [Subgroup.mem_centralizer_iff] at hy'
  exact (hy' d (Set.mem_singleton d)).symm

private theorem one_le_length_of_isQuasisimple_layer
    {d : ↥(StatedSp ℓ F)}
    (hQ : CFSG.Open.IsQuasisimple ↥⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆) : 1 ≤ ℓ := by
  by_contra hℓ0
  have hℓ0' : ℓ = 0 := by omega
  subst hℓ0'
  haveI : Subsingleton ↥(StatedSp 0 F) := inferInstance
  haveI : Subsingleton ↥⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆ := inferInstance
  have hnt : Nontrivial ↥⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆ := by
    haveI : IsSimpleGroup (↥⁅spSupported d ({X - 1} : Set F[X]),
        spSupported d ({X - 1} : Set F[X])⁆ ⧸
        Subgroup.center ↥⁅spSupported d ({X - 1} : Set F[X]),
        spSupported d ({X - 1} : Set F[X])⁆) := hQ.2
    exact (QuotientGroup.mk'_surjective (Subgroup.center
      ↥⁅spSupported d ({X - 1} : Set F[X]), spSupported d ({X - 1} : Set F[X])⁆)).nontrivial
  exact (not_subsingleton_iff_nontrivial.mpr hnt) inferInstance

private theorem exists_two_subgroup_fixedFactor_four (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)}
    (blocks : SpPrimaryBlocks 2 1 3 d
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d))
    (hdim4 : spFixedDim d = 4) :
    ∃ T : Subgroup ↥(StatedSp ℓ F), T ≠ ⊥ ∧ IsPGroup 2 ↥T ∧
      T ≤ ⁅spFixedFactor d, spFixedFactor d⁆ := by
  obtain ⟨⟨e6⟩, -⟩ := spFixed_four_two_alt (ℓ := 2) (f := 1) (p := 3) hF blocks hdim4
  have hcard : Nat.card ↥⁅spFixedFactor d, spFixedFactor d⁆ = 360 := by
    rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h2dvd : 2 ∣ Nat.card ↥⁅spFixedFactor d, spFixedFactor d⁆ := by rw [hcard]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥⁅spFixedFactor d, spFixedFactor d⁆) 2 h2dvd
  refine ⟨(Subgroup.zpowers x).map (Subgroup.subtype (⁅spFixedFactor d, spFixedFactor d⁆)),
    ?_, ?_, ?_⟩
  · intro hbot
    have hxmem : (x : ↥(StatedSp ℓ F)) ∈ (⊥ : Subgroup ↥(StatedSp ℓ F)) := by
      rw [← hbot]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers x)
    rw [Subgroup.mem_bot] at hxmem
    have hx1 : x = 1 := Subtype.ext hxmem
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  · have hcardT : Nat.card ↥((Subgroup.zpowers x).map
        (Subgroup.subtype (⁅spFixedFactor d, spFixedFactor d⁆))) =
        Nat.card ↥(Subgroup.zpowers x) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.zpowers x)
        (Subgroup.subtype (⁅spFixedFactor d, spFixedFactor d⁆))
        (Subgroup.subtype_injective _))).symm
    refine IsPGroup.of_card (n := 1) ?_
    rw [hcardT, Nat.card_zpowers, hx]
    norm_num
  · exact Subgroup.map_subtype_le _

private theorem fixedFactor_perfect_of_three_le (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)}
    (blocks : SpPrimaryBlocks 2 1 3 d
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d))
    {s : ℕ} (hs : spFixedDim d = 2 * s) (hs3 : 3 ≤ s) :
    ⁅spFixedFactor d, spFixedFactor d⁆ = spFixedFactor d := by
  have hd4 : ¬ (spFixedDim d = 4 ∧ Nat.card F = 2) := by
    rintro ⟨h4, -⟩
    rw [hs] at h4
    omega
  have hlist : SpFixedListed d := by
    refine ⟨?_, ?_⟩
    · rw [hs]; omega
    · rintro ⟨h2, -⟩
      rw [hs] at h2
      omega
  have hK : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
  have hq := spFixedFactor_isQuasisimple (ℓ := 2) (f := 1) (p := 3) hK Nat.prime_two
    (by norm_num) blocks hlist hd4
  rw [← Subgroup.map_subtype_commutator, Group.isPerfect_def.mp hq.1, Subgroup.map_top,
    Subgroup.range_subtype]

private theorem exists_involution_fixedFactor [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) {s : ℕ} (hs : spFixedDim d = 2 * s)
    (hs3 : 3 ≤ s) :
    ∃ t ∈ spFixedFactor d, t ≠ 1 ∧ t * t = 1 := by
  have hpos : 0 < Module.finrank F (primaryComponent (spEnd d) (X - 1)) := by
    rw [show Module.finrank F (primaryComponent (spEnd d) (X - 1)) = spFixedDim d from rfl,
      hs]
    omega
  have hW1ne : primaryComponent (spEnd d) (X - 1) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hpos
    simpa using hpos
  obtain ⟨u, huW1, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW1ne
  have hufix : spEnd d u = u := by
    rw [primaryComponent_sub_one_eq_fixSub] at huW1
    exact mem_fixSub.mp huW1
  set t : ↥(StatedSp ℓ F) := spTransvection u (1 : F) with ht
  have htF : t ∈ spFixedFactor d := spTransvection_mem_spFixedFactor hufix 1
  have htsq : t * t = 1 := by
    have h1 : t = t⁻¹ := by
      rw [ht, spTransvection_inv, CharTwo.neg_eq]
    have h2 : t * t⁻¹ = 1 := mul_inv_cancel t
    rwa [← h1] at h2
  refine ⟨t, htF, ?_, htsq⟩
  intro h1
  have hb : ∃ v : V, spForm ℓ F v u = 1 := by
    by_contra h
    push Not at h
    refine hu0 ((spForm_nondegenerate (r := ℓ) (K := F)).2 u fun v => ?_)
    rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF
      (spForm ℓ F v u) with h0 | h1'
    · exact h0
    · exact absurd h1' (h v)
  obtain ⟨v, hv⟩ := hb
  have hτ : spEnd t v = v := by
    rw [h1, spEnd_one, Module.End.one_apply]
  rw [ht, spEnd_spTransvection, hv, one_mul, one_smul] at hτ
  have h0 : u = 0 := add_left_cancel (show v + u = v + 0 by simpa using hτ)
  exact hu0 h0

theorem exists_two_subgroup_le_stdLayer_fixed (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hQ : CFSG.Open.IsQuasisimple ↥⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆) :
    ∃ T : Subgroup ↥(StatedSp ℓ F), T ≠ ⊥ ∧ IsPGroup 2 ↥T ∧
      T ≤ ⁅spSupported d ({X - 1} : Set F[X]),
        spSupported d ({X - 1} : Set F[X])⁆ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hKbar : ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆ = ⁅spFixedFactor d, spFixedFactor d⁆ := rfl
  have hℓ : 1 ≤ ℓ := one_le_length_of_isQuasisimple_layer hQ
  have blocks := spPrimaryBlocks_of_order_three hF hℓ hd3 hd1
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hs' : spFixedDim d = 2 * s := hs
  have h2s : 2 ≤ s := two_le_fixed_half hF hℓ hd3 hd1 (hKbar ▸ hQ) blocks hs'
  rcases Nat.eq_or_lt_of_le h2s with hs2 | hs3
  · obtain ⟨T, hTne, hT2, hTle⟩ :=
      exists_two_subgroup_fixedFactor_four hF blocks (by rw [hs', ← hs2])
    exact ⟨T, hTne, hT2, by rw [hKbar]; exact hTle⟩
  · obtain ⟨t, htF, ht1, htsq⟩ := exists_involution_fixedFactor hF hd3 hs' (by omega : 3 ≤ s)
    refine ⟨Subgroup.zpowers t, ?_, ?_, ?_⟩
    · intro hbot
      have hxmem : t ∈ (⊥ : Subgroup ↥(StatedSp ℓ F)) := by
        rw [← hbot]
        exact Subgroup.mem_zpowers t
      rw [Subgroup.mem_bot] at hxmem
      exact ht1 hxmem
    · refine IsPGroup.of_card (n := 1) ?_
      have htsq2 : t ^ 2 = 1 := by rw [pow_two]; exact htsq
      rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) htsq2 ht1]
      norm_num
    · rw [hKbar, fixedFactor_perfect_of_three_le hF blocks hs' (by omega : 3 ≤ s)]
      exact Subgroup.zpowers_le.mpr htF

theorem stdOutcome_fixed (hF : Nat.card F = 2) (hℓ : 3 ≤ ℓ)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆) :
    StdVanishes A d ∨ StdExtends 3 A d := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hd1 : d ≠ 1 := hd.2.1
  have hdA : d ∈ A := hd.1
  have hℓ1 : 1 ≤ ℓ := by omega
  have blocks := spPrimaryBlocks_of_order_three hF hℓ1 hd3 hd1
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hs' : spFixedDim d = 2 * s := hs
  have hKEq : ⁅spFixedFactor d, spFixedFactor d⁆ = stdLayer d := by
    rw [hK]
    rfl
  have hQ' : CFSG.Open.IsQuasisimple ↥⁅spFixedFactor d, spFixedFactor d⁆ := by
    rw [hKEq]
    exact hd.2.2.2.1.2.2
  have h2s : 2 ≤ s := two_le_fixed_half hF hℓ1 hd3 hd1 hQ' blocks hs'
  by_cases hv : StdVanishes A d
  · exact Or.inl hv
  · right
    obtain ⟨W, hWA, hperp, hdimW3', haction⟩ :=
      exists_lagrangian_block_of_not_stdVanishes hF hℓ hA hd hK hs' hv
    have hdecomp := exists_decomp_mul_pow hF hA hd hK blocks hs' h2s hWA hperp haction
    have hstep1 := inf_quad_le_zpowers_of_std hF hd hK
    have hdCK := mem_centralizer_stdLayer (d := d)
    exact ⟨eq_sup_inf_centralizer hdA hdCK hdecomp,
      exists_centralizing_rotation hF hd3 hK hstep1 hdimW3' hdecomp⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
