module

public import CFSG.GH74.Generic.S1.TQ3BarMat
public import CFSG.GH74.Generic.S1.RQ3Lin
public import CFSG.GH74.Generic.S1.RQ3Sys
public import CFSG.GH74.Generic.S1.TPairFacts

public section

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S1

variable {G : Type} [Group G] [Finite G]

theorem eq_or_eq_mul_of_conj_eq {y : G} (hy2 : orderOf y = 2) {K : Subgroup (CentralizerBar y)}
    (hcent : centralizer (K : Set (CentralizerBar y)) = Subgroup.zpowers (xbar y))
    (hinj : Function.Injective (proj y)) {u v : G} (hu : u ∈ centralizer ({y} : Set G))
    (hv : v ∈ centralizer ({y} : Set G))
    (h : ∀ k ∈ K, barOf hu * k * (barOf hu)⁻¹ = barOf hv * k * (barOf hv)⁻¹) :
    u = v ∨ u = v * y := by
  have hz : (barOf hv)⁻¹ * barOf hu ∈ centralizer (K : Set (CentralizerBar y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := h k hk
    calc k * ((barOf hv)⁻¹ * barOf hu) = (barOf hv)⁻¹ * (barOf hv * k * (barOf hv)⁻¹) * barOf hu := by group
      _ = (barOf hv)⁻¹ * (barOf hu * k * (barOf hu)⁻¹) * barOf hu := by rw [this]
      _ = (barOf hv)⁻¹ * barOf hu * k := by group
  rw [hcent] at hz
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hxo : orderOf (xbar y) = 2 := orderOf_xbar hy2
  have hxx : xbar y ^ 2 = 1 := by
    have := pow_orderOf_eq_one (xbar y)
    rwa [hxo] at this
  have hcases : xbar y ^ n = 1 ∨ xbar y ^ n = xbar y := by
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left
      rw [← Int.emod_add_mul_ediv n 2, h0, _root_.zpow_add, _root_.zpow_mul]
      simp [hxx]
    · right
      rw [← Int.emod_add_mul_ediv n 2, h1, _root_.zpow_add, _root_.zpow_mul]
      simp [hxx]
  rcases hcases with h1 | h1
  · left
    rw [h1] at hn
    have : barOf hu = barOf hv := by
      have := congrArg (fun z => barOf hv * z) hn
      simpa using this.symm
    exact congrArg Subtype.val (hinj this)
  · right
    rw [h1] at hn
    have hvy : v * y ∈ centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.1 hv
      calc v * y * y = (y * v) * y := by rw [this]
        _ = y * (v * y) := by group
    have : barOf hu = barOf hvy := by
      have e1 : barOf hvy = barOf hv * xbar y := rfl
      rw [e1]
      have := congrArg (fun z => barOf hv * z) hn
      simpa using this.symm
    exact congrArg Subtype.val (hinj this)


structure Q3Frame (G : Type) [Group G] [Finite G] (F : Type) [Field F] where
  X : Fin 5 → G
  D : ∀ e, LayerData3 (X e) (StatedSL 4 F)
  X_sq : ∀ e, X e * X e = 1
  X_ne : ∀ e, X e ≠ 1
  X_comm : ∀ i j, X i * X j = X j * X i
  X_prod : X 0 * X 1 * X 2 * X 3 * X 4 = 1
  act : ∀ e j, ActsAsReflOn (D e).iso
    (barOf (mem_centralizer_singleton_iff.2 (X_comm _ _) : X (e.succAbove j) ∈ centralizer ({X e} : Set G)))
    (reflDiag F j)
  cent4 : centralizer ((D 4).K : Set (CentralizerBar (X 4))) = Subgroup.zpowers (xbar (X 4))
  xK : xbar (X 4) ∈ (D 4).K

variable {F : Type} [Field F] [Finite F]

theorem q3_two_ne_zero (hF3 : Nat.card F = 3) : (2 : F) ≠ 0 :=
  two_ne_zero_of_odd_card (by rw [hF3]; exact ⟨1, rfl⟩)

namespace Q3Frame

variable (Fr : Q3Frame G F)

omit [Finite F] in
theorem hw (e : Fin 5) (j : Fin 4) : Fr.X (e.succAbove j) ∈ centralizer ({Fr.X e} : Set G) :=
  mem_centralizer_singleton_iff.2 (Fr.X_comm _ _)

omit [Finite F] in
theorem orderOf_X (e : Fin 5) : orderOf (Fr.X e) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact Fr.X_sq e) (Fr.X_ne e)

omit [Finite F] in
theorem X_mem_cent (i j : Fin 5) : Fr.X i ∈ centralizer ({Fr.X j} : Set G) :=
  mem_centralizer_singleton_iff.2 (Fr.X_comm _ _)

theorem exists_s (hF3 : Nat.card F = 3) {c : G} (hcJ : c ∈ symJ3 Fr.X 3) (hc2 : orderOf c = 2) :
    ∃ s : ↥(StatedSL 4 F), s ∈ blkLin (F := F) 2 3 ∧ (Fr.D 4).ι s = c ∧ s * s = 1 ∧ s ≠ 1 ∧
      ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F 2 3 := by
  rw [symJ3_three (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act] at hcJ
  obtain ⟨s, hs, hsc⟩ := hcJ
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hss : s * s = 1 := by
    apply (Fr.D 4).ι_injective
    rw [map_mul, map_one, hsc]
    rw [← sq, ← hc2]
    exact pow_orderOf_eq_one c
  have hs1 : s ≠ 1 := by
    intro h
    apply hc1
    rw [← hsc, h, map_one]
  exact ⟨s, hs, hsc, hss, hs1, mat_eq_zblk_of_mem_blkLin (q3_two_ne_zero hF3) (by decide) hs hss hs1⟩


omit [Finite F] in
theorem zblk_two_three_eq : zblkMat F 2 3 = reflDiagMat F 2 * reflDiagMat F 3 := by
  unfold zblkMat reflDiagMat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

omit [Finite F] in
theorem exists_s0 : ∃ s₀ : ↥(StatedSL 4 F), s₀ ∈ Subgroup.center ↥(StatedSL 4 F) ∧ s₀ * s₀ = 1 ∧
    s₀ ≠ 1 ∧ (Fr.D 4).ι s₀ = Fr.X 4 := by
  set D4 := Fr.D 4 with hD4
  let k : ↥D4.K := ⟨xbar (Fr.X 4), Fr.xK⟩
  have hxo : orderOf (xbar (Fr.X 4)) = 2 := orderOf_xbar (Fr.orderOf_X 4)
  have hxx : xbar (Fr.X 4) * xbar (Fr.X 4) = 1 := by
    have := pow_orderOf_eq_one (xbar (Fr.X 4))
    rw [hxo] at this
    rw [← sq]
    exact this
  have hkc : ∀ g : ↥D4.K, g * k = k * g := fun g => Subtype.ext (xbar_comm (Fr.X 4) g.1)
  refine ⟨D4.iso k, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg D4.iso (hkc (D4.iso.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · rw [← map_mul]
    have : k * k = 1 := Subtype.ext hxx
    rw [this, map_one]
  · intro h
    have : k = 1 := D4.iso.injective (h.trans (map_one _).symm)
    exact xbar_ne_one (Fr.orderOf_X 4) (congrArg Subtype.val this)
  · have h1 := D4.proj_ιC (D4.iso k)
    rw [MulEquiv.symm_apply_apply] at h1
    have h2 : D4.ιC (D4.iso k) = ⟨Fr.X 4, mem_centralizer_singleton_iff.2 rfl⟩ := by
      apply D4.inj
      rw [h1]
      rfl
    exact congrArg Subtype.val h2


theorem X23_eq (hF3 : Nat.card F = 3) {c : G} (hcJ : c ∈ symJ3 Fr.X 3) (hc2 : orderOf c = 2) :
    Fr.X 2 * Fr.X 3 = c ∨ Fr.X 2 * Fr.X 3 = c * Fr.X 4 := by
  obtain ⟨s, hs, hsc, hss, hs1, hsmat⟩ := Fr.exists_s hF3 hcJ hc2
  set D4 := Fr.D 4 with hD4
  have hu : Fr.X 2 * Fr.X 3 ∈ centralizer ({Fr.X 4} : Set G) :=
    mem_centralizer_singleton_iff.2 (by
      calc Fr.X 2 * Fr.X 3 * Fr.X 4 = Fr.X 2 * (Fr.X 3 * Fr.X 4) := mul_assoc _ _ _
        _ = Fr.X 2 * (Fr.X 4 * Fr.X 3) := by rw [Fr.X_comm 3 4]
        _ = (Fr.X 2 * Fr.X 4) * Fr.X 3 := (mul_assoc _ _ _).symm
        _ = (Fr.X 4 * Fr.X 2) * Fr.X 3 := by rw [Fr.X_comm 2 4]
        _ = Fr.X 4 * (Fr.X 2 * Fr.X 3) := mul_assoc _ _ _)
  have hv : c ∈ centralizer ({Fr.X 4} : Set G) := hsc ▸ D4.ι_mem_cent s
  have h2 : Fr.X 2 ∈ centralizer ({Fr.X 4} : Set G) := Fr.X_mem_cent 2 4
  have h3 : Fr.X 3 ∈ centralizer ({Fr.X 4} : Set G) := Fr.X_mem_cent 3 4
  have hact2 : ActsAsReflOn D4.iso (barOf h2) (reflDiag F 2) := Fr.act 4 2
  have hact3 : ActsAsReflOn D4.iso (barOf h3) (reflDiag F 3) := Fr.act 4 3
  have hbu : barOf hu = barOf h2 * barOf h3 := rfl
  have hbv : barOf hv = ((D4.iso.symm s : ↥D4.K) : CentralizerBar (Fr.X 4)) := by
    have := D4.proj_ιC s
    rw [← this]
    simp only [hsc.symm]
    rfl
  have hsGL : (s : GL (Fin 4) F) = reflDiag F 2 * reflDiag F 3 := by
    apply Units.ext
    rw [Units.val_mul]
    show ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = reflDiagMat F 2 * reflDiagMat F 3
    rw [hsmat, zblk_two_three_eq]
  refine eq_or_eq_mul_of_conj_eq (Fr.orderOf_X 4) Fr.cent4 D4.inj hu hv ?_
  intro k hk
  have hKn : D4.K.Normal := D4.normal
  set kk : ↥D4.K := ⟨k, hk⟩ with hkk
  have hk3 : barOf h3 * k * (barOf h3)⁻¹ ∈ D4.K := hKn.conj_mem _ hk _
  have hk23 : barOf h2 * (barOf h3 * k * (barOf h3)⁻¹) * (barOf h2)⁻¹ ∈ D4.K :=
    hKn.conj_mem _ hk3 _
  have hka : barOf hu * k * (barOf hu)⁻¹ ∈ D4.K := hKn.conj_mem _ hk _
  have hkb : barOf hv * k * (barOf hv)⁻¹ ∈ D4.K := hKn.conj_mem _ hk _
  have e3 := hact3 kk ⟨_, hk3⟩ rfl
  have e2 := hact2 ⟨_, hk3⟩ ⟨_, hk23⟩ rfl
  have hLHS : (⟨barOf hu * k * (barOf hu)⁻¹, hka⟩ : ↥D4.K) = ⟨_, hk23⟩ :=
    Subtype.ext (by
      show barOf hu * k * (barOf hu)⁻¹ =
        barOf h2 * (barOf h3 * k * (barOf h3)⁻¹) * (barOf h2)⁻¹
      rw [hbu]; group)
  have hL : ((D4.iso ⟨barOf hu * k * (barOf hu)⁻¹, hka⟩ : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
      reflDiag F 2 * (reflDiag F 3 * ((D4.iso kk : ↥(StatedSL 4 F)) : GL (Fin 4) F) *
        (reflDiag F 3)⁻¹) * (reflDiag F 2)⁻¹ := by
    rw [hLHS, e2, e3]
  have hR : ((D4.iso ⟨barOf hv * k * (barOf hv)⁻¹, hkb⟩ : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
      (s : GL (Fin 4) F) * ((D4.iso kk : ↥(StatedSL 4 F)) : GL (Fin 4) F) * (s : GL (Fin 4) F)⁻¹ := by
    have hb' : (⟨barOf hv * k * (barOf hv)⁻¹, hkb⟩ : ↥D4.K) =
        D4.iso.symm s * kk * (D4.iso.symm s)⁻¹ := Subtype.ext (by
      show barOf hv * k * (barOf hv)⁻¹ = ((D4.iso.symm s : ↥D4.K) : CentralizerBar (Fr.X 4)) * k *
        ((D4.iso.symm s : ↥D4.K) : CentralizerBar (Fr.X 4))⁻¹
      rw [hbv])
    rw [hb', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simp
  have heq : D4.iso ⟨barOf hu * k * (barOf hu)⁻¹, hka⟩ =
      D4.iso ⟨barOf hv * k * (barOf hv)⁻¹, hkb⟩ := by
    apply Subtype.ext
    rw [hL, hR, hsGL]
    group
  have := D4.iso.injective heq
  exact congrArg Subtype.val this


theorem pair01 (hF3 : Nat.card F = 3) :
    ∃ W : Subgroup G, LinearBlockStandardPair F W (symJ3 Fr.X 0) (symJ3 Fr.X 1) :=
  symSystem3_pair (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act (linKind F)
    (fun a b c hab hac hbc => blkLin_standardPair a b c hab hac hbc) 0 1 rfl

theorem comm_sys (hF3 : Nat.card F = 3) (i j : Fin 4) (hij : (i : ℕ) + 1 < j) :
    ∀ a ∈ symJ3 Fr.X i, ∀ b ∈ symJ3 Fr.X j, a * b = b * a :=
  symSystem3_comm (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act i j hij


omit [Finite G] in
theorem q3_eq_one_of_central_of_equiv {A S : Type*} [Group A] [Group S] (e : A ≃* S)
    (hS : Subgroup.center S = ⊥) {z : A} (hz : ∀ w, z * w = w * z) : z = 1 := by
  have : e z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg e (hz (e.symm g))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [hS, Subgroup.mem_bot] at this
  exact e.injective (this.trans (map_one e).symm)

end Q3Frame

omit [Finite G] in
theorem card_sl3_three (hF3 : Nat.card F = 3) : Nat.card SL(3, F) = 5616 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3) (by norm_num), hF3]
  rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
  norm_num

omit [Finite G] in
theorem card_gl3_three (hF3 : Nat.card F = 3) : Nat.card (GL (Fin 3) F) = 11232 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq (K := F) 3, hF3]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by rfl, Finset.prod_insert (by norm_num),
    Finset.prod_pair (by norm_num)]
  norm_num

omit [Finite G] in
theorem center_sl3_three (hF3 : Nat.card F = 3) : Subgroup.center SL(3, F) = ⊥ := by
  have h := Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) ⟨0, by norm_num⟩).toEquiv
  rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hF3, Fintype.card_fin] at h
  have h1 : Nat.card (Subgroup.center SL(3, F)) = 1 := by
    rw [h]
    norm_num
  exact Subgroup.eq_bot_of_card_eq _ h1


omit [Finite G] in
theorem q3_isSolvable_two_three {X : Type*} [Group X] [Finite X] {a b : ℕ}
    (h : Nat.card X = 2 ^ a * 3 ^ b) : Group.IsSolvable X := by
  let _ : Fintype X := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)

omit [Finite G] in
theorem blkLin_isSolvable (hF3 : Nat.card F = 3) {a b : Fin 4} (hab : a ≠ b) :
    Group.IsSolvable ↥(blkLin (F := F) a b) := by
  obtain ⟨e⟩ := blkLin_equiv (F := F) a b hab
  have hcard : Nat.card SL(2, F) = 2 ^ 3 * 3 ^ 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 2) (by norm_num), hF3]
    rw [show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton]
    norm_num
  have : Group.IsSolvable SL(2, F) := q3_isSolvable_two_three hcard
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

omit [Finite G] in
theorem q3_isSolvable_sup_of_commute {X : Type*} [Group X] {B₁ B₂ : Subgroup X}
    (h : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) [Group.IsSolvable B₁] [Group.IsSolvable B₂] :
    Group.IsSolvable ↥(B₁ ⊔ B₂) := by
  have hc : ∀ (a : ↥B₁) (b : ↥B₂), Commute (B₁.subtype a) (B₂.subtype b) :=
    fun a b => h a a.2 b b.2
  have hr : (B₁.subtype.noncommCoprod B₂.subtype hc).range = B₁ ⊔ B₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have : Group.IsSolvable ↥(B₁.subtype.noncommCoprod B₂.subtype hc).range :=
    Group.isSolvable_of_surjective
      (B₁.subtype.noncommCoprod B₂.subtype hc).rangeRestrict_surjective
  rw [← hr]
  exact this

omit [Finite G] in
theorem q3_eq_bot_of_perfect_of_isSolvable {X : Type*} [Group X] [Finite X] {Q : Subgroup X}
    (hQ : ⁅Q, Q⁆ = Q) (hsolv : Group.IsSolvable ↥Q) : Q = ⊥ := by
  by_contra hne
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
  have : Group.IsPerfect Q := Subgroup.isPerfect_iff.mpr hQ
  have h2 : _root_.commutator Q = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  exact lt_irrefl _ h1

namespace Q3Frame

variable (Fr : Q3Frame G F)

theorem A_data (hF3 : Nat.card F = 3) :
    IsQuasisimple ↥(symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1) ∧
      Nonempty (↥(symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1) ≃* SL(3, F)) := by
  obtain ⟨W, hW⟩ := Fr.pair01 hF3
  obtain ⟨hWe, -⟩ := lin_pair_fusion (q3_two_ne_zero hF3) hW
  obtain ⟨hWq, -⟩ := lin_pair_W_facts hW
  obtain ⟨θ, c, hrange, hker, -⟩ := hW
  have hinj : Function.Injective θ :=
    (MonoidHom.ker_eq_bot_iff θ).1 (by
      rw [eq_bot_iff]
      exact hker.trans (center_sl3_three hF3).le)
  subst hWe
  refine ⟨hWq, ⟨?_⟩⟩
  exact ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm

theorem A_center (hF3 : Nat.card F = 3) :
    ∀ z ∈ symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1, (∀ w ∈ symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1, z * w = w * z) → z = 1 := by
  intro z hz hzc
  obtain ⟨-, ⟨e⟩⟩ := Fr.A_data hF3
  have := q3_eq_one_of_central_of_equiv e (center_sl3_three hF3) (z := ⟨z, hz⟩)
    (fun w => Subtype.ext (hzc w w.2))
  exact congrArg Subtype.val this

theorem A_card (hF3 : Nat.card F = 3) : Nat.card ↥(symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1) = 5616 := by
  obtain ⟨-, ⟨e⟩⟩ := Fr.A_data hF3
  rw [Nat.card_congr e.toEquiv, card_sl3_three hF3]


omit [Finite F] in
theorem central_mul_mat (hF : Nat.card F % 4 = 3) (h2 : (2 : F) ≠ 0) [Finite F]
    {s₀ : ↥(StatedSL 4 F)} (hs : s₀ ∈ Subgroup.center ↥(StatedSL 4 F)) (hs1 : s₀ ≠ 1)
    {z : ↥(StatedSL 4 F)} (hz : z ∈ blkLin (F := F) 2 3) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    (((s₀ * z : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F 0 1 := by
  have hzmat := mat_eq_zblk_of_mem_blkLin h2 (by decide : (2 : Fin 4) ≠ 3) hz hz2 hz1
  have hsmat : ((s₀ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := by
    rcases (mem_center_statedSL_four_iff hF s₀).1 hs with h | h
    · exact absurd (Subtype.ext h) hs1
    · rw [h, xGL_eq_neg_one]
      simp
  rw [Subgroup.coe_mul, Units.val_mul, hsmat, hzmat, neg_mul, one_mul,
    neg_zblkMat_eq (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]

omit [Finite F] in
theorem J1_comm_X (i : Fin 5) (hi4 : i ≠ 4) (hi0 : i ≠ 0) :
    ∀ g ∈ symJ3 Fr.X 0, Fr.X i * g = g * Fr.X i := by
  intro g hg
  have hle : symJ3 Fr.X 0 ≤ centralizer (Fr.X '' {k | k ≠ 4 ∧ k ≠ 0}) := oddRes_le _
  exact (Subgroup.mem_centralizer_iff.1 (hle hg)) (Fr.X i) ⟨i, ⟨hi4, hi0⟩, rfl⟩

theorem X23_eq_c (hF3 : Nat.card F = 3) {c : G} (hcJ : c ∈ symJ3 Fr.X 3) (hc2 : orderOf c = 2) :
    Fr.X 2 * Fr.X 3 = c := by
  rcases Fr.X23_eq hF3 hcJ hc2 with h | h
  · exact h
  exfalso
  have h2 := q3_two_ne_zero hF3
  have hF4 : Nat.card F % 4 = 3 := by rw [hF3]
  obtain ⟨s, hs, hsc, hss, hs1, hsmat⟩ := Fr.exists_s hF3 hcJ hc2
  obtain ⟨s₀, hs₀c, hs₀2, hs₀1, hs₀x⟩ := Fr.exists_s0
  obtain ⟨z, hzblk, hz2, hzc⟩ := lin_blk_center3 hF3
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz2] at this
    rw [← sq]
    exact this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmat := mat_eq_zblk_of_mem_blkLin h2 (by decide : (0 : Fin 4) ≠ 1) hzblk hzz hz1
  have hmat := central_mul_mat hF4 h2 hs₀c hs₀1 hs hss hs1
  have hsz : s₀ * s = z := by
    apply Subtype.ext
    apply Units.ext
    rw [hmat, hzmat]
  have hscomm : s * s₀ = s₀ * s := (Subgroup.mem_center_iff.1 hs₀c s).symm ▸ rfl
  have hy : Fr.X 2 * Fr.X 3 = (Fr.D 4).ι z :=
    calc Fr.X 2 * Fr.X 3 = c * Fr.X 4 := h
      _ = (Fr.D 4).ι s * (Fr.D 4).ι s₀ := by rw [hsc, hs₀x]
      _ = (Fr.D 4).ι (s * s₀) := (map_mul _ _ _).symm
      _ = (Fr.D 4).ι (s₀ * s) := by rw [hscomm]
      _ = (Fr.D 4).ι z := by rw [hsz]
  have hyJ2 : (Fr.D 4).ι z ∈ symJ3 Fr.X 1 := by
    rw [symJ3_one (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act]
    exact ⟨z, hzblk, rfl⟩
  have hyc2 : ∀ g ∈ symJ3 Fr.X 1, g * (Fr.D 4).ι z = (Fr.D 4).ι z * g := by
    rw [symJ3_one (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act]
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hzc g hg]
  have hyc1 : ∀ g ∈ symJ3 Fr.X 0, g * (Fr.D 4).ι z = (Fr.D 4).ι z * g := by
    intro g hg
    rw [← hy]
    have e2 := Fr.J1_comm_X 2 (by decide) (by decide) g hg
    have e3 := Fr.J1_comm_X 3 (by decide) (by decide) g hg
    calc g * (Fr.X 2 * Fr.X 3) = (g * Fr.X 2) * Fr.X 3 := (mul_assoc _ _ _).symm
      _ = (Fr.X 2 * g) * Fr.X 3 := by rw [← e2]
      _ = Fr.X 2 * (g * Fr.X 3) := mul_assoc _ _ _
      _ = Fr.X 2 * (Fr.X 3 * g) := by rw [← e3]
      _ = (Fr.X 2 * Fr.X 3) * g := (mul_assoc _ _ _).symm
  have hyA : (Fr.D 4).ι z ∈ symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1 := Subgroup.mem_sup_right hyJ2
  have hcentA : ∀ w ∈ symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1, (Fr.D 4).ι z * w = w * (Fr.D 4).ι z := by
    have hle : symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1 ≤ centralizer ({(Fr.D 4).ι z} : Set G) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hyc1 g hg
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hyc2 g hg
    intro w hw
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hw)).symm
  have := Fr.A_center hF3 _ hyA hcentA
  apply hz1
  apply (Fr.D 4).ι_injective
  rw [this, map_one]


omit [Finite F] in
theorem X_mul_mem_cent (i j k : Fin 5) : Fr.X i * Fr.X j ∈ centralizer ({Fr.X k} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Commute.mul_left (Fr.X_comm i k) (Fr.X_comm j k) : Commute (Fr.X i * Fr.X j) (Fr.X k))).eq

omit [Finite F] in
theorem act_X23 (hu : Fr.X 2 * Fr.X 3 ∈ centralizer ({Fr.X 2} : Set G)) :
    ActsAsReflOn (Fr.D 2).iso (barOf hu) (reflDiag F 2) := by
  have h3 : Fr.X 3 ∈ centralizer ({Fr.X 2} : Set G) := Fr.X_mem_cent 3 2
  have hact : ActsAsReflOn (Fr.D 2).iso (barOf h3) (reflDiag F 2) := Fr.act 2 2
  intro k k' hkk'
  apply hact k k'
  have hx : barOf hu = xbar (Fr.X 2) * barOf h3 := rfl
  rw [hx] at hkk'
  have hc : ∀ g : CentralizerBar (Fr.X 2), xbar (Fr.X 2) * g * (xbar (Fr.X 2))⁻¹ = g := fun g => by
    rw [← xbar_comm (Fr.X 2) g, mul_inv_cancel_right]
  rw [← hkk']
  calc barOf h3 * (k : CentralizerBar (Fr.X 2)) * (barOf h3)⁻¹
      = xbar (Fr.X 2) * (barOf h3 * (k : CentralizerBar (Fr.X 2)) * (barOf h3)⁻¹) *
          (xbar (Fr.X 2))⁻¹ := (hc _).symm
    _ = xbar (Fr.X 2) * barOf h3 * (k : CentralizerBar (Fr.X 2)) *
          (xbar (Fr.X 2) * barOf h3)⁻¹ := by group

theorem act_c (hF3 : Nat.card F = 3) {c : G} (hcJ : c ∈ symJ3 Fr.X 3) (hc2 : orderOf c = 2)
    (hcX : c ∈ centralizer ({Fr.X 2} : Set G)) :
    ActsAsReflOn (Fr.D 2).iso (barOf hcX) (reflDiag F 2) := by
  have h := Fr.X23_eq_c hF3 hcJ hc2
  subst h
  exact Fr.act_X23 hcX

theorem J1_eq_map (hF3 : Nat.card F = 3) :
    symJ3 Fr.X 0 = (blkLin (F := F) 3 0).map (Fr.D 2).ι :=
  pairResO_eq_map' (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act 2 (a := 3) (b := 0) (c := 1) (d := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem J2_eq_map (hF3 : Nat.card F = 3) :
    symJ3 Fr.X 1 = (blkLin (F := F) 0 1).map (Fr.D 2).ι :=
  pairResO_eq_map' (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act 2 (a := 0) (b := 1) (c := 2) (d := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem A_eq_map (hF3 : Nat.card F = 3) :
    symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1 =
      (blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1).map (Fr.D 2).ι := by
  rw [Fr.J1_eq_map hF3, Fr.J2_eq_map hF3, Subgroup.map_sup]

omit [Finite F] in
theorem Sigma_le_reflCent : blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1 ≤ reflCent F 2 := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · rw [mem_reflCent]
    exact blkLin_comm_refl 3 0 2 (by decide) (by decide) g hg
  · rw [mem_reflCent]
    exact blkLin_comm_refl 0 1 2 (by decide) (by decide) g hg


theorem c_mem_cent2 (hF3 : Nat.card F = 3) {c : G} (hcJ : c ∈ symJ3 Fr.X 3) (hc2 : orderOf c = 2) :
    c ∈ centralizer ({Fr.X 2} : Set G) := by
  rw [← Fr.X23_eq_c hF3 hcJ hc2]
  exact Fr.X_mul_mem_cent 2 3 2

theorem perfect_le_A (hF3 : Nat.card F = 3) {c : G} (hcJ : c ∈ symJ3 Fr.X 3) (hc2 : orderOf c = 2)
    {Q : Subgroup G} (hQ : Q ≤ centralizer ({Fr.X 2} : Set G) ⊓ centralizer ({c} : Set G))
    (hperf : ⁅Q, Q⁆ = Q) : Q ≤ symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1 := by
  set D2 := Fr.D 2 with hD2
  have h2 := q3_two_ne_zero hF3
  have hQX : Q ≤ centralizer ({Fr.X 2} : Set G) := fun q hq => (Subgroup.mem_inf.1 (hQ hq)).1
  have hQc : ∀ q ∈ Q, q * c = c * q := fun q hq =>
    mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hQ hq)).2
  have hrange : Q ≤ D2.ι.range := D2.toLayerData.le_range_ι hperf hQX
  set Q' : Subgroup ↥(StatedSL 4 F) := Q.comap D2.ι with hQ'
  have hmap : Q'.map D2.ι = Q := by
    rw [hQ', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by
    apply Subgroup.map_injective D2.ι_injective
    rw [Subgroup.map_commutator, hmap, hperf]
  have hcX := Fr.c_mem_cent2 hF3 hcJ hc2
  have hactc := Fr.act_c hF3 hcJ hc2 hcX
  have hQ'le : Q' ≤ reflCent F 2 := by
    intro t ht
    rw [mem_reflCent]
    exact D2.toLayerData.comm_of_ι_comm hcX hactc (hQc (D2.ι t) ht)
  have hSigcard : Nat.card ↥(blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1) = 5616 := by
    have hcm : Nat.card ↥((blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1).map D2.ι) =
        Nat.card ↥(blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1) :=
      Subgroup.card_map_of_injective D2.ι_injective
    rw [← Fr.A_eq_map hF3] at hcm
    exact hcm.symm.trans (Fr.A_card hF3)
  have hcard : Nat.card (reflCent F 2) ≤
      2 * Nat.card ↥(blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1) := by
    rw [hSigcard]
    calc Nat.card (reflCent F 2) ≤ Nat.card (GL (Fin 3) F) := card_reflCent_le h2 2
      _ = 11232 := card_gl3_three hF3
      _ = 2 * 5616 := by norm_num
  have hle := perfect_le_of_card_le_two_mul (Sigma_le_reflCent (F := F)) hcard hQ'le hQ'perf
  rw [← hmap, Fr.A_eq_map hF3]
  exact Subgroup.map_mono hle


theorem perfect_eq_bot_cent_x (hF3 : Nat.card F = 3) {c : G} (hcJ : c ∈ symJ3 Fr.X 3)
    (hc2 : orderOf c = 2) {Q : Subgroup G}
    (hQ : Q ≤ centralizer ({Fr.X 4} : Set G) ⊓ centralizer ({c} : Set G)) (hperf : ⁅Q, Q⁆ = Q) :
    Q = ⊥ := by
  set D4 := Fr.D 4 with hD4
  have h2 := q3_two_ne_zero hF3
  obtain ⟨s, hs, hsc, hss, hs1, -⟩ := Fr.exists_s hF3 hcJ hc2
  have hQX : Q ≤ centralizer ({Fr.X 4} : Set G) := fun q hq => (Subgroup.mem_inf.1 (hQ hq)).1
  have hrange : Q ≤ D4.ι.range := D4.toLayerData.le_range_ι hperf hQX
  set Q' : Subgroup ↥(StatedSL 4 F) := Q.comap D4.ι with hQ'
  have hmap : Q'.map D4.ι = Q := by
    rw [hQ', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by
    apply Subgroup.map_injective D4.ι_injective
    rw [Subgroup.map_commutator, hmap, hperf]
  have hcomm : ∀ g ∈ Q', g * s = s * g := by
    intro g hg
    have hg' : D4.ι g ∈ Q := hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hQ hg')).2
    rw [← hsc, ← map_mul, ← map_mul] at h1
    exact D4.ι_injective h1
  have hle := perfect_le_pair_lin h2 (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hs hss hs1 Q' hcomm hQ'perf
  have hsolv : Group.IsSolvable ↥(blkLin (F := F) 0 1 ⊔ blkLin (F := F) 2 3) := by
    have := blkLin_isSolvable (F := F) hF3 (a := 0) (b := 1) (by decide)
    have := blkLin_isSolvable (F := F) hF3 (a := 2) (b := 3) (by decide)
    exact q3_isSolvable_sup_of_commute (fun a ha b hb => blkLin_commute 0 1 2 3
      (by decide) (by decide) (by decide) (by decide) a ha b hb)
  have hQ's : Group.IsSolvable ↥Q' := by
    have : Group.IsSolvable ↥(Q'.subgroupOf (blkLin (F := F) 0 1 ⊔ blkLin (F := F) 2 3)) :=
      inferInstance
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom) (Subgroup.subgroupOfEquivOfLe hle).surjective
  have hbot : Q' = ⊥ := q3_eq_bot_of_perfect_of_isSolvable hQ'perf hQ's
  rw [← hmap, hbot, Subgroup.map_bot]

end Q3Frame

end CFSG.GH74.Generic.S1

