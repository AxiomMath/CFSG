module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VBar
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.I2_5

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification Subgroup
open scoped Pointwise commutatorElement

section Cyc

variable {G : Type} [Group G] [Finite G]

@[expose] def i183vM (x : G) (M : Subgroup G) (n : ℕ) : Subgroup G := GLBConj (x ^ n) M

theorem i183vM_zero (x : G) (M : Subgroup G) : i183vM x M 0 = M := by
  simp [i183vM, gLBConj_one]

theorem i183vM_one (x : G) (M : Subgroup G) : i183vM x M 1 = GLBConj x M := by
  simp [i183vM]

theorem i183vM_two (x : G) (M : Subgroup G) : i183vM x M 2 = GLBConj x (GLBConj x M) := by
  simp [i183vM, gLBConj_gLBConj, pow_two]

theorem i183vM_mod {x : G} (hx3 : x ^ 3 = 1) (M : Subgroup G) (n : ℕ) :
    i183vM x M n = i183vM x M (n % 3) := by
  unfold i183vM
  congr 1
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx3, one_pow, mul_one]

theorem i183vM_conj (x : G) (M : Subgroup G) (n r : ℕ) :
    GLBConj (x ^ r) (i183vM x M n) = i183vM x M (n + r) := by
  simp [i183vM, gLBConj_gLBConj, pow_add]

structure I183vCyc (X : Subgroup G) (x : G) (M : Subgroup G) : Prop where
  hxX : x ∈ X
  hx3 : x ^ 3 = 1
  hM : GLAPComponent 3 X M
  h1 : GLBConj x M ≠ M
  h2 : GLBConj x (GLBConj x M) ≠ M

variable {X : Subgroup G} {x : G} {M : Subgroup G}

theorem i183vM_component (c : I183vCyc X x M) (n : ℕ) : GLAPComponent 3 X (i183vM x M n) := by
  have := glaPComponent_gLBConj c.hM (x ^ n)
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (pow_mem c.hxX n))] at this

theorem i183vM_ne (c : I183vCyc X x M) {a b : ℕ} (hab : a % 3 ≠ b % 3) :
    i183vM x M a ≠ i183vM x M b := by
  have h12 : GLBConj x M ≠ GLBConj x (GLBConj x M) := by
    intro h
    apply c.h1
    have := congrArg (GLBConj x⁻¹) h
    rw [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this
    exact this.symm
  rw [i183vM_mod c.hx3 M a, i183vM_mod c.hx3 M b]
  have ha : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hb : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize a % 3 = r at *
  generalize b % 3 = s at *
  interval_cases r <;> interval_cases s <;>
    first
    | exact absurd rfl hab
    | simp only [i183vM_zero, i183vM_one, i183vM_two]
      first
      | exact c.h1.symm | exact c.h1 | exact c.h2.symm | exact c.h2 | exact h12 | exact h12.symm

@[expose] def i183vMb (X : Subgroup G) (x : G) (M : Subgroup G) (n : ℕ) :
    Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := barX 3 X (i183vM x M n)

@[expose] def i183vKb (X : Subgroup G) (x : G) (M : Subgroup G) :
    Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
  i183vMb X x M 0 ⊔ i183vMb X x M 1 ⊔ i183vMb X x M 2

theorem i183vMb_mod (c : I183vCyc X x M) (n : ℕ) :
    i183vMb X x M n = i183vMb X x M (n % 3) := by
  unfold i183vMb
  rw [i183vM_mod c.hx3 M n]

theorem i183vMb_comp (c : I183vCyc X x M) (n : ℕ) :
    IsComponentOf (i183vMb X x M n) ⊤ := (i183vM_component c n).2.2.1

theorem i183vMb_ne (c : I183vCyc X x M) {a b : ℕ} (hab : a % 3 ≠ b % 3) :
    i183vMb X x M a ≠ i183vMb X x M b := fun h =>
  i183vM_ne c hab (glaPComponent_unique (i183vM_component c a) (i183vM_component c b) h)

theorem i183vMb_comm (c : I183vCyc X x M) {a b : ℕ} (hab : a % 3 ≠ b % 3) :
    ⁅i183vMb X x M a, i183vMb X x M b⁆ = ⊥ :=
  LocalComponents.commute_of_ne _ _ (i183vMb_comp c a) (i183vMb_comp c b) (i183vMb_ne c hab)

theorem i183vMb_le_Kb (c : I183vCyc X x M) (n : ℕ) : i183vMb X x M n ≤ i183vKb X x M := by
  rw [i183vMb_mod c n]
  have hn : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = r at *
  unfold i183vKb
  interval_cases r
  · exact le_sup_of_le_left le_sup_left
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right

theorem i183vKb_le_normalizer (c : I183vCyc X x M) (n : ℕ) :
    i183vKb X x M ≤ Subgroup.normalizer (i183vMb X x M n : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  have key : ∀ j : ℕ, i183vMb X x M j ≤
      Subgroup.normalizer (i183vMb X x M n : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro j
    by_cases hj : j % 3 = n % 3
    · rw [i183vMb_mod c j, hj, ← i183vMb_mod c n]
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (i183vMb_comm c hj)).trans
        (Subgroup.centralizer_le_normalizer _)
  exact sup_le (sup_le (key 0) (key 1)) (key 2)

theorem i183vMb_component_Kb (c : I183vCyc X x M) (n : ℕ) :
    IsComponentOf (i183vMb X x M n) (i183vKb X x M) := by
  have hle := i183vMb_le_Kb c n
  refine ⟨hle, ?_, (i183vMb_comp c n).2.2⟩
  refine CFSG.Quasithin.A3.subnormal_of_normal hle ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  exact i183vKb_le_normalizer c n

theorem i183vKb_components (c : I183vCyc X x M) {C : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)}
    (hC : IsComponentOf C (i183vKb X x M)) : ∃ n : ℕ, n < 3 ∧ C = i183vMb X x M n := by
  by_contra hne
  have hne' : ∀ n : ℕ, C ≠ i183vMb X x M n := fun n h =>
    hne ⟨n % 3, Nat.mod_lt _ (by norm_num), h.trans (i183vMb_mod c n)⟩
  have hcomm : ∀ n : ℕ, i183vMb X x M n ≤ Subgroup.centralizer (C : Set _) := by
    intro n y hy z hz
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hC
        (i183vMb_component_Kb c n) with h | h
    · exact absurd h (hne' n)
    · exact h z hz y hy
  have hK : i183vKb X x M ≤ Subgroup.centralizer (C : Set _) :=
    sup_le (sup_le (hcomm 0) (hcomm 1)) (hcomm 2)
  have hbot : ⁅C, C⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hC.1.trans hK)
  rw [i25_commutator_eq hC.2.2] at hbot
  have := Quasisimple.nontrivial hC.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 this hbot

theorem gLBConj_sup' (g : G) (A B : Subgroup G) : GLBConj g (A ⊔ B) = GLBConj g A ⊔ GLBConj g B :=
  Subgroup.map_sup A B _

theorem i183vEb_mem (hxX : x ∈ X) (hx3 : x ^ 3 = 1)
    {e : ↥X ⧸ GLAPPrimeCore 3 ↥X} (he : e ∈ barX 3 X (Subgroup.zpowers x)) :
    ∃ r : ℕ, r < 3 ∧ ∃ h : x ^ r ∈ X, e = QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x ^ r, h⟩ := by
  obtain ⟨a, ha, rfl⟩ := he
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_subgroupOf).1 ha)
  have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  have h1 : x ^ k = x ^ (k % 3) := zpow_eq_zpow_emod k hx3'
  have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  refine ⟨(k % 3).toNat, by omega, pow_mem hxX _, ?_⟩
  congr 1
  apply Subtype.ext
  show (a : G) = x ^ (k % 3).toNat
  rw [← hk, h1, ← zpow_natCast, Int.toNat_of_nonneg hnn]

theorem mk_mem_Eb (hxX : x ∈ X) (r : ℕ) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x ^ r, pow_mem hxX r⟩ ∈
      barX 3 X (Subgroup.zpowers x) :=
  ⟨⟨x ^ r, pow_mem hxX r⟩, (Subgroup.mem_subgroupOf).2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) r),
    rfl⟩

theorem i183vMb_conj (c : I183vCyc X x M) (r n : ℕ) :
    GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x ^ r, pow_mem c.hxX r⟩)
        (i183vMb X x M n) = i183vMb X x M (n + r) := by
  unfold i183vMb
  rw [← i183vM_conj x M n r]
  exact (i183v_barX_gLBConj (pow_mem c.hxX r) _).symm

theorem i183vKb_gLBConj_le (c : I183vCyc X x M) {e : ↥X ⧸ GLAPPrimeCore 3 ↥X}
    (he : e ∈ barX 3 X (Subgroup.zpowers x)) : GLBConj e (i183vKb X x M) ≤ i183vKb X x M := by
  obtain ⟨r, -, h, rfl⟩ := i183vEb_mem c.hxX c.hx3 he
  unfold i183vKb
  rw [gLBConj_sup', gLBConj_sup', i183vMb_conj c, i183vMb_conj c, i183vMb_conj c]
  exact sup_le (sup_le (i183vMb_le_Kb c _) (i183vMb_le_Kb c _)) (i183vMb_le_Kb c _)

theorem i183vEb_le_normalizer (c : I183vCyc X x M) :
    barX 3 X (Subgroup.zpowers x) ≤
      Subgroup.normalizer (i183vKb X x M : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := fun e he =>
  mem_normalizer_iff_gLBConj_eq.2 (le_antisymm (i183vKb_gLBConj_le c he) (by
    have h := gLBConj_mono e (i183vKb_gLBConj_le c (Subgroup.inv_mem _ he))
    rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h))

theorem i183v_isElemAbelian_zpowers (hx : x ^ 3 = 1) : IsElemAbelian 3 (Subgroup.zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers hx

theorem i183v_apply_I25 (c : I183vCyc X x M) :
    (∀ X₁ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), IsComponentOf X₁ (i183vKb X x M) →
      ∃ (Z : Subgroup ↥X₁) (_ : Z.Normal), Z ≤ Subgroup.center ↥X₁ ∧
        Nonempty (↥(GLALayer (i183vKb X x M ⊓ Subgroup.centralizer
          (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ≃* (↥X₁ ⧸ Z))) ∧
    i183vKb X x M ⊓ Subgroup.centralizer
        (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) =
      GLALayer (i183vKb X x M ⊓ Subgroup.centralizer
        (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) ⊔
        ((Subgroup.center ↥(i183vKb X x M)).map (i183vKb X x M).subtype ⊓
          Subgroup.centralizer (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) := by
  refine input2_5_proved _ 3 Nat.prime_three (i183vKb X x M) (barX 3 X (Subgroup.zpowers x))
    ?_ (i183vEb_le_normalizer c) (isElemAbelian_barX (i183v_isElemAbelian_zpowers c.hx3)) ?_ ?_
  · refine le_antisymm (i25_layer_le _) ?_
    unfold i183vKb
    exact sup_le (sup_le (i25_le_layer (i183vMb_component_Kb c 0))
      (i25_le_layer (i183vMb_component_Kb c 1))) (i25_le_layer (i183vMb_component_Kb c 2))
  · intro L L' hL hL'
    obtain ⟨a, ha, rfl⟩ := i183vKb_components c hL
    obtain ⟨b, hb, rfl⟩ := i183vKb_components c hL'
    refine ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x ^ ((b + 3 - a) % 3), pow_mem c.hxX _⟩,
      mk_mem_Eb c.hxX _, ?_⟩
    rw [i183vMb_conj c, i183vMb_mod c (a + (b + 3 - a) % 3), i183vMb_mod c b]
    congr 1
    omega
  · intro e he he1 L hL
    obtain ⟨a, -, rfl⟩ := i183vKb_components c hL
    obtain ⟨r, hr, h, rfl⟩ := i183vEb_mem c.hxX c.hx3 he
    intro h2
    rw [i183vMb_conj c] at h2
    by_cases hr0 : r = 0
    · apply he1
      subst hr0
      have : (⟨x ^ 0, h⟩ : ↥X) = 1 := Subtype.ext (by simp)
      rw [this, map_one]
    · exact i183vMb_ne c (by omega) h2

theorem i183v_not_le_core {H J : Subgroup G} (hJ : GLAPComponent 3 H J) (hHX : H ≤ X) :
    ¬ J ≤ GLAPPrimeCoreOf 3 X := by
  intro h
  have h1 := LocalBalance.gLAPPrimeCoreOf_inf_le Nat.prime_three X H
  rw [inf_eq_right.2 hHX] at h1
  have h2 : J ≤ GLAPPrimeCoreOf 3 H := fun j hj => h1 ⟨h hj, hJ.1 hj⟩
  have h3 : barX 3 H J = ⊥ := (i183_barX_eq_bot_iff hJ.1).2 h2
  have hnt := Quasisimple.nontrivial hJ.2.2.1.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h3

theorem i183v_Jb_le_Kb (c : I183vCyc X x M) {J : Subgroup G}
    (hJK : J ≤ M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M)) :
    barX 3 X J ≤ i183vKb X x M := by
  have hMX : ∀ n, i183vM x M n ≤ X := fun n => (i183vM_component c n).1
  have e : barX 3 X (i183vM x M 0 ⊔ i183vM x M 1 ⊔ i183vM x M 2) = i183vKb X x M := by
    unfold i183vKb i183vMb
    rw [i183_barX_sup (sup_le (hMX 0) (hMX 1)) (hMX 2), i183_barX_sup (hMX 0) (hMX 1)]
  rw [← e]
  refine barX_mono 3 ?_
  rw [i183vM_zero, i183vM_one, i183vM_two]
  exact hJK

theorem i183v_comm_le {Y : Type*} [Group Y] {K D W C : Subgroup Y} (hC : C = D ⊔ W)
    (hCK : C ≤ K) (hWK : W ≤ K) (hW : ∀ w ∈ W, ∀ g ∈ K, Commute w g) : ⁅C, C⁆ ≤ D := by
  have hDK : D ≤ K := (le_sup_left.trans hC.ge).trans hCK
  have hWN : W ≤ Subgroup.normalizer (D : Set Y) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro d
    have hc : ∀ e ∈ D, w * e * w⁻¹ = e := fun e he => by
      rw [(hW w hw e (hDK he)).eq, mul_assoc, mul_inv_cancel, mul_one]
    have hc' : ∀ e ∈ D, w⁻¹ * e * w = e := fun e he => by
      rw [(hW w⁻¹ (W.inv_mem hw) e (hDK he)).eq, mul_assoc, inv_mul_cancel, mul_one]
    constructor
    · intro hd
      rw [hc d hd]
      exact hd
    · intro hd
      have h2 := hc' _ hd
      rw [show w⁻¹ * (w * d * w⁻¹) * w = d by group] at h2
      exact h2 ▸ hd
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [hC] at ha hb
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left D W hWN
  have ha' : a ∈ (D : Set Y) * (W : Set Y) := by rw [← hmul]; exact ha
  have hb' : b ∈ (D : Set Y) * (W : Set Y) := by rw [← hmul]; exact hb
  obtain ⟨d₁, hd₁, w₁, hw₁, rfl⟩ := ha'
  obtain ⟨d₂, hd₂, w₂, hw₂, rfl⟩ := hb'
  rw [i25_commutatorElement_mul_mul (hW w₁ hw₁ d₂ (hDK hd₂)) (hW w₁ hw₁ w₂ (hWK hw₂))
    (hW w₂ hw₂ d₁ (hDK hd₁))]
  exact D.mul_mem (D.mul_mem (D.mul_mem hd₁ hd₂) (D.inv_mem hd₁)) (D.inv_mem hd₂)

theorem i183v_Jb_eq_layer (c : I183vCyc X x M) {J : Subgroup G}
    (hJ : GLAPComponent 3 (X ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hJK : J ≤ M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M)) :
    barX 3 X J = GLALayer (i183vKb X x M ⊓
      Subgroup.centralizer (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) := by
  classical
  obtain ⟨hconc1, hconc2⟩ := i183v_apply_I25 c
  have hHX : X ⊓ Subgroup.centralizer ({x} : Set G) ≤ X := inf_le_left
  have hJX : J ≤ X := hJ.1.trans hHX
  have hJb1 : barX 3 X J ≤ i183vKb X x M := i183v_Jb_le_Kb c hJK
  have hJb2 : barX 3 X J ≤ Subgroup.centralizer
      (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    refine barX_le_centralizer fun s hs t ht _ _ => ?_
    have hsx : Commute s x := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hs).2
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    have hc : Commute s (x ^ k) := hsx.zpow_right k
    have h1 : s * x ^ k * s⁻¹ * (x ^ k)⁻¹ = 1 := by rw [hc.eq]; group
    rw [h1]
    exact Subgroup.one_mem _
  have hJb3 : ⁅barX 3 X J, barX 3 X J⁆ = barX 3 X J := by
    rw [← barX_commutator 3 hJX hJX, glaPComponent_perfect hJ]
  have hJbC : barX 3 X J ≤ i183vKb X x M ⊓ Subgroup.centralizer
      (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := le_inf hJb1 hJb2
  have hcomm := i183v_comm_le (K := i183vKb X x M) hconc2 inf_le_left
    (inf_le_left.trans (Subgroup.map_subtype_le _)) (by
      rintro _ ⟨hw, -⟩ g hg
      obtain ⟨z, hz, rfl⟩ := hw
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)).symm)
  have hJbD : barX 3 X J ≤ GLALayer (i183vKb X x M ⊓ Subgroup.centralizer
      (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) :=
    calc barX 3 X J = ⁅barX 3 X J, barX 3 X J⁆ := hJb3.symm
      _ ≤ _ := Subgroup.commutator_mono hJbC hJbC
      _ ≤ _ := hcomm
  have hEX : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.2 c.hxX
  have hEp : IsPGroup 3 ↥(Subgroup.zpowers x) :=
    isPGroup_of_isElemAbelian' (i183v_isElemAbelian_zpowers c.hx3)
  have hcz : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCY := i183_centralizer_barX_le Nat.prime_three hEX hEp
  rw [hcz] at hCY
  have hsn : IsSubnormal (barX 3 X J) (barX 3 X (X ⊓ Subgroup.centralizer ({x} : Set G))) :=
    isSubnormal_barX 3 hJ.2.1
  have hDle : GLALayer (i183vKb X x M ⊓ Subgroup.centralizer
      (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) ≤
      barX 3 X (X ⊓ Subgroup.centralizer ({x} : Set G)) :=
    (i25_layer_le _).trans (inf_le_right.trans hCY)
  have hsnD := isSubnormal_of_le_of_le hsn hJbD hDle
  have hMc : IsComponentOf (barX 3 X M) (i183vKb X x M) := by
    have e : i183vMb X x M 0 = barX 3 X M := by
      unfold i183vMb
      rw [i183vM_zero]
    have := i183vMb_component_Kb c 0
    rwa [e] at this
  obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := hconc1 _ hMc
  have hQD : CFSG.Open.IsQuasisimple ↥(GLALayer (i183vKb X x M ⊓ Subgroup.centralizer
      (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) := by
    have := hZn
    exact Components.quasisimple_of_equiv φ (Quasisimple.central_quotient hMc.2.2 Z hZc)
  rcases i183v_eq_or_le_center hsnD hQD with h | h
  · exact h
  · exfalso
    have hab : ⁅barX 3 X J, barX 3 X J⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨z, hz, rfl⟩ := h hb
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨a, hJbD ha⟩)).symm
    rw [hJb3] at hab
    exact i183v_not_le_core hJ hHX ((i183_barX_eq_bot_iff hJX).1 hab)

theorem i183v_diag (c : I183vCyc X x M) {J : Subgroup G}
    (hJ : GLAPComponent 3 (X ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hJK : J ≤ M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M)) :
    ∃ (Z : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) (_ : Z.Normal),
      Z ≤ Subgroup.center (↥M ⧸ GLAPPrimeCore 3 ↥M) ∧
        Nonempty ((↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* ((↥M ⧸ GLAPPrimeCore 3 ↥M) ⧸ Z)) := by
  classical
  obtain ⟨hconc1, -⟩ := i183v_apply_I25 c
  have hHX : X ⊓ Subgroup.centralizer ({x} : Set G) ≤ X := inf_le_left
  have hJX : J ≤ X := hJ.1.trans hHX
  have hDJ := i183v_Jb_eq_layer c hJ hJK
  set D := GLALayer (i183vKb X x M ⊓ Subgroup.centralizer
      (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) with hD
  have hMc : IsComponentOf (barX 3 X M) (i183vKb X x M) := by
    have e : i183vMb X x M 0 = barX 3 X M := by
      unfold i183vMb
      rw [i183vM_zero]
    have := i183vMb_component_Kb c 0
    rwa [e] at this
  obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := hconc1 _ hMc
  have hQD : CFSG.Open.IsQuasisimple ↥D := by
    have := hZn
    exact Components.quasisimple_of_equiv φ (Quasisimple.central_quotient hMc.2.2 Z hZc)
  let e0 := quotEquivBarX Nat.prime_three c.hM.1 c.hM.2.1
  have hcoreMc : GLAPPrimeCore 3 ↥(barX 3 X M) = ⊥ := by
    rw [← glaPPrimeCore_map_iso 3 e0, glaPPrimeCore_quotient_eq_bot Nat.prime_three, Subgroup.map_bot]
  let ρ : ↥J →* (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (Subgroup.inclusion hJX)
  have hrange : ρ.range = D := by
    rw [← hDJ]
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Subgroup.inclusion hJX j, (Subgroup.mem_subgroupOf).2 j.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, (Subgroup.mem_subgroupOf).1 ha⟩, rfl⟩
  have hker1 : ρ.ker ≤ GLAPPrimeCore 3 ↥J := by
    refine le_sSup ⟨MonoidHom.normal_ker ρ, ?_⟩
    have hle : ρ.ker.map J.subtype ≤ GLAPPrimeCoreOf 3 X := by
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨⟨u, hJX u.2⟩, (QuotientGroup.eq_one_iff _).1 hu, rfl⟩
    have hdvd : Nat.card ρ.ker ∣ Nat.card (GLAPPrimeCoreOf 3 X) := by
      rw [← Subgroup.card_map_of_injective J.subtype_injective (f := J.subtype)]
      exact Subgroup.card_dvd_of_le hle
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd =>
      not_dvd_card_glaPPrimeCoreOf Nat.prime_three X (hd.trans hdvd)
  have hker2 : GLAPPrimeCore 3 ↥J ≤ ρ.ker := by
    let N : Subgroup ↥D := ((GLAPPrimeCore 3 ↥J).map ρ).subgroupOf D
    have hN : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨u, hu, hun⟩ := (Subgroup.mem_subgroupOf).1 hn
      obtain ⟨j, hj⟩ : (g : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ ρ.range := by
        rw [hrange]; exact g.2
      refine (Subgroup.mem_subgroupOf).2 ⟨j * u * j⁻¹,
        (GLAPPrimeCore.normal 3 ↥J).conj_mem u hu j, ?_⟩
      rw [map_mul, map_mul, map_inv, hj, hun]
      simp
    have := hN
    rcases Quasisimple.normal_le_center_or_eq_top hQD N with hNc | hNtop
    · intro u hu
      rw [MonoidHom.mem_ker]
      let nD : ↥D := ⟨ρ u, by rw [← hrange]; exact ⟨u, rfl⟩⟩
      have hnN : nD ∈ N := (Subgroup.mem_subgroupOf).2 ⟨u, hu, rfl⟩
      have hnc : nD ∈ Subgroup.center ↥D := hNc hnN
      have hq : φ nD ∈ Subgroup.center (↥(barX 3 X M) ⧸ Z) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := φ.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hnc g']
      have hord : Nat.Coprime 3 (orderOf (φ nD)) := by
        have h1 : orderOf nD = orderOf (ρ u) := (Subgroup.orderOf_coe nD).symm
        have h2 : orderOf (ρ u) ∣ orderOf u := orderOf_map_dvd ρ u
        have h3 : orderOf u ∣ Nat.card (GLAPPrimeCore 3 ↥J) := by
          rw [← Subgroup.orderOf_mk u hu]
          exact orderOf_dvd_natCard _
        have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) :=
          CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)
        rw [MulEquiv.orderOf_eq, h1]
        exact hcop.coprime_dvd_right (h2.trans h3)
      have h0 := i183v_center_quotient_trivial hMc.2.2 hcoreMc Z hZc hq hord
      have hn1 : nD = 1 := φ.injective (by rw [h0, map_one])
      exact congrArg Subtype.val hn1
    · exfalso
      have hU : GLAPPrimeCore 3 ↥J = ⊤ := by
        rw [eq_top_iff]
        intro u0 _
        have hmem : (⟨ρ u0, by rw [← hrange]; exact ⟨u0, rfl⟩⟩ : ↥D) ∈ N := by
          rw [hNtop]
          exact Subgroup.mem_top _
        obtain ⟨u, hu, hρ⟩ := (Subgroup.mem_subgroupOf).1 hmem
        have hk : u⁻¹ * u0 ∈ ρ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, inv_mul_cancel]
        have := (GLAPPrimeCore 3 ↥J).mul_mem hu (hker1 hk)
        simpa using this
      have hJc : J ≤ GLAPPrimeCoreOf 3 J := by
        intro j hj
        refine ⟨⟨j, hj⟩, ?_, rfl⟩
        rw [hU]
        exact Subgroup.mem_top _
      have h2 := glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hJ.2.1
      exact i183v_not_le_core (X := X ⊓ Subgroup.centralizer ({x} : Set G)) hJ le_rfl (hJc.trans h2)
  have hker : ρ.ker = GLAPPrimeCore 3 ↥J := le_antisymm hker1 hker2
  have eJ : (↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* ↥D :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange ρ)).trans (MulEquiv.subgroupCongr hrange)
  have hZ'n : (Z.map e0.symm.toMonoidHom).Normal := hZn.map _ e0.symm.surjective
  refine ⟨Z.map e0.symm.toMonoidHom, hZ'n, ?_,
    ⟨eJ.trans (φ.trans (QuotientGroup.congr Z (Z.map e0.symm.toMonoidHom) e0.symm rfl))⟩⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply e0.injective
  simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
  exact Subgroup.mem_center_iff.1 (hZc hz) (e0 g)

end Cyc

end CFSG.HardMathSupport.Solomon.Coordinator
