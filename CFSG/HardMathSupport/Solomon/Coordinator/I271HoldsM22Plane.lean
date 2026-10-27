module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsM22Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Split
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.M22Plane

open Equiv CFSG.Open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.LieType.SeitzGeneration
open scoped Pointwise

abbrev G : Type := ↥CFSG.Blueprint.NativeSporadic.M22

theorem wp_mem (w : List (Fin 3)) : wp w ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  refine Subgroup.list_prod_mem _ fun z hz => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
  fin_cases i
  · exact m22a.2
  · exact m22b.2
  · exact CFSG.Blueprint.NativeSporadic.M22.inv_mem m22b.2

@[expose] def eG (w : List (Fin 3)) : G := ⟨wp w, wp_mem w⟩

theorem eG_coe (w : List (Fin 3)) : ((eG w : G) : Perm (Fin 22)) = wp w := rfl

theorem sp_mem (i : Fin 8) : sp i ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  fin_cases i
  · exact wp_mem w0
  · exact wp_mem w1
  · exact wp_mem w2
  · exact wp_mem w3
  · exact CFSG.Blueprint.NativeSporadic.M22.inv_mem (wp_mem w0)
  · exact CFSG.Blueprint.NativeSporadic.M22.inv_mem (wp_mem w1)
  · exact CFSG.Blueprint.NativeSporadic.M22.inv_mem (wp_mem w2)
  · exact CFSG.Blueprint.NativeSporadic.M22.inv_mem (wp_mem w3)

@[expose] def sG (i : Fin 8) : G := ⟨sp i, sp_mem i⟩

@[expose] def P0 : Subgroup G := Subgroup.zpowers (eG wx) ⊔ Subgroup.zpowers (eG wy)

theorem eG_x3 : eG wx ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, eG_coe]
  exact wp_x3

theorem eG_y3 : eG wy ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, eG_coe]
  exact wp_y3

theorem eG_xy : eG wx * eG wy = eG wy * eG wx := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, eG_coe, eG_coe]
  exact wp_xy

theorem eG_x_ne_one : eG wx ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  rw [eG_coe, Subgroup.coe_one] at this
  exact wp_x_ne_one this

theorem eG_y_ne_one : eG wy ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  rw [eG_coe, Subgroup.coe_one] at this
  exact wp_y_ne_one this

theorem eG_y_ne_x : eG wy ≠ eG wx := by
  intro h
  have := congrArg Subtype.val h
  rw [eG_coe, eG_coe] at this
  exact wp_y_ne_x this

theorem eG_y_ne_xx : eG wy ≠ eG wx * eG wx := by
  intro h
  have := congrArg Subtype.val h
  rw [Subgroup.coe_mul, eG_coe, eG_coe] at this
  exact wp_y_ne_xx this

theorem x_mem : eG wx ∈ P0 := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
theorem y_mem : eG wy ∈ P0 := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem ref_closure :
    Subgroup.closure {s : G | ∃ p ∈ P0, p ≠ 1 ∧ p * s = s * p} = ⊤ := by
  set F : Set G := {s : G | ∃ p ∈ P0, p ≠ 1 ∧ p * s = s * p} with hF
  have hxy_mem : eG wx * eG wy ∈ P0 := P0.mul_mem x_mem y_mem
  have hxyy_mem : eG wx * eG wy * eG wy ∈ P0 := P0.mul_mem hxy_mem y_mem
  have hxyy_ne : eG wx * eG wy * eG wy ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, eG_coe, eG_coe, Subgroup.coe_one] at this
    exact wp_xyy_ne_one this
  have hc0 : eG wx * eG w0 = eG w0 * eG wx := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, eG_coe, eG_coe]
    exact wp_s0_comm.symm
  have hc1 : (eG wx * eG wy * eG wy) * eG w1 = eG w1 * (eG wx * eG wy * eG wy) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, eG_coe, eG_coe, eG_coe]
    exact wp_s1_comm.symm
  have hc2 : eG wx * eG w2 = eG w2 * eG wx := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, eG_coe, eG_coe]
    exact wp_s2_comm.symm
  have hc3 : eG wy * eG w3 = eG w3 * eG wy := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, eG_coe, eG_coe]
    exact wp_s3_comm.symm
  have h0 : eG w0 ∈ F := ⟨eG wx, x_mem, eG_x_ne_one, hc0⟩
  have h1 : eG w1 ∈ F := ⟨eG wx * eG wy * eG wy, hxyy_mem, hxyy_ne, hc1⟩
  have h2 : eG w2 ∈ F := ⟨eG wx, x_mem, eG_x_ne_one, hc2⟩
  have h3 : eG w3 ∈ F := ⟨eG wy, y_mem, eG_y_ne_one, hc3⟩
  have hsG : ∀ i : Fin 8, sG i ∈ Subgroup.closure F := by
    intro i
    have e0 : sG 0 = eG w0 := rfl
    have e1 : sG 1 = eG w1 := rfl
    have e2 : sG 2 = eG w2 := rfl
    have e3 : sG 3 = eG w3 := rfl
    have e4 : sG 4 = (eG w0)⁻¹ := rfl
    have e5 : sG 5 = (eG w1)⁻¹ := rfl
    have e6 : sG 6 = (eG w2)⁻¹ := rfl
    have e7 : sG 7 = (eG w3)⁻¹ := rfl
    fin_cases i
    · exact (e0 ▸ Subgroup.subset_closure h0 : sG 0 ∈ _)
    · exact (e1 ▸ Subgroup.subset_closure h1 : sG 1 ∈ _)
    · exact (e2 ▸ Subgroup.subset_closure h2 : sG 2 ∈ _)
    · exact (e3 ▸ Subgroup.subset_closure h3 : sG 3 ∈ _)
    · exact (e4 ▸ (Subgroup.closure F).inv_mem (Subgroup.subset_closure h0) : sG 4 ∈ _)
    · exact (e5 ▸ (Subgroup.closure F).inv_mem (Subgroup.subset_closure h1) : sG 5 ∈ _)
    · exact (e6 ▸ (Subgroup.closure F).inv_mem (Subgroup.subset_closure h2) : sG 6 ∈ _)
    · exact (e7 ▸ (Subgroup.closure F).inv_mem (Subgroup.subset_closure h3) : sG 7 ∈ _)
  have hb : m22b ∈ Subgroup.closure F := by
    have hbw : m22b = (wb.map sG).prod := by
      apply Subtype.ext
      rw [show ((wb.map sG).prod : G) = ((wb.map sG).prod : G) from rfl]
      have := map_list_prod (Subgroup.subtype CFSG.Blueprint.NativeSporadic.M22) (wb.map sG)
      simp only [Subgroup.coe_subtype] at this
      rw [this, List.map_map]
      exact m22_b_word
    rw [hbw]
    exact Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact hsG i
  have ha : m22a ∈ Subgroup.closure F := by
    have : m22a = eG w0 := Subtype.ext wp_w0.symm
    rw [this]
    exact Subgroup.subset_closure h0
  have hgen := closure_pair_eq_top m22_eq m22a.2 m22b.2
  rw [eq_top_iff, ← hgen]
  rw [Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | hz
  · exact ha
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hb

theorem card_sup_zpowers_three {Ω : Type*} [Group Ω] [Finite Ω] {x y : Ω} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) (hyx : y ≠ x)
    (hyxx : y ≠ x * x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hPcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hox]
  have hQcard : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hoy]
  have hyP : y ∉ Subgroup.zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have hmod : x ^ (k % 3) = y := by
      rw [← hk]
      have := zpow_mod_orderOf x k
      rw [hox] at this
      exact_mod_cast this
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · rw [h0] at hmod; simp at hmod; exact hy1 hmod.symm
    · rw [h1] at hmod; simp at hmod; exact hyx hmod.symm
    · rw [h2, zpow_two] at hmod; exact hyxx hmod.symm
  have hcQ : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (hxy : Commute x y) m n).eq
  have hPQ : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    by_contra hne
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hzP : (z : Ω) ∈ Subgroup.zpowers x := z.2.1
    have hzQ : (z : Ω) ∈ Subgroup.zpowers y := z.2.2
    have hz1' : (z : Ω) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzo : orderOf (z : Ω) = 3 := by
      have : (z : Ω) ^ 3 = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzP
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
      exact orderOf_eq_prime this hz1'
    have hzPe : Subgroup.zpowers (z : Ω) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzP)
        (by rw [hPcard, Nat.card_zpowers, hzo])
    have hzQe : Subgroup.zpowers (z : Ω) = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzQ)
        (by rw [hQcard, Nat.card_zpowers, hzo])
    apply hyP
    rw [← hzPe, hzQe]
    exact Subgroup.mem_zpowers y
  rw [i224_card_sup hcQ hPQ, hPcard, hQcard]

theorem isPGroup_sup_zpowers_three {Ω : Type*} [Group Ω] {x y : Ω} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) :
    IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  have hcQ : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (hxy : Commute x y) m n).eq
  intro z
  obtain ⟨a, ha, b, hb, hz⟩ := i224_mem_sup_of_comm hcQ z.2
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  show (z : Ω) ^ 3 = 1
  have hxa : a ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hyb : b ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hab : Commute a b := hcQ a ha b hb
  rw [hz, hab.mul_pow, hxa, hyb, one_mul]

theorem P0_card : Nat.card P0 = 9 :=
  card_sup_zpowers_three eG_x3 eG_y3 eG_x_ne_one eG_y_ne_one eG_xy eG_y_ne_x eG_y_ne_xx

theorem P0_isPGroup : IsPGroup 3 P0 := isPGroup_sup_zpowers_three eG_x3 eG_y3 eG_xy

theorem factorization_three_card : Nat.factorization 443520 3 = 2 := by
  have h1 : (443520 : ℕ) = 3 ^ 2 * 49280 := by norm_num
  have h2 : ¬ 3 ∣ 49280 := by norm_num
  rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd h2]

section Plane

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem conj_injective_G :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro x y hxy
  have h1 : x⁻¹ * y ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h2 := congrArg (fun φ : MulAut G => φ z) hxy
    simp only [MulAut.conj_apply] at h2
    calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
      _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h2]
      _ = x⁻¹ * y * z := by group
  rw [CFSG.Sporadic.Schreier.m22_center_eq_bot', Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem m22_plane
    (E : Subgroup (MulAut G))
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    Subgroup.closure {s : G | ∃ ε ∈ E, ε ≠ 1 ∧ ε s = s} = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := conj_injective_G
  have hout : Nat.card (Outer G) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec4.card_outer_le_two_of_card_mulAut_le
      CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card
  have hEinn : E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
    let f : ↥E →* Outer G :=
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner G)).comp E.subtype
    have hr : Nat.card ↥f.range ≤ 2 :=
      le_trans (Nat.card_le_card_of_injective (fun x : ↥f.range => (x : Outer G))
        Subtype.val_injective) hout
    have hd : Nat.card ↥f.range ∣ Nat.card ↥E := Subgroup.card_range_dvd f
    rw [hc] at hd
    have h1 : Nat.card ↥f.range = 1 := by
      have hpos : 0 < Nat.card ↥f.range := Nat.card_pos
      have hcases : Nat.card ↥f.range = 1 ∨ Nat.card ↥f.range = 2 := by omega
      rcases hcases with h | h
      · exact h
      · rw [h] at hd; omega
    have hbot : f.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    intro ε hε
    have hf : f ⟨ε, hε⟩ = 1 := by
      have : f ⟨ε, hε⟩ ∈ f.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    exact (QuotientGroup.eq_one_iff _).1 hf
  set P : Subgroup G := E.comap (MulAut.conj : G →* MulAut G) with hP
  have hEP : P.map (MulAut.conj : G →* MulAut G) = E :=
    Subgroup.map_comap_eq_self hEinn
  have hPcard : Nat.card P = 9 := by
    rw [← hc, ← hEP, Subgroup.card_map_of_injective hinj]
  have hP3 : ∀ p ∈ P, p ^ 3 = 1 := by
    intro p hp
    have h1 : (MulAut.conj p : MulAut G) ^ 3 = 1 := hE.2 _ hp
    apply hinj
    rw [map_pow, map_one]
    exact h1
  have hPp : IsPGroup 3 P := fun p => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hP3 p p.2)⟩
  obtain ⟨Q₀, hQ₀⟩ := P0_isPGroup.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hPp.exists_le_sylow
  have hGcard : Nat.factorization (Nat.card G) 3 = 2 := by
    rw [CFSG.Sporadic.Schreier.m22_card]
    exact factorization_three_card
  have hQ₀card : Nat.card (↑Q₀ : Subgroup G) = 9 := by
    have := Sylow.card_eq_multiplicity Q₀
    rw [hGcard] at this
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact this
  have hQcard : Nat.card (↑Q : Subgroup G) = 9 := by
    have := Sylow.card_eq_multiplicity Q
    rw [hGcard] at this
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact this
  have hP0Q₀ : P0 = ↑Q₀ := Subgroup.eq_of_le_of_card_ge hQ₀ (by rw [hQ₀card, P0_card])
  have hPQ : P = ↑Q := Subgroup.eq_of_le_of_card_ge hQ (by rw [hQcard, hPcard])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₀ Q
  have hsm : (↑Q : Subgroup G) = MulAut.conj g • (↑Q₀ : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  set E₀ : Subgroup (MulAut G) := P0.map (MulAut.conj : G →* MulAut G) with hE₀
  have hEeq : E = E₀.map (MulAut.congr (MulAut.conj g : G ≃* G)).toMonoidHom := by
    ext ε
    constructor
    · intro hε
      rw [← hEP] at hε
      obtain ⟨p, hpP, rfl⟩ := hε
      have hpQ : p ∈ MulAut.conj g • (↑Q₀ : Subgroup G) := hsm ▸ (hPQ ▸ hpP)
      obtain ⟨p₀, hp₀, hpp⟩ := (Subgroup.mem_smul_pointwise_iff_exists p (MulAut.conj g) _).1 hpQ
      refine ⟨MulAut.conj p₀, ⟨p₀, hP0Q₀ ▸ hp₀, rfl⟩, ?_⟩
      rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
      show MulAut.conj (MulAut.conj g p₀) = MulAut.conj p
      rw [← hpp]
      rfl
    · rintro ⟨_, ⟨p₀, hp₀, rfl⟩, rfl⟩
      rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, ← hEP]
      refine ⟨MulAut.conj g p₀, ?_, rfl⟩
      have : MulAut.conj g p₀ ∈ MulAut.conj g • (↑Q₀ : Subgroup G) :=
        Subgroup.smul_mem_pointwise_smul _ _ _ (hP0Q₀ ▸ hp₀)
      rw [← hsm, ← hPQ] at this
      exact this
  have hE₀gen : PlaneGen E₀ := by
    unfold PlaneGen planeClosure
    have hset : {k : G | ∃ e ∈ E₀, e ≠ 1 ∧ e k = k} =
        {s : G | ∃ p ∈ P0, p ≠ 1 ∧ p * s = s * p} := by
      ext s
      constructor
      · rintro ⟨_, ⟨p, hp, rfl⟩, hne, hfix⟩
        refine ⟨p, hp, fun h => hne (by rw [h, map_one]), ?_⟩
        have h2 : p * s * p⁻¹ = s := hfix
        calc p * s = (p * s * p⁻¹) * p := by group
          _ = s * p := by rw [h2]
      · rintro ⟨p, hp, hp1, hcomm⟩
        refine ⟨MulAut.conj p, ⟨p, hp, rfl⟩, fun h => hp1 (hinj (by rw [h, map_one])), ?_⟩
        show p * s * p⁻¹ = s
        rw [hcomm]; group
    rw [hset]
    exact ref_closure
  rw [hEeq]
  exact (planeGen_map_congr _ E₀).2 hE₀gen

end Plane

end CFSG.HardMathSupport.Solomon.Coordinator.M22Plane
