module

public import CFSG.Certificates.Kernel.BabyMonster.E35Cyc
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3

public section

namespace CFSG.KC.BM.E35Group

open CFSG.Open
open CFSG.KC.BM.E35 (CycFacts)

@[expose] def conv5 (c a : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 := fun i => ∑ k : Fin 5, c k * a (i - k)

@[expose] def witTab : List (Fin 5 → ZMod 3) := [
  ![0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1],
  ![2, 1, 0, 0, 0],
  ![1, 1, 1, 1, 1],
  ![0, 2, 1, 2, 1],
  ![0, 1, 1, 1, 1],
  ![1, 0, 0, 0, 2],
  ![0, 2, 2, 2, 2],
  ![0, 1, 2, 1, 2],
  ![0, 0, 0, 1, 2],
  ![0, 2, 0, 1, 0],
  ![0, 1, 0, 1, 0],
  ![2, 1, 2, 1, 0],
  ![0, 1, 2, 0, 1],
  ![1, 1, 1, 1, 1],
  ![0, 0, 0, 0, 2],
  ![1, 1, 0, 2, 2],
  ![2, 0, 2, 1, 1],
  ![0, 0, 0, 2, 1],
  ![0, 2, 0, 2, 0],
  ![0, 1, 0, 2, 0],
  ![0, 0, 0, 0, 1],
  ![1, 0, 1, 2, 2],
  ![2, 2, 0, 1, 1],
  ![1, 1, 1, 1, 1],
  ![2, 2, 1, 0, 1],
  ![0, 2, 1, 0, 2],
  ![0, 0, 1, 2, 0],
  ![1, 0, 0, 2, 0],
  ![0, 1, 1, 0, 1],
  ![2, 0, 1, 0, 0],
  ![0, 2, 0, 0, 1],
  ![0, 0, 2, 2, 2],
  ![0, 2, 0, 2, 2],
  ![0, 1, 1, 1, 0],
  ![0, 2, 2, 1, 1],
  ![1, 2, 1, 0, 2],
  ![0, 0, 1, 0, 2],
  ![1, 1, 1, 1, 1],
  ![0, 1, 2, 0, 2],
  ![0, 2, 1, 0, 0],
  ![2, 1, 2, 2, 2],
  ![1, 1, 1, 1, 1],
  ![2, 2, 0, 2, 0],
  ![0, 2, 2, 0, 1],
  ![0, 0, 0, 2, 0],
  ![1, 1, 1, 1, 1],
  ![2, 2, 0, 0, 2],
  ![1, 0, 2, 2, 1],
  ![1, 0, 1, 1, 0],
  ![0, 1, 1, 0, 0],
  ![0, 2, 1, 1, 2],
  ![0, 0, 1, 1, 2],
  ![1, 1, 1, 1, 1],
  ![0, 0, 2, 1, 0],
  ![0, 2, 2, 0, 2],
  ![1, 1, 1, 1, 1],
  ![0, 1, 0, 1, 1],
  ![0, 1, 1, 2, 2],
  ![0, 2, 2, 2, 0],
  ![1, 0, 2, 0, 0],
  ![0, 0, 1, 1, 1],
  ![0, 1, 0, 0, 2],
  ![0, 0, 0, 1, 0],
  ![1, 1, 0, 0, 1],
  ![1, 1, 1, 0, 0],
  ![0, 1, 2, 2, 1],
  ![1, 1, 2, 1, 1],
  ![0, 0, 2, 2, 1],
  ![2, 0, 1, 1, 2],
  ![0, 2, 2, 0, 0],
  ![1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1],
  ![2, 1, 1, 0, 2],
  ![0, 0, 2, 0, 1],
  ![2, 1, 0, 1, 2],
  ![0, 1, 1, 0, 2],
  ![1, 1, 0, 1, 0],
  ![0, 2, 1, 0, 1],
  ![1, 1, 1, 1, 1],
  ![0, 1, 2, 0, 0],
  ![0, 1, 2, 0, 0],
  ![1, 0, 2, 1, 2],
  ![0, 1, 0, 0, 0],
  ![0, 0, 2, 0, 1],
  ![0, 2, 0, 1, 2],
  ![1, 1, 1, 1, 1],
  ![0, 0, 2, 0, 2],
  ![1, 1, 1, 1, 1],
  ![1, 2, 2, 1, 0],
  ![0, 1, 0, 0, 2],
  ![0, 2, 1, 2, 2],
  ![0, 0, 1, 1, 1],
  ![0, 1, 1, 2, 1],
  ![0, 0, 2, 1, 0],
  ![0, 2, 2, 0, 2],
  ![0, 2, 2, 2, 0],
  ![0, 1, 0, 1, 1],
  ![0, 1, 1, 2, 2],
  ![0, 1, 0, 0, 1],
  ![1, 1, 1, 1, 1],
  ![1, 0, 0, 1, 1],
  ![1, 1, 1, 0, 0],
  ![1, 1, 1, 2, 1],
  ![0, 0, 2, 2, 0],
  ![2, 2, 1, 1, 0],
  ![0, 1, 2, 2, 1],
  ![1, 1, 1, 1, 1],
  ![2, 1, 0, 2, 1],
  ![0, 1, 0, 1, 2],
  ![1, 1, 1, 1, 1],
  ![0, 1, 0, 2, 0],
  ![0, 0, 0, 2, 1],
  ![1, 0, 1, 0, 1],
  ![1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 2],
  ![0, 2, 0, 1, 1],
  ![0, 1, 2, 1, 2],
  ![1, 0, 0, 0, 2],
  ![2, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1],
  ![0, 0, 0, 0, 1],
  ![0, 1, 2, 2, 2],
  ![1, 2, 2, 2, 2],
  ![0, 1, 1, 1, 2],
  ![0, 2, 1, 2, 1],
  ![1, 1, 1, 1, 1],
  ![2, 2, 2, 2, 1],
  ![0, 0, 2, 1, 1],
  ![2, 0, 2, 0, 2],
  ![0, 0, 0, 1, 2],
  ![0, 2, 0, 1, 0],
  ![0, 0, 1, 2, 1],
  ![1, 1, 1, 1, 1],
  ![1, 2, 0, 1, 2],
  ![0, 0, 2, 0, 0],
  ![0, 2, 1, 1, 2],
  ![1, 1, 2, 2, 0],
  ![1, 1, 1, 1, 1],
  ![2, 2, 2, 1, 2],
  ![0, 0, 0, 1, 1],
  ![2, 0, 0, 2, 2],
  ![0, 2, 1, 1, 0],
  ![1, 0, 1, 1, 0],
  ![0, 2, 2, 1, 1],
  ![0, 2, 0, 2, 2],
  ![0, 1, 1, 1, 0],
  ![0, 1, 1, 0, 1],
  ![0, 0, 1, 2, 0],
  ![1, 0, 0, 2, 0],
  ![0, 0, 2, 2, 2],
  ![1, 1, 1, 1, 1],
  ![0, 2, 0, 0, 1],
  ![2, 1, 1, 2, 0],
  ![0, 1, 2, 1, 0],
  ![1, 1, 1, 1, 1],
  ![0, 1, 1, 2, 0],
  ![1, 1, 1, 1, 1],
  ![0, 0, 1, 0, 2],
  ![1, 1, 1, 1, 1],
  ![2, 0, 1, 2, 1],
  ![0, 2, 1, 0, 0],
  ![0, 2, 1, 0, 0],
  ![0, 2, 0, 0, 0],
  ![1, 1, 1, 1, 1],
  ![0, 0, 1, 0, 1],
  ![1, 1, 1, 1, 1],
  ![1, 2, 0, 2, 1],
  ![0, 0, 1, 0, 2],
  ![1, 2, 2, 0, 1],
  ![0, 1, 0, 2, 1],
  ![0, 2, 0, 0, 2],
  ![1, 1, 1, 1, 1],
  ![1, 0, 2, 2, 1],
  ![1, 1, 1, 1, 1],
  ![2, 2, 1, 2, 2],
  ![0, 2, 1, 1, 2],
  ![2, 2, 2, 0, 0],
  ![0, 0, 1, 1, 0],
  ![1, 1, 1, 1, 1],
  ![0, 2, 0, 0, 1],
  ![0, 0, 2, 2, 2],
  ![0, 1, 2, 1, 1],
  ![0, 1, 1, 1, 0],
  ![0, 2, 2, 1, 1],
  ![0, 2, 0, 2, 2],
  ![0, 2, 2, 1, 2],
  ![0, 1, 1, 0, 1],
  ![0, 0, 1, 2, 0],
  ![0, 0, 1, 0, 0],
  ![1, 1, 1, 1, 1],
  ![0, 1, 2, 2, 1],
  ![1, 0, 0, 1, 1],
  ![2, 0, 2, 2, 0],
  ![0, 1, 2, 2, 0],
  ![1, 1, 0, 0, 1],
  ![0, 0, 0, 2, 2],
  ![1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1],
  ![1, 1, 0, 1, 0],
  ![0, 2, 1, 2, 0],
  ![1, 2, 1, 1, 1],
  ![0, 1, 2, 0, 0],
  ![1, 0, 2, 1, 2],
  ![0, 2, 2, 1, 0],
  ![0, 0, 2, 0, 1],
  ![2, 1, 2, 0, 1],
  ![0, 1, 1, 2, 2],
  ![0, 2, 2, 2, 0],
  ![0, 1, 0, 1, 1],
  ![0, 0, 1, 1, 1],
  ![0, 1, 0, 0, 2],
  ![1, 0, 2, 0, 0],
  ![0, 2, 2, 0, 2],
  ![2, 0, 0, 1, 0],
  ![0, 0, 2, 1, 0],
  ![1, 1, 1, 1, 1],
  ![1, 1, 2, 0, 2],
  ![0, 2, 0, 2, 1],
  ![1, 1, 0, 2, 2],
  ![0, 1, 0, 2, 2],
  ![1, 1, 1, 1, 1],
  ![0, 2, 0, 1, 0],
  ![1, 1, 1, 1, 1],
  ![0, 0, 0, 1, 2],
  ![1, 0, 1, 2, 2],
  ![0, 0, 1, 2, 2],
  ![1, 1, 1, 1, 1],
  ![0, 0, 2, 1, 2],
  ![1, 1, 1, 1, 1],
  ![1, 2, 1, 2, 0],
  ![1, 0, 1, 0, 1],
  ![0, 1, 0, 2, 0],
  ![0, 0, 0, 2, 1],
  ![0, 2, 1, 2, 1],
  ![1, 1, 1, 1, 1],
  ![2, 0, 0, 0, 1],
  ![1, 1, 1, 1, 1],
  ![0, 1, 2, 1, 2],
  ![0, 2, 2, 2, 1],
  ![1, 2, 0, 0, 0],
  ![0, 2, 1, 1, 1],
  ![0, 0, 0, 0, 2]
  ]

@[expose] def code5 (a : Fin 5 → ZMod 3) : ℕ :=
  (a 0).val + 3 * (a 1).val + 9 * (a 2).val + 27 * (a 3).val + 81 * (a 4).val

@[expose] def wit (a : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 := witTab.getD (code5 a) 0

set_option maxRecDepth 100000 in
theorem conv5_wit_vec : ∀ a0 a1 a2 a3 a4 : ZMod 3, ![a0, a1, a2, a3, a4] ≠ 0 →
    conv5 (wit ![a0, a1, a2, a3, a4]) ![a0, a1, a2, a3, a4] = ![1, 1, 1, 1, 1] ∨
    conv5 (wit ![a0, a1, a2, a3, a4]) ![a0, a1, a2, a3, a4] = ![1, 2, 0, 0, 0] := by
  decide +kernel

theorem conv5_wit (a : Fin 5 → ZMod 3) (ha : a ≠ 0) :
    conv5 (wit a) a = ![1, 1, 1, 1, 1] ∨ conv5 (wit a) a = ![1, 2, 0, 0, 0] := by
  have e : a = ![a 0, a 1, a 2, a 3, a 4] := by
    funext i
    fin_cases i <;> rfl
  rw [e] at ha ⊢
  exact conv5_wit_vec _ _ _ _ _ ha

@[expose] def rot5 (a : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 := fun i => a (i - 1)

theorem conv5_eq (c a : Fin 5 → ZMod 3) :
    conv5 c a = c 0 • a + c 1 • rot5 a + c 2 • rot5 (rot5 a) + c 3 • rot5 (rot5 (rot5 a)) +
      c 4 • rot5 (rot5 (rot5 (rot5 a))) := by
  funext i
  simp only [conv5, Fin.sum_univ_five, Pi.add_apply, Pi.smul_apply, smul_eq_mul, rot5]
  fin_cases i <;> rfl

section Group

variable {G : Type*} [Group G]

@[expose] def cj (x g : G) (k : ℕ) : G := (g ^ k)⁻¹ * x * g ^ k

theorem cj_add (x g : G) (a k : ℕ) : cj x g (a + k) = (g ^ k)⁻¹ * cj x g a * g ^ k := by
  simp only [cj, pow_add, mul_inv_rev, mul_assoc]

theorem cj_zero (x g : G) : cj x g 0 = x := by
  simp [cj]

theorem commute_conj {a b : G} (h : Commute a b) (u : G) :
    Commute (u⁻¹ * a * u) (u⁻¹ * b * u) := by
  have e := h.map (MulAut.conj u⁻¹).toMonoidHom
  simpa [MulAut.conj_apply] using e

theorem cj_shift (x g : G) {a b : ℕ} (h : Commute (cj x g a) (cj x g b)) (k : ℕ) :
    Commute (cj x g (a + k)) (cj x g (b + k)) := by
  rw [cj_add, cj_add]
  exact commute_conj h _

theorem cj_pow (x g : G) (k n : ℕ) : cj x g k ^ n = cj (x ^ n) g k := by
  have e := conj_pow (a := (g ^ k)⁻¹) (b := x) (i := n)
  rw [inv_inv] at e
  exact e

theorem isElemAbelian_map_subtype' {p : ℕ} {C : Subgroup G} {E : Subgroup C}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map C.subtype) := by
  obtain ⟨hc, hp⟩ := hE
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, y, hy, rfl⟩ := b
    exact congrArg (fun t : E => ((t : C) : G)) (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hp x hx)

theorem mem_normalizer_zpowers {e z : G} (h : Commute e z) :
    e ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [(h.zpow_right k).eq, mul_inv_cancel_right]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc z ^ k = e⁻¹ * z ^ k * e := by
          rw [((h.zpow_right k).inv_left).eq, inv_mul_cancel_right]
      _ = e⁻¹ * (e * t * e⁻¹) * e := by rw [hk]
      _ = t := by group

open scoped IsMulCommutative in
theorem attained_of_cyc {x g : G} (h : CycFacts x g) :
    ∃ E T : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨hx3, hg10, hz1, hzx, h1, h2, hne, hP⟩ := h
  have g9 : g ^ 9 = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hg10]
  have c1 : cj x g 1 = g ^ 9 * x * g := by
    simp [cj, g9]
  have c2 : cj x g 2 = g ^ 9 * (g ^ 9 * x * g) * g := by
    change cj x g (1 + 1) = _
    rw [cj_add, c1, pow_one, g9]
  have c5 : cj x g 5 = x := by
    simp only [cj]
    rw [mul_assoc, ← hzx, ← mul_assoc, inv_mul_cancel, one_mul]
  have cper : ∀ k, cj x g (k + 5) = cj x g k := by
    intro k
    rw [add_comm, cj_add, c5]
    rfl
  have b01 : Commute (cj x g 0) (cj x g 1) := by
    rw [cj_zero, c1]
    exact h1
  have b02 : Commute (cj x g 0) (cj x g 2) := by
    rw [cj_zero, c2]
    exact h2
  have base : ∀ d, d ≤ 4 → Commute (cj x g 0) (cj x g d) := by
    intro d hd
    interval_cases d
    · exact Commute.refl _
    · exact b01
    · exact b02
    · have e := cj_shift x g b02.symm 3
      rwa [cper 0] at e
    · have e := cj_shift x g b01.symm 4
      rwa [cper 0] at e
  have hcomm : ∀ i j : Fin 5, Commute (cj x g i) (cj x g j) := by
    have key : ∀ i j : Fin 5, (i : ℕ) ≤ j → Commute (cj x g i) (cj x g j) := by
      intro i j hij
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hij
      have e := cj_shift x g (base d (by omega)) i
      rwa [zero_add, add_comm d, ← hd] at e
    intro i j
    rcases le_total (i : ℕ) j with hij | hij
    · exact key i j hij
    · exact (key j i hij).symm
  have hy3 : ∀ k, cj x g k ^ 3 = 1 := by
    intro k
    rw [cj_pow, hx3]
    simp [cj]
  have hz : ∀ k, g ^ 5 * cj x g k = cj x g k * g ^ 5 := by
    intro k
    have hgk : Commute (g ^ 5) (g ^ k) := Commute.pow_pow_self g 5 k
    exact ((hgk.inv_right.mul_right hzx).mul_right hgk).eq
  let C := Subgroup.closure (Set.range fun i : Fin 5 => cj x g i)
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin 5 → C := fun i => ⟨cj x g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 3 = 1 := fun i => Subtype.ext (by simpa [v] using hy3 i)
  let w : Fin 5 → ZMod 3 → C := fun i e => v i ^ e.val
  have hw_add : ∀ i e f, w i (e + f) = w i e * w i f := by
    intro i e f
    simp only [w]
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]
  let ψC : (Fin 5 → ZMod 3) → C := fun a => w 0 (a 0) * w 1 (a 1) * w 2 (a 2) * w 3 (a 3) * w 4 (a 4)
  let ψ : (Fin 5 → ZMod 3) → G := fun a => (ψC a : G)
  have ψ_add : ∀ a b, ψ (a + b) = ψ a * ψ b := by
    intro a b
    simp only [ψ, ψC, Pi.add_apply, hw_add]
    rw [← Subgroup.coe_mul]
    congr 1
    ac_rfl
  have ψ_zero : ψ 0 = 1 := by
    simp [ψ, ψC, w]
  have ψ_expl : ∀ a, ψ a = cj x g 0 ^ (a 0).val * cj x g 1 ^ (a 1).val * cj x g 2 ^ (a 2).val *
      cj x g 3 ^ (a 3).val * cj x g 4 ^ (a 4).val := by
    intro a
    simp only [ψ, ψC, w, Subgroup.coe_mul, Subgroup.coe_pow, v]
    rfl
  have cyc : ∀ e0 e1 e2 e3 e4 : ℕ,
      cj x g 1 ^ e0 * cj x g 2 ^ e1 * cj x g 3 ^ e2 * cj x g 4 ^ e3 * cj x g 0 ^ e4 =
      cj x g 0 ^ e4 * cj x g 1 ^ e0 * cj x g 2 ^ e1 * cj x g 3 ^ e2 * cj x g 4 ^ e3 := by
    intro e0 e1 e2 e3 e4
    have e : v 1 ^ e0 * v 2 ^ e1 * v 3 ^ e2 * v 4 ^ e3 * v 0 ^ e4 =
        v 0 ^ e4 * v 1 ^ e0 * v 2 ^ e1 * v 3 ^ e2 * v 4 ^ e3 := by
      rw [mul_comm _ (v 0 ^ e4)]
      simp only [mul_assoc]
    have e' := congrArg Subtype.val e
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, v] at e'
    exact e'
  have kk : ∀ i, g⁻¹ * cj x g i * g = cj x g (i + 1) := by
    intro i
    rw [cj_add, pow_one]
  have k0 : g⁻¹ * cj x g 0 * g = cj x g 1 := kk 0
  have k1 : g⁻¹ * cj x g 1 * g = cj x g 2 := kk 1
  have k2 : g⁻¹ * cj x g 2 * g = cj x g 3 := kk 2
  have k3 : g⁻¹ * cj x g 3 * g = cj x g 4 := kk 3
  have k4 : g⁻¹ * cj x g 4 * g = cj x g 0 := ((kk 4).trans c5).trans (cj_zero x g).symm
  have ψ_rot : ∀ a, g⁻¹ * ψ a * g = ψ (rot5 a) := by
    intro a
    have hc : ∀ (u : G) (e : ℕ), g⁻¹ * u ^ e * g = (g⁻¹ * u * g) ^ e := by
      intro u e
      have := conj_pow (a := g⁻¹) (b := u) (i := e)
      rw [inv_inv] at this
      exact this.symm
    have hm : ∀ u w : G, g⁻¹ * (u * w) * g = (g⁻¹ * u * g) * (g⁻¹ * w * g) := by
      intro u w
      group
    rw [ψ_expl, ψ_expl, hm, hm, hm, hm, hc, hc, hc, hc, hc, k0, k1, k2, k3, k4]
    exact cyc _ _ _ _ _
  let K : AddSubgroup (Fin 5 → ZMod 3) :=
    { carrier := {a | ψ a = 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [ψ_add, ha, hb, one_mul]
      zero_mem' := ψ_zero
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have e := ψ_add (-a) a
        have h0 : -a + a = 0 := neg_add_cancel a
        rw [h0, ψ_zero, ha, mul_one] at e
        exact e.symm }
  have K_rot : ∀ a ∈ K, rot5 a ∈ K := by
    intro a ha
    change ψ (rot5 a) = 1
    have ha' : ψ a = 1 := ha
    rw [← ψ_rot, ha', mul_one, inv_mul_cancel]
  have K_smul : ∀ (c : ZMod 3) a, a ∈ K → c • a ∈ K := by
    intro c a ha
    have e : c • a = c.val • a := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    rw [e]
    exact K.nsmul_mem ha _
  have K_conv : ∀ c a, a ∈ K → conv5 c a ∈ K := by
    intro c a ha
    have r1 := K_rot a ha
    have r2 := K_rot _ r1
    have r3 := K_rot _ r2
    have r4 := K_rot _ r3
    rw [conv5_eq]
    exact K.add_mem (K.add_mem (K.add_mem (K.add_mem (K_smul _ _ ha) (K_smul _ _ r1))
      (K_smul _ _ r2)) (K_smul _ _ r3)) (K_smul _ _ r4)
  have hu : ψ ![1, 1, 1, 1, 1] ≠ 1 := by
    rw [ψ_expl]
    change cj x g 0 ^ 1 * cj x g 1 ^ 1 * cj x g 2 ^ 1 * cj x g 3 ^ 1 * cj x g 4 ^ 1 ≠ 1
    simp only [pow_one, cj]
    rw [g9] at hP
    rw [pow_succ (x * g⁻¹) 3, pow_succ (x * g⁻¹) 2, pow_succ (x * g⁻¹) 1, pow_one] at hP
    intro e
    apply hP
    rw [← e]
    group
  have hv' : ψ ![1, 2, 0, 0, 0] ≠ 1 := by
    rw [ψ_expl]
    change cj x g 0 ^ 1 * cj x g 1 ^ 2 * cj x g 2 ^ 0 * cj x g 3 ^ 0 * cj x g 4 ^ 0 ≠ 1
    simp only [pow_zero, mul_one, pow_one]
    intro e
    apply hne
    rw [← c1]
    calc cj x g 1 = cj x g 1 ^ 3 * (cj x g 1 ^ 2)⁻¹ := by group
      _ = (cj x g 1 ^ 2)⁻¹ := by rw [hy3, one_mul]
      _ = cj x g 0 := (eq_inv_of_mul_eq_one_left e).symm
      _ = x := cj_zero x g
  have hK : ∀ a ∈ K, a = 0 := by
    intro a ha
    by_contra hne0
    have hc := K_conv (wit a) a ha
    rcases conv5_wit a hne0 with e | e
    · rw [e] at hc
      exact hu hc
    · rw [e] at hc
      exact hv' hc
  have hkerG : ∀ a : Fin 5 → Fin 3, a ≠ 0 →
      (List.ofFn fun i : Fin 5 => cj x g i ^ (a i : ℕ)).prod ≠ 1 := by
    intro a ha e
    have e' : cj x g 0 ^ (a 0 : ℕ) * cj x g 1 ^ (a 1 : ℕ) * cj x g 2 ^ (a 2 : ℕ) *
        cj x g 3 ^ (a 3 : ℕ) * cj x g 4 ^ (a 4 : ℕ) = 1 := by
      rw [← e]
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
        mul_assoc]
      rfl
    let a' : Fin 5 → ZMod 3 := a
    have hm : ψ a' = 1 := by
      rw [ψ_expl]
      exact e'
    exact ha (hK a' hm)
  let H := Subgroup.centralizer ({g ^ 5} : Set G)
  have hmem : ∀ i : Fin 5, cj x g i ∈ H := by
    intro i
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hz i
  let u : Fin 5 → H := fun i => ⟨cj x g i, hmem i⟩
  obtain ⟨E', hE', hc⟩ := CFSG.SectionRank.exists_elemAbelian_of_commuting u
    (fun i => Subtype.ext (by simpa [u] using hy3 i)) (fun i j => Subtype.ext (hcomm i j).eq)
    (fun a ha hp => hkerG a ha (by
      have h1 := congrArg H.subtype hp
      rw [map_list_prod, List.map_ofFn, map_one] at h1
      simpa [u, Function.comp_def] using h1))
  have hz2 : (g ^ 5) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hg10
  refine ⟨E'.map H.subtype, Subgroup.zpowers (g ^ 5), isElemAbelian_map_subtype' hE', ?_, ?_, ?_,
    ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hc]
  · exact fun e => hz1 (Subgroup.zpowers_eq_bot.1 e)
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  · rintro _ ⟨e, he, rfl⟩
    have hce := e.2
    rw [Subgroup.mem_centralizer_iff] at hce
    exact mem_normalizer_zpowers (hce _ rfl).symm

theorem cycFacts_of_injective {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
    (hf : Function.Injective f) {x g : M} (h : CycFacts (f x) (f g)) : CycFacts x g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨hf ?_, hf ?_, fun e => h3 ?_, hf ?_, hf ?_, hf ?_, fun e => h7 ?_, fun e => h8 ?_⟩
  · simpa using h1
  · simpa using h2
  · simpa using congrArg f e
  · simpa using h4
  · simpa using h5
  · simpa using h6
  · simpa using congrArg f e
  · simpa using congrArg f e

theorem attained_of_submonoid {M : Type*} [Monoid M] (S : Submonoid M) {X Y : M} (hX : X ∈ S)
    (hY : Y ∈ S) (h : CycFacts X Y) {K : Type*} [Group K] (ψ : K ≃* Sˣ) :
    ∃ E T : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set K) := by
  have hx3 : (⟨X, hX⟩ : S) ^ 3 = 1 := Subtype.ext (by simpa using h.1)
  have hy10 : (⟨Y, hY⟩ : S) ^ 10 = 1 := Subtype.ext (by simpa using h.2.1)
  obtain ⟨xu, hxu⟩ : ∃ u : Sˣ, ((u : S) : M) = X :=
    ⟨⟨⟨X, hX⟩, ⟨X, hX⟩ ^ 2, by rw [← pow_succ']; exact hx3, by rw [← pow_succ]; exact hx3⟩, rfl⟩
  obtain ⟨yu, hyu⟩ : ∃ u : Sˣ, ((u : S) : M) = Y :=
    ⟨⟨⟨Y, hY⟩, ⟨Y, hY⟩ ^ 9, by rw [← pow_succ']; exact hy10, by rw [← pow_succ]; exact hy10⟩,
      rfl⟩
  subst hxu hyu
  let f : K →* M := (S.subtype.comp (Units.coeHom S)).comp ψ.toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (Units.val_injective.comp ψ.injective)
  refine attained_of_cyc (x := ψ.symm xu) (g := ψ.symm yu) (cycFacts_of_injective f hf ?_)
  simpa [f] using h

end Group

end CFSG.KC.BM.E35Group

end
