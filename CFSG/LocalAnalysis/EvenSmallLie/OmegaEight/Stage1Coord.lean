module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bits
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

structure RadicalData (ε : Eps) (L U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p : Fin 6 → G) :
    Prop where
  odd : InvolutionsInOddPart L
  Q_le_U : Q ≤ U
  U_le_P : U ≤ P
  P_eq : P = L ⊓ normalizer (Q : Set G)
  U_pgroup : IsPGroup 2 U
  center_U : ∀ u ∈ U, (∀ x ∈ U, u * x = x * u) → u = 1 ∨ u = a
  ψ_add : ∀ v w, ψ (v + w) = ψ v * ψ w
  ψ_inj : Function.Injective ψ
  ψ_mem : ∀ v, ψ v ∈ Q
  mem_ψ : ∀ x ∈ Q, ∃ v, ψ v = x
  a_eq : a = ψ (Pi.single 0 1)
  p_mem : ∀ i, p i ∈ P
  p_act : ∀ i v, p i * ψ v * (p i)⁻¹ = ψ (genMat ε i *ᵥ v)
  P_le : P ≤ closure ((Q : Set G) ∪ Set.range p)
  card_P : Nat.card P = 64 * (oBound ε / 2)
  S5 : ∀ A : Subgroup G, A ≤ U → (∀ u ∈ U, ∀ x ∈ A, u * x * u⁻¹ ∈ A) →
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) → Nat.card A = 64 →
    ∃ l ∈ L, (∀ x ∈ A, l * x * l⁻¹ ∈ A) ∧ l * a * l⁻¹ ≠ a

@[expose] noncomputable def coord (ψ : V6 → G) (x : G) : V6 := Function.invFun ψ x

@[expose] noncomputable def lin (ψ : V6 → G) (g : G) (v : V6) : V6 := coord ψ (g * ψ v * g⁻¹)

theorem toMat_id6 : toMat 6 6 id6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem genRows_of_le (ε : Eps) {i : ℕ} (hi : 6 ≤ i) : genRows ε i = id6 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 6 := ⟨i - 6, by omega⟩
  cases ε <;> rfl

theorem genMat_of_le (ε : Eps) {i : ℕ} (hi : 6 ≤ i) : genMat ε i = 1 := by
  rw [genMat, genRows_of_le ε hi, toMat_id6]

theorem qfB_one (ε : Eps) : qfB ε 1 = false := by cases ε <;> rfl

theorem qfB_n0 (ε : Eps) : qfB ε (n0 ε) = true := by cases ε <;> rfl

theorem n0_lt (ε : Eps) : n0 ε < 64 := by cases ε <;> decide

@[expose] def pAt (p : Fin 6 → G) (i : ℕ) : G := if h : i < 6 then p ⟨i, h⟩ else 1

@[expose] def wordElt (p : Fin 6 → G) (w : List ℕ) : G := (w.map (pAt p)).prod

namespace RadicalData

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hR : RadicalData ε L U Q P a ψ p)
include hR

theorem ψ_zero : ψ 0 = 1 := by
  have h := hR.ψ_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem ψ_mul_self (v : V6) : ψ v * ψ v = 1 := by
  rw [← hR.ψ_add, ← hR.ψ_zero]
  congr 1
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = c
  fin_cases c <;> rfl

theorem ψ_coord {x : G} (hx : x ∈ Q) : ψ (coord ψ x) = x := by
  obtain ⟨v, rfl⟩ := hR.mem_ψ x hx
  exact Function.invFun_eq ⟨v, rfl⟩

theorem coord_ψ (v : V6) : coord ψ (ψ v) = v := Function.leftInverse_invFun hR.ψ_inj v

theorem Q_comm {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := hR.mem_ψ x hx
  obtain ⟨w, rfl⟩ := hR.mem_ψ y hy
  rw [← hR.ψ_add, ← hR.ψ_add, add_comm]

theorem Q_mul_self {x : G} (hx : x ∈ Q) : x * x = 1 := by
  obtain ⟨v, rfl⟩ := hR.mem_ψ x hx
  exact hR.ψ_mul_self v

theorem card_Q : Nat.card Q = 64 := by
  have e : V6 ≃ Q :=
    Equiv.ofBijective (fun v => ⟨ψ v, hR.ψ_mem v⟩)
      ⟨fun v w h => hR.ψ_inj (congrArg Subtype.val h), fun x => by
        obtain ⟨v, hv⟩ := hR.mem_ψ x.1 x.2
        exact ⟨v, Subtype.ext hv⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  simp

theorem Q_le_L : Q ≤ L := by
  intro x hx
  have := hR.U_le_P (hR.Q_le_U hx)
  rw [hR.P_eq] at this
  exact this.1

theorem P_le_L : P ≤ L := fun x hx => by rw [hR.P_eq] at hx; exact hx.1

theorem P_le_normalizer : P ≤ normalizer (Q : Set G) := fun x hx => by
  rw [hR.P_eq] at hx; exact hx.2

theorem U_le_L : U ≤ L := hR.U_le_P.trans hR.P_le_L

theorem a_mem_Q : a ∈ Q := hR.a_eq ▸ hR.ψ_mem _

theorem a_ne_one : a ≠ 1 := by
  rw [hR.a_eq, ← hR.ψ_zero]
  intro h
  have := congrFun (hR.ψ_inj h) 0
  simp at this

theorem conj_mem_Q {g : G} (hg : g ∈ normalizer (Q : Set G)) (v : V6) : g * ψ v * g⁻¹ ∈ Q :=
  (mem_normalizer_iff.1 hg _).1 (hR.ψ_mem v)

theorem ψ_lin {g : G} (hg : g ∈ normalizer (Q : Set G)) (v : V6) :
    ψ (lin ψ g v) = g * ψ v * g⁻¹ :=
  hR.ψ_coord (hR.conj_mem_Q hg v)

theorem lin_eq_iff {g : G} (hg : g ∈ normalizer (Q : Set G)) (v w : V6) :
    lin ψ g v = w ↔ g * ψ v * g⁻¹ = ψ w := by
  rw [← hR.ψ_lin hg]
  exact ⟨fun h => h ▸ rfl, fun h => hR.ψ_inj h⟩

theorem lin_add {g : G} (hg : g ∈ normalizer (Q : Set G)) (v w : V6) :
    lin ψ g (v + w) = lin ψ g v + lin ψ g w := by
  rw [hR.lin_eq_iff hg, hR.ψ_add, hR.ψ_add, hR.ψ_lin hg, hR.ψ_lin hg]
  group

theorem lin_mul {g h : G} (hg : g ∈ normalizer (Q : Set G)) (hh : h ∈ normalizer (Q : Set G))
    (v : V6) : lin ψ (g * h) v = lin ψ g (lin ψ h v) := by
  rw [hR.lin_eq_iff (mul_mem hg hh), hR.ψ_lin hg, hR.ψ_lin hh]
  group

theorem lin_one (v : V6) : lin ψ 1 v = v := by
  rw [hR.lin_eq_iff (one_mem _)]
  group

theorem lin_inv {g : G} (hg : g ∈ normalizer (Q : Set G)) (v : V6) :
    lin ψ g (lin ψ g⁻¹ v) = v := by
  rw [← hR.lin_mul hg (inv_mem hg), mul_inv_cancel, hR.lin_one]

theorem lin_inv' {g : G} (hg : g ∈ normalizer (Q : Set G)) (v : V6) :
    lin ψ g⁻¹ (lin ψ g v) = v := by
  rw [← hR.lin_mul (inv_mem hg) hg, inv_mul_cancel, hR.lin_one]

theorem lin_of_mem_Q {q : G} (hq : q ∈ Q) (v : V6) : lin ψ q v = v := by
  rw [hR.lin_eq_iff (le_normalizer hq), hR.Q_comm hq (hR.ψ_mem v), mul_inv_cancel_right]

theorem p_mem_normalizer (i : Fin 6) : p i ∈ normalizer (Q : Set G) :=
  hR.P_le_normalizer (hR.p_mem i)

theorem lin_p (i : Fin 6) (v : V6) : lin ψ (p i) v = genMat ε i *ᵥ v := by
  rw [hR.lin_eq_iff (hR.p_mem_normalizer i), hR.p_act]

theorem closure_le_normalizer : closure ((Q : Set G) ∪ Set.range p) ≤ normalizer (Q : Set G) := by
  rw [closure_le]
  rintro x (hx | ⟨i, rfl⟩)
  · exact le_normalizer hx
  · exact hR.p_mem_normalizer i

theorem pAt_mem (i : ℕ) : pAt p i ∈ P := by
  unfold pAt
  split_ifs
  · exact hR.p_mem _
  · exact one_mem _

theorem wordElt_mem (w : List ℕ) : wordElt p w ∈ P := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih =>
    rw [wordElt, List.map_cons, List.prod_cons]
    exact mul_mem (hR.pAt_mem i) ih

theorem lin_pAt (i : ℕ) (v : V6) : lin ψ (pAt p i) v = genMat ε i *ᵥ v := by
  unfold pAt
  split_ifs with h
  · exact hR.lin_p ⟨i, h⟩ v
  · rw [hR.lin_one, genMat_of_le ε (not_lt.1 h), one_mulVec]

theorem lin_wordElt (w : List ℕ) (x : ℕ) :
    lin ψ (wordElt p w) (toVec 6 x) = toVec 6 (wordAct ε w x) := by
  induction w with
  | nil => exact hR.lin_one _
  | cons i w ih =>
    have h : wordElt p (i :: w) = pAt p i * wordElt p w := by
      rw [wordElt, List.map_cons, List.prod_cons]; rfl
    rw [h, hR.lin_mul (hR.P_le_normalizer (hR.pAt_mem i))
      (hR.P_le_normalizer (hR.wordElt_mem w)), ih, hR.lin_pAt, genMat, mulVec_toVec]
    rfl

end RadicalData

end CFSG.EvenSmallLie.OmegaEight.Stage1
