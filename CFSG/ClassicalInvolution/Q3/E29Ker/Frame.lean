module

public import CFSG.ClassicalInvolution.Q3.E29Ker.ModelM0
public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E29Data

variable {X : Type} [Group X]

private theorem fr_conj_prod_map {G : Type*} [Group G] (c : G) (f g : ℕ → G) (W : List ℕ)
    (h : ∀ l ∈ W, g l = c * f l * c⁻¹) :
    (W.map g).prod = c * (W.map f).prod * c⁻¹ := by
  induction W with
  | nil => simp
  | cons a W ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, h a (by simp),
      ih (fun l hl => h l (by simp [hl]))]
    group

structure Hyp (φ : X →* AEQ 8) (Q : Set (Subgroup X)) : Prop where
  range_eq : φ.range = e29Sub
  conj : ∀ L ∈ Q, ∀ x : X, conjSub x L ∈ Q
  ord : ∀ L ∈ Q, Nat.card L = 8
  lab : ∀ L ∈ Q, ∃ α ∈ e29Sets, ∃ (h : α.card = 4) (b : Bool), L.map φ = memBar α h b
  surj : ∀ α ∈ e29Sets, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Q, L.map φ = memBar α h b
  inj : ∀ L ∈ Q, ∀ L' ∈ Q, L.map φ = L'.map φ → L = L'

namespace Hyp

variable {φ : X →* AEQ 8} {Q : Set (Subgroup X)}

theorem card_map (H : Hyp φ Q) {L : Subgroup X} (hL : L ∈ Q) : Nat.card (L.map φ) = 8 := by
  obtain ⟨α, -, h, b, hmap⟩ := H.lab L hL
  rw [hmap]
  exact natCard_memBar (by norm_num) α h b

theorem injOn (H : Hyp φ Q) {L : Subgroup X} (hL : L ∈ Q) {x y : X} (hx : x ∈ L) (hy : y ∈ L)
    (h : φ x = φ y) : x = y := by
  have hker : Nat.card (φ.comp L.subtype).ker = 1 := by
    have h1 := Subgroup.card_ker_mul_card_range (φ.comp L.subtype)
    have hrange : (φ.comp L.subtype).range = L.map φ := by
      rw [← MonoidHom.map_range, Subgroup.range_subtype]
    rw [hrange, H.card_map hL, H.ord L hL] at h1
    omega
  have hinj : Function.Injective (φ.comp L.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp (Subgroup.eq_bot_of_card_eq _ hker)
  exact congrArg Subtype.val
    (hinj (show (φ.comp L.subtype) ⟨x, hx⟩ = (φ.comp L.subtype) ⟨y, hy⟩ from h))

theorem eq_of_map_le (H : Hyp φ Q) {L L' : Subgroup X} (hL : L ∈ Q) (hL' : L' ∈ Q)
    (h : L.map φ ≤ L'.map φ) : L = L' := by
  have hfin : Finite (L'.map φ) := Nat.finite_of_card_ne_zero (by rw [H.card_map hL']; norm_num)
  have hcard : Nat.card (L'.map φ) ≤ Nat.card (L.map φ) :=
    le_of_eq (by rw [H.card_map hL, H.card_map hL'])
  exact H.inj L hL L' hL' (Subgroup.eq_of_le_of_card_ge h hcard)

theorem conjSub_eq_of_gen (H : Hyp φ Q) {L L' : Subgroup X} (hL : L ∈ Q) (hL' : L' ∈ Q)
    {S : Set X} (hS : L ≤ Subgroup.closure S) {g : X}
    (hg : ∀ s ∈ S, φ (g * s * g⁻¹) ∈ L'.map φ) : conjSub g L = L' := by
  let K' : Subgroup X := (L'.map φ).comap φ
  let P : Subgroup X := K'.comap (MulAut.conj g).toMonoidHom
  have hSP : S ⊆ (P : Set X) := fun s hs => hg s hs
  have hLP : L ≤ P := hS.trans ((Subgroup.closure_le _).mpr hSP)
  have hle : (conjSub g L).map φ ≤ L'.map φ := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : g⁻¹ * x * g ∈ L := (mem_conjSub_iff).mp hx
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ K' := hLP h1
    have h4 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [h4] at h2
    exact h2
  exact H.eq_of_map_le (H.conj L hL g) hL' hle

end Hyp

structure Lab (φ : X →* AEQ 8) (Q : Set (Subgroup X)) where
  K1 : Subgroup X
  a : X
  b : X
  T : ℕ → X
  mem_Q : K1 ∈ Q
  a_mem : a ∈ K1
  b_mem : b ∈ K1
  phi_a : φ a = mkQ 8 nA
  phi_b : φ b = mkQ 8 nB
  map_K1 : K1.map φ = memBar α0 α0_card true
  phi_T : ∀ j < 28, φ (T j) = mkQ 8 (nC j)
  T_zero : T 0 = 1

private theorem fr_nWord_conj (j : ℕ) {W : List ℕ} (hW : ∀ l ∈ W, l < 2) :
    nWord j W = nC j * nWord 0 W * (nC j)⁻¹ := by
  unfold nWord
  refine fr_conj_prod_map (nC j) (fun l => nG (2 * 0 + l)) (fun l => nG (2 * j + l)) W ?_
  intro l hl
  have hl2 := hW l hl
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    rw [nG_zero, nG_even j]
  · simp only [Nat.mul_zero, Nat.zero_add]
    rw [nG_one, nG_odd j]

namespace Lab

variable {φ : X →* AEQ 8} {Q : Set (Subgroup X)} (F : Lab φ Q)

@[expose] def gen (i : ℕ) : X :=
  F.T (i / 2) * (if i % 2 = 0 then F.a else F.b) * (F.T (i / 2))⁻¹

@[expose] def L (j : ℕ) : Subgroup X := conjSub (F.T j) F.K1

@[expose] def ev (j : ℕ) (W : List ℕ) : X := (W.map fun l => F.gen (2 * j + l)).prod

@[expose] def z1 : X := F.a * F.a

@[expose] def zj (j : ℕ) : X := F.T j * F.z1 * (F.T j)⁻¹

@[expose] def np (p : ℕ) : X := (F.z1)⁻¹ * F.zj p

@[expose] def N0 : Subgroup X := Subgroup.closure {x | ∃ p ∈ e29Partners, x = F.np p}

theorem exists_lab (H : Hyp φ Q) : Nonempty (Lab φ Q) := by
  obtain ⟨K1, hK1Q, hK1⟩ := H.surj α0 α0_mem_e29Sets α0_card true
  have hA : mkQ 8 nA ∈ K1.map φ := by
    rw [hK1]
    exact mkQ_nA_mem
  have hB : mkQ 8 nB ∈ K1.map φ := by
    rw [hK1]
    exact mkQ_nB_mem
  obtain ⟨a, haK1, hφa⟩ := Subgroup.mem_map.mp hA
  obtain ⟨b, hbK1, hφb⟩ := Subgroup.mem_map.mp hB
  have hlift : ∀ j < 28, ∃ x : X, φ x = mkQ 8 (nC j) := by
    intro j hj
    have hmem : mkQ 8 (nC j) ∈ φ.range := by
      rw [H.range_eq]
      exact Subgroup.mem_map_of_mem (mkQ 8) (nC_mem hj)
    exact MonoidHom.mem_range.mp hmem
  obtain ⟨T, hT0, hTφ⟩ : ∃ T : ℕ → X, T 0 = 1 ∧ ∀ j < 28, φ (T j) = mkQ 8 (nC j) := by
    refine ⟨fun j => if j = 0 then 1 else if h : j < 28 then Classical.choose (hlift j h) else 1,
      by simp, ?_⟩
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp [nC_zero]
    · show φ (if j = 0 then 1 else if h : j < 28 then Classical.choose (hlift j h) else 1) =
        mkQ 8 (nC j)
      rw [if_neg hj0, dif_pos hj]
      exact Classical.choose_spec (hlift j hj)
  exact ⟨⟨K1, a, b, T, hK1Q, haK1, hbK1, hφa, hφb, hK1, hTφ, hT0⟩⟩

theorem gen_zero : F.gen 0 = F.a := by
  unfold gen
  simp [F.T_zero]

theorem gen_one : F.gen 1 = F.b := by
  unfold gen
  simp [F.T_zero]

theorem gen_even (j : ℕ) : F.gen (2 * j) = F.T j * F.a * (F.T j)⁻¹ := by
  have h1 : 2 * j / 2 = j := by omega
  have h2 : 2 * j % 2 = 0 := by omega
  unfold gen
  rw [h1, if_pos h2]

theorem gen_odd (j : ℕ) : F.gen (2 * j + 1) = F.T j * F.b * (F.T j)⁻¹ := by
  have h1 : (2 * j + 1) / 2 = j := by omega
  have h2 : ¬ ((2 * j + 1) % 2 = 0) := by omega
  unfold gen
  rw [h1, if_neg h2]

theorem L_zero : F.L 0 = F.K1 := by
  unfold L
  rw [F.T_zero, conjSub_one]

theorem zj_eq_sq (j : ℕ) : F.zj j = F.gen (2 * j) * F.gen (2 * j) := by
  rw [F.gen_even j]
  unfold zj z1
  group

theorem phi_gen {i : ℕ} (hi : i < 56) : φ (F.gen i) = mkQ 8 (nG i) := by
  have hT := F.phi_T (i / 2) (by omega)
  have hab : φ (if i % 2 = 0 then F.a else F.b) = mkQ 8 (if i % 2 = 0 then nA else nB) := by
    split_ifs
    · exact F.phi_a
    · exact F.phi_b
  unfold gen nG
  simp only [map_mul, map_inv]
  rw [hT, hab]

theorem phi_ev {j : ℕ} (hj : j < 28) {W : List ℕ} (hW : ∀ l ∈ W, l < 2) :
    φ (F.ev j W) = mkQ 8 (nWord j W) := by
  unfold ev nWord
  rw [map_list_prod φ, List.map_map, map_list_prod (mkQ 8), List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  exact F.phi_gen (by have := hW l hl; omega)

theorem L_mem_Q (H : Hyp φ Q) (j : ℕ) : F.L j ∈ Q := H.conj F.K1 F.mem_Q (F.T j)

theorem gen_mem_L (j : ℕ) {l : ℕ} (hl : l < 2) : F.gen (2 * j + l) ∈ F.L j := by
  unfold L
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · rw [Nat.add_zero, F.gen_even j]
    exact conj_mem_conjSub F.a_mem
  · rw [F.gen_odd j]
    exact conj_mem_conjSub F.b_mem

theorem ev_mem_L (j : ℕ) {W : List ℕ} (hW : ∀ l ∈ W, l < 2) : F.ev j W ∈ F.L j := by
  unfold ev
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  exact F.gen_mem_L j (hW l hl)

theorem mem_L (H : Hyp φ Q) {j : ℕ} (hj : j < 28) {x : X}
    (hx : x ∈ F.L j) : ∃ W ∈ localWords29, x = F.ev j W := by
  have hx' : x ∈ conjSub (F.T j) F.K1 := hx
  have hxk : (F.T j)⁻¹ * x * F.T j ∈ F.K1 := (mem_conjSub_iff).mp hx'
  have hmem : φ ((F.T j)⁻¹ * x * F.T j) ∈ memBar α0 α0_card true := by
    rw [← F.map_K1]
    exact Subgroup.mem_map_of_mem φ hxk
  obtain ⟨W, hW, hφk⟩ := mem_memBar_zero29 hmem
  have hWlt : ∀ l ∈ W, l < 2 := localWords29_lt W hW
  refine ⟨W, hW, ?_⟩
  have hconj : φ x = φ (F.T j) * φ ((F.T j)⁻¹ * x * F.T j) * (φ (F.T j))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hφx : φ x = φ (F.ev j W) := by
    rw [F.phi_ev hj hWlt, hconj, hφk, F.phi_T j hj, fr_nWord_conj j hWlt]
    simp only [map_mul, map_inv]
  exact H.injOn (F.L_mem_Q H j) hx (F.ev_mem_L j hWlt) hφx

end Lab

end CFSG.ClassicalInvolution.Q3.E29Ker
