module

public import Certificates.Data.Kernel.M11Local
public import CFSG.Certificates.Kernel.Misc.KGrpProof
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.KC.M11L

open Equiv CFSG.KC.LQT CFSG.KC.Misc CFSG.KC.Misc.Clos CFSG.GH74.KGroups

theorem hn11 : (11 : ℕ) ≤ 32 := by norm_num

theorem allL_map_iff (L : List (Perm (Fin 11))) (f : ℕ → Bool) :
    P.allL (L.map pcode) f = true ↔ ∀ g ∈ L, f (pcode g) = true := by
  rw [KG.allL_iff, List.forall_mem_map]

theorem anyL_map_iff (L : List (Perm (Fin 11))) (f : ℕ → Bool) :
    P.anyL (L.map pcode) f = true ↔ ∃ g ∈ L, f (pcode g) = true := by
  rw [KG.anyL_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
    exact ⟨g, hg, h⟩
  · rintro ⟨g, hg, h⟩
    exact ⟨pcode g, List.mem_map.2 ⟨g, hg, rfl⟩, h⟩

theorem beq_img (g : Perm (Fin 11)) (i j : Fin 11) :
    Nat.beq (P.img (pcode g) i) j = true ↔ g i = j := by
  rw [KG.beq_true_iff, pcode_img_proved hn11, Fin.val_inj]

theorem conj_pcode (g v : Perm (Fin 11)) : P.conj 11 (pcode g) (pcode v) = pcode (g * v * g⁻¹) := by
  unfold P.conj
  rw [KG.pcode_mul_proved hn11, pcode_inv_proved hn11, KG.pcode_mul_proved hn11]

theorem nodupK_sound : ∀ {l : List ℕ}, nodupK l = true → l.Nodup
  | [], _ => List.nodup_nil
  | c :: l, h => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (KG.memL c l)) (nodupK l) = true at h
    rw [KG.andB_iff, KG.notB_iff, KG.memL_iff] at h
    exact List.nodup_cons.2 ⟨h.1, nodupK_sound h.2⟩

theorem closK_sound {L : List (Perm (Fin 11))} (h : closK (L.map pcode) = true) :
    (∀ c ∈ L, c⁻¹ ∈ L) ∧ ∀ c ∈ L, ∀ d ∈ L, c * d ∈ L := by
  unfold closK at h
  rw [allL_map_iff] at h
  refine ⟨fun c hc => ?_, fun c hc d hd => ?_⟩
  · have h1 := (KG.andB_iff.1 (h c hc)).1
    rwa [pcode_inv_proved hn11, KG.memL_map_iff_proved hn11] at h1
  · have h1 := (KG.andB_iff.1 (h c hc)).2
    rw [allL_map_iff] at h1
    have h2 := h1 d hd
    rwa [KG.pcode_mul_proved hn11, KG.memL_map_iff_proved hn11] at h2

theorem fix01K_sound {e : Perm (Fin 11)} (h : fix01K (pcode e) = true) :
    e 0 = 0 ∧ e 1 = 1 ∧ ∀ i : Fin 11, 2 ≤ (i : ℕ) → e i ≠ i := by
  unfold fix01K at h
  rw [KG.andB_iff, KG.andB_iff, allN_iff] at h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨(beq_img e 0 0).1 h0, (beq_img e 1 1).1 h1, fun i hi he => ?_⟩
  have h3 : CFSG.KC.Ord.notB (Nat.beq (P.img (pcode e) ((i : ℕ) - 2 + 2)) ((i : ℕ) - 2 + 2)) =
      true := h2 _ (by omega)
  rw [KG.notB_iff, Nat.sub_add_cancel hi] at h3
  exact h3 ((beq_img e i i).2 he)

theorem regK_sound {L : List (Perm (Fin 11))} (h : regK (L.map pcode) = true) :
    ∀ i : Fin 11, 2 ≤ (i : ℕ) → ∃ e ∈ L, e 2 = i := by
  intro i hi
  unfold regK at h
  rw [allN_iff] at h
  have h1 : P.anyL (L.map pcode) (fun e => Nat.beq (P.img e 2) ((i : ℕ) - 2 + 2)) = true :=
    h _ (by omega)
  rw [anyL_map_iff, Nat.sub_add_cancel hi] at h1
  obtain ⟨e, he, h2⟩ := h1
  exact ⟨e, he, (beq_img e 2 i).1 h2⟩

theorem duadK_iff (g : Perm (Fin 11)) :
    duadK (pcode g) = true ↔ ((g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 1 ∧ g 1 = 0)) := by
  have h00 : Nat.beq (P.img (pcode g) 0) 0 = true ↔ g 0 = 0 := beq_img g 0 0
  have h11 : Nat.beq (P.img (pcode g) 1) 1 = true ↔ g 1 = 1 := beq_img g 1 1
  have h01 : Nat.beq (P.img (pcode g) 0) 1 = true ↔ g 0 = 1 := beq_img g 0 1
  have h10 : Nat.beq (P.img (pcode g) 1) 0 = true ↔ g 1 = 0 := beq_img g 1 0
  unfold duadK
  rw [KG.orB_iff, KG.andB_iff, KG.andB_iff, h00, h11, h01, h10]

theorem transK_sound {m : ℕ} {s : Perm (Fin 11)} {L : List (Perm (Fin 11))}
    (h : transK m (pcode s) (L.map pcode) = true) :
    ∀ v ∈ L, v ≠ 1 → ∀ t ∈ L, t ≠ 1 → ∃ k < m,
      ((s ^ k) 0 = 0 ∧ (s ^ k) 1 = 1 ∨ (s ^ k) 0 = 1 ∧ (s ^ k) 1 = 0) ∧
        s ^ k * v * (s ^ k)⁻¹ = t := by
  intro v hv hv1 t ht ht1
  unfold transK at h
  rw [allL_map_iff] at h
  have h1 := h v hv
  rw [KG.orB_iff, KG.isOne_iff_proved hn11, allL_map_iff] at h1
  have h2 := h1.resolve_left hv1 t ht
  rw [KG.orB_iff, KG.isOne_iff_proved hn11, anyN_iff] at h2
  obtain ⟨k, hk, h3⟩ := h2.resolve_left ht1
  rw [KG.andB_iff, KG.pcode_pow_proved hn11, duadK_iff, conj_pcode, KG.beq_iff_proved hn11] at h3
  exact ⟨k, hk, h3⟩

theorem m11K_sound {x y s a b : Perm (Fin 11)} {wx wy ws : List Bool}
    (h : m11K (pcode x) (pcode y) (pcode s) (pcode a) (pcode b) wx wy ws = true) :
    evalW a b wx = x ∧ evalW a b wy = y ∧ evalW a b ws = s ∧ (pow3list x y).Nodup ∧
      (∀ c ∈ pow3list x y, c⁻¹ ∈ pow3list x y) ∧
      (∀ c ∈ pow3list x y, ∀ d ∈ pow3list x y, c * d ∈ pow3list x y) ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧
      y ∉ ([1, x, x ^ 2] : List (Perm (Fin 11))) ∧
      (∀ e ∈ pow3list x y, e ≠ 1 → e 0 = 0 ∧ e 1 = 1 ∧ ∀ i : Fin 11, 2 ≤ (i : ℕ) → e i ≠ i) ∧
      (∀ i : Fin 11, 2 ≤ (i : ℕ) → ∃ e ∈ pow3list x y, e 2 = i) ∧
      ((s 0 = 0 ∧ s 1 = 1) ∨ (s 0 = 1 ∧ s 1 = 0)) ∧ s ^ 8 = 1 ∧ s ^ 4 ≠ 1 ∧
      s * x * s⁻¹ ∈ pow3list x y ∧ s * y * s⁻¹ ∈ pow3list x y ∧
      (∀ t ∈ pow3list x y, t ≠ 1 → s * t * s⁻¹ ≠ t) ∧
      (∀ v ∈ pow3list x y, v ≠ 1 → ∀ t ∈ pow3list x y, t ≠ 1 → ∃ k < 8,
        ((s ^ k) 0 = 0 ∧ (s ^ k) 1 = 1 ∨ (s ^ k) 0 = 1 ∧ (s ^ k) 1 = 0) ∧
          s ^ k * v * (s ^ k)⁻¹ = t) := by
  unfold m11K at h
  rw [KG.pow3K_eq_proved hn11] at h
  simp only [KG.andB_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := h
  rw [KG.evalWK_eq_proved hn11, KG.beq_iff_proved hn11] at h1 h2 h3
  rw [KG.notB_iff, KG.pow2K_eq_proved hn11, KG.memL_map_iff_proved hn11] at h10
  rw [KG.pcode_pow_proved hn11, KG.isOne_iff_proved hn11] at h14
  rw [KG.notB_iff, KG.pcode_pow_proved hn11, KG.isOne_iff_proved hn11] at h15
  rw [conj_pcode, KG.memL_map_iff_proved hn11] at h16 h17
  obtain ⟨hinv, hmul⟩ := closK_sound h5
  refine ⟨h1, h2, h3, (nodupK_sound h4).of_map pcode, hinv, hmul,
    (KG.cubeOne_iff_proved hn11 x).1 h6, (KG.cubeOne_iff_proved hn11 y).1 h7,
    (KG.comm_iff_proved hn11 x y).1 h8,
    fun hx => (KG.notB_iff.1 h9) ((KG.isOne_iff_proved hn11 x).2 hx), h10, ?_,
    regK_sound h12, (duadK_iff s).1 h13, h14, h15, h16, h17, ?_, transK_sound h19⟩
  · intro e he he1
    have h' := (allL_map_iff _ _).1 h11 e he
    rw [KG.orB_iff, KG.isOne_iff_proved hn11] at h'
    exact fix01K_sound (h'.resolve_left he1)
  · intro t ht ht1
    have h' := (allL_map_iff _ _).1 h18 t ht
    rw [KG.orB_iff, KG.isOne_iff_proved hn11, KG.notB_iff, conj_pcode,
      KG.beq_iff_proved hn11] at h'
    exact h'.resolve_left ht1

end CFSG.KC.M11L

end
