module

public import CFSG.Permutation.FinPackPow

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95IvAuxK

open Equiv Equiv.Perm CFSG.Permutation.FinPack

theorem h16 : 7 ≤ 16 := by norm_num

@[expose] noncomputable def commK (c d : ℕ) : Bool := Nat.beq (mulK 7 c d) (mulK 7 d c)

@[expose] noncomputable def q12 (c : ℕ) : Bool :=
  !commK c 106180641 || !evenK 7 c ||
    (Nat.beq (powK 7 106181136 c 6) 106181136 &&
      (!Nat.beq (powK 7 106181136 c 2) 106181136 ||
        (Nat.beq c 106181136 || Nat.beq c 90391056 || Nat.beq c 70668816 || Nat.beq c 54878736)))

theorem q12_walk : walkK 7 q12 7 0 0 0 = true := by decide +kernel

@[expose] noncomputable def q34 (c : ℕ) : Bool :=
  !Nat.beq (supK 7 c) 3 ||
    ((!commK c 106180641 || (Nat.beq c 106180641 || Nat.beq c 106180866 || disjK 7 106180641 c)) &&
      (!disjK 7 106180641 c ||
        !walkK 7 (fun t => !(commK t 106180641 && Nat.beq (mulK 7 t c) (mulK 7 104153616 t)))
          7 0 0 0))

theorem q34_walk : walkK 7 q34 7 0 0 0 = true := by decide +kernel

theorem commK_iff {σ τ : Perm (Fin 7)} : commK (enc σ) (enc τ) = true ↔ σ * τ = τ * σ :=
  comm_enc_iff h16

theorem eq_iff_beq {σ τ : Perm (Fin 7)} {t : ℕ} (ht : enc τ = t) :
    σ = τ ↔ Nat.beq (enc σ) t = true := by
  rw [← ht, beq_enc_iff h16]

theorem pow_iff_beq {σ : Perm (Fin 7)} {e : ℕ} (he : enc (1 : Perm (Fin 7)) = e) (k : ℕ) :
    σ ^ k = 1 ↔ Nat.beq (powK 7 e (enc σ) k) e = true := by
  rw [← enc_pow h16 he, ← he, beq_enc_iff h16]

theorem pow_inv_K (a x y : Perm (Fin 7)) (ha : enc a = 106180641)
    (he : enc (1 : Perm (Fin 7)) = 106181136) (hx : enc x = 90391056) (hy : enc y = 70668816)
    (hxy : enc (x * y) = 54878736) (g : Perm (Fin 7)) :
    (Perm.sign g = 1 → g * a = a * g → g ^ 6 = 1) ∧
      (Perm.sign g = 1 → g * a = a * g → g ^ 2 = 1 → g = 1 ∨ g = x ∨ g = y ∨ g = x * y) := by
  have h := walkK_sound q12_walk g
  have hc : g * a = a * g ↔ commK (enc g) 106180641 = true := by
    rw [← ha]
    exact commK_iff.symm
  rw [q12.eq_1] at h
  refine ⟨fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
  · rw [(sign_eq_one_iff_evenK h16 g).1 h1, hc.1 h2] at h
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    exact (pow_iff_beq he 6).2 h.1
  · rw [(sign_eq_one_iff_evenK h16 g).1 h1, hc.1 h2, (pow_iff_beq he 2).1 h3] at h
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.2 with ((e | e) | e) | e
    · exact Or.inl ((eq_iff_beq he).2 e)
    · exact Or.inr (Or.inl ((eq_iff_beq hx).2 e))
    · exact Or.inr (Or.inr (Or.inl ((eq_iff_beq hy).2 e)))
    · exact Or.inr (Or.inr (Or.inr ((eq_iff_beq hxy).2 e)))

theorem three_K (a b : Perm (Fin 7)) (ha : enc a = 106180641) (ha2 : enc (a ^ 2) = 106180866)
    (hb : enc b = 104153616) (g : Perm (Fin 7)) :
    (g.support.card = 3 → g * a = a * g → g = a ∨ g = a ^ 2 ∨ Disjoint a.support g.support) ∧
      (g.support.card = 3 → Disjoint a.support g.support →
        ∃ τ : Perm (Fin 7), τ * a = a * τ ∧ τ * g = b * τ) := by
  have h := walkK_sound q34_walk g
  have hs : g.support.card = 3 ↔ Nat.beq (supK 7 (enc g)) 3 = true := by
    rw [card_support_eq_supK h16, Nat.beq_eq]
  have hc : g * a = a * g ↔ commK (enc g) 106180641 = true := by
    rw [← ha]
    exact commK_iff.symm
  have hd : Disjoint a.support g.support ↔ disjK 7 106180641 (enc g) = true := by
    rw [← ha]
    exact disjoint_support_iff h16 a g
  rw [q34.eq_1] at h
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [hs.1 h1, hc.1 h2] at h
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.1 with (e | e) | e
    · exact Or.inl ((eq_iff_beq ha).2 e)
    · exact Or.inr (Or.inl ((eq_iff_beq ha2).2 e))
    · exact Or.inr (Or.inr (hd.2 e))
  · rw [hs.1 h1, hd.1 h2] at h
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_true, true_and,
      Bool.not_eq_true'] at h
    obtain ⟨τ, hτ⟩ := exists_of_walkK
      (P := fun t => commK t 106180641 && Nat.beq (mulK 7 t (enc g)) (mulK 7 104153616 t)) h
    simp only [Bool.and_eq_true] at hτ
    obtain ⟨t1, t2⟩ := hτ
    rw [← ha] at t1
    rw [← hb, ← enc_mul h16, ← enc_mul h16, beq_enc_iff h16] at t2
    exact ⟨τ, commK_iff.1 t1, t2⟩

@[expose] noncomputable def qV (c : ℕ) : Bool :=
  Nat.beq c 106181136 || Nat.beq c 90391056 || Nat.beq c 70668816 || Nat.beq c 54878736

theorem cnt_V : cntK 7 qV 7 0 0 0 = 4 := by decide +kernel

theorem card_V_K (x y : Perm (Fin 7)) (he : enc (1 : Perm (Fin 7)) = 106181136)
    (hx : enc x = 90391056) (hy : enc y = 70668816) (hxy : enc (x * y) = 54878736) :
    Fintype.card {g : Perm (Fin 7) // g = 1 ∨ g = x ∨ g = y ∨ g = x * y} = 4 := by
  have hP : ∀ g : Perm (Fin 7), (g = 1 ∨ g = x ∨ g = y ∨ g = x * y) ↔ qV (enc g) = true := by
    intro g
    rw [qV.eq_1]
    simp only [Bool.or_eq_true, or_assoc]
    rw [← eq_iff_beq he, ← eq_iff_beq hx, ← eq_iff_beq hy, ← eq_iff_beq hxy]
  rw [Fintype.card_subtype, Finset.filter_congr (fun g _ => hP g), card_filter_eq_cntK, cnt_V]

@[expose] noncomputable def LV : List ℕ := [90391056, 70668816, 54878736]

@[expose] noncomputable def genB : Bool :=
  allK (fun v => allK (fun u₁ => allK (fun u₂ => Nat.beq u₁ u₂ || (Nat.beq v 106181136 ||
    (Nat.beq v u₁ || (Nat.beq v u₂ || Nat.beq v (mulK 7 u₁ u₂))))) LV) LV) (106181136 :: LV)

theorem genB_check : genB = true := by decide +kernel

theorem mem_of_map {l : List (Perm (Fin 7))} {L : List ℕ} (hl : l.map enc = L) {a : Perm (Fin 7)}
    (h : a ∈ l) : enc a ∈ L := by
  rw [← hl]
  exact List.mem_map_of_mem h

theorem gen_K {l₁ l₂ : List (Perm (Fin 7))} (he : enc (1 : Perm (Fin 7)) = 106181136)
    (h₁ : l₁.map enc = 106181136 :: LV) (h₂ : l₂.map enc = LV) :
    ∀ v ∈ l₁, ∀ u₁ ∈ l₂, ∀ u₂ ∈ l₂, u₁ ≠ u₂ → v = 1 ∨ v = u₁ ∨ v = u₂ ∨ v = u₁ * u₂ := by
  intro v hv u₁ hu₁ u₂ hu₂ hne
  have hb := allK_iff.1 (allK_iff.1 (allK_iff.1 genB_check _ (mem_of_map h₁ hv)) _
    (mem_of_map h₂ hu₁)) _ (mem_of_map h₂ hu₂)
  rw [beq_enc_false h16 hne, ← he] at hb
  simp only [Bool.false_or, Bool.or_eq_true, ← enc_mul h16, beq_enc_iff h16] at hb
  exact hb

@[expose] noncomputable def cmK (w b bi : ℕ) : ℕ := mulK 7 (mulK 7 (mulK 7 w b) (invPK 7 w)) bi

@[expose] noncomputable def inV (c : ℕ) : Bool :=
  Nat.beq c 90391056 || (Nat.beq c 70668816 || Nat.beq c 54878736)

@[expose] noncomputable def commB : Bool :=
  allK (fun w => inV (cmK w 104153616 105075216) && (inV (cmK w 105075216 104153616) &&
    !Nat.beq (cmK w 104153616 105075216) (cmK w 105075216 104153616))) LV

theorem commB_check : commB = true := by decide +kernel

theorem enc_comm (w b : Perm (Fin 7)) :
    enc (w * b * w⁻¹ * b⁻¹) = cmK (enc w) (enc b) (enc b⁻¹) := by
  rw [cmK, enc_mul h16, enc_mul h16, enc_mul h16, enc_inv h16 w]

theorem inV_iff {c : Perm (Fin 7)} (x y : Perm (Fin 7)) (hx : enc x = 90391056)
    (hy : enc y = 70668816) (hxy : enc (x * y) = 54878736) :
    inV (enc c) = true ↔ c = x ∨ c = y ∨ c = x * y := by
  rw [inV.eq_1]
  simp only [Bool.or_eq_true]
  rw [← eq_iff_beq hx, ← eq_iff_beq hy, ← eq_iff_beq hxy]

theorem comm_K {l : List (Perm (Fin 7))} (x y b : Perm (Fin 7)) (hl : l.map enc = LV)
    (hx : enc x = 90391056) (hy : enc y = 70668816) (hxy : enc (x * y) = 54878736)
    (hb : enc b = 104153616) (hbi : enc b⁻¹ = 105075216) (hb2 : enc (b ^ 2) = 105075216)
    (hb2i : enc (b ^ 2)⁻¹ = 104153616) : ∀ w ∈ l,
      (w * b * w⁻¹ * b⁻¹ = x ∨ w * b * w⁻¹ * b⁻¹ = y ∨ w * b * w⁻¹ * b⁻¹ = x * y) ∧
        (w * b ^ 2 * w⁻¹ * (b ^ 2)⁻¹ = x ∨ w * b ^ 2 * w⁻¹ * (b ^ 2)⁻¹ = y ∨
          w * b ^ 2 * w⁻¹ * (b ^ 2)⁻¹ = x * y) ∧
        w * b * w⁻¹ * b⁻¹ ≠ w * b ^ 2 * w⁻¹ * (b ^ 2)⁻¹ := by
  intro w hw
  have h := allK_iff.1 commB_check _ (mem_of_map hl hw)
  have e1 : cmK (enc w) 104153616 105075216 = enc (w * b * w⁻¹ * b⁻¹) := by
    rw [enc_comm, hb, hbi]
  have e2 : cmK (enc w) 105075216 104153616 = enc (w * b ^ 2 * w⁻¹ * (b ^ 2)⁻¹) := by
    rw [enc_comm, hb2, hb2i]
  rw [e1, e2] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(inV_iff x y hx hy hxy).1 h1, (inV_iff x y hx hy hxy).1 h2, fun e => ?_⟩
  rw [e, Nat.beq_refl] at h3
  cases h3

end CFSG.LocalAnalysis.GLTheoremB.Prop95IvAuxK
