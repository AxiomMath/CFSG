module

public import Certificates.Data.Kernel.EvenBN.YamadaK
public import CFSG.Certificates.Kernel.EvenBN.F4MatSound

public section

namespace CFSG.KC.YamadaK

open CFSG.KC.Enum CFSG.KC.F4Mat CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open Certificates.U52Yamada

theorem g4_code (x : F4) : g4 (code x) = x := f4_code x

theorem all4_spec {f : Nat → Bool} (h : all4 f = true) (x : F4) : f (code x) = true := by
  obtain ⟨⟨c, hc⟩⟩ := x
  simp only [all4, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  change f c = true
  interval_cases c <;> assumption

theorem g4_inj {x y : Nat} (hx : x < 4) (hy : y < 4) (h : g4 x = g4 y) : x = y := by
  have h' := congrArg (fun z : F4 => z.code.val) h
  change x % 4 = y % 4 at h'
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'

theorem vpK_iff {a b : Nat} (ha : a < 4) (hb : b < 4) :
    vpK a b = true ↔ ValidPair (g4 a) (g4 b) := by
  change Nat.beq (ent MT (4 * a + ent BT a)) (Nat.xor b (ent BT b)) = true ↔
    f4 a * bar (f4 a) = f4 b + bar (f4 b)
  rw [← bt_ok ha, ← bt_ok hb, ← mt_ok ha (ent_lt _ _)]
  obtain ⟨hr, hrl⟩ := xor_ok hb (ent_lt BT b)
  rw [← hr]
  exact ⟨fun h => by rw [Nat.eq_of_beq_eq_true h], fun h => by
    rw [g4_inj (ent_lt _ _) hrl h]
    exact Nat.beq_refl _⟩

theorem decM_barK (A : Nat) : decM (barK A) = (decM A).map bar := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  change f4 (ent (barK A) (5 * i.val + j.val)) = bar (f4 (ent A (5 * i.val + j.val)))
  simp only [barK, strictN_app]
  refine (congrArg f4 (ent_encF (f := fun t => ent BT (ent A t)) (fun t => ent_lt _ _) 25 0 _
    (by omega))).trans ?_
  rw [Nat.zero_add]
  exact bt_ok (ent_lt _ _)

theorem chkL_of {N : Nat} : ∀ {L : List (Nat × Nat)}, (∀ p ∈ L, ent N p.1 = p.2) → chkL N L = true
  | [], _ => by
    unfold chkL
    rw [strictB_app]
  | (k, v) :: L, h => by
    have ih := chkL_of (L := L) fun p hp => h p (List.mem_cons_of_mem _ hp)
    have e : Nat.beq (ent N k) v = true := by
      rw [h (k, v) List.mem_cons_self]
      exact Nat.beq_refl v
    have h' : Bool.rec (motive := fun _ => Bool) false (chkL N L) (Nat.beq (ent N k) v) = true := by
      rw [e]
      exact ih
    unfold chkL at h' ⊢
    rw [strictB_app] at h' ⊢
    exact h'

theorem ent_of {N : Nat} {M : Matrix (Fin 5) (Fin 5) F4} (h : decM N = M) (i j : Fin 5) :
    ent N (5 * i.val + j.val) = code (M i j) := by
  rw [← h]
  change ent N _ = ent N (5 * i.val + j.val) % 4
  exact (Nat.mod_eq_of_lt (ent_lt _ _)).symm

theorem idL_spec : ∀ p ∈ idL, ∃ i j : Fin 5,
    p.1 = 5 * i.val + j.val ∧ p.2 = code ((1 : Matrix (Fin 5) (Fin 5) F4) i j) := by decide

theorem chkL_id {N : Nat} (h : decM N = 1) : chkL N idL = true := by
  refine chkL_of fun p hp => ?_
  obtain ⟨i, j, h1, h2⟩ := idL_spec p hp
  rw [h1, h2]
  exact ent_of h i j

theorem decM_nfK (a₁ b₁ a₂ a₃ a₄ b₄ : Nat) :
    decM (nfK a₁ b₁ a₂ a₃ a₄ b₄) = nfMat (g4 a₁) (g4 b₁) (g4 a₂) (g4 a₃) (g4 a₄) (g4 b₄) := by
  simp only [nfK, decM_mulK, decM_enc, nfMat]

theorem wordK_eq : ∀ w : List (Fin 10), decM (wordK w) = wordMat w
  | [] => by
    change decM (enc 1) = _
    rw [decM_enc]
    rfl
  | i :: w => by
    change decM (mulK (enc (genMat i)) (wordK w)) = _
    rw [decM_mulK, decM_enc, wordK_eq w, wordMat, wordMat, List.map_cons, List.prod_cons]

theorem decM_conjK (k : Fin 8) (S : Nat) : decM (conjK k S) =
    wordMat (conjWord k) * decM S * invMat (wordMat (conjWord k)) := by
  simp only [conjK, decM_mulK, decM_invK, wordK_eq]

theorem t39_sound {a₁ b₁ a₂ a₃ a₄ b₄ : Nat} (ha₁ : a₁ < 4) (hb₁ : b₁ < 4) (ha₄ : a₄ < 4)
    (hb₄ : b₄ < 4) (h : t39 a₁ b₁ a₂ a₃ a₄ b₄ = true) :
    ValidPair (g4 a₁) (g4 b₁) → ValidPair (g4 a₄) (g4 b₄) →
      nfMat (g4 a₁) (g4 b₁) (g4 a₂) (g4 a₃) (g4 a₄) (g4 b₄) *
        nfMat (g4 a₁) (g4 b₁) (g4 a₂) (g4 a₃) (g4 a₄) (g4 b₄) = 1 →
      IsFShape (nfMat (g4 a₁) (g4 b₁) (g4 a₂) (g4 a₃) (g4 a₄) (g4 b₄)) ∨ ∃ k : Fin 8,
        IsFShape (wordMat (conjWord k) * nfMat (g4 a₁) (g4 b₁) (g4 a₂) (g4 a₃) (g4 a₄) (g4 b₄) *
          invMat (wordMat (conjWord k))) := by
  intro h1 h4 hs
  have hS := decM_nfK a₁ b₁ a₂ a₃ a₄ b₄
  unfold t39 at h
  rw [(vpK_iff ha₁ hb₁).2 h1, (vpK_iff ha₄ hb₄).2 h4, strictB_app] at h
  generalize nfK a₁ b₁ a₂ a₃ a₄ b₄ = S at h hS
  rw [← hS] at hs ⊢
  have hid : chkL (mulK S S) idL = true := chkL_id (by rw [decM_mulK, hs])
  rw [hid] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  have hk : ∀ k : Fin 8, chkL (conjK k S) fShapeL = true → ∃ k : Fin 8,
      IsFShape (wordMat (conjWord k) * decM S * invMat (wordMat (conjWord k))) := fun k hk =>
    ⟨k, by rw [← decM_conjK]; exact fShape_of hk⟩
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  exacts [Or.inl (fShape_of h), Or.inr (hk 0 h), Or.inr (hk 1 h), Or.inr (hk 2 h),
    Or.inr (hk 3 h), Or.inr (hk 4 h), Or.inr (hk 5 h), Or.inr (hk 6 h), Or.inr (hk 7 h)]

theorem w3101_sound {m S : Nat} (h : w3101 m S = true) : ∃ c₁ d₁ c₂ c₃ c₄ d₄ : F4,
    ValidPair c₁ d₁ ∧ ValidPair c₄ d₄ ∧
      nfMat c₁ d₁ c₂ c₃ c₄ d₄ * decM S = (nfMat c₁ d₁ c₂ c₃ c₄ d₄).map bar := by
  have hd : ∀ i, dg m i < 4 := fun i => Nat.mod_lt _ (by decide)
  unfold w3101 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h4⟩, h⟩ := h
  rw [strictB_app] at h
  refine ⟨g4 (dg m 5), g4 (dg m 4), g4 (dg m 3), g4 (dg m 2), g4 (dg m 1), g4 (dg m 0), (vpK_iff (hd 5) (hd 4)).1 h1, (vpK_iff (hd 1) (hd 0)).1 h4, ?_⟩
  rw [← decM_nfK, ← decM_mulK, ← decM_barK, Nat.eq_of_beq_eq_true h]

theorem t3101_sound {H : List (Nat × Nat)} {a₁ b₁ a₂ a₃ a₄ b₄ : Nat} (ha₁ : a₁ < 4)
    (hb₁ : b₁ < 4) (ha₄ : a₄ < 4) (hb₄ : b₄ < 4) (h : t3101 H a₁ b₁ a₂ a₃ a₄ b₄ = true) :
    ValidPair (g4 a₁) (g4 b₁) → ValidPair (g4 a₄) (g4 b₄) →
      nfMat (g4 a₁) (g4 b₁) (g4 a₂) (g4 a₃) (g4 a₄) (g4 b₄) *
        (nfMat (g4 a₁) (g4 b₁) (g4 a₂) (g4 a₃) (g4 a₄) (g4 b₄)).map bar = 1 →
      ∃ c₁ d₁ c₂ c₃ c₄ d₄ : F4, ValidPair c₁ d₁ ∧ ValidPair c₄ d₄ ∧
        nfMat c₁ d₁ c₂ c₃ c₄ d₄ * nfMat (g4 a₁) (g4 b₁) (g4 a₂) (g4 a₃) (g4 a₄) (g4 b₄) =
          (nfMat c₁ d₁ c₂ c₃ c₄ d₄).map bar := by
  intro h1 h4 hs
  have hS := decM_nfK a₁ b₁ a₂ a₃ a₄ b₄
  unfold t3101 at h
  rw [(vpK_iff ha₁ hb₁).2 h1, (vpK_iff ha₄ hb₄).2 h4, strictB_app] at h
  generalize nfK a₁ b₁ a₂ a₃ a₄ b₄ = S at h hS
  rw [← hS] at hs ⊢
  have hid : chkL (mulK S (barK S)) idL = true := chkL_id (by rw [decM_mulK, decM_barK, hs])
  rw [hid] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact w3101_sound h

end CFSG.KC.YamadaK

end
