module

public import Certificates.Data.Kernel.TwistDce.Defs
public import CFSG.Certificates.CosetEnumeration
import CFSG.Certificates.Kernel.TwistDce.Walk
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Certificates.TwDce

open CFSG.KC.TwDce CFSG.Certificates.CosetEnumeration CFSG.KC.YModel

@[expose] noncomputable def wList (w : ℕ) : List ℕ := (List.range (wLen w)).map (wAt w)

@[expose] noncomputable def wVal {G : Type*} [Group G] (x : ℕ → G) (w : ℕ) : G :=
  evalWord x (wList w)

open CFSG.Certificates.TwDce.Words CFSG.Certificates.TwDce.Core

section Fold

variable {F RD RW RA RJ : ℕ → ℕ} {THM E BS NB : ℕ}

private theorem foldStep_eq (r S : ℕ) : foldStep F THM E BS NB RD RW RA RJ r S =
    if andB (Nat.blt 0 S) (andB (nodesOK S (RD r)) (recOK F THM E BS NB RD RW RA r (RJ r))) = true
    then (if Nat.beq (dKind (RD r)) 0 = true then S + 1 else S) else 0 := by
  unfold foldStep
  rw [sN_eq, brec_eq, brec_eq]

private theorem foldRange_succ (a n S : ℕ) : foldRange F THM E BS NB RD RW RA RJ a (n + 1) S =
    foldRange F THM E BS NB RD RW RA RJ (a + 1) n (foldStep F THM E BS NB RD RW RA RJ a S) := by
  unfold foldRange
  exact sN_eq _ _

private theorem foldRange_snoc (n : ℕ) : ∀ a S, foldRange F THM E BS NB RD RW RA RJ a (n + 1) S =
    foldStep F THM E BS NB RD RW RA RJ (a + n) (foldRange F THM E BS NB RD RW RA RJ a n S) := by
  induction n with
  | zero => intro a S; rw [foldRange_succ]; rfl
  | succ n ih =>
    intro a S
    rw [foldRange_succ, ih, foldRange_succ, show a + 1 + n = a + (n + 1) by omega]

end Fold

variable {G : Type*} [Group G]

private theorem recHolds_congr {RD RW RA : ℕ → ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}
    {X X' : ℕ → G} {f : ℕ} (h : RecHolds RD RW RA H x u X f)
    (h1 : dKind (RD f) < 3 → X' (dN1 (RD f)) = X (dN1 (RD f)) ∧ X' (dN2 (RD f)) = X (dN2 (RD f)))
    (h2 : dKind (RD f) < 5 → X' (dN2 (RD f)) = X (dN2 (RD f))) :
    RecHolds RD RW RA H x u X' f := by
  refine ⟨h.rw, h.ra, fun hk => ?_, fun hk3 hk5 => ?_⟩
  · rw [(h1 hk).1, (h1 hk).2]; exact h.fact hk
  · rw [h2 hk5]; exact h.stab hk3 hk5

private theorem beq_t {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

private theorem beq_f {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private def Bnd (RD : ℕ → ℕ) (j S : ℕ) : Prop :=
  ∀ r < j, (dKind (RD r) < 3 → dN1 (RD r) < S ∧ dN2 (RD r) < S) ∧
    (3 ≤ dKind (RD r) → dKind (RD r) < 5 → dN2 (RD r) < S)

private theorem rec_spec {F RD RW RA : ℕ → ℕ} {THM E BS NB : ℕ}
    {H : Subgroup G} {x : ℕ → G} {u : G}
    (hxH : ∀ c < 10, x c ∈ H) (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hE : E < 10 → (x E * u) ^ 4 = 1)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} (hX0 : X 0 = 1) {j J : ℕ} (hH : Hist RD RW RA H x u X j)
    (hRW : GW (2 ^ 20) (RW j)) (hRA : GW (2 ^ 20) (RA j)) (hk0 : dKind (RD j) ≠ 0)
    (h : recOK F THM E BS NB RD RW RA j J = true) : RecHolds RD RW RA H x u X j := by
  simp only [recOK, sB_eq, brec_eq, andB_iff] at h
  obtain ⟨-, -, h⟩ := h
  have hk0' : Nat.beq (dKind (RD j)) 0 = false := beq_f hk0
  rw [hk0'] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨hRW, hRA, fun hk => ?_, fun hk3 hk5 => ?_⟩
  · obtain hk1 | hk2 : dKind (RD j) = 1 ∨ dKind (RD j) = 2 := by omega
    · rw [beq_t hk1] at h
      exact walkOK_spec F RD RW RA THM E BS NB H x u hx hu hθ hE hone hH hRW hRA (by simpa using h)
    · rw [beq_f (a := dKind (RD j)) (b := 1) (by omega),
        beq_t hk2] at h
      exact factStepOK_spec F RD RW RA THM BS NB H x u hx hu hθ hone hH hRW hRA
        (by simpa using h)
  · rw [beq_f (a := dKind (RD j)) (b := 1) (by omega),
      beq_f (a := dKind (RD j)) (b := 2) (by omega)] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain hk3' | hk4 : dKind (RD j) = 3 ∨ dKind (RD j) = 4 := by omega
    · rw [show Nat.beq (dKind (RD j)) 3 = true by simp [hk3']] at h
      exact diffOK_spec F RD RW RA THM BS NB H x u hx hu hθ hone hH hRW (by simpa using h)
    · rw [beq_f (a := dKind (RD j)) (b := 3) (by omega)] at h
      simp only [Bool.false_eq_true, ↓reduceIte, andB_iff] at h
      rw [Nat.eq_of_beq_eq_true h.2, hX0, one_mul, inv_one, mul_one]
      exact evalWord_mem hxH hRW.lt

theorem dce_sound {F RD RW RA RJ : ℕ → ℕ} {THM E BS NB N C : ℕ}
    (hfold : foldRange F THM E BS NB RD RW RA RJ 0 N 1 = C) (hC : 0 < C)
    {G : Type*} [Group G] (H : Subgroup G) (x : ℕ → G) (u : G)
    (hxH : ∀ c < 10, x c ∈ H) (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hE : E < 10 → (x E * u) ^ 4 = 1)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    (hlen : ∀ r < N, wLen (RW r) < 2 ^ 20 ∧ wLen (RA r) < 2 ^ 20) :
    ∃ X : ℕ → G, X 0 = 1 ∧ ∀ r < N,
      (dKind (RD r) < 3 → dN1 (RD r) < C ∧ dN2 (RD r) < C ∧
        X (dN1 (RD r)) * wVal x (RW r) * u * (X (dN2 (RD r)) * wVal x (RA r))⁻¹ ∈ H) ∧
      (3 ≤ dKind (RD r) → dKind (RD r) < 5 → dN2 (RD r) < C ∧
        X (dN2 (RD r)) * wVal x (RW r) * (X (dN2 (RD r)))⁻¹ ∈ H) := by
  have inv : ∀ j ≤ N, 0 < foldRange F THM E BS NB RD RW RA RJ 0 j 1 → ∃ X : ℕ → G, X 0 = 1 ∧
      Hist RD RW RA H x u X j ∧ Bnd RD j (foldRange F THM E BS NB RD RW RA RJ 0 j 1) := by
    intro j
    induction j with
    | zero =>
      intro _ _
      exact ⟨fun _ => 1, rfl, fun f hf => absurd hf (Nat.not_lt_zero _),
        fun r hr => absurd hr (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj hS'
      rw [foldRange_snoc, zero_add] at hS' ⊢
      set S := foldRange F THM E BS NB RD RW RA RJ 0 j 1 with hSdef
      rw [foldStep_eq] at hS' ⊢
      split_ifs at hS' ⊢ with hc hk
      · simp only [andB_iff] at hc
        obtain ⟨hS0, hn, hrec⟩ := hc
        obtain ⟨X, hX0, hH, hB⟩ := ih (by omega) (Nat.blt_eq.mp hS0)
        have hk' : dKind (RD j) = 0 := Nat.eq_of_beq_eq_true hk
        simp only [nodesOK, sB_eq, brec_eq, hk, ↓reduceIte, andB_iff] at hn
        obtain ⟨hn1, hn2, -⟩ := hn
        have hn1' : dN1 (RD j) < S := Nat.blt_eq.mp hn1
        have hn2' : dN2 (RD j) = S := Nat.eq_of_beq_eq_true hn2
        have hS0' : 0 < S := Nat.blt_eq.mp hS0
        have hiw : wInH (RW j) = true := by
          simp only [recOK, sB_eq, andB_iff] at hrec; exact hrec.1
        have hia : wInH (RA j) = true := by
          simp only [recOK, sB_eq, andB_iff] at hrec; exact hrec.2.1
        have hRW : GW (2 ^ 20) (RW j) := ⟨(wInH_spec hiw).1, (wInH_spec hiw).2, (hlen j hj).1⟩
        have hRA : GW (2 ^ 20) (RA j) := ⟨(wInH_spec hia).1, (wInH_spec hia).2, (hlen j hj).2⟩
        let X' := Function.update X S (X (dN1 (RD j)) * val x (RW j) * u * (val x (RA j))⁻¹)
        have hX'lt : ∀ n < S, X' n = X n := fun n hn => Function.update_of_ne (by omega) _ _
        refine ⟨X', by rw [hX'lt 0 hS0', hX0], fun f hf => ?_, fun r hr => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hf | rfl
          · exact recHolds_congr (hH f hf)
              (fun hk3 => ⟨hX'lt _ ((hB f hf).1 hk3).1, hX'lt _ ((hB f hf).1 hk3).2⟩)
              (fun hk5 => by
                by_cases hk3 : dKind (RD f) < 3
                · exact hX'lt _ ((hB f hf).1 hk3).2
                · exact hX'lt _ ((hB f hf).2 (by omega) hk5))
          · refine ⟨hRW, hRA, fun _ => ?_, fun hk3 => absurd hk3 (by omega)⟩
            rw [hX'lt _ hn1', hn2']
            show _ * (Function.update X S _ S * _)⁻¹ ∈ H
            rw [Function.update_self, inv_mul_cancel_right, mul_inv_cancel]
            exact H.one_mem
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
          · exact ⟨fun hk3 => ⟨by have := ((hB r hr).1 hk3).1; omega,
              by have := ((hB r hr).1 hk3).2; omega⟩,
              fun hk3 hk5 => by have := (hB r hr).2 hk3 hk5; omega⟩
          · exact ⟨fun _ => ⟨by omega, by omega⟩, fun hk3 => absurd hk3 (by omega)⟩
      · simp only [andB_iff] at hc
        obtain ⟨hS0, hn, hrec⟩ := hc
        obtain ⟨X, hX0, hH, hB⟩ := ih (by omega) (Nat.blt_eq.mp hS0)
        have hk' : dKind (RD j) ≠ 0 := fun h => hk (beq_t h)
        have hiw : wInH (RW j) = true := by
          simp only [recOK, sB_eq, andB_iff] at hrec; exact hrec.1
        have hia : wInH (RA j) = true := by
          simp only [recOK, sB_eq, andB_iff] at hrec; exact hrec.2.1
        have hRW : GW (2 ^ 20) (RW j) := ⟨(wInH_spec hiw).1, (wInH_spec hiw).2, (hlen j hj).1⟩
        have hRA : GW (2 ^ 20) (RA j) := ⟨(wInH_spec hia).1, (wInH_spec hia).2, (hlen j hj).2⟩
        have hR := rec_spec hxH hx hu hθ hE hone hX0 hH hRW hRA hk' hrec
        refine ⟨X, hX0, fun f hf => ?_, fun r hr => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hf | rfl
          · exact hH f hf
          · exact hR
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
          · exact hB r hr
          · have hk0 : Nat.beq (dKind (RD r)) 0 = false := beq_f hk'
            simp only [nodesOK, sB_eq, brec_eq, hk0, Bool.false_eq_true, ↓reduceIte] at hn
            refine ⟨fun hk3 => ?_, fun hk3 hk5 => ?_⟩
            · have hf : isFact (dKind (RD r)) = true := Nat.blt_eq.mpr hk3
              rw [hf, if_pos rfl, andB_iff] at hn
              exact ⟨Nat.blt_eq.mp hn.1, Nat.blt_eq.mp hn.2⟩
            · have hf : isFact (dKind (RD r)) = false := by
                rw [isFact]; simp only [Nat.blt_eq, Bool.not_eq_true] at *
                exact Bool.eq_false_iff.mpr (by simpa using hk3)
              rw [hf] at hn
              simp only [Bool.false_eq_true, ↓reduceIte] at hn
              exact Nat.blt_eq.mp hn
      · exact absurd hS' (lt_irrefl 0)
  obtain ⟨X, hX0, hH, hB⟩ := inv N le_rfl (hfold ▸ hC)
  rw [hfold] at hB
  refine ⟨X, hX0, fun r hr => ⟨fun hk => ⟨((hB r hr).1 hk).1, ((hB r hr).1 hk).2, ?_⟩,
    fun hk3 hk5 => ⟨(hB r hr).2 hk3 hk5, ?_⟩⟩⟩
  · exact (hH r hr).fact hk
  · exact (hH r hr).stab hk3 hk5

end CFSG.Certificates.TwDce

end
