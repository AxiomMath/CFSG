module

public import Certificates.Data.Kernel.OrbRow.CentL
public import CFSG.Certificates.Kernel.OrbRow.PRepFacts
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover
public import CFSG.Certificates.Kernel.OrbRow.WordRep
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw.Orb
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW)

theorem bRec_cases {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem movLvK_sound {w m : ℕ} {S : List ℕ} {k lv lo : ℕ} :
    ∀ {F : List ℕ}, movLvK w m S k lv lo F = true → ∀ p ∈ F, lo ≤ p →
      ∃ j, lvOk k lv j ∧ pg w m (getS S j) p ≠ p
  | [], _, p, hp, _ => absurd hp List.not_mem_nil
  | q :: F, h, p, hp, hlo => by
    have h' : Bool.rec (motive := fun _ => Bool) false (movLvK w m S k lv lo F)
        (bIf(Nat.blt q lo, true,
          bIf(allN k (fun j => bIf(Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1),
            Nat.beq (pg w m (getS S j) q) q, true)), false, true))) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 hp with rfl | hp
    · rcases bRec_cases h1 with ⟨hb, -⟩ | ⟨-, h3⟩
      · have := Nat.le_of_ble_eq_true hb
        omega
      · rcases bRec_cases h3 with ⟨-, h4⟩ | ⟨ha, -⟩
        · exact absurd h4 Bool.false_ne_true
        · have : ¬ ∀ j < k, (bIf(Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1),
              Nat.beq (pg w m (getS S j) p) p, true)) = true := fun hall => by
            rw [allN_iff.2 hall] at ha
            exact Bool.false_ne_true ha.symm
          push_neg at this
          obtain ⟨j, hj, hf⟩ := this
          rcases hc : Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) with _ | _
          · rw [hc] at hf
            exact absurd rfl hf
          · rw [hc] at hf
            refine ⟨j, lvOk_iff.2 ⟨hj, testBit_iff_fld.1 hc⟩, fun he => hf ?_⟩
            rw [he]
            exact Nat.beq_refl p
    · exact movLvK_sound h2 p hp hlo

theorem relK_sound {n w : ℕ} {S : List ℕ} {o : ℕ → ℕ} :
    ∀ {ws : List (List (ℕ × Bool))}, relK n w S o ws = true →
      ∀ wd ∈ ws, posWordK n w (getS S) (invPow o wd) = pidn n w
  | [], _, wd, hwd => absurd hwd List.not_mem_nil
  | v :: ws, h, wd, hwd => by
    have h' : Bool.rec (motive := fun _ => Bool) false (relK n w S o ws)
        (Nat.beq (posWordK n w (getS S) (invPow o v)) (pidn n w)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 hwd with rfl | hwd
    · exact Nat.eq_of_beq_eq_true h1
    · exact relK_sound h2 wd hwd

theorem invPow_cons (o : ℕ → ℕ) (a : ℕ) (b : Bool) (wd : List (ℕ × Bool)) :
    invPow o ((a, b) :: wd) = cond b (a :: invPow o wd)
      (List.replicate (o a - 1) a ++ invPow o wd) := by
  cases b <;> rfl

theorem mem_invPow (o : ℕ → ℕ) {l : ℕ} : ∀ {wd : List (ℕ × Bool)}, l ∈ invPow o wd →
    ∃ x ∈ wd, x.1 = l
  | [], h => absurd h List.not_mem_nil
  | (a, b) :: wd, h => by
    rw [invPow_cons] at h
    cases b
    · rcases List.mem_append.1 h with h | h
      · exact ⟨(a, false), List.mem_cons_self, (List.eq_of_mem_replicate h).symm⟩
      · obtain ⟨x, hx, e⟩ := mem_invPow o h
        exact ⟨x, List.mem_cons_of_mem _ hx, e⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨(l, true), List.mem_cons_self, rfl⟩
      · obtain ⟨x, hx, e⟩ := mem_invPow o h
        exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

theorem invPow_prod {G : Type*} [Group G] {m : ℕ} (g : Fin m → G) (σ : ℕ → G)
    (hσ : ∀ i : Fin m, σ i.val = g i) (o : ℕ → ℕ) :
    ∀ wd : List (Fin m × Bool), (∀ l ∈ wd, l.2 = false → g l.1 ^ (o l.1.val - 1) = (g l.1)⁻¹) →
      ((invPow o (wd.map fun l => (l.1.val, l.2))).map σ).prod = evalW g wd
  | [], _ => rfl
  | (a, b) :: wd, h => by
    have ih := invPow_prod g σ hσ o wd fun l hl => h l (List.mem_cons_of_mem _ hl)
    have e : evalW g ((a, b) :: wd) = cond b (g a) (g a)⁻¹ * evalW g wd := by
      unfold evalW
      rw [List.map_cons, List.prod_cons]
    rw [List.map_cons, invPow_cons, e, ← ih]
    cases b
    · change ((List.replicate (o a.val - 1) a.val ++ _).map σ).prod = _
      rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, hσ,
        h (a, false) List.mem_cons_self rfl]
      rfl
    · change ((a.val :: _).map σ).prod = _
      rw [List.map_cons, List.prod_cons, hσ]
      rfl

end CFSG.KC.OrbRow

end
