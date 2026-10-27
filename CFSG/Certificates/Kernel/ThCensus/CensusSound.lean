module

public import CFSG.Certificates.Kernel.ThCensus.WordSound
public import Mathlib.GroupTheory.OrderOfElement
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.ThCensus.Sound

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThCensus

theorem exists_getD_of_mem {α : Type*} {l : List α} {a d : α} (h : a ∈ l) :
    ∃ k < l.length, l.getD k d = a := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨k, hk, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]⟩

theorem getD_mem {α : Type*} {l : List α} {k : ℕ} (d : α) (hk : k < l.length) : l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

theorem anyL_spec {α : Type} (p : α → Bool) : ∀ l : List α, anyL p l = true → ∃ a ∈ l, p a = true
  | [], h => absurd h Bool.false_ne_true
  | a :: l, h => by
    rcases Dce.orB_iff.1 h with h | h
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨b, hb, hpb⟩ := anyL_spec p l h
      exact ⟨b, List.mem_cons_of_mem _ hb, hpb⟩

theorem fusIdxOK_spec {nr nt : ℕ} : ∀ F : List (List ℕ), fusIdxOK nr nt F = true →
    ∀ e ∈ F, e.getD 0 0 < nr ∧ e.getD 1 0 < nt
  | [], _, e, he => absurd he List.not_mem_nil
  | x :: F, h, e, he => by
    obtain ⟨h1, h2⟩ := Dce.andB_iff.1 h
    rcases List.mem_cons.1 he with rfl | he
    · obtain ⟨-, h3⟩ := Dce.andB_iff.1 h1
      obtain ⟨h4, h5⟩ := Dce.andB_iff.1 h3
      exact ⟨Nat.blt_eq.mp h4, Nat.blt_eq.mp h5⟩
    · exact fusIdxOK_spec F h2 e he

section Census

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {G : Type*} [Group G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)}

theorem ord3_spec (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hφ : Function.Injective φ) {RB : ℕ → ℕ} {r : ℕ} {X : G} (hX : φ X = pkMat (RB r))
    (h : ord3OK RB c rm ONE r = true) : orderOf X = 3 := by
  obtain ⟨h1, h2⟩ := Dce.andB_iff.1 h
  have hne : Nat.beq (mulB c rm (RB r) ONE) ONE = false := by
    cases hb : Nat.beq (mulB c rm (RB r) ONE) ONE
    · rfl
    · rw [hb] at h2
      exact absurd h2 Bool.false_ne_true
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  refine orderOf_eq_prime ?_ ?_
  · apply hφ
    have e := congrArg pkMat (Nat.eq_of_beq_eq_true h1)
    rw [pkMat_mulB hk, pkMat_mulB hk, ← hX, pkMat_one hk, ← map_mul, ← map_mul, ← pow_three'] at e
    rw [e, map_one]
  · intro hX1
    have e : mulB c rm (RB r) ONE = ONE := by
      refine pkMat_inj (inLayout_mulB hk _ _) (inLayout_one hk) ?_
      rw [pkMat_mulB hk, ← hX, hX1, map_one, pkMat_one hk, Matrix.mul_one]
    rw [e, Nat.beq_refl] at hne
    exact Bool.noConfusion hne

variable (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
  (hφ : Function.Injective φ) {g : ℕ → G} {RB PW : ℕ → ℕ}
  (hpw : ∀ k < 10, ∀ e, 1 ≤ e → e < 3 → pkMat (PW (k * (3 - 1) + e - 1)) = φ (g k ^ e))
  {Z S U : G} {rz rs ru : ℕ} (hZ : φ Z = pkMat (RB rz)) (hS : φ S = pkMat (RB rs))
  (hU : φ U = pkMat (RB ru))
include hk hφ hpw hZ hS hU

theorem tgt_conj {rb nt : ℕ} {tgts cen : List (List ℕ)} {WC : ℕ → ℕ}
    (hA : ∃ u : G, φ u = pkMat (RB 1)) (hB : ∃ u : G, φ u = pkMat (RB 2))
    (hb2 : ∃ u : G, φ u = pkMat (RB rb)) (hnt : nt ≤ tgts.length) (htgts : nfsOK tgts = true)
    (hcen : ∀ j < nt, cenOK RB PW c rm ONE rb rz rs ru (tgts.getD j []) (cen.getD j []) (WC j) =
      true)
    (hlet : ∀ j < nt, wordLetOK 3 ((cen.getD j []).getD 1 0) (WC j) = true) :
    ∀ j < nt, ∃ k C : G, (C = Z ∨ C = Z ^ 2 ∨ C = S ∨ C = S ^ 2 ∨ C = U ∨ C = U ^ 2) ∧
      k * C * k⁻¹ = nfFrom g 10 0 (permNfNum (tgts.getD j [])) := by
  intro j hj
  obtain ⟨h1, h2⟩ := Dce.andB_iff.1 (hcen j hj)
  obtain ⟨C, hC, hCm⟩ := clsM_spec hk hZ hS hU (k := (cen.getD j []).getD 0 0) (Nat.blt_eq.mp h1)
  have hl : ∀ x < 3, x < 4 → ∃ u : G, φ u = pkMat (RB (letR 1 2 rb 0 x)) := by
    intro x hx _
    rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2) with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hb2
  obtain ⟨W, hW⟩ := wordR_spec hk hl _ _ ONE (hlet j hj) 1 (by rw [pkMat_one hk, map_one])
  have hT := nfM_spec hk hpw (nfsOK_spec tgts htgts _ (getD_mem [] (by omega : j < tgts.length)))
  have e := conj_of_conjEq hk hφ hT hCm hW h2
  refine ⟨W⁻¹, C, hC, ?_⟩
  rw [inv_inv, mul_assoc, ← e]
  group

theorem rep_conj {rb r2 r3 nr nt : ℕ} {reps tgts cen fus : List (List ℕ)} {WC WF : ℕ → ℕ}
    (hA : ∃ u : G, φ u = pkMat (RB 1)) (hB : ∃ u : G, φ u = pkMat (RB 2))
    (hb2 : ∃ u : G, φ u = pkMat (RB rb)) (hx1 : ∃ u : G, φ u = pkMat (RB r2))
    (hx2 : ∃ u : G, φ u = pkMat (RB r3)) (hnt : tgts.length = nt) (hnr : nr ≤ reps.length)
    (hreps : nfsOK reps = true) (htgts : nfsOK tgts = true)
    (hcen : ∀ j < nt, cenOK RB PW c rm ONE rb rz rs ru (tgts.getD j []) (cen.getD j []) (WC j) =
      true)
    (hlet : ∀ j < nt, wordLetOK 3 ((cen.getD j []).getD 1 0) (WC j) = true)
    (hfus : ∀ k < fus.length, fusOK RB PW c rm ONE r2 r3 reps tgts (fus.getD k []) (WF k) = true)
    (hfi : fusIdxOK nr nt fus = true) (hcov : coverOK reps tgts fus nr = true) :
    ∀ m < nr, ∃ k C : G, (C = Z ∨ C = Z ^ 2 ∨ C = S ∨ C = S ^ 2 ∨ C = U ∨ C = U ^ 2) ∧
      k * C * k⁻¹ = nfFrom g 10 0 (permNfNum (reps.getD m [])) := by
  have htc := tgt_conj hk hφ hpw hZ hS hU hA hB hb2 hnt.ge htgts hcen hlet
  intro m hm
  have hR := nfM_spec hk hpw (g := g) (nfsOK_spec reps hreps _ (getD_mem [] (by omega : m < reps.length)))
  have hc := (Dce.allB_iff _ nr).1 hcov m hm
  rcases Dce.orB_iff.1 hc with hc | hc
  · obtain ⟨e, he, hem⟩ := anyL_spec _ fus hc
    have hem' : e.getD 0 0 = m := Nat.eq_of_beq_eq_true hem
    obtain ⟨kf, hkf, rfl⟩ := exists_getD_of_mem (d := []) he
    obtain ⟨-, hj⟩ := fusIdxOK_spec fus hfi _ he
    have hf := hfus kf hkf
    have hl : ∀ x < 4, x < 4 → ∃ u : G, φ u = pkMat (RB (letR 1 2 r2 r3 x)) := by
      intro x hx _
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl
      · exact hA
      · exact hB
      · exact hx1
      · exact hx2
    obtain ⟨W, hW⟩ := wordR_spec hk hl _ _ ONE (wordLetOK_four _ _) 1
      (by rw [pkMat_one hk, map_one])
    have hT := nfM_spec hk hpw (g := g)
      (nfsOK_spec tgts htgts _ (getD_mem [] (by omega : (fus.getD kf []).getD 1 0 < tgts.length)))
    have hR' := nfM_spec hk hpw (g := g) (nfsOK_spec reps hreps _
      (getD_mem [] (by omega : (fus.getD kf []).getD 0 0 < reps.length)))
    have e := conj_of_conjEq hk hφ hR' hT hW hf
    obtain ⟨k, C, hC, hkC⟩ := htc _ hj
    refine ⟨W⁻¹ * k, C, hC, ?_⟩
    rw [← hem']
    have e2 : nfFrom g 10 0 (permNfNum (reps.getD ((fus.getD kf []).getD 0 0) [])) =
        W⁻¹ * nfFrom g 10 0 (permNfNum (tgts.getD ((fus.getD kf []).getD 1 0) [])) * W := by
      rw [mul_assoc, ← e]
      group
    rw [e2, ← hkC]
    group
  · obtain ⟨t, ht, hte⟩ := anyL_spec _ tgts hc
    obtain ⟨j, hj, rfl⟩ := exists_getD_of_mem (d := []) ht
    have hT := nfM_spec hk hpw (g := g) (nfsOK_spec tgts htgts _ ht)
    have heq : nfM PW c rm ONE (tgts.getD j []) = nfM PW c rm ONE (reps.getD m []) := by
      unfold nfM
      rw [Nat.eq_of_beq_eq_true hte]
    have e : nfFrom g 10 0 (permNfNum (tgts.getD j [])) =
        nfFrom g 10 0 (permNfNum (reps.getD m [])) := by
      apply hφ
      rw [← hT, ← hR, heq]
    rw [← e]
    exact htc j (by omega)

omit hk hφ hpw hZ hS hU in
theorem census_of_reps {Q : Subgroup G} {R : ℕ → G} {nr : ℕ}
    (hQ : ∀ x ∈ Q, x ^ 3 = 1 → x = 1 ∨ ∃ m < nr, ∃ c ∈ Q, c * x * c⁻¹ = R m)
    (hR : ∀ m < nr, ∃ k C : G, (C = Z ∨ C = Z ^ 2 ∨ C = S ∨ C = S ^ 2 ∨ C = U ∨ C = U ^ 2) ∧
      k * C * k⁻¹ = R m) {x : G} (hx : x ∈ Q) (ho : orderOf x = 3) :
    ∃ k C : G, (C = Z ∨ C = Z ^ 2 ∨ C = S ∨ C = S ^ 2 ∨ C = U ∨ C = U ^ 2) ∧ k * C * k⁻¹ = x := by
  rcases hQ x hx (by rw [← ho]; exact pow_orderOf_eq_one x) with h1 | ⟨m, hm, c, -, hc⟩
  · rw [h1, orderOf_one] at ho
    exact absurd ho (by norm_num)
  · obtain ⟨k, C, hC, hkC⟩ := hR m hm
    refine ⟨c⁻¹ * k, C, hC, ?_⟩
    have e : x = c⁻¹ * R m * c := by
      rw [← hc]
      group
    rw [e, ← hkC]
    group

end Census

end CFSG.KC.ThCensus.Sound

end
