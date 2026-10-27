module

public import Certificates.Data.Kernel.GMS78RuSGrp
import CFSG.Certificates.Kernel.GMS78RuSC.Basic
import CFSG.Certificates.Kernel.GMS78RuP.Basic
import CFSG.Certificates.Kernel.GMS78RuS17.Basic

public section

namespace CFSG.KC.GMS.SG

open CFSG.KLie.CT CFSG.KC.Loop

theorem czListEq_eq : ∀ {a b : List Nat}, czListEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [czListEq] at h
  | _ :: _, [], h => by simp [czListEq] at h
  | x :: a, y :: b, h => by
    have h' : andB (Nat.beq x y) (czListEq a b) = true := h
    obtain ⟨h1, h2⟩ := P117.andB_iff.1 h'
    rw [Nat.eq_of_beq_eq_true h1, czListEq_eq h2]

theorem gAnyL_iff (p : Nat → Bool) : ∀ l : List Nat, gAnyL p l = true ↔ ∃ a ∈ l, p a = true
  | [] => by simp [gAnyL]
  | a :: l => by
    have e : gAnyL p (a :: l) = orB (p a) (gAnyL p l) := rfl
    rw [e]
    unfold orB
    cases h : p a <;> simp [h, gAnyL_iff p l]

theorem gMap_eq (f : Nat → Nat) : ∀ L : List Nat, gMap f L = L.map f
  | [] => rfl
  | x :: L => by
    have e : gMap f (x :: L) = f x :: gMap f L := rfl
    rw [e, gMap_eq f L, List.map_cons]

theorem anyN_iff' (f : Nat → Bool) : ∀ n, anyN n f = true ↔ ∃ i < n, f i = true
  | 0 => by simp [anyN]
  | n + 1 => by
    have e : anyN (n + 1) f = orB (f n) (anyN n f) := rfl
    rw [e]
    unfold orB
    cases hf : f n
    · change anyN n f = true ↔ _
      rw [anyN_iff' f n]
      constructor
      · rintro ⟨i, hi, h2⟩
        exact ⟨i, by omega, h2⟩
      · rintro ⟨i, hi, h2⟩
        rcases Nat.lt_or_ge i n with h | h
        · exact ⟨i, h, h2⟩
        · have e2 : i = n := by omega
          rw [e2, hf] at h2
          exact absurd h2 (by decide)
    · exact ⟨fun _ => ⟨n, by omega, hf⟩, fun _ => rfl⟩

theorem kGrp17_sound (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO u0 : Nat)
    (U K : List Nat) (h : kGrp17 GT DPR LIN DM DO u0 U K = true) :
    ∀ l < U.length, kAll17 GT DPR LIN DM DO (U.getD l 0) (K.getD l 0) = true := by
  intro l hl
  unfold kGrp17 at h
  beta_reduce at h
  obtain ⟨hlen, h⟩ := P117.andB_iff.1 h
  obtain ⟨hclo, h⟩ := P117.andB_iff.1 h
  rw [SC.neStrictB_eq] at h
  beta_reduce at h
  have hz := (S17.sZipAll_iff _ U K).1 h l hl
  unfold kGrpOne at hz
  rw [SC.neStrictB_eq, SC.neStrictB_eq] at hz
  beta_reduce at hz
  obtain ⟨hC, hz⟩ := P117.andB_iff.1 hz
  obtain ⟨hN, hz⟩ := P117.andB_iff.1 hz
  obtain ⟨hK, hz⟩ := P117.andB_iff.1 hz
  have hC' := czListEq_eq hC
  unfold kAll17
  rw [SC.neStrictB_eq, SC.neStrictB_eq]
  beta_reduce
  rw [hN, hC']
  dsimp only
  rw [P117.andB_iff, P117.andB_iff]
  refine ⟨hK, hlen, ?_⟩
  unfold sZxR
  beta_reduce
  rw [P117.andB_iff]
  exact ⟨hclo, hz⟩

theorem kGrpAt_sound (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat)
    (I K P : List Nat) (h : kGrpAt GT DPR LIN DM DO I K P = true) :
    ∀ p ∈ P, kAll17 GT DPR LIN DM DO (neGet 0 I p) (neGet 0 K p) = true := by
  intro p hp
  unfold kGrpAt at h
  have hs := kGrp17_sound _ _ _ _ _ _ _ _ h
  rw [gMap_eq, gMap_eq] at hs
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hp
  have hl' : l < (P.map (neGet 0 I)).length := by
    rw [List.length_map]
    exact hl
  have := hs l hl'
  simpa [hl] using this

theorem kAll17H_sound (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat)
    (I K : List Nat) (G : List (List Nat)) (n j : Nat)
    (hG : ∀ g < n, kGrpAt GT DPR LIN DM DO I K (neGet [] G g) = true)
    (h : kAll17H GT DPR LIN DM DO I K G n j = true) :
    kAll17 GT DPR LIN DM DO (neGet 0 I j) (neGet 0 K j) = true := by
  unfold kAll17H at h
  beta_reduce at h
  cases hN : kNeedZ (neGet 0 I j) (neGet 0 K j)
  · rw [hN] at h
    exact h
  · rw [hN] at h
    obtain ⟨g, hg, hgp⟩ := (anyN_iff' _ n).1 h
    obtain ⟨p, hp, hpj⟩ := (gAnyL_iff _ _).1 hgp
    have e := Nat.eq_of_beq_eq_true hpj
    subst e
    exact kGrpAt_sound _ _ _ _ _ _ _ _ (hG g hg) p hp

end CFSG.KC.GMS.SG

end
