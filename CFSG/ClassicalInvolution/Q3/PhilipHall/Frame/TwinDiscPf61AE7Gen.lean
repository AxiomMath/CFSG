module

public import Certificates.Certificate393002
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf61AE7Cent
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Coc

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117
open Certificates.AE7OddGen

namespace TwinDisc

namespace AE5

theorem aeModel7_oddGen_check : oddGenProp :=
  of_decide_eq_true Certificates.certificate393002

section Spec

theorem eqWr_iff {x y : Wr 7} : eqWr x y = true ↔ x = y := by
  unfold eqWr
  rw [List.all_eq_true]
  constructor
  · intro h
    refine Wr.ext (funext fun i => ?_) (Equiv.ext fun i => ?_)
    · have := h i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    · have := h i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
  · rintro rfl i _
    simp

theorem keyV_inj {x y : Wr 7} (h : keyV x = keyV y) : x.vec = y.vec :=
  funext fun i => List.map_inj_left.mp h i (List.mem_finRange i)

theorem keyP_inj {σ τ : Equiv.Perm (Fin 7)} (h : keyP σ = keyP τ) : σ = τ :=
  Equiv.ext fun i => List.map_inj_left.mp h i (List.mem_finRange i)

theorem flagOK_spec {α : Finset (Fin 7)} {p q : Fin 7} (h : flagOK α p q = true) :
    ∃ L : List (Wr 7),
      (∀ b ∈ L, b * ofVec (indL [p, q]) = ofVec (indL [p, q]) * b ∨
        b * ofVec (indF α) = ofVec (indF α) * b) ∧
      (∀ b ∈ L, wsum b = 0 ∧ Equiv.Perm.sign b.perm = 1 ∧ b ^ 15 = 1) ∧
      (∀ j k : Fin 7, j ≠ k → ∃ w ∈ W₁, evalG L w = ofVec (indL [j, k])) ∧
      (∀ a b c : Fin 7, a ≠ b → b ≠ c → a ≠ c →
        ∃ w ∈ W₂, (evalG L w).perm = Equiv.swap a b * Equiv.swap b c) := by
  simp only [flagOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨Lrel (flagFun α p q), ?_, ?_, ?_, ?_⟩
  · intro b hb
    unfold commOK at h1
    rw [List.all_eq_true] at h1
    have := h1 b hb
    simpa only [Bool.or_eq_true, eqWr_iff] using this
  · intro b hb
    unfold aeOK at h2
    rw [List.all_eq_true] at h2
    have := h2 b hb
    simpa only [Bool.and_eq_true, decide_eq_true_eq, eqWr_iff, and_assoc] using this
  · intro j k hjk
    unfold pairsOK at h3
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h3
    rcases h3 j (List.mem_finRange j) k (List.mem_finRange k) with h | h
    · exact absurd h hjk
    · rw [List.contains_iff_mem, List.mem_map] at h
      obtain ⟨w, hw, hwe⟩ := h
      simp only [Prod.mk.injEq] at hwe
      exact ⟨w, hw, Wr.ext (keyV_inj hwe.2) (keyP_inj hwe.1)⟩
  · intro a b c hab hbc hac
    unfold cyclesOK at h4
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h4
    rcases h4 a (List.mem_finRange a) b (List.mem_finRange b) c (List.mem_finRange c) with
      (((h | h) | h) | h)
    · exact absurd h hab
    · exact absurd h hbc
    · exact absurd h hac
    · rw [List.contains_iff_mem, List.mem_map] at h
      obtain ⟨w, hw, hwe⟩ := h
      exact ⟨w, hw, keyP_inj hwe⟩

end Spec

theorem evalG_mem {G : Type*} [Group G] (H : Subgroup G) (gens : List G)
    (hg : ∀ g ∈ gens, g ∈ H) (w : List ℕ) : evalG gens w ∈ H := by
  unfold evalG
  suffices ∀ acc : G, acc ∈ H → w.foldl (fun acc k =>
      acc * if k % 2 = 0 then gens.getD (k / 2) 1 else (gens.getD (k / 2) 1)⁻¹) acc ∈ H from
    this 1 H.one_mem
  induction w with
  | nil => exact fun acc h => h
  | cons k w ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    refine ih _ (H.mul_mem hacc ?_)
    have hget : gens.getD (k / 2) 1 ∈ H := by
      by_cases hlt : k / 2 < gens.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact hg _ (List.getElem_mem hlt)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        exact H.one_mem
    split_ifs
    · exact hget
    · exact H.inv_mem hget

theorem aeModel_le_of_pairVec_threeCycles {n : ℕ} {H : Subgroup (AEQ n)} (hHM : H ≤ TL4.aeModel n)
    (hvec : ∀ j k : Fin n, j ≠ k → TL4.vbar n (TL4.pairVec j k) ∈ H)
    (hperm : ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
      ∃ h ∈ H, TL4.Mdl117.permQ n h = Equiv.swap a b * Equiv.swap b c) :
    TL4.aeModel n ≤ H := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hσ : w.perm ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.mpr hw.2
  have hK : alternatingGroup (Fin n) ≤ H.map (TL4.Mdl117.permQ n) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ3
    obtain ⟨a, b, c, hab, hbc, hac, rfl⟩ := TL4.Mdl117.exists_swap_of_isThreeCycle hσ3
    obtain ⟨h, hh, hp⟩ := hperm a b c hab hbc hac
    exact ⟨h, hh, hp⟩
  obtain ⟨h, hh, hph⟩ := hK hσ
  have hy : mkQ n w * h⁻¹ ∈ TL4.aeModel n :=
    (TL4.aeModel n).mul_mem ⟨w, hw, rfl⟩ ((TL4.aeModel n).inv_mem (hHM hh))
  have hyp : TL4.Mdl117.permQ n (mkQ n w * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hph, TL4.Mdl117.permQ_mkQ, mul_inv_cancel]
  obtain ⟨v, hv, hyv⟩ := TL4.Mdl117.exists_vec_of_permQ_eq_one hy hyp
  have hvH : mkQ n (ofVec v) ∈ H := TL4.mem_of_pairVec hvec hv
  have hx : mkQ n w = mkQ n (ofVec v) * h := by
    rw [← hyv]
    group
  rw [hx]
  exact H.mul_mem hvH hh

@[expose] def oddCent7 (α : Finset (Fin 7)) (hα : α.card = 4) (p q : Fin 7) : Set (AEQ 7) :=
  {b | b ∈ TL4.aeModel 7 ∧ Odd (orderOf b) ∧
    (b * TL4.vbar 7 (TL4.pairVec p q) = TL4.vbar 7 (TL4.pairVec p q) * b ∨
      b * zBar α hα = zBar α hα * b)}

theorem indL_pair {j k : Fin 7} (hjk : j ≠ k) :
    (indL [j, k] : Fin 7 → ZMod 2) = TL4.pairVec j k := by
  funext i
  rw [pairVec_apply hjk]
  simp [indL]

theorem closure_oddCent7 {α : Finset (Fin 7)} (hα : α.card = 4)
    {p q : Fin 7} (hpq : p ≠ q) (hpα : p ∉ α) (hqα : q ∉ α) :
    Subgroup.closure (oddCent7 α hα p q) = TL4.aeModel 7 := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun b hb => hb.1) ?_
  have hflag := aeModel7_oddGen_check α (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hα⟩)
    p q hpα hqα hpq
  obtain ⟨L, hcomm, hae, hpairs, hcycles⟩ := flagOK_spec hflag
  have hzvec : mkQ 7 (ofVec (indF α)) = zBar α hα := by
    rw [zBar, TL4.Mdl117.zOf_emb_eq]
  have hgvec : mkQ 7 (ofVec (indL [p, q])) = TL4.vbar 7 (TL4.pairVec p q) := by
    rw [indL_pair hpq]
    rfl
  have hL : ∀ b ∈ L, mkQ 7 b ∈ oddCent7 α hα p q := by
    intro b hb
    obtain ⟨hs, hsg, h15⟩ := hae b hb
    refine ⟨⟨b, ⟨hs, hsg⟩, rfl⟩, ?_, ?_⟩
    · have : orderOf (mkQ 7 b) ∣ 15 :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h15, map_one])
      exact Odd.of_dvd_nat (by decide) this
    · rcases hcomm b hb with h | h
      · left
        have := congrArg (mkQ 7) h
        rwa [map_mul, map_mul, hgvec] at this
      · right
        have := congrArg (mkQ 7) h
        rwa [map_mul, map_mul, hzvec] at this
  set H := Subgroup.closure (oddCent7 α hα p q) with hH
  have hLH : ∀ g ∈ L.map (mkQ 7), g ∈ H := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure (hL b hb)
  have hword : ∀ w, mkQ 7 (evalG L w) ∈ H := fun w => by
    rw [TL4.Mdl117.evalG_map (mkQ 7) L w]
    exact evalG_mem H _ hLH w
  have hHM : H ≤ TL4.aeModel 7 := (Subgroup.closure_le _).mpr fun b hb => hb.1
  refine aeModel_le_of_pairVec_threeCycles hHM (fun j k hjk => ?_) (fun a b c hab hbc hac => ?_)
  · obtain ⟨w, -, hw⟩ := hpairs j k hjk
    have := hword w
    rwa [hw, indL_pair hjk] at this
  · obtain ⟨w, -, hw⟩ := hcycles a b c hab hbc hac
    exact ⟨mkQ 7 (evalG L w), hword w, by rw [TL4.Mdl117.permQ_mkQ, hw]⟩

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
