module

public import CFSG.Certificates.Kernel.Misc.Coset.ActSound

public section

namespace CFSG.KC.MiscCoset.Act

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

theorem movesOK_spec {A : ℕ → ℕ} {L : ℕ} :
    ∀ {us : List (List ℕ)}, movesOK A L us = true → ∀ v ∈ us, walk A L v 0 ≠ 0
  | [], _, v, hv => absurd hv List.not_mem_nil
  | u :: us, h, v, hv => by
    have h' : (notB (fixOK A L u) && movesOK A L us) = true := by
      rw [← andB_eq]
      exact h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hv with rfl | hv
    · intro e
      have : fixOK A L v = true := by
        change Nat.beq _ 0 = true
        rw [Nat.beq_eq]
        exact e
      rw [this] at h'
      exact absurd h'.1 (by decide)
    · exact movesOK_spec h'.2 v hv

theorem stab_sound {m N : ℕ} (ws : List (List (Fin m × Bool))) {rels : List (List ℕ)}
    (hrels : codes ws = rels) {A : ℕ → ℕ} (hN : 0 < N)
    (hpt : ∀ x < N, pointOK A m N rels x = true) (fix move : List (List (Fin m × Bool)))
    {F M : List (List ℕ)} (hF : codes fix = F) (hM : codes move = M)
    (hfix : relsAt A (Nat.add m m) F 0 = true) (hmove : movesOK A (Nat.add m m) M = true) :
    ∃ S : Subgroup (PG m ws),
      (∀ u ∈ fix, PresentedGroup.mk _ (FreeGroup.mk u) ∈ S) ∧
        ∀ u ∈ move, PresentedGroup.mk _ (FreeGroup.mk u) ∉ S := by
  obtain ⟨ψ, hψ⟩ := exists_act ws (fun r hr => hrels ▸ hr) hpt
  set c₀ : {c : ℕ // c < N} := ⟨0, hN⟩ with hc₀
  let S : Subgroup (PG m ws) :=
    { carrier := {g | (ψ g).unop c₀ = c₀}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul, MulOpposite.unop_mul, Equiv.Perm.coe_mul,
          Function.comp_apply] at ha hb ⊢
        rw [ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_inv, MulOpposite.unop_inv] at ha ⊢
        rw [Equiv.Perm.inv_eq_iff_eq, ha] }
  refine ⟨S, fun u hu => ?_, fun u hu hmem => ?_⟩
  · change (ψ (PresentedGroup.mk _ (FreeGroup.mk u))).unop c₀ = c₀
    apply Subtype.ext
    rw [act_mk ψ hψ u c₀]
    exact relsAt_spec hfix _ (hF ▸ List.mem_map_of_mem hu)
  · have h1 : (ψ (PresentedGroup.mk _ (FreeGroup.mk u))).unop c₀ = c₀ := hmem
    have h2 := congrArg Subtype.val h1
    rw [act_mk ψ hψ u c₀] at h2
    exact movesOK_spec hmove _ (hM ▸ List.mem_map_of_mem hu) h2

end CFSG.KC.MiscCoset.Act

end
