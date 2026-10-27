module

public import Certificates.Data.Kernel.Co2X9
public import CFSG.Certificates.Kernel.Co2Syl.Sound

public section

namespace CFSG.KC.Co2X9

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.TabMatGrp

theorem orK_eq (a b : Bool) : orK a b = (a || b) := by cases a <;> rfl

variable {CF G W : Nat → Nat} {N D : Nat}

theorem blkX_spec {b : Nat} (h : blkX CF G D W N b = true) :
    ∀ i < 64, 64 * b + i < N →
      recT CF G N (64 * b + i) = true ∧ cenK CF G D W (64 * b + i) = true := by
  intro i hi hN
  have := recAll (p := fun i => implK (Nat.blt (Nat.add (Nat.mul 64 b) i) N)
    (andK (recT CF G N (Nat.add (Nat.mul 64 b) i)) (cenK CF G D W (Nat.add (Nat.mul 64 b) i))))
    64 h i hi
  have hb : Nat.blt (Nat.add (Nat.mul 64 b) i) N = true := blt_iff.2 hN
  rw [implK_eq, hb, if_pos rfl, andK_eq, Bool.and_eq_true] at this
  exact this

theorem blkX_ok {nb : Nat} (hN : N ≤ 64 * nb) (h : ∀ b < nb, blkX CF G D W N b = true) :
    ∀ k < N, recT CF G N k = true ∧ cenK CF G D W k = true := by
  intro k hk
  have := blkX_spec (h (k / 64) (by omega)) (k % 64) (Nat.mod_lt _ (by norm_num)) (by omega)
  rwa [Nat.div_add_mod] at this

theorem treeRecs_of {nb : Nat} (hN : N ≤ 64 * nb) (h : ∀ b < nb, blkX CF G D W N b = true)
    (h0 : elemAt CF 0 = IDP) (h1 : mOf (recAt CF 0) = 1) (hs : N < BAD) : TreeRecs CF G N :=
  ⟨fun k hk => (blkX_ok hN h k hk).1, h0, h1, hs⟩

theorem cenK_spec {k : Nat} (h : cenK CF G D W k = true) :
    mulV (elemAt CF k) (elemAt CF k) = IDP ∨ mulV (elemAt CF k) (elemAt CF k) = D ∨
      (W k < 5 ∧ mulV (G (W k)) (mulV (elemAt CF k) (elemAt CF k)) ≠
        mulV (mulV (elemAt CF k) (elemAt CF k)) (G (W k))) := by
  unfold cenK commK at h
  simp only [letB_eq, orK_eq, andK_eq, notK_eq, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  rcases h with h | h | ⟨h1, h2⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h))
  · exact Or.inr (Or.inr ⟨blt_iff.1 h1, Nat.ne_of_beq_eq_false h2⟩)

theorem cen_sound (hR : TreeRecs CF G N) (hc : Nat.card (genMon G) ≤ N)
    (hC : ∀ k < N, cenK CF G D W k = true) :
    ∀ y ∈ genMon G, (∀ x ∈ genMon G, x * (y * y) = y * y * x) →
      y * y = 1 ∨ y * y = MatP 22 D := by
  intro y hy hz
  obtain ⟨k, hk, rfl⟩ := tree_surj hR hc y hy
  rw [← MatP_mulV]
  rcases cenK_spec (hC k hk) with e | e | ⟨hw, hne⟩
  · exact Or.inl (by rw [e, MatP_IDP])
  · exact Or.inr (by rw [e])
  · refine absurd (MatP_inj' (mulV_lt _ _) (mulV_lt _ _) ?_) hne
    simp only [MatP_mulV]
    exact hz _ (gen_mem G hw)

theorem sqW_sound (hR : TreeRecs CF G N) {k : Nat} (h : sqWK CF N D k = true) :
    ∃ y ∈ genMon G, y * y = MatP 22 D := by
  unfold sqWK at h
  rw [andK_eq, Bool.and_eq_true] at h
  exact ⟨_, tree_mem hR k (blt_iff.1 h.1), by rw [← MatP_mulV, Nat.eq_of_beq_eq_true h.2]⟩

theorem conjK_sound {F A B : Nat} (h : conjK F A B = true) :
    MatP 22 F * MatP 22 A = MatP 22 B * MatP 22 F := by
  rw [← MatP_mulV, ← MatP_mulV, Nat.eq_of_beq_eq_true h]

theorem neK_sound (hD : D < 2 ^ 484) (h : neK D = true) : MatP 22 D ≠ 1 := by
  intro e
  rw [← MatP_IDP] at e
  have e' := MatP_inj' hD IDP_lt e
  unfold neK at h
  simp [notK_eq, e', Nat.beq_refl] at h

end CFSG.KC.Co2X9

end
