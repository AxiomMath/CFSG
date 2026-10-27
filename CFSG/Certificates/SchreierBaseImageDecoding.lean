module

public import CFSG.Certificates.SchreierChainOrderStabilizers

public section

namespace CFSG.Certificates.RawSchreierDatum

variable {n : ℕ} (Q : RawSchreierDatum n)

@[expose] def decodeStep (v : Fin Q.baseCount → Fin n) (i : ℕ) (p : Equiv.Perm (Fin n)) :
    Option (Equiv.Perm (Fin n)) :=
  if h : i < Q.baseCount then
    (Q.transversal? ⟨i, h⟩ (p⁻¹ (v ⟨i, h⟩))).map fun t => p * t
  else none

@[expose] def decodePrefix (v : Fin Q.baseCount → Fin n) : ℕ → Option (Equiv.Perm (Fin n))
  | 0 => some 1
  | i + 1 => (decodePrefix v i).bind (Q.decodeStep v i)

theorem decodePrefix_zero (v : Fin Q.baseCount → Fin n) : Q.decodePrefix v 0 = some 1 :=
  rfl

theorem decodePrefix_succ (v : Fin Q.baseCount → Fin n) (i : ℕ) :
    Q.decodePrefix v (i + 1) = (Q.decodePrefix v i).bind (Q.decodeStep v i) :=
  rfl

variable {Q}

theorem decodePrefix_sound (hQ : ValidSchreier Q) (v : Fin Q.baseCount → Fin n) :
    ∀ i ≤ Q.baseCount, ∀ p, Q.decodePrefix v i = some p →
      p ∈ Q.originalSubgroup ∧ ∀ j : Fin Q.baseCount, j.val < i → p (Q.base.get j) = v j := by
  intro i
  induction i with
  | zero =>
    intro _ p hp
    rw [decodePrefix_zero, Option.some_inj] at hp
    subst hp
    exact ⟨one_mem _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ i ih =>
    intro hi p' hp'
    rw [decodePrefix_succ, Option.bind_eq_some_iff] at hp'
    obtain ⟨p, hp, hstep⟩ := hp'
    have hik : i < Q.baseCount := by omega
    rw [decodeStep] at hstep
    simp only [hik, ↓reduceDIte, Option.map_eq_some_iff] at hstep
    obtain ⟨t, ht, rfl⟩ := hstep
    obtain ⟨hpG, hpv⟩ := ih (by omega) p hp
    obtain ⟨htH, htfix, htb⟩ := Q.transversal_sound ⟨i, hik⟩ _ t ht
    have htG : t ∈ Q.originalSubgroup := by
      rw [← Q.levelSubgroup_zero_eq_original hQ]
      exact Q.levelSubgroup_antitone 0 i (Nat.zero_le _) htH
    refine ⟨mul_mem hpG htG, fun j hj => ?_⟩
    rw [Equiv.Perm.mul_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [Q.levelSubgroup_fixes_base_index i t htH j hj]
      exact hpv j hj
    · have hjeq : j = ⟨i, hik⟩ := Fin.ext hj
      subst hjeq
      rw [htb]
      exact p.apply_symm_apply _

theorem decodePrefix_complete (hQ : ValidSchreier Q) (v : Fin Q.baseCount → Fin n)
    (g : Equiv.Perm (Fin n)) (hg : g ∈ Q.originalSubgroup)
    (hgv : ∀ j, g (Q.base.get j) = v j) :
    ∀ i ≤ Q.baseCount, ∃ p, Q.decodePrefix v i = some p ∧ p⁻¹ * g ∈ Q.levelSubgroup i := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨1, rfl, ?_⟩
    rw [inv_one, one_mul, Q.levelSubgroup_zero_eq_original hQ]
    exact hg
  | succ i ih =>
    intro hi
    have hik : i < Q.baseCount := by omega
    obtain ⟨p, hp, hpg⟩ := ih (by omega)
    set j : Fin Q.baseCount := ⟨i, hik⟩ with hj
    have hx : p⁻¹ (v j) ∈ Q.orbitPoints j := by
      rw [Q.orbitPoints_eq_orbit j]
      refine ⟨⟨p⁻¹ * g, hpg⟩, ?_⟩
      change (p⁻¹ * g) (Q.base.get j) = p⁻¹ (v j)
      rw [Equiv.Perm.mul_apply, hgv]
    obtain ⟨t, ht, htH, -, htb⟩ := Q.orbitPoint_transversal j _ hx
    refine ⟨p * t, ?_, ?_⟩
    · rw [decodePrefix_succ, hp, Option.bind_some, decodeStep]
      simp only [hik, ↓reduceDIte]
      change Option.map _ (Q.transversal? j (p⁻¹ (v j))) = _
      rw [ht]
      rfl
    · change (p * t)⁻¹ * g ∈ Q.levelSubgroup (j.val + 1)
      rw [Q.levelSubgroup_succ_eq_stabilizer hQ j]
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [mul_inv_rev, mul_assoc]
        exact mul_mem (inv_mem htH) hpg
      · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, mul_inv_rev, Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply, hgv, ← htb]
        exact t.symm_apply_apply _

variable (Q)

theorem schreier_base_image_decoding (hQ : ValidSchreier Q) (v : Fin Q.baseCount → Fin n) :
    ((Q.decodePrefix v Q.baseCount).isSome ↔
      ∃ g ∈ Q.originalSubgroup, ∀ i, g (Q.base.get i) = v i) ∧
    (∀ g : Equiv.Perm (Fin n), Q.decodePrefix v Q.baseCount = some g ↔
      g ∈ Q.originalSubgroup ∧ ∀ i, g (Q.base.get i) = v i) ∧
    (∀ g ∈ Q.originalSubgroup, (∀ i, g (Q.base.get i) = v i) →
      ∀ i ≤ Q.baseCount, ∃ p, Q.decodePrefix v i = some p ∧
        p⁻¹ * g ∈ Q.originalSubgroup ∧ ∀ b ∈ Q.base.toList.take i, (p⁻¹ * g) b = b) ∧
    (Q.baseCount = 0 → Q.decodePrefix v 0 = some 1 ∧ Q.originalSubgroup = ⊥) := by
  have hiff : ∀ g : Equiv.Perm (Fin n), Q.decodePrefix v Q.baseCount = some g ↔
      g ∈ Q.originalSubgroup ∧ ∀ i, g (Q.base.get i) = v i := by
    intro g
    constructor
    · intro h
      obtain ⟨hgG, hgv⟩ := decodePrefix_sound hQ v Q.baseCount le_rfl g h
      exact ⟨hgG, fun i => hgv i i.2⟩
    · rintro ⟨hgG, hgv⟩
      obtain ⟨p, hp, hpg⟩ := decodePrefix_complete hQ v g hgG hgv Q.baseCount le_rfl
      rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot, inv_mul_eq_one] at hpg
      rw [hp, hpg]
  refine ⟨?_, hiff, ?_, fun hk => ⟨rfl, ?_⟩⟩
  · constructor
    · intro h
      obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h
      exact ⟨g, (hiff g).1 hg⟩
    · rintro ⟨g, hgG, hgv⟩
      rw [(hiff g).2 ⟨hgG, hgv⟩]
      rfl
  · intro g hg hgv i hi
    obtain ⟨p, hp, hpg⟩ := decodePrefix_complete hQ v g hg hgv i hi
    exact ⟨p, hp, (Q.mem_levelSubgroup_iff hQ i hi _).1 hpg⟩
  · have h0 := Q.levelSubgroup_terminal_eq_bot hQ
    rw [hk, Q.levelSubgroup_zero_eq_original hQ] at h0
    exact h0

end CFSG.Certificates.RawSchreierDatum
