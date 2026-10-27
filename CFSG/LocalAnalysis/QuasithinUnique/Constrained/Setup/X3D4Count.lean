module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3H13Defs

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer

variable {k : Type*} [Field k] {V' : Type*} [AddCommGroup V'] [Module k V'] [Finite V']

theorem card_inf_mul_card_ge {M U U' : Submodule k V'} (hU : U ≤ M) (hU' : U' ≤ M) :
    Nat.card ↥U * Nat.card ↥U' ≤ Nat.card ↥M * Nat.card ↥(U ⊓ U') := by
  have h1 := natCard_sup_mul_natCard_inf U U'
  have h2 : Nat.card ↥(U ⊔ U') ≤ Nat.card ↥M :=
    Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le (sup_le hU hU'))
  calc Nat.card ↥U * Nat.card ↥U' = Nat.card ↥(U ⊔ U') * Nat.card ↥(U ⊓ U') := h1.symm
    _ ≤ Nat.card ↥M * Nat.card ↥(U ⊓ U') := Nat.mul_le_mul_right _ h2

theorem card_le_pow_mul_card_iInf {ι : Type*} {M : Submodule k V'} {q : ℕ} (U : ι → Submodule k V')
    (s : Finset ι) (hUM : ∀ i ∈ s, U i ≤ M) (hq : ∀ i ∈ s, Nat.card ↥M ≤ q * Nat.card ↥(U i)) :
    Nat.card ↥M ≤ q ^ s.card * Nat.card ↥(M ⊓ s.inf U) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have ih' := ih (fun j hj => hUM j (Finset.mem_insert_of_mem hj))
      (fun j hj => hq j (Finset.mem_insert_of_mem hj))
    have hUi := hUM i (Finset.mem_insert_self i s)
    have hqi := hq i (Finset.mem_insert_self i s)
    set T := M ⊓ s.inf U with hT
    have hTM : T ≤ M := inf_le_left
    have hkey := card_inf_mul_card_ge hTM hUi
    have heq : M ⊓ (insert i s).inf U = T ⊓ U i := by
      rw [Finset.inf_insert, hT]
      ext x
      simp only [Submodule.mem_inf]
      constructor
      · rintro ⟨hxM, hxi, hxs⟩
        exact ⟨⟨hxM, hxs⟩, hxi⟩
      · rintro ⟨⟨hxM, hxs⟩, hxi⟩
        exact ⟨hxM, hxi, hxs⟩
    rw [heq, Finset.card_insert_of_notMem hi, pow_succ]
    have hMpos : 0 < Nat.card ↥M := Nat.card_pos
    have h3 : Nat.card ↥T ≤ q * Nat.card ↥(T ⊓ U i) := by
      have : Nat.card ↥T * Nat.card ↥M ≤ (q * Nat.card ↥(T ⊓ U i)) * Nat.card ↥M := by
        calc Nat.card ↥T * Nat.card ↥M ≤ Nat.card ↥T * (q * Nat.card ↥(U i)) :=
              Nat.mul_le_mul_left _ hqi
          _ = q * (Nat.card ↥T * Nat.card ↥(U i)) := by ring
          _ ≤ q * (Nat.card ↥M * Nat.card ↥(T ⊓ U i)) := Nat.mul_le_mul_left _ hkey
          _ = (q * Nat.card ↥(T ⊓ U i)) * Nat.card ↥M := by ring
      exact Nat.le_of_mul_le_mul_right this hMpos
    calc Nat.card ↥M ≤ q ^ s.card * Nat.card ↥T := ih'
      _ ≤ q ^ s.card * (q * Nat.card ↥(T ⊓ U i)) := Nat.mul_le_mul_left _ h3
      _ = q ^ s.card * q * Nat.card ↥(T ⊓ U i) := by ring

variable {X : Type*} [Group X]

omit [Finite V'] in
theorem isInvariant_fixSub {σ : X →* (V' ≃ₗ[k] V')} {L : Subgroup X} :
    Offender.IsInvariant σ L (fixSub σ L) := fun l hl x hx => by
  rw [hx l hl]; exact hx

omit [Finite V'] in
theorem fixSub_sup_eq_bot {σ : X →* (V' ≃ₗ[k] V')} {L : Subgroup X}
    (s : Finset (Submodule k V')) (hind : s.SupIndep id)
    (hs : ∀ U ∈ s, IsNontrivialLSimple σ L U) : s.sup id ⊓ fixSub σ L = ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert U s hU ih =>
    have hind' : s.SupIndep id := hind.subset (Finset.subset_insert U s)
    have hdisj : Disjoint (id U) (s.sup id) :=
      hind (Finset.subset_insert U s) (Finset.mem_insert_self U s) hU
    have ih' := ih hind' (fun V hV => hs V (Finset.mem_insert_of_mem hV))
    have hUs := hs U (Finset.mem_insert_self U s)
    have hsinv : Offender.IsInvariant σ L (s.sup id) :=
      isInvariant_finset_sup s fun W hW => (hs W (Finset.mem_insert_of_mem hW)).1.1
    rw [Finset.sup_insert, eq_bot_iff]
    intro m hm
    obtain ⟨hmsup, hfix⟩ := Submodule.mem_inf.1 hm
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hmsup
    have hfix' : ∀ l ∈ L, σ l (u + v) = u + v := hfix
    have hsplit : ∀ l ∈ L, σ l u = u ∧ σ l v = v := by
      intro l hl
      have h1 := hfix' l hl
      rw [map_add] at h1
      have h2 : σ l u - u = -(σ l v - v) := by
        have : (σ l u - u) + (σ l v - v) = 0 := by
          rw [show (σ l u - u) + (σ l v - v) = (σ l u + σ l v) - (u + v) by abel, h1, sub_self]
        exact eq_neg_of_add_eq_zero_left this
      have hmemU : σ l u - u ∈ id U := U.sub_mem (hUs.1.1 l hl u hu) hu
      have hmemS : -(σ l v - v) ∈ s.sup id := (s.sup id).neg_mem
        ((s.sup id).sub_mem (hsinv l hl v hv) hv)
      rw [← h2] at hmemS
      have h0 : σ l u - u = 0 := by
        have := hdisj.le_bot ⟨hmemU, hmemS⟩
        exact (Submodule.mem_bot k).1 this
      refine ⟨sub_eq_zero.1 h0, ?_⟩
      have : σ l v - v = 0 := by
        rw [h0] at h2
        exact neg_eq_zero.1 h2.symm
      exact sub_eq_zero.1 this
    have hu0 : u = 0 := by
      have hubot : U ⊓ fixSub σ L = ⊥ := by
        rcases hUs.1.2.2 (U ⊓ fixSub σ L) (isInvariant_inf hUs.1.1 isInvariant_fixSub)
          inf_le_left with h | h
        · exact h
        · exact absurd (h ▸ inf_le_right) hUs.2
      have : u ∈ U ⊓ fixSub σ L := ⟨hu, fun l hl => (hsplit l hl).1⟩
      rw [hubot] at this
      exact (Submodule.mem_bot k).1 this
    have hv0 : v = 0 := by
      have : v ∈ s.sup id ⊓ fixSub σ L := ⟨hv, fun l hl => (hsplit l hl).2⟩
      rw [ih'] at this
      exact (Submodule.mem_bot k).1 this
    rw [hu0, hv0, add_zero]
    exact Submodule.zero_mem _

end CFSG.QuasithinUnique.Setup.X3
