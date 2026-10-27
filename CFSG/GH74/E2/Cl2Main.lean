module

public import CFSG.GH74.E2.Cl2Final

public section

namespace CFSG.GH74.E2

open Subgroup

universe u

section Aux

variable {Q : Type*} [Group Q]

theorem aux_map_dsub (g : MulAut Q) : (dsub Q).map g.toMonoidHom = dsub Q := by
  rw [dsub, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ g.surjective]

theorem aux_map_gamma3 (g : MulAut Q) :
    (⁅dsub Q, (⊤ : Subgroup Q)⁆).map g.toMonoidHom = ⁅dsub Q, (⊤ : Subgroup Q)⁆ := by
  rw [Subgroup.map_commutator, aux_map_dsub, Subgroup.map_top_of_surjective _ g.surjective]

theorem aux_mem_gamma3 (g : MulAut Q) {x : Q} (hx : x ∈ (⁅dsub Q, (⊤ : Subgroup Q)⁆)) :
    g x ∈ (⁅dsub Q, (⊤ : Subgroup Q)⁆) := by
  have : g x ∈ (⁅dsub Q, (⊤ : Subgroup Q)⁆).map g.toMonoidHom := ⟨x, hx, rfl⟩
  rwa [aux_map_gamma3] at this

theorem aux_mem_center (g : MulAut Q) {x : Q} (hx : x ∈ center Q) : g x ∈ center Q := by
  have h1 : (center Q).map g.toMonoidHom = center Q := Subgroup.map_center_eq g
  have : g x ∈ (center Q).map g.toMonoidHom := ⟨x, hx, rfl⟩
  rwa [h1] at this

theorem aux_inv_iff {g : MulAut Q} (hg : g ^ 3 = 1) {M : Subgroup Q} (hM : ∀ x ∈ M, g x ∈ M)
    (x : Q) : g x ∈ M ↔ x ∈ M := by
  refine ⟨fun h => ?_, hM x⟩
  have h3 : ∀ y, g (g (g y)) = y := fun y => by
    have := congrArg (fun f : MulAut Q => f y) hg
    simpa [pow_succ, MulAut.mul_apply] using this
  have := hM _ (hM _ h)
  rwa [h3] at this

end Aux

section Main

theorem aux_cl2_core : ∀ (n : ℕ) (Q : Type u) [Group Q] [Finite Q], Nat.card Q = n →
    IsPGroup 2 Q → FourGen Q → ∀ {a b : MulAut Q}, BPair Q a b →
      ⁅dsub Q, (⊤ : Subgroup Q)⁆ = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q _ _ hn hQ h4 a b h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_contra hne
    set γ : Subgroup Q := ⁅dsub Q, (⊤ : Subgroup Q)⁆ with hγ
    have hγa : ∀ x ∈ γ, a x ∈ γ := fun x hx => aux_mem_gamma3 a hx
    have hγb : ∀ x ∈ γ, b x ∈ γ := fun x hx => aux_mem_gamma3 b hx
    have hγd : γ ≤ dsub Q := Subgroup.commutator_le_left (dsub Q) ⊤
    have hnil : Group.IsNilpotent Q := hQ.isNilpotent
    have hγn : γ.Normal := inferInstanceAs (⁅dsub Q, (⊤ : Subgroup Q)⁆).Normal
    let S : Set (Subgroup Q) := {M | ⊥ < M ∧ M ≤ γ ⊓ center Q ∧ (∀ x ∈ M, a x ∈ M) ∧
      (∀ x ∈ M, b x ∈ M)}
    have hM0 : γ ⊓ center Q ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    have hSne : S.Nonempty := ⟨γ ⊓ center Q, bot_lt_iff_ne_bot.2 hM0, le_rfl,
      fun x hx => ⟨hγa x hx.1, aux_mem_center a hx.2⟩,
      fun x hx => ⟨hγb x hx.1, aux_mem_center b hx.2⟩⟩
    obtain ⟨R, hRS, hRmin⟩ := wellFounded_lt.has_min S hSne
    obtain ⟨hRbot, hRle, hRa, hRb⟩ := hRS
    have hRmin' : ∀ M ∈ S, M ≤ R → M = R := fun M hM hMR => by
      by_contra hMR'
      exact hRmin M hM (lt_of_le_of_ne hMR hMR')
    have hRc : R ≤ center Q := hRle.trans inf_le_right
    have hRγ : R ≤ γ := hRle.trans inf_le_left
    have hRn : R.Normal := ⟨fun x hx g => by
      have h1 := Subgroup.mem_center_iff.1 (hRc hx) g
      have h2 : g * x * g⁻¹ = x := by
        calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h1]
          _ = x := by group
      rw [h2]
      exact hx⟩
    have hRf : R ≤ frattini Q := hRγ.trans (hγd.trans (dsub_le_frattini hQ))
    have hRa' : ∀ x, a x ∈ R ↔ x ∈ R := aux_inv_iff h.a_cube hRa
    have hRb' : ∀ x, b x ∈ R ↔ x ∈ R := aux_inv_iff h.b_cube hRb
    have hRne : R ≠ ⊥ := ne_of_gt hRbot
    have hcard : Nat.card (Q ⧸ R) < n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R
      have h2 : 1 < Nat.card R := by
        have := Nat.card_pos (α := R)
        by_contra hle
        exact hRne (Subgroup.card_eq_one.1 (by omega))
      have h3 := Nat.card_pos (α := Q ⧸ R)
      rw [← hn, h1]
      nlinarith
    have hbar := ih _ hcard (Q ⧸ R) rfl (hQ.to_quotient R) (FourGen.quotient h4 R)
      (h.quotient hQ R hRa' hRb' hRf)
    have hγR : γ ≤ R := by
      have hmap : γ.map (QuotientGroup.mk' R) = ⁅dsub (Q ⧸ R), (⊤ : Subgroup (Q ⧸ R))⁆ := by
        rw [hγ, Subgroup.map_commutator, dsub, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)]
      rw [hbar] at hmap
      intro x hx
      have : QuotientGroup.mk' R x ∈ γ.map (QuotientGroup.mk' R) := ⟨x, hx, rfl⟩
      rw [hmap, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    have hRγ' : R = γ := le_antisymm hRγ hγR
    have hRelem : ∀ n ∈ R, n * n = 1 := by
      let E : Subgroup Q :=
        { carrier := {x | x ∈ R ∧ x * x = 1}
          mul_mem' := fun {x y} hx hy => by
            refine ⟨R.mul_mem hx.1 hy.1, ?_⟩
            have hxy : x * y = y * x := (Subgroup.mem_center_iff.1 (hRc hy.1) x)
            calc x * y * (x * y) = x * (y * x) * y := by group
              _ = x * (x * y) * y := by rw [← hxy]
              _ = (x * x) * (y * y) := by group
              _ = 1 := by rw [hx.2, hy.2, mul_one]
          one_mem' := ⟨R.one_mem, mul_one 1⟩
          inv_mem' := fun {x} hx => by
            refine ⟨R.inv_mem hx.1, ?_⟩
            have hxx : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
            rw [hxx, hx.2, inv_one] }
      have hEle : E ≤ R := fun x hx => hx.1
      have hEne : ⊥ < E := by
        have h2 : 2 ∣ Nat.card R := by
          obtain ⟨k, hk⟩ := (hQ.to_subgroup R).exists_card_eq
          rcases k with _ | k
          · exfalso
            exact hRne (Subgroup.card_eq_one.1 (by simpa using hk))
          · exact ⟨2 ^ k, by rw [hk]; ring⟩
        obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
        refine lt_of_le_of_ne bot_le (fun hbot => ?_)
        have hgE : (g : Q) ∈ E := by
          refine ⟨g.2, ?_⟩
          have : g ^ 2 = 1 := by
            have := pow_orderOf_eq_one g
            rwa [hg] at this
          have h2' := congrArg Subtype.val this
          simpa [pow_two] using h2'
        rw [← hbot] at hgE
        have : (g : Q) = 1 := Subgroup.mem_bot.1 hgE
        have hg1 : g = 1 := Subtype.ext this
        rw [hg1, orderOf_one] at hg
        omega
      have hES : E ∈ S := by
        refine ⟨hEne, hEle.trans hRle, fun x hx => ⟨hRa x hx.1, ?_⟩, fun x hx => ⟨hRb x hx.1, ?_⟩⟩
        · rw [← map_mul, hx.2, map_one]
        · rw [← map_mul, hx.2, map_one]
      have hER : E = R := hRmin' E hES hEle
      intro x hx
      have : x ∈ E := by rw [hER]; exact hx
      exact this.2
    have hcl3 : Cl3 Q a b R :=
      { bpair := h
        four := h4
        N_central := hRc
        N_elem := hRelem
        N_ne := hRne
        N_inva := hRa
        N_invb := hRb
        N_eq := hRγ'
        N_simple := fun M hMR hMa hMb => by
          by_cases hMbot : M = ⊥
          · exact Or.inl hMbot
          · exact Or.inr (hRmin' M ⟨bot_lt_iff_ne_bot.2 hMbot, hMR.trans hRle, hMa, hMb⟩ hMR) }
    exact Cl3.false hQ hcl3

theorem cl2_core {Q : Type u} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) (h4 : FourGen Q)
    {a b : MulAut Q} (h : BPair Q a b) : ⁅dsub Q, (⊤ : Subgroup Q)⁆ = ⊥ :=
  aux_cl2_core (Nat.card Q) Q rfl hQ h4 h

end Main

end CFSG.GH74.E2
