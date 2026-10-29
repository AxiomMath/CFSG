module

public import CFSG.GF2Type.Smith1979W3.CaseD.Model8
public import CFSG.GF2Type.Smith1979W3.CaseD.Jordan
public import CFSG.GF2Type.Smith1979W3.CaseD.PermTables

public section

namespace CFSG.GF2Type.Smith1979W3.CaseD

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix Matrix Finset Equiv

@[expose] def Irr8 (X : Subgroup (Perm (Fin 8))) : Prop :=
  ∀ U : Submodule (ZMod 2) (ι6 → ZMod 2),
    (∀ σ ∈ X, ∀ u ∈ U, Mm σ *ᵥ u ∈ U) → U = ⊥ ∨ U = ⊤

variable {X : Subgroup (Perm (Fin 8))}

theorem Irr8.false_of_orth (h : Irr8 X) {A : Set (ι6 → ZMod 2)}
    (hA : ∀ σ ∈ X, ∀ a ∈ A, Mm σ *ᵥ a ∈ A) {a : ι6 → ZMod 2} (haA : a ∈ A) (ha0 : a ≠ 0)
    {w : ι6 → ZMod 2} (hw0 : w ≠ 0) (horth : ∀ a ∈ A, polar6 a w = 0) : False := by
  let U : Submodule (ZMod 2) (ι6 → ZMod 2) := Submodule.span (ZMod 2) A
  have hU : ∀ σ ∈ X, ∀ u ∈ U, Mm σ *ᵥ u ∈ U := by
    intro σ hσ u hu
    refine Submodule.span_induction (p := fun x _ => Mm σ *ᵥ x ∈ U) ?_ ?_ ?_ ?_ hu
    · intro x hx
      exact Submodule.subset_span (hA σ hσ x hx)
    · rw [Matrix.mulVec_zero]
      exact Submodule.zero_mem U
    · intro x y _ _ ihx ihy
      rw [Matrix.mulVec_add]
      exact Submodule.add_mem U ihx ihy
    · intro c x _ ih
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem U c ih
  have hmem : a ∈ U := Submodule.subset_span haA
  rcases h U hU with hbot | htop
  · rw [hbot] at hmem
    exact ha0 ((Submodule.mem_bot (ZMod 2)).mp hmem)
  · obtain ⟨v, hv⟩ := exists_polar6_eq_one hw0
    have hvU : v ∈ U := by rw [htop]; exact Submodule.mem_top
    let W : Submodule (ZMod 2) (ι6 → ZMod 2) :=
      { carrier := {x | polar6 x w = 0}
        zero_mem' := polar6_zero_left w
        add_mem' := by
          intro x y hx hy
          change polar6 (x + y) w = 0
          rw [polar6_add_left, hx, hy, add_zero]
        smul_mem' := by
          intro c x hx
          change polar6 (c • x) w = 0
          rw [polar6_smul_left, hx, mul_zero] }
    have hW : U ≤ W := Submodule.span_le.mpr (fun x hx => horth x hx)
    have hzero : polar6 v w = 0 := hW hvU
    rw [hv] at hzero
    exact one_ne_zero hzero

theorem Irr8.card_stable (h : Irr8 X) {O : Finset (Fin 8)}
    (hO : ∀ σ ∈ X, ∀ x ∈ O, σ x ∈ O) (hne : O.Nonempty) (hproper : O ≠ Finset.univ) :
    O.card = 1 ∨ O.card = 7 := by
  classical
  have hstable : ∀ σ ∈ X, O.map σ.toEmbedding = O := by
    intro σ hσ
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hO σ hσ y hy
    · rw [Finset.card_map]
  have hvS_ne_zero : ∀ S : Finset (Fin 8), Even S.card → S ≠ ∅ → S ≠ Finset.univ →
      vS S ≠ 0 := by
    intro S hS hS0 hSu hzero
    rw [vS_eq_zero_iff hS] at hzero
    rcases hzero with h | h
    · exact hS0 h
    · exact hSu h
  have heven_false : Even O.card → False := by
    intro hev
    have hO0 : vS O ≠ 0 :=
      hvS_ne_zero O hev (Finset.nonempty_iff_ne_empty.mp hne) hproper
    refine h.false_of_orth (A := {vS O}) (a := vS O) (w := vS O) ?_
      (Set.mem_singleton (vS O)) hO0 hO0 ?_
    · intro σ hσ a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha, Mm_vS σ hev, hstable σ hσ]
      exact Set.mem_singleton (vS O)
    · intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact polar6_self (vS O)
  have hodd_false : O.card = 3 ∨ O.card = 5 → False := by
    intro hcard
    have h2lt : 1 < O.card := by omega
    obtain ⟨p, hpO, q, hqO, hpq⟩ := Finset.one_lt_card.mp h2lt
    have hcompl : Oᶜ.card = 8 - O.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have h2compl : 1 < Oᶜ.card := by rw [hcompl]; omega
    obtain ⟨d, hdO, e, heO, hde⟩ := Finset.one_lt_card.mp h2compl
    have hdO' : d ∉ O := Finset.mem_compl.mp hdO
    have heO' : e ∉ O := Finset.mem_compl.mp heO
    let A : Set (ι6 → ZMod 2) := {v | ∃ a ∈ O, ∃ b ∈ O, a ≠ b ∧ v = uvec a b}
    have hA : ∀ σ ∈ X, ∀ a ∈ A, Mm σ *ᵥ a ∈ A := by
      intro σ hσ a ha
      obtain ⟨u, huO, v, hvO, huv, rfl⟩ := ha
      exact ⟨σ u, hO σ hσ u huO, σ v, hO σ hσ v hvO, σ.injective.ne huv, Mm_pair σ u v⟩
    have haA : uvec p q ∈ A := ⟨p, hpO, q, hqO, hpq, rfl⟩
    have hQ0 : Q6 (0 : ι6 → ZMod 2) = 0 := by decide
    have hpq0 : uvec p q ≠ 0 := by
      intro h0
      have h1 : Q6 (uvec p q) = 1 := Q6_uvec p q hpq
      rw [h0, hQ0] at h1
      exact one_ne_zero h1.symm
    have hde0 : uvec d e ≠ 0 := by
      intro h0
      have h1 : Q6 (uvec d e) = 1 := Q6_uvec d e hde
      rw [h0, hQ0] at h1
      exact one_ne_zero h1.symm
    refine h.false_of_orth (A := A) (a := uvec p q) (w := uvec d e) hA haA hpq0 hde0 ?_
    intro a ha
    obtain ⟨u, huO, v, hvO, huv, rfl⟩ := ha
    have hdisj : Disjoint ({u, v} : Finset (Fin 8)) {d, e} := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_insert, Finset.mem_singleton] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with h | h
      · exact hdO' (h ▸ huO)
      · exact heO' (h ▸ huO)
      · exact hdO' (h ▸ hvO)
      · exact heO' (h ▸ hvO)
    rw [uvec_eq_vS huv, uvec_eq_vS hde,
      polar6_vS (by rw [Finset.card_pair huv]; decide) (by rw [Finset.card_pair hde]; decide),
      Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty]
    decide
  have hlt : O.card < 8 := by
    have hss : O ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ O, hproper⟩
    simpa using Finset.card_lt_card hss
  have hpos : 0 < O.card := Finset.card_pos.mpr hne
  by_contra hcon
  rw [not_or] at hcon
  have hcases : O.card = 2 ∨ O.card = 3 ∨ O.card = 4 ∨ O.card = 5 ∨ O.card = 6 := by
    omega
  rcases hcases with h2 | h3 | h4 | h5 | h6
  · exact heven_false (by rw [h2]; decide)
  · exact hodd_false (Or.inl h3)
  · exact heven_false (by rw [h4]; decide)
  · exact hodd_false (Or.inr h5)
  · exact heven_false (by rw [h6]; decide)

theorem Irr8.exists_orbit (h : Irr8 X) {t : Perm (Fin 8)} (htX : t ∈ X) (ht : IsDT t) :
    ∃ Ω : Finset (Fin 8), (Ω.card = 7 ∨ Ω.card = 8) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, ∃ σ ∈ X, σ x = y) ∧ (∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x) := by
  classical
  have hex : ∃ p : Fin 8, t p ≠ p := by
    by_contra hc
    push Not at hc
    exact ht.ne_one (Equiv.ext hc)
  obtain ⟨p, htp⟩ := hex
  let Ω : Finset (Fin 8) := Finset.univ.filter (fun y => ∃ σ ∈ X, σ p = y)
  have hpΩ : p ∈ Ω := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ p, ⟨1, X.one_mem, rfl⟩⟩
  have htpΩ : t p ∈ Ω := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨t, htX, rfl⟩⟩
  have h2 : 2 ≤ Ω.card := by
    have h1 : 1 < Ω.card := Finset.one_lt_card.mpr ⟨p, hpΩ, t p, htpΩ, htp.symm⟩
    omega
  have hstable : ∀ σ ∈ X, ∀ x ∈ Ω, σ x ∈ Ω := by
    intro σ hσ x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨-, τ, hτ, hτp⟩ := hx
    exact ⟨Finset.mem_univ _, σ * τ, X.mul_mem hσ hτ, by rw [Equiv.Perm.mul_apply, hτp]⟩
  have htrans : ∀ x ∈ Ω, ∀ y ∈ Ω, ∃ σ ∈ X, σ x = y := by
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨-, σ, hσ, hσp⟩ := hx
    obtain ⟨-, τ, hτ, hτp⟩ := hy
    refine ⟨τ * σ.symm, X.mul_mem hτ (X.inv_mem hσ), ?_⟩
    rw [Equiv.Perm.mul_apply, ← hσp, Equiv.symm_apply_apply, hτp]
  by_cases hΩ : Ω = Finset.univ
  · refine ⟨Ω, Or.inr ?_, htrans, ?_⟩
    · rw [hΩ, Finset.card_univ, Fintype.card_fin]
    · intro σ hσ x hx
      rw [hΩ] at hx
      exact absurd (Finset.mem_univ x) hx
  · have hne : Ω.Nonempty := ⟨p, hpΩ⟩
    have h7 : Ω.card = 7 := by
      rcases h.card_stable hstable hne hΩ with h1 | h7
      · omega
      · exact h7
    have hcompl : Ωᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h7]
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcompl
    refine ⟨Ω, Or.inl h7, htrans, ?_⟩
    intro σ hσ x hx
    have hxq : x = q := by
      have hx' : x ∈ Ωᶜ := by simpa using hx
      rw [hq] at hx'
      simpa using hx'
    have hσxq : σ x = q := by
      have hnot : σ x ∉ Ω := by
        intro hmem
        have hmem' : σ.symm (σ x) ∈ Ω := hstable σ.symm (X.inv_mem hσ) (σ x) hmem
        rw [Equiv.symm_apply_apply] at hmem'
        exact hx hmem'
      have hσx' : σ x ∈ Ωᶜ := by simpa using hnot
      rw [hq] at hσx'
      simpa using hσx'
    rw [hσxq, hxq]

theorem Irr8.not_block (h : Irr8 X) {B : Finset (Fin 8)} (h2 : 2 ≤ B.card) (h8 : B.card < 8)
    (hdvd : B.card ∣ 8) :
    ∃ σ ∈ X, B.map σ.toEmbedding ≠ B ∧ ¬ Disjoint (B.map σ.toEmbedding) B := by
  classical
  by_contra hc
  have hc' : ∀ σ ∈ X, B.map σ.toEmbedding = B ∨ Disjoint (B.map σ.toEmbedding) B := by
    intro σ hσ
    by_contra h
    push Not at h
    exact hc ⟨σ, hσ, h⟩
  have hBcard : B.card = 2 ∨ B.card = 4 := by
    interval_cases B.card
    · exact Or.inl rfl
    · exfalso; exact absurd hdvd (by decide)
    · exact Or.inr rfl
    · exfalso; exact absurd hdvd (by decide)
    · exfalso; exact absurd hdvd (by decide)
    · exfalso; exact absurd hdvd (by decide)
  have hBeven : Even B.card := by
    rcases hBcard with hB | hB <;> rw [hB] <;> decide
  have hB0 : vS B ≠ 0 := by
    intro hzero
    rw [vS_eq_zero_iff hBeven] at hzero
    rcases hzero with h | h
    · rw [h] at h2
      simp only [Finset.card_empty] at h2
      omega
    · rw [h] at h8
      simp only [Finset.card_univ, Fintype.card_fin] at h8
      omega
  let A : Set (ι6 → ZMod 2) := {v | ∃ σ ∈ X, v = vS (B.map σ.toEmbedding)}
  have hA : ∀ σ ∈ X, ∀ a ∈ A, Mm σ *ᵥ a ∈ A := by
    intro τ hτ a ha
    obtain ⟨σ, hσ, rfl⟩ := ha
    refine ⟨τ * σ, X.mul_mem hτ hσ, ?_⟩
    have hSeven : Even (B.map σ.toEmbedding).card := by rw [Finset.card_map]; exact hBeven
    have hemp : (σ.toEmbedding).trans (τ.toEmbedding) = (τ * σ).toEmbedding := by
      ext x
      rfl
    rw [Mm_vS τ hSeven, Finset.map_map, hemp]
  have haA : vS B ∈ A := by
    refine ⟨1, X.one_mem, ?_⟩
    rw [show (1 : Perm (Fin 8)).toEmbedding = Function.Embedding.refl (Fin 8) from rfl,
      Finset.map_refl]
  refine h.false_of_orth (A := A) (a := vS B) (w := vS B) hA haA hB0 hB0 ?_
  intro a ha
  obtain ⟨σ, hσ, rfl⟩ := ha
  have hSeven : Even (B.map σ.toEmbedding).card := by rw [Finset.card_map]; exact hBeven
  rw [polar6_vS hSeven hBeven]
  rcases hc' σ hσ with heq | hdisj
  · rw [heq, Finset.inter_self]
    rcases hBcard with hB | hB <;> rw [hB] <;> decide
  · rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty]
    decide

theorem Irr8.isPreprimitive_res (h : Irr8 X) {Ω : Finset (Fin 8)}
    (hcard : Ω.card = 7 ∨ Ω.card = 8) (htrans : ∀ x ∈ Ω, ∀ y ∈ Ω, ∃ σ ∈ X, σ x = y)
    (hfix : ∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x) :
    MulAction.IsPreprimitive (resGroup X Ω) {x // x ∈ Ω} := by
  rcases hcard with h7 | h8
  · exact isPreprimitive_resGroup_of_prime hfix htrans (by rw [h7]; norm_num)
  · refine isPreprimitive_resGroup_of_blocks hfix htrans ?_
    intro B _hB h2 hlt hdvd
    exact h.not_block h2 (by omega) (by simpa [h8] using hdvd)

end CFSG.GF2Type.Smith1979W3.CaseD
