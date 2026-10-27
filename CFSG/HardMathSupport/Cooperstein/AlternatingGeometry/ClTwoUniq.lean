module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClR3
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClR2

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.Quasithin CFSG.AGLEmbedding CFSG.Open

section Uniq

variable {Ω : Type*} [DecidableEq Ω] [Fintype Ω] {σ τ : Perm Ω} {cσ cτ : Ω → Bool}

theorem eq_of_dblGroup_le_isPGroup' (hcard : 6 ≤ Fintype.card Ω)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (hcσ : ∀ x, cσ (σ x) = cσ x)
    (hτ1 : ∀ x, τ x ≠ x) (hτ2 : ∀ x, τ (τ x) = x) (hcτ : ∀ x, cτ (τ x) = cτ x)
    (h4 : ∀ x, σ x ≠ τ x → (cls cσ x).card ≠ 4 ∧ (cls cτ x).card ≠ 4)
    {P : Subgroup (Perm Ω)} (hP : IsPGroup 2 P)
    (hσP : dblGroup σ cσ ≤ P) (hτP : dblGroup τ cτ ≤ P) : σ = τ := by
  by_contra hne
  obtain ⟨p, hp, hNσ, hNτ⟩ := exists_good_point hcard hσ1 hσ2 hcσ hτ1 hτ2 hcτ hne
  obtain ⟨q, hqc, hqp, hqp', hqd, hqd'⟩ := exists_mem_cls_aux (σ := σ) cσ hσ1 hσ2 hcσ
    (p := p) (d := τ p) (hτ1 p) (Ne.symm hp) hNσ (h4 p hp).1
  obtain ⟨e, hec, hep, hep', hed, hed'⟩ := exists_mem_cls_aux (σ := τ) cτ hτ1 hτ2 hcτ
    (p := p) (d := σ p) (hσ1 p) hp hNτ (h4 p hp).2
  have hx : swap p (σ p) * swap q (σ q) ∈ dblGroup σ cσ :=
    Subgroup.subset_closure ⟨p, q, hqp, hqp', hqc, rfl⟩
  have hy : swap p (τ p) * swap e (τ e) ∈ dblGroup τ cτ :=
    Subgroup.subset_closure ⟨p, e, hep, hep', hec, rfl⟩
  have hg := P.mul_mem (hσP hx) (hτP hy)
  have hσinj : ∀ a b, σ a = σ b → a = b := fun a b h => σ.injective h
  have hτinj : ∀ a b, τ a = τ b → a = b := fun a b h => τ.injective h
  obtain ⟨h1, h2, h3⟩ := threeCycle_of_blocks (p := p) (p' := σ p) (d := τ p) (q := q)
    (q' := σ q) (e := e) (f := τ e) (hσ1 p).symm (hτ1 p).symm hp
    hqp hqp' hqd
    (by intro h; apply hqp'; rw [← h, hσ2])
    (by intro h; exact hqp (hσinj _ _ h))
    (by intro h; apply hqd'; rw [← h, hσ2])
    hep hed hep'
    (by intro h; apply hep'; rw [← h, hτ2])
    (by intro h; apply hed'; rw [← h, hτ2])
    (by intro h; exact hep (hτinj _ _ h))
  exact not_isPGroup_of_threeCycle hP hg (a := p) (b := τ p) (c := σ p)
    (hτ1 p).symm hp.symm (hσ1 p) h1 h2 h3

end Uniq

namespace Classif.Pre

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {W : Subgroup (Perm Ω)} {ι : Type*}
  {E : ι → Subgroup (Perm Ω)} (P : Pre W E)

theorem le_pairPres_of_blockData {i₀ : ι} {σ : Perm Ω} {c : Ω → Bool}
    (hB : BlockData (E i₀) σ c)
    (hΛ : ∀ y, partner P.twoGroup y = y ↔ c y = true)
    (h6 : 6 ≤ (Finset.univ.filter fun y => c y = true).card)
    (h4 : (Finset.univ.filter fun y => c y = true).card ≠ 4) (i : ι) :
    E i ≤ pairPres σ hB.1 hB.2.1 := by
  classical
  obtain ⟨hσ1, hσ2, hg0, hc0, hcol0, hdbl0⟩ := hB
  have hB0 : BlockData (E i₀) σ c := ⟨hσ1, hσ2, hg0, hc0, hcol0, hdbl0⟩
  have hex : ∃ z, partner P.twoGroup z = z := by
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega : 0 < (Finset.univ.filter fun y => c y = true).card)
    exact ⟨y, (hΛ y).2 (by simpa using hy)⟩
  have hmatched : ∀ y, c y = false → σ y = partner P.twoGroup y := by
    intro y hy
    have hsw : swap y (σ y) ∈ E i₀ := by
      by_contra h
      have := (hcol0 y).2 h
      rw [hy] at this; exact absurd this (by simp)
    exact (partner_eq_of_swap_mem P.twoGroup (hσ1 y).symm (P.le i₀ hsw)).symm
  have hΛcard : Fintype.card Ω ≥ 6 := by
    have := Finset.card_le_univ (Finset.univ.filter fun y => c y = true)
    omega
  rcases shape_cases (P.shape i) with hsw | ⟨x, hx⟩ | hall
  ·
    refine (Offender.le_closure_swaps_of_swapType hsw).trans ?_
    rw [Subgroup.closure_le]
    rintro t ⟨htE, a, b, hab, rfl⟩
    have hpb : partner P.twoGroup a = b := partner_eq_of_swap_mem P.twoGroup hab (P.le i htE)
    have hca : c a = false := by
      by_contra h
      have h' : c a = true := by simpa using h
      have := (hΛ a).2 h'
      rw [hpb] at this
      exact hab this.symm
    rw [← hpb, ← hmatched a hca]
    exact swap_mem_pairPres hσ1 hσ2 a
  ·
    exfalso
    have hsub : (↑(Finset.univ.filter fun y => c y = true) : Set Ω) ⊆ orbit (E i) x := by
      intro z hz
      have hz' : c z = true := by simpa using hz
      exact unmatched_mem_orbit_of_fourOrbit P.twoGroup (P.le i) (P.exp i) (P.shape i) hx
        ((hΛ z).2 hz')
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, hx] at this
    omega
  · obtain ⟨σ', c', hbd'⟩ := blockData_of_shape hall.1 hall.2
    obtain ⟨hs1, hs2, hg, hc, hcol, hdbl⟩ := hbd'
    have hbd' : BlockData (E i) σ' c' := ⟨hs1, hs2, hg, hc, hcol, hdbl⟩
    have hmatched' : ∀ y, c' y = false → σ' y = partner P.twoGroup y := by
      intro y hy
      have hsw : swap y (σ' y) ∈ E i := by
        by_contra h
        have := (hcol y).2 h
        rw [hy] at this; exact absurd this (by simp)
      exact (partner_eq_of_swap_mem P.twoGroup (hs1 y).symm (P.le i hsw)).symm
    have hΛc' : ∀ y, partner P.twoGroup y = y → c' y = true := by
      intro y hy
      by_contra h
      have h' : c' y = false := by simpa using h
      have := hmatched' y h'
      exact hs1 y (this.trans hy)
    have h3' : 3 ≤ (Finset.univ.filter fun y => c' y = true).card := by
      have hsub : (Finset.univ.filter fun y => c y = true) ⊆ Finset.univ.filter fun y => c' y = true := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact hΛc' y ((hΛ y).2 hy)
      have := Finset.card_le_card hsub
      omega
    have hΛ' := unmatched_iff_true P.twoGroup (P.le i) hbd' h3' hex
    have hcls : ∀ y, partner P.twoGroup y = y → (cls c y).card = (Finset.univ.filter fun y => c y = true).card ∧
        (cls c' y).card = (Finset.univ.filter fun y => c y = true).card := by
      intro y hy
      have e1 : cls c y = Finset.univ.filter fun y => c y = true := by
        unfold cls; rw [(hΛ y).1 hy]
      have e2 : cls c' y = Finset.univ.filter fun y => c y = true := by
        unfold cls
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [(hΛ' y).1 hy, ← hΛ' z, ← hΛ z]
      rw [e1, e2]; exact ⟨rfl, rfl⟩
    have hσeq : σ = σ' := by
      refine eq_of_dblGroup_le_isPGroup' hΛcard hσ1 hσ2 hc0 hs1 hs2 hc ?_ P.twoGroup
        (hdbl0.trans (P.le i₀)) (hdbl.trans (P.le i))
      intro p hp
      have hpm : partner P.twoGroup p = p := by
        by_contra hne
        have hcf : c p = false := by
          by_contra h
          exact hne ((hΛ p).2 (by simpa using h))
        have hcf' : c' p = false := by
          by_contra h
          exact hne ((hΛ' p).2 (by simpa using h))
        exact hp ((hmatched p hcf).trans (hmatched' p hcf').symm)
      obtain ⟨e1, e2⟩ := hcls p hpm
      exact ⟨by rw [e1]; exact h4, by rw [e2]; exact h4⟩
    subst hσeq
    intro g hg' z
    exact hg g hg' z

end Classif.Pre

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
