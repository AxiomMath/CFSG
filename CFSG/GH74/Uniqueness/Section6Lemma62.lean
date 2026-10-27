module

public import CFSG.GH74.Uniqueness.Section6Basic
public import CFSG.GH74.Uniqueness.Section5Stmt
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Lemma62

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
private theorem conjugate_le_conjugate_of_le {A B : Subgroup X} (h : A ≤ B) (g : X) :
    conjugate A g ≤ conjugate B g := by
  intro x hx
  rw [mem_conjugate_iff] at hx ⊢
  exact h hx

omit [Finite X] in
private theorem card_conjugate_eq {A : Subgroup X} (g : X) :
    Nat.card (conjugate A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem odd_card_of_pgroup_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X}
    (hQ : IsPGroup p Q) : Odd (Nat.card Q) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

omit [Finite X] in
theorem mem_normalizer_closure_invertedSet_of_orderOf_eq_two {D : Subgroup X} {z : X}
    (hz : orderOf z = 2) :
    z ∈ normalizer
      ((Subgroup.closure (CFSG.OddInversion.invertedSet D z) : Subgroup X) : Set X) := by
  have hfwd : ∀ x ∈ Subgroup.closure (CFSG.OddInversion.invertedSet D z),
      z * x * z⁻¹ ∈ Subgroup.closure (CFSG.OddInversion.invertedSet D z) := by
    intro x hx
    have : Subgroup.closure (CFSG.OddInversion.invertedSet D z) ≤
        (Subgroup.closure (CFSG.OddInversion.invertedSet D z)).comap
          (MulAut.conj z).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (MulAut.conj z).toMonoidHom y = z * y * z⁻¹ := by simp
      rw [e, hy.2]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure hy)
    simpa [MulAut.conj_apply] using this hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hfwd x, fun hx => ?_⟩
  have h2 := hfwd _ hx
  rwa [CFSG.OddInversion.conj_conj_of_orderOf_eq_two hz x] at h2

theorem exists_T4Cand_of_normalized (hZ : IsInvariantInvolutionSet Z) {z : X} {p : ℕ}
    {Q : Subgroup X} (hz : z ∈ Z) (hzM : z ∈ M) (hp : p.Prime) (hp2 : p ≠ 2) (hQ : IsPGroup p Q)
    (hQM : Q ≤ M) (hΩ : 2 ≤ (omegaFix M (Q : Set X)).ncard)
    (hI : 2 ≤ Nat.card (CFSG.OddInversion.invertedSet Q z)) :
    ∃ W : Subgroup X, T4Cand Z M z p W ∧
      Nat.card (CFSG.OddInversion.invertedSet W z) =
        Nat.card (CFSG.OddInversion.invertedSet Q z) := by
  have hz2 : orderOf z = 2 := hZ.1 z hz
  set W : Subgroup X := Subgroup.closure (CFSG.OddInversion.invertedSet Q z) with hWdef
  have hWQ : W ≤ Q := (Subgroup.closure_le Q).mpr fun x hx => hx.1
  have hzW : z ∈ normalizer (W : Set X) := mem_normalizer_closure_invertedSet_of_orderOf_eq_two hz2
  have hIW : CFSG.OddInversion.invertedSet W z = CFSG.OddInversion.invertedSet Q z :=
    Set.Subset.antisymm (fun x hx => ⟨hWQ hx.1, hx.2⟩)
      (fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩)
  have hQodd : Odd (Nat.card Q) := odd_card_of_pgroup_ne_two hp hp2 hQ
  have hWodd : Odd (Nat.card W) := Odd.of_dvd_nat hQodd (Subgroup.card_dvd_of_le hWQ)
  refine ⟨W, ⟨hz, hzM, hp, hp2, hQ.to_le hWQ, hWQ.trans hQM, hzW, ?_, ?_, ?_⟩, by rw [hIW]⟩
  · rw [← closure_invertedSet_eq_commutator hz2 hWodd hzW, hIW]
  · intro hbot
    have hsub : CFSG.OddInversion.invertedSet Q z ⊆ {1} := Subgroup.closure_eq_bot_iff.mp hbot
    have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton (1 : X))
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h1
    omega
  · exact hΩ.trans (Set.ncard_le_ncard (omegaFix_anti fun x hx => hWQ hx) (Set.toFinite _))

theorem ZDSetup.lemma62 (S : ZDSetup X Z M) : Lemma62Stmt Z M := by
  intro z p W hW γ hγ hγM
  have hZ := S.invariant
  have h := S.prodDisc
  have hcand := hW.cand
  obtain ⟨hγΩ, hWγ⟩ := h.mem_omegaFix_iff.mp hγ
  have hTFAE := h.prop38c hZ hcand.mem_Z hcand.mem_M hγΩ hγM hcand.prime hcand.ne_two
  have hupper := hcand.card_invertedSet_le hZ h
  constructor
  · rintro ⟨Q, hQ, hzQ⟩
    have hQcard : Nat.card (CFSG.OddInversion.invertedSet Q z) = zNumShare Z M p :=
      (h.prop38b hZ hcand.mem_Z hcand.mem_M hγΩ hγM hcand.prime hcand.ne_two hQ.le hQ.isPGroup
        hzQ).2 hQ
    have hQM : Q ≤ M := hQ.le.trans inf_le_left
    have hQγ : Q ≤ γ := hQ.le.trans inf_le_right
    have hΩQ : 2 ≤ (omegaFix M (Q : Set X)).ncard := by
      have hsub : ({M, γ} : Set (Subgroup X)) ⊆ omegaFix M (Q : Set X) := by
        intro x hx
        rcases hx with rfl | rfl
        · exact h.self_mem_omegaFix_iff.mpr hQM
        · exact h.mem_omegaFix_iff.mpr ⟨hγΩ, hQγ⟩
      calc 2 = ({M, γ} : Set (Subgroup X)).ncard := (Set.ncard_pair (Ne.symm hγM)).symm
        _ ≤ (omegaFix M (Q : Set X)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hI : 2 ≤ Nat.card (CFSG.OddInversion.invertedSet Q z) :=
      hQcard ▸ hcand.two_le_zNumShare hZ h
    obtain ⟨W₂, hW₂, hW₂card⟩ := exists_T4Cand_of_normalized hZ hcand.mem_Z hcand.mem_M hcand.prime
      hcand.ne_two hQ.isPGroup hQM hΩQ hI
    have hle := hW.max W₂ hW₂
    rw [hW₂card, hQcard] at hle
    exact le_antisymm hupper hle
  · intro hcard
    have h31 := hTFAE.out 3 1
    exact h31.mp ⟨W, le_inf hcand.le_M hWγ, hcand.pgroup, hcand.normalizes, hcard⟩

theorem T4Max.card_eq_zNumShare_of_not_doublyTransitive (S : ZDSetup X Z M)
    (hC57 : Cor57Stmt Z M) {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Max Z M z p W) :
    ¬ DoublyTransitive M → Nat.card (CFSG.OddInversion.invertedSet W z) = zNumShare Z M p := by
  intro hnot
  have hZ := S.invariant
  have h := S.prodDisc
  have hcand := hW.cand
  obtain ⟨⟨s, hs, Q, hQp, hQ3, hsQ, hcnt, hfix⟩, -⟩ := hC57 hnot p hcand.prime hcand.ne_two
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.isConj_of_mem hZ hs hcand.mem_Z)
  set g : X := c⁻¹ with hg
  have hgsz : g⁻¹ * s * g = z := by rw [hg, inv_inv]; exact hc
  have hsg : s * g = g * z := by rw [← hgsz]; group
  set P : Subgroup X := conjugate Q g with hP
  have hPp : IsPGroup p P := hQp.map _
  have hzP : z ∈ normalizer (P : Set X) := by
    rw [← conjugate_eq_iff_mem_normalizer, hP, conjugate_conjugate, ← hsg, ← conjugate_conjugate,
      conjugate_eq_iff_mem_normalizer.mpr hsQ]
  have hfixM : conjugate (conjugate M g⁻¹) s = conjugate M g⁻¹ := by
    rw [conjugate_conjugate, show g⁻¹ * s = z * g⁻¹ by rw [← hgsz]; group, ← conjugate_conjugate,
      (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr hcand.mem_M]
  have hQβ : Q ≤ conjugate M g⁻¹ := hfix _ (conjugate_mem_omega (self_mem_omega M) g⁻¹) hfixM
  have hPM : P ≤ M := by
    have := conjugate_le_conjugate_of_le hQβ g
    rwa [conjugate_conjugate, inv_mul_cancel, conjugate_one] at this
  have hPodd : Odd (Nat.card P) := odd_card_of_pgroup_ne_two hcand.prime hcand.ne_two hPp
  have hPcard : Nat.card (CFSG.OddInversion.invertedSet P z) = zNumShare Z M p := by
    rw [← zCosetNum_eq_card_invertedSet hZ hcand.mem_Z hPodd hzP, ← hcnt, ← hgsz, hP]
    exact zCosetNum_conjugate hZ Q s g
  have hΩP : 2 ≤ (omegaFix M (P : Set X)).ncard := by
    rw [hP, ncard_omegaFix_conjugate]
    omega
  have hm2 : 2 ≤ zNumShare Z M p := hcand.two_le_zNumShare hZ h
  obtain ⟨W₂, hW₂, hW₂card⟩ := exists_T4Cand_of_normalized hZ hcand.mem_Z hcand.mem_M hcand.prime
    hcand.ne_two hPp hPM hΩP (hPcard ▸ hm2)
  have hle := hW.max W₂ hW₂
  rw [hW₂card, hPcard] at hle
  exact le_antisymm (hcand.card_invertedSet_le hZ h) hle

end Lemma62

end CFSG.GH74.Uniqueness
