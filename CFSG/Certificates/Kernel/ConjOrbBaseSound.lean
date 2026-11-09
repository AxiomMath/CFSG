module

public import Certificates.Data.Kernel.ConjOrbBase
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.Certificates.Kernel.Spor.RawBaseEq

public section

namespace CFSG.KC.ConjOrbBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.OrbGroup
open CFSG.KLie.CT (fget)

theorem baseClos_spec {n w ng N nb BP r i : Nat} {G GI T E D : Nat → Nat}
    (h : CFSG.KC.ConjOrb.baseClos n w ng N nb BP G GI T E D r i = true) :
    (i ≠ r → CFSG.KC.ConjOrb.pconj n w (mask w) (G (CFSG.KC.ConjOrb.tLab (D i)))
      (GI (CFSG.KC.ConjOrb.tLab (D i))) (T (CFSG.KC.ConjOrb.tPar (D i))) = T i) ∧
    ∀ k < ng, fget (E i) k 20 < N ∧ ∀ s < nb,
      pg w (mask w) (T (fget (E i) k 20)) (pg w (mask w) BP s) =
        pg w (mask w) (G k) (pg w (mask w) (T i) (pg w (mask w) (GI k) (pg w (mask w) BP s))) := by
  unfold CFSG.KC.ConjOrb.baseClos at h
  rw [CFSG.KC.ConjOrb.strictB_eq, CFSG.KC.ConjOrb.strictB_eq, bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hir => ?_, fun k hk => ?_⟩
  · have hb : Nat.beq i r = false := by
      cases e : Nat.beq i r
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hir
    rw [hb] at h1
    change strictB (D i) _ = true at h1
    rw [CFSG.KC.ConjOrb.strictB_eq] at h1
    exact Nat.eq_of_beq_eq_true h1
  · have h3 := allN_spec h2 k hk
    rw [CFSG.KC.ConjOrb.strictB_eq, bAnd_iff] at h3
    refine ⟨Nat.blt_eq.mp h3.1, fun s hs => ?_⟩
    have h4 := allN_spec h3.2 s hs
    rw [CFSG.KC.ConjOrb.strictB_eq] at h4
    exact Nat.eq_of_beq_eq_true h4

theorem closPt_of_base {n w : Nat} (hn : n < 2 ^ 32) {kS kO nb BP NS CH : ℕ}
    {PS PSI LR TR TRI : ℕ → ℕ} {Dw : List (List ℤ)} {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS nb BP S base)
    (hh : CFSG.KS.Raw.headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO Dw nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    {ng N r : Nat} {G GI T E D : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    {t : Equiv.Perm (Fin n)}
    (hh0 : CFSG.KC.ConjOrb.headK n w ng G GI = true)
    (hg : ∀ k < ng, PRep n w (G k) (g k))
    (hgm : ∀ k < ng, ∀ c ∈ Gen n S kO, g k * c * (g k)⁻¹ ∈ Gen n S kO)
    (hcr : canonK n w (mask w) (n * w) (T r) = true) (ht : PRep n w (T r) t)
    (htm : t ∈ Gen n S kO)
    (htr : ∀ i < N, CFSG.KC.ConjOrb.treePt ng N r E D i = true)
    (hbc : ∀ i < N, CFSG.KC.ConjOrb.baseClos n w ng N nb BP G GI T E D r i = true) :
    ∀ i < N, CFSG.KC.ConjOrb.closPt n w ng N G GI T E i = true := by
  obtain ⟨-, hG0⟩ := CFSG.KC.ConjOrb.headK_spec hh0
  have hGI : ∀ k < ng, PRep n w (GI k) (g k)⁻¹ := fun k hk => prep_inv (hg k hk) (hG0 k hk).2.2
  have hQd : ∀ d, ∀ i < N, CFSG.KC.ConjOrb.tDep (D i) = d →
      canonK n w (mask w) (n * w) (T i) = true ∧ ∃ c ∈ Gen n S kO, PRep n w (T i) c := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd
      by_cases hir : i = r
      · subst hir
        exact ⟨hcr, t, htm, ht⟩
      · obtain ⟨hp, hlab, -, hdep⟩ := CFSG.KC.ConjOrb.treePt_spec (htr i hi) hir
        obtain ⟨hcp, c, hcm, hc⟩ := ih _ (by omega) _ hp rfl
        rw [← (baseClos_spec (hbc i hi)).1 hir]
        refine ⟨CFSG.KC.BfsPin.canonK_pcomp (hG0 _ hlab).1
            (CFSG.KC.BfsPin.canonK_pcomp hcp (hG0 _ hlab).2.1), _, ?_,
          prep_pconj hn (hg _ hlab) (hGI _ hlab) hc⟩
        exact hgm _ hlab c hcm
  have hQ : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true ∧
      ∃ c ∈ Gen n S kO, PRep n w (T i) c := fun i hi => hQd _ i hi rfl
  intro i hi
  obtain ⟨hci, c, hcm, hc⟩ := hQ i hi
  have hedge : ∀ k < ng, fget (E i) k 20 < N ∧
      CFSG.KC.ConjOrb.pconj n w (mask w) (G k) (GI k) (T i) = T (fget (E i) k 20) := by
    intro k hk
    obtain ⟨hj, hbase⟩ := (baseClos_spec (hbc i hi)).2 k hk
    refine ⟨hj, ?_⟩
    obtain ⟨hcj, c', hcm', hc'⟩ := hQ _ hj
    have hconj := prep_pconj hn (hg k hk) (hGI k hk) hc
    have heq : g k * c * (g k)⁻¹ = c' := by
      refine CFSG.KS.Raw.BaseEq.eq_of_baseN hb hh hl hNS hs
        (hgm k hk c hcm)
        hcm' fun s hs' hbs => ?_
      apply Fin.ext
      have e0 : pg w (mask w) (GI k) (pg w (mask w) BP s) = ((g k)⁻¹ ⟨_, hbs⟩ : Fin n).val :=
        hGI k hk ⟨_, hbs⟩
      have e1 : pg w (mask w) (T (fget (E i) k 20)) (pg w (mask w) BP s) =
          (c' ⟨_, hbs⟩ : Fin n).val := hc' ⟨_, hbs⟩
      have e2 := hbase s hs'
      rw [e0, hc, hg k hk, e1] at e2
      rw [e2]
      rfl
    have hcq := CFSG.KC.BfsPin.canonK_pcomp (hG0 k hk).1
      (CFSG.KC.BfsPin.canonK_pcomp hci (hG0 k hk).2.1)
    obtain ⟨-, hw, hp0, -⟩ := CFSG.KS.PF.canon_facts hcq
    obtain ⟨-, -, hq0, -⟩ := CFSG.KS.PF.canon_facts hcj
    refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp0 hq0 fun x hx => ?_
    rw [hconj ⟨x, hx⟩, hc' ⟨x, hx⟩, heq]
  unfold CFSG.KC.ConjOrb.closPt
  rw [CFSG.KC.ConjOrb.strictB_eq, CFSG.KC.ConjOrb.strictB_eq, bAnd_iff]
  refine ⟨hci, allN_iff.2 fun k hk => ?_⟩
  beta_reduce
  rw [CFSG.KC.ConjOrb.strictB_eq, bAnd_iff]
  obtain ⟨hj, he⟩ := hedge k hk
  exact ⟨Nat.blt_eq.mpr hj, by rw [he]; exact Nat.beq_refl _⟩

end CFSG.KC.ConjOrbBase

end
