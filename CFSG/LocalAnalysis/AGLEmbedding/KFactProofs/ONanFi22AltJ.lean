module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22AltSound
public import Certificates.Certificate9560

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Alt

open CFSG.Sporadic.Fi22 (J rep_alpha rep_beta actionChecks_parts)

theorem altData_J :
    ∃ (X Y : J) (q xs : ℕ → J), AltData X Y q xs := by
  have hg : Fi22Guest.guestCheck 3510 CFSG.Sporadic.Fi22.orb.alpha CFSG.Sporadic.Fi22.orb.alpha
      CFSG.Sporadic.Fi22.orb.beta (CFSG.Sporadic.Th.Native.invT 3510 CFSG.Sporadic.Fi22.orb.beta)
      = true := Fi22Guest.guest_check
  unfold Fi22Guest.guestCheck at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨h1, h2⟩, -⟩ := hg
  exact altData_of_check (n := 3510) (by norm_num) rep_alpha
    CFSG.Sporadic.Bridge.Fi22.rep_alpha_inv rep_beta
    (CFSG.Sporadic.Th.Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.2.1) h1 h2
    Certificates.certificate9560

theorem altData_of_isFi22
    {L : Type} [Group L]
    (hL : Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group)) :
    (∃ (X Y : L) (q xs : ℕ → L), AltData X Y q xs) ∧ Nat.card L = 64561751654400 := by
  obtain ⟨φ⟩ := hL
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  let ψ : J ≃* L := (CFSG.Sporadic.Fi22.fi22EquivJ.symm.trans β).trans φ.symm
  obtain ⟨X, Y, q, xs, D⟩ := altData_J
  refine ⟨⟨_, _, _, _, D.map ψ⟩, ?_⟩
  rw [← Nat.card_congr ψ.toEquiv]
  exact CFSG.Sporadic.Fi22.card_J

end CFSG.AGLEmbedding.KFactProofs.Fi22Alt
