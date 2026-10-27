module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Ker
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Case

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)
  (Φ : ↥(fz410M R E) →* Equiv.Perm (Fz410Om E P Q))
  (hΦ : ∀ (n : ↥(fz410M R E)) (A : Fz410Om E P Q), (Φ n A).1 = fz410Cj (n : G) A.1)

include D hΦ

theorem act_surjective : Function.Surjective Φ := by
  have hcard : Nat.card (Fz410Om E P Q) = 4 := D.card_Om
  haveI : Finite (Fz410Om E P Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hρx : Φ ⟨rho, D.rho_mem_M⟩ D.Wom = D.Wom :=
    D.act_W Φ hΦ ⟨rho, D.rho_mem_M⟩ D.rho_mem_N2
  have hlx : Φ ⟨lam, D.lam_mem_M⟩ D.Wom = D.Wom :=
    D.act_W Φ hΦ ⟨lam, D.lam_mem_M⟩ D.lam_mem_N2
  obtain ⟨g, hg, w, hw, hgw⟩ := D.exists_move
  have hρr : Φ ⟨rho, D.rho_mem_M⟩ ∈ Φ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hlr : Φ ⟨lam, D.lam_mem_M⟩ ∈ Φ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hgr : Φ ⟨g, hg⟩ ∈ Φ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hσ : Φ ⟨g, hg⟩ D.Wom ≠ D.Wom := by
    intro h
    apply hgw
    have h1 : ((Φ ⟨g, hg⟩ D.Wom : Fz410Om E P Q) : Subgroup G) = fz410Cj g W :=
      hΦ ⟨g, hg⟩ D.Wom
    have h2 : ((Φ ⟨g, hg⟩ D.Wom : Fz410Om E P Q) : Subgroup G) = W := by rw [h]; rfl
    rw [h2] at h1
    have h3 : g * w * g⁻¹ ∈ fz410Cj g W := by
      rw [mem_fz410Cj]
      simpa [mul_assoc] using hw
    rw [← h1] at h3
    exact h3
  have htrans : ∀ y : Fz410Om E P Q, ∃ h ∈ Φ.range, h D.Wom = y := by
    intro y
    by_cases hy : y = D.Wom
    · exact ⟨1, Subgroup.one_mem _, by simp [hy]⟩
    · obtain ⟨k, -, hky⟩ := fz410_perm_trans hcard D.Wom (a := Φ ⟨rho, D.rho_mem_M⟩) hρx
        (D.act_rho_pow Φ hΦ) (D.act_rho_ne_one Φ hΦ) hσ y hy
      exact ⟨Φ ⟨rho, D.rho_mem_M⟩ ^ k * Φ ⟨g, hg⟩,
        Subgroup.mul_mem _ (Subgroup.pow_mem _ (hρr) k)
          (hgr), hky⟩
  have htop := fz410_perm_top hcard Φ.range D.Wom htrans (a := Φ ⟨rho, D.rho_mem_M⟩)
    (b := Φ ⟨lam, D.lam_mem_M⟩) (hρr)
    (hlr) hρx hlx (D.act_rho_pow Φ hΦ)
    (D.act_rho_ne_one Φ hΦ) (D.act_lam_sq Φ hΦ) (D.act_lam_rho Φ hΦ)
  exact MonoidHom.range_eq_top.mp htop

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
