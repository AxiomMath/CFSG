module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4A
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Inn

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {K : Type} [Field K]

theorem sp4_caseA [Finite K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ n)
    [CharP K p]
    (hcen : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥) {r : ℕ}
    {V Z : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (h2 : N2Cfg (StatedProj (StatedSp 2 K)) r V Z) (h3 : N3Full (StatedProj (StatedSp 2 K)) V Z)
    (hrp : r = p) : False := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hr : r.Prime := h2.1
  have hr2 : Odd r := h2.2.1
  have hVe : IsElementaryAbelian r ↥V := h2.2.2.1
  have hVc : Nat.card ↥V = r ^ 2 := h2.2.2.2.1
  have := hVe
  obtain ⟨g, hg1, hgV⟩ := exists_inn_mem hodd hp hK hr hr2 hVc
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hgp : g ^ p = 1 := by
    have h1 : (MulAut.conj g) ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian _ hgV
    rw [hrp, ← map_pow] at h1
    exact hinj (by rw [h1, map_one])
  obtain ⟨u, hug, hup⟩ := exists_lift_pow_eq_one (hp.eq_two_or_odd'.resolve_left hp2) hgp
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hg1 (by rw [← hug, map_one])
  have h2' : N2Cfg (StatedProj (StatedSp 2 K)) p V Z := hrp ▸ h2
  exact caseA hp2 hcen h2' h3 hup hu1 (by rw [hug]; exact hgV)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
