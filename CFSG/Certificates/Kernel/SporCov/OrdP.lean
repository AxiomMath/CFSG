module

public import Certificates.Data.Kernel.SporCov.OrdP
public import CFSG.Certificates.Kernel.SporCov.LaneKit

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub

variable {p w S d T L H CM RM ONE LV HV nb : ℕ}

theorem ordPK_mat (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {Y q : ℕ} (hq : q < 65536) (hY : validM p nb L H Y = true)
    (h : ordPK (mulR p w S d T L H CM RM) ONE Y q = true) :
    ordMat p d w S Y ^ q = 1 ∧ ordMat p d w S Y ≠ 1 := by
  unfold ordPK at h
  rw [forceR_eq] at h
  exact prime_sound' hc hnb (RB := fun _ => Y) (nreg := 2) (r := 1) hq hY h

theorem ordPK_orderOf {G : Type} [Group G] {ρ : G →* Matrix (Fin d) (Fin d) (ZMod p)}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hρ : Function.Injective ρ) {Y q : ℕ} {g : G} (hq : q.Prime) (hq' : q < 65536)
    (hY : validM p nb L H Y = true) (hg : ordMat p d w S Y = ρ g)
    (h : ordPK (mulR p w S d T L H CM RM) ONE Y q = true) : orderOf g = q := by
  obtain ⟨h1, h2⟩ := ordPK_mat hc hnb hq' hY h
  have : Fact q.Prime := ⟨hq⟩
  refine orderOf_eq_prime (hρ ?_) ?_
  · rw [map_pow, ← hg, h1, map_one]
  · rintro rfl
    exact h2 (by rw [hg, map_one])

end CFSG.KD.SporCov

end
