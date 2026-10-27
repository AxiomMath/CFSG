module

public import CFSG.CGT.Timmesfeld75.Sec66Cfg
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.CGT.Timmesfeld75.JLemma35
public import CFSG.CGT.Timmesfeld75.JLemmaTrans
public import CFSG.CGT.Timmesfeld75.Sec5SevenB
public import CFSG.CGT.Timmesfeld75.Sec62Orbit

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    H ≤ Subgroup.normalizer (K : Set G) := fun h hh =>
  Subgroup.centralizer_le_normalizer (K : Set G)
    (Subgroup.mem_centralizer_iff.2 fun k hk => (hc h hh k hk).symm)

theorem card_sup_le_mul_of_commute [Finite G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  let φ : H × K → ↥(H ⊔ K) := fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ ((H : Set G) * (K : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K (le_normalizer_of_commute hc)]
      exact hz
    obtain ⟨p, hp, q, hq, rfl⟩ := hz'
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_surjective φ hsurj

@[expose] def sec66Fam (U Tb P : Subgroup G) : Fin 3 → Subgroup G := ![U, Tb, P]

@[expose] def sec66Q (U Tb P : Subgroup G) : Subgroup G :=
  ⨆ j, ⨅ i, normIn (sec66Fam U Tb P j) (sec66Fam U Tb P i)

theorem iSup_fin_three (f : Fin 3 → Subgroup G) : ⨆ i, f i = f 0 ⊔ f 1 ⊔ f 2 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · exact sup_le (sup_le (le_iSup f 0) (le_iSup f 1)) (le_iSup f 2)

theorem iSup_sec66Fam (U Tb P : Subgroup G) : ⨆ i, sec66Fam U Tb P i = U ⊔ Tb ⊔ P :=
  iSup_fin_three _

section Basic

variable {U Tb P : Subgroup G} {y y' : G} {q : ℕ}

theorem sec66Q_eq (U Tb P : Subgroup G) : sec66Q U Tb P =
    (⨅ i, normIn U (sec66Fam U Tb P i)) ⊔ (⨅ i, normIn Tb (sec66Fam U Tb P i)) ⊔
      (⨅ i, normIn P (sec66Fam U Tb P i)) :=
  iSup_fin_three (fun j => ⨅ i, normIn (sec66Fam U Tb P j) (sec66Fam U Tb P i))

theorem famF_zero (U Tb P : Subgroup G) :
    (⨅ i, normIn U (sec66Fam U Tb P i)) = normIn U Tb ⊓ normIn U P := by
  apply le_antisymm
  · exact le_inf (iInf_le (fun i => normIn U (sec66Fam U Tb P i)) 1)
      (iInf_le (fun i => normIn U (sec66Fam U Tb P i)) 2)
  · refine le_iInf fun i => ?_
    fin_cases i
    · intro x hx
      exact mem_normIn.2 ⟨normIn_le _ _ hx.1, Subgroup.le_normalizer (normIn_le _ _ hx.1)⟩
    · exact inf_le_left
    · exact inf_le_right

theorem Sec66Cfg.y_mem_famF (c : Sec66Cfg U Tb P y y' q) :
    y ∈ ⨅ i, normIn Tb (sec66Fam U Tb P i) := by
  refine Subgroup.mem_iInf.2 fun i => ?_
  fin_cases i
  · exact mem_normIn.2 ⟨c.yB, c.yU⟩
  · exact mem_normIn.2 ⟨c.yB, Subgroup.le_normalizer c.yB⟩
  · exact mem_normIn.2 ⟨c.yB, c.yP⟩

theorem Sec66Cfg.y'_mem_famF (c : Sec66Cfg U Tb P y y' q) :
    y' ∈ ⨅ i, normIn P (sec66Fam U Tb P i) := by
  refine Subgroup.mem_iInf.2 fun i => ?_
  fin_cases i
  · exact mem_normIn.2 ⟨c.y'P, c.y'U⟩
  · exact mem_normIn.2 ⟨c.y'P, c.y'B⟩
  · exact mem_normIn.2 ⟨c.y'P, Subgroup.le_normalizer c.y'P⟩

theorem Sec66Cfg.y_mem_Q (c : Sec66Cfg U Tb P y y' q) : y ∈ sec66Q U Tb P := by
  rw [sec66Q_eq]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right c.y_mem_famF)

theorem Sec66Cfg.y'_mem_Q (c : Sec66Cfg U Tb P y y' q) : y' ∈ sec66Q U Tb P := by
  rw [sec66Q_eq]
  exact Subgroup.mem_sup_right c.y'_mem_famF

end Basic

end CFSG.CGT.Timmesfeld75
