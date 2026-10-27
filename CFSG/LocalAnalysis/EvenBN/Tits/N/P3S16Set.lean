module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16Gen
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S17

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section S16Set

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem Cv_le_Hg : Cv d ≤ Hg d := Subgroup.centralizer_le_normalizer _

theorem t_mul_Cv_mul_inv (h49 : d.Thm49Statement) (hd : d.Hyp) {k : G} (hk : k ∈ Cv d) :
    d.t * k * d.t⁻¹ ∈ Cv d := by
  have htN : d.t ∈ normalizer (d.s56V : Set G) := t_mem_Hg h49 hd
  rw [Cv_eq, Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : d.t⁻¹ * v * d.t ∈ d.s56V := (mem_normalizer_iff''.1 htN v).1 hv
  have hc := Subgroup.mem_centralizer_iff.1 hk _ hv'
  calc v * (d.t * k * d.t⁻¹) = d.t * ((d.t⁻¹ * v * d.t) * k) * d.t⁻¹ := by group
    _ = d.t * (k * (d.t⁻¹ * v * d.t)) * d.t⁻¹ := by rw [hc]
    _ = d.t * k * d.t⁻¹ * v := by group

theorem t_not_mem_Cv (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) : d.t ∉ Cv d := by
  intro h
  exact star_t_ne h49 hd hz ((actFun_eq_one_iff d.s56V (t_mem_Hg h49 hd)).2 h)

theorem E_eq_V_inf_Ct (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.E = d.s56V ⊓ centralizer ({d.t} : Set G) := by
  refine le_antisymm (fun e he => ⟨hd.s56_E_le_V h49 he,
    mem_centralizer_singleton_iff.2 (hd.L_comm_t (d.liftSub_le _ he))⟩) (fun v hv => ?_)
  rw [← CMt_inf_V h49 hd]
  exact ⟨mem_inf.2 ⟨V_le_M hv.1, hv.2⟩, hv.1⟩

theorem Hg_inf_centralizer_le_CMt (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Hg d ⊓ centralizer ({d.t} : Set G) ≤ CMt d := by
  rintro h ⟨hH, hC⟩
  have hht : h * d.t = d.t * h := mem_centralizer_singleton_iff.1 hC
  have hE : h ∈ normalizer (d.E : Set G) := by
    rw [E_eq_V_inf_Ct h49 hd]
    exact mem_normalizer_inf hH (Subgroup.le_normalizer (mem_centralizer_singleton_iff.2 hht))
  have ht : h ∈ normalizer ((zpowers d.t : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun g hg => ?_)
    obtain ⟨n, rfl⟩ := hg
    exact (Commute.zpow_left (show Commute d.t h from hht.symm) n).eq
  exact ⟨mem_normalizer_sup hE ht, hC⟩

theorem t_mem_OrbSet (S : Subgroup G) : d.t ∈ OrbSet d S :=
  ⟨⟨1, one_mem _, by group⟩, 1, one_mem _, by group⟩

theorem OrbSet_facts (hd : d.Hyp) {S : Subgroup G} {x : G} (hx : x ∈ OrbSet d S) :
    x * x = 1 ∧ ∃ s ∈ S, x = s * d.t := by
  obtain ⟨⟨h, -, rfl⟩, hs⟩ := hx
  refine ⟨?_, hs⟩
  calc h * d.t * h⁻¹ * (h * d.t * h⁻¹) = h * (d.t * d.t) * h⁻¹ := by group
    _ = 1 := by rw [hd.t_mul_self]; group

theorem part_a (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (Cv d)) (hSt : ∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S)
    (htrans : Trans S (OrbSet d S)) :
    img d (Hg d ⊓ centralizer ({d.t} : Set G)) = centralizer ({star d d.t} : Set _) ⊓ Hs d := by
  refine le_antisymm ?_ ?_
  ·
    exact imgIn_inf_centralizer_le d.s56V (Hg d) d.t
  ·
    have ht2 := hd.t_mul_self
    have htK := t_not_mem_Cv h49 hd hz
    have htN := fun k (hk : k ∈ Cv d) => t_mul_Cv_mul_inv h49 hd hk
    have key := centralizer_act_le_imgIn_of_transitive d.s56V (t_mem_Hg h49 hd) (by
      intro h hhN hc
      have hu2 : h * d.t * h⁻¹ * (h * d.t * h⁻¹) = 1 := by
        calc h * d.t * h⁻¹ * (h * d.t * h⁻¹) = h * (d.t * d.t) * h⁻¹ := by group
          _ = 1 := by rw [ht2]; group
      have hc' : (h * d.t * h⁻¹)⁻¹ * d.t ∈ Cv d := hc
      have hu : ∃ k ∈ Cv d, h * d.t * h⁻¹ = k * d.t := by
        refine ⟨d.t * ((h * d.t * h⁻¹)⁻¹ * d.t)⁻¹ * d.t⁻¹, htN _ (inv_mem hc'), ?_⟩
        group
      obtain ⟨k, hk, s, hs, hks⟩ := exists_conj_mem_St hS hSt ht2 htK htN hu2 hu
      have hxO : s * d.t ∈ OrbSet d S :=
        ⟨⟨k * h, mul_mem (Cv_le_Hg hk) hhN, by rw [← hks]; group⟩, s, hs, rfl⟩
      obtain ⟨s', hs', hs't⟩ := htrans d.t (t_mem_OrbSet S) _ hxO
      have hs'K : s' ∈ Cv d := hS.1 hs'
      refine ⟨s'⁻¹ * k, mul_mem (inv_mem hs'K) hk, ?_⟩
      calc s'⁻¹ * k * (h * d.t * h⁻¹) * (s'⁻¹ * k)⁻¹
          = s'⁻¹ * (k * (h * d.t * h⁻¹) * k⁻¹) * s' := by group
        _ = s'⁻¹ * (s * d.t) * s' := by rw [hks]
        _ = s'⁻¹ * (s' * d.t * s'⁻¹) * s' := by rw [hs't]
        _ = d.t := by group)
    intro x hx
    have hx' := key hx
    rw [← imgIn_inf_normalizer, inf_comm] at hx'
    exact hx'

end S16Set

end CFSG.LocalAnalysis.EvenBN.Tits.N
