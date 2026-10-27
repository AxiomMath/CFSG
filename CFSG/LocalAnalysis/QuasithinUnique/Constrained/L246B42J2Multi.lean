module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr

public section

namespace CFSG.QuasithinUnique.Bridge.J2Excl

open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Multi

variable {n : ℕ} {K : Subgroup (Equiv.Perm (Fin n))} {gens : List PArr}

@[expose] def multiConjCheck (n : ℕ) (gens : List PArr) (ts : List PArr) (ws : List (List ℤ))
    (prog : List (ℤ × ℤ)) (targets : List (Array ℕ)) : Bool :=
  let regs := pRun n (ws.flatMap fun w => ts.map fun t => pConj n (pWord n gens w) t) prog
  targets.all fun A => regs.any fun r => eqA n r.1 A

theorem exists_conjugators_multi (hK : RegIn n K gens) {ts : List PArr}
    {T : Set (Equiv.Perm (Fin n))} (hts : ∀ t ∈ ts, ∃ τ ∈ T, PRep n t τ) :
    ∀ ws : List (List ℤ), ∃ gs : List (Equiv.Perm (Fin n)), gs.length = ws.length ∧
      (∀ g ∈ gs, g ∈ K) ∧
      ∀ r ∈ ws.flatMap (fun w => ts.map fun t => pConj n (pWord n gens w) t),
        ∃ y ∈ conjSet gs T, PRep n r y := by
  intro ws
  induction ws with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons w ws ih =>
    obtain ⟨gs, hlen, hgs, hr⟩ := ih
    obtain ⟨g, hg, hrep⟩ := hK.word w
    refine ⟨g :: gs, by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hg
      · exact hgs x hx
    · intro r hr'
      rw [List.flatMap_cons, List.mem_append] at hr'
      rcases hr' with hr' | hr'
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hr'
        obtain ⟨τ, hτ, htτ⟩ := hts t ht
        exact ⟨g * τ * g⁻¹, ⟨g, List.mem_cons_self, τ, hτ, rfl⟩, (hrep.mul htτ).mul hrep.inv⟩
      · obtain ⟨y, ⟨c, hc, t, ht, rfl⟩, hy⟩ := hr r hr'
        exact ⟨c * t * c⁻¹, ⟨c, List.mem_cons_of_mem _ hc, t, ht, rfl⟩, hy⟩

theorem multiConj_sound (hK : RegIn n K gens) {ts : List PArr} {T : Set (Equiv.Perm (Fin n))}
    (hts : ∀ t ∈ ts, ∃ τ ∈ T, PRep n t τ) {ws : List (List ℤ)} {prog : List (ℤ × ℤ)}
    {targets : List (Array ℕ)} (hc : multiConjCheck n gens ts ws prog targets = true) :
    ∃ gs : List (Equiv.Perm (Fin n)), gs.length = ws.length ∧ (∀ g ∈ gs, g ∈ K) ∧
      ∀ A ∈ targets, ∀ a : Equiv.Perm (Fin n), Rep n A a →
        a ∈ Subgroup.closure (conjSet gs T) := by
  obtain ⟨gs, hlen, hgs, hr⟩ := exists_conjugators_multi hK hts ws
  refine ⟨gs, hlen, hgs, fun A hA a hAa => ?_⟩
  set K' : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure (conjSet gs T) with hK'
  have hreg : RegIn n K'
      (ws.flatMap fun w => ts.map fun t => pConj n (pWord n gens w) t) := by
    intro r hr0
    obtain ⟨y, hy, hrep⟩ := hr r hr0
    exact ⟨y, Subgroup.subset_closure hy, hrep⟩
  have hrun := hreg.run prog
  simp only [multiConjCheck, List.all_eq_true, List.any_eq_true] at hc
  obtain ⟨r, hrmem, hrA⟩ := hc A hA
  obtain ⟨g', hg', hrep⟩ := hrun r hrmem
  have : g' = a := (eqA_iff hrep.1 hAa).1 hrA
  rw [← this]
  exact hg'

end Multi

end CFSG.QuasithinUnique.Bridge.J2Excl
