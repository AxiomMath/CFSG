module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Main

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement Pointwise

variable {α : Type} [Fintype α] [DecidableEq α]

theorem step1_odd (p : OddInv α) (h7 : 7 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {E : Subgroup (Perm α)} (hE : IsComponentOf E Y) {S : Set α}
    (hS : ∀ y ∈ Y, ∀ z ∈ S, y z ∈ S) (hω : p.ω ∈ S) (hmove : ∃ e ∈ E, ∃ z ∈ S, e z ≠ z) :
    ∀ e ∈ E, ∀ z, z ∉ S → e z = z := by
  have h5 : 5 ≤ Fintype.card α := by omega
  have hperf : ⁅E, E⁆ = E := quasisimple_comm_eq hE.2.2
  have hWcl : ∀ x ∈ (Sᶜ : Set α), p.μ x ∈ (Sᶜ : Set α) := by
    intro x hx
    rw [Set.mem_compl_iff] at hx ⊢
    intro hmx
    apply hx
    have h1 : x ∈ MulAction.orbit (↥Y) (p.μ x) := by
      have h2 := orbit_mu_mem_odd p h5 hB (p.μ x)
      rwa [p.inv] at h2
    obtain ⟨g, hg⟩ := h1
    have hgx : (g : Perm α) (p.μ x) = x := hg
    have h3 := hS (g : Perm α) g.2 (p.μ x) hmx
    rwa [hgx] at h3
  have hωc : p.ω ∉ (Sᶜ : Set α) := by
    rw [Set.mem_compl_iff, not_not]
    exact hω
  have hEW : ∀ e ∈ E, ∀ x ∈ (Sᶜ : Set α), e x ∈ (Sᶜ : Set α) := by
    intro e he x hx
    rw [Set.mem_compl_iff] at hx ⊢
    intro hex
    apply hx
    have hinv : e⁻¹ ∈ Y := hE.1 (E.inv_mem he)
    have := hS _ hinv _ hex
    rwa [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
  have hsep : ∀ w, w ∉ S → ∀ z ∈ S, z ≠ w ∧ z ≠ p.μ w := by
    intro w hw z hz
    refine ⟨fun h => hw (by rw [← h]; exact hz), fun h => ?_⟩
    have hpm : p.μ w ∈ (Sᶜ : Set α) := hWcl w (Set.mem_compl hw)
    rw [Set.mem_compl_iff] at hpm
    exact hpm (by rw [← h]; exact hz)
  have hσ : ∀ x ∈ (Sᶜ : Set α), ∀ y ∈ (Sᶜ : Set α), y ≠ x → y ≠ p.μ x →
      swap x (p.μ x) * swap y (p.μ y) ∈ Y ⊓ fixOn S := by
    intro x hx y hy hyx hyμ
    rw [Set.mem_compl_iff] at hx hy
    have hxω : x ≠ p.ω := fun h => hx (by rw [h]; exact hω)
    have hyω : y ≠ p.ω := fun h => hy (by rw [h]; exact hω)
    refine Subgroup.mem_inf.mpr ⟨hB x y hxω hyω hyx hyμ, mem_fixOn.mpr fun z hz => ?_⟩
    obtain ⟨hzy, hzμy⟩ := hsep y hy z hz
    obtain ⟨hzx, hzμx⟩ := hsep x hx z hz
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzy hzμy,
      Equiv.swap_apply_of_ne_of_ne hzx hzμx]
  have hcomm : ⁅E, Y ⊓ fixOn S⁆ = ⊥ := by
    rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hE (step1Aux_sub hS) with h | h
    · exfalso
      obtain ⟨e, he, z, hz, hez⟩ := hmove
      exact hez (mem_fixOn.mp (Subgroup.mem_inf.mp (h he)).2 z hz)
    · exact h
  have hcommute : ∀ e ∈ E, ∀ x ∈ (Sᶜ : Set α), ∀ y ∈ (Sᶜ : Set α), y ≠ x → y ≠ p.μ x →
      Commute e (swap x (p.μ x) * swap y (p.μ y)) := by
    intro e he x hx y hy hyx hyμ
    have h1 : ⁅e, swap x (p.μ x) * swap y (p.μ y)⁆ ∈ ⁅E, Y ⊓ fixOn S⁆ :=
      Subgroup.commutator_mem_commutator he (hσ x hx y hy hyx hyμ)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  by_cases hsmall : Nat.card (Sᶜ : Set α) ≤ 4
  · intro e he z hz
    exact perfect_fix_small hperf hsmall hEW e he z hz
  · obtain ⟨r, hr⟩ := even_card_of_closed_odd p (Sᶜ : Set α) hWcl hωc
    have h6 : 6 ≤ Nat.card (Sᶜ : Set α) := by omega
    have hpairs : ∀ e ∈ E, ∀ x ∈ (Sᶜ : Set α), e x = x ∨ e x = p.μ x := fun e he =>
      fix_pairs_of_commute_odd p hWcl hωc h6 (hcommute e he)
    intro e he z hz
    exact perfect_fix_pairs_odd p hperf hpairs hWcl e he z hz

theorem generic_odd (p : OddInv α) (h7 : 7 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {E : Subgroup (Perm α)} (hE : IsComponentOf E Y)
    (hmove : ∃ e ∈ E, e p.ω ≠ p.ω) (hS : MulAction.orbit (↥Y) p.ω ≠ Set.univ) :
    ∃ k, 5 ≤ k ∧ k ≤ Fintype.card α ∧ Nonempty (↥E ≃* alternatingGroup (Fin k)) := by
  classical
  set S : Set α := MulAction.orbit (↥Y) p.ω with hSdef
  have hSinv : ∀ y ∈ Y, ∀ z ∈ S, y z ∈ S := by
    intro y hy z hz
    obtain ⟨g, rfl⟩ := hz
    exact ⟨⟨y, hy⟩ * g, by simp [mul_smul]⟩
  have hωS : p.ω ∈ S := MulAction.mem_orbit_self p.ω
  have hmoveS : ∃ e ∈ E, ∃ z ∈ S, e z ≠ z := by
    obtain ⟨e, he, hne⟩ := hmove
    exact ⟨e, he, p.ω, hωS, hne⟩
  have htriv := step1_odd p h7 hB hE hSinv hωS hmoveS
  have horb_eq : ∀ z ∈ S, MulAction.orbit (↥Y) z = S := fun z hz => MulAction.orbit_eq_iff.2 hz
  have hμS : ∀ z ∈ S, p.μ z ∈ S := by
    intro z hz
    have h1 := orbit_mu_mem_odd p (by omega) hB z
    rwa [horb_eq z hz] at h1
  have hiff : ∀ z, p.μ z ∈ S ↔ z ∈ S := fun z =>
    ⟨fun h => by simpa [p.inv] using hμS _ h, hμS z⟩
  have hinv : ∀ z : ↥S, (p.μ.subtypePerm hiff) ((p.μ.subtypePerm hiff) z) = z := by
    intro z
    ext
    simp [p.inv]
  have hfix : (p.μ.subtypePerm hiff) ⟨p.ω, hωS⟩ = ⟨p.ω, hωS⟩ := Subtype.ext p.fix
  have hfpf : ∀ z : ↥S, z ≠ ⟨p.ω, hωS⟩ → (p.μ.subtypePerm hiff) z ≠ z := by
    intro z hz h
    exact p.fpf z.1 (fun h' => hz (Subtype.ext h')) (congrArg Subtype.val h)
  let q : OddInv ↥S := ⟨p.μ.subtypePerm hiff, ⟨p.ω, hωS⟩, hinv, hfix, hfpf⟩
  let ρ : ↥Y →* Perm ↥S := MulAction.toPermHom ↥Y ↥S
  have hρ : ∀ (g : ↥Y) (t : ↥S), ((ρ g t : ↥S) : α) = (g : Perm α) t := fun g t => rfl
  have hq : ∀ z : ↥S, z ≠ q.ω → swap z (q.μ z) ∈ ρ.range := by
    intro z hzω
    obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
      by_contra h
      push Not at h
      exact hS (Set.eq_univ_of_forall h)
    have hwω : w ≠ p.ω := fun h => hw (h ▸ hωS)
    have hzω' : z.1 ≠ p.ω := fun h => hzω (Subtype.ext h)
    have hwz : w ≠ z.1 := fun h => hw (h ▸ z.2)
    have hwμ : w ≠ p.μ z.1 := fun h => hw (h ▸ hμS z.1 z.2)
    have hμw : p.μ w ∉ S := fun h => hw (by simpa [p.inv] using hμS _ h)
    have hσ : swap z.1 (p.μ z.1) * swap w (p.μ w) ∈ Y := hB z.1 w hzω' hwω hwz hwμ
    refine ⟨⟨_, hσ⟩, ?_⟩
    apply Equiv.ext
    intro t
    apply Subtype.ext
    have h1 : swap w (p.μ w) t.1 = t.1 := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; exact hw (h ▸ t.2)
      · intro h; exact hμw (h ▸ t.2)
    show (swap z.1 (p.μ z.1) * swap w (p.μ w) : Perm α) t.1 = _
    rw [Perm.mul_apply, h1]
    rw [coe_swap_subtype]
    rfl
  let φ : ↥(E.subgroupOf Y) →* Perm ↥S := ρ.comp (E.subgroupOf Y).subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgE : ((g : ↥Y) : Perm α) ∈ E := g.2
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro z
    show ((g : ↥Y) : Perm α) z = z
    by_cases hz : z ∈ S
    · have h2 := congrArg (fun f : Perm ↥S => ((f ⟨z, hz⟩ : ↥S) : α)) hg
      simpa [φ, hρ] using h2
    · exact htriv _ hgE z hz
  have hsubY : IsSubnormal (E.subgroupOf Y) ⊤ := by
    have h := CFSG.Quasithin.A3.subnormal_comap Y.subtype hE.2.1
    rwa [show Y.comap Y.subtype = ⊤ from Subgroup.subgroupOf_self Y] at h
  have hE'sub : IsSubnormal φ.range ρ.range := by
    have h := CFSG.Quasithin.A3.subnormal_map ρ hsubY
    rw [← MonoidHom.range_eq_map] at h
    have hr : φ.range = (E.subgroupOf Y).map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr]
    exact h
  have isoE : ↥E ≃* ↥φ.range :=
    (Subgroup.subgroupOfEquivOfLe hE.1).symm.trans (MonoidHom.ofInjective hφinj)
  have hE' : IsComponentOf φ.range ρ.range :=
    ⟨by rintro _ ⟨g, rfl⟩; exact ⟨(g : ↥Y), rfl⟩, hE'sub,
      open_isQuasisimple_of_mulEquiv isoE hE.2.2⟩
  obtain ⟨C, hC5, hEC⟩ := tc_odd q hq hE'
  refine ⟨C.card, hC5, ?_, ?_⟩
  · calc C.card ≤ Fintype.card ↥S := Finset.card_le_univ C
      _ ≤ Fintype.card α := Fintype.card_subtype_le _
  · obtain ⟨eAlt⟩ := altOn_equiv C
    exact ⟨isoE.trans ((MulEquiv.subgroupCongr hEC).trans (eAlt.trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq (Fintype.card_coe C)))))⟩

theorem structure_component_odd (p : OddInv α) (h9 : 9 ≤ Fintype.card α)
    (hodd : Odd (Fintype.card α)) {Y : Subgroup (Perm α)} (hYA : Y ≤ alternatingGroup α)
    (hB : p.Contained Y) {E : Subgroup (Perm α)} (hE : IsComponentOf E Y)
    (hmove : ∃ e ∈ E, e p.ω ≠ p.ω) :
    ∃ k, 5 ≤ k ∧ k ≤ Fintype.card α ∧ Nonempty (↥E ≃* alternatingGroup (Fin k)) := by
  by_cases h : MulAction.orbit (↥Y) p.ω = Set.univ
  · have htr : MulAction.IsPretransitive (↥Y) α :=
      (MulAction.isPretransitive_iff_orbit_eq_univ p.ω).2 h
    have hle : alternatingGroup α ≤ Y := alt_le_odd p h9 hodd hB htr
    have hYeq : Y = alternatingGroup α := le_antisymm hYA hle
    have hne : E ≠ ⊥ := quasisimple_ne_bot hE.2.2
    have hEsub : CFSG.Open.IsSubnormal E (alternatingGroup α) := by
      rw [← hYeq]
      exact hE.2.1
    have hsimple : IsSimpleGroup ↥(alternatingGroup α) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; omega)
    have hEeq : E = alternatingGroup α := by
      rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hEsub hsimple with h' | h'
      · exact absurd h' hne
      · exact h'
    exact ⟨Fintype.card α, by omega, le_refl _,
      ⟨(MulEquiv.subgroupCongr hEeq).trans (Equiv.altCongrHom (Fintype.equivFin α))⟩⟩
  · exact generic_odd p (by omega) hB hE hmove h

end CFSG.QuasithinUnique.L246C127.AltBig
