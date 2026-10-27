module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PureD4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem hr7 : (highRoot Tag.E8) 7 = 2 := by
  rw [← theta_eq]
  decide +kernel

theorem isRoot_hr : IsRoot Tag.E8 (highRoot Tag.E8) := isRoot_highRoot Tag.E8

theorem commute_Uθ_rootSubgroup (K : Type) [Field K] {β : Fin Tag.E8.rank → ℤ}
    (hβ : IsRoot Tag.E8 β) (hd : β 7 = 0 ∨ β 7 = 1) (s t : K) :
    Commute (pinnedX Tag.E8 K (highRoot Tag.E8) s) (pinnedX Tag.E8 K β t) := by
  rw [← theta_eq]
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg β (mem_rootFinset.2 hβ) hd
  refine Heis.commute_pinnedX_of_commPairs_nil Tag.E8 K (mem_rootFinset.1 theta_mem) hβ hne hne'
    ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact commCandidates_theta_data β (mem_rootFinset.2 hβ) hd p hp.1 (mem_rootFinset.2 hp.2)

theorem commute_Uθ_conjSub (K : Type) [Field K] {p : ModGL Tag.E8 K} (hp : p ∈ Pθ Tag.E8 K)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (hd : β 7 = 0 ∨ β 7 = 1) :
    ∀ x ∈ Uθ Tag.E8 K, ∀ y ∈ conjSub p (rootSubgroup Tag.E8 K β), x * y = y * x := by
  intro x hx y hy
  have hpn := Pθ_le_normalizer_Uθ Tag.E8 K (inv_mem hp)
  have hx' : p⁻¹ * x * p ∈ Uθ Tag.E8 K := by
    have := (Subgroup.mem_normalizer_iff.1 hpn x).1 hx
    simpa using this
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hx'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hy)
  have hc := (commute_Uθ_rootSubgroup K hβ hd s t).eq
  have hs' : pinnedX Tag.E8 K (highRoot Tag.E8) s = p⁻¹ * x * p := hs
  rw [hs', ht] at hc
  calc x * y = p * ((p⁻¹ * x * p) * (p⁻¹ * y * p)) * p⁻¹ := by group
    _ = p * ((p⁻¹ * y * p) * (p⁻¹ * x * p)) * p⁻¹ := by rw [hc]
    _ = y * x := by group

theorem comm_mem_Qθ (K : Type) [Field K] {p : ModGL Tag.E8 K} (hp : p ∈ Pθ Tag.E8 K)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (hd : -1 ≤ β 7) :
    ∀ u ∈ Uθ Tag.E8 K, ∀ d ∈ conjSub p (rootSubgroup Tag.E8 K β), ⁅u, d⁆ ∈ Qθ Tag.E8 K := by
  intro u hu d hd'
  have hb := deg_bounds β (mem_rootFinset.2 hβ)
  by_cases h01 : β 7 = 0 ∨ β 7 = 1
  · have hc := commute_Uθ_conjSub K hp hβ h01 u hu d hd'
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
    exact one_mem _
  by_cases h2 : β 7 = 2
  · have hθ : β = highRoot Tag.E8 := by
      rw [← theta_eq]; exact deg_eq_two β (mem_rootFinset.2 hβ) h2
    subst hθ
    have hD : conjSub p (rootSubgroup Tag.E8 K (highRoot Tag.E8)) = Uθ Tag.E8 K :=
      Heis.conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.E8 K hp)
    rw [hD] at hd'
    obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hu
    obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hd'
    have hc : pinnedX Tag.E8 K (highRoot Tag.E8) s * pinnedX Tag.E8 K (highRoot Tag.E8) t =
        pinnedX Tag.E8 K (highRoot Tag.E8) t * pinnedX Tag.E8 K (highRoot Tag.E8) s := by
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
    exact one_mem _
  have h1 : β 7 = -1 := by omega
  have hne : highRoot Tag.E8 ≠ β := by
    intro h
    have h7 := congrArg (fun x : Fin Tag.E8.rank → ℤ => x 7) h
    simp only [hr7] at h7
    omega
  have hne' : highRoot Tag.E8 ≠ -β := by
    intro h
    have h7 := congrArg (fun x : Fin Tag.E8.rank → ℤ => x 7) h
    simp only [hr7, Pi.neg_apply] at h7
    omega
  have hpn := Pθ_le_normalizer_Uθ Tag.E8 K (inv_mem hp)
  have hu' : p⁻¹ * u * p ∈ Uθ Tag.E8 K := by
    have := (Subgroup.mem_normalizer_iff.1 hpn u).1 hu
    simpa using this
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hd')
  have hu_eq : u = p * pinnedX Tag.E8 K (highRoot Tag.E8) s * p⁻¹ := by rw [hs]; group
  have hd_eq : d = p * pinnedX Tag.E8 K β t * p⁻¹ := by rw [ht]; group
  have hcc : ⁅u, d⁆ = p * ⁅pinnedX Tag.E8 K (highRoot Tag.E8) s, pinnedX Tag.E8 K β t⁆ * p⁻¹ := by
    rw [hu_eq, hd_eq]
    simp only [commutatorElement_def]
    group
  have hsl := simply_laced_root_commutator_unit.{0} Tag.E8 (Or.inr (Or.inr (Or.inr rfl)))
    isRoot_hr hβ hne hne'
  have hpQ : p ∈ Subgroup.normalizer (Qθ Tag.E8 K : Set (ModGL Tag.E8 K)) :=
    Pθ_le_normalizer_Qθ Tag.E8 K hp
  have hQconj : ∀ q ∈ Qθ Tag.E8 K, p * q * p⁻¹ ∈ Qθ Tag.E8 K := fun q hq =>
    (Subgroup.mem_normalizer_iff.1 hpQ q).1 hq
  by_cases hr : IsRoot Tag.E8 (highRoot Tag.E8 + β)
  · obtain ⟨-, hF⟩ := hsl.1 hr
    obtain ⟨W, hW⟩ : ∃ W : K, ⁅pinnedX Tag.E8 K (highRoot Tag.E8) s, pinnedX Tag.E8 K β t⁆ =
        pinnedX Tag.E8 K (highRoot Tag.E8 + β) W := ⟨_, hF K s t⟩
    have hdeg : (highRoot Tag.E8 + β) 7 = 1 := by
      simp only [Pi.add_apply, hr7, h1]
      norm_num
    have hD : highRoot Tag.E8 + β ∈ Deg1 Tag.E8 := ⟨hr, hdeg⟩
    rw [hcc, hW]
    exact hQconj _ (pinnedX_mem_Qθ_of_mem_Deg1 hD W)
  · have hcm := hsl.2 hr K (pinnedX Tag.E8 K (highRoot Tag.E8) s) (mem_rootSubgroup.2 ⟨s, rfl⟩)
      (pinnedX Tag.E8 K β t) (mem_rootSubgroup.2 ⟨t, rfl⟩)
    have hc1 : ⁅pinnedX Tag.E8 K (highRoot Tag.E8) s, pinnedX Tag.E8 K β t⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 hcm.eq
    rw [hcc, hc1]
    simp only [mul_one, mul_inv_cancel]
    exact one_mem _

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley in
theorem exists_weyl_Uθ (K : Type) [Field K] :
    ∃ m₀ ∈ Uθ Tag.E8 K ⊔ Heis.Uneg Tag.E8 K, conjSub m₀ (Uθ Tag.E8 K) = Heis.Uneg Tag.E8 K := by
  set ρ := rootSL2 Tag.E8 K (highRoot Tag.E8) with hρ
  set m₀ : ModGL Tag.E8 K := ρ (nSL (1 : Kˣ)) with hm₀
  have hsw : ∀ z : K, m₀ * ρ (uSL z) * m₀⁻¹ = ρ (vSL (-z)) := by
    intro z
    have h := nSL_mul_uSL (K := K) (1 : Kˣ) z
    have h' : m₀ * ρ (uSL z) = ρ (vSL (-z)) * m₀ := by
      rw [hm₀, ← map_mul, ← map_mul, h]
      simp
    calc m₀ * ρ (uSL z) * m₀⁻¹ = (ρ (vSL (-z)) * m₀) * m₀⁻¹ := by rw [h']
      _ = ρ (vSL (-z)) := by group
  have hU : ∀ z : K, ∃ c : K, ρ (uSL z) = pinnedX Tag.E8 K (highRoot Tag.E8) c :=
    fun z => ⟨_, rootSL2_uSL_eq _ z⟩
  have hU' : ∀ c : K, ∃ z : K, pinnedX Tag.E8 K (highRoot Tag.E8) c = ρ (uSL z) := by
    intro c
    refine ⟨(pinnedData Tag.E8 (highRoot Tag.E8)).2.2 • c, ?_⟩
    rw [hρ, rootSL2_uSL_eq]
    congr 1
    rcases pinnedSign_eq Tag.E8 (highRoot Tag.E8) with h | h <;> rw [h] <;> simp
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) (isRoot_hr)
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, zero_mul] at hε; exact zero_ne_one hε
  have hV : ∀ z : K, ∃ e : K, ρ (vSL z) = pinnedX Tag.E8 K (-highRoot Tag.E8) e :=
    fun z => ⟨_, hv z⟩
  have hV' : ∀ e : K, ∃ z : K, pinnedX Tag.E8 K (-highRoot Tag.E8) e = ρ (vSL z) := by
    intro e
    refine ⟨ε⁻¹ * e, ?_⟩
    rw [hρ, hv, ← mul_assoc, mul_inv_cancel₀ hε0, one_mul]
  refine ⟨m₀, ?_, ?_⟩
  · have : m₀ ∈ (rootSL2 Tag.E8 K (highRoot Tag.E8)).range := ⟨_, rfl⟩
    rwa [range_rootSL2_of_isRoot isRoot_hr] at this
  · ext x
    constructor
    · intro hx
      rw [mem_conjSub_iff] at hx
      obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hx
      obtain ⟨z, hz⟩ := hU' c
      have hx' : x = ρ (vSL (-z)) := by
        calc x = m₀ * (m₀⁻¹ * x * m₀) * m₀⁻¹ := by group
          _ = m₀ * ρ (uSL z) * m₀⁻¹ := by rw [← hc, hz]
          _ = ρ (vSL (-z)) := hsw z
      obtain ⟨e, he⟩ := hV (-z)
      rw [hx', he]
      exact mem_rootSubgroup.2 ⟨e, rfl⟩
    · intro hx
      rw [mem_conjSub_iff]
      obtain ⟨e, he⟩ := mem_rootSubgroup.1 hx
      obtain ⟨z, hz⟩ := hV' e
      have hx' : x = m₀ * ρ (uSL (-z)) * m₀⁻¹ := by
        rw [hsw, neg_neg, ← hz, he]
      have h3 : m₀⁻¹ * x * m₀ = ρ (uSL (-z)) := by
        rw [hx']; group
      rw [h3]
      obtain ⟨c, hc⟩ := hU (-z)
      exact mem_rootSubgroup.2 ⟨c, hc.symm⟩

theorem theta_dichotomy' (K : Type) [Field K] {D : Subgroup (ModGL Tag.E8 K)}
    (hD : IsLongRootSubgroup Tag.E8 K D) :
    (∀ u ∈ Uθ Tag.E8 K, ∀ d ∈ D, ⁅u, d⁆ ∈ Qθ Tag.E8 K) ∨
      ∃ m ∈ Uθ Tag.E8 K ⊔ D, conjSub m (Uθ Tag.E8 K) = D := by
  obtain ⟨g, hg, rfl⟩ := hD
  obtain ⟨p, hp, β, hβ, -, hgβ⟩ := Heis.exists_normalForm Tag.E8 K hg
  rw [hgβ]
  have hb := deg_bounds β (mem_rootFinset.2 hβ)
  by_cases hneg : β 7 = -2
  · right
    have hβe : β = -highRoot Tag.E8 := by
      rw [← theta_eq]; exact deg_eq_neg_two β (mem_rootFinset.2 hβ) hneg
    subst hβe
    obtain ⟨q, hq, hpq⟩ := Heis.exists_conjSub_Pθ_Uneg Tag.E8 K hp
    have hqP : q ∈ Pθ Tag.E8 K := Qθ_le_Pθ Tag.E8 K hq
    have hqU : conjSub q (Uθ Tag.E8 K) = Uθ Tag.E8 K :=
      Heis.conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.E8 K hqP)
    have hqU' : conjSub q⁻¹ (Uθ Tag.E8 K) = Uθ Tag.E8 K :=
      Heis.conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.E8 K (inv_mem hqP))
    obtain ⟨m₀, hm₀mem, hconj⟩ := exists_weyl_Uθ K
    refine ⟨q * m₀ * q⁻¹, ?_, ?_⟩
    · have h1 : q * m₀ * q⁻¹ ∈ conjSub q (Uθ Tag.E8 K ⊔ Heis.Uneg Tag.E8 K) := by
        rw [mem_conjSub_iff]
        have e : q⁻¹ * (q * m₀ * q⁻¹) * q = m₀ := by group
        rw [e]
        exact hm₀mem
      have h2 : conjSub q (Uθ Tag.E8 K ⊔ Heis.Uneg Tag.E8 K) =
          conjSub q (Uθ Tag.E8 K) ⊔ conjSub q (Heis.Uneg Tag.E8 K) := by
        unfold conjSub
        rw [Subgroup.map_sup]
      rw [h2, hqU] at h1
      have hpq' : conjSub p (rootSubgroup Tag.E8 K (-highRoot Tag.E8)) =
          conjSub q (Heis.Uneg Tag.E8 K) := hpq
      rw [hpq']
      exact h1
    · have hpq' : conjSub p (rootSubgroup Tag.E8 K (-highRoot Tag.E8)) =
          conjSub q (Heis.Uneg Tag.E8 K) := hpq
      rw [hpq']
      calc conjSub (q * m₀ * q⁻¹) (Uθ Tag.E8 K)
          = conjSub q (conjSub m₀ (conjSub q⁻¹ (Uθ Tag.E8 K))) := by
            rw [conjSub_mul, conjSub_mul]
        _ = conjSub q (conjSub m₀ (Uθ Tag.E8 K)) := by rw [hqU']
        _ = conjSub q (Heis.Uneg Tag.E8 K) := by rw [hconj]
  · left
    exact comm_mem_Qθ K hp hβ (by omega)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PureD4Aux
