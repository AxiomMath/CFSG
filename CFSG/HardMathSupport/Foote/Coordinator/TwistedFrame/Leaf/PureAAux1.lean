module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PureAAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped commutatorElement

set_option linter.unusedSectionVars false

@[expose] def DichData (τ : Tag) : Prop :=
  (∀ β ∈ rootFinset τ, (β (iθ τ) = 0 ∨ β (iθ τ) = 1) →
      highRoot τ ≠ β ∧ highRoot τ ≠ -β ∧
      ∀ q ∈ commCandidates, q.1 • highRoot τ + q.2 • β ∉ rootFinset τ) ∧
  (∀ β ∈ rootFinset τ, iform β β = iform (highRoot τ) (highRoot τ) → β (iθ τ) = -1 →
      highRoot τ ≠ β ∧ highRoot τ ≠ -β ∧
      (∀ q ∈ commCandidates, q ≠ (1, 1) → q.1 • highRoot τ + q.2 • β ∉ rootFinset τ) ∧
      highRoot τ + β ∈ rootFinset τ) ∧
  (∀ β ∈ rootFinset τ, -2 ≤ β (iθ τ) ∧ β (iθ τ) ≤ 2) ∧
  (∀ β ∈ rootFinset τ, β (iθ τ) = 2 → β = highRoot τ) ∧
  (∀ β ∈ rootFinset τ, β (iθ τ) = -2 → β = -highRoot τ) ∧
  highRoot τ (iθ τ) = 2

theorem conjSub_sup {G : Type*} [Group G] (g : G) (A B : Subgroup G) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B := by
  unfold conjSub
  rw [Subgroup.map_sup]


section Dichotomy

variable {τ : Tag} (hdat : DichData τ) (K : Type) [Field K]

include hdat

theorem commute_theta_pinnedX {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hd : β (iθ τ) = 0 ∨ β (iθ τ) = 1) (s t : K) :
    Commute (pinnedX τ K (highRoot τ) s) (pinnedX τ K β t) := by
  obtain ⟨hne, hne', hnil⟩ := hdat.1 β (mem_rootFinset.2 hβ) hd
  refine Heis.commute_pinnedX_of_commPairs_nil τ K (isRoot_highRoot τ) hβ hne hne' ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact hnil p hp.1 (mem_rootFinset.2 hp.2)

theorem commute_Uθ_conjSub {p : ModGL τ K} (hp : p ∈ Pθ τ K) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hd : β (iθ τ) = 0 ∨ β (iθ τ) = 1) :
    ∀ x ∈ Uθ τ K, ∀ y ∈ conjSub p (rootSubgroup τ K β), x * y = y * x := by
  intro x hx y hy
  have hpn := Pθ_le_normalizer_Uθ τ K (inv_mem hp)
  have hx' : p⁻¹ * x * p ∈ Uθ τ K := by
    have := (Subgroup.mem_normalizer_iff.1 hpn x).1 hx
    simpa using this
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hx'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hy)
  have hc := (commute_theta_pinnedX hdat K hβ hd s t).eq
  rw [hs, ht] at hc
  calc x * y = p * ((p⁻¹ * x * p) * (p⁻¹ * y * p)) * p⁻¹ := by group
    _ = p * ((p⁻¹ * y * p) * (p⁻¹ * x * p)) * p⁻¹ := by rw [hc]
    _ = y * x := by group

theorem comm_mem_Qθ {p : ModGL τ K} (hp : p ∈ Pθ τ K) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hlong : IsLongRoot τ β) (hd : -1 ≤ β (iθ τ)) :
    ∀ u ∈ Uθ τ K, ∀ d ∈ conjSub p (rootSubgroup τ K β), ⁅u, d⁆ ∈ Qθ τ K := by
  intro u hu d hd'
  have hb := hdat.2.2.1 β (mem_rootFinset.2 hβ)
  by_cases h01 : β (iθ τ) = 0 ∨ β (iθ τ) = 1
  · have hc := commute_Uθ_conjSub hdat K hp hβ h01 u hu d hd'
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
    exact one_mem _
  by_cases h2 : β (iθ τ) = 2
  · have hθ : β = highRoot τ := hdat.2.2.2.1 β (mem_rootFinset.2 hβ) h2
    subst hθ
    have hD : conjSub p (rootSubgroup τ K (highRoot τ)) = Uθ τ K :=
      Heis.conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ τ K hp)
    rw [hD] at hd'
    obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hu
    obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hd'
    have hc : pinnedX τ K (highRoot τ) s * pinnedX τ K (highRoot τ) t =
        pinnedX τ K (highRoot τ) t * pinnedX τ K (highRoot τ) s := by
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
    exact one_mem _
  have h1 : β (iθ τ) = -1 := by omega
  obtain ⟨hne, hne', hcand, hθβ⟩ := hdat.2.1 β (mem_rootFinset.2 hβ) hlong h1
  have hpn := Pθ_le_normalizer_Uθ τ K (inv_mem hp)
  have hu' : p⁻¹ * u * p ∈ Uθ τ K := by
    have := (Subgroup.mem_normalizer_iff.1 hpn u).1 hu
    simpa using this
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hd')
  obtain ⟨-, -, -, -, hF⟩ := root_commutator_formula.{0} τ (isRoot_highRoot τ) hβ hne hne'
  have hF' := hF K s t
  have hpairs : commPairs τ (highRoot τ) β = [(1, 1)] := by
    refine list_eq_singleton_of_forall_eq (fun q hq => ?_) (commPairs_nodup _ _) ?_
    · rw [mem_commPairs] at hq
      by_contra hne1
      exact hcand q hq.1 hne1 (mem_rootFinset.2 hq.2)
    · rw [mem_commPairs]
      refine ⟨by decide, ?_⟩
      simpa using mem_rootFinset.1 hθβ
  rw [hpairs] at hF'
  obtain ⟨w, hw⟩ : ∃ w : K, pinnedX τ K (highRoot τ) s * pinnedX τ K β t *
      pinnedX τ K (highRoot τ) (-s) * pinnedX τ K β (-t) = pinnedX τ K (highRoot τ + β) w :=
    ⟨_, by simpa using hF'⟩
  have hβ2 : IsRoot τ (highRoot τ + β) := mem_rootFinset.1 hθβ
  have hdeg : (highRoot τ + β) (iθ τ) = 1 := by
    show highRoot τ (iθ τ) + β (iθ τ) = 1
    rw [hdat.2.2.2.2.2, h1]
    norm_num
  have hu_eq : u = p * pinnedX τ K (highRoot τ) s * p⁻¹ := by rw [hs]; group
  have hd_eq : d = p * pinnedX τ K β t * p⁻¹ := by rw [ht]; group
  have hcc : ⁅u, d⁆ = p * pinnedX τ K (highRoot τ + β) w * p⁻¹ := by
    rw [← hw, commutatorElement_def, hu_eq, hd_eq, ← pinnedX_neg, ← pinnedX_neg]
    group
  have hQconj : ∀ q ∈ Qθ τ K, p * q * p⁻¹ ∈ Qθ τ K := fun q hq =>
    (Subgroup.mem_normalizer_iff.1 (Pθ_le_normalizer_Qθ τ K hp) q).1 hq
  rw [hcc]
  exact hQconj _ (pinnedX_mem_Qθ_of_mem_Deg1 (⟨hβ2, hdeg⟩ : highRoot τ + β ∈ Deg1 τ) w)

theorem exists_swap :
    ∃ m₀ ∈ Uθ τ K ⊔ Heis.Uneg τ K, conjSub m₀ (Uθ τ K) = Heis.Uneg τ K := by
  set ρ := rootSL2 τ K (highRoot τ) with hρ
  set m₀ : ModGL τ K := ρ (nSL (1 : Kˣ)) with hm₀
  have hsw : ∀ z : K, m₀ * ρ (uSL z) * m₀⁻¹ = ρ (vSL (-z)) := by
    intro z
    have h := nSL_mul_uSL (K := K) (1 : Kˣ) z
    have h' : m₀ * ρ (uSL z) = ρ (vSL (-z)) * m₀ := by
      rw [hm₀, ← map_mul, ← map_mul, h]
      simp
    calc m₀ * ρ (uSL z) * m₀⁻¹ = (ρ (vSL (-z)) * m₀) * m₀⁻¹ := by rw [h']
      _ = ρ (vSL (-z)) := by group
  have hU : ∀ z : K, ∃ c : K, ρ (uSL z) = pinnedX τ K (highRoot τ) c :=
    fun z => ⟨_, rootSL2_uSL_eq _ z⟩
  have hU' : ∀ c : K, ∃ z : K, pinnedX τ K (highRoot τ) c = ρ (uSL z) := by
    intro c
    refine ⟨(pinnedData τ (highRoot τ)).2.2 • c, ?_⟩
    rw [hρ, rootSL2_uSL_eq]
    congr 1
    rcases pinnedSign_eq τ (highRoot τ) with h | h <;> rw [h] <;> simp
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) (isRoot_highRoot τ)
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, zero_mul] at hε; exact zero_ne_one hε
  have hV : ∀ z : K, ∃ e : K, ρ (vSL z) = pinnedX τ K (-highRoot τ) e :=
    fun z => ⟨_, hv z⟩
  have hV' : ∀ e : K, ∃ z : K, pinnedX τ K (-highRoot τ) e = ρ (vSL z) := by
    intro e
    refine ⟨ε⁻¹ * e, ?_⟩
    rw [hρ, hv, ← mul_assoc, mul_inv_cancel₀ hε0, one_mul]
  have hconj : conjSub m₀ (Uθ τ K) = Heis.Uneg τ K := by
    ext x
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
  refine ⟨m₀, ?_, hconj⟩
  have : m₀ ∈ (rootSL2 τ K (highRoot τ)).range := ⟨_, rfl⟩
  rwa [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (isRoot_highRoot τ)] at this

theorem theta_dichotomy {D : Subgroup (ModGL τ K)} (hD : IsLongRootSubgroup τ K D) :
    (∀ u ∈ Uθ τ K, ∀ d ∈ D, ⁅u, d⁆ ∈ Qθ τ K) ∨
      ∃ m ∈ Uθ τ K ⊔ D, conjSub m (Uθ τ K) = D := by
  obtain ⟨g, hg, rfl⟩ := hD
  obtain ⟨p, hp, β, hβ, ⟨w, hw⟩, hgβ⟩ := Heis.exists_normalForm τ K hg
  rw [hgβ]
  have hlong : IsLongRoot τ β := by
    rw [hw]
    exact Heis.isLongRoot_smul_highRoot τ w
  have hb := hdat.2.2.1 β (mem_rootFinset.2 hβ)
  by_cases hneg : β (iθ τ) = -2
  · right
    have hβe : β = -highRoot τ := hdat.2.2.2.2.1 β (mem_rootFinset.2 hβ) hneg
    subst hβe
    obtain ⟨q, hq, hpq⟩ := Heis.exists_conjSub_Pθ_Uneg τ K hp
    have hqP : q ∈ Pθ τ K := Qθ_le_Pθ τ K hq
    have hqU : conjSub q (Uθ τ K) = Uθ τ K :=
      Heis.conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ τ K hqP)
    have hqU' : conjSub q⁻¹ (Uθ τ K) = Uθ τ K :=
      Heis.conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ τ K (inv_mem hqP))
    obtain ⟨m₀, hm₀mem, hconj⟩ := exists_swap hdat K
    refine ⟨q * m₀ * q⁻¹, ?_, ?_⟩
    · have h1 : q * m₀ * q⁻¹ ∈ conjSub q (Uθ τ K ⊔ Heis.Uneg τ K) := by
        rw [mem_conjSub_iff]
        have e : q⁻¹ * (q * m₀ * q⁻¹) * q = m₀ := by group
        rw [e]
        exact hm₀mem
      rw [conjSub_sup, hqU] at h1
      have hpq' : conjSub p (rootSubgroup τ K (-highRoot τ)) =
          conjSub q (Heis.Uneg τ K) := hpq
      rw [hpq']
      exact h1
    · have hpq' : conjSub p (rootSubgroup τ K (-highRoot τ)) =
          conjSub q (Heis.Uneg τ K) := hpq
      rw [hpq']
      calc conjSub (q * m₀ * q⁻¹) (Uθ τ K)
          = conjSub q (conjSub m₀ (conjSub q⁻¹ (Uθ τ K))) := by
            rw [conjSub_mul, conjSub_mul]
        _ = conjSub q (conjSub m₀ (Uθ τ K)) := by rw [hqU']
        _ = conjSub q (Heis.Uneg τ K) := by rw [hconj]
  · left
    exact comm_mem_Qθ hdat K hp hβ hlong (by omega)

theorem mirror_dichotomy {m₀ : ModGL τ K} (hm₀ : m₀ ∈ adjointGroup τ K)
    (hconj : conjSub m₀ (Uθ τ K) = Heis.Uneg τ K)
    {B : Subgroup (ModGL τ K)} (hB : IsLongRootSubgroup τ K B) :
    (∀ u ∈ Heis.Uneg τ K, ∀ d ∈ B, ⁅u, d⁆ ∈ conjSub m₀ (Qθ τ K)) ∨
      ∃ m ∈ Heis.Uneg τ K ⊔ B, conjSub m (Heis.Uneg τ K) = B := by
  obtain ⟨g, hg, rfl⟩ := hB
  have hD : IsLongRootSubgroup τ K (conjSub (m₀⁻¹ * g) (Uθ τ K)) :=
    ⟨m₀⁻¹ * g, mul_mem (inv_mem hm₀) hg, rfl⟩
  have hBD : conjSub g (Uθ τ K) = conjSub m₀ (conjSub (m₀⁻¹ * g) (Uθ τ K)) := by
    rw [← conjSub_mul, mul_inv_cancel_left]
  rcases theta_dichotomy hdat K hD with h | ⟨m, hm, hmD⟩
  · left
    intro u hu d hd
    rw [← hconj] at hu
    have hu' : m₀⁻¹ * u * m₀ ∈ Uθ τ K := mem_conjSub_iff.1 hu
    have hd' : m₀⁻¹ * d * m₀ ∈ conjSub (m₀⁻¹ * g) (Uθ τ K) := by
      rw [hBD] at hd
      exact mem_conjSub_iff.1 hd
    have := h _ hu' _ hd'
    rw [mem_conjSub_iff]
    have e : m₀⁻¹ * ⁅u, d⁆ * m₀ = ⁅m₀⁻¹ * u * m₀, m₀⁻¹ * d * m₀⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact this
  · right
    refine ⟨m₀ * m * m₀⁻¹, ?_, ?_⟩
    · have h1 : m₀ * m * m₀⁻¹ ∈ conjSub m₀ (Uθ τ K ⊔ conjSub (m₀⁻¹ * g) (Uθ τ K)) := by
        rw [mem_conjSub_iff]
        have e : m₀⁻¹ * (m₀ * m * m₀⁻¹) * m₀ = m := by group
        rw [e]
        exact hm
      rw [conjSub_sup, hconj, ← hBD] at h1
      exact h1
    · rw [hBD, ← hconj]
      calc conjSub (m₀ * m * m₀⁻¹) (conjSub m₀ (Uθ τ K))
          = conjSub m₀ (conjSub m (Uθ τ K)) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub m₀ (conjSub (m₀⁻¹ * g) (Uθ τ K)) := by rw [hmD]

end Dichotomy

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PureAAux
