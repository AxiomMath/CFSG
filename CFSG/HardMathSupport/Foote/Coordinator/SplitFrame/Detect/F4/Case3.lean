module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Split
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Case3Data
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Transport
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Case3Dichotomy
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Lemma5
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.FZero
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureF4Pair

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Closure

set_option linter.unusedSectionVars false


theorem commPairs_eq_single {α β : Fin Tag.F4.rank → ℤ}
    (h : ∀ p ∈ commCandidates, p.1 • α + p.2 • β ∈ rootFinset .F4 ↔ p = (1, 1)) :
    commPairs .F4 α β = [(1, 1)] := by
  classical
  have hc : ∀ p ∈ commCandidates, decide (IsRoot Tag.F4 (p.1 • α + p.2 • β)) =
      decide (p = (1, 1)) := fun p hp => by
    rw [decide_eq_decide, ← mem_rootFinset (τ := Tag.F4)]
    exact h p hp
  unfold commPairs
  rw [List.filter_congr hc]
  decide

theorem commPairs_eq_nil {α β : Fin Tag.F4.rank → ℤ}
    (h : ∀ p ∈ commCandidates, p.1 • α + p.2 • β ∉ rootFinset .F4) : commPairs .F4 α β = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun p hp => by
    rw [mem_commPairs] at hp
    exact h p hp.1 (mem_rootFinset.2 hp.2)

variable (K : Type) [Field K]

theorem rootSubgroup_le_Qθ {β : Fin Tag.F4.rank → ℤ} (hβ : β ∈ Deg1 Tag.F4) :
    rootSubgroup Tag.F4 K β ≤ Qθ Tag.F4 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨e, rfl⟩
  exact pinnedX_mem_Qθ K hβ e

theorem conjSub_le_Qθ {p : ModGL Tag.F4 K} (hp : p ∈ Pθ Tag.F4 K) {A : Subgroup (ModGL Tag.F4 K)}
    (hA : A ≤ Qθ Tag.F4 K) : conjSub p A ≤ Qθ Tag.F4 K := by
  intro x hx
  have h1 : p⁻¹ * x * p ∈ Qθ Tag.F4 K := hA (mem_conjSub_iff.1 hx)
  have hn := Pθ_le_normalizer_Qθ Tag.F4 K hp
  have h2 := (Subgroup.mem_normalizer_iff.1 hn (p⁻¹ * x * p)).1 h1
  have e : p * (p⁻¹ * x * p) * p⁻¹ = x := by group
  rwa [e] at h2

theorem conjSub_add_le {H : Subgroup (ModGL Tag.F4 K)} {p : ModGL Tag.F4 K}
    {v w : Fin Tag.F4.rank → ℤ} (hv : IsRoot Tag.F4 v) (hw : IsRoot Tag.F4 w) (hne : v ≠ w)
    (hP : commPairs .F4 v w = [(1, 1)]) (hnr : ¬ IsRoot .F4 (w - v))
    (hA : conjSub p (rootSubgroup Tag.F4 K v) ≤ H) (hB : conjSub p (rootSubgroup Tag.F4 K w) ≤ H) :
    conjSub p (rootSubgroup Tag.F4 K (v + w)) ≤ H := by
  have h1 : ∀ x : ModGL Tag.F4 K, ∀ u : Fin Tag.F4.rank → ℤ,
      conjSub p (rootSubgroup Tag.F4 K u) ≤ H → x ∈ rootSubgroup Tag.F4 K u →
        x ∈ conjSub p⁻¹ H := by
    intro x u hu hx
    rw [mem_conjSub_iff, inv_inv]
    have : p * x * p⁻¹ ∈ conjSub p (rootSubgroup Tag.F4 K u) := by
      rw [mem_conjSub_iff]
      have e : p⁻¹ * (p * x * p⁻¹) * p = x := by group
      rw [e]
      exact hx
    exact hu this
  have h2 := rootSubgroup_add_le_single (conjSub p⁻¹ H) hv hw hne hP hnr
    (fun x hx => h1 x v hA hx) (fun x hx => h1 x w hB hx)
  calc conjSub p (rootSubgroup Tag.F4 K (v + w)) ≤ conjSub p (conjSub p⁻¹ H) := conjSub_mono p h2
    _ = H := conjSub_conjSub_inv p H

theorem class_two_conjSub {l : ModGL Tag.F4 K} (hl : l ∈ Pθ Tag.F4 K)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hlong : IsLongRoot Tag.F4 β)
    (hdeg : β 0 = -1) :
    ∀ u ∈ Uθ Tag.F4 K, ∀ d ∈ conjSub l (rootSubgroup Tag.F4 K β),
      Commute (u * d * u⁻¹ * d⁻¹) u := by
  intro u hu d hd
  obtain ⟨⟨hθβ, hθβ0⟩, hnr, hne1, hne2, hne3, hne4, hP, hcomm⟩ :=
    case3_data β (mem_rootFinset.2 hβ) hdeg hlong
  have hθβroot : IsRoot Tag.F4 (theta + β) := mem_rootFinset.1 hθβ
  have hl' := Pθ_le_normalizer_Uθ Tag.F4 K (inv_mem hl)
  have hu' : l⁻¹ * u * l ∈ Uθ Tag.F4 K := by
    have := (Subgroup.mem_normalizer_iff.1 hl' u).1 hu
    simpa using this
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hd)
  obtain ⟨C, -, hF⟩ := exists_pinnedX_commFormula_F4_exact isRoot_theta hβ hne1 hne2
  have h1 := hF K s t
  rw [commPairs_eq_single hP] at h1
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_nsmul,
    pow_one] at h1
  rw [← pinnedX_neg Tag.F4 K theta s, ← pinnedX_neg Tag.F4 K β t] at h1
  have hy : Commute (pinnedX Tag.F4 K (theta + β) (((C (1, 1) : ℤ) : K) * s * t))
      (pinnedX Tag.F4 K theta s) :=
    commute_pinnedX_of_commPairs_nil Tag.F4 K hθβroot isRoot_theta hne3 hne4
      (commPairs_eq_nil hcomm) _ _
  have hs' : pinnedX Tag.F4 K theta s = l⁻¹ * u * l := hs
  have ht' : pinnedX Tag.F4 K β t = l⁻¹ * d * l := ht
  rw [hs', ht'] at h1
  rw [hs'] at hy
  have e : u * d * u⁻¹ * d⁻¹ = l * (l⁻¹ * u * l * (l⁻¹ * d * l) * (l⁻¹ * u * l)⁻¹ *
      (l⁻¹ * d * l)⁻¹) * l⁻¹ := by group
  rw [e, h1]
  have e2 : u = l * (l⁻¹ * u * l) * l⁻¹ := by group
  show (l * pinnedX Tag.F4 K (theta + β) (((C (1, 1) : ℤ) : K) * s * t) * l⁻¹) * u =
    u * (l * pinnedX Tag.F4 K (theta + β) (((C (1, 1) : ℤ) : K) * s * t) * l⁻¹)
  calc (l * pinnedX Tag.F4 K (theta + β) (((C (1, 1) : ℤ) : K) * s * t) * l⁻¹) * u
      = l * (pinnedX Tag.F4 K (theta + β) (((C (1, 1) : ℤ) : K) * s * t) * (l⁻¹ * u * l)) * l⁻¹ := by
        group
    _ = l * ((l⁻¹ * u * l) * pinnedX Tag.F4 K (theta + β) (((C (1, 1) : ℤ) : K) * s * t)) * l⁻¹ := by
        rw [hy.eq]
    _ = u * (l * pinnedX Tag.F4 K (theta + β) (((C (1, 1) : ℤ) : K) * s * t) * l⁻¹) := by
        group

theorem case_three {H : Subgroup (ModGL Tag.F4 K)} (hH : H ≤ adjointGroup Tag.F4 K)
    (hX : XS K ≤ H) {g p : ModGL Tag.F4 K} (hg : g ∈ H) (hp : p ∈ Pθ Tag.F4 K)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hlong : IsLongRoot Tag.F4 β)
    (hdeg : β 0 = -1)
    (hB : conjSub g (Uθ Tag.F4 K) = conjSub p (rootSubgroup Tag.F4 K β))
    (hnot : ¬ conjSub g (Uθ Tag.F4 K) ≤ XS K) [Finite K] : MPart K H := by
  classical
  have hUH : Uθ Tag.F4 K ≤ H := (Uθ_le_X1 K).trans ((X1_le_XS K).trans hX)
  have hBH : conjSub g (Uθ Tag.F4 K) ≤ H := conjSub_le_of_mem_of_le hg hUH
  obtain ⟨⟨hθβ, hθβ0⟩, hnr, hne1, hne2, hne3, hne4, hP, hcomm⟩ :=
    case3_data β (mem_rootFinset.2 hβ) hdeg hlong
  have hθβroot : IsRoot Tag.F4 (theta + β) := mem_rootFinset.1 hθβ
  have hθβdeg1 : theta + β ∈ Deg1 Tag.F4 := ⟨hθβroot, hθβ0⟩
  obtain ⟨q, hq, l, hl, rfl⟩ := exists_factor_Pθ Tag.F4 K hp
  have hlP : l ∈ Pθ Tag.F4 K := Lθ_le_Pθ Tag.F4 K hl
  have hBq : conjSub g (Uθ Tag.F4 K) = conjSub q (conjSub l (rootSubgroup Tag.F4 K β)) := by
    rw [hB, conjSub_mul]
  rcases case3_dichotomy K hl hβ hlong hdeg with ⟨c, hc, hcM⟩ | hD
  ·
    have hcond : conjSub (q * l) (rootSubgroup Tag.F4 K (theta + β)) ≤ H := by
      refine conjSub_add_le K isRoot_theta hβ hne1 (commPairs_eq_single hP)
        (fun h => hnr (mem_rootFinset.2 h)) ?_ ?_
      · have e : conjSub (q * l) (rootSubgroup Tag.F4 K theta) = Uθ Tag.F4 K :=
          conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.F4 K hp)
        rw [e]
        exact hUH
      · rw [← hB]
        exact hBH
    have hcmem : q * c * q⁻¹ ∈ conjSub (q * l) (rootSubgroup Tag.F4 K (theta + β)) := by
      rw [conjSub_mul, mem_conjSub_iff]
      have e : q⁻¹ * (q * c * q⁻¹) * q = c := by group
      rw [e]
      exact hc
    have hcQ : c ∈ Qθ Tag.F4 K := conjSub_le_Qθ K hlP (rootSubgroup_le_Qθ K hθβdeg1) hc
    have hs := heisCoord_spec Tag.F4 K
    have hcoord : heisCoord Tag.F4 K (q * c * q⁻¹) = heisCoord Tag.F4 K c := by
      rw [hs.mul _ (mul_mem hq hcQ) _ (inv_mem hq), hs.mul _ hq _ hcQ, heisCoord_inv hq]
      abel
    obtain ⟨β₀, hβ₀, hne⟩ := hcM
    exact ⟨q * c * q⁻¹, hcond hcmem, mul_mem (mul_mem hq hcQ) (inv_mem hq), β₀, hβ₀,
      by rw [hcoord]; exact hne⟩
  ·
    have hDlong : IsLongRootSubgroup Tag.F4 K (conjSub l (rootSubgroup Tag.F4 K β)) := by
      refine ⟨q⁻¹ * g, mul_mem (inv_mem (Qθ_le_adjointGroup Tag.F4 K hq)) (hH hg), ?_⟩
      rw [conjSub_mul, hBq, conjSub_inv_conjSub]
    have hcl := class_two_conjSub K hlP hβ hlong hdeg
    obtain ⟨ν, hν, hDν⟩ : ∃ ν, (ν = -alpha1 ∨ ν = -root1342) ∧
        conjSub l (rootSubgroup Tag.F4 K β) = rootSubgroup Tag.F4 K ν := by
      rcases lemma5_neg K hDlong hD with h | h
      · exact ⟨-alpha1, Or.inl rfl, eq_of_pure_class_two K hDlong (Or.inl rfl) h hcl⟩
      · exact ⟨-root1342, Or.inr rfl, eq_of_pure_class_two K hDlong (Or.inr rfl) h hcl⟩
    obtain ⟨s, hsX1, w, hwQ, rfl, hwM⟩ := exists_split_Q K hq
    have hsH : s ∈ H := hX (X1_le_XS K hsX1)
    have hB'eq : conjSub w (rootSubgroup Tag.F4 K ν) = conjSub s⁻¹ (conjSub g (Uθ Tag.F4 K)) := by
      rw [hBq, hDν, ← conjSub_mul, inv_mul_cancel_left]
    have hB'H : conjSub w (rootSubgroup Tag.F4 K ν) ≤ H := by
      rw [hB'eq]
      exact conjSub_le_of_mem_of_le (inv_mem hsH) hBH
    have hB'not : ¬ conjSub w (rootSubgroup Tag.F4 K ν) ≤ XS K := by
      intro hle
      apply hnot
      have e : conjSub g (Uθ Tag.F4 K) = conjSub s (conjSub w (rootSubgroup Tag.F4 K ν)) := by
        rw [hBq, hDν, conjSub_mul]
      rw [e]
      exact conjSub_le_of_mem_of_le (X1_le_XS K hsX1) hle
    have hνfacts : -ν ∈ S1set ∧ -ν ∈ sRoots1 ∧ -ν ∈ Deg1 Tag.F4 := by
      rcases hν with rfl | rfl
      · rw [neg_neg]
        exact ⟨alpha1_mem_S1set, by decide +kernel, alpha1_deg1⟩
      · rw [neg_neg]
        exact ⟨root1342_mem_S1set, by decide +kernel, root1342_deg1⟩
    obtain ⟨n', hn'X, hn'θ, hn'neg⟩ := transport_pair K hνfacts.1
    have hn'XS : n' ∈ XS K := X1_le_XS K hn'X
    have hn'H : n' ∈ H := hX hn'XS
    have hwcomm : ∀ x ∈ rootSubgroup Tag.F4 K (-ν), w * x = x * w := by
      intro x hx
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
      exact (heisCoord_spec Tag.F4 K).commute_disjoint w hwQ (-ν) hνfacts.2.2 c
        (fun γ hγ => lemma2_core γ (hwM γ hγ) (-ν) hνfacts.2.1)
    have hw'comm : ∀ x ∈ Uθ Tag.F4 K, (n'⁻¹ * w * n') * x = x * (n'⁻¹ * w * n') := by
      intro x hx
      have hx' : n' * x * n'⁻¹ ∈ rootSubgroup Tag.F4 K (-ν) := by
        rw [← hn'θ, mem_conjSub_iff]
        have e : n'⁻¹ * (n' * x * n'⁻¹) * n' = x := by group
        rw [e]
        exact hx
      have h := hwcomm _ hx'
      calc n'⁻¹ * w * n' * x = n'⁻¹ * (w * (n' * x * n'⁻¹)) * n' := by group
        _ = n'⁻¹ * ((n' * x * n'⁻¹) * w) * n' := by rw [h]
        _ = x * (n'⁻¹ * w * n') := by group
    have hw'G : n'⁻¹ * w * n' ∈ adjointGroup Tag.F4 K :=
      mul_mem (mul_mem (inv_mem (rootSpan_le_adjointGroup K _ hn'X))
        (Qθ_le_adjointGroup Tag.F4 K hwQ)) (rootSpan_le_adjointGroup K _ hn'X)
    have hw'P : n'⁻¹ * w * n' ∈ Pθ Tag.F4 K := centralizer_Uθ_le_Pθ Tag.F4 K hw'G hw'comm
    have hconj : conjSub (n'⁻¹ * w * n') (Heis.Uneg Tag.F4 K) =
        conjSub n'⁻¹ (conjSub w (rootSubgroup Tag.F4 K ν)) := by
      rw [conjSub_mul, conjSub_mul, hn'neg, neg_neg]
    refine case_two K hX hw'P ?_ ?_
    · rw [hconj]
      exact conjSub_le_of_mem_of_le (inv_mem hn'H) hB'H
    · intro hle
      apply hB'not
      rw [hconj] at hle
      have e : conjSub w (rootSubgroup Tag.F4 K ν) =
          conjSub n' (conjSub n'⁻¹ (conjSub w (rootSubgroup Tag.F4 K ν))) :=
        (conjSub_conjSub_inv n' _).symm
      rw [e]
      exact conjSub_le_of_mem_of_le hn'XS hle

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
