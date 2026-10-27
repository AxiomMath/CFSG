module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Split
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Case3Data
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Transport
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.Case3Dichotomy
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.Lemma5
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.FZero
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.ConjSub
public import CFSG.LieType.Chevalley.RootCommutator

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem isRoot_theta_E8 : IsRoot Tag.E8 theta := mem_rootFinset.1 theta_mem

theorem commutator_E8 {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) (hβ : IsRoot Tag.E8 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hr : IsRoot Tag.E8 (α + β)) :
    (commConst Tag.E8 α β (1, 1) = 1 ∨ commConst Tag.E8 α β (1, 1) = -1) ∧
      ∀ (K : Type) [Field K] (c d : K), ⁅pinnedX Tag.E8 K α c, pinnedX Tag.E8 K β d⁆ =
        pinnedX Tag.E8 K (α + β) ((commConst Tag.E8 α β (1, 1) : K) * c * d) :=
  ⟨((simply_laced_root_commutator_unit.{0} Tag.E8 (Or.inr (Or.inr (Or.inr rfl))) hα hβ hne
      hne').1 hr).1,
    fun K _ c d => ((simply_laced_root_commutator_unit.{0} Tag.E8 (Or.inr (Or.inr (Or.inr rfl)))
      hα hβ hne hne').1 hr).2 K c d⟩

theorem commute_E8 {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) (hβ : IsRoot Tag.E8 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hr : ¬ IsRoot Tag.E8 (α + β)) {K : Type} [Field K] (c d : K) :
    Commute (pinnedX Tag.E8 K α c) (pinnedX Tag.E8 K β d) :=
  (simply_laced_root_commutator_unit.{0} Tag.E8 (Or.inr (Or.inr (Or.inr rfl))) hα hβ hne
    hne').2 hr K _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem rootSubgroup_add_le_E8 {K : Type} [Field K] (H : Subgroup (ModGL Tag.E8 K))
    {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) (hβ : IsRoot Tag.E8 β) (hne : α ≠ β)
    (hne' : α ≠ -β) (hr : IsRoot Tag.E8 (α + β)) (hA : rootSubgroup Tag.E8 K α ≤ H)
    (hB : rootSubgroup Tag.E8 K β ≤ H) : rootSubgroup Tag.E8 K (α + β) ≤ H := by
  obtain ⟨hε, hF⟩ := commutator_E8 hα hβ hne hne' hr
  have hsq : ((commConst Tag.E8 α β (1, 1) : ℤ) : K) * ((commConst Tag.E8 α β (1, 1) : ℤ) : K) =
      1 := by
    rcases hε with h | h <;> rw [h] <;> simp
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨e, rfl⟩
  have h1 := hF K 1 (((commConst Tag.E8 α β (1, 1) : ℤ) : K) * e)
  rw [← mul_assoc, mul_one, hsq, one_mul, commutatorElement_def] at h1
  rw [← h1]
  have hx := hA (mem_rootSubgroup.2 ⟨1, rfl⟩)
  have hy := hB (mem_rootSubgroup.2 ⟨((commConst Tag.E8 α β (1, 1) : ℤ) : K) * e, rfl⟩)
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

variable (K : Type) [Field K]

theorem conjSub_add_le {H : Subgroup (ModGL Tag.E8 K)} {p : ModGL Tag.E8 K}
    {v w : Fin Tag.E8.rank → ℤ} (hv : IsRoot Tag.E8 v) (hw : IsRoot Tag.E8 w) (hne : v ≠ w)
    (hne' : v ≠ -w) (hr : IsRoot Tag.E8 (v + w))
    (hA : conjSub p (rootSubgroup Tag.E8 K v) ≤ H) (hB : conjSub p (rootSubgroup Tag.E8 K w) ≤ H) :
    conjSub p (rootSubgroup Tag.E8 K (v + w)) ≤ H := by
  have h1 : ∀ x : ModGL Tag.E8 K, ∀ u : Fin Tag.E8.rank → ℤ,
      conjSub p (rootSubgroup Tag.E8 K u) ≤ H → x ∈ rootSubgroup Tag.E8 K u →
        x ∈ conjSub p⁻¹ H := by
    intro x u hu hx
    rw [mem_conjSub_iff, inv_inv]
    have : p * x * p⁻¹ ∈ conjSub p (rootSubgroup Tag.E8 K u) := by
      rw [mem_conjSub_iff]
      have e : p⁻¹ * (p * x * p⁻¹) * p = x := by group
      rw [e]
      exact hx
    exact hu this
  have h2 := rootSubgroup_add_le_E8 (conjSub p⁻¹ H) hv hw hne hne' hr
    (fun x hx => h1 x v hA hx) (fun x hx => h1 x w hB hx)
  calc conjSub p (rootSubgroup Tag.E8 K (v + w)) ≤ conjSub p (conjSub p⁻¹ H) := conjSub_mono p h2
    _ = H := conjSub_conjSub_inv p H

theorem rootSubgroup_le_Qθ_E8 {β : Fin Tag.E8.rank → ℤ} (hβ : β ∈ Deg1 Tag.E8) :
    rootSubgroup Tag.E8 K β ≤ Qθ Tag.E8 K :=
  rootSubgroup_le_Qθ_of_mem_Deg1 hβ

theorem class_two_conjSub {l : ModGL Tag.E8 K} (hl : l ∈ Pθ Tag.E8 K)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (hdeg : β 7 = -1) :
    ∀ u ∈ Uθ Tag.E8 K, ∀ d ∈ conjSub l (rootSubgroup Tag.E8 K β),
      Commute (u * d * u⁻¹ * d⁻¹) u := by
  intro u hu d hd
  obtain ⟨⟨hθβ, hθβ0⟩, hne1, hne2, hne3, hne4, hnr⟩ := case3_data β (mem_rootFinset.2 hβ) hdeg
  have hθβroot : IsRoot Tag.E8 (theta + β) := mem_rootFinset.1 hθβ
  have hl' := Pθ_le_normalizer_Uθ Tag.E8 K (inv_mem hl)
  have hu' : l⁻¹ * u * l ∈ Uθ Tag.E8 K := by
    have := (Subgroup.mem_normalizer_iff.1 hl' u).1 hu
    simpa using this
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hd)
  obtain ⟨-, hF⟩ := commutator_E8 isRoot_theta_E8 hβ hne1 hne2 hθβroot
  have h1 := hF K s t
  have hy : Commute (pinnedX Tag.E8 K (theta + β) (((commConst Tag.E8 theta β (1, 1) : ℤ) : K) * s * t))
      (pinnedX Tag.E8 K theta s) :=
    commute_E8 hθβroot isRoot_theta_E8 hne3 hne4 (fun h => hnr (mem_rootFinset.2 h)) _ _
  have hs' : pinnedX Tag.E8 K theta s = l⁻¹ * u * l := hs
  have ht' : pinnedX Tag.E8 K β t = l⁻¹ * d * l := ht
  rw [commutatorElement_def] at h1
  rw [hs', ht'] at h1
  rw [hs'] at hy
  have e : u * d * u⁻¹ * d⁻¹ = l * (l⁻¹ * u * l * (l⁻¹ * d * l) * (l⁻¹ * u * l)⁻¹ *
      (l⁻¹ * d * l)⁻¹) * l⁻¹ := by group
  rw [e, h1]
  show (l * pinnedX Tag.E8 K (theta + β) (((commConst Tag.E8 theta β (1, 1) : ℤ) : K) * s * t) *
      l⁻¹) * u =
    u * (l * pinnedX Tag.E8 K (theta + β) (((commConst Tag.E8 theta β (1, 1) : ℤ) : K) * s * t) *
      l⁻¹)
  calc (l * pinnedX Tag.E8 K (theta + β) (((commConst Tag.E8 theta β (1, 1) : ℤ) : K) * s * t) *
        l⁻¹) * u
      = l * (pinnedX Tag.E8 K (theta + β) (((commConst Tag.E8 theta β (1, 1) : ℤ) : K) * s * t) *
          (l⁻¹ * u * l)) * l⁻¹ := by group
    _ = l * ((l⁻¹ * u * l) * pinnedX Tag.E8 K (theta + β)
          (((commConst Tag.E8 theta β (1, 1) : ℤ) : K) * s * t)) * l⁻¹ := by rw [hy.eq]
    _ = u * (l * pinnedX Tag.E8 K (theta + β)
          (((commConst Tag.E8 theta β (1, 1) : ℤ) : K) * s * t) * l⁻¹) := by group

theorem case_three_tail {H : Subgroup (ModGL Tag.E8 K)} (hX : XS K ≤ H) {g q : ModGL Tag.E8 K}
    (hg : g ∈ H) (hq : q ∈ Qθ Tag.E8 K) {ν : Fin Tag.E8.rank → ℤ} (hν : ν ∈ pureNegDirs)
    (hB : conjSub g (Uθ Tag.E8 K) = conjSub q (rootSubgroup Tag.E8 K ν))
    (hnot : ¬ conjSub g (Uθ Tag.E8 K) ≤ XS K) : MPart K H := by
  classical
  have hUH : Uθ Tag.E8 K ≤ H := (Uθ_le_X1 K).trans ((X1_le_XS K).trans hX)
  have hBH : conjSub g (Uθ Tag.E8 K) ≤ H := conjSub_le_of_mem_of_le hg hUH
  obtain ⟨s, hsX1, w, hwQ, rfl, hwM⟩ := exists_split_Q K hq
  have hsH : s ∈ H := hX (X1_le_XS K hsX1)
  have hB'eq : conjSub w (rootSubgroup Tag.E8 K ν) = conjSub s⁻¹ (conjSub g (Uθ Tag.E8 K)) := by
    rw [hB, ← conjSub_mul, inv_mul_cancel_left]
  have hB'H : conjSub w (rootSubgroup Tag.E8 K ν) ≤ H := by
    rw [hB'eq]
    exact conjSub_le_of_mem_of_le (inv_mem hsH) hBH
  have hB'not : ¬ conjSub w (rootSubgroup Tag.E8 K ν) ≤ XS K := by
    intro hle
    apply hnot
    have e : conjSub g (Uθ Tag.E8 K) = conjSub s (conjSub w (rootSubgroup Tag.E8 K ν)) := by
      rw [hB, conjSub_mul]
    rw [e]
    exact conjSub_le_of_mem_of_le (X1_le_XS K hsX1) hle
  obtain ⟨hnS1, hnS⟩ := pureNeg_data ν hν
  have hνD : -ν ∈ Deg1 Tag.E8 := mem_Deg1_E8.2 ⟨mem_rootFinset.1 (Finset.mem_filter.1 hnS).1,
    (Finset.mem_filter.1 hnS).2.1⟩
  obtain ⟨n', hn'X, hn'θ, hn'neg⟩ := transport_pair K (α := -ν) hnS1
  have hn'XS : n' ∈ XS K := X1_le_XS K hn'X
  have hn'H : n' ∈ H := hX hn'XS
  have hwcomm : ∀ x ∈ rootSubgroup Tag.E8 K (-ν), w * x = x * w := by
    intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    exact (heisCoord_spec Tag.E8 K).commute_disjoint w hwQ (-ν) hνD c
      (fun γ hγ => lemma2_core γ (hwM γ hγ) (-ν) hnS)
  have hw'comm : ∀ x ∈ Uθ Tag.E8 K, (n'⁻¹ * w * n') * x = x * (n'⁻¹ * w * n') := by
    intro x hx
    have hx' : n' * x * n'⁻¹ ∈ rootSubgroup Tag.E8 K (-ν) := by
      rw [← hn'θ, mem_conjSub_iff]
      have e : n'⁻¹ * (n' * x * n'⁻¹) * n' = x := by group
      rw [e]
      exact hx
    have h := hwcomm _ hx'
    calc n'⁻¹ * w * n' * x = n'⁻¹ * (w * (n' * x * n'⁻¹)) * n' := by group
      _ = n'⁻¹ * ((n' * x * n'⁻¹) * w) * n' := by rw [h]
      _ = x * (n'⁻¹ * w * n') := by group
  have hw'G : n'⁻¹ * w * n' ∈ adjointGroup Tag.E8 K :=
    mul_mem (mul_mem (inv_mem (rootSpan_le_adjointGroup K _ hn'X))
      (Qθ_le_adjointGroup Tag.E8 K hwQ)) (rootSpan_le_adjointGroup K _ hn'X)
  have hw'P : n'⁻¹ * w * n' ∈ Pθ Tag.E8 K := centralizer_Uθ_le_Pθ Tag.E8 K hw'G hw'comm
  have hconj : conjSub (n'⁻¹ * w * n') (Heis.Uneg Tag.E8 K) =
      conjSub n'⁻¹ (conjSub w (rootSubgroup Tag.E8 K ν)) := by
    rw [conjSub_mul, conjSub_mul, hn'neg, neg_neg]
  refine case_two K hX hw'P ?_ ?_
  · rw [hconj]
    exact conjSub_le_of_mem_of_le (inv_mem hn'H) hB'H
  · intro hle
    apply hB'not
    rw [hconj] at hle
    have e : conjSub w (rootSubgroup Tag.E8 K ν) =
        conjSub n' (conjSub n'⁻¹ (conjSub w (rootSubgroup Tag.E8 K ν))) :=
      (conjSub_conjSub_inv n' _).symm
    rw [e]
    exact conjSub_le_of_mem_of_le hn'XS hle

theorem case_three [Finite K] {H : Subgroup (ModGL Tag.E8 K)} (hH : H ≤ adjointGroup Tag.E8 K)
    (hX : XS K ≤ H) {g p : ModGL Tag.E8 K} (hg : g ∈ H) (hp : p ∈ Pθ Tag.E8 K)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (hdeg : β 7 = -1)
    (hB : conjSub g (Uθ Tag.E8 K) = conjSub p (rootSubgroup Tag.E8 K β))
    (hnot : ¬ conjSub g (Uθ Tag.E8 K) ≤ XS K) : MPart K H := by
  classical
  have hUH : Uθ Tag.E8 K ≤ H := (Uθ_le_X1 K).trans ((X1_le_XS K).trans hX)
  have hBH : conjSub g (Uθ Tag.E8 K) ≤ H := conjSub_le_of_mem_of_le hg hUH
  obtain ⟨⟨hθβ, hθβ0⟩, hne1, hne2, hne3, hne4, hnr⟩ := case3_data β (mem_rootFinset.2 hβ) hdeg
  have hθβroot : IsRoot Tag.E8 (theta + β) := mem_rootFinset.1 hθβ
  have hθβdeg1 : theta + β ∈ Deg1 Tag.E8 := ⟨hθβroot, hθβ0⟩
  obtain ⟨q, hq, l, hl, rfl⟩ := exists_factor_Pθ Tag.E8 K hp
  have hlP : l ∈ Pθ Tag.E8 K := Lθ_le_Pθ Tag.E8 K hl
  have hBq : conjSub g (Uθ Tag.E8 K) = conjSub q (conjSub l (rootSubgroup Tag.E8 K β)) := by
    rw [hB, conjSub_mul]
  rcases case3_dichotomy K hl hβ hdeg with ⟨c, hc, hcM⟩ | hD
  ·
    have hcond : conjSub (q * l) (rootSubgroup Tag.E8 K (theta + β)) ≤ H := by
      refine conjSub_add_le K isRoot_theta_E8 hβ hne1 hne2 hθβroot ?_ ?_
      · have e : conjSub (q * l) (rootSubgroup Tag.E8 K theta) = Uθ Tag.E8 K :=
          conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.E8 K hp)
        rw [e]
        exact hUH
      · rw [← hB]
        exact hBH
    have hcmem : q * c * q⁻¹ ∈ conjSub (q * l) (rootSubgroup Tag.E8 K (theta + β)) := by
      rw [conjSub_mul, mem_conjSub_iff]
      have e : q⁻¹ * (q * c * q⁻¹) * q = c := by group
      rw [e]
      exact hc
    have hcQ : c ∈ Qθ Tag.E8 K := conjSub_le_Qθ hlP (rootSubgroup_le_Qθ_E8 K hθβdeg1) hc
    have hs := heisCoord_spec Tag.E8 K
    have hcoord : heisCoord Tag.E8 K (q * c * q⁻¹) = heisCoord Tag.E8 K c := by
      rw [hs.mul _ (mul_mem hq hcQ) _ (inv_mem hq), hs.mul _ hq _ hcQ, heisCoord_inv hq]
      abel
    obtain ⟨β₀, hβ₀, hne⟩ := hcM
    exact ⟨q * c * q⁻¹, hcond hcmem, mul_mem (mul_mem hq hcQ) (inv_mem hq), β₀, hβ₀,
      by rw [hcoord]; exact hne⟩
  ·
    have hDlong : IsLongRootSubgroup Tag.E8 K (conjSub l (rootSubgroup Tag.E8 K β)) := by
      refine ⟨q⁻¹ * g, mul_mem (inv_mem (Qθ_le_adjointGroup Tag.E8 K hq)) (hH hg), ?_⟩
      rw [conjSub_mul, hBq, conjSub_inv_conjSub]
    obtain ⟨y, hyX, hyL, ν, hν, hle⟩ := lemma5_neg K hDlong hD
    have hyG : y ∈ adjointGroup Tag.E8 K := rootSpan_le_adjointGroup K _ hyX
    have hyP : y ∈ Pθ Tag.E8 K := Lθ_le_Pθ Tag.E8 K hyL
    have hDy : IsLongRootSubgroup Tag.E8 K (conjSub y (conjSub l (rootSubgroup Tag.E8 K β))) := by
      obtain ⟨g', hg', hD'⟩ := hDlong
      exact ⟨y * g', mul_mem hyG hg', by rw [conjSub_mul, ← hD']⟩
    have hcl := class_two_conjSub K hlP hβ hdeg
    have hcl' : ∀ u ∈ Uθ Tag.E8 K, ∀ d ∈ conjSub y (conjSub l (rootSubgroup Tag.E8 K β)),
        Commute (u * d * u⁻¹ * d⁻¹) u := by
      intro u hu d hd
      have hy' := Pθ_le_normalizer_Uθ Tag.E8 K (inv_mem hyP)
      have hu' : y⁻¹ * u * y ∈ Uθ Tag.E8 K := by
        have := (Subgroup.mem_normalizer_iff.1 hy' u).1 hu
        simpa using this
      have hd' : y⁻¹ * d * y ∈ conjSub l (rootSubgroup Tag.E8 K β) := mem_conjSub_iff.1 hd
      have hc := hcl _ hu' _ hd'
      have e1 : u * d * u⁻¹ * d⁻¹ = y * ((y⁻¹ * u * y) * (y⁻¹ * d * y) * (y⁻¹ * u * y)⁻¹ *
          (y⁻¹ * d * y)⁻¹) * y⁻¹ := by group
      have e2 : u = y * (y⁻¹ * u * y) * y⁻¹ := by group
      rw [e1]
      show (y * ((y⁻¹ * u * y) * (y⁻¹ * d * y) * (y⁻¹ * u * y)⁻¹ * (y⁻¹ * d * y)⁻¹) * y⁻¹) * u =
        u * (y * ((y⁻¹ * u * y) * (y⁻¹ * d * y) * (y⁻¹ * u * y)⁻¹ * (y⁻¹ * d * y)⁻¹) * y⁻¹)
      have hc' := hc.eq
      calc (y * ((y⁻¹ * u * y) * (y⁻¹ * d * y) * (y⁻¹ * u * y)⁻¹ * (y⁻¹ * d * y)⁻¹) * y⁻¹) * u
          = y * (((y⁻¹ * u * y) * (y⁻¹ * d * y) * (y⁻¹ * u * y)⁻¹ * (y⁻¹ * d * y)⁻¹) *
              (y⁻¹ * u * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * u * y) * ((y⁻¹ * u * y) * (y⁻¹ * d * y) * (y⁻¹ * u * y)⁻¹ *
              (y⁻¹ * d * y)⁻¹)) * y⁻¹ := by rw [hc']
        _ = u * (y * ((y⁻¹ * u * y) * (y⁻¹ * d * y) * (y⁻¹ * u * y)⁻¹ *
              (y⁻¹ * d * y)⁻¹) * y⁻¹) := by group
    have hDν : conjSub y (conjSub l (rootSubgroup Tag.E8 K β)) = rootSubgroup Tag.E8 K ν :=
      eq_of_pure_class_two K hDy hν hle hcl'
    have hyXS : y ∈ XS K := X1_le_XS K hyX
    refine case_three_tail K hX (g := y * g) (q := y * q * y⁻¹) (mul_mem (hX hyXS) hg) ?_ hν ?_ ?_
    ·
      have hn := Pθ_le_normalizer_Qθ Tag.E8 K hyP
      have := (Subgroup.mem_normalizer_iff.1 hn q).1 hq
      exact this
    · calc conjSub (y * g) (Uθ Tag.E8 K) = conjSub y (conjSub g (Uθ Tag.E8 K)) :=
            conjSub_mul _ _ _
        _ = conjSub y (conjSub q (conjSub l (rootSubgroup Tag.E8 K β))) := by rw [hBq]
        _ = conjSub (y * q) (conjSub l (rootSubgroup Tag.E8 K β)) := (conjSub_mul _ _ _).symm
        _ = conjSub (y * q * y⁻¹) (conjSub y (conjSub l (rootSubgroup Tag.E8 K β))) := by
            rw [← conjSub_mul (y * q * y⁻¹) y, show y * q * y⁻¹ * y = y * q by group]
        _ = conjSub (y * q * y⁻¹) (rootSubgroup Tag.E8 K ν) := by rw [hDν]
    · intro hle'
      apply hnot
      have e : conjSub g (Uθ Tag.E8 K) = conjSub y⁻¹ (conjSub (y * g) (Uθ Tag.E8 K)) := by
        rw [← conjSub_mul, inv_mul_cancel_left]
      rw [e]
      exact conjSub_le_of_mem_of_le (inv_mem hyXS) hle'

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
