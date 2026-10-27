module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Action
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureF4Pair
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.MPart

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open Heis

set_option linter.unusedSectionVars false


namespace CaseTwo

structure CoverData (γ δ : Fin Tag.F4.rank → ℤ)
    (s : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ))
    (ℓ : (Fin Tag.F4.rank → ℤ) → ℤ) : Prop where
  γ_S1 : γ ∈ S1set
  γ_deg1 : γ ∈ rootFinset .F4 ∧ γ 0 = 1
  δ_deg1 : δ ∈ deg1Roots
  disj : ∀ ν ∈ mRoots, ν + γ ∉ rootFinset .F4
  pairs : ∀ p ∈ commCandidates, p.1 • γ + p.2 • (-theta) ∈ rootFinset .F4 → p = (1, 1)
  sum_root : γ + -theta ∈ rootFinset .F4
  nr : -theta - γ ∉ rootFinset .F4
  ne : γ ≠ -theta
  sum_eq : γ + -theta = -δ
  sθ : s theta = γ
  sδ : s (-δ) = δ
  ℓδ : ℓ δ = -1
  ℓ_sub : ∀ a b, ℓ (a - b) = ℓ a - ℓ b
  ℓ_two : ∀ a, ℓ (2 • a) = 2 * ℓ a
  mdich : ∀ ν ∈ mRoots, (ℓ ν = 1 ∧ s ν = ν) ∨
    (ℓ ν = 0 ∧ s ν + δ = ν ∧ s ν ∈ rootFinset .F4 ∧ s ν 0 = 0 ∧ ℓ (s ν) = 1 ∧
      δ - s ν ∉ rootFinset .F4)

theorem coverData_alpha1 :
    CoverData alpha1 root1342 sGamma (fun ν => 2 * ν 0 - ν 1) where
  γ_S1 := alpha1_mem_S1set
  γ_deg1 := by decide +kernel
  δ_deg1 := by decide +kernel
  disj := by decide +kernel
  pairs := by decide +kernel
  sum_root := by decide +kernel
  nr := by decide +kernel
  ne := by decide +kernel
  sum_eq := by decide +kernel
  sθ := by decide +kernel
  sδ := by decide +kernel
  ℓδ := by decide +kernel
  ℓ_sub := fun a b => by simp only [Pi.sub_apply]; ring
  ℓ_two := fun a => by simp only [Pi.smul_apply, nsmul_eq_mul]; push_cast; ring
  mdich := by decide +kernel

theorem coverData_root1342 :
    CoverData root1342 alpha1 (reflect Tag.F4 0) (fun ν => ν 1 - ν 0) where
  γ_S1 := root1342_mem_S1set
  γ_deg1 := by decide +kernel
  δ_deg1 := by decide +kernel
  disj := by decide +kernel
  pairs := by decide +kernel
  sum_root := by decide +kernel
  nr := by decide +kernel
  ne := by decide +kernel
  sum_eq := by decide +kernel
  sθ := by decide +kernel
  sδ := by decide +kernel
  ℓδ := by decide +kernel
  ℓ_sub := fun a b => by simp only [Pi.sub_apply]; ring
  ℓ_two := fun a => by simp only [Pi.smul_apply, nsmul_eq_mul]; push_cast; ring
  mdich := by decide +kernel

theorem cover_dichotomy : ∀ μ ∈ mRoots, 2 * μ 0 - μ 1 = 0 ∨ μ 1 - μ 0 = 0 := by decide +kernel

section Generic

variable (K : Type) [Field K]

theorem commute_theta_pinnedX_deg0 {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (h0 : β 0 = 0)
    (s t : K) : Commute (pinnedX Tag.F4 K theta s) (pinnedX Tag.F4 K β t) := by
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg β (mem_rootFinset.2 hβ) (Or.inl h0)
  refine Heis.commute_pinnedX_of_commPairs_nil Tag.F4 K isRoot_theta hβ hne hne' ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact commCandidates_theta_data β (mem_rootFinset.2 hβ) (Or.inl h0) p hp.1
    (mem_rootFinset.2 hp.2)

theorem pinnedX_mem_Pθ_deg0 {ρ : Fin Tag.F4.rank → ℤ} (hρ : IsRoot Tag.F4 ρ) (h0 : ρ 0 = 0)
    (c : K) : pinnedX Tag.F4 K ρ c ∈ Pθ Tag.F4 K := by
  refine Heis.centralizer_Uθ_le_Pθ Tag.F4 K (pinnedX_mem_adjointGroup ρ c) fun x hx => ?_
  obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
  exact (commute_theta_pinnedX_deg0 K hρ h0 a c).eq.symm

theorem levi_conj_mem_Qθ {ρ : Fin Tag.F4.rank → ℤ} (hρ : IsRoot Tag.F4 ρ) (h0 : ρ 0 = 0) (c : K)
    {q : ModGL Tag.F4 K} (hq : q ∈ Qθ Tag.F4 K) :
    pinnedX Tag.F4 K ρ c * q * (pinnedX Tag.F4 K ρ c)⁻¹ ∈ Qθ Tag.F4 K := by
  have hn := parabolicSubgroup_le_normalizer_parabolicRadical (τ := Tag.F4) (K := K)
    (Heis.Jθ Tag.F4) (pinnedX_mem_Pθ_deg0 K hρ h0 c)
  exact (Subgroup.mem_normalizer_iff.1 hn q).1 hq

theorem heisCoord_conj_Q {g q : ModGL Tag.F4 K} (hg : g ∈ Qθ Tag.F4 K) (hq : q ∈ Qθ Tag.F4 K) :
    g * q * g⁻¹ ∈ Qθ Tag.F4 K ∧ heisCoord Tag.F4 K (g * q * g⁻¹) = heisCoord Tag.F4 K q := by
  have hs := heisCoord_spec Tag.F4 K
  refine ⟨mul_mem (mul_mem hg hq) (inv_mem hg), ?_⟩
  rw [hs.mul _ (mul_mem hg hq) _ (inv_mem hg), hs.mul _ hg _ hq, heisCoord_inv hg]
  abel

theorem commPairs_eq_single {γ : Fin Tag.F4.rank → ℤ}
    (hpairs : ∀ p ∈ commCandidates, p.1 • γ + p.2 • (-theta) ∈ rootFinset .F4 → p = (1, 1))
    (hsum : γ + -theta ∈ rootFinset .F4) : commPairs .F4 γ (-theta) = [(1, 1)] := by
  refine list_eq_singleton_of_forall_eq (a := ((1, 1) : ℕ × ℕ)) (fun p hp => ?_)
    (commPairs_nodup _ _) ?_
  · rw [mem_commPairs] at hp
    exact hpairs p hp.1 (mem_rootFinset.2 hp.2)
  · rw [mem_commPairs]
    refine ⟨by decide, ?_⟩
    simpa using mem_rootFinset.1 hsum

theorem transported_coord {γ δ : Fin Tag.F4.rank → ℤ}
    {s : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)} {ℓ : (Fin Tag.F4.rank → ℤ) → ℤ}
    (D : CoverData γ δ s ℓ) {m X : ModGL Tag.F4 K}
    (hconj : ∀ ν, IsRoot Tag.F4 ν →
      conjSub m (rootSubgroup Tag.F4 K ν) = rootSubgroup Tag.F4 K (s ν))
    (hXmem : X ∈ rootSubgroup Tag.F4 K (-δ)) (hX1 : X ≠ 1) {μ₀ : Fin Tag.F4.rank → ℤ}
    (hℓ : ℓ μ₀ = 0) {w : ModGL Tag.F4 K} (hw : w ∈ Qθ Tag.F4 K)
    (hwM : ∀ ν, heisCoord Tag.F4 K w ν ≠ 0 → ν ∈ mRoots) :
    m * (w * X * w⁻¹) * m⁻¹ ∈ Qθ Tag.F4 K ∧
      (heisCoord Tag.F4 K (m * (w * X * w⁻¹) * m⁻¹) μ₀ ≠ 0 ↔ heisCoord Tag.F4 K w μ₀ ≠ 0) := by
  have hs := heisCoord_spec Tag.F4 K
  obtain ⟨a1, a2, h1, -, hact⟩ := exists_action_data K
  have hδD : δ ∈ Deg1 Tag.F4 := mem_Deg1_of_mem_deg1Roots D.δ_deg1
  have hδR : IsRoot Tag.F4 δ := hδD.1
  have hγD : γ ∈ Deg1 Tag.F4 := deg1_iff.2 ⟨mem_rootFinset.1 D.γ_deg1.1, D.γ_deg1.2⟩
  obtain ⟨s', hs'0, hs'⟩ : ∃ s' : K, s' ≠ 0 ∧ m * X * m⁻¹ = pinnedX Tag.F4 K δ s' := by
    have hmem : m * X * m⁻¹ ∈ conjSub m (rootSubgroup Tag.F4 K (-δ)) :=
      mem_conjSub_iff.2 (by rw [show m⁻¹ * (m * X * m⁻¹) * m = X by group]; exact hXmem)
    rw [hconj _ (IsRoot.neg hδR), D.sδ] at hmem
    obtain ⟨s', hs'⟩ := mem_rootSubgroup.1 hmem
    refine ⟨s', fun h0 => hX1 ?_, hs'.symm⟩
    rw [h0, pinnedX_zero] at hs'
    calc X = m⁻¹ * (m * X * m⁻¹) * m := by group
      _ = 1 := by rw [← hs']; group
  have hδQ : pinnedX Tag.F4 K δ s' ∈ Qθ Tag.F4 K := pinnedX_mem_Qθ K hδD s'
  have hy_eq : ∀ w' : ModGL Tag.F4 K, m * (w' * X * w'⁻¹) * m⁻¹ =
      (m * w' * m⁻¹) * pinnedX Tag.F4 K δ s' * (m * w' * m⁻¹)⁻¹ := by
    intro w'
    rw [← hs']
    group
  have key : ∀ l : List (Fin Tag.F4.rank → ℤ), (∀ ν ∈ l, ν ∈ mRoots) →
      ∀ w' : ModGL Tag.F4 K, w' ∈ Qθ Tag.F4 K → (∀ ν, heisCoord Tag.F4 K w' ν ≠ 0 → ν ∈ l) →
        m * (w' * X * w'⁻¹) * m⁻¹ ∈ Qθ Tag.F4 K ∧
        (∀ ν, ℓ ν ≤ -1 →
          heisCoord Tag.F4 K (m * (w' * X * w'⁻¹) * m⁻¹) ν =
            (Pi.single δ s' : (Fin Tag.F4.rank → ℤ) → K) ν) ∧
        (heisCoord Tag.F4 K (m * (w' * X * w'⁻¹) * m⁻¹) μ₀ ≠ 0 ↔
          heisCoord Tag.F4 K w' μ₀ ≠ 0) := by
    intro l
    induction l with
    | nil =>
      intro _ w' hw' hsupp
      have h0 : heisCoord Tag.F4 K w' = 0 := funext fun ν => by
        by_contra hne
        exact List.not_mem_nil (hsupp ν hne)
      have hU : w' ∈ Uθ Tag.F4 K := (hs.eq_zero_iff w' hw').1 h0
      have hu : m * w' * m⁻¹ ∈ rootSubgroup Tag.F4 K γ := by
        have h' := hconj theta isRoot_theta
        rw [D.sθ] at h'
        have hmem : m * w' * m⁻¹ ∈ conjSub m (rootSubgroup Tag.F4 K theta) :=
          mem_conjSub_iff.2 (by rw [show m⁻¹ * (m * w' * m⁻¹) * m = w' by group]; exact hU)
        rwa [h'] at hmem
      obtain ⟨z, hz⟩ := mem_rootSubgroup.1 hu
      have huQ : m * w' * m⁻¹ ∈ Qθ Tag.F4 K := by
        rw [← hz]; exact pinnedX_mem_Qθ K hγD z
      obtain ⟨hyQ, hyc⟩ := heisCoord_conj_Q K huQ hδQ
      rw [hy_eq w']
      refine ⟨hyQ, fun ν _ => ?_, ?_⟩
      · rw [hyc, hs.pinnedX_deg1 δ hδD s']
      · rw [hyc, hs.pinnedX_deg1 δ hδD s', h0]
        have hne : μ₀ ≠ δ := fun h => by have := D.ℓδ; rw [← h, hℓ] at this; omega
        rw [Pi.single_eq_of_ne hne]
        simp
    | cons ν₁ l ih =>
      intro hl w' hw' hsupp
      have hν₁ : ν₁ ∈ mRoots := hl ν₁ List.mem_cons_self
      have hl' : ∀ ν ∈ l, ν ∈ mRoots := fun ν hν => hl ν (List.mem_cons_of_mem _ hν)
      have hν₁D : ν₁ ∈ Deg1 Tag.F4 := mem_Deg1_of_mem_deg1Roots (List.mem_append_left _ hν₁)
      have hroot : ν₁ ∈ rootFinset .F4 := (mRoots_data ν₁ hν₁).1
      obtain ⟨c, hc⟩ : ∃ c : K, c = heisCoord Tag.F4 K w' ν₁ := ⟨_, rfl⟩
      obtain ⟨w₁, hw₁def⟩ : ∃ w₁ : ModGL Tag.F4 K, w₁ = pinnedX Tag.F4 K ν₁ (-c) * w' :=
        ⟨_, rfl⟩
      have hxQ : pinnedX Tag.F4 K ν₁ (-c) ∈ Qθ Tag.F4 K := pinnedX_mem_Qθ K hν₁D (-c)
      have hw₁ : w₁ ∈ Qθ Tag.F4 K := by rw [hw₁def]; exact mul_mem hxQ hw'
      have hcoord₁ : ∀ ν, heisCoord Tag.F4 K w₁ ν =
          (Pi.single ν₁ (-c) : (Fin Tag.F4.rank → ℤ) → K) ν + heisCoord Tag.F4 K w' ν := by
        intro ν
        rw [hw₁def, hs.mul _ hxQ _ hw', hs.pinnedX_deg1 ν₁ hν₁D (-c)]
        rfl
      have hcoord₁_self : heisCoord Tag.F4 K w₁ ν₁ = 0 := by
        rw [hcoord₁, Pi.single_eq_same, hc]; ring
      have hcoord₁_ne : ∀ ν, ν ≠ ν₁ → heisCoord Tag.F4 K w₁ ν = heisCoord Tag.F4 K w' ν := by
        intro ν hν
        rw [hcoord₁, Pi.single_eq_of_ne hν, zero_add]
      have hsupp₁ : ∀ ν, heisCoord Tag.F4 K w₁ ν ≠ 0 → ν ∈ l := by
        intro ν hν
        by_cases hνe : ν = ν₁
        · subst hνe
          exact absurd hcoord₁_self hν
        · have := hsupp ν (by rwa [hcoord₁_ne ν hνe] at hν)
          rcases List.mem_cons.1 this with h | h
          · exact absurd h hνe
          · exact h
      have hwdec : w' = pinnedX Tag.F4 K ν₁ c * w₁ := by
        rw [hw₁def, ← mul_assoc, ← pinnedX_add, add_neg_cancel, pinnedX_zero, one_mul]
      obtain ⟨hQ₁, hℓ₁, hμ₁⟩ := ih hl' w₁ hw₁ hsupp₁
      obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ModGL Tag.F4 K, y₁ = m * (w₁ * X * w₁⁻¹) * m⁻¹ := ⟨_, rfl⟩
      rw [← hy₁] at hQ₁ hℓ₁ hμ₁
      have hy : m * (w' * X * w'⁻¹) * m⁻¹ =
          (m * pinnedX Tag.F4 K ν₁ c * m⁻¹) * y₁ * (m * pinnedX Tag.F4 K ν₁ c * m⁻¹)⁻¹ := by
        rw [hy₁, hwdec]; group
      have hfmem : m * pinnedX Tag.F4 K ν₁ c * m⁻¹ ∈ conjSub m (rootSubgroup Tag.F4 K ν₁) :=
        mem_conjSub_iff.2 (by
          rw [show m⁻¹ * (m * pinnedX Tag.F4 K ν₁ c * m⁻¹) * m = pinnedX Tag.F4 K ν₁ c by group]
          exact F4Closure.pinnedX_mem_rootSubgroup_F4 ν₁ c)
      rw [hconj ν₁ (mem_rootFinset.1 hroot)] at hfmem
      obtain ⟨c₁, hc₁⟩ := mem_rootSubgroup.1 hfmem
      have hc₁zero : c₁ = 0 ↔ c = 0 := by
        constructor
        · intro h0
          rw [h0, pinnedX_zero] at hc₁
          have : pinnedX Tag.F4 K ν₁ c = 1 := by
            calc pinnedX Tag.F4 K ν₁ c = m⁻¹ * (m * pinnedX Tag.F4 K ν₁ c * m⁻¹) * m := by group
              _ = 1 := by rw [← hc₁]; group
          exact pinnedX_injective Tag.F4 K ν₁ (this.trans (pinnedX_zero _ _ _).symm)
        · intro h0
          rw [h0, pinnedX_zero, mul_one, mul_inv_cancel] at hc₁
          exact pinnedX_injective Tag.F4 K (s ν₁) (hc₁.trans (pinnedX_zero _ _ _).symm)
      rcases D.mdich ν₁ hν₁ with ⟨hℓ1, hs1⟩ | ⟨hℓ0, hsν, hρR, hρ0, hℓρ, hδρ⟩
      ·
        have hfQ : m * pinnedX Tag.F4 K ν₁ c * m⁻¹ ∈ Qθ Tag.F4 K := by
          rw [← hc₁, hs1]
          exact pinnedX_mem_Qθ K hν₁D c₁
        obtain ⟨hyQ, hyc⟩ := heisCoord_conj_Q K hfQ hQ₁
        rw [hy]
        have hne : ν₁ ≠ μ₀ := fun h => by rw [h] at hℓ1; omega
        refine ⟨hyQ, fun ν hν => ?_, ?_⟩
        · rw [hyc]; exact hℓ₁ ν hν
        · rw [hyc, ← hcoord₁_ne μ₀ (Ne.symm hne)]; exact hμ₁
      ·
        have hy' : m * (w' * X * w'⁻¹) * m⁻¹ =
            pinnedX Tag.F4 K (s ν₁) c₁ * y₁ * (pinnedX Tag.F4 K (s ν₁) c₁)⁻¹ := by
          rw [hy, hc₁]
        have hyQ := levi_conj_mem_Qθ K (mem_rootFinset.1 hρR) hρ0 c₁ hQ₁
        have hcoordy := hact (s ν₁) hρR hρ0 c₁ y₁ hQ₁
        have hl1 : ∀ ν, ℓ (ν - s ν₁) = ℓ ν - 1 := fun ν => by rw [D.ℓ_sub, hℓρ]
        have hl2 : ∀ ν, ℓ (ν - 2 • s ν₁) = ℓ ν - 2 := fun ν => by
          rw [D.ℓ_sub, D.ℓ_two, hℓρ]; ring
        have hv0 : ∀ ν, ℓ ν ≤ -2 → heisCoord Tag.F4 K y₁ ν = 0 := by
          intro ν hν
          rw [hℓ₁ ν (by omega)]
          refine Pi.single_eq_of_ne (fun h => ?_) _
          rw [h, D.ℓδ] at hν
          omega
        rw [hy']
        refine ⟨hyQ, fun ν hν => ?_, ?_⟩
        · rw [hcoordy]
          simp only [actFun]
          rw [hv0 (ν - s ν₁) (by rw [hl1]; omega), hv0 (ν - 2 • s ν₁) (by rw [hl2]; omega),
            mul_zero, mul_zero, add_zero, add_zero]
          exact hℓ₁ ν hν
        · by_cases hνμ : ν₁ = μ₀
          ·
            have hμs : μ₀ - s ν₁ = δ := by
              rw [← hνμ]
              exact sub_eq_iff_eq_add'.2 hsν.symm
            have hv1 : heisCoord Tag.F4 K y₁ (μ₀ - s ν₁) = s' := by
              rw [hℓ₁ (μ₀ - s ν₁) (by rw [hl1, hℓ]; omega), hμs, Pi.single_eq_same]
            have hv2 : heisCoord Tag.F4 K y₁ (μ₀ - 2 • s ν₁) = 0 :=
              hv0 _ (by rw [hl2, hℓ]; omega)
            have hw1z : heisCoord Tag.F4 K w₁ μ₀ = 0 := by rw [← hνμ]; exact hcoord₁_self
            have hvμ : heisCoord Tag.F4 K y₁ μ₀ = 0 := by
              by_contra hne
              exact (not_not.2 hw1z) (hμ₁.1 hne)
            have ha1 : ((a1 (s ν₁) δ : ℤ) : K) ≠ 0 := by
              have hsum : s ν₁ + δ ∈ rootFinset .F4 := by rw [hsν]; exact hroot
              have habs := (h1 (s ν₁) hρR hρ0 δ D.δ_deg1).1 hsum
              rw [if_neg hδρ] at habs
              rcases (abs_eq zero_le_one).1 habs with h | h <;> rw [h] <;> simp
            have hcμ : heisCoord Tag.F4 K w' μ₀ = c := by rw [← hνμ, hc]
            rw [hcoordy]
            simp only [actFun]
            rw [hv1, hv2, hvμ, hμs, mul_zero, add_zero, zero_add, hcμ]
            constructor
            · intro h hc0
              apply h
              rw [hc₁zero.2 hc0]
              ring
            · intro h h0
              rcases mul_eq_zero.1 h0 with h0 | h0
              · rcases mul_eq_zero.1 h0 with h0 | h0
                · exact h (hc₁zero.1 h0)
                · exact ha1 h0
              · exact hs'0 h0
          ·
            have hμs : μ₀ - s ν₁ ≠ δ := fun h => hνμ (by
              calc ν₁ = s ν₁ + δ := hsν.symm
                _ = s ν₁ + (μ₀ - s ν₁) := by rw [h]
                _ = μ₀ := by abel)
            have hv1 : heisCoord Tag.F4 K y₁ (μ₀ - s ν₁) = 0 := by
              rw [hℓ₁ (μ₀ - s ν₁) (by rw [hl1, hℓ]; omega)]
              exact Pi.single_eq_of_ne hμs _
            have hv2 : heisCoord Tag.F4 K y₁ (μ₀ - 2 • s ν₁) = 0 :=
              hv0 _ (by rw [hl2, hℓ]; omega)
            rw [hcoordy]
            simp only [actFun]
            rw [hv1, hv2, mul_zero, mul_zero, add_zero, add_zero]
            rw [hcoord₁_ne μ₀ (Ne.symm hνμ)] at hμ₁
            exact hμ₁
  have := key mRoots (fun _ h => h) w hw hwM
  exact ⟨this.1, this.2.2⟩

theorem case_two_generic {γ δ : Fin Tag.F4.rank → ℤ}
    {s : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)} {ℓ : (Fin Tag.F4.rank → ℤ) → ℤ}
    (D : CoverData γ δ s ℓ) {m : ModGL Tag.F4 K} (hm : m ∈ X1 K)
    (hconj : ∀ ν, IsRoot Tag.F4 ν →
      conjSub m (rootSubgroup Tag.F4 K ν) = rootSubgroup Tag.F4 K (s ν))
    {H : Subgroup (ModGL Tag.F4 K)} (hX : XS K ≤ H) {w : ModGL Tag.F4 K}
    (hw : w ∈ Qθ Tag.F4 K) (hwM : ∀ ν, heisCoord Tag.F4 K w ν ≠ 0 → ν ∈ mRoots)
    (hB : conjSub w (Heis.Uneg Tag.F4 K) ≤ H) {μ₀ : Fin Tag.F4.rank → ℤ} (hμ₀ : μ₀ ∈ mRoots)
    (hc : heisCoord Tag.F4 K w μ₀ ≠ 0) (hℓ : ℓ μ₀ = 0) : MPart K H := by
  have hs := heisCoord_spec Tag.F4 K
  have hγD : γ ∈ Deg1 Tag.F4 := deg1_iff.2 ⟨mem_rootFinset.1 D.γ_deg1.1, D.γ_deg1.2⟩
  have hγcomm : ∀ a : K, w * pinnedX Tag.F4 K γ a = pinnedX Tag.F4 K γ a * w := fun a =>
    hs.commute_disjoint w hw γ hγD a fun ν hν => D.disj ν (hwM ν hν)
  have hγH : ∀ a : K, pinnedX Tag.F4 K γ a ∈ H := fun a =>
    hX (X1_le_XS K (pinnedX_mem_rootSpan (S := S1set) D.γ_S1 a))
  have hAγ : rootSubgroup Tag.F4 K γ ≤ conjSub w⁻¹ H := by
    intro x hx
    obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
    rw [mem_conjSub_iff, inv_inv]
    rw [show w * pinnedX Tag.F4 K γ a * w⁻¹ = pinnedX Tag.F4 K γ a by rw [hγcomm a]; group]
    exact hγH a
  have hAneg : rootSubgroup Tag.F4 K (-theta) ≤ conjSub w⁻¹ H := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv]
    exact hB (mem_conjSub_iff.2 (by rw [show w⁻¹ * (w * x * w⁻¹) * w = x by group]; exact hx))
  have hneg : IsRoot Tag.F4 (-theta) := Heis.isRoot_neg_highRoot Tag.F4
  have hAsum := F4Closure.rootSubgroup_add_le_single (conjSub w⁻¹ H)
    (mem_rootFinset.1 D.γ_deg1.1) hneg D.ne
    (commPairs_eq_single D.pairs D.sum_root) (fun h => D.nr (mem_rootFinset.2 h)) hAγ hAneg
  rw [D.sum_eq] at hAsum
  have hXA := hAsum (F4Closure.pinnedX_mem_rootSubgroup_F4 (-δ) (1 : K))
  have hwXH : w * pinnedX Tag.F4 K (-δ) 1 * w⁻¹ ∈ H := by
    have := mem_conjSub_iff.1 hXA
    rwa [inv_inv] at this
  have hX1 : pinnedX Tag.F4 K (-δ) (1 : K) ≠ 1 := fun h =>
    one_ne_zero (pinnedX_injective Tag.F4 K (-δ) (h.trans (pinnedX_zero _ _ _).symm))
  obtain ⟨hyQ, hyc⟩ := transported_coord K D hconj
    (F4Closure.pinnedX_mem_rootSubgroup_F4 (-δ) 1) hX1 hℓ hw hwM
  have hmH : m ∈ H := hX (X1_le_XS K hm)
  exact ⟨m * (w * pinnedX Tag.F4 K (-δ) 1 * w⁻¹) * m⁻¹,
    mul_mem (mul_mem hmH hwXH) (inv_mem hmH), hyQ, μ₀, hμ₀, hyc.2 hc⟩

end Generic

end CaseTwo

theorem case_two_core (K : Type) [Field K] {H : Subgroup (ModGL Tag.F4 K)} (hX : XS K ≤ H)
    {w : ModGL Tag.F4 K} (hw : w ∈ Qθ Tag.F4 K)
    (hwM : ∀ ν, heisCoord Tag.F4 K w ν ≠ 0 → ν ∈ mRoots)
    (hw0 : ∃ ν, heisCoord Tag.F4 K w ν ≠ 0)
    (hB : conjSub w (Heis.Uneg Tag.F4 K) ≤ H) : MPart K H := by
  obtain ⟨μ₀, hμ₀⟩ := hw0
  have hμ₀M := hwM μ₀ hμ₀
  rcases CaseTwo.cover_dichotomy μ₀ hμ₀M with h | h
  · exact CaseTwo.case_two_generic K CaseTwo.coverData_alpha1 (nB_mem K)
      (fun ν hν => conjSub_nB K hν) hX hw hwM hB hμ₀M hμ₀ h
  · exact CaseTwo.case_two_generic K CaseTwo.coverData_root1342 (nA_mem K)
      (fun ν hν => conjSub_nA K hν) hX hw hwM hB hμ₀M hμ₀ h

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
