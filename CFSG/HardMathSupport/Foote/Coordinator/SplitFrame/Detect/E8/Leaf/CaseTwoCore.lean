module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.Action
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Transport
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureE8

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false

namespace CaseTwo

@[expose] def vP : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 3, 2, 1]

@[expose] def vQ : Fin Tag.E8.rank → ℤ := ![0, 0, 0, 0, 0, 1, 1, 1]

@[expose] def wordA : List (Fin 4) := [0, 1, 2, 1, 0]

@[expose] def wordB : List (Fin 4) := [0, 1, 2, 3, 2, 1, 0]

@[expose] def sA (v : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ := wordA.foldr reflGen v

@[expose] def sB (v : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ := wordB.foldr reflGen v

@[expose] def ellA (ν : Fin Tag.E8.rank → ℤ) : ℤ := ν 4 - ν 5

@[expose] def ellB (ν : Fin Tag.E8.rank → ℤ) : ℤ := ν 5 + ν 7 - ν 4

theorem vP_vQ : vP + vQ = theta ∧ vP ∈ sRootsList ∧ vQ ∈ sRootsList ∧ vP 4 % 5 = 0 ∧
    vQ 4 % 5 = 0 ∧ ellA vQ = -1 ∧ ellB vP = -1 := by decide +kernel

theorem s_data : sA theta = vP ∧ sA (-vQ) = vQ ∧ sB theta = vQ ∧ sB (-vP) = vP := by
  decide +kernel

theorem cover_data : ∀ ν ∈ mRoots,
    ((ellA ν = 1 ∧ sA ν = ν) ∨
      (ellA ν = 0 ∧ sA ν + vQ = ν ∧ sA ν 7 = 0 ∧ ellA (sA ν) = 1)) ∧
    ((ellB ν = 1 ∧ sB ν = ν) ∨
      (ellB ν = 0 ∧ sB ν + vP = ν ∧ sB ν 7 = 0 ∧ ellB (sB ν) = 1)) ∧
    (ellA ν = 0 ∨ ellB ν = 0) := by decide +kernel

end CaseTwo


namespace CaseTwo

structure CoverData (γ δ : Fin Tag.E8.rank → ℤ)
    (s : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ))
    (ℓ : (Fin Tag.E8.rank → ℤ) → ℤ) : Prop where
  γ_S1 : γ ∈ S1set
  γ_root : IsRoot Tag.E8 γ
  γ_deg : γ 7 = 1
  δ_root : IsRoot Tag.E8 δ
  δ_deg : δ 7 = 1
  disj : ∀ ν ∈ mRoots, ν + γ ∉ rootFinset .E8
  sum_eq : γ + -theta = -δ
  sroot : ∀ ν, IsRoot Tag.E8 ν → IsRoot Tag.E8 (s ν)
  sθ : s theta = γ
  sδ : s (-δ) = δ
  ℓδ : ℓ δ = -1
  ℓ_sub : ∀ a b, ℓ (a - b) = ℓ a - ℓ b
  mdich : ∀ ν ∈ mRoots, (ℓ ν = 1 ∧ s ν = ν) ∨
    (ℓ ν = 0 ∧ s ν + δ = ν ∧ s ν 7 = 0 ∧ ℓ (s ν) = 1)

theorem coverData_of {γ δ : Fin Tag.E8.rank → ℤ}
    {s : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ)} {ℓ : (Fin Tag.E8.rank → ℤ) → ℤ}
    (hγ : γ ∈ sRootsList) (hδ : δ ∈ sRootsList) (hsum : γ + δ = theta) (hδ4 : δ 4 % 5 = 0)
    (hsroot : ∀ ν, IsRoot Tag.E8 ν → IsRoot Tag.E8 (s ν)) (hsθ : s theta = γ)
    (hsδ : s (-δ) = δ) (hℓδ : ℓ δ = -1) (hℓ : ∀ a b, ℓ (a - b) = ℓ a - ℓ b)
    (hm : ∀ ν ∈ mRoots, (ℓ ν = 1 ∧ s ν = ν) ∨
      (ℓ ν = 0 ∧ s ν + δ = ν ∧ s ν 7 = 0 ∧ ℓ (s ν) = 1)) : CoverData γ δ s ℓ := by
  obtain ⟨hγR, hγ7, hγS⟩ := sRootsList_data γ hγ
  obtain ⟨hδR, hδ7, -⟩ := sRootsList_data δ hδ
  refine ⟨hγS, mem_rootFinset.1 hγR, hγ7, mem_rootFinset.1 hδR, hδ7, ?_, ?_, hsroot, hsθ, hsδ,
    hℓδ, hℓ, hm⟩
  · intro ν hν hmem
    obtain ⟨-, hν7, hν4⟩ := mem_mRoots.1 hν
    have h2 : (ν + γ) 7 = 2 := by rw [Pi.add_apply, hν7, hγ7]; norm_num
    have e := deg_eq_two (ν + γ) hmem h2
    have : ν = δ := add_right_cancel (e.trans (by rw [← hsum, add_comm]))
    exact hν4 (this ▸ hδ4)
  · rw [← hsum]
    abel

theorem isRoot_foldr_reflGen (W : List (Fin 4)) {γ : Fin Tag.E8.rank → ℤ}
    (hγ : IsRoot Tag.E8 γ) : IsRoot Tag.E8 (W.foldr reflGen γ) := by
  induction W with
  | nil => exact hγ
  | cons i W ih => exact isRoot_reflGen i ih

theorem coverData_A : CoverData vP vQ sA ellA := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := vP_vQ
  obtain ⟨h8, h9, -, -⟩ := s_data
  exact coverData_of h2 h3 h1 h5 (fun ν hν => isRoot_foldr_reflGen wordA hν) h8 h9 h6
    (fun a b => by simp only [ellA, Pi.sub_apply]; ring) fun ν hν => (cover_data ν hν).1

theorem coverData_B : CoverData vQ vP sB ellB := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := vP_vQ
  obtain ⟨-, -, h8, h9⟩ := s_data
  exact coverData_of h3 h2 (by rw [add_comm]; exact h1) h4
    (fun ν hν => isRoot_foldr_reflGen wordB hν) h8 h9 h7
    (fun a b => by simp only [ellB, Pi.sub_apply]; ring) fun ν hν => (cover_data ν hν).2.1

section Generic

variable (K : Type) [Field K]

theorem isRoot_theta_E8 : IsRoot Tag.E8 theta := mem_rootFinset.1 theta_mem

theorem commute_theta_pinnedX_deg0 {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (h0 : β 7 = 0)
    (s t : K) : Commute (pinnedX Tag.E8 K theta s) (pinnedX Tag.E8 K β t) := by
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg β (mem_rootFinset.2 hβ) (Or.inl h0)
  refine Heis.commute_pinnedX_of_commPairs_nil Tag.E8 K isRoot_theta_E8 hβ hne hne' ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact commCandidates_theta_data β (mem_rootFinset.2 hβ) (Or.inl h0) p hp.1
    (mem_rootFinset.2 hp.2)

theorem pinnedX_mem_Pθ_deg0 {ρ : Fin Tag.E8.rank → ℤ} (hρ : IsRoot Tag.E8 ρ) (h0 : ρ 7 = 0)
    (c : K) : pinnedX Tag.E8 K ρ c ∈ Pθ Tag.E8 K := by
  refine Heis.centralizer_Uθ_le_Pθ Tag.E8 K (pinnedX_mem_adjointGroup ρ c) fun x hx => ?_
  obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
  exact (commute_theta_pinnedX_deg0 K hρ h0 a c).eq.symm

theorem levi_conj_mem_Qθ {ρ : Fin Tag.E8.rank → ℤ} (hρ : IsRoot Tag.E8 ρ) (h0 : ρ 7 = 0) (c : K)
    {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K) :
    pinnedX Tag.E8 K ρ c * q * (pinnedX Tag.E8 K ρ c)⁻¹ ∈ Qθ Tag.E8 K := by
  have hn := parabolicSubgroup_le_normalizer_parabolicRadical (τ := Tag.E8) (K := K)
    (Heis.Jθ Tag.E8) (pinnedX_mem_Pθ_deg0 K hρ h0 c)
  exact (Subgroup.mem_normalizer_iff.1 hn q).1 hq

theorem heisCoord_conj_Q {g q : ModGL Tag.E8 K} (hg : g ∈ Qθ Tag.E8 K) (hq : q ∈ Qθ Tag.E8 K) :
    g * q * g⁻¹ ∈ Qθ Tag.E8 K ∧ heisCoord Tag.E8 K (g * q * g⁻¹) = heisCoord Tag.E8 K q := by
  have hs := heisCoord_spec Tag.E8 K
  refine ⟨mul_mem (mul_mem hg hq) (inv_mem hg), ?_⟩
  rw [hs.mul _ (mul_mem hg hq) _ (inv_mem hg), hs.mul _ hg _ hq, heisCoord_inv hg]
  abel

theorem transported_coord {γ δ : Fin Tag.E8.rank → ℤ}
    {s : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ)} {ℓ : (Fin Tag.E8.rank → ℤ) → ℤ}
    (D : CoverData γ δ s ℓ) {m X : ModGL Tag.E8 K}
    (hconj : ∀ ν, IsRoot Tag.E8 ν →
      conjSub m (rootSubgroup Tag.E8 K ν) = rootSubgroup Tag.E8 K (s ν))
    (hXmem : X ∈ rootSubgroup Tag.E8 K (-δ)) (hX1 : X ≠ 1) {μ₀ : Fin Tag.E8.rank → ℤ}
    (hℓ : ℓ μ₀ = 0) {w : ModGL Tag.E8 K} (hw : w ∈ Qθ Tag.E8 K)
    (hwM : ∀ ν, heisCoord Tag.E8 K w ν ≠ 0 → ν ∈ mRoots) :
    m * (w * X * w⁻¹) * m⁻¹ ∈ Qθ Tag.E8 K ∧
      (heisCoord Tag.E8 K (m * (w * X * w⁻¹) * m⁻¹) μ₀ ≠ 0 ↔ heisCoord Tag.E8 K w μ₀ ≠ 0) := by
  have hs := heisCoord_spec Tag.E8 K
  obtain ⟨a, hAdm, hact⟩ := exists_action_data K
  have hδD : δ ∈ Deg1 Tag.E8 := mem_Deg1_E8.2 ⟨D.δ_root, D.δ_deg⟩
  have hγD : γ ∈ Deg1 Tag.E8 := mem_Deg1_E8.2 ⟨D.γ_root, D.γ_deg⟩
  obtain ⟨s', hs'0, hs'⟩ : ∃ s' : K, s' ≠ 0 ∧ m * X * m⁻¹ = pinnedX Tag.E8 K δ s' := by
    have hmem : m * X * m⁻¹ ∈ conjSub m (rootSubgroup Tag.E8 K (-δ)) :=
      mem_conjSub_iff.2 (by rw [show m⁻¹ * (m * X * m⁻¹) * m = X by group]; exact hXmem)
    rw [hconj _ (IsRoot.neg D.δ_root), D.sδ] at hmem
    obtain ⟨s', hs'⟩ := mem_rootSubgroup.1 hmem
    refine ⟨s', fun h0 => hX1 ?_, hs'.symm⟩
    rw [h0, pinnedX_zero] at hs'
    calc X = m⁻¹ * (m * X * m⁻¹) * m := by group
      _ = 1 := by rw [← hs']; group
  have hδQ : pinnedX Tag.E8 K δ s' ∈ Qθ Tag.E8 K := pinnedX_mem_Qθ_of_mem_Deg1 hδD s'
  have hy_eq : ∀ w' : ModGL Tag.E8 K, m * (w' * X * w'⁻¹) * m⁻¹ =
      (m * w' * m⁻¹) * pinnedX Tag.E8 K δ s' * (m * w' * m⁻¹)⁻¹ := by
    intro w'
    rw [← hs']
    group
  have key : ∀ l : List (Fin Tag.E8.rank → ℤ), (∀ ν ∈ l, ν ∈ mRoots) →
      ∀ w' : ModGL Tag.E8 K, w' ∈ Qθ Tag.E8 K → (∀ ν, heisCoord Tag.E8 K w' ν ≠ 0 → ν ∈ l) →
        m * (w' * X * w'⁻¹) * m⁻¹ ∈ Qθ Tag.E8 K ∧
        (∀ ν, ℓ ν ≤ -1 →
          heisCoord Tag.E8 K (m * (w' * X * w'⁻¹) * m⁻¹) ν =
            (Pi.single δ s' : (Fin Tag.E8.rank → ℤ) → K) ν) ∧
        (heisCoord Tag.E8 K (m * (w' * X * w'⁻¹) * m⁻¹) μ₀ ≠ 0 ↔
          heisCoord Tag.E8 K w' μ₀ ≠ 0) := by
    intro l
    induction l with
    | nil =>
      intro _ w' hw' hsupp
      have h0 : heisCoord Tag.E8 K w' = 0 := funext fun ν => by
        by_contra hne
        exact List.not_mem_nil (hsupp ν hne)
      have hU : w' ∈ Uθ Tag.E8 K := (hs.eq_zero_iff w' hw').1 h0
      have hu : m * w' * m⁻¹ ∈ rootSubgroup Tag.E8 K γ := by
        have h' := hconj theta isRoot_theta_E8
        rw [D.sθ] at h'
        have hmem : m * w' * m⁻¹ ∈ conjSub m (rootSubgroup Tag.E8 K theta) :=
          mem_conjSub_iff.2 (by rw [show m⁻¹ * (m * w' * m⁻¹) * m = w' by group]; exact hU)
        rwa [h'] at hmem
      obtain ⟨z, hz⟩ := mem_rootSubgroup.1 hu
      have huQ : m * w' * m⁻¹ ∈ Qθ Tag.E8 K := by
        rw [← hz]; exact pinnedX_mem_Qθ_of_mem_Deg1 hγD z
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
      obtain ⟨hroot, hν₁7, -⟩ := mem_mRoots.1 hν₁
      have hν₁D : ν₁ ∈ Deg1 Tag.E8 := mem_Deg1_E8.2 ⟨hroot, hν₁7⟩
      obtain ⟨c, hc⟩ : ∃ c : K, c = heisCoord Tag.E8 K w' ν₁ := ⟨_, rfl⟩
      obtain ⟨w₁, hw₁def⟩ : ∃ w₁ : ModGL Tag.E8 K, w₁ = pinnedX Tag.E8 K ν₁ (-c) * w' :=
        ⟨_, rfl⟩
      have hxQ : pinnedX Tag.E8 K ν₁ (-c) ∈ Qθ Tag.E8 K := pinnedX_mem_Qθ_of_mem_Deg1 hν₁D (-c)
      have hw₁ : w₁ ∈ Qθ Tag.E8 K := by rw [hw₁def]; exact mul_mem hxQ hw'
      have hcoord₁ : ∀ ν, heisCoord Tag.E8 K w₁ ν =
          (Pi.single ν₁ (-c) : (Fin Tag.E8.rank → ℤ) → K) ν + heisCoord Tag.E8 K w' ν := by
        intro ν
        rw [hw₁def, hs.mul _ hxQ _ hw', hs.pinnedX_deg1 ν₁ hν₁D (-c)]
        rfl
      have hcoord₁_self : heisCoord Tag.E8 K w₁ ν₁ = 0 := by
        rw [hcoord₁, Pi.single_eq_same, hc]; ring
      have hcoord₁_ne : ∀ ν, ν ≠ ν₁ → heisCoord Tag.E8 K w₁ ν = heisCoord Tag.E8 K w' ν := by
        intro ν hν
        rw [hcoord₁, Pi.single_eq_of_ne hν, zero_add]
      have hsupp₁ : ∀ ν, heisCoord Tag.E8 K w₁ ν ≠ 0 → ν ∈ l := by
        intro ν hν
        by_cases hνe : ν = ν₁
        · subst hνe
          exact absurd hcoord₁_self hν
        · have := hsupp ν (by rwa [hcoord₁_ne ν hνe] at hν)
          rcases List.mem_cons.1 this with h | h
          · exact absurd h hνe
          · exact h
      have hwdec : w' = pinnedX Tag.E8 K ν₁ c * w₁ := by
        rw [hw₁def, ← mul_assoc, ← pinnedX_add, add_neg_cancel, pinnedX_zero, one_mul]
      obtain ⟨hQ₁, hℓ₁, hμ₁⟩ := ih hl' w₁ hw₁ hsupp₁
      obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ModGL Tag.E8 K, y₁ = m * (w₁ * X * w₁⁻¹) * m⁻¹ := ⟨_, rfl⟩
      rw [← hy₁] at hQ₁ hℓ₁ hμ₁
      have hy : m * (w' * X * w'⁻¹) * m⁻¹ =
          (m * pinnedX Tag.E8 K ν₁ c * m⁻¹) * y₁ * (m * pinnedX Tag.E8 K ν₁ c * m⁻¹)⁻¹ := by
        rw [hy₁, hwdec]; group
      have hfmem : m * pinnedX Tag.E8 K ν₁ c * m⁻¹ ∈ conjSub m (rootSubgroup Tag.E8 K ν₁) :=
        mem_conjSub_iff.2 (by
          rw [show m⁻¹ * (m * pinnedX Tag.E8 K ν₁ c * m⁻¹) * m = pinnedX Tag.E8 K ν₁ c by group]
          exact pinnedX_mem_rootSubgroup ν₁ c)
      rw [hconj ν₁ hroot] at hfmem
      obtain ⟨c₁, hc₁⟩ := mem_rootSubgroup.1 hfmem
      have hc₁zero : c₁ = 0 ↔ c = 0 := by
        constructor
        · intro h0
          rw [h0, pinnedX_zero] at hc₁
          have : pinnedX Tag.E8 K ν₁ c = 1 := by
            calc pinnedX Tag.E8 K ν₁ c = m⁻¹ * (m * pinnedX Tag.E8 K ν₁ c * m⁻¹) * m := by group
              _ = 1 := by rw [← hc₁]; group
          exact pinnedX_injective Tag.E8 K ν₁ (this.trans (pinnedX_zero _ _ _).symm)
        · intro h0
          rw [h0, pinnedX_zero, mul_one, mul_inv_cancel] at hc₁
          exact pinnedX_injective Tag.E8 K (s ν₁) (hc₁.trans (pinnedX_zero _ _ _).symm)
      rcases D.mdich ν₁ hν₁ with ⟨hℓ1, hs1⟩ | ⟨hℓ0, hsν, hρ0, hℓρ⟩
      ·
        have hfQ : m * pinnedX Tag.E8 K ν₁ c * m⁻¹ ∈ Qθ Tag.E8 K := by
          rw [← hc₁, hs1]
          exact pinnedX_mem_Qθ_of_mem_Deg1 hν₁D c₁
        obtain ⟨hyQ, hyc⟩ := heisCoord_conj_Q K hfQ hQ₁
        rw [hy]
        have hne : ν₁ ≠ μ₀ := fun h => by rw [h] at hℓ1; omega
        refine ⟨hyQ, fun ν hν => ?_, ?_⟩
        · rw [hyc]; exact hℓ₁ ν hν
        · rw [hyc, ← hcoord₁_ne μ₀ (Ne.symm hne)]; exact hμ₁
      ·
        have hρR : IsRoot Tag.E8 (s ν₁) := D.sroot ν₁ hroot
        have hy' : m * (w' * X * w'⁻¹) * m⁻¹ =
            pinnedX Tag.E8 K (s ν₁) c₁ * y₁ * (pinnedX Tag.E8 K (s ν₁) c₁)⁻¹ := by
          rw [hy, hc₁]
        have hyQ := levi_conj_mem_Qθ K hρR hρ0 c₁ hQ₁
        have hcoordy := hact (s ν₁) (mem_rootFinset.2 hρR) hρ0 c₁ y₁ hQ₁
        have hl1 : ∀ ν, ℓ (ν - s ν₁) = ℓ ν - 1 := fun ν => by rw [D.ℓ_sub, hℓρ]
        have hv0 : ∀ ν, ℓ ν ≤ -2 → heisCoord Tag.E8 K y₁ ν = 0 := by
          intro ν hν
          rw [hℓ₁ ν (by omega)]
          refine Pi.single_eq_of_ne (fun h => ?_) _
          rw [h, D.ℓδ] at hν
          omega
        rw [hy']
        refine ⟨hyQ, fun ν hν => ?_, ?_⟩
        · rw [hcoordy]
          simp only [actFun]
          rw [hv0 (ν - s ν₁) (by rw [hl1]; omega), mul_zero, add_zero]
          exact hℓ₁ ν hν
        · by_cases hνμ : ν₁ = μ₀
          ·
            have hμs : μ₀ - s ν₁ = δ := by
              rw [← hνμ]
              exact sub_eq_iff_eq_add'.2 hsν.symm
            have hv1 : heisCoord Tag.E8 K y₁ (μ₀ - s ν₁) = s' := by
              rw [hℓ₁ (μ₀ - s ν₁) (by rw [hl1, hℓ]; omega), hμs, Pi.single_eq_same]
            have hw1z : heisCoord Tag.E8 K w₁ μ₀ = 0 := by rw [← hνμ]; exact hcoord₁_self
            have hvμ : heisCoord Tag.E8 K y₁ μ₀ = 0 := by
              by_contra hne
              exact (not_not.2 hw1z) (hμ₁.1 hne)
            have ha1 : ((a (s ν₁) δ : ℤ) : K) ≠ 0 := by
              have hsum : s ν₁ + δ ∈ rootFinset .E8 := by rw [hsν]; exact mem_rootFinset.2 hroot
              have habs := (hAdm (s ν₁) (mem_rootFinset.2 hρR) hρ0 δ
                (mem_deg1Roots.2 ⟨D.δ_root, D.δ_deg⟩)).1 hsum
              rcases (abs_eq zero_le_one).1 habs with h | h <;> rw [h] <;> simp
            have hcμ : heisCoord Tag.E8 K w' μ₀ = c := by rw [← hνμ, hc]
            rw [hcoordy]
            simp only [actFun]
            rw [hv1, hvμ, hμs, zero_add, hcμ]
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
            have hv1 : heisCoord Tag.E8 K y₁ (μ₀ - s ν₁) = 0 := by
              rw [hℓ₁ (μ₀ - s ν₁) (by rw [hl1, hℓ]; omega)]
              exact Pi.single_eq_of_ne hμs _
            rw [hcoordy]
            simp only [actFun]
            rw [hv1, mul_zero, add_zero]
            rw [hcoord₁_ne μ₀ (Ne.symm hνμ)] at hμ₁
            exact hμ₁
  have := key mRoots.toList (fun _ h => Finset.mem_toList.1 h) w hw
    (fun ν hν => Finset.mem_toList.2 (hwM ν hν))
  exact ⟨this.1, this.2.2⟩

theorem case_two_generic {γ δ : Fin Tag.E8.rank → ℤ}
    {s : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ)} {ℓ : (Fin Tag.E8.rank → ℤ) → ℤ}
    (D : CoverData γ δ s ℓ) {m : ModGL Tag.E8 K} (hm : m ∈ X1 K)
    (hconj : ∀ ν, IsRoot Tag.E8 ν →
      conjSub m (rootSubgroup Tag.E8 K ν) = rootSubgroup Tag.E8 K (s ν))
    {H : Subgroup (ModGL Tag.E8 K)} (hX : XS K ≤ H) {w : ModGL Tag.E8 K}
    (hw : w ∈ Qθ Tag.E8 K) (hwM : ∀ ν, heisCoord Tag.E8 K w ν ≠ 0 → ν ∈ mRoots)
    (hB : conjSub w (Heis.Uneg Tag.E8 K) ≤ H) {μ₀ : Fin Tag.E8.rank → ℤ} (hμ₀ : μ₀ ∈ mRoots)
    (hc : heisCoord Tag.E8 K w μ₀ ≠ 0) (hℓ : ℓ μ₀ = 0) : MPart K H := by
  have hs := heisCoord_spec Tag.E8 K
  have hγD : γ ∈ Deg1 Tag.E8 := mem_Deg1_E8.2 ⟨D.γ_root, D.γ_deg⟩
  have hγcomm : ∀ a : K, w * pinnedX Tag.E8 K γ a = pinnedX Tag.E8 K γ a * w := fun a =>
    hs.commute_disjoint w hw γ hγD a fun ν hν => D.disj ν (hwM ν hν)
  have hγH : ∀ a : K, pinnedX Tag.E8 K γ a ∈ H := fun a =>
    hX (X1_le_XS K (pinnedX_mem_rootSpan (S := S1set) D.γ_S1 a))
  have hAγ : rootSubgroup Tag.E8 K γ ≤ conjSub w⁻¹ H := by
    intro x hx
    obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
    rw [mem_conjSub_iff, inv_inv]
    rw [show w * pinnedX Tag.E8 K γ a * w⁻¹ = pinnedX Tag.E8 K γ a by rw [hγcomm a]; group]
    exact hγH a
  have hAneg : rootSubgroup Tag.E8 K (-theta) ≤ conjSub w⁻¹ H := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv]
    exact hB (mem_conjSub_iff.2 (by rw [show w⁻¹ * (w * x * w⁻¹) * w = x by group]; exact hx))
  have hneg : IsRoot Tag.E8 (-theta) := Heis.isRoot_neg_highRoot Tag.E8
  have hne : γ ≠ -theta := fun h => by
    have h7 := congrFun h 7
    have h8 : (-theta) 7 = -2 := by decide +kernel
    rw [D.γ_deg, h8] at h7
    omega
  have hsum : IsRoot Tag.E8 (γ + -theta) := by
    rw [D.sum_eq]
    exact IsRoot.neg D.δ_root
  have hAsum := rootSubgroup_add_le (conjSub w⁻¹ H) D.γ_root hneg hsum hne hAγ hAneg
  rw [D.sum_eq] at hAsum
  have hXA := hAsum (pinnedX_mem_rootSubgroup (-δ) (1 : K))
  have hwXH : w * pinnedX Tag.E8 K (-δ) 1 * w⁻¹ ∈ H := by
    have := mem_conjSub_iff.1 hXA
    rwa [inv_inv] at this
  have hX1 : pinnedX Tag.E8 K (-δ) (1 : K) ≠ 1 := fun h =>
    one_ne_zero (pinnedX_injective Tag.E8 K (-δ) (h.trans (pinnedX_zero _ _ _).symm))
  obtain ⟨hyQ, hyc⟩ := transported_coord K D hconj
    (pinnedX_mem_rootSubgroup (-δ) 1) hX1 hℓ hw hwM
  have hmH : m ∈ H := hX (X1_le_XS K hm)
  exact ⟨m * (w * pinnedX Tag.E8 K (-δ) 1 * w⁻¹) * m⁻¹,
    mul_mem (mul_mem hmH hwXH) (inv_mem hmH), hyQ, μ₀, hμ₀, hyc.2 hc⟩

end Generic

end CaseTwo

theorem case_two_core (K : Type) [Field K] {H : Subgroup (ModGL Tag.E8 K)} (hX : XS K ≤ H)
    {w : ModGL Tag.E8 K} (hw : w ∈ Qθ Tag.E8 K)
    (hwM : ∀ ν, heisCoord Tag.E8 K w ν ≠ 0 → ν ∈ mRoots)
    (hw0 : ∃ ν, heisCoord Tag.E8 K w ν ≠ 0)
    (hB : conjSub w (Heis.Uneg Tag.E8 K) ≤ H) : MPart K H := by
  obtain ⟨μ₀, hμ₀⟩ := hw0
  have hμ₀M := hwM μ₀ hμ₀
  rcases (CaseTwo.cover_data μ₀ hμ₀M).2.2 with h | h
  · obtain ⟨m, hm, hconj⟩ := exists_word_transport K CaseTwo.wordA
    exact CaseTwo.case_two_generic K CaseTwo.coverData_A hm hconj hX hw hwM hB hμ₀M hμ₀ h
  · obtain ⟨m, hm, hconj⟩ := exists_word_transport K CaseTwo.wordB
    exact CaseTwo.case_two_generic K CaseTwo.coverData_B hm hconj hX hw hwM hB hμ₀M hμ₀ h

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
