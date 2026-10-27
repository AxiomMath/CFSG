module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XRoot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement IsMulCommutative


theorem ne_pair_of_node0 {τ : Tag} {v w : Fin τ.rank → ℤ} (hv : v (node0 τ) = 1)
    (hw : w (node0 τ) = 0) : v ≠ w ∧ v ≠ -w := by
  constructor
  · intro h
    have := congrArg (fun f => f (node0 τ)) h
    omega
  · intro h
    have := congrArg (fun f => f (node0 τ)) h
    simp only [Pi.neg_apply] at this
    omega

@[expose] def conjSub {G : Type*} [Group G] (E : Subgroup G) (y : G)
    (hE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) : E →* E where
  toFun e := ⟨y * e * y⁻¹, hE e e.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjSub_val {G : Type*} [Group G] (E : Subgroup G) (y : G) (hE : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (e : E) : ((conjSub E y hE e : E) : G) = y * e * y⁻¹ :=
  rfl

theorem conj_mem_closure {G : Type*} [Group G] {S : Set G} {y : G}
    (hS : ∀ t ∈ S, y * t * y⁻¹ ∈ Subgroup.closure S) :
    ∀ e ∈ Subgroup.closure S, y * e * y⁻¹ ∈ Subgroup.closure S := by
  intro e he
  have h : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.closure_le]
    exact fun t ht => hS t ht
  exact h he

@[expose] noncomputable def fE {τ : Tag} {K : Type} [Field K] {Ψ : List (Fin τ.rank → ℤ)} {ι : Type*}
    (ψ : ι → Fin τ.rank → ℤ) (hψ : ∀ i, ψ i ∈ Ψ) (i : ι) (c : K) :
    ↥(Subgroup.closure (rootSet τ K Ψ)) :=
  ⟨rootEl τ K (ψ i) c, Subgroup.subset_closure ⟨ψ i, hψ i, c, rfl⟩⟩

theorem fE_add {τ : Tag} {K : Type} [Field K] {Ψ : List (Fin τ.rank → ℤ)} {ι : Type*}
    (ψ : ι → Fin τ.rank → ℤ) (hψ : ∀ i, ψ i ∈ Ψ) (i : ι) (c d : K) :
    fE ψ hψ i (c + d) = fE ψ hψ i c * fE ψ hψ i d := by
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  exact (rootEl_mul τ K (ψ i) c d).symm

theorem comm_mem_E {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    {Ψ : List (Fin τ.rank → ℤ)} (hroot : ∀ ε ∈ Ψ, IsRoot τ ε)
    (h0node : ∀ ε ∈ Ψ, ε (node0 τ) = 1) {β : Fin τ.rank → ℤ} (hβr : IsRoot τ β)
    (hβ0 : β (node0 τ) = 0)
    (hall : ∀ ε ∈ Ψ, 0 ≤ rf τ ε β ∨ (rf τ ε β = -1 ∧ ε + β ∈ Ψ ∧ IsRoot τ (ε + β)))
    {ε : Fin τ.rank → ℤ} (hε : ε ∈ Ψ) (c : K) :
    ⁅rootEl τ K β 1, rootEl τ K ε c⁆ ∈ Subgroup.closure (rootSet τ K Ψ) := by
  obtain ⟨hne, hne'⟩ := ne_pair_of_node0 (h0node ε hε) hβ0
  rcases hall ε hε with h0 | ⟨_, hsΨ, hsr⟩
  · rw [commutator_root_caseA hτ (hroot ε hε) hβr hne h0 c]
    exact one_mem _
  · obtain ⟨s, -, hs⟩ := commutator_root_caseB (K := K) hτ (hroot ε hε) hβr hne hne' hsr
    rw [hs c]
    exact Subgroup.subset_closure ⟨ε + β, hsΨ, s * c, rfl⟩


theorem add_node0 {τ : Tag} {v w : Fin τ.rank → ℤ} (hv : v (node0 τ) = 1) (hw : w (node0 τ) = 0) :
    (v + w) (node0 τ) = 1 := by
  simp [hv, hw]

set_option synthInstance.maxHeartbeats 400000 in
theorem central_coeff_zero {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    {Ψ : List (Fin τ.rank → ℤ)} (hΨ : PsiOK τ Ψ = true)
    [IsMulCommutative (Subgroup.closure (rootSet τ K Ψ))]
    (hchain : ∀ γ ∈ Ψ, ∃ β β' : Fin τ.rank → ℤ, chainOK τ Ψ γ β β' = true)
    {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : ι → Fin τ.rank → ℤ) (hψ : ∀ i, ψ i ∈ Ψ)
    (hinj : Function.Injective ψ) (x : ι → K)
    (hcent : (∏ i, fE ψ hψ i (x i)).1 ∈ Subgroup.center (adjointGroup τ K)) (i₀ : ι) :
    x i₀ = 0 := by
  have hS : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨hroot, h0node, hpos⟩ := PsiOK_spec hΨ
  obtain ⟨β, β', hch⟩ := hchain (ψ i₀) (hψ i₀)
  obtain ⟨hβr, hβ'r, hβ0, hβ'0, hγβ, hsum, hall, hcond⟩ := chainOK_spec hch
  have hγ0 : ψ i₀ (node0 τ) = 1 := h0node _ (hψ i₀)
  have hγr : IsRoot τ (ψ i₀) := hroot _ (hψ i₀)
  have hγsum : IsRoot τ (ψ i₀ + β) := by
    rcases hall _ (hψ i₀) with h0 | ⟨_, _, hr⟩
    · rw [hγβ] at h0
      norm_num at h0
    · exact hr
  have hconj : ∀ t ∈ rootSet τ K Ψ,
      rootEl τ K β 1 * t * (rootEl τ K β 1)⁻¹ ∈ Subgroup.closure (rootSet τ K Ψ) := by
    rintro _ ⟨ε, hε, c, rfl⟩
    have h1 : rootEl τ K β 1 * rootEl τ K ε c * (rootEl τ K β 1)⁻¹ =
        ⁅rootEl τ K β 1, rootEl τ K ε c⁆ * rootEl τ K ε c := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact mul_mem (comm_mem_E hS hroot h0node hβr hβ0 hall hε c)
      (Subgroup.subset_closure ⟨ε, hε, c, rfl⟩)
  let φ : ↥(Subgroup.closure (rootSet τ K Ψ)) →* ↥(Subgroup.closure (rootSet τ K Ψ)) :=
    conjSub _ (rootEl τ K β 1) (conj_mem_closure hconj)
  let f : ι → ↥(Subgroup.closure (rootSet τ K Ψ)) := fun i => fE ψ hψ i (x i)
  let w : ι → ↥(Subgroup.closure (rootSet τ K Ψ)) := fun i => φ (f i) * (f i)⁻¹
  have hfix : φ (∏ i, f i) = ∏ i, f i := by
    apply Subtype.ext
    have hc : rootEl τ K β 1 * (∏ i, f i).1 = (∏ i, f i).1 * rootEl τ K β 1 :=
      Subgroup.mem_center_iff.1 hcent (rootEl τ K β 1)
    rw [conjSub_val]
    rw [hc, mul_inv_cancel_right]
  have hφw : ∀ i, φ (f i) = w i * f i := fun i => by simp [w]
  have hprod : ∏ i, w i = 1 := prod_eq_one_of_fix φ f w hφw hfix
  have hwG : ∀ i, (w i : adjointGroup τ K) = ⁅rootEl τ K β 1, rootEl τ K (ψ i) (x i)⁆ := by
    intro i
    show rootEl τ K β 1 * rootEl τ K (ψ i) (x i) * (rootEl τ K β 1)⁻¹ *
        (rootEl τ K (ψ i) (x i))⁻¹ = _
    rw [commutatorElement_def]
  let y' : adjointGroup τ K := rootEl τ K β' 1
  let F : Subgroup ↥(Subgroup.closure (rootSet τ K Ψ)) :=
    (Subgroup.centralizer ({y'} : Set (adjointGroup τ K))).comap
      (Subgroup.closure (rootSet τ K Ψ)).subtype
  have hFmem : ∀ e : ↥(Subgroup.closure (rootSet τ K Ψ)),
      e ∈ F ↔ Commute y' (e : adjointGroup τ K) := by
    intro e
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact h y' (Set.mem_singleton y')
    · intro h g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact h
  have hwF : ∀ j ∈ Finset.univ.erase i₀, w j ∈ F := by
    intro j hj
    have hji : j ≠ i₀ := Finset.ne_of_mem_erase hj
    have hψne : ψ j ≠ ψ i₀ := fun h => hji (hinj h)
    rw [hFmem, hwG j]
    rcases hall _ (hψ j) with h0 | ⟨hrf, hsΨ, hsr⟩
    · rw [commutator_root_caseA hS (hroot _ (hψ j)) hβr
        (ne_pair_of_node0 (h0node _ (hψ j)) hβ0).1 h0 (x j)]
      exact Commute.one_right _
    · obtain ⟨s, -, hs⟩ := commutator_root_caseB (K := K) hS (hroot _ (hψ j)) hβr
        (ne_pair_of_node0 (h0node _ (hψ j)) hβ0).1
        (ne_pair_of_node0 (h0node _ (hψ j)) hβ0).2 hsr
      rw [hs (x j)]
      have hcomm := pinnedX_commute_of_rootForm_nonneg hS hsr hβ'r
        (ne_pair_of_node0 (add_node0 (h0node _ (hψ j)) hβ0) hβ'0).1
        (hcond (ψ j) (hψ j) hψne hrf) (s * x j) 1
      show rootEl τ K β' 1 * rootEl τ K (ψ j + β) (s * x j) =
        rootEl τ K (ψ j + β) (s * x j) * rootEl τ K β' 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, rootEl_val, rootEl_val]
      exact hcomm.symm.eq
  have hwi : w i₀ ∈ F := by
    rw [prod_erase_inv w hprod i₀]
    exact F.inv_mem (F.prod_mem hwF)
  rw [hFmem, hwG i₀] at hwi
  obtain ⟨s, hs, hs'⟩ := commutator_root_caseB (K := K) hS hγr hβr
    (ne_pair_of_node0 hγ0 hβ0).1 (ne_pair_of_node0 hγ0 hβ0).2 hγsum
  rw [hs' (x i₀)] at hwi
  have hcomm1 : ⁅rootEl τ K β' 1, rootEl τ K (ψ i₀ + β) (s * x i₀)⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.2 hwi
  obtain ⟨s', hs'', hs3⟩ := commutator_root_caseB (K := K) hS hγsum hβ'r
    (ne_pair_of_node0 (add_node0 hγ0 hβ0) hβ'0).1
    (ne_pair_of_node0 (add_node0 hγ0 hβ0) hβ'0).2 hsum
  rw [hs3 (s * x i₀)] at hcomm1
  have h2 : s' * (s * x i₀) = 0 := by
    have h3 := congrArg Subtype.val hcomm1
    rw [rootEl_val] at h3
    exact pinnedX_injective τ K _ (by rw [pinnedX_zero]; exact h3)
  have hunit : ∀ a : K, (a = 1 ∨ a = -1) → ∀ b : K, a * b = 0 → b = 0 := by
    intro a ha b hb
    rcases ha with rfl | rfl
    · simpa using hb
    · simpa using hb
  exact hunit s hs _ (hunit s' hs'' _ h2)

end CFSG.LocalAnalysis.GLTheoremA.I107X

end
