module

public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag} {M : Type*} [CommGroup M]

@[expose] def KernelSizes (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (sizes : List ℕ) : Prop :=
  (kernelRoots χ).ncard = sizes.sum ∧ Nat.card (KernelComponent χ) = sizes.length ∧
    ∀ n, {i : KernelComponent χ | (componentRoots χ i).ncard = n}.ncard = sizes.count n

theorem KernelSizes.of_perm {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {s t : List ℕ}
    (h : KernelSizes χ s) (hp : s.Perm t) : KernelSizes χ t :=
  ⟨h.1.trans hp.sum_eq, h.2.1.trans hp.length_eq, fun n => (h.2.2 n).trans (hp.count_eq n)⟩

theorem KernelSizes.subsingleton {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {n : ℕ}
    (h : KernelSizes χ [n]) : Subsingleton (KernelComponent χ) :=
  (Nat.card_eq_one_iff_unique.1 h.2.1).1

theorem KernelSizes.componentRoots_eq {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {n : ℕ}
    (h : KernelSizes χ [n]) (i : KernelComponent χ) : componentRoots χ i = kernelRoots χ := by
  have := h.subsingleton
  ext α
  exact ⟨fun ⟨hα, _⟩ => hα, fun hα => ⟨hα, Subsingleton.elim _ _⟩⟩

theorem KernelSizes.ncard_eq {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {n : ℕ}
    (h : KernelSizes χ [n]) : (kernelRoots χ).ncard = n := by
  simpa using h.1

structure ComponentCert where
  lab : List ℕ
  mid : List ℕ

namespace ComponentCert

variable (τ) (S : ComponentCert) (inS : ℕ → Bool)

@[expose] def rt (k : ℕ) : Fin τ.rank → ℤ := τ.rootCertificate.root k

@[expose] def check : Bool :=
  (List.range τ.rootCount).all fun k => !(inS k) ||
    (decide (S.lab.getD k 0 < τ.rootCount) && inS (S.lab.getD k 0) &&
      (S.lab.getD (S.lab.getD k 0) 0 == S.lab.getD k 0) &&
      ((k == S.lab.getD k 0) ||
        decide (iform (rt τ k) (rt τ (S.lab.getD k 0)) ≠ 0) ||
        (decide (S.mid.getD k 0 < τ.rootCount) && inS (S.mid.getD k 0) &&
          decide (iform (rt τ k) (rt τ (S.mid.getD k 0)) ≠ 0) &&
          decide (iform (rt τ (S.mid.getD k 0)) (rt τ (S.lab.getD k 0)) ≠ 0))) &&
      (List.range τ.rootCount).all fun j => !(inS j) || (S.lab.getD k 0 == S.lab.getD j 0) ||
        decide (iform (rt τ k) (rt τ j) = 0))

@[expose] def sigmaIdx : List ℕ := (List.range τ.rootCount).filter inS

@[expose] def leaders : List ℕ := (sigmaIdx τ inS).filter fun ℓ => S.lab.getD ℓ 0 == ℓ

@[expose] def sizes : List ℕ :=
  (leaders τ S inS).map fun ℓ => ((sigmaIdx τ inS).map fun k => S.lab.getD k 0).count ℓ

section Sound

variable {τ} {S} {inS}

theorem nodup_sigmaIdx : (sigmaIdx τ inS).Nodup := List.nodup_range.filter _

theorem mem_sigmaIdx {k : ℕ} : k ∈ sigmaIdx τ inS ↔ k < τ.rootCount ∧ inS k = true := by
  simp [sigmaIdx]

theorem lt_of_mem_sigmaIdx {k : ℕ} (hk : k ∈ sigmaIdx τ inS) : k < τ.rootCount :=
  (mem_sigmaIdx.1 hk).1

variable {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem rt_injOn {k j : ℕ} (hk : k < τ.rootCount) (hj : j < τ.rootCount)
    (h : rt τ k = rt τ j) : k = j := by
  have hN := τ.rootCertificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hN
  rw [τ.rootCertificate_length] at hN
  exact List.inj_on_of_nodup_map hN (List.mem_range.2 hk) (List.mem_range.2 hj)
    (congrArg List.ofFn h)

variable (hS : ∀ k < τ.rootCount, inS k = true ↔ χ (Multiplicative.ofAdd (rt τ k)) = 1)

include hS in
theorem mem_kernelRoots_iff {α : Fin τ.rank → ℤ} :
    α ∈ kernelRoots χ ↔ ∃ k ∈ sigmaIdx τ inS, rt τ k = α := by
  constructor
  · rintro ⟨hα, hχ⟩
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
    rw [τ.rootCertificate_length] at hk
    exact ⟨k, mem_sigmaIdx.2 ⟨hk, (hS k hk).2 hχ⟩, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk' := mem_sigmaIdx.1 hk
    exact ⟨RootCertificate.isRoot_root τ.rootCertificate_check k
      (by rw [τ.rootCertificate_length]; exact hk'.1), (hS k hk'.1).1 hk'.2⟩

theorem check_spec (h : S.check τ inS = true) {k : ℕ} (hk : k ∈ sigmaIdx τ inS) :
    S.lab.getD k 0 < τ.rootCount ∧ inS (S.lab.getD k 0) = true ∧
    S.lab.getD (S.lab.getD k 0) 0 = S.lab.getD k 0 ∧
    (k = S.lab.getD k 0 ∨ iform (rt τ k) (rt τ (S.lab.getD k 0)) ≠ 0 ∨
      (S.mid.getD k 0 < τ.rootCount ∧ inS (S.mid.getD k 0) = true ∧
        iform (rt τ k) (rt τ (S.mid.getD k 0)) ≠ 0 ∧
        iform (rt τ (S.mid.getD k 0)) (rt τ (S.lab.getD k 0)) ≠ 0)) ∧
    ∀ j ∈ sigmaIdx τ inS, S.lab.getD k 0 ≠ S.lab.getD j 0 → iform (rt τ k) (rt τ j) = 0 := by
  simp only [check, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ne_eq] at h
  have hk' := mem_sigmaIdx.1 hk
  rcases h k hk'.1 with h0 | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · rw [hk'.2] at h0
    exact absurd h0 (by decide)
  · refine ⟨h1, h2, h3, ?_, ?_⟩
    · rcases h4 with (h4 | h4) | ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩
      · exact Or.inl h4
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr ⟨m1, m2, m3, m4⟩)
    · intro j hj hne
      have hj' := mem_sigmaIdx.1 hj
      rcases h5 j hj'.1 with (h6 | h6) | h6
      · rw [hj'.2] at h6
        exact absurd h6 (by decide)
      · exact absurd h6 hne
      · exact h6

variable (τ inS) in
noncomputable def idx (α : Fin τ.rank → ℤ) : ℕ :=
  Function.invFunOn (rt τ) {k | k ∈ sigmaIdx τ inS} α

variable (S inS) in
noncomputable def lam (α : Fin τ.rank → ℤ) : ℕ := S.lab.getD (idx τ inS α) 0

include hS in
theorem idx_spec {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) :
    idx τ inS α ∈ sigmaIdx τ inS ∧ rt τ (idx τ inS α) = α :=
  Function.invFunOn_pos ((mem_kernelRoots_iff hS).1 hα)

theorem idx_rt {k : ℕ} (hk : k ∈ sigmaIdx τ inS) : idx τ inS (rt τ k) = k := by
  have := Function.invFunOn_pos (f := rt τ) (s := {k | k ∈ sigmaIdx τ inS}) (b := rt τ k)
    ⟨k, hk, rfl⟩
  exact rt_injOn (lt_of_mem_sigmaIdx this.1) (lt_of_mem_sigmaIdx hk) this.2

variable (χ) in
def Adj (α β : kernelRoots χ) : Prop :=
  (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0

include hS in
def rootOf {k : ℕ} (hk : k ∈ sigmaIdx τ inS) : kernelRoots χ :=
  ⟨rt τ k, (mem_kernelRoots_iff hS).2 ⟨k, hk, rfl⟩⟩

theorem leader_mem (h : S.check τ inS = true) {k : ℕ} (hk : k ∈ sigmaIdx τ inS) :
    S.lab.getD k 0 ∈ sigmaIdx τ inS :=
  mem_sigmaIdx.2 ⟨(check_spec h hk).1, (check_spec h hk).2.1⟩

variable (h : S.check τ inS = true)

include hS h in
theorem lam_eq_of_eqvGen {a b : kernelRoots χ} (hab : Relation.EqvGen (Adj χ) a b) :
    lam S inS a.1 = lam S inS b.1 := by
  induction hab with
  | rel a b hr =>
    obtain ⟨hka, hra⟩ := idx_spec hS a.2
    obtain ⟨hkb, hrb⟩ := idx_spec hS b.2
    by_contra hne
    apply hr
    have := (check_spec h hka).2.2.2.2 _ hkb hne
    rw [hra, hrb] at this
    rw [dotProduct_mulVec_eq_iform]
    exact this
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

include hS h in
theorem eqvGen_leader {k : ℕ} (hk : k ∈ sigmaIdx τ inS) :
    Relation.EqvGen (Adj χ) (rootOf hS hk) (rootOf hS (leader_mem h hk)) := by
  obtain ⟨-, -, -, hc, -⟩ := check_spec h hk
  rcases hc with hc | hc | ⟨m1, m2, m3, m4⟩
  · have : rootOf hS hk = rootOf hS (leader_mem h hk) := Subtype.ext (congrArg (rt τ) hc)
    rw [this]
    exact Relation.EqvGen.refl _
  · refine Relation.EqvGen.rel _ _ ?_
    show rt τ k ⬝ᵥ (τ.symmetrizedCartan *ᵥ rt τ (S.lab.getD k 0)) ≠ 0
    rw [dotProduct_mulVec_eq_iform]
    exact hc
  · have hm : S.mid.getD k 0 ∈ sigmaIdx τ inS := mem_sigmaIdx.2 ⟨m1, m2⟩
    refine Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel (rootOf hS hk) (rootOf hS hm) ?_)
      (Relation.EqvGen.rel (rootOf hS hm) (rootOf hS (leader_mem h hk)) ?_)
    · show rt τ k ⬝ᵥ (τ.symmetrizedCartan *ᵥ rt τ (S.mid.getD k 0)) ≠ 0
      rw [dotProduct_mulVec_eq_iform]
      exact m3
    · show rt τ (S.mid.getD k 0) ⬝ᵥ (τ.symmetrizedCartan *ᵥ rt τ (S.lab.getD k 0)) ≠ 0
      rw [dotProduct_mulVec_eq_iform]
      exact m4

include hS h in
theorem eqvGen_of_lam_eq {a b : kernelRoots χ} (hab : lam S inS a.1 = lam S inS b.1) :
    Relation.EqvGen (Adj χ) a b := by
  obtain ⟨hka, hra⟩ := idx_spec hS a.2
  obtain ⟨hkb, hrb⟩ := idx_spec hS b.2
  have ha : a = rootOf hS hka := Subtype.ext hra.symm
  have hb : b = rootOf hS hkb := Subtype.ext hrb.symm
  have hlab : S.lab.getD (idx τ inS a.1) 0 = S.lab.getD (idx τ inS b.1) 0 := hab
  have hm : rootOf hS (leader_mem h hka) = rootOf hS (leader_mem h hkb) :=
    Subtype.ext (congrArg (rt τ) hlab)
  have key : Relation.EqvGen (Adj χ) (rootOf hS hka) (rootOf hS hkb) :=
    Relation.EqvGen.trans _ _ _ (eqvGen_leader hS h hka)
      (by rw [hm]; exact Relation.EqvGen.symm _ _ (eqvGen_leader hS h hkb))
  rw [← ha, ← hb] at key
  exact key

include hS h in
noncomputable def clsLab : KernelComponent χ → ℕ :=
  Quotient.lift (fun a : kernelRoots χ => lam S inS a.1) fun _ _ hab => lam_eq_of_eqvGen hS h hab

include hS h in
theorem clsLab_injective : Function.Injective (clsLab hS h) := by
  intro i j
  refine Quotient.inductionOn i fun a => Quotient.inductionOn j fun b hab => ?_
  exact Quotient.sound (eqvGen_of_lam_eq hS h hab)

include hS h in
theorem clsLab_mem_leaders (i : KernelComponent χ) : clsLab hS h i ∈ leaders τ S inS := by
  refine Quotient.inductionOn i fun a => ?_
  obtain ⟨hka, -⟩ := idx_spec hS a.2
  obtain ⟨h1, h2, h3, -⟩ := check_spec h hka
  show S.lab.getD (idx τ inS a.1) 0 ∈ leaders τ S inS
  simp only [leaders, List.mem_filter, beq_iff_eq]
  exact ⟨mem_sigmaIdx.2 ⟨h1, h2⟩, h3⟩

include hS h in
theorem mem_range_clsLab {ℓ : ℕ} (hℓ : ℓ ∈ leaders τ S inS) : ℓ ∈ Set.range (clsLab hS h) := by
  simp only [leaders, List.mem_filter, beq_iff_eq] at hℓ
  obtain ⟨hk, hlab⟩ := hℓ
  refine ⟨Quotient.mk _ (rootOf hS hk), ?_⟩
  show S.lab.getD (idx τ inS (rt τ ℓ)) 0 = ℓ
  rw [idx_rt hk]
  exact hlab

include hS h in
theorem componentRoots_eq (i : KernelComponent χ) :
    componentRoots χ i = rt τ '' {k | k ∈ sigmaIdx τ inS ∧ S.lab.getD k 0 = clsLab hS h i} := by
  refine Quotient.inductionOn i fun a => ?_
  ext α
  constructor
  · rintro ⟨hα, hi⟩
    have h1 : clsLab hS h (⟦⟨α, hα⟩⟧ : KernelComponent χ) = clsLab hS h (⟦a⟧ : KernelComponent χ) :=
      congrArg _ hi
    obtain ⟨hk, hr⟩ := idx_spec hS hα
    exact ⟨idx τ inS α, ⟨hk, h1⟩, hr⟩
  · rintro ⟨k, ⟨hk, hlab⟩, rfl⟩
    refine ⟨(mem_kernelRoots_iff hS).2 ⟨k, hk, rfl⟩, ?_⟩
    apply clsLab_injective hS h
    show S.lab.getD (idx τ inS (rt τ k)) 0 = clsLab hS h (⟦a⟧ : KernelComponent χ)
    rw [idx_rt hk]
    exact hlab

theorem nodup_leaders : (leaders τ S inS).Nodup := nodup_sigmaIdx.filter _

theorem count_map_eq_length_filter (l : List ℕ) (f : ℕ → ℕ) (ℓ : ℕ) :
    (l.map f).count ℓ = (l.filter fun k => f k == ℓ).length := by
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  rfl

include hS h in
theorem ncard_componentRoots (i : KernelComponent χ) :
    (componentRoots χ i).ncard =
      ((sigmaIdx τ inS).map fun k => S.lab.getD k 0).count (clsLab hS h i) := by
  rw [componentRoots_eq hS h i, Set.InjOn.ncard_image, count_map_eq_length_filter]
  · have hset : {k | k ∈ sigmaIdx τ inS ∧ S.lab.getD k 0 = clsLab hS h i} =
        ↑(((sigmaIdx τ inS).filter fun k => S.lab.getD k 0 == clsLab hS h i).toFinset) := by
      ext k
      simp
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_sigmaIdx.filter _)]
  · intro k hk j hj hkj
    exact rt_injOn (lt_of_mem_sigmaIdx hk.1) (lt_of_mem_sigmaIdx hj.1) hkj

include hS in
theorem ncard_kernelRoots_filter (P : (Fin τ.rank → ℤ) → Prop) [DecidablePred P] :
    {α | α ∈ kernelRoots χ ∧ P α}.ncard =
      ((sigmaIdx τ inS).filter fun k => decide (P (rt τ k))).length := by
  have hX : {α | α ∈ kernelRoots χ ∧ P α} =
      rt τ '' ↑(((sigmaIdx τ inS).filter fun k => decide (P (rt τ k))).toFinset) := by
    ext α
    rw [Set.mem_setOf_eq, mem_kernelRoots_iff hS]
    simp only [Set.mem_image, Finset.mem_coe, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hP⟩
      exact ⟨k, ⟨hk, hP⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hP⟩, rfl⟩
      exact ⟨⟨k, hk, rfl⟩, hP⟩
  rw [hX, Set.InjOn.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (nodup_sigmaIdx.filter _)]
  intro k hk j hj hkj
  exact rt_injOn (lt_of_mem_sigmaIdx (List.mem_filter.1 (List.mem_toFinset.1 hk)).1)
    (lt_of_mem_sigmaIdx (List.mem_filter.1 (List.mem_toFinset.1 hj)).1) hkj

include hS h in
theorem kernelSizes_of_check : KernelSizes χ (S.sizes τ inS) := by
  have hinj := clsLab_injective hS h
  set f : ℕ → ℕ := fun k => S.lab.getD k 0 with hf
  set cnt : ℕ → ℕ := fun ℓ => ((sigmaIdx τ inS).map f).count ℓ with hcnt
  have hrange : Set.range (clsLab hS h) = ↑(leaders τ S inS).toFinset := by
    ext ℓ
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ clsLab_mem_leaders hS h i, mem_range_clsLab hS h⟩
  refine ⟨?_, ?_, ?_⟩
  · have hX : kernelRoots χ = rt τ '' ↑((sigmaIdx τ inS).toFinset) := by
      ext α
      rw [mem_kernelRoots_iff hS]
      simp
    have hlead : (leaders τ S inS).toFinset = ((sigmaIdx τ inS).map f).toFinset := by
      ext ℓ
      simp only [List.mem_toFinset, List.mem_map]
      constructor
      · intro hℓ
        have := List.mem_filter.1 hℓ
        exact ⟨ℓ, this.1, beq_iff_eq.1 this.2⟩
      · rintro ⟨k, hk, rfl⟩
        obtain ⟨h1, h2, h3, -⟩ := check_spec h hk
        exact List.mem_filter.2 ⟨mem_sigmaIdx.2 ⟨h1, h2⟩, beq_iff_eq.2 h3⟩
    rw [hX, Set.InjOn.ncard_image, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup nodup_sigmaIdx]
    · calc (sigmaIdx τ inS).length = ((sigmaIdx τ inS).map f).length := (List.length_map _).symm
        _ = Multiset.card (↑((sigmaIdx τ inS).map f) : Multiset ℕ) := (Multiset.coe_card _).symm
        _ = ∑ a ∈ (↑((sigmaIdx τ inS).map f) : Multiset ℕ).toFinset,
              Multiset.count a (↑((sigmaIdx τ inS).map f) : Multiset ℕ) :=
            (Multiset.toFinset_sum_count_eq _).symm
        _ = ∑ a ∈ (leaders τ S inS).toFinset, cnt a := by
            have e : (↑((sigmaIdx τ inS).map f) : Multiset ℕ).toFinset =
                (leaders τ S inS).toFinset := hlead.symm
            rw [e]
            simp only [Multiset.coe_count, hcnt]
        _ = ((leaders τ S inS).map cnt).sum := List.sum_toFinset cnt nodup_leaders
    · intro k hk j hj hkj
      exact rt_injOn (lt_of_mem_sigmaIdx (by simpa using hk))
        (lt_of_mem_sigmaIdx (by simpa using hj)) hkj
  · rw [sizes, List.length_map, Nat.card_congr (Equiv.ofInjective _ hinj), Nat.card_coe_set_eq,
      hrange, Set.ncard_coe_finset, List.toFinset_card_of_nodup nodup_leaders]
  · intro n
    have hset : {i : KernelComponent χ | (componentRoots χ i).ncard = n} =
        clsLab hS h ⁻¹' {ℓ | ℓ ∈ leaders τ S inS ∧ cnt ℓ = n} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [ncard_componentRoots hS h i]
      exact ⟨fun hi => ⟨clsLab_mem_leaders hS h i, hi⟩, fun hi => hi.2⟩
    have hfin : {ℓ | ℓ ∈ leaders τ S inS ∧ cnt ℓ = n} =
        ↑(((leaders τ S inS).filter fun ℓ => cnt ℓ == n).toFinset) := by
      ext ℓ
      simp
    rw [hset, Set.ncard_preimage_of_injective_subset_range hinj
      (fun ℓ hℓ => mem_range_clsLab hS h hℓ.1), hfin, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup (nodup_leaders.filter _)]
    show _ = ((leaders τ S inS).map cnt).count n
    rw [count_map_eq_length_filter]

end Sound

end ComponentCert

end CFSG.HardMathSupport.Timmesfeld.Steinberg
