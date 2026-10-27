module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeylFive

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {M : Type*} [CommGroup M]

omit [CommGroup M] in
theorem chainRefl_succ {n : ℕ} (β : Fin (n + 1) → Fin τ.rank → ℤ) :
    chainRefl β = rootReflection (β 0) * chainRefl (fun i : Fin n => β i.succ) := by
  simp only [chainRefl, List.ofFn_succ, List.prod_cons]

omit [CommGroup M] in
theorem chainRefl_zero (β : Fin 0 → Fin τ.rank → ℤ) : chainRefl β = 1 := by
  simp [chainRefl]

omit [CommGroup M] in
theorem IsAChain.tail {n : ℕ} {β : Fin (n + 1) → Fin τ.rank → ℤ} (h : IsAChain β) :
    IsAChain (fun i : Fin n => β i.succ) where
  isRoot i := h.isRoot i.succ
  adj i j hij := h.adj i.succ j.succ (by simp [hij])
  orth i j hij := h.orth i.succ j.succ (by simp; omega)


omit [CommGroup M] in
theorem chainRefl_smul_of_perp {n : ℕ} {β : Fin n → Fin τ.rank → ℤ}
    (hβ : ∀ k, IsRoot τ (β k)) {x : Fin τ.rank → ℤ} (hx : ∀ k, iform (β k) x = 0) :
    chainRefl β • x = x := by
  induction n with
  | zero => rw [chainRefl_zero, one_smul]
  | succ n ih =>
    rw [chainRefl_succ, mul_smul, ih (fun k => hβ k.succ) (fun k => hx k.succ),
      rootReflection_smul_of_iform_eq_zero (hβ 0) (hx 0)]

theorem chainRefl_mem_kernelWeylGroup {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {n : ℕ}
    {β : Fin n → Fin τ.rank → ℤ} (hβ : ∀ k, β k ∈ kernelRoots χ) :
    chainRefl β ∈ kernelWeylGroup χ := by
  refine Subgroup.list_prod_mem _ fun r hr => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hr
  exact rootReflection_mem_kernelWeylGroup (hβ k)

omit [CommGroup M] in
theorem IsAChain.chainRefl_smul (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) :
    ∀ {n : ℕ} {β : Fin (n + 1) → Fin τ.rank → ℤ}, IsAChain β →
      (∀ i : Fin n, chainRefl β • β i.castSucc = β i.succ) ∧
        chainRefl β • β (Fin.last n) = -∑ k, β k := by
  intro n
  induction n with
  | zero =>
    intro β h
    refine ⟨fun i => i.elim0, ?_⟩
    have e : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [e, chainRefl_succ, chainRefl_zero, mul_one, rootReflection_smul_SL hSL (h.isRoot 0),
      Fin.sum_univ_one, hSL _ (h.isRoot 0)]
    module
  | succ n ih =>
    intro β h
    obtain ⟨ih1, ih2⟩ := ih h.tail
    have hc : chainRefl β = rootReflection (β 0) *
        chainRefl (fun i : Fin (n + 1) => β i.succ) := chainRefl_succ β
    have r0 := rootReflection_smul_SL hSL (h.isRoot 0)
    have g00 : iform (β 0) (β 0) = 2 := hSL _ (h.isRoot 0)
    have g01 : iform (β 0) (β (Fin.succ 0)) = -1 := h.adj 0 (Fin.succ 0) (by simp)
    have g0k : ∀ k : Fin n, iform (β 0) (β k.succ.succ) = 0 := fun k =>
      h.orth 0 k.succ.succ (by simp)
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      ·
        have hc' : chainRefl (fun i : Fin (n + 1) => β i.succ) =
            rootReflection (β (Fin.succ 0)) * chainRefl (fun i : Fin n => β i.succ.succ) :=
          chainRefl_succ _
        have hperp : chainRefl (fun i : Fin n => β i.succ.succ) • β 0 = β 0 :=
          chainRefl_smul_of_perp (fun k => h.isRoot _) fun k => by rw [iform_comm]; exact g0k k
        have r1 := rootReflection_smul_SL hSL (h.isRoot (Fin.succ 0))
        rw [Fin.castSucc_zero, hc, mul_smul, hc', mul_smul, hperp, r1, iform_comm, g01, r0,
          iform_sub_right, iform_smul_right, g00, g01]
        module
      ·
        have e1 : β j.succ.castSucc = β j.castSucc.succ := by rw [Fin.succ_castSucc]
        rw [e1, hc, mul_smul, ih1 j, rootReflection_smul_of_iform_eq_zero (h.isRoot 0) (g0k j)]
    · have e1 : β (Fin.last (n + 1)) = β (Fin.last n).succ := by rw [Fin.succ_last]
      have hsum : iform (β 0) (∑ k : Fin (n + 1), β k.succ) = -1 := by
        rw [iform_finset_sum_right, Fin.sum_univ_succ, g01,
          Finset.sum_eq_zero fun k _ => g0k k, add_zero]
      rw [e1, hc, mul_smul, ih2, r0, iform_neg_snd, hsum, Fin.sum_univ_succ (f := β)]
      simp only [neg_neg, one_smul]
      abel

@[expose] def OrbitZero (p : ℕ) (w : WeylGroup τ) : Prop :=
  ∀ γ : Fin τ.rank → ℤ, (∀ v, w • v = v → iform γ v = 0) → ∑ k ∈ Finset.range p, w ^ k • γ = 0

omit [CommGroup M] in
theorem pow_smul_eq_of_smul_eq {w : WeylGroup τ} {v : Fin τ.rank → ℤ} (hv : w • v = v) :
    ∀ k : ℕ, w ^ k • v = v
  | 0 => by rw [pow_zero, one_smul]
  | k + 1 => by rw [pow_succ, mul_smul, hv, pow_smul_eq_of_smul_eq hv k]

omit [CommGroup M] in
theorem sum_range_pow_succ_smul {p : ℕ} {w : WeylGroup τ} {γ : Fin τ.rank → ℤ}
    (h : w ^ p • γ = γ) : ∑ k ∈ Finset.range p, w ^ (k + 1) • γ =
      ∑ k ∈ Finset.range p, w ^ k • γ := by
  have h1 := Finset.sum_range_succ' (fun k => w ^ k • γ) p
  have h2 := Finset.sum_range_succ (fun k => w ^ k • γ) p
  simp only [pow_zero, one_smul] at h1
  rw [h1, h] at h2
  exact add_right_cancel h2

omit [CommGroup M] in
theorem orbitZero_of_pow {p : ℕ} {w : WeylGroup τ} (hp : w ^ p = 1) : OrbitZero p w := by
  intro γ hγ
  set s := ∑ k ∈ Finset.range p, w ^ k • γ with hs
  have hws : w • s = s := by
    rw [hs, Finset.smul_sum]
    simp_rw [← mul_smul, ← pow_succ']
    exact sum_range_pow_succ_smul (by rw [hp, one_smul])
  have hss : iform s s = 0 := by
    conv_lhs => rw [hs]
    rw [iform_finset_sum_left]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : iform (w ^ k • γ) s = iform γ s := by
      conv_lhs => rw [← pow_smul_eq_of_smul_eq hws k]
      exact iform_smul _ _ _
    rw [this]
    exact hγ s hws
  by_contra hne
  exact absurd hss (iform_self_pos hne).ne'

omit [CommGroup M] in
theorem perp_pow_smul {w : WeylGroup τ} {x : Fin τ.rank → ℤ}
    (hx : ∀ v, w • v = v → iform x v = 0) :
    ∀ k : ℕ, ∀ v, w • v = v → iform (w ^ k • x) v = 0
  | 0 => by simpa using hx
  | k + 1 => by
    rw [pow_succ', mul_smul]
    exact perp_smul (perp_pow_smul hx k)

omit [CommGroup M] in
theorem OrbitZero.pow_smul_self {p : ℕ} {w : WeylGroup τ} (hP : OrbitZero p w)
    {x : Fin τ.rank → ℤ} (hx : ∀ v, w • v = v → iform x v = 0) : w ^ p • x = x := by
  have h0 := hP x hx
  have h1 := hP (w • x) (perp_smul hx)
  simp_rw [← mul_smul, ← pow_succ] at h1
  have h2 := Finset.sum_range_succ' (fun k => w ^ k • x) p
  have h3 := Finset.sum_range_succ (fun k => w ^ k • x) p
  simp only [pow_zero, one_smul] at h2
  rw [h0, zero_add] at h3
  rw [h1, zero_add] at h2
  exact h3.symm.trans h2

theorem exists_chainBlocks_aux (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {n : ℕ}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hgood : ∀ w ∈ kernelWeylGroup χ, OrbitZero (n + 2) w → w ≠ 1 →
      ∃ γ ∈ kernelRoots χ, (∀ v, w • v = v → iform γ v = 0) ∧
        IsAChain (fun i : Fin (n + 1) => w ^ (i : ℕ) • γ)) :
    ∀ (N : ℕ) (w : WeylGroup τ), w ∈ kernelWeylGroup χ → OrbitZero (n + 2) w →
      {γ | IsRoot τ γ ∧ w • γ ≠ γ}.ncard = N →
      ∃ B : List (Fin (n + 1) → Fin τ.rank → ℤ),
        (∀ β ∈ B, IsAChain β ∧ ∀ x ∈ aChainRoots β, x ∈ kernelRoots χ ∧
          ∀ v, w • v = v → iform x v = 0) ∧
        B.Pairwise ChainsStrOrth ∧ w = (B.map chainRefl).prod := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro w hw hP hN
  by_cases hw1 : w = 1
  · subst hw1
    exact ⟨[], by simp, List.Pairwise.nil, by simp⟩
  obtain ⟨γ, hγS, hγp, hch⟩ := hgood w hw hP hw1
  have hwχ : w ∈ charStabilizer χ := kernelWeylGroup_le hw
  set β : Fin (n + 1) → Fin τ.rank → ℤ := fun i => w ^ (i : ℕ) • γ with hβ
  have hβS : ∀ k, β k ∈ kernelRoots χ := fun k =>
    smul_mem_kernelRoots (pow_mem hwχ _) hγS
  have hβp : ∀ k, ∀ v, w • v = v → iform (β k) v = 0 := fun k => perp_pow_smul hγp k
  have hlast : w ^ (n + 1) • γ = -∑ k, β k := by
    have h0 := hP γ hγp
    rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h0
    exact eq_neg_of_add_eq_zero_right h0
  obtain ⟨c1, c2⟩ := hch.chainRefl_smul hSL
  set c := chainRefl β with hc
  have hcw : ∀ i, c • β i = w • β i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have : w • β (Fin.last n) = w ^ (n + 1) • γ := by
        rw [hβ]
        simp only [Fin.val_last]
        rw [← mul_smul, ← pow_succ']
      rw [this, hlast]
      exact c2
    · have : w • β j.castSucc = β j.succ := by
        rw [hβ]
        simp only [Fin.val_castSucc, Fin.val_succ]
        rw [← mul_smul, ← pow_succ']
      rw [this]
      exact c1 j
  have hcS : c ∈ kernelWeylGroup χ := chainRefl_mem_kernelWeylGroup hβS
  have hcfix : ∀ x, (∀ k, iform (β k) x = 0) → c • x = x := fun x hx =>
    chainRefl_smul_of_perp hch.isRoot hx
  have hcinvfix : ∀ x, (∀ k, iform (β k) x = 0) → c⁻¹ • x = x := fun x hx => by
    conv_lhs => rw [← hcfix x hx]
    rw [inv_smul_smul]
  set w' := c⁻¹ * w with hw'def
  have hw'S : w' ∈ kernelWeylGroup χ := mul_mem (inv_mem hcS) hw
  have hw' : ∀ x : Fin τ.rank → ℤ, w' • x = c⁻¹ • w • x := fun x => mul_smul _ _ _
  have hfixβ : ∀ k, w' • β k = β k := fun k => by rw [hw', ← hcw, inv_smul_smul]
  have hfix : ∀ v, w • v = v → w' • v = v := fun v hv => by
    rw [hw', hv, hcinvfix v fun k => hβp k v hv]
  have hperp : ∀ x, (∀ k, iform (β k) x = 0) → ∀ k, iform (β k) (w • x) = 0 := by
    intro x hx k
    refine Fin.cases ?_ (fun j => ?_) k
    · have e : β 0 = w • w ^ (n + 1) • γ := by
        rw [← mul_smul, ← pow_succ', hP.pow_smul_self hγp]
        simp [hβ]
      rw [e, iform_smul, hlast, iform_neg_fst, iform_finset_sum_left,
        Finset.sum_eq_zero fun k _ => hx k, neg_zero]
    · have e : β j.succ = w • β j.castSucc := by
        rw [hβ]
        simp only [Fin.val_castSucc, Fin.val_succ]
        rw [← mul_smul, ← pow_succ']
      rw [e, iform_smul]
      exact hx _
  have hw'eq : ∀ x, (∀ k, iform (β k) x = 0) → w' • x = w • x := fun x hx => by
    rw [hw', hcinvfix _ (hperp x hx)]
  have hP' : OrbitZero (n + 2) w' := by
    intro δ hδ
    have hδβ : ∀ k, iform (β k) δ = 0 := fun k => by
      rw [iform_comm]
      exact hδ _ (hfixβ k)
    have hδw : ∀ v, w • v = v → iform δ v = 0 := fun v hv => hδ v (hfix v hv)
    have key : ∀ m : ℕ, w' ^ m • δ = w ^ m • δ ∧ ∀ k, iform (β k) (w ^ m • δ) = 0 := by
      intro m
      induction m with
      | zero => exact ⟨by simp, by simpa using hδβ⟩
      | succ m ihm =>
        refine ⟨?_, ?_⟩
        · rw [pow_succ', pow_succ', mul_smul w', mul_smul w, ihm.1, hw'eq _ ihm.2]
        · rw [pow_succ', mul_smul]
          exact hperp _ ihm.2
    rw [Finset.sum_congr rfl fun m _ => (key m).1]
    exact hP δ hδw
  have hsub : {δ | IsRoot τ δ ∧ w' • δ ≠ δ} ⊂ {δ | IsRoot τ δ ∧ w • δ ≠ δ} := by
    refine ⟨fun δ ⟨hδ, hne⟩ => ⟨hδ, fun h => hne (hfix δ h)⟩, fun h => ?_⟩
    have hmov : w • γ ≠ γ := fun e => by
      have := hγp γ e
      rw [hSL γ hγS.1] at this
      omega
    have hγ0 : β 0 = γ := by simp [hβ]
    exact (h ⟨hγS.1, hmov⟩).2 (by rw [← hγ0]; exact hfixβ 0)
  have hlt : {δ | IsRoot τ δ ∧ w' • δ ≠ δ}.ncard < N := by
    rw [← hN]
    exact Set.ncard_lt_ncard hsub ((finite_setOf_isRoot τ).subset fun δ h => h.1)
  obtain ⟨B', hB', hpair', hprod'⟩ := ih _ hlt w' hw'S hP' rfl
  refine ⟨β :: B', fun δ hδ => ?_, List.Pairwise.cons (fun δ hδ => ?_) hpair', ?_⟩
  · rcases List.mem_cons.1 hδ with rfl | hδ
    · exact ⟨hch, fun x hx => ⟨aChainRoots_subset_kernelRoots hSL hch hβS hx,
        fun v hv => iform_eq_zero_of_mem_aChainRoots hx fun k => hβp k v hv⟩⟩
    · obtain ⟨h1, h2⟩ := hB' δ hδ
      exact ⟨h1, fun x hx => ⟨(h2 x hx).1, fun v hv => (h2 x hx).2 v (hfix v hv)⟩⟩
  · obtain ⟨hδch, hδ2⟩ := hB' δ hδ
    intro x hx y hy
    have hxr := mem_aChainRoots_isRoot hSL hch x hx
    have hyr := mem_aChainRoots_isRoot hSL hδch y hy
    have hx' : w' • x = x := smul_eq_of_mem_aChainRoots hx hfixβ
    refine strOrth_of_iform_eq_zero_SL hSL hxr hyr ?_
    rw [iform_comm]
    exact (hδ2 y hy).2 x hx'
  · rw [List.map_cons, List.prod_cons, ← hprod', hw'def, ← hc, mul_inv_cancel_left]

theorem exists_chainBlocks (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {n : ℕ}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hgood : ∀ w ∈ kernelWeylGroup χ, OrbitZero (n + 2) w → w ≠ 1 →
      ∃ γ ∈ kernelRoots χ, (∀ v, w • v = v → iform γ v = 0) ∧
        IsAChain (fun i : Fin (n + 1) => w ^ (i : ℕ) • γ))
    {w : WeylGroup τ} (hw : w ∈ kernelWeylGroup χ) (hP : OrbitZero (n + 2) w) :
    ∃ B : List (Fin (n + 1) → Fin τ.rank → ℤ),
      (∀ β ∈ B, IsAChain β ∧ aChainRoots β ⊆ kernelRoots χ) ∧
      B.Pairwise ChainsStrOrth ∧ w = (B.map chainRefl).prod := by
  obtain ⟨B, hB, hpair, hprod⟩ := exists_chainBlocks_aux hSL hgood _ w hw hP rfl
  exact ⟨B, fun β hβ => ⟨(hB β hβ).1, fun x hx => ((hB β hβ).2 x hx).1⟩, hpair, hprod⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
