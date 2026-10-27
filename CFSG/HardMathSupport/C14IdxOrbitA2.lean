module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction

private theorem iterate_iform {τ : Tag} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (m : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((⇑θ)^[m] x) ((⇑θ)^[m] y) = iform x y := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hθ, ih]

private theorem iterate_mem_simpleRoots {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hΔ : Set.MapsTo θ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)))
    {α : Fin τ.rank → ℤ} (hα : α ∈ simpleRoots (kernelRoots χ)) (m : ℕ) :
    (⇑θ)^[m] α ∈ simpleRoots (kernelRoots χ) :=
  Set.MapsTo.iterate hΔ m hα

private theorem iterate_iform_eq {τ : Tag} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) {α : Fin τ.rank → ℤ} {i j : ℕ}
    (hij : i ≤ j) :
    iform ((⇑θ)^[i] α) ((⇑θ)^[j] α) = iform α ((⇑θ)^[j - i] α) := by
  have e : (⇑θ)^[i] ((⇑θ)^[j - i] α) = (⇑θ)^[j] α := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hij]
  rw [← e, iterate_iform hθ i]

private theorem iterate_iform_period
    {τ : Tag}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) {α : Fin τ.rank → ℤ} {m n : ℕ}
    (hmn : m ≤ n) (hn : (⇑θ)^[n] α = α) :
    iform α ((⇑θ)^[m] α) = iform α ((⇑θ)^[n - m] α) := by
  have e : (⇑θ)^[m] ((⇑θ)^[n - m] α) = α := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hmn, hn]
  calc iform α ((⇑θ)^[m] α)
      = iform ((⇑θ)^[m] α) α := iform_comm _ _
    _ = iform ((⇑θ)^[m] α) ((⇑θ)^[m] ((⇑θ)^[n - m] α)) := by rw [e]
    _ = iform α ((⇑θ)^[n - m] α) := iterate_iform hθ m α _

private theorem oddDerivNotRootB_of_not_isRoot
    {τ : Tag} {v : Fin τ.rank → ℤ} (hv : ¬ IsRoot τ v) :
    oddDerivNotRootB τ v = true := by
  have h : RootOps.isRootB τ v = false := by
    cases hb : RootOps.isRootB τ v with
    | false => rfl
    | true => exact absurd (RootOps.isRootB_iff.1 hb) hv
  simp [oddDerivNotRootB, h]

theorem orthogonal_or_a2Cycle
    {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)} (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hΔ : Set.MapsTo θ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)))
    {α : Fin τ.rank → ℤ} (hα : α ∈ simpleRoots (kernelRoots χ)) {n : ℕ} (hn : 0 < n)
    (hnα : (⇑θ)^[n] α = α) (hmin : ∀ m, 0 < m → m < n → (⇑θ)^[m] α ≠ α) :
    (∀ i < n, ∀ j < n, i ≠ j → iform ((⇑θ)^[i] α) ((⇑θ)^[j] α) = 0) ∨
      ∃ k, n = 2 * k ∧ OddDerivPair τ α ((⇑θ)^[k] α) ∧
        ∀ i, 0 < i → i < k → ∀ γ ∈ ({α, (⇑θ)^[k] α} : Set (Fin τ.rank → ℤ)),
          ∀ δ ∈ ({α, (⇑θ)^[k] α} : Set (Fin τ.rank → ℤ)), iform γ ((⇑θ)^[i] δ) = 0 := by
  classical
  have hαroot : IsRoot τ α := simpleRoots_isRoot hα
  have hαker : α ∈ kernelRoots χ := simpleRoots_subset hα
  have hmem : ∀ m, (⇑θ)^[m] α ∈ simpleRoots (kernelRoots χ) :=
    fun m => iterate_mem_simpleRoots hΔ hα m
  by_cases horth : ∀ m, 0 < m → m < n → iform α ((⇑θ)^[m] α) = 0
  · left
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · rw [iterate_iform_eq hθ (le_of_lt hlt)]
      exact horth (j - i) (by omega) (by omega)
    · rw [iform_comm, iterate_iform_eq hθ (le_of_lt hgt)]
      exact horth (i - j) (by omega) (by omega)
  · right
    push Not at horth
    obtain ⟨m, hm0, hmn, hmne⟩ := horth
    let P : ℕ → Prop := fun t => 0 < t ∧ t < n ∧ iform α ((⇑θ)^[t] α) ≠ 0
    have hP : ∃ t, P t := ⟨m, hm0, hmn, hmne⟩
    let k : ℕ := Nat.find hP
    have hk : P k := Nat.find_spec hP
    have hk0 : 0 < k := hk.1
    have hklt : k < n := hk.2.1
    have hkne : iform α ((⇑θ)^[k] α) ≠ 0 := hk.2.2
    have hzero_below : ∀ t, 0 < t → t < k → iform α ((⇑θ)^[t] α) = 0 := by
      intro t ht0 htk
      by_contra hne
      exact (Nat.find_min hP htk) ⟨ht0, lt_trans htk hklt, hne⟩
    let β : Fin τ.rank → ℤ := (⇑θ)^[k] α
    have hβeq : β = (⇑θ)^[k] α := rfl
    have hβmem : β ∈ simpleRoots (kernelRoots χ) := hmem k
    have hβroot : IsRoot τ β := simpleRoots_isRoot hβmem
    have hβker : β ∈ kernelRoots χ := simpleRoots_subset hβmem
    have hαβ_ne : α ≠ β := by
      intro h
      exact hmin k hk0 hklt (by rw [← hβeq, ← h])
    have hne_neg : α ≠ -β := by
      intro h
      have hh := congrArg height h
      rw [height_neg] at hh
      have hαh := simpleRoots_height_pos hα
      have hβh := simpleRoots_height_pos hβmem
      omega
    have hif_nonpos : iform α β ≤ 0 :=
      iform_nonpos_of_mem_simpleRoots_kernelRoots hα hβmem hαβ_ne
    have hif_neg : iform α β < 0 :=
      lt_of_le_of_ne hif_nonpos (fun h => hkne (by rwa [hβeq] at h))
    let L : ℤ := iform α α
    have hLpos : 0 < L := iform_self_pos hαroot.ne_zero
    let mm : ℤ := corootPair α β
    have hmmul : mm * L = 2 * iform α β := corootPair_mul hαroot β
    have hmm_neg : mm < 0 := by
      by_contra h
      have h0 : 0 ≤ mm := by omega
      have h1 : 0 ≤ mm * L := mul_nonneg h0 hLpos.le
      have h2 : 2 * iform α β < 0 := by linarith
      linarith
    have hββ : iform β β = L := by
      rw [hβeq]
      exact iterate_iform hθ k α α
    have hsumroot : IsRoot τ (α + β) :=
      isRoot_add_of_iform_neg hαroot hβroot hne_neg hif_neg
    have hsum_ne : α + β ≠ 0 := by
      intro h
      have hh : height (α + β) = 0 := by rw [h]; simp [height]
      rw [height_add] at hh
      have hαh := simpleRoots_height_pos hα
      have hβh := simpleRoots_height_pos hβmem
      omega
    have hvv : iform (α + β) (α + β) = (2 + mm) * L := by
      rw [iform_add_left, iform_add_right, iform_add_right, iform_comm β α,
        show iform α α = L from rfl, hββ]
      nlinarith [hmmul]
    have h2mm : 0 < 2 + mm := by
      have h := iform_self_pos hsum_ne
      rw [hvv] at h
      exact pos_of_mul_pos_left h hLpos.le
    have hmmeq : mm = -1 := by omega
    have hif2 : 2 * iform α β = -L := by
      rw [hmmeq] at hmmul
      linarith
    have hnot_sub : ¬ IsRoot τ (α - β) := by
      intro hsub
      have hchi : χ (Multiplicative.ofAdd (α - β)) = 1 := by
        rw [ofAdd_sub, map_div, hαker.2, hβker.2, div_one]
      have hγker : α - β ∈ kernelRoots χ := ⟨hsub, hchi⟩
      have hαs : α ∈ posRoots (kernelRoots χ) := simpleRoot_mem_posRoots hα
      have hβs : β ∈ posRoots (kernelRoots χ) := simpleRoot_mem_posRoots hβmem
      have hnotα := (mem_simpleRoots.1 hα).2.2
      have hnotβ := (mem_simpleRoots.1 hβmem).2.2
      rcases IsRoot.height_pos_or_neg hsub with hpos | hneg
      · have hγpos : α - β ∈ posRoots (kernelRoots χ) := ⟨hγker, hpos⟩
        exact hnotα (α - β) hγpos β hβs (by abel)
      · have hγ'ker : -(α - β) ∈ kernelRoots χ := by
          refine ⟨IsRoot.neg hsub, ?_⟩
          rw [ofAdd_neg, map_inv, hchi, inv_one]
        have hγ'pos : -(α - β) ∈ posRoots (kernelRoots χ) := by
          refine ⟨hγ'ker, ?_⟩
          rw [height_neg]
          omega
        exact hnotβ (-(α - β)) hγ'pos α hαs (by abel)
    have hnot_2a : ¬ IsRoot τ (2 • α + β) := by
      intro h2
      have hcp : corootPair α (2 • α + β) = 3 := by
        apply mul_right_cancel₀ hLpos.ne'
        rw [corootPair_mul hαroot (2 • α + β)]
        have e : iform α (2 • α + β) = 2 * L + iform α β := by
          rw [two_nsmul, iform_add_right, iform_add_right]
          ring
        rw [e]
        linarith
      have hr : rootReflection α • (2 • α + β) = -(α - β) := by
        rw [rootReflection_smul hαroot, hcp, two_nsmul, zsmul_eq_mul]
        ring
      exact hnot_sub (isRoot_neg_iff.1 (hr ▸ IsRoot.smul h2 (rootReflection α)))
    have hnot_a2b : ¬ IsRoot τ (α + 2 • β) := by
      intro h2
      have hcp : corootPair β (α + 2 • β) = 3 := by
        apply mul_right_cancel₀ (iform_self_pos_of_isRoot hβroot).ne'
        rw [corootPair_mul hβroot (α + 2 • β), hββ]
        have e : iform β (α + 2 • β) = iform α β + 2 * L := by
          rw [two_nsmul, iform_add_right, iform_add_right, iform_comm β α, hββ]
          ring
        rw [e]
        linarith
      have hr : rootReflection β • (α + 2 • β) = α - β := by
        rw [rootReflection_smul hβroot, hcp, two_nsmul, zsmul_eq_mul]
        ring
      exact hnot_sub (hr ▸ IsRoot.smul h2 (rootReflection β))
    have hstring : oddDerivStringB τ α β = true := by
      rw [oddDerivStringB]
      simp only [oddDerivNotRootB_of_not_isRoot hnot_sub,
        oddDerivNotRootB_of_not_isRoot hnot_2a,
        oddDerivNotRootB_of_not_isRoot hnot_a2b, Bool.and_self]
    have hpair : OddDerivPair τ α β :=
      oddDerivPair_of_oddDerivStringB hαroot hβroot hαβ_ne hne_neg hsumroot hstring
    have h2k : (⇑θ)^[2 * k] α = α := by
      by_contra hnot2k
      let g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) := (⇑θ)^[k]
      have hg_eq : g = (⇑θ)^[k] := rfl
      have hgper : Function.IsPeriodicPt g n α := by
        show g^[n] α = α
        rw [hg_eq, ← Function.iterate_mul, Nat.mul_comm]
        exact (show Function.IsPeriodicPt (⇑θ) n α from hnα).mul_const k
      let s : ℕ := Function.minimalPeriod g α
      have hs0 : 0 < s := hgper.minimalPeriod_pos hn
      have hsfix : g^[s] α = α := Function.isPeriodicPt_minimalPeriod g α
      have hsmin : ∀ t, 0 < t → t < s → g^[t] α ≠ α := by
        intro t ht0 hts
        exact Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (Nat.ne_of_gt ht0) hts
      have hsk : (⇑θ)^[s * k] α = α := by
        have h := hsfix
        rw [hg_eq, ← Function.iterate_mul, Nat.mul_comm] at h
        exact h
      have hs1 : s ≠ 1 := by
        intro h1
        have h := hsfix
        rw [h1] at h
        exact hmin k hk0 hklt (by simpa [hg_eq, Function.iterate_one] using h)
      have hs2 : s ≠ 2 := by
        intro h2
        apply hnot2k
        have h := hsfix
        rw [h2] at h
        rw [hg_eq, ← Function.iterate_mul, Nat.mul_comm] at h
        exact h
      have hs3 : 3 ≤ s := by omega
      have hginj : Function.Injective g := by
        rw [hg_eq]
        exact Function.Injective.iterate θ.injective k
      let γ : ℕ → Fin τ.rank → ℤ := fun j => g^[j] α
      let O : Finset (Fin τ.rank → ℤ) := (Finset.range s).image γ
      have hγθ : ∀ j, γ j = (⇑θ)^[j * k] α := by
        intro j
        show g^[j] α = (⇑θ)^[j * k] α
        rw [hg_eq, ← Function.iterate_mul, Nat.mul_comm]
      have hO_mem : ∀ x ∈ O, x ∈ simpleRoots (kernelRoots χ) := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
        rw [hγθ j]
        exact hmem (j * k)
      have hγinj : Set.InjOn γ (Set.Iio s) := by
        intro j hj l hl hjl
        exact Function.iterate_injOn_Iio_minimalPeriod hj hl hjl
      have hOcard : O.card = s := by
        have hinj : Set.InjOn γ ↑(Finset.range s) := by
          intro j hj l hl h
          exact hγinj (by simpa using hj) (by simpa using hl) h
        rw [show O = (Finset.range s).image γ from rfl, Finset.card_image_of_injOn hinj]
        simp
      have hgγ : ∀ t j, j < s → g^[t] (γ j) = γ ((j + t) % s) := by
        intro t j hj
        have e1 : g^[t] (γ j) = g^[t + j] α := by
          rw [show γ j = g^[j] α from rfl, ← Function.iterate_add_apply]
        have hmod : g^[(j + t) % s] α = g^[(j + t)] α :=
          (Function.isPeriodicPt_minimalPeriod g α).iterate_mod_apply (j + t)
        rw [e1]
        rw [show γ ((j + t) % s) = g^[(j + t) % s] α from rfl, hmod]
        congr 1
        omega
      have hgO : ∀ t j, j < s → g^[t] (γ j) ∈ O := by
        intro t j hj
        rw [hgγ t j hj]
        exact Finset.mem_image.2
          ⟨(j + t) % s, Finset.mem_range.2 (Nat.mod_lt _ hs0), rfl⟩
      let v : Fin τ.rank → ℤ := ∑ x ∈ O, x
      have hbound : ∀ x ∈ O, iform x v ≤ 0 := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
        have hj' : j < s := Finset.mem_range.1 hj
        let b : Fin τ.rank → ℤ := g (γ j)
        let c : Fin τ.rank → ℤ := g^[s - 1] (γ j)
        have hbO : b ∈ O := by
          simpa [b, Function.iterate_one] using hgO 1 j hj'
        have hcO : c ∈ O := hgO (s - 1) j hj'
        have hbne : b ≠ γ j := by
          intro h
          have h' : g (g^[j] α) = g^[j] α := h
          have h1 : g α = α := by
            have h2 : g^[j] (g α) = g^[j] α := by
              rw [← Function.iterate_succ_apply g j α]
              rwa [← Function.iterate_succ_apply' g j α] at h'
            exact (hginj.iterate j) h2
          exact hsmin 1 (by omega) (by omega)
            (by simpa [Function.iterate_one] using h1)
        have hcne : c ≠ γ j := by
          intro h
          have h' : g^[s - 1] (g^[j] α) = g^[j] α := h
          have e : g^[s - 1] (g^[j] α) = g^[j] (g^[s - 1] α) := by
            rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
            congr 1
            omega
          have h2 : g^[j] (g^[s - 1] α) = g^[j] α := by rwa [e] at h'
          exact hsmin (s - 1) (by omega) (by omega) ((hginj.iterate j) h2)
        have hbc : b ≠ c := by
          intro h
          have e1 : b = g^[j] (g α) := by
            show g (g^[j] α) = g^[j] (g α)
            rw [← Function.iterate_succ_apply' g j α, ← Function.iterate_succ_apply g j α]
          have e2 : c = g^[j] (g^[s - 1] α) := by
            show g^[s - 1] (g^[j] α) = g^[j] (g^[s - 1] α)
            rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
            congr 1
            omega
          have h2 : g^[j] (g α) = g^[j] (g^[s - 1] α) := by
            rw [← e1, ← e2]
            exact h
          have h3 : g α = g^[s - 1] α := (hginj.iterate j) h2
          have e3 : g^[s - 1] α = g (g^[s - 2] α) := by
            rw [← Function.iterate_succ_apply' g (s - 2) α]
            congr 1
            omega
          rw [e3] at h3
          exact hsmin (s - 2) (by omega) (by omega) (hginj h3).symm
        let S : Finset (Fin τ.rank → ℤ) := {γ j, b, c}
        have hSsub : S ⊆ O := by
          intro y hy
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact Finset.mem_image.2 ⟨j, hj, rfl⟩
          · exact hbO
          · exact hcO
        have hnonpos : ∀ y ∈ O, y ∉ S → iform (γ j) y ≤ 0 := by
          intro y hyO hyS
          refine iform_nonpos_of_mem_simpleRoots_kernelRoots
            (hO_mem (γ j) (Finset.mem_image.2 ⟨j, hj, rfl⟩)) (hO_mem y hyO) ?_
          intro hxy
          exact hyS (by rw [← hxy]; simp [S])
        have hsum_le : ∑ y ∈ O, iform (γ j) y ≤ ∑ y ∈ S, iform (γ j) y :=
          Finset.sum_le_sum_of_subset_of_nonpos hSsub hnonpos
        have hxb : γ j ≠ b := fun h => hbne h.symm
        have hxc : γ j ≠ c := fun h => hcne h.symm
        have hSsum : ∑ y ∈ S, iform (γ j) y =
            iform (γ j) (γ j) + iform (γ j) b + iform (γ j) c := by
          simp only [S]
          rw [Finset.sum_insert (by simp [hxb, hxc]),
            Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]
          ring
        have hdiag : iform (γ j) (γ j) = L := by
          rw [hγθ j]
          exact iterate_iform hθ (j * k) α α
        have hbval : iform (γ j) b = iform α β := by
          have hbθ : b = (⇑θ)^[j * k] β := by
            show g (γ j) = (⇑θ)^[j * k] ((⇑θ)^[k] α)
            rw [hg_eq, hγθ j, ← Function.iterate_add_apply,
              ← Function.iterate_add_apply]
            congr 1
            omega
          rw [hγθ j, hbθ, iterate_iform hθ (j * k) α β]
        have hcval : iform (γ j) c = iform α β := by
          have hcθ : c = (⇑θ)^[j * k] ((⇑θ)^[(s - 1) * k] α) := by
            have e1 : c = ((⇑θ)^[k])^[s - 1] ((⇑θ)^[j * k] α) := by
              show g^[s - 1] (γ j) = _
              rw [hg_eq, hγθ j]
            have e2 : ((⇑θ)^[k])^[s - 1] ((⇑θ)^[j * k] α) =
                (⇑θ)^[k * (s - 1)] ((⇑θ)^[j * k] α) := by
              rw [← Function.iterate_mul]
            have e3 : (⇑θ)^[k * (s - 1)] ((⇑θ)^[j * k] α) =
                (⇑θ)^[j * k] ((⇑θ)^[(s - 1) * k] α) := by
              rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
              congr 1
              ring
            rw [e1, e2, e3]
          have hlast : iform α ((⇑θ)^[(s - 1) * k] α) = iform α β := by
            have hfix : (⇑θ)^[k] ((⇑θ)^[(s - 1) * k] α) = α := by
              rw [← Function.iterate_add_apply]
              have harith : k + (s - 1) * k = s * k := by
                conv_rhs => rw [show s = (s - 1) + 1 from by omega]
                rw [Nat.add_mul, one_mul]
                exact Nat.add_comm k ((s - 1) * k)
              rw [harith]
              exact hsk
            calc iform α ((⇑θ)^[(s - 1) * k] α)
                = iform ((⇑θ)^[k] α) ((⇑θ)^[k] ((⇑θ)^[(s - 1) * k] α)) :=
                    (iterate_iform hθ k α _).symm
              _ = iform β α := by rw [hfix, hβeq]
              _ = iform α β := iform_comm _ _
          rw [hγθ j, hcθ, iterate_iform hθ (j * k) α ((⇑θ)^[(s - 1) * k] α),
            hlast]
        have hbc_sum : iform (γ j) b + iform (γ j) c = -L := by
          rw [hbval, hcval]
          linarith [hif2]
        have hSsum0 : ∑ y ∈ S, iform (γ j) y = 0 := by
          rw [hSsum, hdiag]
          linarith [hbc_sum]
        have hsum_eq : iform (γ j) v = ∑ y ∈ O, iform (γ j) y :=
          iform_finset_sum_right O (γ j) id
        rw [hSsum0, ← hsum_eq] at hsum_le
        exact hsum_le
      have hvv_nonpos : iform v v ≤ 0 := by
        have hvv : iform v v = ∑ x ∈ O, iform x v := iform_finset_sum_left O id v
        rw [hvv]
        exact Finset.sum_nonpos hbound
      have hvne : v ≠ 0 := by
        intro hv0
        have hpos : 0 < height v := by
          show 0 < height (∑ x ∈ O, x)
          rw [height_finset_sum]
          refine Finset.sum_pos (fun x hx => simpleRoots_height_pos (hO_mem x hx)) ?_
          exact ⟨γ 0, Finset.mem_image.2 ⟨0, Finset.mem_range.2 hs0, rfl⟩⟩
        rw [hv0] at hpos
        simp [height] at hpos
      exact absurd hvv_nonpos (not_le.2 (iform_self_pos hvne))
    have hminper : Function.minimalPeriod (⇑θ) α = n := by
      apply le_antisymm
      · exact (show Function.IsPeriodicPt (⇑θ) n α from hnα).minimalPeriod_le hn
      · by_contra h
        have hlt : Function.minimalPeriod (⇑θ) α < n := by omega
        have hpos := (show Function.IsPeriodicPt (⇑θ) n α from hnα).minimalPeriod_pos hn
        exact hmin _ hpos hlt (Function.isPeriodicPt_minimalPeriod (⇑θ) α)
    have hdvd : n ∣ 2 * k := by
      have hper := (show Function.IsPeriodicPt (⇑θ) (2 * k) α from h2k).minimalPeriod_dvd
      rwa [hminper] at hper
    have hn2k : n = 2 * k := by
      obtain ⟨t, ht⟩ := hdvd
      have htpos : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · rw [h, mul_zero] at ht
          omega
        · exact h
      have ht1 : t = 1 := by
        by_contra h
        have ht2 : 2 ≤ t := by omega
        have h2n : 2 * n ≤ n * t := by
          rw [mul_comm 2 n]
          exact Nat.mul_le_mul_left n ht2
        rw [← ht] at h2n
        omega
      rw [ht, ht1, mul_one]
    refine ⟨k, hn2k, hpair, ?_⟩
    intro i hi0 hik γ hγ δ hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ hδ
    rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
    · exact hzero_below i hi0 hik
    · rw [← Function.iterate_add_apply]
      rw [iterate_iform_period hθ (by omega : i + k ≤ 2 * k) h2k]
      rw [show 2 * k - (i + k) = k - i by omega]
      exact hzero_below (k - i) (by omega) (by omega)
    · rw [iform_comm, iterate_iform_eq hθ (le_of_lt hik)]
      exact hzero_below (k - i) (by omega) (by omega)
    · have e : (⇑θ)^[i] ((⇑θ)^[k] α) = (⇑θ)^[k] ((⇑θ)^[i] α) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        congr 1
        omega
      rw [e, iterate_iform hθ k _ _]
      exact hzero_below i hi0 hik

end CFSG.HardMathSupport.C14Idx
