module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree


open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint

section Signed

theorem exists_reflProd_neg (S : Set (Fin TwistTag.E6.tag.rank → ℤ)) (n : ℕ)
    (β : ℕ → Fin TwistTag.E6.tag.rank → ℤ) (hroot : ∀ k, IsRoot TwistTag.E6.tag (β k))
    (hS : ∀ k, β k ∈ S)
    (horth : ∀ k l, k < n → l < n → k ≠ l → iform (β k) (β l) = 0) :
    ∃ z ∈ Subgroup.closure (rootReflection '' S), ∀ k, k < n → z • β k = -β k := by
  obtain ⟨zs, hz0, hzs⟩ : ∃ zs : ℕ → WeylGroup TwistTag.E6.tag, zs 0 = 1 ∧
      ∀ m, zs (m + 1) = zs m * rootReflection (β m) :=
    ⟨fun m => Nat.rec (motive := fun _ => WeylGroup TwistTag.E6.tag) 1
      (fun j acc => acc * rootReflection (β j)) m, rfl, fun m => rfl⟩
  have hmem : ∀ m, m ≤ n → zs m ∈ Subgroup.closure (rootReflection '' S) := by
    intro m
    induction m with
    | zero => intro _; rw [hz0]; exact one_mem _
    | succ m ih =>
      intro hm
      rw [hzs m]
      exact mul_mem (ih (by omega)) (Subgroup.subset_closure ⟨β m, hS m, rfl⟩)
  have hneg : ∀ m, m ≤ n → ∀ k, k < n →
      zs m • β k = if k < m then -β k else β k := by
    intro m
    induction m with
    | zero => intro _ k _; rw [hz0]; simp
    | succ m ih =>
      intro hm k hk
      rw [hzs m, mul_smul]
      by_cases hkm : k = m
      · subst hkm
        rw [rootReflection_smul_self (hroot k), smul_neg, ih (by omega) k hk]
        simp
      · have hiform : iform (β m) (β k) = 0 := (horth m k (by omega) hk (Ne.symm hkm))
        rw [rootReflection_smul_of_iform_eq_zero (hroot m) hiform, ih (by omega) k hk]
        have : (k < m + 1) ↔ (k < m) := by omega
        simp only [this]
  refine ⟨zs n, hmem n le_rfl, fun k hk => ?_⟩
  rw [hneg n le_rfl k hk, if_pos hk]

theorem kill_cycle_signed {L : Type} [Field L] {ι : Type} (a : ι → Fin TwistTag.E6.tag.rank → Lˣ)
    (w : WeylGroup TwistTag.E6.tag)
    (hw : (fun α => w • permLattice TwistTag.E6.perm α) '' familyKernel a = familyKernel a)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ familyKernel a) :
    ∃ x ∈ Subgroup.closure (rootReflection '' familyKernel a), ∃ (n : ℕ) (β : ℕ → Fin TwistTag.E6.tag.rank → ℤ),
      0 < n ∧ (∀ k, β (k + n) = β k) ∧ β 0 = α ∧ (∀ k, β k ∈ familyKernel a) ∧
      (∀ k l, k < n → l < n → k ≠ l →
        iform (β k) (β l) = 0 ∧ β k ≠ β l ∧ ¬ IsRoot TwistTag.E6.tag (β k + β l)) ∧
      ∀ k, (x * w) • permLattice TwistTag.E6.perm (β k) = β (k + 1) := by
  set r : WeylGroup TwistTag.E6.tag := CFSG.RankThree.Chevalley.e6HRReflProd with hr_def
  have hr : ∀ x, r • x = -permLattice TwistTag.E6.perm x := fun x =>
    CFSG.RankThree.Chevalley.e6HRReflProd_smul x
  have hu : (fun β => (w * r) • β) '' familyKernel a = familyKernel a := by
    have e : (fun β => (w * r) • β) =
        (fun β => -β) ∘ (fun β => w • permLattice TwistTag.E6.perm β) := by
      funext β
      simp only [Function.comp, mul_smul, hr, smul_neg]
    rw [e, Set.image_comp, hw]
    ext β
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact neg_mem_familyKernel a hγ
    · intro hβ
      exact ⟨-β, neg_mem_familyKernel a hβ, neg_neg β⟩
  obtain ⟨xu, hxu, n, hn, β', hβ'0, hβ'S, horth', hcyc⟩ :=
    exists_kill_root_cycle (τ := TwistTag.E6.tag) (Or.inr (Or.inl rfl)) (familyChar a) (w * r)
      (by rw [kernelRoots_familyChar]; exact hu) (by rw [kernelRoots_familyChar]; exact hα)
  rw [kernelRoots_familyChar] at hxu hβ'S
  set β : ℕ → Fin TwistTag.E6.tag.rank → ℤ := fun k => β' ⟨k % n, Nat.mod_lt _ hn⟩ with hβ_def
  have hβper : ∀ j, β j = β' ⟨j % n, Nat.mod_lt _ hn⟩ := fun j => rfl
  have hβmod : ∀ j, β (j % n) = β j := by
    intro j
    rw [hβper, hβper]
    congr 1
    exact Fin.ext (Nat.mod_mod j n)
  have hβS : ∀ k, β k ∈ familyKernel a := fun k => hβ'S ⟨k % n, Nat.mod_lt _ hn⟩
  have hβroot : ∀ k, IsRoot TwistTag.E6.tag (β k) := fun k => (hβS k).1
  have hβk : ∀ k (hk : k < n), β k = β' ⟨k, hk⟩ := fun k hk => by
    rw [hβper]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt hk)
  have hβorth : ∀ k l, k < n → l < n → k ≠ l →
      iform (β k) (β l) = 0 := by
    intro k l hk hl hkl
    rw [hβk k hk, hβk l hl]
    exact (horth' ⟨k, hk⟩ ⟨l, hl⟩ (fun h => hkl (congrArg Fin.val h))).1
  have hcycP : ∀ k, (xu * (w * r)) • β k = β (k + 1) := by
    intro k
    rw [hβper k, hβper (k + 1)]
    have hfin : (⟨(k + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) =
        ⟨((k % n) + 1) % n, Nat.mod_lt _ hn⟩ := Fin.ext (Nat.mod_add_mod k n 1).symm
    rw [hfin]
    exact hcyc ⟨k % n, Nat.mod_lt _ hn⟩
  obtain ⟨z, hzc, hzneg⟩ := exists_reflProd_neg (familyKernel a) n β hβroot hβS hβorth
  have hzall : ∀ j, z • β j = -β j := fun j => by
    rw [← hβmod j]
    exact hzneg (j % n) (Nat.mod_lt _ hn)
  refine ⟨z * xu, mul_mem hzc hxu, n, β, hn, fun k => ?_, ?_, hβS, ?_, ?_⟩
  · rw [hβper, hβper]
    congr 1
    exact Fin.ext (Nat.add_mod_right k n)
  · rw [hβper 0]
    have h0 : (⟨0 % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext (Nat.zero_mod n)
    rw [h0, hβ'0]
  · intro k l hk hl hkl
    refine ⟨hβorth k l hk hl hkl, ?_, ?_⟩
    · rw [hβk k hk, hβk l hl]
      exact (horth' ⟨k, hk⟩ ⟨l, hl⟩ (fun h => hkl (congrArg Fin.val h))).2.1
    · rw [hβk k hk, hβk l hl]
      intro h
      exact (horth' ⟨k, hk⟩ ⟨l, hl⟩ (fun h' => hkl (congrArg Fin.val h'))).2.2.2 1 1 one_pos one_pos
        (by simpa [one_smul] using h)
  · intro k
    have hpi : permLattice TwistTag.E6.perm (β k) = -(r • β k) := by
      rw [hr, neg_neg]
    have hassoc : (z * xu * w) * r = z * (xu * (w * r)) := by group
    rw [hpi, smul_neg, ← mul_smul, hassoc, mul_smul, hcycP k, hzall, neg_neg]

end Signed

end CFSG.LieType.SeitzGeneration.ExcHighThree
