module

public import CFSG.LieType.Chevalley.Native
public import CFSG.LieType.Chevalley.NativeHolds
public import CFSG.LieType.BorelTits.FixedWeighted
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits CFSG.LieType.BorelTits.Weighted RootSpace
open scoped RealInnerProductSpace

variable {τ : Tag} {K : Type} [Field K]

theorem span_labelWeight :
    Submodule.span ℝ (Set.range (labelWeight : Label τ → RootSpace τ)) = ⊤ := by
  refine eq_top_iff.2 ((span_ofLattice_isRoot (τ := τ)).symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨α, rfl⟩
  exact ⟨.inr α, rfl⟩

theorem labelWeight_eq_of_monomial [Finite K] (m : monomialGroup τ K) (a b : Label τ)
    (hab : Finsupp.basisSingleOne.repr (glRep (adjointGroup τ K) (m : adjointGroup τ K)
      (Finsupp.basisSingleOne b)) a ≠ 0) :
    labelWeight a = weylAct τ (weylHom τ K m) (labelWeight b) := by
  have h := isMonomial_weylHom m a b (by simpa using hab)
  rw [labelWeight_eq_ofLattice, labelWeight_eq_ofLattice, h, weylAct_ofLattice]

theorem labelWeight_eq_of_nrep [Finite K] (w : WeylGroup τ) (a b : Label τ)
    (hab : Finsupp.basisSingleOne.repr (glRep (adjointGroup τ K) (nrep τ K w)
      (Finsupp.basisSingleOne b)) a ≠ 0) :
    labelWeight a = weylAct τ w (labelWeight b) := by
  have h := labelWeight_eq_of_monomial ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ a b hab
  rwa [weylHom_nrep] at h

theorem labelWeight_eq_of_nrep_inv [Finite K] (w : WeylGroup τ) (a b : Label τ)
    (hab : Finsupp.basisSingleOne.repr (glRep (adjointGroup τ K) (nrep τ K w)⁻¹
      (Finsupp.basisSingleOne b)) a ≠ 0) :
    weylAct τ w (labelWeight a) = labelWeight b := by
  have h := labelWeight_eq_of_monomial (⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ :
    monomialGroup τ K)⁻¹ a b hab
  rw [map_inv, weylHom_nrep] at h
  rw [h, act_act_inv]

theorem nrep_one : nrep τ K 1 = 1 :=
  Subtype.ext (canonicalRep_one _ _)

section RootSubgroups

variable [Finite K] (F : RootSubgroups τ K)

omit [Finite K] in
theorem RootSubgroups.inner_eq_of_mem {α : Root τ} {x : adjointGroup τ K} (hx : x ∈ F.X α)
    (v : RootSpace τ) {a b : Label τ}
    (hab : Finsupp.basisSingleOne.repr ((glRep (adjointGroup τ K) x - 1)
      (Finsupp.basisSingleOne b)) a ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ ⟪labelWeight a, v⟫ = ⟪labelWeight b, v⟫ + k * ⟪ofLattice α.1, v⟫ := by
  obtain ⟨k, hk, hw⟩ := F.weight_shift α x hx a b (by simpa using hab)
  refine ⟨k, hk, ?_⟩
  rw [labelWeight_eq_ofLattice, labelWeight_eq_ofLattice, hw, ofLattice_add,
    ← Nat.cast_smul_eq_nsmul ℤ, ofLattice_smul, inner_add_left, real_inner_smul_left]
  norm_cast

omit [Finite K] in
theorem RootSubgroups.raises_of_mem {α : Root τ} {x : adjointGroup τ K} (hx : x ∈ F.X α)
    {v : RootSpace τ} (hv : 0 ≤ ⟪ofLattice α.1, v⟫) :
    Raises Finsupp.basisSingleOne labelWeight v ⟪ofLattice α.1, v⟫
      (glRep (adjointGroup τ K) x - 1) := by
  intro a b hab
  obtain ⟨k, hk, hw⟩ := F.inner_eq_of_mem hx v hab
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [hw]
  nlinarith

theorem RootSubgroups.mem_triangular_of_mem {α : Root τ} {x : adjointGroup τ K}
    (hx : x ∈ F.X α) {v : RootSpace τ} (hv : 0 ≤ ⟪ofLattice α.1, v⟫) :
    x ∈ triangular Finsupp.basisSingleOne labelWeight (glRep (adjointGroup τ K)) v := by
  rw [mem_triangular]
  have : glRep (adjointGroup τ K) x = 1 + (glRep (adjointGroup τ K) x - 1) := by abel
  rw [this]
  exact (raises_one v).add ((F.raises_of_mem hx hv).mono hv)

theorem RootSubgroups.B_le_triangular {v : RootSpace τ} (hv : v ∈ dominantCone τ) :
    F.toRootGroupData.B ≤
      triangular Finsupp.basisSingleOne labelWeight (glRep (adjointGroup τ K)) v := by
  refine sup_le ?_ ?_
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := (RootGroupData.mem_H_iff (D := F.toRootGroupData)).mp hx
    rw [mem_triangular]
    intro i j hij
    have h := labelWeight_eq_of_monomial k i j (by simpa using hij)
    change weylHom τ K k = 1 at hk
    rw [h, hk, map_one, LinearIsometryEquiv.coe_one, id, add_zero]
  · refine iSup₂_le fun α hα x hx => ?_
    exact F.mem_triangular_of_mem hx (IsRoot.inner_nonneg_of_mem_dominantCone α.2 hα hv)

theorem RootSubgroups.U_le_gradedKernel {v₀ : RootSpace τ}
    (hv₀ : ∀ α : Root τ, 0 < height α.1 → 0 < ⟪ofLattice α.1, v₀⟫) :
    F.toRootGroupData.U ≤
      gradedKernel Finsupp.basisSingleOne labelWeight (glRep (adjointGroup τ K)) v₀ := by
  refine iSup₂_le fun α hα x hx => ?_
  exact ⟨_, hv₀ α hα, F.raises_of_mem hx (hv₀ α hα).le⟩

@[expose] noncomputable def RootSubgroups.Uneg : Subgroup (adjointGroup τ K) :=
  ⨆ (α : Root τ) (_ : height α.1 < 0), F.X α

theorem RootSubgroups.Uneg_le_gradedKernel {v₀ : RootSpace τ}
    (hv₀ : ∀ α : Root τ, 0 < height α.1 → 0 < ⟪ofLattice α.1, v₀⟫) :
    F.Uneg ≤
      gradedKernel Finsupp.basisSingleOne labelWeight (glRep (adjointGroup τ K)) (-v₀) := by
  refine iSup₂_le fun α hα x hx => ?_
  have hpos : 0 < ⟪ofLattice α.1, -v₀⟫ := by
    have := hv₀ (-α) (by change 0 < height (-α.1); rw [height_neg]; omega)
    rw [inner_neg_right]
    change 0 < ⟪ofLattice (-α.1), v₀⟫ at this
    rw [ofLattice_neg, inner_neg_left] at this
    exact this
  exact ⟨_, hpos, F.raises_of_mem hx hpos.le⟩

theorem eq_one_of_mem_gradedKernel_neg {v₀ : RootSpace τ} {x : adjointGroup τ K}
    (h₁ : x ∈ gradedKernel Finsupp.basisSingleOne labelWeight (glRep (adjointGroup τ K)) v₀)
    (h₂ : x ∈ gradedKernel Finsupp.basisSingleOne labelWeight (glRep (adjointGroup τ K)) (-v₀)) :
    x = 1 := by
  obtain ⟨c₁, hc₁, H₁⟩ := h₁
  obtain ⟨c₂, hc₂, H₂⟩ := h₂
  have hzero : glRep (adjointGroup τ K) x - 1 = 0 := by
    refine eq_zero_of_repr_eq_zero Finsupp.basisSingleOne fun i j => ?_
    by_contra hij
    have e1 := H₁ i j hij
    have e2 := H₂ i j hij
    rw [inner_neg_right, inner_neg_right] at e2
    linarith
  exact glRep_injective _ (by rw [map_one]; exact sub_eq_zero.mp hzero)

theorem RootSubgroups.eq_one_of_mem_U_of_mem_Uneg {x : adjointGroup τ K}
    (hU : x ∈ F.toRootGroupData.U) (hUneg : x ∈ F.Uneg) : x = 1 :=
  eq_one_of_mem_gradedKernel_neg
    (F.U_le_gradedKernel (fun _ hα => IsRoot.inner_heightVector_pos hα) hU)
    (F.Uneg_le_gradedKernel (fun _ hα => IsRoot.inner_heightVector_pos hα) hUneg)

theorem RootSubgroups.isPGroup_U (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p F.toRootGroupData.U :=
  (isPGroup_gradedKernel (glRep (adjointGroup τ K)) p (glRep_injective _) (heightVector τ)).to_le
    (F.U_le_gradedKernel fun _ hα => IsRoot.inner_heightVector_pos hα)

theorem RootSubgroups.B_le_normalizer_U :
    F.toRootGroupData.B ≤ Subgroup.normalizer (F.toRootGroupData.U : Set (adjointGroup τ K)) :=
  sup_le RootGroupData.H_le_normalizer_U Subgroup.le_normalizer

theorem RootSubgroups.mem_U_of_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP K p]
    {t : adjointGroup τ K} (ht : t ∈ F.toRootGroupData.B) {k : ℕ} (hk : t ^ p ^ k = 1) :
    t ∈ F.toRootGroupData.U := by
  set D := F.toRootGroupData
  have hz : IsPGroup p (Subgroup.zpowers t) := by
    have hdvd : orderOf t ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hT : IsPGroup p (D.U ⊔ Subgroup.zpowers t : Subgroup (adjointGroup τ K)) :=
    IsPGroup.to_sup_of_normal_left' (F.isPGroup_U p) hz
      (Subgroup.zpowers_le.mpr (F.B_le_normalizer_U ht))
  have hle := RootGroupData.le_U_of_isPGroup (D := D) p (F.coprime_card_H p) hT le_sup_left
    (sup_le RootGroupData.U_le_B (Subgroup.zpowers_le.mpr ht))
  exact hle (le_sup_right (a := D.U) (Subgroup.mem_zpowers t))

end RootSubgroups

theorem holds_of_fixedNative [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (adjointGroup τ K)) (W' : Subgroup (WeylGroup τ))
    (E' : Submodule ℝ (RootSpace τ)) (v₀ : RootSpace τ)
    (hv₀ : ∀ α : Root τ, 0 < height α.1 → 0 < ⟪ofLattice α.1, v₀⟫) (hv₀E : v₀ ∈ E')
    (hE' : ∀ w ∈ W', ∀ x ∈ E', weylAct τ w x ∈ E') (hnΓ : ∀ w ∈ W', nrep τ K w ∈ Γ)
    (hfix : ∀ v ∈ E', (∀ w ∈ W', weylAct τ w v = v) → v = 0)
    (hcover : ∀ x ∈ E', ∃ w ∈ W', ∃ y ∈ E', y ∈ dominantCone τ ∧ x = weylAct τ w y)
    (hbruhat : ∀ g ∈ Γ, ∃ w ∈ W', ∃ b₁ ∈ (nativeData τ K).B, b₁ ∈ Γ ∧
      ∃ b₂ ∈ (nativeData τ K).B, b₂ ∈ Γ ∧ g = b₁ * nrep τ K w * b₂)
    (hUw : ∀ w ∈ W', w ≠ 1 → ∃ u ∈ (nativeData τ K).U, u ∈ Γ ∧
      nrep τ K w * u * (nrep τ K w)⁻¹ ∉ (nativeData τ K).U) :
    Holds Γ p := by
  set F := nativeRootSubgroups τ K
  refine holds_of_fixedData (b := Finsupp.basisSingleOne) (wt := labelWeight)
    (glRep (adjointGroup τ K)) p (glRep_injective _) (weylAct τ) (nrep τ K)
    (nativeData τ K).B (nativeData τ K).U (dominantCone τ) v₀ Γ W' E' span_labelWeight
    (fun w _ i j hij => labelWeight_eq_of_nrep w i j hij)
    (fun w _ i j hij => labelWeight_eq_of_nrep_inv w i j hij) ?_ ?_ (F.isPGroup_U p)
    F.B_le_normalizer_U (fun t ht ⟨k, hk⟩ => F.mem_U_of_pow_eq_one p ht hk)
    (by rw [nrep_one]; exact one_mem _) hE' hnΓ hfix hcover hbruhat hUw hv₀E
  · intro x hx v hv i j hij
    have := (F.B_le_triangular hv hx) i j hij
    linarith
  · intro u hu i j hij
    obtain ⟨c, hc, huc⟩ := F.U_le_gradedKernel hv₀ hu
    have := huc i j (by rwa [LinearMap.sub_apply, Module.End.one_apply])
    linarith

end CFSG.LieType.Chevalley
