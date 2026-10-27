module

public import CFSG.ClassicalInvolution.Q3.TL3DichBurn

public section

namespace CFSG.ClassicalInvolution.Q3.TightA

open CFSG CFSG.ClassicalInvolution.Asc77

variable {Y : Type} [Group Y]

abbrev inn (A : Subgroup Y) : Subgroup (MulAut ↥A) := (MulAut.conj : ↥A →* MulAut ↥A).range

theorem ker_conj (A : Subgroup Y) :
    (MulAut.conj : ↥A →* MulAut ↥A).ker = Subgroup.center ↥A := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := DFunLike.congr_fun h g
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = x * g * x⁻¹ * x := by rw [this]
      _ = x * g := by group
  · intro h
    refine MulEquiv.ext fun g => ?_
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g]
    group

noncomputable def innEquiv (A : Subgroup Y) : ↥A ⧸ Subgroup.center ↥A ≃* ↥(inn A) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conj A).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem inn_isSimpleGroup {A : Subgroup Y} (hA : CFSG.IsQuasisimple ↥A) :
    IsSimpleGroup ↥(inn A) :=
  have := hA.2.1
  (innEquiv A).symm.isSimpleGroup

theorem inn_nonabelian {A : Subgroup Y} (hA : CFSG.IsQuasisimple ↥A) :
    ∃ a b : ↥(inn A), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hA.2.2
  refine ⟨innEquiv A a, innEquiv A b, fun h => hab ?_⟩
  apply (innEquiv A).injective
  rw [map_mul, map_mul, h]

theorem not_isSolvable_inn [Finite Y] {A : Subgroup Y} (hA : CFSG.IsQuasisimple ↥A) :
    ¬ Group.IsSolvable ↥(inn A) := by
  intro hs
  have : Group.IsPerfect ↥A := hA.1
  have : Group.IsPerfect ↥(inn A) :=
    Group.IsPerfect.ofSurjective (f := (MulAut.conj : ↥A →* MulAut ↥A).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨a, b, hab⟩ := inn_nonabelian hA
  have : Nontrivial ↥(inn A) := ⟨⟨a * b, b * a, hab⟩⟩
  exact Group.IsPerfect.not_isSolvable ↥(inn A) hs

theorem mem_normalizer_of_acts {A : Subgroup Y} {x w : Y} (hx : x ∈ A)
    (h : ∀ a ∈ A, w * a * w⁻¹ = x * a * x⁻¹) : w ∈ Subgroup.normalizer (A : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [h b hb]
    exact A.mul_mem (A.mul_mem hx hb) (A.inv_mem hx)
  · intro hb
    have hc : x⁻¹ * (w * b * w⁻¹) * x ∈ A :=
      A.mul_mem (A.mul_mem (A.inv_mem hx) hb) hx
    have e := h _ hc
    have e2 : w * (x⁻¹ * (w * b * w⁻¹) * x) * w⁻¹ = w * b * w⁻¹ := by
      rw [e]; group
    have e3 : x⁻¹ * (w * b * w⁻¹) * x = b := by
      have := congrArg (fun y => w⁻¹ * y * w) e2
      simpa [mul_assoc] using this
    rw [← e3]
    exact hc

@[expose] noncomputable def actOn (A W : Subgroup Y) : ↥(W ⊓ Subgroup.normalizer (A : Set Y)) →* MulAut ↥A :=
  A.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)

theorem actOn_apply (A W : Subgroup Y) (g : ↥(W ⊓ Subgroup.normalizer (A : Set Y))) (a : ↥A) :
    ((actOn A W g a : ↥A) : Y) = (g : Y) * (a : Y) * (g : Y)⁻¹ := rfl

theorem conj_mem_range_actOn {A W : Subgroup Y} {x w : Y} (hx : x ∈ A) (hw : w ∈ W)
    (h : ∀ a ∈ A, w * a * w⁻¹ = x * a * x⁻¹) :
    MulAut.conj (⟨x, hx⟩ : ↥A) ∈ (actOn A W).range := by
  refine ⟨⟨w, hw, mem_normalizer_of_acts hx h⟩, ?_⟩
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [actOn_apply]
  exact h a a.2

theorem false_of_solvable_covers [Finite Y] {A W : Subgroup Y} (hA : CFSG.IsQuasisimple ↥A)
    (hW : Group.IsSolvable ↥W) (hcov : ∀ x ∈ A, ∃ w ∈ W, ∀ a ∈ A, w * a * w⁻¹ = x * a * x⁻¹) :
    False := by
  have hW1 : Group.IsSolvable ↥(W ⊓ Subgroup.normalizer (A : Set Y)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hrange : Group.IsSolvable ↥(actOn A W).range :=
    Group.isSolvable_of_surjective (f := (actOn A W).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hle : inn A ≤ (actOn A W).range := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨w, hw, hwx⟩ := hcov x hx
    exact conj_mem_range_actOn hx hw hwx
  apply not_isSolvable_inn hA
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective _)

theorem false_of_cyclic_cover [Finite Y] {A X V₀ : Subgroup Y} (hA : CFSG.IsQuasisimple ↥A)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center ↥A)) {a : Y} (haA : a ∈ A)
    (hanc : ∃ y ∈ A, a * y ≠ y * a) (ha2 : ∀ y ∈ A, (a * a) * y = y * (a * a))
    (htwin : ∀ w ∈ A, (∀ y ∈ A, (w * a * w⁻¹ * a⁻¹) * y = y * (w * a * w⁻¹ * a⁻¹)) →
      w * a = a * w)
    (hV : IsSylow2In V₀ (A ⊓ Subgroup.centralizer ({a} : Set Y))) (hX : IsCyclic ↥X)
    (hcov : ∀ x ∈ V₀, ∃ ξ ∈ X, ∀ y ∈ A, ξ * y * ξ⁻¹ = x * y * x⁻¹) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι : ↥A →* MulAut ↥A := MulAut.conj with hι
  set a' : ↥A := ⟨a, haA⟩ with ha'
  set i : MulAut ↥A := ι a' with hi
  have hV0A : V₀ ≤ A := hV.1.trans inf_le_left
  have hiI : i ∈ inn A := ⟨a', rfl⟩
  have hi2 : i * i = 1 := by
    rw [hi, ← map_mul]
    refine MulEquiv.ext fun y => Subtype.ext ?_
    simp only [hι, ha', MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      MulMemClass.mk_mul_mk]
    calc a * a * (y : Y) * (a * a)⁻¹ = (y : Y) * (a * a) * (a * a)⁻¹ := by rw [ha2 y y.2]
      _ = y := by group
  have hi1 : i ≠ 1 := by
    intro h
    obtain ⟨y, hyA, hay⟩ := hanc
    have := congrArg (fun φ : MulAut ↥A => ((φ ⟨y, hyA⟩ : ↥A) : Y)) h
    simp only [hi, hι, ha', MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at this
    apply hay
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [this]
  set V : Subgroup (MulAut ↥A) := (V₀.subgroupOf A).map ι with hVdef
  have hVsyl : IsSylow2In V (inn A ⊓ Subgroup.centralizer ({i} : Set (MulAut ↥A))) := by
    refine ⟨?_, (hV.2.1.comap_subtype).map ι, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hxa : (x : Y) * a = a * x := by
        have := (hV.1 hx).2
        exact (Subgroup.mem_centralizer_singleton_iff.mp this)
      rw [hi, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxa
    · intro V' hV'le hV'2 hVV'
      set P : Subgroup Y := (V'.comap ι).map A.subtype with hPdef
      have hker : IsPGroup 2 ↥ι.ker := by
        rw [hι, ker_conj]
        exact hZ2
      have hP2 : IsPGroup 2 ↥P := (hV'2.comap_of_ker_isPGroup ι hker).map _
      have hPle : P ≤ A ⊓ Subgroup.centralizer ({a} : Set Y) := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hxc : ι x * i = i * ι x :=
          Subgroup.mem_centralizer_singleton_iff.mp (hV'le hx).2
        have hz : ∀ y ∈ A, ((x : Y) * a * (x : Y)⁻¹ * a⁻¹) * y =
            y * ((x : Y) * a * (x : Y)⁻¹ * a⁻¹) := by
          intro y hy
          have e1 : ι (x * a' * x⁻¹ * a'⁻¹) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hi, hxc]
            group
          have e2 : x * a' * x⁻¹ * a'⁻¹ ∈ Subgroup.center ↥A := by
            rw [← ker_conj A]
            exact e1
          have := Subgroup.mem_center_iff.mp e2 ⟨y, hy⟩
          have := congrArg Subtype.val this
          simpa [ha'] using this.symm
        exact htwin x x.2 hz
      have hV0P : V₀ ≤ P := by
        intro x hx
        refine ⟨⟨x, hV0A hx⟩, hVV' ⟨⟨x, hV0A hx⟩, hx, rfl⟩, rfl⟩
      have hPeq : P = V₀ := hV.eq_of_le hP2 hPle hV0P
      refine le_antisymm ?_ hVV'
      intro v hv
      obtain ⟨x, rfl⟩ := (hV'le hv).1
      have hxP : (x : Y) ∈ P := ⟨x, hv, rfl⟩
      rw [hPeq] at hxP
      exact ⟨x, hxP, rfl⟩
  have hVcyc : IsCyclic ↥V := by
    have hXN : ∀ v ∈ V, v ∈ (actOn A X).range := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨ξ, hξ, hξx⟩ := hcov x hx
      exact conj_mem_range_actOn x.2 hξ hξx
    have hcyc1 : IsCyclic ↥(X ⊓ Subgroup.normalizer (A : Set Y)) :=
      isCyclic_of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
    have hcyc2 : IsCyclic ↥(actOn A X).range :=
      isCyclic_of_surjective (actOn A X).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    exact isCyclic_of_injective (Subgroup.inclusion hXN) (Subgroup.inclusion_injective _)
  exact not_isCyclic_of_isSylow2In_centralizer (inn_isSimpleGroup hA) (inn_nonabelian hA) hiI hi2
    hi1 hVsyl hVcyc

end CFSG.ClassicalInvolution.Q3.TightA
