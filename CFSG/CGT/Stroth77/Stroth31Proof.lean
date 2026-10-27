module

public import CFSG.CGT.Stroth77.Stroth31
public import CFSG.GroupTheory.HuppertProduct.PGroupMho

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

noncomputable def fixedSubgroup (P Q : Type*) [Group P] [Group Q] [MulDistribMulAction P Q] :
    Subgroup Q where
  carrier := MulAction.fixedPoints P Q
  one_mem' := by
    rw [MulAction.mem_fixedPoints]
    intro p
    exact smul_one p
  mul_mem' := by
    intro x y hx hy
    rw [MulAction.mem_fixedPoints] at hx hy ⊢
    intro p
    rw [smul_mul', hx p, hy p]
  inv_mem' := by
    intro x hx
    rw [MulAction.mem_fixedPoints] at hx ⊢
    intro p
    rw [smul_inv', hx p]

@[simp]
theorem mem_fixedSubgroup {P Q : Type*} [Group P] [Group Q] [MulDistribMulAction P Q]
    {x : Q} : x ∈ fixedSubgroup P Q ↔ ∀ p : P, p • x = x :=
  Iff.rfl

theorem finrank_le_two_of_invariant_span {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (U R : V ≃ₗ[ZMod 2] V)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ x ∈ W, U x ∈ W) → (∀ x ∈ W, R x ∈ W) → W = ⊥ ∨ W = ⊤)
    {v w : V} (hv : v ≠ 0)
    (hU : ∀ x ∈ Submodule.span (ZMod 2) ({v, w} : Set V), U x ∈ Submodule.span (ZMod 2) ({v, w} : Set V))
    (hR : ∀ x ∈ Submodule.span (ZMod 2) ({v, w} : Set V), R x ∈ Submodule.span (ZMod 2) ({v, w} : Set V)) :
    Module.finrank (ZMod 2) V ≤ 2 := by
  classical
  haveI : Fact (1 < 2) := ⟨by decide⟩
  let W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({v, w} : Set V)
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hmem : v ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hbot]
      exact Submodule.subset_span (by simp)
    exact hv (by simpa using hmem)
  have hWtop : W = ⊤ := by
    rcases hirr W hU hR with h | h
    · exact absurd h hWne
    · exact h
  have hfin : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) W := by
    rw [← finrank_top (ZMod 2) V, ← hWtop]
  rw [hfin]
  let s : Finset V := {v, w}
  have h := finrank_span_finset_le_card (R := ZMod 2) (M := V) (s := s)
  have hcard : s.card ≤ 2 := by
    simpa [s] using (Finset.card_le_two (a := v) (b := w))
  have hset : ((s : Finset V) : Set V) = ({v, w} : Set V) := by simp [s]
  change Module.finrank (ZMod 2) W ≤ 2
  rw [hset] at h
  exact h.trans hcard

theorem finrank_le_two_of_sigmaThree {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (U R : V ≃ₗ[ZMod 2] V)
    (hU2 : ∀ v, U (U v) = v)
    (hR3 : ∀ v, R (R (R v)) = v)
    (hrel : ∀ v, R (U v) = U (R.symm v))
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ x ∈ W, U x ∈ W) → (∀ x ∈ W, R x ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.finrank (ZMod 2) V ≤ 2 := by
  classical
  haveI : Fact (1 < 2) := ⟨by decide⟩
  have span_R_invariant : ∀ {v : V}, R (R v) = R v + v →
      ∀ x ∈ Submodule.span (ZMod 2) ({v, R v} : Set V),
        R x ∈ Submodule.span (ZMod 2) ({v, R v} : Set V) := by
    intro v hquad
    intro x hx
    refine Submodule.span_induction (p := fun x _ =>
      R x ∈ Submodule.span (ZMod 2) ({v, R v} : Set V)) ?_ ?_ ?_ ?_ hx
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · rw [hquad]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
  have span_U_invariant : ∀ {v w : V} {W : Submodule (ZMod 2) V},
      W = Submodule.span (ZMod 2) ({v, w} : Set V) →
      U v ∈ W → U w ∈ W → ∀ x ∈ W, U x ∈ W := by
    intro v w W hW hv hw
    rw [hW] at hv hw ⊢
    intro x hx
    refine Submodule.span_induction (p := fun x _ =>
      U x ∈ Submodule.span (ZMod 2) ({v, w} : Set V)) ?_ ?_ ?_ ?_ hx
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hw
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
  have quad_of_no_fixed : (∀ v, R v = v → v = 0) → ∀ v, R (R v) = R v + v := by
    intro hno v
    have hfix : R (R (R v) + R v + v) = R (R v) + R v + v := by
      rw [map_add, map_add, hR3 v]
      abel
    have hzero : R (R v) + R v + v = 0 := hno _ hfix
    have hself : (R v + v) + (R v + v) = 0 := by
      have h2 : (2 : ZMod 2) • (R v + v) = 0 := by
        rw [show (2 : ZMod 2) = 0 from by decide, zero_smul]
      rwa [two_smul] at h2
    have hzero' : R (R v) + (R v + v) = 0 := by
      rw [← add_assoc]
      exact hzero
    exact add_right_cancel (hzero'.trans hself.symm)
  by_cases hfix : ∃ v, v ≠ 0 ∧ R v = v
  ·
    obtain ⟨v₀, hv₀, hRfix⟩ := hfix
    let W : Submodule (ZMod 2) V :=
      { carrier := {v | R v = v}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [map_add, hx, hy]
        smul_mem' := by
          intro a x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          rw [map_smul, hx] }
    have hWU : ∀ x ∈ W, U x ∈ W := by
      intro x hx
      have hx' : R x = x := hx
      change R (U x) = U x
      rw [hrel x, show R.symm x = x from R.symm_apply_eq.mpr hx'.symm]
    have hWR : ∀ x ∈ W, R x ∈ W := by
      intro x hx
      have hx' : R x = x := hx
      change R (R x) = R x
      rw [hx']
      exact hx'
    have hWtop : W = ⊤ := by
      rcases hirr W hWU hWR with h | h
      · exfalso
        have : v₀ ∈ (⊥ : Submodule (ZMod 2) V) := by
          rw [← h]; exact hRfix
        exact hv₀ (by simpa using this)
      · exact h
    have hRtriv : ∀ x, R x = x := by
      intro x
      have : x ∈ W := by rw [hWtop]; exact Submodule.mem_top
      exact this
    by_cases hV : Nontrivial V
    · obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hU : ∀ x ∈ Submodule.span (ZMod 2) ({v, U v} : Set V),
          U x ∈ Submodule.span (ZMod 2) ({v, U v} : Set V) := by
        have hspanU := span_U_invariant (v := v) (w := U v)
          (W := Submodule.span (ZMod 2) ({v, U v} : Set V)) rfl
          (Submodule.subset_span (by simp)) (by
            rw [hU2 v]
            exact Submodule.subset_span (by simp))
        exact hspanU
      have hR : ∀ x ∈ Submodule.span (ZMod 2) ({v, U v} : Set V),
          R x ∈ Submodule.span (ZMod 2) ({v, U v} : Set V) := by
        intro x hx
        rw [hRtriv x]
        exact hx
      exact finrank_le_two_of_invariant_span U R hirr hv hU hR
    · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      have hzero : Module.finrank (ZMod 2) V = 0 :=
        Module.finrank_zero_of_subsingleton
      rw [hzero]
      omega
  ·
    push_neg at hfix
    have hno : ∀ v, R v = v → v = 0 := by
      intro v hv
      by_contra hne
      exact hfix v hne hv
    have hquad : ∀ v, R (R v) = R v + v := quad_of_no_fixed hno
    by_cases hV : Nontrivial V
    · obtain ⟨v, hv⟩ := exists_ne (0 : V)
      by_cases hUv : U v = v
      ·
        have hWR : ∀ x ∈ Submodule.span (ZMod 2) ({v, R v} : Set V),
            R x ∈ Submodule.span (ZMod 2) ({v, R v} : Set V) :=
          span_R_invariant (hquad v)
        have hU : ∀ x ∈ Submodule.span (ZMod 2) ({v, R v} : Set V),
            U x ∈ Submodule.span (ZMod 2) ({v, R v} : Set V) := by
          have hspanU := span_U_invariant (v := v) (w := R v)
            (W := Submodule.span (ZMod 2) ({v, R v} : Set V)) rfl
            (by rw [hUv]; exact Submodule.subset_span (by simp))
            (by
              have h1 : R (U (R v)) = v := by
                rw [hrel (R v), R.symm_apply_apply, hUv]
              have h2 : U (R v) = R.symm v := by
                simpa using congrArg R.symm h1
              have h3 : R.symm v = R (R v) :=
                R.symm_apply_eq.mpr (hR3 v).symm
              rw [h2, h3, hquad v]
              exact Submodule.add_mem _
                (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
          exact hspanU
        exact finrank_le_two_of_invariant_span U R hirr hv hU hWR
      ·
        let z : V := v + U v
        have hz : z ≠ 0 := by
          intro hz0
          have hvv : v + v = 0 := by
            rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from by decide, zero_smul]
          have : U v = v := by
            have hsum : v + U v = v + v := hz0.trans hvv.symm
            exact (add_right_inj v).mp hsum
          exact hUv this
        have hzU : U z = z := by
          simp only [z]
          rw [map_add, hU2]
          abel
        have hU : ∀ x ∈ Submodule.span (ZMod 2) ({z, R z} : Set V),
            U x ∈ Submodule.span (ZMod 2) ({z, R z} : Set V) := by
          have hspanU := span_U_invariant (v := z) (w := R z)
            (W := Submodule.span (ZMod 2) ({z, R z} : Set V)) rfl
            (by rw [hzU]; exact Submodule.subset_span (by simp))
            (by
              have h1 : R (U (R z)) = z := by
                rw [hrel (R z), R.symm_apply_apply, hzU]
              have h2 : U (R z) = R.symm z := by
                simpa using congrArg R.symm h1
              have h3 : R.symm z = R (R z) :=
                R.symm_apply_eq.mpr (hR3 z).symm
              rw [h2, h3, hquad z]
              exact Submodule.add_mem _
                (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
          exact hspanU
        have hWR : ∀ x ∈ Submodule.span (ZMod 2) ({z, R z} : Set V),
            R x ∈ Submodule.span (ZMod 2) ({z, R z} : Set V) :=
          span_R_invariant (hquad z)
        exact finrank_le_two_of_invariant_span U R hirr hz hU hWR
    · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      have hzero : Module.finrank (ZMod 2) V = 0 :=
        Module.finrank_zero_of_subsingleton
      rw [hzero]
      omega

theorem le_normalizer_of_conj_mem {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ x ∈ H, k * x * k⁻¹ ∈ H) : K ≤ Subgroup.normalizer H := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h k hk x
  · intro hx
    have := h k⁻¹ (K.inv_mem hk) (k * x * k⁻¹) hx
    simpa [mul_assoc] using this



@[expose]
noncomputable def conjOnSubgroupC {S : Type*} [Group S] {C : Subgroup S} (g : S)
    (hg : g ∈ Subgroup.normalizer C) : C →* C where
  toFun x := ⟨g * (x : S) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : S)).mp x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Subgroup.coe_mk, Subgroup.coe_mul]
    group

theorem conjOnSubgroupC_bijective {S : Type*} [Group S] {C : Subgroup S} (g : S)
    (hg : g ∈ Subgroup.normalizer C) : Function.Bijective (conjOnSubgroupC g hg) := by
  constructor
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    simp only [conjOnSubgroupC, MonoidHom.coe_mk, OneHom.coe_mk] at h
    apply Subtype.ext
    calc (x : S) = g⁻¹ * (g * (x : S) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (y : S) * g⁻¹) * g := by rw [h]
      _ = (y : S) := by group
  · intro y
    refine ⟨⟨g⁻¹ * (y : S) * g, ?_⟩, ?_⟩
    · have hg' : g⁻¹ ∈ Subgroup.normalizer C := Subgroup.inv_mem _ hg
      have h := (Subgroup.mem_normalizer_iff.mp hg' (y : S)).mp y.2
      simpa using h
    · ext
      simp only [conjOnSubgroupC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
      group

@[expose]
noncomputable def conjAutSubgroupC {S : Type*} [Group S] {C : Subgroup S} (g : S)
    (hg : g ∈ Subgroup.normalizer C) : MulAut C :=
  MulEquiv.ofBijective (conjOnSubgroupC g hg) (conjOnSubgroupC_bijective g hg)

@[expose]
noncomputable def conjQuotientMapC {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    (C ⧸ B.subgroupOf C) →* (C ⧸ B.subgroupOf C) :=
  QuotientGroup.map (B.subgroupOf C) (B.subgroupOf C) (conjOnSubgroupC g hgC) (by
    intro x hx
    change g * (x : S) * g⁻¹ ∈ B
    exact (Subgroup.mem_normalizer_iff.mp hgB (x : S)).mp (Subgroup.mem_subgroupOf.mp hx))

@[simp]
theorem conjQuotientMapC_mk {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjQuotientMapC g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjOnSubgroupC g hgC x) := by
  rw [conjQuotientMapC]
  exact QuotientGroup.map_mk _ _ _ _ x

theorem conjQuotientMapC_left_inv {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.LeftInverse
      (conjQuotientMapC g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjQuotientMapC g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotientMapC_mk, conjQuotientMapC_mk]
    congr 1
    ext
    simp only [conjOnSubgroupC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
    group

theorem conjQuotientMapC_right_inv {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.RightInverse
      (conjQuotientMapC g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjQuotientMapC g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotientMapC_mk, conjQuotientMapC_mk]
    congr 1
    ext
    simp only [conjOnSubgroupC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
    group

@[expose]
noncomputable def conjAutQuotientC {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) : MulAut (C ⧸ B.subgroupOf C) :=
  MulEquiv.ofBijective (conjQuotientMapC g hgC hgB)
    ⟨(conjQuotientMapC_left_inv g hgC hgB).injective,
     (conjQuotientMapC_right_inv g hgC hgB).surjective⟩

@[simp]
theorem conjAutQuotientC_apply_mk {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjAutQuotientC g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjOnSubgroupC g hgC x) :=
  conjQuotientMapC_mk g hgC hgB x

@[expose]
noncomputable def conjAutQuotientHomC {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] :
    (Subgroup.normalizer (C : Set S) ⊓ Subgroup.normalizer (B : Set S) : Subgroup S) →*
      MulAut (C ⧸ B.subgroupOf C) where
  toFun g := conjAutQuotientC (g : S) (Subgroup.mem_inf.mp g.2).1 (Subgroup.mem_inf.mp g.2).2
  map_one' := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [conjAutQuotientC_apply_mk]
      simp [conjOnSubgroupC]
  map_mul' g h := by
    set hgC : (g:S) ∈ Subgroup.normalizer C := (Subgroup.mem_inf.mp g.2).1
    set hhC : (h:S) ∈ Subgroup.normalizer C := (Subgroup.mem_inf.mp h.2).1
    set hgB : (g:S) ∈ Subgroup.normalizer B := (Subgroup.mem_inf.mp g.2).2
    set hhB : (h:S) ∈ Subgroup.normalizer B := (Subgroup.mem_inf.mp h.2).2
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change conjAutQuotientC ((g:S) * (h:S)) (Subgroup.mul_mem _ hgC hhC)
          (Subgroup.mul_mem _ hgB hhB) (QuotientGroup.mk x) =
        conjAutQuotientC (g:S) hgC hgB
          (conjAutQuotientC (h:S) hhC hhB (QuotientGroup.mk x))
      rw [conjAutQuotientC_apply_mk (g := (g:S) * (h:S))
          (hgC := Subgroup.mul_mem _ hgC hhC) (hgB := Subgroup.mul_mem _ hgB hhB),
        conjAutQuotientC_apply_mk (g := (h:S)) (hgC := hhC) (hgB := hhB),
        conjAutQuotientC_apply_mk (g := (g:S)) (hgC := hgC) (hgB := hgB)
          (x := conjOnSubgroupC (h:S) hhC x)]
      congr 1
      ext
      simp only [conjOnSubgroupC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk,
        Subgroup.coe_mul]
      group

theorem conjAutQuotient_eq_bot_or_top {X : StrothAmbient G} {Z : StrothDatum X}
    {C : Subgroup G} [hN : (Z.D.subgroupOf C).Normal]
    (hDC : Z.D ≤ C)
    (hmin : IsMinimalLModuleMod Z.dataD C)
    (hLD : ∀ l ∈ Z.dataD.L, l ∈ Subgroup.normalizer (Z.D : Set G))
    (R : Subgroup (C ⧸ Z.D.subgroupOf C))
    (hR : ∀ (l : G) (hl : l ∈ Z.dataD.L) (r : C ⧸ Z.D.subgroupOf C), r ∈ R →
      conjAutQuotientC l (hmin.le_normalizer hl) (hLD l hl) r ∈ R) :
    R = ⊥ ∨ R = ⊤ := by
  classical
  let π : C →* C ⧸ Z.D.subgroupOf C := QuotientGroup.mk' (Z.D.subgroupOf C)
  let E : Subgroup G := (R.comap π).map C.subtype
  have hDE : Z.D ≤ E := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hDC hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hxN : (⟨x, hDC hx⟩ : C) ∈ Z.D.subgroupOf C := by
      rwa [Subgroup.mem_subgroupOf]
    have hxone : π ⟨x, hDC hx⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hxN
    rw [hxone]
    exact R.one_mem
  have hEC : E ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, -, rfl⟩
    exact c.2
  have hEinv : Z.dataD.L ≤ Subgroup.normalizer E := by
    refine le_normalizer_of_conj_mem ?_
    intro l hl x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, hc, rfl⟩
    have hcR : π c ∈ R := hc
    refine Subgroup.mem_map.mpr ⟨conjOnSubgroupC l (hmin.le_normalizer hl) c, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hcomm : π (conjOnSubgroupC l (hmin.le_normalizer hl) c) =
        conjAutQuotientC l (hmin.le_normalizer hl) (hLD l hl) (π c) := by
      exact (conjAutQuotientC_apply_mk l (hmin.le_normalizer hl) (hLD l hl) c).symm
    rw [hcomm]
    exact hR l hl (π c) hcR
  have hdich : E = Z.D ∨ E = C := by
    by_cases hECeq : E = C
    · exact Or.inr hECeq
    · refine Or.inl ?_
      have hEltC : E < C := lt_of_le_of_ne hEC hECeq
      have hnotlt : ¬ Z.D < E := fun hDElt => hmin.2.2 E hDElt hEltC hEinv
      have hEDeq : Z.D = E := by
        by_contra hne
        exact hnotlt (lt_of_le_of_ne hDE hne)
      exact hEDeq.symm
  rcases hdich with hED | hECeq
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (Z.D.subgroupOf C) r
    have hcE : (c : G) ∈ E := by
      refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      rwa [hc]
    have hcD : (c : G) ∈ Z.D := by simpa [hED] using hcE
    have hcone : π c = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by rwa [Subgroup.mem_subgroupOf])
    rw [← hc, hcone]
  · right
    rw [Subgroup.eq_top_iff']
    intro r
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (Z.D.subgroupOf C) r
    have hcE : (c : G) ∈ E := by
      rw [hECeq]
      exact c.2
    rcases Subgroup.mem_map.mp hcE with ⟨c', hc', hc'eq⟩
    have hcc' : c' = c := Subtype.ext hc'eq
    rw [← hc]
    rw [← hcc']
    exact hc'


theorem isElementaryAbelian_quotient_of_minimal {X : StrothAmbient G} {Z : StrothDatum X}
    {C : Subgroup G} [hN : (Z.D.subgroupOf C).Normal]
    (hDC : Z.D ≤ C) (hCR : C ≤ strothR X Z.D)
    (hmin : IsMinimalLModuleMod Z.dataD C)
    (hLD : ∀ l ∈ Z.dataD.L, l ∈ Subgroup.normalizer (Z.D : Set G)) :
    IsElementaryAbelian 2 (C ⧸ Z.D.subgroupOf C) := by
  classical
  let Q := C ⧸ Z.D.subgroupOf C
  have hQp : IsPGroup 2 Q :=
    (isPGroup_of_le_strothR hCR).to_quotient (Z.D.subgroupOf C)
  have hQne : Z.D.subgroupOf C ≠ ⊤ := by
    intro htop
    exact not_le_of_gt hmin.d_lt (Subgroup.subgroupOf_eq_top.mp htop)
  haveI hQnt : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hQne
  have hcenter_inv : ∀ (l : G) (hl : l ∈ Z.dataD.L) (r : Q),
      r ∈ Subgroup.center Q →
        conjAutQuotientC l (hmin.le_normalizer hl) (hLD l hl) r ∈ Subgroup.center Q := by
    intro l hl r hr
    have hmap := (Subgroup.characteristic_iff_map_le.mp Subgroup.centerCharacteristic)
      (conjAutQuotientC l (hmin.le_normalizer hl) (hLD l hl))
    exact hmap (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)
  have hcenter := conjAutQuotient_eq_bot_or_top (Z := Z) (C := C) hDC hmin hLD
    (Subgroup.center Q) hcenter_inv
  have hcenter_top : Subgroup.center Q = ⊤ := by
    rcases hcenter with hbot | htop
    · exact absurd hbot (ne_of_gt hQp.bot_lt_center)
    · exact htop
  haveI hQcomm : IsMulCommutative Q := Subgroup.center_eq_top_iff.mp hcenter_top
  let M : Subgroup Q := CFSG.GroupTheory.HuppertProduct.mho (⊤ : Subgroup Q) 2
  have hM_inv : ∀ (l : G) (hl : l ∈ Z.dataD.L) (r : Q), r ∈ M →
      conjAutQuotientC l (hmin.le_normalizer hl) (hLD l hl) r ∈ M := by
    intro l hl r hr
    let φ := conjAutQuotientC l (hmin.le_normalizer hl) (hLD l hl)
    have hmap : M.map φ.toMonoidHom ≤ M := by
      rw [Subgroup.map_le_iff_le_comap]
      refine CFSG.GroupTheory.HuppertProduct.mho_le_of_forall ?_
      intro x _hx
      rw [Subgroup.mem_comap, map_pow]
      exact CFSG.GroupTheory.HuppertProduct.pow_mem_mho (S := (⊤ : Subgroup Q)) (n := 2)
        (g := φ x) (Subgroup.mem_top _)
    exact hmap (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)
  have hM := conjAutQuotient_eq_bot_or_top (Z := Z) (C := C) hDC hmin hLD M hM_inv
  have hMbot : M = ⊥ := by
    rcases hM with hbot | htop
    · exact hbot
    · exfalso
      have htopSub : IsPGroup 2 ↥(⊤ : Subgroup Q) :=
        hQp.of_equiv Subgroup.topEquiv.symm
      have hbot : (⊤ : Subgroup Q) = ⊥ :=
        CFSG.GroupTheory.HuppertProduct.eq_bot_of_mho_eq_self (S := (⊤ : Subgroup Q))
          (p := 2) htopSub htop
      exact top_ne_bot (α := Subgroup Q) hbot
  refine
    { toIsMulCommutative := hQcomm
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  have hxM : x ^ 2 ∈ M :=
    CFSG.GroupTheory.HuppertProduct.pow_mem_mho (S := (⊤ : Subgroup Q)) (n := 2)
      (g := x) (Subgroup.mem_top _)
  rw [hMbot] at hxM
  simpa using hxM


theorem mem_normalizer_closure_pair_of_conj_mem {S : Type*} [Group S] [Finite S] {g u v : S}
    (hu : g * u * g⁻¹ ∈ Subgroup.closure ({u, v} : Set S))
    (hv : g * v * g⁻¹ ∈ Subgroup.closure ({u, v} : Set S)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({u, v} : Set S)) := by
  let P : Subgroup S := Subgroup.closure ({u, v} : Set S)
  have hmap : P.map (MulAut.conj g).toMonoidHom ≤ P := by
    rw [Subgroup.map_le_iff_le_comap]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa [P, MulAut.conj_apply] using hu
    · simpa [P, MulAut.conj_apply] using hv
  have hcard : Nat.card P ≤ Nat.card (P.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hEq : P.map (MulAut.conj g).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hmap hcard
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hEq

theorem StrothWeakTypeData.L_le_normalizer_closure_uv_t {S : Type*} [Group S] [Finite S]
    {B : Subgroup S}
    {τ : StrothTypeIndex} (D : StrothWeakTypeData B τ) :
    D.L ≤ Subgroup.normalizer (Subgroup.closure ({D.uv, D.t} : Set S)) := by
  rw [StrothWeakTypeData.L, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have huv_inv : D.uv⁻¹ = D.uv := inv_eq_of_mul_eq_one_right D.uv_sq
  have ht_inv : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right D.t_sq
  have hu_inv : D.u⁻¹ = D.u := inv_eq_of_mul_eq_one_right D.u_sq
  rcases hg with rfl | rfl | rfl | rfl
  ·
    refine mem_normalizer_closure_pair_of_conj_mem ?_ ?_
    · have : D.uv * D.uv * D.uv⁻¹ = D.uv := by
        calc D.uv * D.uv * D.uv⁻¹ = 1 * D.uv⁻¹ := by rw [D.uv_sq]
          _ = D.uv⁻¹ := by group
          _ = D.uv := huv_inv
      rw [this]
      exact Subgroup.subset_closure (by simp)
    · have : D.uv * D.t * D.uv⁻¹ = D.t := by
        calc D.uv * D.t * D.uv⁻¹ = D.t * D.uv * D.uv⁻¹ := by rw [D.uv_comm_t]
          _ = D.t * (D.uv * D.uv⁻¹) := by group
          _ = D.t := by rw [mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.subset_closure (by simp)
  ·
    refine mem_normalizer_closure_pair_of_conj_mem ?_ ?_
    · have : D.t * D.uv * D.t⁻¹ = D.uv := by
        calc D.t * D.uv * D.t⁻¹ = D.uv * D.t * D.t⁻¹ := by rw [← D.uv_comm_t]
          _ = D.uv * (D.t * D.t⁻¹) := by group
          _ = D.uv := by rw [mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.subset_closure (by simp)
    · have : D.t * D.t * D.t⁻¹ = D.t := by
        calc D.t * D.t * D.t⁻¹ = 1 * D.t⁻¹ := by rw [D.t_sq]
          _ = D.t⁻¹ := by group
          _ = D.t := ht_inv
      rw [this]
      exact Subgroup.subset_closure (by simp)
  ·
    refine mem_normalizer_closure_pair_of_conj_mem ?_ ?_
    · have : D.u * D.uv * D.u⁻¹ = D.uv := by
        calc D.u * D.uv * D.u⁻¹ = D.uv * D.u * D.u⁻¹ := by rw [← D.uv_comm_u]
          _ = D.uv * (D.u * D.u⁻¹) := by group
          _ = D.uv := by rw [mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.subset_closure (by simp)
    · have h : D.u * D.t = D.uv * D.t * D.u⁻¹ := by
        calc D.u * D.t = D.u * (D.t * D.u) * D.u⁻¹ := by group
          _ = D.u * (D.u * D.uv * D.t) * D.u⁻¹ := by rw [D.t_u]
          _ = (D.u * D.u) * D.uv * D.t * D.u⁻¹ := by group
          _ = D.uv * D.t * D.u⁻¹ := by simp [D.u_sq, mul_assoc]
      have hres : D.u * D.t * D.u⁻¹ = D.uv * D.t := by
        calc D.u * D.t * D.u⁻¹ = (D.uv * D.t * D.u⁻¹) * D.u⁻¹ := by rw [h]
          _ = D.uv * D.t := by simp [hu_inv, D.u_sq, mul_assoc]
      rw [hres]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  ·
    have hmem : D.ρ⁻¹ ∈
        Subgroup.normalizer (Subgroup.closure ({D.uv, D.t} : Set S)) := by
      refine mem_normalizer_closure_pair_of_conj_mem ?_ ?_
      · have h : D.ρ⁻¹ * D.uv * (D.ρ⁻¹)⁻¹ = D.t := by
          rw [inv_inv]
          calc D.ρ⁻¹ * D.uv * D.ρ = D.ρ⁻¹ * (D.uv * D.ρ) := by group
            _ = D.ρ⁻¹ * (D.ρ * D.t) := by rw [D.uv_rho]
            _ = D.t := by group
        rw [h]
        exact Subgroup.subset_closure (by simp)
      · have h : D.ρ⁻¹ * D.t * (D.ρ⁻¹)⁻¹ = D.uv * D.t := by
          rw [inv_inv]
          calc D.ρ⁻¹ * D.t * D.ρ = D.ρ⁻¹ * (D.t * D.ρ) := by group
            _ = D.ρ⁻¹ * (D.ρ * D.uv * D.t) := by rw [D.t_rho]
            _ = D.uv * D.t := by group
        rw [h]
        exact Subgroup.mul_mem _
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    simpa using Subgroup.inv_mem _ hmem


theorem Subgroup.inv_mem_of_map_le {S : Type*} [Group S] [Finite S]
    {H : Subgroup S} {φ : MulAut S} (h : ∀ x ∈ H, φ x ∈ H) :
    ∀ x ∈ H, φ⁻¹ x ∈ H := by
  have hmap : H.map φ.toMonoidHom ≤ H := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    exact h x hx
  have hcard : Nat.card H ≤ Nat.card (H.map φ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective φ.injective]
  have hEq : H.map φ.toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hmap hcard
  intro x hx
  have hxmap : x ∈ H.map φ.toMonoidHom := by rw [hEq]; exact hx
  rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
  rw [← hyx]
  simpa using hy


theorem index_le_four_of_minimal_general (X : StrothAmbient G) (Z : StrothDatum X)
    (C : Subgroup G)
    (hDC : Z.D ≤ C) (hCR : C ≤ strothR X Z.D)
    (hmin : IsMinimalLModuleMod Z.dataD C) :
    (Z.D.subgroupOf C).index ≤ 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hCN : C ≤ Subgroup.normalizer (Z.D : Set G) :=
    hCR.trans (strothR_le_normalizer X Z.D)
  haveI hN : (Z.D.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hCN
  let Q := C ⧸ Z.D.subgroupOf C
  have hLD : ∀ l ∈ Z.dataD.L, l ∈ Subgroup.normalizer (Z.D : Set G) := by
    intro l hl
    rw [Z.hL] at hl
    exact Z.L_le_normalizer hl
  have hLinf : Z.dataD.L ≤
      (Subgroup.normalizer (C : Set G) ⊓ Subgroup.normalizer (Z.D : Set G) : Subgroup G) := by
    intro l hl
    exact ⟨hmin.le_normalizer hl, hLD l hl⟩
  let ψ : Z.dataD.L →* MulAut Q :=
    (conjAutQuotientHomC (S := G) (B := Z.D) (C := C)).comp (Subgroup.inclusion hLinf)
  have hEA : IsElementaryAbelian 2 Q :=
    isElementaryAbelian_quotient_of_minimal hDC hCR hmin hLD
  haveI hEA' : IsElementaryAbelian 2 Q := hEA
  have hQp : IsPGroup 2 Q := hEA.isPGroup 2 Q
  have hQne : Z.D.subgroupOf C ≠ ⊤ := by
    intro htop
    exact not_le_of_gt hmin.d_lt (Subgroup.subgroupOf_eq_top.mp htop)
  haveI hQnt : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hQne
  let P : Subgroup G := Subgroup.closure ({Z.dataD.uv, Z.dataD.t} : Set G)
  have hPL : P ≤ Z.dataD.L := by
    rw [show P = Subgroup.closure ({Z.dataD.uv, Z.dataD.t} : Set G) from rfl,
      Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Z.dataD.uv_mem_L
    · exact Z.dataD.t_mem_L
  have hPnorm : Z.dataD.L ≤ Subgroup.normalizer P :=
    Z.dataD.L_le_normalizer_closure_uv_t
  have hcomm : Subgroup.zpowers Z.dataD.t ≤
      Subgroup.centralizer (Subgroup.zpowers Z.dataD.uv : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ Subgroup.zpowers Z.dataD.t at hy
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨n, rfl⟩ := hy
    exact (Commute.zpow_left (show Commute Z.dataD.t Z.dataD.uv from Z.dataD.uv_comm_t.symm) n).eq
  have hEAuv : IsElementaryAbelian 2 (Subgroup.zpowers Z.dataD.uv) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (by
      simpa [pow_two] using Z.dataD.uv_sq)
  have hEAt : IsElementaryAbelian 2 (Subgroup.zpowers Z.dataD.t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (by
      simpa [pow_two] using Z.dataD.t_sq)
  have hEAP : IsElementaryAbelian 2
      (show Subgroup G from Subgroup.zpowers Z.dataD.uv ⊔ Subgroup.zpowers Z.dataD.t) :=
    IsElementaryAbelian.sup_of_le_centralizer hcomm
  have hP_eq : P =
      (show Subgroup G from Subgroup.zpowers Z.dataD.uv ⊔ Subgroup.zpowers Z.dataD.t) := by
    rw [show P = Subgroup.closure ({Z.dataD.uv, Z.dataD.t} : Set G) from rfl,
      Subgroup.zpowers_eq_closure Z.dataD.uv, Subgroup.zpowers_eq_closure Z.dataD.t,
      ← Subgroup.closure_union]
    congr 1
  have hEAP' : IsElementaryAbelian 2 P := hP_eq ▸ hEAP
  have hPp : IsPGroup 2 P := hEAP'.isPGroup 2 P
  let ψP : P →* MulAut Q := ψ.comp (Subgroup.inclusion hPL)
  letI : MulDistribMulAction P Q := MulDistribMulAction.compHom Q ψP
  let FixP : Subgroup Q := fixedSubgroup P Q
  have hdvd : 2 ∣ Nat.card Q := by
    rcases hQp.card_eq_or_dvd with h1 | h2
    · exfalso
      have hsub : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp h1).1
      exact not_subsingleton_iff_nontrivial.mpr ‹Nontrivial Q› hsub
    · exact h2
  have hFix_ne : FixP ≠ ⊥ := by
    obtain ⟨q, hq, hqne⟩ :=
      hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point Q hdvd
        (a := 1) (by simp [MulAction.mem_fixedPoints])
    intro hbot
    have hqbot : q ∈ (⊥ : Subgroup Q) := by rw [← hbot]; exact hq
    exact hqne.symm (by simpa using hqbot)
  have hFix_inv : ∀ (l : G) (hl : l ∈ Z.dataD.L) (r : Q), r ∈ FixP →
      conjAutQuotientC l (hmin.le_normalizer hl) (hLD l hl) r ∈ FixP := by
    intro l hl r hr
    change ψ ⟨l, hl⟩ r ∈ FixP
    rw [mem_fixedSubgroup] at hr ⊢
    intro p
    have hconjP : l⁻¹ * (p : G) * l ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hPnorm (Z.dataD.L.inv_mem hl)) (p : G)).mp p.2
      simpa [mul_assoc] using this
    have hprod : (⟨(p : G), hPL p.2⟩ : Z.dataD.L) * ⟨l, hl⟩ =
        ⟨l, hl⟩ * ⟨l⁻¹ * (p : G) * l, hPL hconjP⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      group
    calc ψP p (ψ ⟨l, hl⟩ r)
        = ψ ⟨(p : G), hPL p.2⟩ (ψ ⟨l, hl⟩ r) := rfl
      _ = ψ (⟨(p : G), hPL p.2⟩ * ⟨l, hl⟩) r := by rw [map_mul]; rfl
      _ = ψ (⟨l, hl⟩ * ⟨l⁻¹ * (p : G) * l, hPL hconjP⟩) r := by rw [hprod]
      _ = ψ ⟨l, hl⟩ (ψ ⟨l⁻¹ * (p : G) * l, hPL hconjP⟩ r) := by rw [map_mul]; rfl
      _ = ψ ⟨l, hl⟩ r := by
          rw [show ψ ⟨l⁻¹ * (p : G) * l, hPL hconjP⟩ r = r from
            hr ⟨l⁻¹ * (p : G) * l, hconjP⟩]
  have hFix_top : FixP = ⊤ := by
    rcases conjAutQuotient_eq_bot_or_top (Z := Z) (C := C) hDC hmin hLD FixP hFix_inv with
      hbot | htop
    · exact absurd hbot hFix_ne
    · exact htop
  have huv_triv : ∀ (h : Z.dataD.uv ∈ Z.dataD.L),
      ψ ⟨Z.dataD.uv, h⟩ = 1 := by
    intro h
    apply MulEquiv.ext
    intro q
    have hq : q ∈ FixP := by rw [hFix_top]; exact Subgroup.mem_top q
    rw [mem_fixedSubgroup] at hq
    have hp : (ψP ⟨Z.dataD.uv, Subgroup.subset_closure (by simp)⟩) q = q := hq _
    show ψ ⟨Z.dataD.uv, h⟩ q = q
    convert hp using 2
    rfl
  have ht_triv : ∀ (h : Z.dataD.t ∈ Z.dataD.L),
      ψ ⟨Z.dataD.t, h⟩ = 1 := by
    intro h
    apply MulEquiv.ext
    intro q
    have hq : q ∈ FixP := by rw [hFix_top]; exact Subgroup.mem_top q
    rw [mem_fixedSubgroup] at hq
    have hp : (ψP ⟨Z.dataD.t, Subgroup.subset_closure (by simp)⟩) q = q := hq _
    show ψ ⟨Z.dataD.t, h⟩ q = q
    convert hp using 2
    rfl
  have hQcenter : Subgroup.center Q = ⊤ :=
    Subgroup.center_eq_top_iff.mpr hEA.toIsMulCommutative
  letI : CommGroup Q := Group.commGroupOfCenterEqTop hQcenter
  let V := Additive Q
  let toAddEquiv (f : MulAut Q) : V ≃+ V :=
    { toFun := fun x => Additive.ofMul (f (Additive.toMul x))
      invFun := fun x => Additive.ofMul (f.symm (Additive.toMul x))
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by
        intro x y
        change Additive.ofMul (f (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul (f (Additive.toMul x)) + Additive.ofMul (f (Additive.toMul y))
        rw [map_mul]
        rfl }
  haveI : NeZero 2 := ⟨by decide⟩
  have zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
    intro c
    have hval : c.val = 0 ∨ c.val = 1 := by
      have := ZMod.val_lt (n := 2) c
      omega
    rcases hval with h0 | h1
    · left; rw [← ZMod.natCast_zmod_val c, h0]; simp
    · right; rw [← ZMod.natCast_zmod_val c, h1]; simp
  let toLin (f : MulAut Q) : V ≃ₗ[ZMod 2] V :=
    (toAddEquiv f).toLinearEquiv (by
      intro c x
      rcases zmod2_cases c with rfl | rfl <;> simp [toAddEquiv])
  have toLin_one : toLin (1 : MulAut Q) = 1 := by
    apply LinearEquiv.ext
    intro x
    simp [toLin, toAddEquiv]
  have toLin_mul (f g : MulAut Q) : toLin (f * g) = toLin f * toLin g := by
    apply LinearEquiv.ext
    intro x
    simp [toLin, toAddEquiv, MulAut.mul_apply, mul_assoc]
  have toLin_inv (f : MulAut Q) : toLin f⁻¹ = (toLin f)⁻¹ := by
    apply LinearEquiv.ext
    intro x
    simp [toLin, toAddEquiv]
  let U : V ≃ₗ[ZMod 2] V := toLin (ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩)
  let R : V ≃ₗ[ZMod 2] V := toLin (ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩)
  have hU2 : ∀ v, U (U v) = v := by
    intro v
    have hu2' : (⟨Z.dataD.u, Z.dataD.u_mem_L⟩ : Z.dataD.L) *
        ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ = 1 := by
      apply Subtype.ext
      simpa using Z.dataD.u_sq
    have hu2 : ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ *
        ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ = 1 := by
      rw [← map_mul, hu2', map_one]
    change (toLin (ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩) *
      toLin (ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩)) v = v
    rw [← toLin_mul, hu2, toLin_one]
    rfl
  have hρ3N : Z.dataD.ρ ^ 3 ∈ Subgroup.normalizer (C : Set G) :=
    Subgroup.pow_mem _ (hmin.le_normalizer Z.dataD.ρ_mem_L) 3
  have hρ3C : Z.dataD.ρ ^ 3 ∈ Subgroup.centralizer (Z.D : Set G) :=
    Z.dataD.rho_cube_mem
  have hρ3_comm : ∀ c : C,
      (((⟨Z.dataD.ρ ^ 3 * (c : G) * (Z.dataD.ρ ^ 3)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hρ3N (c : G)).mp c.2⟩ : C)⁻¹ * c : C) : G) ∈ Z.D := by
    intro c
    let y : C := (⟨Z.dataD.ρ ^ 3 * (c : G) * (Z.dataD.ρ ^ 3)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hρ3N (c : G)).mp c.2⟩ : C)⁻¹ * c
    change (y : G) ∈ Z.D
    have hx_d_all : ∀ d ∈ Z.D, Z.dataD.ρ ^ 3 * d * (Z.dataD.ρ ^ 3)⁻¹ = d := by
      intro d hd
      have h := hρ3C
      rw [Subgroup.mem_centralizer_iff] at h
      rw [← h d hd]
      group
    have hy_central : (y : G) ∈ Subgroup.centralizer (Z.D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hx_d := hx_d_all d hd
      have hd' : (c : G) * d * (c : G)⁻¹ ∈ Z.D :=
        (Subgroup.mem_normalizer_iff.mp (hCN c.2) d).mp hd
      have hx_d' : (Z.dataD.ρ ^ 3)⁻¹ * ((c : G) * d * (c : G)⁻¹) *
          Z.dataD.ρ ^ 3 = (c : G) * d * (c : G)⁻¹ := by
        calc (Z.dataD.ρ ^ 3)⁻¹ * ((c : G) * d * (c : G)⁻¹) * Z.dataD.ρ ^ 3
            = (Z.dataD.ρ ^ 3)⁻¹ *
                (Z.dataD.ρ ^ 3 * ((c : G) * d * (c : G)⁻¹) * (Z.dataD.ρ ^ 3)⁻¹) *
                Z.dataD.ρ ^ 3 := by
              rw [hx_d_all ((c : G) * d * (c : G)⁻¹) hd']
          _ = (c : G) * d * (c : G)⁻¹ := by group
      have hyconj : (y : G) * d * (y : G)⁻¹ = d := by
        change ((Z.dataD.ρ ^ 3 * (c : G) * (Z.dataD.ρ ^ 3)⁻¹)⁻¹ * (c : G)) * d *
            ((Z.dataD.ρ ^ 3 * (c : G) * (Z.dataD.ρ ^ 3)⁻¹)⁻¹ * (c : G))⁻¹ = d
        calc
          (Z.dataD.ρ ^ 3 * (c : G) * (Z.dataD.ρ ^ 3)⁻¹)⁻¹ * (c : G) * d *
              ((Z.dataD.ρ ^ 3 * (c : G) * (Z.dataD.ρ ^ 3)⁻¹)⁻¹ * (c : G))⁻¹
            = Z.dataD.ρ ^ 3 * (c : G)⁻¹ *
                ((Z.dataD.ρ ^ 3)⁻¹ * ((c : G) * d * (c : G)⁻¹) *
                  Z.dataD.ρ ^ 3) * (c : G) * (Z.dataD.ρ ^ 3)⁻¹ := by group
          _ = Z.dataD.ρ ^ 3 * (c : G)⁻¹ * ((c : G) * d * (c : G)⁻¹) *
                (c : G) * (Z.dataD.ρ ^ 3)⁻¹ := by rw [hx_d']
          _ = Z.dataD.ρ ^ 3 * d * (Z.dataD.ρ ^ 3)⁻¹ := by group
          _ = d := hx_d
      calc d * (y : G) = ((y : G) * d * (y : G)⁻¹) * (y : G) := by rw [hyconj]
        _ = (y : G) * d := by group
    have hyS : (y : G) ∈ (X.S : Subgroup G) :=
      le_sylow_of_le_strothR hCR y.2
    have hyCentIn : (y : G) ∈ Z.centralizerIn := ⟨hyS, hy_central⟩
    rwa [Z.centralizerIn_eq] at hyCentIn
  have hρ3act : conjAutQuotientC Z.dataD.ρ
      (hmin.le_normalizer Z.dataD.ρ_mem_L)
      (hLD Z.dataD.ρ Z.dataD.ρ_mem_L) ^ 3 = 1 := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      rw [pow_three, MulAut.mul_apply, MulAut.mul_apply]
      rw [conjAutQuotientC_apply_mk, conjAutQuotientC_apply_mk,
        conjAutQuotientC_apply_mk]
      refine (QuotientGroup.eq).mpr ?_
      rw [Subgroup.mem_subgroupOf]
      have htriple :
          conjOnSubgroupC Z.dataD.ρ (hmin.le_normalizer Z.dataD.ρ_mem_L)
            (conjOnSubgroupC Z.dataD.ρ (hmin.le_normalizer Z.dataD.ρ_mem_L)
              (conjOnSubgroupC Z.dataD.ρ (hmin.le_normalizer Z.dataD.ρ_mem_L) c)) =
          ⟨Z.dataD.ρ ^ 3 * (c : G) * (Z.dataD.ρ ^ 3)⁻¹,
            (Subgroup.mem_normalizer_iff.mp hρ3N (c : G)).mp c.2⟩ := by
        ext
        simp only [conjOnSubgroupC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
        rw [pow_three]
        group
      rw [htriple]
      exact hρ3_comm c
  have hR3 : ∀ v, R (R (R v)) = v := by
    intro v
    have hr3 : ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩ *
        ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩ *
        ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩ = 1 := by
      have h := hρ3act
      change (ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩ : MulAut Q) ^ 3 = 1 at h
      rwa [pow_three] at h
    change ((toLin (ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩) *
      toLin (ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩)) *
      toLin (ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩)) v = v
    rw [← toLin_mul, ← toLin_mul, hr3, toLin_one]
    rfl
  have hrel : ∀ v, R (U v) = U (R.symm v) := by
    intro v
    let A : MulAut Q := ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩
    let B : MulAut Q := ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩
    have h1 : A * B * A * B = 1 := by
      calc A * B * A * B
          = ψ (⟨Z.dataD.u, Z.dataD.u_mem_L⟩ * ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩ *
              ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ * ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩) := by
            rw [show A = ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ from rfl,
              show B = ψ ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩ from rfl]
            rw [← map_mul, ← map_mul, ← map_mul]
        _ = 1 := by
            rw [show (⟨Z.dataD.u, Z.dataD.u_mem_L⟩ * ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩ *
              ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ * ⟨Z.dataD.ρ, Z.dataD.ρ_mem_L⟩ : Z.dataD.L) = 1 from
              Subtype.ext Z.dataD.u_rho, map_one]
    have h1' : A * B * A = B⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hA2 : A * A = 1 := by
      change ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ * ψ ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ = 1
      rw [← map_mul]
      rw [show (⟨Z.dataD.u, Z.dataD.u_mem_L⟩ * ⟨Z.dataD.u, Z.dataD.u_mem_L⟩ : Z.dataD.L) = 1 from by
        apply Subtype.ext
        simpa using Z.dataD.u_sq, map_one]
    have hrelMul : B * A = A * B⁻¹ := by
      calc B * A = (A * A) * B * A := by rw [hA2]; group
        _ = A * (A * B * A) := by group
        _ = A * B⁻¹ := by rw [h1']
    change (toLin B * toLin A) v = (toLin A * (toLin B)⁻¹) v
    rw [← toLin_mul B A, ← toLin_inv B, ← toLin_mul A B⁻¹, hrelMul]
  have hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ x ∈ W, U x ∈ W) → (∀ x ∈ W, R x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hU hR
    let H : Subgroup Q :=
      { carrier := { q | Additive.ofMul q ∈ W }
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          change Additive.ofMul (a * b) ∈ W
          change Additive.ofMul a + Additive.ofMul b ∈ W
          exact W.add_mem ha hb
        inv_mem' := by
          intro a ha
          change Additive.ofMul a⁻¹ ∈ W
          change -Additive.ofMul a ∈ W
          exact W.neg_mem ha }
    have hHinv : ∀ (l : G) (hl : l ∈ Z.dataD.L) (r : Q), r ∈ H →
        conjAutQuotientC l (hmin.le_normalizer hl) (hLD l hl) r ∈ H := by
      intro l hl
      change ∀ r ∈ H, ψ ⟨l, hl⟩ r ∈ H
      refine Subgroup.closure_induction
        (k := ({Z.dataD.uv, Z.dataD.t, Z.dataD.u, Z.dataD.ρ} : Set G))
        (p := fun l hl' => ∀ r ∈ H, ψ ⟨l, hl'⟩ r ∈ H) ?_ ?_ ?_ ?_ hl
      · intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · intro r hr
          have h1 : ∀ (h : Z.dataD.uv ∈ Z.dataD.L), (ψ ⟨Z.dataD.uv, h⟩) r = r := by
            intro h
            rw [huv_triv h]
            rfl
          rw [h1 (Subgroup.subset_closure (by simp))]
          exact hr
        · intro r hr
          have h1 : ∀ (h : Z.dataD.t ∈ Z.dataD.L), (ψ ⟨Z.dataD.t, h⟩) r = r := by
            intro h
            rw [ht_triv h]
            rfl
          rw [h1 (Subgroup.subset_closure (by simp))]
          exact hr
        · intro r hr
          change Additive.ofMul r ∈ W at hr
          have hUmem : U (Additive.ofMul r) ∈ W := hU _ hr
          change Additive.ofMul (ψ ⟨Z.dataD.u, _⟩ r) ∈ W
          simpa [U, toLin, toAddEquiv] using hUmem
        · intro r hr
          change Additive.ofMul r ∈ W at hr
          have hRmem : R (Additive.ofMul r) ∈ W := hR _ hr
          change Additive.ofMul (ψ ⟨Z.dataD.ρ, _⟩ r) ∈ W
          simpa [R, toLin, toAddEquiv] using hRmem
      · intro r hr
        have h1 : (ψ ⟨(1 : G), _⟩ : MulAut Q) = 1 := map_one ψ
        rw [show (ψ ⟨(1 : G), _⟩) r = r from congrArg (fun f : MulAut Q => f r) h1]
        exact hr
      · intro g h hgL hhL hg hh r hr
        have hprod : (⟨g, hgL⟩ : Z.dataD.L) * ⟨h, hhL⟩ =
            ⟨g * h, Subgroup.mul_mem _ hgL hhL⟩ := rfl
        rw [← hprod, map_mul]
        simpa [MulAut.mul_apply] using hg _ (hh _ hr)
      · intro g hgL hg r hr
        have hinv : (⟨g, hgL⟩ : Z.dataD.L)⁻¹ =
            ⟨g⁻¹, Subgroup.inv_mem _ hgL⟩ := rfl
        rw [← hinv, map_inv]
        exact Subgroup.inv_mem_of_map_le (H := H) hg r hr
    have hH := conjAutQuotient_eq_bot_or_top (Z := Z) (C := C) hDC hmin hLD H hHinv
    rcases hH with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hxH : Additive.toMul x ∈ H := by
        change Additive.ofMul (Additive.toMul x) ∈ W
        simpa using hx
      rw [hbot] at hxH
      have hx1 : Additive.toMul x = 1 := by simpa using hxH
      simpa [hx1]
    · right
      rw [Submodule.eq_top_iff']
      intro x
      have hxH : Additive.toMul x ∈ H := by rw [htop]; exact Subgroup.mem_top _
      change Additive.ofMul (Additive.toMul x) ∈ W at hxH
      simpa using hxH
  have hfinrank : Module.finrank (ZMod 2) V ≤ 2 :=
    finrank_le_two_of_sigmaThree U R hU2 hR3 hrel hirr
  have hcardQ : Nat.card Q ≤ 4 := by
    have hVcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have hVle : Nat.card V ≤ 4 := by
      rw [hVcard]
      calc 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ 2 :=
            Nat.pow_le_pow_right (by norm_num) hfinrank
        _ = 4 := by norm_num
    rwa [Nat.card_congr Additive.toMul] at hVle
  rw [Subgroup.index_eq_card]
  exact hcardQ

theorem index_le_four_of_minimal (X : StrothAmbient G) {m : ℕ} (Z : StrothDatum X)
    (hτ : Z.τ = StrothTypeIndex.t100 m) (C : Subgroup G)
    (hDC : Z.D ≤ C) (hCR : C ≤ strothR X Z.D)
    (hmin : IsMinimalLModuleMod Z.dataD C) :
    (Z.D.subgroupOf C).index ≤ 4 :=
  index_le_four_of_minimal_general X Z C hDC hCR hmin

end CFSG.CGT.Stroth77
