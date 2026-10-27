module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise commutatorElement


theorem exists_pow_two_of_two_dvd_isPrimePow {q : ℕ} (h2 : 2 ∣ q) (hq : IsPrimePow q) :
    ∃ e, 0 < e ∧ q = 2 ^ e := by
  obtain ⟨r, e, hr, he, hq⟩ := (isPrimePow_nat_iff q).1 hq
  have h2r : 2 ∣ r := Nat.prime_two.dvd_of_dvd_pow (hq ▸ h2)
  have hr2 : r = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 h2r).symm
  exact ⟨e, he, hq.symm.trans (by rw [hr2])⟩

theorem pow_eq_two_of_two_dvd_of_lt_four {q s : ℕ} (h2 : 2 ∣ q) (hq : IsPrimePow q)
    (hs : 0 < s) (hQ : q ^ s < 4) : q ^ s = 2 := by
  obtain ⟨e, he, rfl⟩ := exists_pow_two_of_two_dvd_isPrimePow h2 hq
  rw [← pow_mul] at hQ ⊢
  have hpos : 0 < e * s := Nat.mul_pos he hs
  have hlt : 2 ^ (e * s) < 2 ^ 2 := by norm_num at hQ ⊢; exact hQ
  have h1 : e * s < 2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
  have h2' : e * s = 1 := by omega
  rw [h2']
  norm_num

theorem card_fixSubfield_eq_two {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {σ : L ≃+* L} {Q : ℕ} (hσ : ∀ c, σ c = c ^ Q) (hQ : Q = 2) :
    Nat.card ↥(fixSubfield σ) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ 2 = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ, hQ]
    rfl
  obtain ⟨-, hcard⟩ := ncard_pow_eq_self (L := L) 2 1 (by norm_num)
  have h1 : Nat.card ↥(fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
    Nat.card_coe_set_eq (fixSubfield σ : Set L)
  rw [h1, hset]
  simpa using hcard

theorem isPerfect_CQ_of_isPerfect_componentRootSpan {τ : Tag} {L : Type} [Field L]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (σ : L ≃+* L)
    (hperf : Group.IsPerfect ↥(componentRootSpan ↥(fixSubfield σ) χ i)) :
    Group.IsPerfect ↥(CQ σ i) := by
  rw [CQ_eq_map]
  haveI := hperf
  let e := Subgroup.equivMapOfInjective (componentRootSpan ↥(fixSubfield σ) χ i)
    (baseChangeGL (fixSubfield σ).subtype) (baseChangeGL_injective (fixSubfield σ).subtype)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

private theorem false_of_rankOne {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {σ : L ≃+* L} {z : ModGL τ L}
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hK2 : Nat.card ↥(fixSubfield σ) = 2)
    (hrank : ∀ α ∈ componentRoots (rootCharHom a) i,
      ∀ δ ∈ componentRoots (rootCharHom a) i, δ = α ∨ δ = -α) : False := by
  classical
  haveI hfinK : Finite ↥(fixSubfield σ) := Nat.finite_of_card_ne_zero (by omega)
  have hKle : Nat.card ↥(fixSubfield σ) ≤ 3 := by omega
  haveI : Group.IsSolvable ↥(componentRootSpan ↥(fixSubfield σ) (rootCharHom a) i) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_componentRootSpan_of_rank_one
      hKle i hrank
  have hsL := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_unit_sq_ne_one_alg (L := L)
  obtain ⟨f, hf1, -, -⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  haveI : Group.IsSolvable ↥(f.range) := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hsolvR : Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hf1)
  haveI : Nontrivial (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := hQS.2.1.toNontrivial
  haveI : Nontrivial ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (QuotientGroup.mk'_surjective (Subgroup.center _)).nontrivial
  haveI : Group.IsPerfect ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := hQS.1
  exact (Group.IsPerfect.not_isSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) hsolvR

theorem exists_mulEquiv_alternating_of_b2Block {K : Type} [Field K]
    (hK2 : ∀ x : K, x = 0 ∨ x = 1)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) {s l : Fin Tag.F4.rank → ℤ}
    (hss : CFSG.LieType.Steinberg.Adjoint.iform s s = 2)
    (hll : CFSG.LieType.Steinberg.Adjoint.iform l l = 4)
    (hsl : CFSG.LieType.Steinberg.Adjoint.iform s l = -2)
    (hΨ : componentRoots χ i = {s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)}) :
    Nonempty (↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ ≃*
      alternatingGroup (Fin 6)) := by
  classical
  have h2 : (2 : K) = 0 := by
    rcases hK2 (1 + 1) with h | h
    · rwa [one_add_one_eq_two] at h
    · exact absurd (by linear_combination h : (1 : K) = 0) one_ne_zero
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hΨc := isRootComponent_componentRoots (χ := χ) i
  have hs : IsRoot .F4 s := hΨc.isRoot s (by rw [hΨ]; simp)
  have hl : IsRoot .F4 l := hΨc.isRoot l (by rw [hΨ]; simp)
  have hrel := b2Rel_F4 (K := K) hs hl hss hll hsl
  obtain ⟨-, hb, -⟩ := f4_commutator_mixed hs hl hss hll hsl
  set S := componentRootSpan K χ i with hSdef
  have hSgen : S = Subgroup.closure ({xr K s, xr K (-s), xr K l, xr K (-l), xr K (s + l),
      xr K (-(s + l)), xr K (2 • s + l), xr K (-(2 • s + l))} : Set (ModGL Tag.F4 K)) := by
    apply le_antisymm
    · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rcases hK2 c with rfl | rfl
      · rw [pinnedX_zero]
        exact one_mem _
      · apply Subgroup.subset_closure
        have hα' : α ∈ ({s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)} :
            Set (Fin Tag.F4.rank → ℤ)) := hΨ ▸ hα
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα' ⊢
        rcases hα' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [xr]
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      have hmem : ∀ γ : Fin Tag.F4.rank → ℤ, γ ∈ ({s, -s, l, -l, s + l, -(s + l), 2 • s + l,
          -(2 • s + l)} : Set (Fin Tag.F4.rank → ℤ)) → γ ∈ componentRoots χ i :=
        fun γ h => hΨ ▸ h
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact pinnedX_mem_rootSpan (hmem _ (by simp)) 1
  have hcox := b2_isCoxeterA hrel
  have h01 : b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l)) (xr K (s + l)) (xr K (-(s + l)))
      (xr K (2 • s + l)) (xr K (-(2 • s + l))) 0 ≠
      b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l)) (xr K (s + l)) (xr K (-(s + l)))
        (xr K (2 • s + l)) (xr K (-(2 • s + l))) 1 :=
    fun h => xr_ne_xr_neg hb (by simpa [b2t] using h.symm)
  obtain ⟨e, -⟩ := exists_mulEquiv_closure_five hcox h01
  have hS : S = Subgroup.closure (b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l))
      (xr K (s + l)) (xr K (-(s + l))) (xr K (2 • s + l)) (xr K (-(2 • s + l))) ''
      Set.Iio 5) := hSgen.trans (b2_closure_eq hrel)
  let Φ : ↥S ≃* Equiv.Perm (Fin 6) := (MulEquiv.subgroupCongr hS).trans e.symm
  have hle : ⁅S, S⁆ ≤ S := Subgroup.commutator_le_self S
  have himg := CFSG.LargeExtraspecial.S45Q.img_commutator Φ
  exact ⟨(CFSG.LargeExtraspecial.S45Q.imgEquiv Φ hle).trans (MulEquiv.subgroupCongr himg)⟩

theorem b2Block_derived_card_center {K : Type} [Field K]
    (hK2 : ∀ x : K, x = 0 ∨ x = 1)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) {s l : Fin Tag.F4.rank → ℤ}
    (hss : CFSG.LieType.Steinberg.Adjoint.iform s s = 2)
    (hll : CFSG.LieType.Steinberg.Adjoint.iform l l = 4)
    (hsl : CFSG.LieType.Steinberg.Adjoint.iform s l = -2)
    (hΨ : componentRoots χ i = {s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)}) :
    Nat.card ↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = 360 ∧
      Subgroup.center ↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = ⊥ ∧
      Group.IsPerfect ↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  obtain ⟨ψ⟩ := exists_mulEquiv_alternating_of_b2Block hK2 i hss hll hsl hΨ
  have hcard : Nat.card ↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = 360 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.LargeExtraspecial.S45Q.card_alternatingGroup_six]
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hperf : Group.IsPerfect ↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :=
    Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  refine ⟨hcard, ?_, hperf⟩
  have hmap := Subgroup.map_center_eq ψ
  rw [alternatingGroup.center_eq_bot (by simp)] at hmap
  rw [Subgroup.map_eq_bot_iff] at hmap
  have hker : (ψ : ↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ →*
      alternatingGroup (Fin 6)).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    exact ψ.injective
  rw [hker] at hmap
  exact le_bot_iff.1 hmap

private theorem false_of_b2Block {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup Tag.F4 L p) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {σ : L ≃+* L} {z : ModGL Tag.F4 L}
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL Tag.F4 L,
      g ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (h360 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 360)
    (hK2 : Nat.card ↥(fixSubfield σ) = 2)
    {s' l : Fin Tag.F4.rank → ℤ}
    (hss : CFSG.LieType.Steinberg.Adjoint.iform s' s' = 2)
    (hll : CFSG.LieType.Steinberg.Adjoint.iform l l = 4)
    (hsl : CFSG.LieType.Steinberg.Adjoint.iform s' l = -2)
    (hΨ : componentRoots (rootCharHom a) i =
      {s', -s', l, -l, s' + l, -(s' + l), 2 • s' + l, -(2 • s' + l)}) : False := by
  classical
  haveI hfinK : Finite ↥(fixSubfield σ) := Nat.finite_of_card_ne_zero (by omega)
  have hK2' : ∀ x : ↥(fixSubfield σ), x = 0 ∨ x = 1 := eq_zero_or_one_of_card_two hK2
  obtain ⟨hcardD, hcenterD, hperfD⟩ := b2Block_derived_card_center hK2' i hss hll hsl hΨ
  set C := componentRootSpan ↥(fixSubfield σ) (rootCharHom a) i with hC
  set D := ⁅C, C⁆ with hD
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hperfD
  have hsL := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_unit_sq_ne_one_alg (L := L)
  have hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1 := by
    intro d hd hd0
    let : Fintype ↥(fixSubfield σ) := Fintype.ofFinite _
    have hcard : Fintype.card ↥(fixSubfield σ) = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hK2
    have hdK : d ∈ fixSubfield σ := hd
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨d, hdK⟩ : ↥(fixSubfield σ))
      (fun h => hd0 (congrArg Subtype.val h))
    rw [hcard] at h1
    simpa using congrArg Subtype.val h1
  have hY : ∀ g g' : ModGL Tag.F4 L, g ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) →
      frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g, g'⁆ ∈ D.map (baseChangeGL (fixSubfield σ).subtype) := by
    intro g g' hg hg' hgZ hgZ'
    have := orbit_commutator_mem_commutator_CQT S hT i hs hmin σ hsL hF hg hg' hgZ hgZ'
    rwa [CQ_eq_map, ← Subgroup.map_commutator] at this
  obtain ⟨f, hf1, hker, hf2⟩ := rationalComponent_eq_rangeT S hT i hs hmin σ z hnorm hz
    D (Subgroup.commutator_le_self C) hY
  have hRf : rationalComponent S.ρ S.Γ (rootCharHom a) i = f.range :=
    le_antisymm hf1 (hf2 hDperf)
  have hkerf : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact hcenterD ▸ hker hx
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hkerf
  have hcardRi : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = 360 := by
    rw [hRf]
    change Nat.card ↥(Set.range f) = 360
    rw [Nat.card_range_of_injective hinj, hcardD]
  have hcenterRi : Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ := by
    let e : ↥D ≃* ↥(f.range) := MonoidHom.ofInjective hinj
    have hmap := Subgroup.map_center_eq (e.trans (MulEquiv.subgroupCongr hRf.symm))
    rw [hcenterD, Subgroup.map_bot] at hmap
    exact hmap.symm
  have h360eq : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 360 := by
    rw [hcenterRi, Nat.card_congr (QuotientGroup.quotientBot).toEquiv]
    exact hcardRi
  exact h360 h360eq

theorem isPerfect_CQ_of_inner_small {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {σ : L ≃+* L} {z : ModGL τ L}
    (hσ : ∀ c, σ c = c ^ (S.D.q ^ s))
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hG2 : τ = .G2 → 4 ≤ S.D.q)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (h360 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 360)
    (hQ : S.D.q ^ s < 4) : Group.IsPerfect ↥(CQ σ i) := by
  classical
  have h2dvd : 2 ∣ S.D.q := (CharP.cast_eq_zero_iff L 2 S.D.q).1 S.hqpow.2
  have hqs : S.D.q ^ s = 2 := pow_eq_two_of_two_dvd_of_lt_four h2dvd S.hqpow.1
    (NeZero.pos s) hQ
  have hK2 : Nat.card ↥(fixSubfield σ) = 2 := card_fixSubfield_eq_two hσ hqs
  haveI hfinK : Finite ↥(fixSubfield σ) := Nat.finite_of_card_ne_zero (by omega)
  have hK2' : ∀ x : ↥(fixSubfield σ), x = 0 ∨ x = 1 := eq_zero_or_one_of_card_two hK2
  have hq2 : S.D.q = 2 := by
    have h1 : S.D.q ≤ S.D.q ^ s := Nat.le_self_pow (NeZero.ne s) S.D.q
    have h2 : 2 ≤ S.D.q := S.hqpow.1.two_le
    omega
  refine isPerfect_CQ_of_isPerfect_componentRootSpan i σ ?_
  by_cases hrank : ∀ α ∈ componentRoots (rootCharHom a) i,
      ∀ δ ∈ componentRoots (rootCharHom a) i, δ = α ∨ δ = -α
  · exact (false_of_rankOne S hT i hs hmin hnorm hz hQS hK2 hrank).elim
  have hbig : ∃ α ∈ componentRoots (rootCharHom a) i,
      ∃ δ ∈ componentRoots (rootCharHom a) i, δ ≠ α ∧ δ ≠ -α := by
    push Not at hrank
    exact hrank
  have hτ : ∀ τ : Tag, τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    intro τ; cases τ <;> simp
  rcases hτ τ with rfl | rfl | h | h | h | h
  · exact absurd (hG2 rfl) (by omega)
  · by_cases hA2 : ∃ α ∈ componentRoots (rootCharHom a) i,
        ∃ δ ∈ componentRoots (rootCharHom a) i, δ ≠ α ∧ δ ≠ -α ∧
          CFSG.LieType.Steinberg.Adjoint.iform α α =
            CFSG.LieType.Steinberg.Adjoint.iform δ δ ∧
          CFSG.LieType.Steinberg.Adjoint.iform α δ ≠ 0
    · exact isPerfect_componentRootSpan_F4_two hK2' i hA2
    · push Not at hA2
      obtain ⟨α, β, hαα, hββ, hαβ, hΨ⟩ := eq_b2Block_of_noA2 i hbig hA2
      exact (false_of_b2Block S hT i hs hmin hnorm hz h360 hK2 hαα hββ hαβ hΨ).elim
  · exact isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig
  · exact isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig
  · exact isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig
  · exact isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig

theorem innerKindSmallCompAction_holds : InnerKindSmallCompAction := by
  intro τ L _ _ _ p₀ p S hp hp2 a hT hap hTp h1 hG2 i hkind hQS h360 hQlt y hyZ hyF hyStab
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinner
  have hperf : Group.IsPerfect ↥(CQ σ i) :=
    isPerfect_CQ_of_inner_small S hT i hs hmin hσ hnorm hz hG2 hQS h360 hQlt
  exact centerQuotientHom_mem_innAutDerived_inner_of_untwist S hT i hs hmin σ hσ hzZ
    hnorm hz hperf hyZ hyF hyStab

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
