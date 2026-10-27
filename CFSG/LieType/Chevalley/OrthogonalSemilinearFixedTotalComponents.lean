module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootQuasisimple
public import CFSG.LieType.Chevalley.OddToralInvolutionFixedComponents
public import CFSG.GroupTheory.FixedCentralProductDescent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open scoped commutatorElement Pointwise

section Descent

variable {G : Type*} [Group G] {ι : Type*}

theorem iSup_subgroupOf_iSup_eq_top (H : ι → Subgroup G) :
    ⨆ i, (H i).subgroupOf (⨆ j, H j) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.iSup_induction' with
  | hp i y hy => exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_subgroupOf.2 hy)
  | h1 => exact one_mem _
  | hmul y z hy hz ihy ihz => exact mul_mem ihy ihz

theorem commutatorElement_mem_iSup_fixed [Finite ι] (F : MulAut G) (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hF : ∀ i, (H i).map F.toMonoidHom = H i) {r r' : G} (hr : r ∈ ⨆ i, H i)
    (hr' : r' ∈ ⨆ i, H i) (hFr : F r = r) (hFr' : F r' = r') :
    ⁅r, r'⁆ ∈ ⨆ i, (H i ⊓ F.toMonoidHom.eqLocus (MonoidHom.id G)) := by
  have := Fintype.ofFinite ι
  set T := ⨆ i, H i with hT
  have hHT : ∀ i, H i ≤ T := le_iSup H
  have hFT : ∀ x ∈ T, F x ∈ T := by
    intro x hx
    have h1 : F x ∈ T.map F.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rwa [hT, Subgroup.map_iSup, iSup_congr hF] at h1
  have hFT' : ∀ x ∈ T, F.symm x ∈ T := by
    intro x hx
    rw [hT, ← iSup_congr hF, ← Subgroup.map_iSup] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  let FT : MulAut T :=
    { toFun := fun x => ⟨F x, hFT x x.2⟩
      invFun := fun x => ⟨F.symm x, hFT' x x.2⟩
      left_inv := fun x => Subtype.ext (F.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (F.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (map_mul F (x : G) y) }
  let H' : ι → Subgroup T := fun i => (H i).subgroupOf T
  have hcomm' : Pairwise fun i j => ∀ x y : T, x ∈ H' i → y ∈ H' j → Commute x y :=
    fun i j hij x y hx hy => Subtype.ext (hcomm hij x y hx hy).eq
  have hgen' : ⨆ i, H' i = ⊤ := iSup_subgroupOf_iSup_eq_top H
  have hF' : ∀ i, (H' i).map FT.toMonoidHom = H' ((1 : Equiv.Perm ι) i) := by
    intro i
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show F (y : G) ∈ H i
      rw [← hF i]
      exact Subgroup.mem_map_of_mem _ hy
    · intro hx
      have hx' : (x : G) ∈ (H i).map F.toMonoidHom := by
        rw [hF i]
        exact hx
      obtain ⟨z, hz, hzx⟩ := hx'
      exact ⟨⟨z, hHT i hz⟩, hz, Subtype.ext hzx⟩
  obtain ⟨happ, -, -, hcommU, -⟩ := CFSG.GroupTheory.fixed_central_product_abelian_descent H'
    hcomm' hgen' FT 1 hF'
  have hrT : (⟨r, hr⟩ : T) ∈ FT.toMonoidHom.eqLocus (MonoidHom.id T) := Subtype.ext hFr
  have hr'T : (⟨r', hr'⟩ : T) ∈ FT.toMonoidHom.eqLocus (MonoidHom.id T) := Subtype.ext hFr'
  obtain ⟨t, ht, hμt⟩ := hcommU (Subgroup.commutator_mem_commutator hrT hr'T)
  have e : ⁅r, r'⁆ = ((Subgroup.noncommPiCoprod hcomm' t : T) : G) := by
    rw [hμt]
    rfl
  rw [e]
  have hti : ∀ i, (((t i : T)) : G) ∈ H i ⊓ F.toMonoidHom.eqLocus (MonoidHom.id G) := by
    intro i
    refine ⟨(t i).2, ?_⟩
    have h1 := happ t i
    have h2 : CFSG.GroupTheory.centralProductAut H' FT 1 hF' t = t := ht
    rw [h2] at h1
    have h3 := congrArg Subtype.val h1
    exact h3.symm
  have hmem : Subgroup.noncommPiCoprod hcomm' t ∈
      (⨆ i, (H i ⊓ F.toMonoidHom.eqLocus (MonoidHom.id G))).comap T.subtype := by
    rw [Subgroup.noncommPiCoprod_apply]
    exact Subgroup.noncommProd_mem _ _ fun i _ =>
      Subgroup.mem_iSup_of_mem (ι := ι) i (hti i)
  exact hmem

theorem commutatorElement_mem_of_le_normalizer {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    {a b : G} (ha : a ∈ H ⊔ N) (hb : b ∈ H ⊔ N) : ⁅a, b⁆ ∈ N := by
  have hmul : ((H ⊔ N : Subgroup G) : Set G) = (H : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H N hHN
  have ha' : a ∈ (H : Set G) * (N : Set G) := by rw [← hmul]; exact ha
  have hb' : b ∈ (H : Set G) * (N : Set G) := by rw [← hmul]; exact hb
  obtain ⟨h, hh, s, hs, rfl⟩ := ha'
  obtain ⟨h', hh', s', hs', rfl⟩ := hb'
  have hconj : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (hHN hg) x).1 hx
  have e : ⁅h * s, h' * s'⁆ = (h * s * h⁻¹) * ((h * h') * (s' * s⁻¹) * (h' * h)⁻¹) *
      (h' * s'⁻¹ * h'⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, ← hH h hh h' hh']
  exact mul_mem (mul_mem (hconj h hh s hs) (hconj _ (mul_mem hh hh') _
    (mul_mem hs' (inv_mem hs)))) (hconj h' hh' _ (inv_mem hs'))

theorem normal_isSolvable_subgroupOf {A B : Subgroup G}
    (hconj : ∀ x ∈ B, ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hcomm : ∀ x ∈ B, ∀ y ∈ B, ⁅x, y⁆ ∈ A) :
    ∃ _ : (A.subgroupOf B).Normal, Group.IsSolvable (B ⧸ A.subgroupOf B) := by
  have hN : (A.subgroupOf B).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (hconj g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  refine ⟨hN, Group.isSolvable_of_comm fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (((x * y)⁻¹ * (y * x) : B) : G) = ⁅((y⁻¹ : B) : G), ((x⁻¹ : B) : G)⁆ := by
    rw [commutatorElement_def]
    push_cast
    group
  rw [e]
  exact hcomm _ (y⁻¹).2 _ (x⁻¹).2

end Descent

section RootGroups

variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem unionRootSpan_le_centralizer_of_disjoint
    {J₁ J₂ : Set (KernelComponent χ)}
    (h : Disjoint J₁ J₂) :
    unionRootSpan K χ J₁ ≤ Subgroup.centralizer (unionRootSpan K χ J₂ : Set (ModGL τ K)) := by
  refine iSup₂_le fun α ⟨hα, hαJ⟩ => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun β ⟨hβ, hβJ⟩ => ?_
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hne : (⟦⟨α, hα⟩⟧ : KernelComponent χ) ≠ ⟦⟨β, hβ⟩⟧ := fun e =>
    Set.disjoint_left.1 h hαJ (by rw [e]; exact hβJ)
  exact (commute_of_mk_ne hne K x hx y hy).eq

end RootGroups

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

@[expose] def classOrbit
    (i₀ : KernelComponent D.χ) : Set (KernelComponent D.χ) :=
  {i | ∃ m : ℕ, ∃ α ∈ componentRoots D.χ i₀, ∃ β ∈ componentRoots D.χ i,
    (D.θ ^ m) (toReal α) = toReal β}

theorem self_mem_classOrbit
    (i : KernelComponent D.χ) : i ∈ D.classOrbit i := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep i
  exact ⟨0, a, ⟨a.2, rfl⟩, a, ⟨a.2, rfl⟩, by rw [pow_zero, Module.End.one_apply]⟩

theorem classOrbit_subset_of_mem
    {i₀ c : KernelComponent D.χ} (hc : c ∈ D.classOrbit i₀) :
    D.classOrbit c ⊆ D.classOrbit i₀ := by
  rintro d ⟨m', γ, ⟨hγK, hγc⟩, δ, ⟨hδK, hδd⟩, hm'⟩
  obtain ⟨m, α, hα, β, ⟨hβK, hβc⟩, hm⟩ := hc
  have hspec := D.thetaPowVec_spec hβK m'
  have hcls := D.mk_eq_of_pow (a := ⟨β, hβK⟩) (b := ⟨γ, hγK⟩) (hβc.trans hγc.symm) m'
    (a' := ⟨_, hspec.2.2⟩) (b' := ⟨δ, hδK⟩) hspec.1.symm hm'
  refine ⟨m' + m, α, hα, _, ⟨hspec.2.2, hcls.trans hδd⟩, ?_⟩
  rw [pow_add, Module.End.mul_apply, hm, hspec.1]

theorem mem_classOrbit_symm
    {i₀ c : KernelComponent D.χ} (hc : c ∈ D.classOrbit i₀) :
    i₀ ∈ D.classOrbit c := by
  obtain ⟨n, hn, hper⟩ := D.exists_pow_eq_on_kernelRoots
  obtain ⟨m, α, hα, β, hβ, hm⟩ := hc
  refine ⟨(n - 1) * m, β, hβ, α, hα, ?_⟩
  have e : (n - 1) * m + m = n * m := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  rw [← hm, ← Module.End.mul_apply, ← pow_add, e, pow_mul, Module.End.pow_apply]
  exact Function.iterate_fixed (hper α hα.1) m

theorem classOrbit_eq_of_mem
    {i₀ c : KernelComponent D.χ} (hc : c ∈ D.classOrbit i₀) :
    D.classOrbit c = D.classOrbit i₀ :=
  (D.classOrbit_subset_of_mem hc).antisymm
    (D.classOrbit_subset_of_mem (D.mem_classOrbit_symm hc))

theorem disjoint_of_ne
    {J₁ J₂ : Set.range D.classOrbit} (h : J₁ ≠ J₂) :
    Disjoint (J₁ : Set (KernelComponent D.χ)) J₂ := by
  obtain ⟨_, i₁, rfl⟩ := J₁
  obtain ⟨_, i₂, rfl⟩ := J₂
  refine Set.disjoint_left.2 fun c h₁ h₂ => h (Subtype.ext ?_)
  exact (D.classOrbit_eq_of_mem h₁).symm.trans (D.classOrbit_eq_of_mem h₂)

theorem finite_orbitIndex
    : Finite (Set.range D.classOrbit) := by
  have := D.finite_kernelComponent
  infer_instance

@[expose] def withOrbit
    (J' : Set.range D.classOrbit) :
    OrthogonalSemilinearFixedRootDatum τ p₀ k :=
  { D with
    J := J'
    isThetaOrbit := by
      obtain ⟨i₀, h⟩ := J'.2
      exact ⟨i₀, h.symm⟩ }

@[expose] def kernelSpan :
    Subgroup (ModGL τ k) :=
  rootSpan τ k (kernelRoots D.χ)

@[expose] def torusKernelSpan
    : Subgroup (ModGL τ k) :=
  torusGroup τ k ⊔ D.kernelSpan

@[expose] def totalFixedGroup :
    Subgroup (adjointGroup τ k) :=
  D.torusKernelSpan.subgroupOf (adjointGroup τ k) ⊓ D.F.toMonoidHom.eqLocus (MonoidHom.id _)

@[expose] def kernelFixedGroup :
    Subgroup (adjointGroup τ k) :=
  D.kernelSpan.subgroupOf (adjointGroup τ k) ⊓ D.F.toMonoidHom.eqLocus (MonoidHom.id _)

@[expose] def orbitFixedJoin :
    Subgroup (adjointGroup τ k) :=
  ⨆ J' : Set.range D.classOrbit, (D.withOrbit J').fixedGroup

theorem mem_totalFixedGroup
    {x : adjointGroup τ k} :
    x ∈ D.totalFixedGroup ↔ (x : ModGL τ k) ∈ D.torusKernelSpan ∧ D.F x = x := by
  rw [totalFixedGroup, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rfl

theorem mem_kernelFixedGroup
    {x : adjointGroup τ k} :
    x ∈ D.kernelFixedGroup ↔ (x : ModGL τ k) ∈ D.kernelSpan ∧ D.F x = x := by
  rw [kernelFixedGroup, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rfl

theorem kernelFixedGroup_le_totalFixedGroup
    : D.kernelFixedGroup ≤ D.totalFixedGroup :=
  fun _ hx => D.mem_totalFixedGroup.2 ⟨Subgroup.mem_sup_right (D.mem_kernelFixedGroup.1 hx).1,
    (D.mem_kernelFixedGroup.1 hx).2⟩

theorem torusKernelSpan_le_normalizer :
    D.torusKernelSpan ≤ Subgroup.normalizer (D.kernelSpan : Set (ModGL τ k)) :=
  sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1) Subgroup.le_normalizer

theorem conj_mem_kernelFixedGroup
    {x r : adjointGroup τ k} (hx : x ∈ D.totalFixedGroup)
    (hr : r ∈ D.kernelFixedGroup) : x * r * x⁻¹ ∈ D.kernelFixedGroup := by
  obtain ⟨hxM, hxF⟩ := D.mem_totalFixedGroup.1 hx
  obtain ⟨hrS, hrF⟩ := D.mem_kernelFixedGroup.1 hr
  refine D.mem_kernelFixedGroup.2 ⟨?_, by rw [map_mul, map_mul, map_inv, hxF, hrF]⟩
  exact (Subgroup.mem_normalizer_iff.1 (D.torusKernelSpan_le_normalizer hxM) _).1 hrS

theorem commutatorElement_mem_kernelFixedGroup
    {x y : adjointGroup τ k}
    (hx : x ∈ D.totalFixedGroup) (hy : y ∈ D.totalFixedGroup) :
    ⁅x, y⁆ ∈ D.kernelFixedGroup := by
  obtain ⟨hxM, hxF⟩ := D.mem_totalFixedGroup.1 hx
  obtain ⟨hyM, hyF⟩ := D.mem_totalFixedGroup.1 hy
  refine D.mem_kernelFixedGroup.2 ⟨?_, by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hxF, hyF]⟩
  have h := commutatorElement_mem_of_le_normalizer (N := D.kernelSpan)
    (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
    (fun _ ha _ hb => mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha)
      (torusGroup_le_diagonalGroup hb)) hxM hyM
  have e : ((⁅x, y⁆ : adjointGroup τ k) : ModGL τ k) = ⁅(x : ModGL τ k), (y : ModGL τ k)⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    push_cast
    rfl
  rw [e]
  exact h

theorem rootSpanJ_withOrbit_le_kernelSpan
    (J' : Set.range D.classOrbit) :
    (D.withOrbit J').rootSpanJ ≤ D.kernelSpan :=
  rootSpan_mono fun _ hα => hα.1

theorem iSup_rootSpanJ_withOrbit :
    ⨆ J' : Set.range D.classOrbit, (D.withOrbit J').rootSpanJ = D.kernelSpan := by
  refine le_antisymm (iSup_le D.rootSpanJ_withOrbit_le_kernelSpan) (iSup₂_le fun α hα => ?_)
  let J' : Set.range D.classOrbit := ⟨D.classOrbit ⟦⟨α, hα⟩⟧, ⟦⟨α, hα⟩⟧, rfl⟩
  exact (rootSubgroup_le_unionRootSpan (K := k) (J := (J' : Set (KernelComponent D.χ)))
    ⟨hα, D.self_mem_classOrbit _⟩).trans
      (le_iSup (fun J' : Set.range D.classOrbit => (D.withOrbit J').rootSpanJ) J')

theorem commute_of_ne
    {J₁ J₂ : Set.range D.classOrbit} (h : J₁ ≠ J₂) {x y : ModGL τ k}
    (hx : x ∈ (D.withOrbit J₁).rootSpanJ) (hy : y ∈ (D.withOrbit J₂).rootSpanJ) :
    Commute x y :=
  (Subgroup.mem_centralizer_iff.1
    (unionRootSpan_le_centralizer_of_disjoint (D.disjoint_of_ne h) hx) y hy).symm

theorem kernelSpan_le_normalizer
    (J' : Set.range D.classOrbit) :
    D.kernelSpan ≤ Subgroup.normalizer ((D.withOrbit J').rootSpanJ : Set (ModGL τ k)) := by
  rw [← D.iSup_rootSpanJ_withOrbit]
  refine iSup_le fun J'' => ?_
  by_cases h : J'' = J'
  · rw [h]
    exact Subgroup.le_normalizer
  · exact (unionRootSpan_le_centralizer_of_disjoint (D.disjoint_of_ne h)).trans
      (Subgroup.centralizer_le_normalizer _)

theorem conj_mem_fixedGroup_withOrbit
    {J' : Set.range D.classOrbit} {r x : adjointGroup τ k}
    (hr : r ∈ D.kernelFixedGroup) (hx : x ∈ (D.withOrbit J').fixedGroup) :
    r * x * r⁻¹ ∈ (D.withOrbit J').fixedGroup := by
  obtain ⟨hrS, hrF⟩ := D.mem_kernelFixedGroup.1 hr
  obtain ⟨hxS, hxF⟩ := (D.withOrbit J').mem_fixedGroup.1 hx
  change D.F x = x at hxF
  refine (D.withOrbit J').mem_fixedGroup.2 ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 (D.kernelSpan_le_normalizer J' hrS) _).1 hxS
  · change D.F (r * x * r⁻¹) = r * x * r⁻¹
    rw [map_mul, map_mul, map_inv, hrF, hxF]

theorem fixedGroup_withOrbit_le_kernelFixedGroup
    (J' : Set.range D.classOrbit) :
    (D.withOrbit J').fixedGroup ≤ D.kernelFixedGroup := fun _ hx =>
  D.mem_kernelFixedGroup.2 ⟨D.rootSpanJ_withOrbit_le_kernelSpan J'
    ((D.withOrbit J').mem_fixedGroup.1 hx).1, ((D.withOrbit J').mem_fixedGroup.1 hx).2⟩

theorem fixedGroup_withOrbit_le_orbitFixedJoin
    (J' : Set.range D.classOrbit) :
    (D.withOrbit J').fixedGroup ≤ D.orbitFixedJoin :=
  le_iSup (fun J' : Set.range D.classOrbit => (D.withOrbit J').fixedGroup) J'

theorem orbitFixedJoin_le_kernelFixedGroup
    : D.orbitFixedJoin ≤ D.kernelFixedGroup :=
  iSup_le D.fixedGroup_withOrbit_le_kernelFixedGroup

theorem conj_mem_orbitFixedJoin
    {r u : adjointGroup τ k} (hr : r ∈ D.kernelFixedGroup)
    (hu : u ∈ D.orbitFixedJoin) : r * u * r⁻¹ ∈ D.orbitFixedJoin := by
  unfold orbitFixedJoin at hu ⊢
  induction hu using Subgroup.iSup_induction' with
  | hp J' x hx => exact Subgroup.mem_iSup_of_mem J' (D.conj_mem_fixedGroup_withOrbit hr hx)
  | h1 => simp
  | hmul x y _ _ hx hy =>
    have e : r * (x * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹) := by group
    rw [e]
    exact mul_mem hx hy

theorem commutatorElement_mem_orbitFixedJoin
    {r r' : adjointGroup τ k}
    (hr : r ∈ D.kernelFixedGroup) (hr' : r' ∈ D.kernelFixedGroup) :
    ⁅r, r'⁆ ∈ D.orbitFixedJoin := by
  have := D.finite_orbitIndex
  have hmem : ∀ x : adjointGroup τ k, (x : ModGL τ k) ∈ D.kernelSpan →
      x ∈ ⨆ J' : Set.range D.classOrbit,
        (D.withOrbit J').rootSpanJ.subgroupOf (adjointGroup τ k) := by
    intro x hx
    have h1 : (⨆ J' : Set.range D.classOrbit,
        (D.withOrbit J').rootSpanJ.subgroupOf (adjointGroup τ k)).map
          (adjointGroup τ k).subtype = D.kernelSpan := by
      rw [Subgroup.map_iSup, ← D.iSup_rootSpanJ_withOrbit]
      refine iSup_congr fun J' => ?_
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_of_le_left unionRootSpan_le_adjointGroup
    rw [← h1] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  exact commutatorElement_mem_iSup_fixed D.F
    (fun J' => (D.withOrbit J').rootSpanJ.subgroupOf (adjointGroup τ k))
    (fun J₁ J₂ h x y hx hy => Subtype.ext (D.commute_of_ne h hx hy).eq)
    (fun J' => (D.withOrbit J').map_rootSpanJ) (hmem r (D.mem_kernelFixedGroup.1 hr).1)
    (hmem r' (D.mem_kernelFixedGroup.1 hr').1) (D.mem_kernelFixedGroup.1 hr).2
    (D.mem_kernelFixedGroup.1 hr').2

end OrthogonalSemilinearFixedRootDatum

open CFSG.ComponentClassification.CatalogueBPrimeJoin in
theorem orthogonal_semilinear_total_fixed_p_components
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime]
    {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) (hX : Finite D.totalFixedGroup) :
    ∀ ℓ : ℕ, ℓ.Prime → ∀ L : Subgroup D.totalFixedGroup, CFSG.IsPComponent ℓ L →
      CFSG.IsQuasisimple L := by
  intro ℓ hℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hRX := D.kernelFixedGroup_le_totalFixedGroup
  have hUR := D.orbitFixedJoin_le_kernelFixedGroup
  have hR : Finite D.kernelFixedGroup :=
    Finite.of_injective _ (Subgroup.inclusion_injective hRX)
  have hU : Finite D.orbitFixedJoin := Finite.of_injective _ (Subgroup.inclusion_injective hUR)
  have hqU : ∀ L : Subgroup D.orbitFixedJoin, CFSG.IsPComponent ℓ L →
      CFSG.IsQuasisimple L := by
    have := D.finite_orbitIndex
    let e := (Finite.equivFin (Set.range D.classOrbit)).symm
    refine p_component_quasisimplicity_subnormal_join ℓ hℓ _
      (fun j => (D.withOrbit (e j)).fixedGroup.subgroupOf D.orbitFixedJoin) (fun j => ?_) ?_
      (fun j => ?_)
    · have hN : ((D.withOrbit (e j)).fixedGroup.subgroupOf D.orbitFixedJoin).Normal :=
        ⟨fun n hn g => Subgroup.mem_subgroupOf.2
          (D.conj_mem_fixedGroup_withOrbit (hUR g.2) (Subgroup.mem_subgroupOf.1 hn))⟩
      exact hN.isSubnormal
    · rw [e.iSup_comp (g := fun J' => (D.withOrbit J').fixedGroup.subgroupOf D.orbitFixedJoin)]
      exact iSup_subgroupOf_iSup_eq_top _
    · exact OddToralFixed.pComponent_quasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (D.fixedGroup_withOrbit_le_orbitFixedJoin (e j)))
        ((orthogonal_semilinear_fixed_root_quasisimplicity (D.withOrbit (e j))).2.2.2.2.2 ℓ hℓ)
  have hqR : ∀ L : Subgroup D.kernelFixedGroup, CFSG.IsPComponent ℓ L →
      CFSG.IsQuasisimple L := by
    obtain ⟨hN, hS⟩ := normal_isSolvable_subgroupOf (A := D.orbitFixedJoin)
      (B := D.kernelFixedGroup) (fun x hx a ha => D.conj_mem_orbitFixedJoin hx ha)
      (fun x hx y hy => D.commutatorElement_mem_orbitFixedJoin hx hy)
    exact pComponent_quasisimple_of_normal_solvable_quotient ℓ _
      (OddToralFixed.pComponent_quasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUR) hqU)
  obtain ⟨hN, hS⟩ := normal_isSolvable_subgroupOf (A := D.kernelFixedGroup)
    (B := D.totalFixedGroup) (fun x hx a ha => D.conj_mem_kernelFixedGroup hx ha)
    (fun x hx y hy => D.commutatorElement_mem_kernelFixedGroup hx hy)
  exact pComponent_quasisimple_of_normal_solvable_quotient ℓ _
    (OddToralFixed.pComponent_quasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRX) hqR)

end CFSG.LieType.Chevalley
