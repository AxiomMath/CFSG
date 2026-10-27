module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Lab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LabHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompInn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)

private theorem two_le_n_of_canonLabel_n_eq_three {lab : GLALabel}
    (hlab : CFSG.Assembly.LargeEvenInLambda2 lab) (h : (canonLabel lab).n = 3) : 2 ≤ lab.n := by
  obtain ⟨t, r, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  show 2 ≤ n
  change (canonLabel ⟨t, r, n⟩).n = 3 at h
  cases t <;> simp only [canonLabel] at h <;> (try split_ifs at h) <;> (try simp at h) <;> omega

private theorem congr_apply_apply' {G H : Type} [Group G] [Group H] (e : G ≃* H) (α : MulAut G)
    (g : G) : MulAut.congr e α (e g) = e (α g) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

private theorem congr_symm_apply' {G H : Type} [Group G] [Group H] (e : G ≃* H) (α : MulAut H)
    (g : G) : MulAut.congr e.symm α g = e.symm (α (e g)) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_symm]

private theorem mem_map_equiv_iff {G H : Type} [Group G] [Group H] (e : G ≃* H) (A : Subgroup G)
    (g : G) : e g ∈ A.map e.toMonoidHom ↔ g ∈ A := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem map_eq_self_of_forall_iff {G : Type} [Group G] (H : Subgroup G) (f : MulAut G)
    (h : ∀ x, f x ∈ H ↔ x ∈ H) : H.map f.toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have := h (f.symm x)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

private theorem chevAut_mem_chevTransfer {Γ : Type} [Group Γ] {K J : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (K : Set Γ)) (hgJ : g ∈ Subgroup.normalizer (J : Set Γ))
    {s : PSimple 3 K} (hs : s ∈ chevTransfer 3 K J) :
    chevAut 3 K ⟨g, hg⟩ s ∈ chevTransfer 3 K J := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hs
  rw [chevAut_chevQuotHom]
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
  rw [chev_coe_normalizerMonoidHom]
  exact (Subgroup.mem_normalizer_iff.1 hgJ k).1 (Subgroup.mem_subgroupOf.1 hk)

private theorem congr_chevAut_mem_stab {Γ : Type} [Group Γ] {K J : Subgroup Γ} {g : Γ}
    (hgK : g ∈ Subgroup.normalizer (K : Set Γ)) (hgJ : g ∈ Subgroup.normalizer (J : Set Γ))
    {T : Type} [Group T] (e : PSimple 3 K ≃* T) :
    MulAut.congr e (chevAut 3 K ⟨g, hgK⟩) ∈
      CFSG.GroupActions.subgroupStabAut ((chevTransfer 3 K J).map e.toMonoidHom) := by
  have hJstab : ∀ s : PSimple 3 K,
      chevAut 3 K ⟨g, hgK⟩ s ∈ chevTransfer 3 K J ↔ s ∈ chevTransfer 3 K J := by
    intro s
    refine ⟨fun h => ?_, chevAut_mem_chevTransfer hgK hgJ⟩
    have h' := chevAut_mem_chevTransfer (Subgroup.inv_mem _ hgK) (Subgroup.inv_mem _ hgJ) h
    rwa [← MulAut.mul_apply, ← map_mul,
      show (⟨g⁻¹, Subgroup.inv_mem _ hgK⟩ * ⟨g, hgK⟩ : ↥(Subgroup.normalizer (K : Set Γ))) = 1 from
        Subtype.ext (inv_mul_cancel g), map_one, MulAut.one_apply] at h'
  refine map_eq_self_of_forall_iff _ _ fun t => ?_
  obtain ⟨s, rfl⟩ := e.surjective t
  rw [congr_apply_apply']
  exact (mem_map_equiv_iff e _ _).trans ((hJstab s).trans (mem_map_equiv_iff e _ _).symm)

private theorem exists_surjection_to_transfer {Γ : Type} [Group Γ] {K J : Subgroup Γ} (hJK : J ≤ K)
    {T : Type} [Group T] (e : PSimple 3 K ≃* T) :
    ∃ π : ↥J →* ↥((chevTransfer 3 K J).map e.toMonoidHom), Function.Surjective π ∧
      ∀ j : ↥J, ((π j : ↥((chevTransfer 3 K J).map e.toMonoidHom)) : T) =
        e (chevQuotHom 3 K (Subgroup.inclusion hJK j)) := by
  refine ⟨((e.toMonoidHom.comp (chevQuotHom 3 K)).comp (Subgroup.inclusion hJK)).codRestrict _
    (fun j => ?_), ?_, fun j => rfl⟩
  · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 j.2))
  · rintro ⟨t, ht⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hs
    exact ⟨⟨k, Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩

private theorem congr_chevAut_apply_transfer {Γ : Type} [Group Γ] {K J : Subgroup Γ} (hJK : J ≤ K)
    {g : Γ} (hgK : g ∈ Subgroup.normalizer (K : Set Γ)) (hgJ : g ∈ Subgroup.normalizer (J : Set Γ))
    {T : Type} [Group T] (e : PSimple 3 K ≃* T) (j : ↥J) :
    MulAut.congr e (chevAut 3 K ⟨g, hgK⟩) (e (chevQuotHom 3 K (Subgroup.inclusion hJK j))) =
      e (chevQuotHom 3 K (Subgroup.inclusion hJK (J.normalizerMonoidHom ⟨g, hgJ⟩ j))) := by
  rw [congr_apply_apply', chevAut_chevQuotHom]
  rfl

private theorem exists_equivariant_equiv {Γ : Type} [Group Γ] [Finite Γ] {K J X : Subgroup Γ}
    (hJ : GLAPComponent 3 X J) (hJK : J ≤ K) {g : Γ} (hgK : g ∈ Subgroup.normalizer (K : Set Γ))
    (hgJ : g ∈ Subgroup.normalizer (J : Set Γ)) {T : Type} [Group T] [Finite T]
    (e : PSimple 3 K ≃* T) {Y : Subgroup T}
    (hJp' : GLAPComponent 3 Y ((chevTransfer 3 K J).map e.toMonoidHom))
    (hKq : CFSG.Open.IsQuasisimple ↥((chevTransfer 3 K J).map e.toMonoidHom))
    (hstab : MulAut.congr e (chevAut 3 K ⟨g, hgK⟩) ∈
      CFSG.GroupActions.subgroupStabAut ((chevTransfer 3 K J).map e.toMonoidHom)) :
    ∃ ι : PSimple 3 J ≃* ↥((chevTransfer 3 K J).map e.toMonoidHom) ⧸
        Subgroup.center ↥((chevTransfer 3 K J).map e.toMonoidHom),
      ∀ s : PSimple 3 J, centerQuotientHom _ (CFSG.GroupActions.subgroupStabRestrict
        ((chevTransfer 3 K J).map e.toMonoidHom) ⟨MulAut.congr e (chevAut 3 K ⟨g, hgK⟩), hstab⟩)
        (ι s) = ι (chevAut 3 J ⟨g, hgJ⟩ s) := by
  obtain ⟨π, hπ, hπval⟩ := exists_surjection_to_transfer hJK e
  obtain ⟨ι, hι⟩ := u9_exists_pSimple_equiv_centerQuot Nat.prime_three
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ) hKq
    (isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJp')) π hπ
  refine ⟨ι, fun s => ?_⟩
  obtain ⟨j, rfl⟩ := chevQuotHom_surjective 3 J s
  obtain ⟨j', hj'⟩ : ∃ j' : ↥J, j' = J.normalizerMonoidHom ⟨g, hgJ⟩ j := ⟨_, rfl⟩
  have h1 : ι (chevQuotHom 3 J j) = QuotientGroup.mk (π j) := hι j
  have h5 : ι (chevQuotHom 3 J j') = QuotientGroup.mk (π j') := hι j'
  have h2 : CFSG.GroupActions.subgroupStabRestrict ((chevTransfer 3 K J).map e.toMonoidHom)
      ⟨MulAut.congr e (chevAut 3 K ⟨g, hgK⟩), hstab⟩ (π j) = π j' := by
    apply Subtype.ext
    rw [CFSG.GroupActions.subgroupStabRestrict_apply, hπval j, hπval j', hj']
    exact congr_chevAut_apply_transfer hJK hgK hgJ e j
  have h3 : chevAut 3 J ⟨g, hgJ⟩ (chevQuotHom 3 J j) = chevQuotHom 3 J j' := by
    rw [hj']
    exact chevAut_chevQuotHom 3 J ⟨g, hgJ⟩ j
  have h4 := onCenterQuotient_apply_mk (CFSG.GroupActions.subgroupStabRestrict
    ((chevTransfer 3 K J).map e.toMonoidHom) ⟨MulAut.congr e (chevAut 3 K ⟨g, hgK⟩), hstab⟩) (π j)
  rw [h3, h1, h5, ← h2]
  exact h4

section GF8Inn


theorem u9_chevAut_mem_innAutDerived_gf8 {Γ : Type} [Group Γ] [Finite Γ] {K : Subgroup Γ} {y : Γ}
    (hy : y ∈ Subgroup.normalizer (K : Set Γ)) (hq : CFSG.Open.IsQuasisimple (PQuot 3 K))
    (hI : S10.InnDiagOn 3 (Subgroup.zpowers y) K) (d : TauCeti.ValidLieTypeIndex)
    (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd2 : d.1.characteristic = 2)
    (hfs : KD264Lie.fieldSize d.1 = 8) :
    chevAut 3 K ⟨y, hy⟩ ∈ innAutDerived (PSimple 3 K) := by
  obtain ⟨lab, hlab, hin⟩ := innDiagKind_chevAut hy hq hI
  have hlam := CanonSubcomp.lambda2_of_hasLabel hlab
  have h2 : 2 ^ (canonLabel lab).n = KD264Lie.fieldSize d.1 :=
    CanonSubcomp.two_pow_canonLabel_n_of_lie CFSG.StandardType.ggLabelRigidInput_holds hlab d hd2 e
  have h3 : (canonLabel lab).n = 3 :=
    Nat.pow_right_injective (le_refl 2) (show 2 ^ (canonLabel lab).n = 2 ^ 3 by rw [h2, hfs])
  exact CanonSubcomp.mem_innAutDerived_of_innDiagKind
    CFSG.StandardType.ggInndiagCommRestInput_holds (Y10F.center_centerQuot_eq_bot hq)
    (two_le_n_of_canonLabel_n_eq_three hlam h3) hin

end GF8Inn

section GF8Comp


theorem u9_gf8_component {Γ : Type} [Group Γ] [Finite Γ] {K J : Subgroup Γ} {x : Γ} (hx : x ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (K : Set Γ)) (hq : CFSG.Open.IsQuasisimple (PQuot 3 K))
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J) (d : TauCeti.ValidLieTypeIndex)
    (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd2 : d.1.characteristic = 2)
    (hβ1 : MulAut.congr e (chevAut 3 K ⟨x, hxN⟩) ≠ 1) :
    GLAPComponent 3 (fixSubgroup (MulAut.congr e (chevAut 3 K ⟨x, hxN⟩)))
        ((chevTransfer 3 K J).map e.toMonoidHom) ∧
      CFSG.Open.IsComponentOf ((chevTransfer 3 K J).map e.toMonoidHom)
        (fixSubgroup (MulAut.congr e (chevAut 3 K ⟨x, hxN⟩))) := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx
  have hJp : GLAPComponent 3 (fixSubgroup (chevAut 3 K ⟨x, hxN⟩)) (chevTransfer 3 K J) :=
    glaPComponent_chevTransfer Nat.prime_three hxN hxp hJ
  obtain ⟨hJp', -⟩ := chevQ_transport Nat.prime_three e hJp
  refine ⟨hJp', ?_⟩
  haveI : IsSimpleGroup (PSimple 3 K) := hq.2
  have hsimple' : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := e.symm.isSimpleGroup
  have hnc' : ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a := by
    obtain ⟨u, v, huv⟩ := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      _ hq
    exact ⟨e u, e v, fun h => huv (e.injective (by simpa using h))⟩
  have hβ3 : MulAut.congr e (chevAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow, chevAut_pow_eq_one 3 K hxN hx, map_one]
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
    (TauCeti.CFSGIndex.lie d).Group hsimple' hnc' d ⟨MulEquiv.refl _⟩ 3 Nat.prime_three
    (by decide) (by rw [hd2]; decide) _ hβ3 hβ1
  exact (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJp'
    (hpil _ hJp'.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJp'))).1

end GF8Comp

section Main


theorem u9Gf8Absurd_holds : U9Gf8Absurd := by
  unfold U9Gf8Absurd
  intro Γ _ _ K J x a hx ha hxa hI1 hI2 hJ hJU hF d heS hd2 hfs hC hx1
  obtain ⟨eS⟩ := heS
  have hxN : x ∈ Subgroup.normalizer (K : Set Γ) := hI1.1 (Subgroup.mem_zpowers x)
  have haN : a ∈ Subgroup.normalizer (K : Set Γ) := hI2.1 (Subgroup.mem_zpowers a)
  have haiN : a⁻¹ ∈ Subgroup.normalizer (K : Set Γ) := Subgroup.inv_mem _ haN
  have hI2i : S10.InnDiagOn 3 (Subgroup.zpowers a⁻¹) K := by
    rw [Subgroup.zpowers_inv]
    exact hI2
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have haJ : a ∈ Subgroup.normalizer (J : Set Γ) := hF.1
  have haiJ : a⁻¹ ∈ Subgroup.normalizer (J : Set Γ) := Subgroup.inv_mem _ haJ
  have hlabAll : Y10F.HasLabel (PQuot 3 K) (fun _ => True) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hI1.2
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := Y10F.hasLabel_isQuasisimple hlabAll
  have hβ₀D := u9_chevAut_mem_innAutDerived_gf8 hxN hq hI1 d eS hd2 hfs
  have hγ₀D := u9_chevAut_mem_innAutDerived_gf8 haiN hq hI2i d eS hd2 hfs
  have hβ₀3 : chevAut 3 K ⟨x, hxN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hxN hx
  have hγ₀3 : chevAut 3 K ⟨a⁻¹, haiN⟩ ^ 3 = 1 :=
    chevAut_pow_eq_one 3 K haiN (by rw [inv_pow, ha, inv_one])
  have hcomm : chevAut 3 K ⟨x, hxN⟩ * chevAut 3 K ⟨a⁻¹, haiN⟩ =
      chevAut 3 K ⟨a⁻¹, haiN⟩ * chevAut 3 K ⟨x, hxN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Commute.inv_right (show Commute x a from hxa)).eq
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ eS.toEquiv
  have hβmem := (mem_innAutDerived_congr eS).2 hβ₀D
  have hymem := (mem_innAutDerived_congr eS).2 hγ₀D
  have hβ3 : MulAut.congr eS (chevAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow, hβ₀3, map_one]
  have hy3 : MulAut.congr eS (chevAut 3 K ⟨a⁻¹, haiN⟩) ^ 3 = 1 := by
    rw [← map_pow, hγ₀3, map_one]
  have hβ1 : MulAut.congr eS (chevAut 3 K ⟨x, hxN⟩) ≠ 1 := fun h =>
    hx1 ((MulAut.congr eS).injective (by rw [map_one]; exact h))
  have hβy : MulAut.congr eS (chevAut 3 K ⟨x, hxN⟩) * MulAut.congr eS (chevAut 3 K ⟨a⁻¹, haiN⟩) =
      MulAut.congr eS (chevAut 3 K ⟨a⁻¹, haiN⟩) * MulAut.congr eS (chevAut 3 K ⟨x, hxN⟩) := by
    rw [← map_mul (MulAut.congr eS), ← map_mul (MulAut.congr eS), hcomm]
  obtain ⟨hJp', hKc⟩ := u9_gf8_component hx hxN hq hJ d eS hd2 hβ1
  have hystab := congr_chevAut_mem_stab (J := J) haiN haiJ eS
  obtain ⟨ι, hι⟩ := exists_equivariant_equiv hJ hJK haiN haiJ eS hJp' hKc.2.2 hystab
  obtain ⟨q, hv, hq8, ⟨eJ⟩⟩ := CatB.lieIndex_isU3eight hJU
  have hres := hC _ hβmem hβ3 hβ1 _ hKc ⟨.twistedA 2 q, hv⟩ ⟨q, Or.inr rfl, hq8⟩
    ⟨ι.symm.trans eJ⟩ _ hymem hy3 hβy hystab
  have hmem : MI.indAut 3 J a haJ ∈ innAutDerived (PSimple 3 J) := by
    have hν : MulAut.congr ι.symm (centerQuotientHom _ (CFSG.GroupActions.subgroupStabRestrict
        ((chevTransfer 3 K J).map eS.toMonoidHom)
        ⟨MulAut.congr eS (chevAut 3 K ⟨a⁻¹, haiN⟩), hystab⟩)) = MI.indAut 3 J a haJ := by
      ext s
      rw [congr_symm_apply', hι s, MulEquiv.symm_apply_apply]
      rfl
    rw [← hν]
    exact (mem_innAutDerived_congr ι.symm).2 hres
  exact (MI.field_nonInnDiag_holds Nat.prime_three (by norm_num) hF).2
    (u9_innDiagOn_of_indAut_mem_innAutDerived haJ
      (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ) hJU hmem)

end Main

end CFSG.LocalAnalysis.GLTheoremA.I141F
