module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerAutImageProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.I542ThreeGroup
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three.Component
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.I542ThreeOffender
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.I542ThreeTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Final

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound


open CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.Quasithin
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld CFSG.HardMathSupport.Meierfrankenfeld.AGL81
open scoped commutatorElement

theorem exists_component_of_three_component
    {Y : Type} [Group Y] [Finite Y] (hO2 : CFSG.pCore 2 Y = ⊥)
    {E L J : Subgroup Y} [hE : E.Normal] [hL : L.Normal] (hEL : E ≤ L)
    (hEJ : ∀ j ∈ J, ∀ e ∈ E, j * e = e * j) (hLJ : L ≤ ⁅L, J⁆ ⊔ E)
    (hE3 : ¬ 3 ∣ Nat.card E) {Q : Type} [Group Q] (f : Y →* Q) (hf : f.ker = E)
    (hS : IsSimpleGroup ↥(L.map f)) (hnc : ¬ IsMulCommutative ↥(L.map f))
    (hty : IsRankTwoLayerType ↥(L.map f)) :
    ∃ R : Subgroup Y, R.Normal ∧ ⁅R, J⁆ = R ∧ IsComponentOf R ⊤ ∧ IsRankTwoLayerType ↥R ∧
      ∃ e : ↥R ≃* ↥(L.map f), ∀ r : ↥R, (e r : Q) = f (r : Y) := by
  classical
  set R : Subgroup Y := ⁅L, J⁆ with hR
  have hRn : R.Normal := normal_commutator_commutator hL hEL hEJ hLJ f hf hS hnc
  have hperf : ⁅R, R⁆ = R := commutator_self_eq hL hEJ hLJ f hf hS hnc
  have hRJ : ⁅R, J⁆ = R := commutator_commutator_eq hL hEJ hLJ
  have hRL : R ≤ L := commutator_le_of_normal hL J
  have hcen : ∀ z ∈ R, (∀ r ∈ R, z * r = r * z) → z ∈ E := fun z hz hzc =>
    mem_of_central hL hLJ f hf hS hnc hz hzc
  have hinf := inf_commutes hL hEJ hLJ
  let φ : ↥R →* ↥(L.map f) := (f.comp R.subtype).codRestrict (L.map f)
    (fun r => Subgroup.mem_map_of_mem f (hRL r.2))
  have hφs : Function.Surjective φ := by
    rintro ⟨s, hs⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨r, hr, e, he, hre⟩ := Subgroup.mem_sup_of_normal_right.mp (hLJ hl)
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    show f r = f l
    have hfe : f e = 1 := by rw [← MonoidHom.mem_ker, hf]; exact he
    rw [← hre, map_mul, hfe, mul_one]
  have hφk : φ.ker = Subgroup.center ↥R := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx g
      have h1 : f (x : Y) = 1 := congrArg Subtype.val hx
      have hxE : (x : Y) ∈ E := by rw [← hf]; exact h1
      exact Subtype.ext (hinf _ ⟨x.2, hxE⟩ _ g.2).symm
    · intro hx
      have hxE : (x : Y) ∈ E := hcen x x.2 fun r hr => by
        have := hx ⟨r, hr⟩
        exact (congrArg Subtype.val this).symm
      apply Subtype.ext
      show f x = 1
      rw [← MonoidHom.mem_ker, hf]; exact hxE
  have hRperf : Group.IsPerfect ↥R := by
    refine Group.isPerfect_def.mpr ?_
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_subtype_commutator, hperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eq1 : (↥R ⧸ Subgroup.center ↥R) ≃* ↥(L.map f) :=
    (QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have htyR : IsRankTwoLayerType (↥R ⧸ Subgroup.center ↥R) :=
    isRankTwoLayerType_of_equiv eq1.symm hty
  have h2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥R) := by
    intro hdvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype ↥(Subgroup.center ↥R) := Fintype.ofFinite _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥(Subgroup.center ↥R)) 2
      (by rwa [Fintype.card_eq_nat_card])
    have hxm : ((x : ↥R) : Y) ∈ Coordinator.centerInvolutions R := by
      refine ⟨(x : ↥R).2, fun r hr => ?_, ?_⟩
      · have := Subgroup.mem_center_iff.mp x.2 ⟨r, hr⟩
        exact (congrArg Subtype.val this).symm
      · have : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
        have h' := congrArg (fun z : ↥(Subgroup.center ↥R) => ((z : ↥R) : Y)) this
        simpa using h'
    rw [Coordinator.centerInvolutions_eq_bot hO2 R, Subgroup.mem_bot] at hxm
    have : x = 1 := Subtype.ext (Subtype.ext hxm)
    rw [this, orderOf_one] at hx
    omega
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥R) := by
    intro hdvd
    apply hE3
    refine hdvd.trans ?_
    have hle : (Subgroup.center ↥R).map R.subtype ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      refine hcen x x.2 fun r hr => ?_
      have := Subgroup.mem_center_iff.mp hx ⟨r, hr⟩
      exact (congrArg Subtype.val this).symm
    rw [← Subgroup.card_map_of_injective R.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hc : Subgroup.center ↥R = ⊥ := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three.center_eq_bot_of_layerType htyR h2 h3
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφk, hc]
  let e : ↥R ≃* ↥(L.map f) := MulEquiv.ofBijective φ ⟨hφi, hφs⟩
  refine ⟨R, hRn, hRJ, ⟨le_top, ?_, hRperf.commutator_eq_top, ?_⟩,
    isRankTwoLayerType_of_equiv e.symm hty, e, fun r => rfl⟩
  · haveI := hRn
    exact IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl _)
  · haveI := hS
    exact MulEquiv.isSimpleGroup eq1


theorem agl81I542Three
    : AGL81I542Three := by
  intro X _ _ T hGN E L _ _ hCE hEL h3 hS hnc hty hJ
  classical
  set C := gnC T with hC
  set π : X →* X ⧸ C := QuotientGroup.mk' C with hπ
  let q : (X ⧸ C) →* X ⧸ E :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.AutImageStar.quotMapHom C E hCE
  have hqπ : ∀ x : X, q (π x) = QuotientGroup.mk' E x := fun x => rfl
  have hqs : Function.Surjective q := fun w => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective E w
    exact ⟨π x, rfl⟩
  have hker : q.ker = E.map π := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    rw [MonoidHom.mem_ker, hqπ]
    constructor
    · intro hx
      exact ⟨x, (QuotientGroup.eq_one_iff x).mp hx, rfl⟩
    · rintro ⟨x', hx', hx'x⟩
      have : x'⁻¹ * x ∈ C := QuotientGroup.eq.mp hx'x
      refine (QuotientGroup.eq_one_iff x).mpr ?_
      have h1 : x = x' * (x'⁻¹ * x) := by group
      rw [h1]; exact E.mul_mem hx' (hCE this)
  set E' : Subgroup (X ⧸ C) := E.map π with hE'
  set L' : Subgroup (X ⧸ C) := L.map π with hL'
  haveI hE'n : E'.Normal := Subgroup.Normal.map ‹E.Normal› π (QuotientGroup.mk'_surjective C)
  haveI hL'n : L'.Normal := Subgroup.Normal.map ‹L.Normal› π (QuotientGroup.mk'_surjective C)
  have hEL' : E' ≤ L' := Subgroup.map_mono hEL
  have hEJ : ∀ j ∈ gnImg T (thompsonJ T), ∀ e ∈ E', j * e = e * j := fun j hj e he =>
    (Subgroup.mem_centralizer_iff.mp (thompsonJ_star_le_centralizer hGN E' h3 hj) e he).symm
  have hLJ : L' ≤ ⁅L', gnImg T (thompsonJ T)⁆ ⊔ E' := by
    have := Subgroup.map_mono (f := π) hJ
    rwa [Subgroup.map_sup, Subgroup.map_commutator] at this
  have hmapL : L'.map q = L.map (QuotientGroup.mk' E) := by
    rw [hL', Subgroup.map_map]; rfl
  have hS' : IsSimpleGroup ↥(L'.map q) := by rw [hmapL]; exact hS
  have hnc' : ¬ IsMulCommutative ↥(L'.map q) := by rw [hmapL]; exact hnc
  have hty' : IsRankTwoLayerType ↥(L'.map q) := by rw [hmapL]; exact hty
  obtain ⟨R, hRn, hRJ, hRc, hRty, e, he⟩ := exists_component_of_three_component
    (Y := X ⧸ C) (FF531.pCore_two_gnQuot hGN) hEL' hEJ hLJ h3 q hker hS' hnc' hty'
  have hAut : AutInOK R := HardMathSupport.Meierfrankenfeld.AGL81.I542.agl81I542 X T hGN R hRc hRJ hRty
  haveI : R.Normal := hRn
  haveI : (L.map (QuotientGroup.mk' E)).Normal :=
    Subgroup.Normal.map ‹L.Normal› _ (QuotientGroup.mk'_surjective E)
  let φ : ↥R ≃* ↥(L.map (QuotientGroup.mk' E)) := e.trans (MulEquiv.subgroupCongr hmapL)
  exact autInOK_of_surj_equiv R (L.map (QuotientGroup.mk' E)) q hqs φ (fun n => he n) hAut

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
