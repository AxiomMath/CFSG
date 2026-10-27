module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentComp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentToral
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Multi
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp TwE6UniqAbs
open scoped MatrixGroups Matrix commutatorElement

theorem fixSubgroup_conj_eq_centralizer_e6 {P : Type*} [Group P] (x : P) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set P) := by
  ext g
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  show x * g * x⁻¹ = g ↔ g * x = x * g
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [h]
      _ = g := by group

theorem isComponentOf_of_glaPComponent_core_bot {G : Type*} [Group G] {p : ℕ}
    {X L : Subgroup G} (hX : GLAPPrimeCoreOf p X = ⊥) (hL : GLAPComponent p X L) :
    IsComponentOf L X := by
  have hcore : GLAPPrimeCore p ↥X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hX
  refine ⟨hL.1, hL.2.1, ?_⟩
  have hq := hL.2.2.1.2.2
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective (L.subgroupOf X) _ hinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hL.1)) hq

theorem exists_noncomm_of_isQuasisimple_e6 {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => h b a
  have := hQ.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

section Three


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem Std8.comap_inf_centralizer (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) :
    (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 (a0 ω)}).comap D.S.Γ.subtype =
      Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← D.coe_z0 hω]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨g.2, congrArg Subtype.val h⟩

theorem Std8.isComponentOf_Rc
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) (i : KernelComponent (rootCharHom (a0 ω))) :
    IsComponentOf (D.Rc ω i) (Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)) := by
  obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus D.S (D.a0_mem_torus hω) i
  have hcomp : IsComponentOf (rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i)
      (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 (a0 ω)}) :=
    ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub,
      open_isQuasisimple (D.rationalComponent_quasisimple_lie hω i).1⟩
  have hrange : D.S.Γ.subtype.range = D.S.Γ := Subgroup.range_subtype _
  have h := isComponentOf_comap_of_injective D.S.Γ.subtype D.S.Γ.subtype_injective
    (by rw [hrange]; exact D.rationalComponent_le_Γ i) (by rw [hrange]; exact inf_le_left) hcomp
  rwa [D.comap_inf_centralizer hω] at h

@[expose] def jOf : Fin 3 → Fin Tag.E6.rank := ![0, 4, 1]

theorem cls_single_jOf : ∀ k : Fin 3, cls (Pi.single (jOf k) 1) = k := by decide +kernel

theorem single_jOf_three : ∀ k : Fin 3, (Pi.single (jOf k) 1 : Fin Tag.E6.rank → ℤ) 3 = 0 := by
  decide +kernel

theorem iform_single_self_e6 :
    ∀ j : Fin Tag.E6.rank, iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) = 2 := by
  decide +kernel

theorem Std8.three_dvd_card_Rc (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3)
    (i : KernelComponent (rootCharHom (a0 ω))) : 3 ∣ Nat.card ↥(D.Rc ω i) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he⟩ := exists_classEquiv hω
  have hω3 := pow_three_of_orderOf_three hω
  have hω9 : ω ^ 9 = 1 := by rw [show 9 = 3 * 3 by rfl, pow_mul, hω3, one_pow]
  set j : Fin Tag.E6.rank := jOf (e i) with hj
  have hβ : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
      componentRoots (rootCharHom (a0 ω)) i := by
    rw [he i]
    exact ⟨isRoot_single _ _, by rw [hj, single_jOf_three]; exact dvd_zero 3, cls_single_jOf _⟩
  have hg := D.rootSL2_HSL_mem_rationalComponent hβ hω9
  have hgΓ : rootSL2 Tag.E6 L (Pi.single j 1) (HSL ω) ∈ D.S.Γ := D.rationalComponent_le_Γ i hg
  set y : ↥(D.Rc ω i) := ⟨⟨_, hgΓ⟩, hg⟩ with hy
  have hval : ((y : ↥D.S.Γ) : ModGL Tag.E6 L) =
      rootDiagUnit Tag.E6 (fun j' => ω ^ iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ)
        (Pi.single j' 1)) :=
    rootSL2_HSL_eq_rootDiagUnit' (isRoot_single _ _) ω
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (((y : ↥D.S.Γ) : ModGL Tag.E6 L)) ^ 3 = 1
    rw [hval, rootDiagUnit_pow]
    have : (fun j' => ω ^ iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ) (Pi.single j' 1)) ^ 3 =
        1 := by
      funext j'
      simp only [Pi.pow_apply, Pi.one_apply]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω3, one_zpow]
    rw [this, rootDiagUnit_one]
  have hy1 : y ≠ 1 := by
    intro h1
    have h2 : ((y : ↥D.S.Γ) : ModGL Tag.E6 L) = 1 := by rw [h1]; rfl
    rw [hval, ← rootDiagUnit_one (τ := Tag.E6) (K := L)] at h2
    have h3 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L) h2)
      j
    simp only [Pi.one_apply, iform_single_self_e6] at h3
    have h4 : orderOf ω ∣ 2 := by
      rw [← Int.natCast_dvd_natCast]
      exact (orderOf_dvd_iff_zpow_eq_one).2 (by simpa using h3)
    rw [hω] at h4
    omega
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hdvd := orderOf_dvd_natCard y
  rwa [hord] at hdvd

theorem Std8.mem_iSup_Rc_iff (D : Std8 L) {ω : Lˣ} {g : ↥D.S.Γ} :
    g ∈ ⨆ i, D.Rc ω i ↔ (g : ModGL Tag.E6 L) ∈
      ⨆ i : KernelComponent (rootCharHom (a0 ω)),
        rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i := by
  have hmap : (⨆ i, D.Rc ω i).map D.S.Γ.subtype =
      ⨆ i : KernelComponent (rootCharHom (a0 ω)),
        rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => D.map_Rc i
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem D.S.Γ.subtype_injective).symm

theorem Std8.pow_nine_of_commute_dV (D : Std8 L) {ω : Lˣ}
    (hω : orderOf ω = 3) {g : ↥D.S.Γ}
    (h : ∀ x : Fin Tag.E6.rank → ZMod 3, Commute (dV ω x) (g : ModGL Tag.E6 L)) : g ^ 9 = 1 := by
  have hmM : (g : ModGL Tag.E6 L) ∈ D.S.D.model := D.Γ_le_model g.2
  obtain ⟨hmem, hF⟩ := D.mem_model_iff.1 hmM
  have hT := mem_torusGroup_of_commute_dV hω hmem h
  have hmT : (g : ModGL Tag.E6 L) ∈ D.S.D.torus := D.mem_torus_iff.2 ⟨hT, hF⟩
  apply Subtype.ext
  simpa using D.pow_nine_of_mem_torus hmT

theorem Std8.isPGroup_centralizer_iSup_Rc (D : Std8 L) {ω : Lˣ}
    (hω : orderOf ω = 3) :
    IsPGroup 3 ↥(Subgroup.centralizer ((⨆ i, D.Rc ω i : Subgroup ↥D.S.Γ) : Set ↥D.S.Γ)) := by
  intro g
  refine ⟨2, ?_⟩
  have hcomm : ∀ x : Fin Tag.E6.rank → ZMod 3,
      Commute (dV ω x) (((g : ↥D.S.Γ)) : ModGL Tag.E6 L) := fun x => by
    have hx : (⟨dV ω x, D.dV_mem_Γ (pow_three_of_orderOf_three hω) x⟩ : ↥D.S.Γ) ∈
        ⨆ i, D.Rc ω i := D.mem_iSup_Rc_iff.2 (D.dV_mem_iSup_rationalComponent hω x)
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 g.2 _ hx)
  have h9 := D.pow_nine_of_commute_dV hω hcomm
  apply Subtype.ext
  simpa using h9

theorem Std8.glaPPrimeCore_z0_eq_bot
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) :
    GLAPPrimeCore 3 ↥(Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)) = ⊥ := by
  haveI := D.finite_Γ
  exact glaPPrimeCore_eq_bot_of_subnormal_family Nat.prime_three (fun i => D.Rc ω i)
    (fun i => (D.isComponentOf_Rc hω i).2.1) (fun i => (D.Rc_quasisimple_lie hω i).1)
    (fun i => D.three_dvd_card_Rc hω i)
    ((D.isPGroup_centralizer_iSup_Rc hω).to_le inf_le_right)

theorem Std8.exists_Rc_eq_of_glaPComponent
    (D : Std8 L) {ω : Lˣ}
    (hω : orderOf ω = 3) {J : Subgroup ↥D.S.Γ}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)) J) :
    ∃ i : KernelComponent (rootCharHom (a0 ω)), J = D.Rc ω i := by
  haveI := D.finite_Γ
  have hcoreOf : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)) = ⊥ := by
    unfold GLAPPrimeCoreOf
    rw [D.glaPPrimeCore_z0_eq_bot hω]
    exact Subgroup.map_bot _
  have hK : IsComponentOf J (fixSubgroup (MulAut.conj (D.z0 hω))) := by
    rw [fixSubgroup_conj_eq_centralizer_e6]
    exact isComponentOf_of_glaPComponent_core_bot hcoreOf hJ
  have hβ : ∀ c : ↥D.S.Γ, D.S.Γ.subtype ((MulAut.conj (D.z0 hω)) c) =
      rootDiagUnit Tag.E6 (a0 ω) * D.S.Γ.subtype c * (rootDiagUnit Tag.E6 (a0 ω))⁻¹ := by
    intro c
    rw [← D.coe_z0 hω]
    rfl
  obtain ⟨i, -, hKi⟩ := components_of_langSetup D.S Nat.prime_three D.S.Γ.subtype
    D.S.Γ.subtype_injective (Subgroup.range_subtype _) (MulAut.conj (D.z0 hω)) hβ
    (D.a0_mem_torus hω) (a0_pow_three hω) (a0_ne_one hω) (D.hTame hω) hK
  refine ⟨i, ?_⟩
  have h := congrArg (Subgroup.comap D.S.Γ.subtype) hKi
  rw [Subgroup.comap_map_eq_self_of_injective D.S.Γ.subtype_injective] at h
  exact h

theorem Std8.threeComponents
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) :
    ∃ T : Fin 3 → Subgroup ↥D.S.Γ, Function.Injective T ∧
      (∀ J : Subgroup ↥D.S.Γ,
        GLAPComponent 3 (Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)) J ↔ ∃ k, J = T k) ∧
      (∀ k, CFSG.Open.IsQuasisimple ↥(T k) ∧
        IsLieQuot ↥(T k) OuterFourInAux.IsU3EightIndex) ∧
      (∀ k l, k ≠ l → ∀ u ∈ T k, ∀ v ∈ T l, Commute u v) ∧ D.z0 hω ∈ ⨆ k, T k ∧
      IsPGroup 3 ↥(Subgroup.centralizer ((⨆ k, T k : Subgroup ↥D.S.Γ) : Set ↥D.S.Γ)) ∧
      GLAPPrimeCore 3 ↥(Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)) = ⊥ := by
  haveI := D.finite_Γ
  obtain ⟨e, -⟩ := exists_classEquiv hω
  set T : Fin 3 → Subgroup ↥D.S.Γ := fun k => D.Rc ω (e.symm k) with hT
  have hjoin : (⨆ k, T k) = ⨆ i, D.Rc ω i := e.symm.iSup_comp (g := fun i => D.Rc ω i)
  have hcomp : ∀ k, IsComponentOf (T k) (Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)) :=
    fun k => D.isComponentOf_Rc hω (e.symm k)
  have hq : ∀ k, CFSG.Open.IsQuasisimple ↥(T k) := fun k =>
    (D.Rc_quasisimple_lie hω (e.symm k)).1
  have hcore := D.glaPPrimeCore_z0_eq_bot hω
  refine ⟨T, ?_, fun J => ⟨fun hJ => ?_, fun ⟨k, hk⟩ => hk ▸
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_subnormal_quasisimple (hcomp k).2.1
      (hq k) hcore⟩,
    fun k => ⟨hq k, (D.Rc_quasisimple_lie hω (e.symm k)).2⟩,
    fun k l hkl u hu v hv => D.Rc_commute (e.symm.injective.ne hkl) hu hv, ?_,
    by rw [hjoin]; exact D.isPGroup_centralizer_iSup_Rc hω, hcore⟩
  ·
    intro k l hkl
    by_contra hne
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple_e6 (hq k)
    have hb : (b : ↥D.S.Γ) ∈ T l := hkl ▸ b.2
    exact hab (Subtype.ext (D.Rc_commute (e.symm.injective.ne hne) a.2 hb).eq)
  ·
    obtain ⟨i, hi⟩ := D.exists_Rc_eq_of_glaPComponent hω hJ
    exact ⟨e i, by rw [hi]; simp [hT]⟩
  ·
    rw [hjoin]
    exact D.mem_iSup_Rc_iff.2 (by simpa [Std8.z0] using D.dV_mem_iSup_rationalComponent hω x0)

end Three

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
