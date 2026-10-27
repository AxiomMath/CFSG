module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcRoots
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.GLTheoremA.T173X

variable {τ : Tag} {F : Type} [Field F]

theorem centralizer_rootDiagUnit_le_toralCentralizer
    (a : Fin τ.rank → Fˣ) {d : ↥(adjointGroup τ F)}
    (hd : (d : ModGL τ F) = rootDiagUnit τ a) :
    (Subgroup.centralizer ({d} : Set ↥(adjointGroup τ F))).map
        (adjointGroup τ F).subtype ≤ toralCentralizer τ F a := by
  rintro x ⟨g, hg, rfl⟩
  rw [mem_toralCentralizer]
  refine ⟨g.2, ?_⟩
  show rootDiagUnit τ a * (g : ModGL τ F) * (rootDiagUnit τ a)⁻¹ = (g : ModGL τ F)
  have hgd : d * g = g * d := Subgroup.mem_centralizer_iff.1 hg d (Set.mem_singleton d)
  have h2 : rootDiagUnit τ a * (g : ModGL τ F) = (g : ModGL τ F) * rootDiagUnit τ a := by
    simpa only [Subgroup.coe_mul, hd] using congrArg Subtype.val hgd
  rw [h2, mul_assoc, mul_inv_cancel, mul_one]

theorem map_centralizer_eq_toralCentralizer
    (a : Fin τ.rank → Fˣ) {d : ↥(adjointGroup τ F)}
    (hd : (d : ModGL τ F) = rootDiagUnit τ a) :
    (Subgroup.centralizer ({d} : Set ↥(adjointGroup τ F))).map
        (adjointGroup τ F).subtype = toralCentralizer τ F a := by
  refine le_antisymm (centralizer_rootDiagUnit_le_toralCentralizer a hd) ?_
  rintro x hx
  rw [mem_toralCentralizer] at hx
  obtain ⟨hxG, hxconj⟩ := hx
  refine Subgroup.mem_map.2 ⟨⟨x, hxG⟩, ?_, rfl⟩
  refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have h2 : rootDiagUnit τ a * x = x * rootDiagUnit τ a := by
    calc rootDiagUnit τ a * x
        = (rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by group
      _ = x * rootDiagUnit τ a := by rw [hxconj]
  exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hd, h2])

private theorem commutator_toralRootGroup_le_subgroupOf
    (a : Fin τ.rank → Fˣ)
    (hN : ((rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a)).Normal) :
    commutator ↥(toralRootGroup τ F a) ≤
      (rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a) := by
  haveI := hN
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  have htop : ((torusGroup τ F).subgroupOf (toralRootGroup τ F a)) ⊔
      ((rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := torusGroup τ F)
      (A' := rootSpan τ F (rootCharKernel a)) (B := toralRootGroup τ F a)
      (le_sup_left) (le_sup_right)]
    exact Subgroup.subgroupOf_self _
  obtain ⟨tx, htx, sx, hsx, hx'⟩ := (Subgroup.mem_sup_of_normal_right
    (s := (torusGroup τ F).subgroupOf (toralRootGroup τ F a))
    (t := (rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a))).1
    (htop ▸ Subgroup.mem_top x)
  obtain ⟨ty, hty, sy, hsy, hy'⟩ := (Subgroup.mem_sup_of_normal_right
    (s := (torusGroup τ F).subgroupOf (toralRootGroup τ F a))
    (t := (rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a))).1
    (htop ▸ Subgroup.mem_top y)
  have hsx1 : (QuotientGroup.mk sx : ↥(toralRootGroup τ F a) ⧸
      (rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a)) = 1 :=
    (QuotientGroup.eq_one_iff sx).2 hsx
  have hsy1 : (QuotientGroup.mk sy : ↥(toralRootGroup τ F a) ⧸
      (rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a)) = 1 :=
    (QuotientGroup.eq_one_iff sy).2 hsy
  have ex : (QuotientGroup.mk x : ↥(toralRootGroup τ F a) ⧸
      (rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a)) =
      QuotientGroup.mk tx := by
    conv_lhs => rw [← hx']
    rw [QuotientGroup.mk_mul ((rootSpan τ F (rootCharKernel a)).subgroupOf
      (toralRootGroup τ F a)), hsx1, mul_one]
  have ey : (QuotientGroup.mk y : ↥(toralRootGroup τ F a) ⧸
      (rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a)) =
      QuotientGroup.mk ty := by
    conv_lhs => rw [← hy']
    rw [QuotientGroup.mk_mul ((rootSpan τ F (rootCharKernel a)).subgroupOf
      (toralRootGroup τ F a)), hsy1, mul_one]
  have hcomm : (tx : ModGL τ F) * (ty : ModGL τ F) = (ty : ModGL τ F) * (tx : ModGL τ F) :=
    mul_comm_of_mem_diagonalGroup
      (torusGroup_le_diagonalGroup (Subgroup.mem_subgroupOf.1 htx))
      (torusGroup_le_diagonalGroup (Subgroup.mem_subgroupOf.1 hty))
  calc (QuotientGroup.mk x : ↥(toralRootGroup τ F a) ⧸
        (rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a)) *
        QuotientGroup.mk y
      = QuotientGroup.mk tx * QuotientGroup.mk ty := by rw [ex, ey]
    _ = QuotientGroup.mk (tx * ty) := (QuotientGroup.mk_mul _ tx ty).symm
    _ = QuotientGroup.mk (ty * tx) := congrArg QuotientGroup.mk (Subtype.ext hcomm)
    _ = QuotientGroup.mk ty * QuotientGroup.mk tx := QuotientGroup.mk_mul _ ty tx
    _ = QuotientGroup.mk y * QuotientGroup.mk x := by rw [ex, ey]

theorem commutator_toralRootGroup_le_rootSpan
    (a : Fin τ.rank → Fˣ) :
    ⁅toralRootGroup τ F a, toralRootGroup τ F a⁆ ≤ rootSpan τ F (rootCharKernel a) := by
  have hSM : rootSpan τ F (rootCharKernel a) ≤ toralRootGroup τ F a := le_sup_right
  have hN : ((rootSpan τ F (rootCharKernel a)).subgroupOf (toralRootGroup τ F a)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).2 ?_
    refine sup_le ?_ (Subgroup.le_normalizer)
    exact torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have h := Subgroup.map_mono (f := (toralRootGroup τ F a).subtype)
    (commutator_toralRootGroup_le_subgroupOf a hN)
  rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hSM] at h

private theorem map_stdLayer_le_toralCentralizer {p : ℕ} {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d) :
    (stdLayer d).map (adjointGroup τ F).subtype ≤ toralCentralizer τ F a := by
  have h : (stdLayer d).map (adjointGroup τ F).subtype ≤
      (Subgroup.centralizer ({d} : Set ↥(adjointGroup τ F))).map (adjointGroup τ F).subtype :=
    Subgroup.map_mono hstd.2.2.2.1.1
  rwa [map_centralizer_eq_toralCentralizer a hd] at h

private theorem isComponent_stdLayer_subgroupOf_toralCentralizer {p : ℕ} {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d) :
    CFSG.IsComponent (((stdLayer d).map (adjointGroup τ F).subtype).subgroupOf
      (toralCentralizer τ F a)) := by
  have hLmX := map_stdLayer_le_toralCentralizer hd hstd
  have hsub : CFSG.Open.IsSubnormal ((stdLayer d).map (adjointGroup τ F).subtype)
      (toralCentralizer τ F a) := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSubnormal_map
      hstd.2.2.2.1.2.1 (adjointGroup τ F).subtype (adjointGroup τ F).subtype_injective
    rwa [map_centralizer_eq_toralCentralizer a hd] at h
  have hqLm : CFSG.Open.IsQuasisimple ↥((stdLayer d).map (adjointGroup τ F).subtype) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective (stdLayer d) (adjointGroup τ F).subtype
        (adjointGroup τ F).subtype_injective) hstd.2.2.2.1.2.2
  exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLmX).1
    ((CFSG.Assembly.isComponentOf_iff_open).2 ⟨hLmX, hsub, hqLm⟩)

private theorem map_stdLayer_le_rootSpan_of_le_toralRootGroup {p : ℕ} {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hstd : IsStdElt p (TableBExc.torusPow τ F p) d)
    (hLmM : (stdLayer d).map (adjointGroup τ F).subtype ≤ toralRootGroup τ F a) :
    (stdLayer d).map (adjointGroup τ F).subtype ≤ rootSpan τ F (rootCharKernel a) := by
  have hcomm : commutator ↥(stdLayer d) = ⊤ := hstd.2.2.2.1.2.2.1
  rw [commutator_def] at hcomm
  have hperf : ⁅stdLayer d, stdLayer d⁆ = stdLayer d := by
    have h := congrArg (Subgroup.map (stdLayer d).subtype) hcomm
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have h1 : (stdLayer d).map (adjointGroup τ F).subtype =
      ⁅(stdLayer d).map (adjointGroup τ F).subtype,
        (stdLayer d).map (adjointGroup τ F).subtype⁆ := by
    rw [← Subgroup.map_commutator (stdLayer d) (stdLayer d) (adjointGroup τ F).subtype, hperf]
  calc (stdLayer d).map (adjointGroup τ F).subtype
      = ⁅(stdLayer d).map (adjointGroup τ F).subtype,
          (stdLayer d).map (adjointGroup τ F).subtype⁆ := h1
    _ ≤ ⁅toralRootGroup τ F a, toralRootGroup τ F a⁆ := Subgroup.commutator_mono hLmM hLmM
    _ ≤ rootSpan τ F (rootCharKernel a) := commutator_toralRootGroup_le_rootSpan a

private theorem false_of_commutator_stdLayer_toralRootGroup_eq_bot {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Fˣ} {d : ↥(adjointGroup τ F)}
    (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d)
    (hV : p ^ 2 ≤ Nat.card (TableBExc.torusPow τ F p))
    (hKM : ⁅((stdLayer d).map (adjointGroup τ F).subtype).subgroupOf (toralCentralizer τ F a),
        (toralRootGroup τ F a).subgroupOf (toralCentralizer τ F a)⁆ = ⊥) : False := by
  have hLmX := map_stdLayer_le_toralCentralizer hd hstd
  have hTle : torusGroup τ F ≤ toralCentralizer τ F a := torusGroup_le_toralCentralizer a
  have hTcent : torusGroup τ F ≤
      Subgroup.centralizer ((stdLayer d).map (adjointGroup τ F).subtype : Set (ModGL τ F)) := by
    have h1 : ⁅((stdLayer d).map (adjointGroup τ F).subtype).subgroupOf (toralCentralizer τ F a),
        (torusGroup τ F).subgroupOf (toralCentralizer τ F a)⁆ = ⊥ :=
      bot_unique ((Subgroup.commutator_mono le_rfl
        (Subgroup.subgroupOf_mono _ le_sup_left)).trans hKM.le)
    have h := congrArg (Subgroup.map (toralCentralizer τ F a).subtype) h1
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLmX, inf_eq_left.2 hTle,
      Subgroup.map_bot] at h
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hVle : TableBExc.torusPow τ F p ≤ Subgroup.zpowers d := by
    rw [← hstd.2.2.2.2]
    refine le_inf le_rfl ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hvT : (v : ModGL τ F) ∈ torusGroup τ F := (TableBExc.mem_torusPow.1 hv).1
    have hvC := hTcent hvT
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hvC (y : ModGL τ F)
      (Subgroup.mem_map_of_mem _ hy))
  have hEq : TableBExc.torusPow τ F p = Subgroup.zpowers d :=
    le_antisymm hVle (Subgroup.zpowers_le.2 hstd.1)
  have hcard : Nat.card (TableBExc.torusPow τ F p) = p := by
    rw [hEq, Nat.card_zpowers]
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hstd.2.2.1 hstd.2.1
  have h2 : p ^ 2 ≤ p := by rwa [hcard] at hV
  have h3 := hp.two_le
  nlinarith

theorem stdLayer_le_rootSpan_rootCharKernel
    [Finite F] {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d)
    (hV : p ^ 2 ≤ Nat.card (TableBExc.torusPow τ F p)) :
    stdLayer d ≤ (rootSpan τ F (rootCharKernel a)).subgroupOf (adjointGroup τ F) := by
  classical
  haveI : Finite (ModGL τ F) := finite_modGL
  haveI : Finite ↥(toralCentralizer τ F a) := Subtype.finite
  rcases CFSG.LocalCores.component_normal_subgroup
    (isComponent_stdLayer_subgroupOf_toralCentralizer hd hstd)
    (toralRootGroup_normal (τ := τ) (K := F) a) with hKM | hKM
  · have hLmM : (stdLayer d).map (adjointGroup τ F).subtype ≤ toralRootGroup τ F a := by
      intro x hx
      exact hKM (show (⟨x, map_stdLayer_le_toralCentralizer hd hstd hx⟩ :
        ↥(toralCentralizer τ F a)) ∈ ((stdLayer d).map (adjointGroup τ F).subtype).subgroupOf
          (toralCentralizer τ F a) from hx)
    intro x hx
    exact Subgroup.mem_subgroupOf.2
      (map_stdLayer_le_rootSpan_of_le_toralRootGroup hstd hLmM (Subgroup.mem_map_of_mem _ hx))
  · exact (false_of_commutator_stdLayer_toralRootGroup_eq_bot hp hd hstd hV hKM).elim

theorem rootCharKernel_nonempty_of_isStdElt
    [Finite F] {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d)
    (hV : p ^ 2 ≤ Nat.card (TableBExc.torusPow τ F p)) :
    (rootCharKernel a).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hle := stdLayer_le_rootSpan_rootCharKernel (F := F) (τ := τ) hp (a := a) hd hstd hV
  have hbot : (rootSpan τ F (rootCharKernel a)).subgroupOf (adjointGroup τ F) = ⊥ := by
    rw [hne, show rootSpan τ F (∅ : Set (Fin τ.rank → ℤ)) = ⊥ from by simp [rootSpan],
      Subgroup.bot_subgroupOf]
  rw [hbot] at hle
  have hLbot : stdLayer d = ⊥ := le_bot_iff.1 hle
  have hq : CFSG.Open.IsQuasisimple ↥(stdLayer d) := hstd.2.2.2.1.2.2
  have hntq : Nontrivial (↥(stdLayer d) ⧸ Subgroup.center ↥(stdLayer d)) := hq.2.toNontrivial
  have hnt : Nontrivial ↥(stdLayer d) :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥(stdLayer d))).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot (stdLayer d)).mp hnt hLbot

theorem rootDiagUnit_mem_adjointGroup_of_exc
    [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hp3 : τ = .E6 → p ≠ 3)
    {b : Fin τ.rank → Fˣ} (hb : ∀ i, b i ^ p = 1) :
    rootDiagUnit τ b ∈ adjointGroup τ F := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact CFSG.ComponentClassification.CatFC.DS81.Ex.rootDiagUnit_mem_adjointGroup_of_charTwo
      (by simp) (ringChar.eq F 2) b
  · refine CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (x := rootDiagUnit .E6 b) ?_
    exact TableBExc.fullp_E6 hp.one_lt
      ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm (hp3 rfl))) b hb
  · exact CFSG.ComponentClassification.CatFC.DS81.Ex.rootDiagUnit_mem_adjointGroup_of_charTwo
      (by simp) (ringChar.eq F 2) b
  · exact CFSG.ComponentClassification.CatFC.DS81.Ex.rootDiagUnit_mem_adjointGroup_of_charTwo
      (by simp) (ringChar.eq F 2) b

theorem exists_rootDiagUnit_eq_of_mem_torusPow
    {p : ℕ} {g : ↥(adjointGroup τ F)} (hg : g ∈ TableBExc.torusPow τ F p) :
    ∃ a : Fin τ.rank → Fˣ, (∀ i, a i ^ p = 1) ∧ (g : ModGL τ F) = rootDiagUnit τ a := by
  obtain ⟨a, ha⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup
    (TableBExc.mem_torusPow.1 hg).1
  have hap' : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
    rw [← rootDiagUnit_pow, ← ha, ← Subgroup.coe_pow, hg.2, OneMemClass.coe_one,
      rootDiagUnit_one]
  have hap : a ^ p = 1 := rootDiagUnit_injective hap'
  exact ⟨a, fun i => by simpa using congrFun hap i, ha⟩

private theorem rootSpan_le_centralizer_rootDiagUnit
    {a : Fin τ.rank → Fˣ} {b : Fin τ.rank → Fˣ}
    (hbKer : ∀ α ∈ rootCharKernel a, rootChar b α = 1) :
    rootSpan τ F (rootCharKernel a) ≤
      Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ F)) := by
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hconj := rootDiagUnit_conj_pinnedX b hα.1 c
  rw [hbKer α hα, Units.val_one, one_mul] at hconj
  calc rootDiagUnit τ b * pinnedX τ F α c
      = (rootDiagUnit τ b * pinnedX τ F α c * (rootDiagUnit τ b)⁻¹) * rootDiagUnit τ b := by
        group
    _ = pinnedX τ F α c * rootDiagUnit τ b := by rw [hconj]

theorem rootDiagUnit_mem_zpowers_of_rootChar_eq_one
    [Finite F] {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d)
    (hV : p ^ 2 ≤ Nat.card (TableBExc.torusPow τ F p))
    {b : Fin τ.rank → Fˣ} (hb : ∀ i, b i ^ p = 1)
    (hbadj : rootDiagUnit τ b ∈ adjointGroup τ F)
    (hbKer : ∀ α ∈ rootCharKernel a, rootChar b α = 1) :
    rootDiagUnit τ b ∈ Subgroup.zpowers (rootDiagUnit τ a) := by
  classical
  have hSC := rootSpan_le_centralizer_rootDiagUnit hbKer
  have hle := stdLayer_le_rootSpan_rootCharKernel (F := F) (τ := τ) hp (a := a) hd hstd hV
  have hvp : (⟨rootDiagUnit τ b, hbadj⟩ : ↥(adjointGroup τ F)) ^ p = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, OneMemClass.coe_one, rootDiagUnit_pow]
    have hbp : b ^ p = 1 := funext hb
    rw [hbp, rootDiagUnit_one]
  have hvV : (⟨rootDiagUnit τ b, hbadj⟩ : ↥(adjointGroup τ F)) ∈
      TableBExc.torusPow τ F p :=
    TableBExc.mem_torusPow.2 ⟨CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup
      b hbadj, hvp⟩
  have hvcent : (⟨rootDiagUnit τ b, hbadj⟩ : ↥(adjointGroup τ F)) ∈
      Subgroup.centralizer (stdLayer d : Set ↥(adjointGroup τ F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyS : (y : ModGL τ F) ∈ rootSpan τ F (rootCharKernel a) :=
      Subgroup.mem_subgroupOf.1 (hle hy)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hSC hyS) (rootDiagUnit τ b)
      (Set.mem_singleton _)).symm
  have hmem : (⟨rootDiagUnit τ b, hbadj⟩ : ↥(adjointGroup τ F)) ∈ Subgroup.zpowers d := by
    rw [← hstd.2.2.2.2]
    exact Subgroup.mem_inf.2 ⟨hvV, hvcent⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have hcoe : ((d ^ k : ↥(adjointGroup τ F)) : ModGL τ F) = (rootDiagUnit τ a) ^ k := by
    rw [Subgroup.coe_zpow, hd]
  rw [← hcoe, hk]

theorem card_torusPow_exc
    [Finite F] [CharP F 2] {n p : ℕ} (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n - 1) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hp3 : τ = .E6 → p ≠ 3) :
    Nat.card (TableBExc.torusPow τ F p) = p ^ τ.rank := by
  have hpq' : p ∣ Nat.card F - 1 := by rw [hn]; exact hpq
  rcases hτ with rfl | rfl | rfl | rfl
  · rw [show TableBExc.torusPow Tag.F4 F p = TableBF4.torusPow F p from rfl]
    exact TableBF4.card_torusPow hp hpq'
  · exact TableBExc.card_torusPow_E6 hp (hp3 rfl) hpq'
  · exact TableBExc.card_torusPow_E7 hp hpq'
  · exact TableBExc.card_torusPow_E8 hp hpq'

theorem two_le_rank_exc (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : 2 ≤ τ.rank := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide

theorem rootCharKernel_nonempty_of_isStdElt_of_exc
    [Finite F] [CharP F 2] {n p : ℕ} (hn : Nat.card F = 2 ^ n) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hp3 : τ = .E6 → p ≠ 3) :
    (rootCharKernel a).Nonempty := by
  refine rootCharKernel_nonempty_of_isStdElt hp hd hstd ?_
  rw [card_torusPow_exc hn hp hpq hτ hp3]
  exact Nat.pow_le_pow_right hp.pos (two_le_rank_exc hτ)

theorem rootDiagUnit_mem_zpowers_of_rootChar_eq_one_of_exc
    [Finite F] [CharP F 2] {n p : ℕ} (hn : Nat.card F = 2 ^ n) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hp3 : τ = .E6 → p ≠ 3)
    {b : Fin τ.rank → Fˣ} (hb : ∀ i, b i ^ p = 1)
    (hbKer : ∀ α ∈ rootCharKernel a, rootChar b α = 1) :
    rootDiagUnit τ b ∈ Subgroup.zpowers (rootDiagUnit τ a) := by
  refine rootDiagUnit_mem_zpowers_of_rootChar_eq_one hp hd hstd ?_ hb
    (rootDiagUnit_mem_adjointGroup_of_exc hp hτ hp3 hb) hbKer
  rw [card_torusPow_exc hn hp hpq hτ hp3]
  exact Nat.pow_le_pow_right hp.pos (two_le_rank_exc hτ)

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
