module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import CFSG.LieType.Steinberg.CentralExt.PSLAlternating
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Mult
public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.Quasithin.SteinbergBYEvenLinearSymplecticTwoThreeControl
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.SteinbergBICommonNormalizerTools
public import CFSG.Quasithin.SteinbergBIEvenLinearThreeThreeSylowAction
public import CFSG.Quasithin.SteinbergBIEvenSymplecticTwoThreeTriangular
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.RankThree.PartTwo.Sec19.Item194Used

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.ClassicalEven
  CFSG.SectionRank.ClassicalOdd CFSG.StandardType CFSG.Blueprint Matrix

section Torus

variable {F : Type} [Field F] [Fintype F]

def diagVecSucc (k : ℕ) (u : Fin k → Fˣ) : Fin (k + 1) → Fˣ :=
  Fin.cons ((∏ i, u i)⁻¹) u

def diagVecSuccHom (k : ℕ) : (Fin k → Fˣ) →* (Fin (k + 1) → Fˣ) where
  toFun := diagVecSucc k
  map_one' := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [diagVecSucc]
    · intro j
      simp [diagVecSucc]
  map_mul' u v := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [diagVecSucc, Pi.mul_apply, Finset.prod_mul_distrib, mul_comm]
    · intro j
      simp [diagVecSucc, Pi.mul_apply]

theorem prod_diagVecSucc (k : ℕ) (u : Fin k → Fˣ) : ∏ i, diagVecSucc k u i = 1 := by
  rw [diagVecSucc, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact inv_mul_cancel _

theorem diagVecSucc_injective (k : ℕ) : Function.Injective (diagVecSucc (F := F) k) := by
  intro u v h
  funext i
  have := congrFun h i.succ
  simpa [diagVecSucc] using this

def diagVecOne (k : ℕ) (u : Fin k → Fˣ) : Fin (k + 2) → Fˣ :=
  Fin.cons 1 (diagVecSucc k u)

def diagVecOneHom (k : ℕ) : (Fin k → Fˣ) →* (Fin (k + 2) → Fˣ) where
  toFun := diagVecOne k
  map_one' := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [diagVecOne]
    · intro j
      refine Fin.cases ?_ ?_ j
      · simp [diagVecOne, diagVecSucc]
      · intro l
        simp [diagVecOne, diagVecSucc]
  map_mul' u v := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [diagVecOne]
    · intro j
      refine Fin.cases ?_ ?_ j
      · simp [diagVecOne, diagVecSucc, Finset.prod_mul_distrib, mul_comm]
      · intro l
        simp [diagVecOne, diagVecSucc, Pi.mul_apply]

theorem prod_diagVecOne (k : ℕ) (u : Fin k → Fˣ) : ∏ i, diagVecOne k u i = 1 := by
  rw [diagVecOne, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul]
  exact prod_diagVecSucc k u

theorem diagVecOne_injective (k : ℕ) : Function.Injective (diagVecOne (F := F) k) := by
  intro u v h
  funext i
  have := congrFun h (Fin.succ (Fin.succ i))
  simpa [diagVecOne, diagVecSucc] using this

def rootsPiHom (k r : ℕ) : (Fin k → rootsOfUnity r F) →* (Fin k → Fˣ) :=
  MonoidHom.pi fun i =>
    (Subgroup.subtype (rootsOfUnity r F)).comp
      (Pi.evalMonoidHom (fun _ => rootsOfUnity r F) i)

theorem rootsPiHom_injective (k r : ℕ) : Function.Injective (rootsPiHom (F := F) k r) := by
  intro u v h
  funext i
  have := congrFun h i
  simpa [rootsPiHom] using this

def diagTorusGL (k r : ℕ) : Subgroup (GL (Fin (k + 2)) F) :=
  (torusDiag.comp ((diagVecOneHom (F := F) k).comp (rootsPiHom (F := F) k r))).range

theorem diagTorusGL_le_SL (k r : ℕ) : diagTorusGL (F := F) k r ≤ StatedSL (k + 2) F := by
  rintro _ ⟨u, rfl⟩
  refine torusDiag_mem_SL ?_
  show ∏ i, diagVecOne k (fun j => ((u j : rootsOfUnity r F) : Fˣ)) i = 1
  exact prod_diagVecOne k _

theorem card_diagTorusGL (k r : ℕ) [NeZero r] (hrd : r ∣ Nat.card F - 1) :
    Nat.card (diagTorusGL (F := F) k r) = r ^ k := by
  have hinj : Function.Injective
      ⇑(torusDiag.comp ((diagVecOneHom (F := F) k).comp (rootsPiHom (F := F) k r))) :=
    torusDiag_injective.comp ((diagVecOne_injective k).comp (rootsPiHom_injective k r))
  rw [diagTorusGL, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (K := ⊤) (f := torusDiag.comp
      ((diagVecOneHom (F := F) k).comp (rootsPiHom (F := F) k r))) hinj,
    Subgroup.card_top, Nat.card_fun, Nat.card_fin]
  rw [CFSG.LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd r,
    Nat.gcd_eq_left (by rwa [← Nat.card_eq_fintype_card])]

theorem isElemAbelian_diagTorusGL (k r : ℕ) (hr : r.Prime) :
    IsElemAbelian r (diagTorusGL (F := F) k r) := by
  have htop : IsElemAbelian r (⊤ : Subgroup (Fin k → rootsOfUnity r F)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (funext fun i => mul_comm (a.val i) (b.val i))
    · funext i
      exact Subtype.ext (by
        simpa using (mem_rootsOfUnity r ((x i : rootsOfUnity r F) : Fˣ)).mp (x i).2)
  rw [diagTorusGL, MonoidHom.range_eq_map]
  exact htop.map _

noncomputable def rootSubgroupGL (d : ℕ) : Subgroup (GL (Fin d) F) :=
  (linHom d 1 1).range

theorem mem_rootSubgroupGL {d : ℕ} {x : GL (Fin d) F} :
    x ∈ rootSubgroupGL (F := F) d ↔
      ∃ s : Multiplicative (Fin 1 × Fin 1 → F), linHom (K := F) d 1 1 s = x :=
  MonoidHom.mem_range

theorem rootSubgroupGL_le_SL (d : ℕ) [CharP F 2] : rootSubgroupGL (F := F) d ≤ StatedSL d F := by
  rintro _ ⟨s, rfl⟩
  refine Subgroup.subset_closure ?_
  refine det_eq_one_of_pow_char (p := 2) ?_
  have hs : s * s = 1 := by
    apply Multiplicative.toAdd.injective
    change s.toAdd + s.toAdd = 0
    funext i
    exact CharTwo.add_self_eq_zero _
  have h2 : (linHom (K := F) d 1 1 s) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hs, map_one]
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]

theorem card_rootSubgroupGL {d : ℕ} (hd : 2 ≤ d) :
    Nat.card (rootSubgroupGL (F := F) d) = Nat.card F := by
  rw [rootSubgroupGL, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (K := ⊤) (f := linHom (K := F) d 1 1)
      (linHom_injective (by omega)), Subgroup.card_top,
    Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (Fin 1 × Fin 1 → F) ≃ (Fin 1 × Fin 1 → F)),
    Nat.card_fun, Nat.card_prod]
  norm_num

theorem isPGroup_two_rootSubgroupGL (d : ℕ) [CharP F 2] : IsPGroup 2 (rootSubgroupGL (F := F) d) := by
  refine IsPGroup.iff_orderOf.2 fun x => ?_
  obtain ⟨s, hs⟩ := x.2
  have hs' : s * s = 1 := by
    apply Multiplicative.toAdd.injective
    change s.toAdd + s.toAdd = 0
    funext i
    exact CharTwo.add_self_eq_zero _
  have h2 : (linHom (K := F) d 1 1 s) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hs', map_one]
  have hdvd : orderOf x ∣ 2 := by
    rw [← Subgroup.orderOf_coe x, ← hs]
    exact orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by rw [pow_zero]; exact h⟩
  · exact ⟨1, by rw [pow_one]; exact h⟩

theorem rootSubgroupGL_subgroupOf_inf_scalars (d : ℕ) (hd : 2 ≤ d) :
    (rootSubgroupGL (F := F) d).subgroupOf (StatedSL d F) ⊓
      (StatedScalars (Fin d) F).subgroupOf (StatedSL d F) = ⊥ := by
  haveI : NeZero d := ⟨by omega⟩
  rw [eq_bot_iff]
  rintro z ⟨hzX, hzK⟩
  rw [Subgroup.mem_bot]
  have hzX' : (z : GL (Fin d) F) ∈ rootSubgroupGL (F := F) d := hzX
  have hzK' : (z : GL (Fin d) F) ∈ StatedScalars (Fin d) F := hzK
  obtain ⟨s, hs⟩ := hzX'
  obtain ⟨c, hc⟩ := hzK'
  have h01 : (0 : Fin d) ≠ 1 := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
    omega
  have hs0 : s.toAdd ⟨0, 0⟩ = 0 := by
    have h01' : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
      intro h
      exact h01 (Fin.ext (by simpa using congrArg Fin.val h))
    have heq : linHom (K := F) d 1 1 s = GeneralLinearGroup.scalar (Fin d) c := hs.trans hc.symm
    have h1 := congrFun (congrFun (congrArg
      (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) heq)
      ⟨0, by omega⟩) ⟨1, by omega⟩
    rw [linHom, coe_glOfAdd, Matrix.add_apply] at h1
    have hL : (1 : Matrix (Fin d) (Fin d) F) ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 := by
      rw [Matrix.one_apply, if_neg h01']
    have hR : (GeneralLinearGroup.scalar (Fin d) c :
        Matrix (Fin d) (Fin d) F) ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 := by
      rw [GeneralLinearGroup.coe_scalar]
      simp [h01']
    rw [hL, hR, zero_add] at h1
    simpa [linBlock] using h1
  have hs1 : s = 1 := by
    apply Multiplicative.toAdd.injective
    funext x
    obtain ⟨i, j⟩ := x
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 0 := Fin.ext (by omega)
    subst hi
    subst hj
    exact hs0
  apply Subtype.ext
  rw [← hs, hs1, map_one]
  rfl

@[expose] noncomputable def rootClassSubgroup (n : ℕ) : Subgroup (StatedProj (StatedSL n F)) :=
  ((rootSubgroupGL (F := F) n).subgroupOf (StatedSL n F)).map
    (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)))

theorem card_rootClassSubgroup [CharP F 2] {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (rootClassSubgroup (F := F) n) = Nat.card F := by
  let π : ↥(StatedSL n F) →* StatedProj (StatedSL n F) :=
    QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))
  have hX_SL : rootSubgroupGL (F := F) n ≤ StatedSL n F := rootSubgroupGL_le_SL n
  have hbot : (rootSubgroupGL (F := F) n).subgroupOf (StatedSL n F) ⊓ π.ker = ⊥ := by
    rw [show π.ker = (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) from
      QuotientGroup.ker_mk' _]
    exact rootSubgroupGL_subgroupOf_inf_scalars n hn
  rw [rootClassSubgroup,
    CFSG.Quasithin.Ch1Sec3.card_map_of_inf_ker_eq_bot (φ := π) (P :=
      (rootSubgroupGL (F := F) n).subgroupOf (StatedSL n F)) hbot,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_SL).toEquiv]
  exact card_rootSubgroupGL hn

theorem rootClassSubgroup_ne_bot [CharP F 2] {n : ℕ} (hn : 2 ≤ n) :
    rootClassSubgroup (F := F) n ≠ ⊥ := by
  have hcard := card_rootClassSubgroup (F := F) hn
  have hgt : 1 < Nat.card (rootClassSubgroup (F := F) n) := by
    rw [hcard, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact (Subgroup.one_lt_card_iff_ne_bot _).1 hgt

theorem isPGroup_two_rootClassSubgroup [CharP F 2] {n : ℕ} (hn : 2 ≤ n) :
    IsPGroup 2 (rootClassSubgroup (F := F) n) := by
  have hX_SL : rootSubgroupGL (F := F) n ≤ StatedSL n F := rootSubgroupGL_le_SL n
  have hXSL2 : IsPGroup 2 ((rootSubgroupGL (F := F) n).subgroupOf (StatedSL n F)) :=
    (isPGroup_two_rootSubgroupGL n).of_equiv (Subgroup.subgroupOfEquivOfLe hX_SL).symm
  exact hXSL2.map _

theorem diagonal_mul_linBlock_one_one {k : ℕ} (v : Fin (k + 2) → Fˣ) (s : Fin 1 × Fin 1 → F) :
    diagonal (fun i => (v i : F)) * linBlock (k + 2) 1 1 s *
        diagonal (fun i => (((v i)⁻¹ : Fˣ) : F)) =
      linBlock (k + 2) 1 1 (fun _ => (v 0 : F) * s ⟨0, 0⟩ * (((v 1)⁻¹ : Fˣ) : F)) := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply_eq, linBlock,
    Matrix.of_apply]
  by_cases h : i.val < 1 ∧ 1 ≤ j.val ∧ j.val < 2
  · have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp h.1)
    have hj : j = 1 := Fin.ext (by
      have h1 := h.2.1
      have h2 := h.2.2
      have hv : j.val = 1 := by omega
      simpa using hv)
    subst hi
    subst hj
    simp [h]
  · simp only [dif_neg h, mul_zero, zero_mul]

theorem torusDiag_mul_linHom_mul_inv (k : ℕ) (v : Fin (k + 2) → Fˣ)
    (s : Multiplicative (Fin 1 × Fin 1 → F)) :
    torusDiag v * linHom (K := F) (k + 2) 1 1 s * torusDiag (fun i => (v i)⁻¹) =
      linHom (K := F) (k + 2) 1 1
        (Multiplicative.ofAdd (fun _ => (v 0 : F) * s.toAdd ⟨0, 0⟩ *
          (((v 1)⁻¹ : Fˣ) : F))) := by
  apply Units.ext
  simp only [Units.val_mul, coe_torusDiag, linHom, coe_glOfAdd]
  have hD : (diagonal fun i => (v i : F)) *
      (diagonal fun i => (((v i)⁻¹ : Fˣ) : F)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h : ((v i : Fˣ) : F) * (((v i)⁻¹ : Fˣ) : F) = ((1 : Fˣ) : F) := by
      rw [← Units.val_mul, mul_inv_cancel]
    simpa using h
  rw [mul_add, add_mul, mul_one, show (diagonal fun i => (v i : F)) *
      (diagonal fun i => (((v i)⁻¹ : Fˣ) : F)) = 1 from hD,
    diagonal_mul_linBlock_one_one]
  rfl

theorem diagTorusGL_le_normalizer_rootSubgroupGL (k r : ℕ) :
    diagTorusGL (F := F) k r ≤
      Subgroup.normalizer (rootSubgroupGL (F := F) (k + 2) : Set (GL (Fin (k + 2)) F)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro _ ⟨u, rfl⟩ x hx
  obtain ⟨s, hs⟩ := hx
  set v : Fin (k + 2) → Fˣ := diagVecOne k (fun j => ((u j : rootsOfUnity r F) : Fˣ)) with hv
  change torusDiag v * x * (torusDiag v)⁻¹ ∈ rootSubgroupGL (k + 2)
  refine ⟨Multiplicative.ofAdd (fun _ =>
    (v 0 : F) * s.toAdd ⟨0, 0⟩ * (((v 1)⁻¹ : Fˣ) : F)), ?_⟩
  rw [← hs, ← map_inv (torusDiag (K := F))]
  exact (torusDiag_mul_linHom_mul_inv k v s).symm

theorem exists_elemAbelian_le_normalizer_statedProj_of (d r k : ℕ) [CharP F 2] (hd : 2 ≤ d)
    (hr : r.Prime) (hr2 : r ≠ 2) (D0 : Subgroup (GL (Fin d) F))
    (hD_SL : D0 ≤ StatedSL d F)
    (hD_scal : ∀ z : ↥(StatedSL d F), (z : GL (Fin d) F) ∈ D0 →
      (z : GL (Fin d) F) ∈ StatedScalars (Fin d) F → (z : GL (Fin d) F) = 1)
    (hDcard : Nat.card D0 = r ^ k) (hDab : IsElemAbelian r D0)
    (hDnorm : D0 ≤ Subgroup.normalizer (rootSubgroupGL (F := F) d : Set (GL (Fin d) F))) :
    ∃ E X : Subgroup (StatedProj (StatedSL d F)),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian r E ∧ Nat.card E = r ^ k ∧
        E ≤ Subgroup.normalizer (X : Set (StatedProj (StatedSL d F))) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hX_SL : rootSubgroupGL (F := F) d ≤ StatedSL d F := rootSubgroupGL_le_SL d
  let π : ↥(StatedSL d F) →* StatedProj (StatedSL d F) :=
    QuotientGroup.mk' ((StatedScalars (Fin d) F).subgroupOf (StatedSL d F))
  let DSL : Subgroup ↥(StatedSL d F) := D0.subgroupOf _
  let XSL : Subgroup ↥(StatedSL d F) := (rootSubgroupGL (F := F) d).subgroupOf _
  have hπker : π.ker = (StatedScalars (Fin d) F).subgroupOf (StatedSL d F) :=
    QuotientGroup.ker_mk' _
  have hDbot : DSL ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzD, hzK⟩
    have hzD' : (z : GL (Fin d) F) ∈ D0 := hzD
    rw [hπker] at hzK
    have hz1 : (z : GL (Fin d) F) = 1 := hD_scal z hzD' hzK
    exact Subtype.ext hz1
  have hXbot : XSL ⊓ π.ker = ⊥ := by
    rw [hπker]
    exact rootSubgroupGL_subgroupOf_inf_scalars d hd
  have hnorm : DSL ≤ Subgroup.normalizer (XSL : Set ↥(StatedSL d F)) := by
    rw [Subgroup.le_normalizer_iff] at hDnorm ⊢
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb ⊢
    simpa using hDnorm (a : GL (Fin d) F) ha (b : GL (Fin d) F) hb
  refine ⟨DSL.map π, XSL.map π, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact rootClassSubgroup_ne_bot (F := F) hd
  ·
    exact isPGroup_two_rootClassSubgroup (F := F) hd
  ·
    have hDSL : IsElemAbelian r DSL := hDab.subgroupOf (StatedSL d F)
    exact hDSL.map π
  ·
    rw [CFSG.Quasithin.Ch1Sec3.card_map_of_inf_ker_eq_bot (φ := π) (P := DSL) hDbot,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_SL).toEquiv, hDcard]
  ·
    exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map π)

theorem exists_elemAbelian_le_normalizer_statedProj (k r : ℕ) [CharP F 2] (hr : r.Prime)
    (hr2 : r ≠ 2) (hrd : r ∣ Nat.card F - 1) :
    ∃ E X : Subgroup (StatedProj (StatedSL (k + 2) F)),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian r E ∧ Nat.card E = r ^ k ∧
        E ≤ Subgroup.normalizer (X : Set (StatedProj (StatedSL (k + 2) F))) := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  refine exists_elemAbelian_le_normalizer_statedProj_of (k + 2) r k (by omega) hr hr2
    (diagTorusGL (F := F) k r) (diagTorusGL_le_SL k r) ?_ (card_diagTorusGL k r hrd)
    (isElemAbelian_diagTorusGL k r hr) (diagTorusGL_le_normalizer_rootSubgroupGL k r)
  rintro z hzD hzK
  obtain ⟨u, hu⟩ := hzD
  obtain ⟨c, hc⟩ := hzK
  have h00 : (c : F) = 1 := by
    have heq : torusDiag (K := F) (diagVecOne k
        (fun j => ((u j : rootsOfUnity r F) : Fˣ))) =
        GeneralLinearGroup.scalar (Fin (k + 2)) c := hu.trans hc.symm
    have h1 : (((diagVecOne k (fun j => ((u j : rootsOfUnity r F) : Fˣ)))
        ⟨0, by omega⟩ : Fˣ) : F) = (c : F) := by
      have h2 := congrFun (congrFun (congrArg
        (fun x : GL (Fin (k + 2)) F => (x : Matrix (Fin (k + 2)) (Fin (k + 2)) F)) heq)
        ⟨0, by omega⟩) ⟨0, by omega⟩
      rwa [coe_torusDiag, Matrix.diagonal_apply_eq,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
    have h1' : (1 : F) = (c : F) := by simpa [diagVecOne] using h1
    exact h1'.symm
  have hc1 : c = 1 := Units.ext h00
  rw [← hc, hc1, map_one]

def diagTorusSixGL (r : ℕ) : Subgroup (GL (Fin 6) F) :=
  (torusDiag.comp ((diagVecSuccHom (F := F) 5).comp (rootsPiHom (F := F) 5 r))).range

theorem diagTorusSixGL_le_SL (r : ℕ) : diagTorusSixGL (F := F) r ≤ StatedSL 6 F := by
  rintro _ ⟨u, rfl⟩
  refine torusDiag_mem_SL ?_
  show ∏ i, diagVecSucc 5 (fun j => ((u j : rootsOfUnity r F) : Fˣ)) i = 1
  exact prod_diagVecSucc 5 _

theorem card_diagTorusSixGL (r : ℕ) [NeZero r] (hrd : r ∣ Nat.card F - 1) :
    Nat.card (diagTorusSixGL (F := F) r) = r ^ 5 := by
  have hinj : Function.Injective
      ⇑(torusDiag.comp ((diagVecSuccHom (F := F) 5).comp (rootsPiHom (F := F) 5 r))) :=
    torusDiag_injective.comp ((diagVecSucc_injective 5).comp (rootsPiHom_injective 5 r))
  rw [diagTorusSixGL, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (K := ⊤) (f := torusDiag.comp
      ((diagVecSuccHom (F := F) 5).comp (rootsPiHom (F := F) 5 r))) hinj,
    Subgroup.card_top, Nat.card_fun, Nat.card_fin]
  rw [CFSG.LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd r,
    Nat.gcd_eq_left (by rwa [← Nat.card_eq_fintype_card])]

theorem isElemAbelian_diagTorusSixGL (r : ℕ) (hr : r.Prime) :
    IsElemAbelian r (diagTorusSixGL (F := F) r) := by
  have htop : IsElemAbelian r (⊤ : Subgroup (Fin 5 → rootsOfUnity r F)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (funext fun i => mul_comm (a.val i) (b.val i))
    · funext i
      exact Subtype.ext (by
        simpa using (mem_rootsOfUnity r ((x i : rootsOfUnity r F) : Fˣ)).mp (x i).2)
  rw [diagTorusSixGL, MonoidHom.range_eq_map]
  exact htop.map _

theorem diagTorusSixGL_le_normalizer_rootSubgroupGL (r : ℕ) :
    diagTorusSixGL (F := F) r ≤
      Subgroup.normalizer (rootSubgroupGL (F := F) 6 : Set (GL (Fin 6) F)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro _ ⟨u, rfl⟩ x hx
  obtain ⟨s, hs⟩ := hx
  set v : Fin 6 → Fˣ := diagVecSucc 5 (fun j => ((u j : rootsOfUnity r F) : Fˣ)) with hv
  change torusDiag v * x * (torusDiag v)⁻¹ ∈ rootSubgroupGL 6
  refine ⟨Multiplicative.ofAdd (fun _ =>
    (v 0 : F) * s.toAdd ⟨0, 0⟩ * (((v 1)⁻¹ : Fˣ) : F)), ?_⟩
  rw [← hs, ← map_inv (torusDiag (K := F))]
  exact (torusDiag_mul_linHom_mul_inv 4 v s).symm

end Torus

theorem diagTorusGL_subgroupOf_inf_scalars {F : Type} [Field F] [Fintype F] (k r : ℕ) :
    (diagTorusGL (F := F) k r).subgroupOf (StatedSL (k + 2) F) ⊓
      (StatedScalars (Fin (k + 2)) F).subgroupOf (StatedSL (k + 2) F) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzD, hzK⟩
  rw [Subgroup.mem_bot]
  have hzD' : (z : GL (Fin (k + 2)) F) ∈ diagTorusGL (F := F) k r := hzD
  have hzK' : (z : GL (Fin (k + 2)) F) ∈ StatedScalars (Fin (k + 2)) F := hzK
  obtain ⟨u, hu⟩ := hzD'
  obtain ⟨c, hc⟩ := hzK'
  have h00 : (c : F) = 1 := by
    have heq : torusDiag (K := F) (diagVecOne k
        (fun j => ((u j : rootsOfUnity r F) : Fˣ))) =
        GeneralLinearGroup.scalar (Fin (k + 2)) c := hu.trans hc.symm
    have h1 : (((diagVecOne k (fun j => ((u j : rootsOfUnity r F) : Fˣ)))
        ⟨0, by omega⟩ : Fˣ) : F) = (c : F) := by
      have h2 := congrFun (congrFun (congrArg
        (fun x : GL (Fin (k + 2)) F => (x : Matrix (Fin (k + 2)) (Fin (k + 2)) F)) heq)
        ⟨0, by omega⟩) ⟨0, by omega⟩
      rwa [coe_torusDiag, Matrix.diagonal_apply_eq,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
    have h1' : (1 : F) = (c : F) := by simpa [diagVecOne] using h1
    exact h1'.symm
  have hc1 : c = 1 := Units.ext h00
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem exists_surjective_of_card_hopfMultiplier {S E E₀ : Type} [Group S] [Finite S]
    [Group E] [Finite E] [Group E₀] [Finite E₀] [Group.IsPerfect S] [Group.IsPerfect E]
    [Group.IsPerfect E₀] {p : E →* S} (hp : Function.Surjective p) (hker : p.ker ≤ Subgroup.center E)
    {p₀ : E₀ →* S} (hp₀ : Function.Surjective p₀) (hker₀ : p₀.ker ≤ Subgroup.center E₀)
    (hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) = Nat.card p₀.ker) :
    ∃ φ : E₀ →* E, Function.Surjective φ ∧ φ.ker ≤ p₀.ker := by
  classical
  haveI : Finite (CFSG.RankThree.PerfectCover.HopfCover S) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover inferInstance
  haveI : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier S) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier inferInstance
  let h := CFSG.RankThree.PerfectCover.hopfLift p hp hker
  let h₀ := CFSG.RankThree.PerfectCover.hopfLift p₀ hp₀ hker₀
  have hh : Function.Surjective h := CFSG.RankThree.PerfectCover.hopfLift_surjective p hp hker
  have hh₀ : Function.Surjective h₀ := CFSG.RankThree.PerfectCover.hopfLift_surjective p₀ hp₀ hker₀
  have hU : Nat.card (CFSG.RankThree.PerfectCover.HopfCover S) =
      Nat.card S * Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) := by
    have key := Subgroup.card_ker_mul_card_range (CFSG.RankThree.PerfectCover.hopfCoverMap S)
    rw [show (CFSG.RankThree.PerfectCover.hopfCoverMap S).ker =
        CFSG.RankThree.PerfectCover.hopfMultiplier S from rfl,
      MonoidHom.range_eq_top.mpr (CFSG.RankThree.PerfectCover.hopfCoverMap_surjective),
      Subgroup.card_top, Nat.mul_comm] at key
    exact key.symm
  have hE₀ : Nat.card E₀ = Nat.card p₀.ker * Nat.card S := by
    have key := Subgroup.card_ker_mul_card_range p₀
    rw [MonoidHom.range_eq_top.mpr hp₀, Subgroup.card_top] at key
    exact key.symm
  have hK : Nat.card h₀.ker * Nat.card E₀ =
      Nat.card (CFSG.RankThree.PerfectCover.HopfCover S) := by
    have key := Subgroup.card_ker_mul_card_range h₀
    rw [MonoidHom.range_eq_top.mpr hh₀, Subgroup.card_top] at key
    exact key
  have hkey : Nat.card h₀.ker * Nat.card E₀ = 1 * Nat.card E₀ := by
    calc Nat.card h₀.ker * Nat.card E₀ =
        Nat.card (CFSG.RankThree.PerfectCover.HopfCover S) := hK
      _ = Nat.card S * Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) := hU
      _ = Nat.card S * Nat.card p₀.ker := by rw [hcard]
      _ = Nat.card p₀.ker * Nat.card S := Nat.mul_comm _ _
      _ = Nat.card E₀ := hE₀.symm
      _ = 1 * Nat.card E₀ := (one_mul _).symm
  have hk1 : Nat.card h₀.ker = 1 :=
    Nat.mul_right_cancel (Nat.card_pos (α := E₀)) hkey
  have hinj₀ : Function.Injective h₀ :=
    MonoidHom.ker_eq_bot_iff h₀ |>.mp (Subgroup.card_eq_one.mp hk1)
  let e₀ : CFSG.RankThree.PerfectCover.HopfCover S ≃* E₀ :=
    MulEquiv.ofBijective h₀ ⟨hinj₀, hh₀⟩
  refine ⟨h.comp e₀.symm.toMonoidHom, hh.comp e₀.symm.surjective, ?_⟩
  intro x hx
  change h (e₀.symm x) = 1 at hx
  have hxM : e₀.symm x ∈ CFSG.RankThree.PerfectCover.hopfMultiplier S := by
    rw [MonoidHom.mem_ker]
    have h1 : CFSG.RankThree.PerfectCover.hopfCoverMap S (e₀.symm x) =
        p (h (e₀.symm x)) := by
      rw [← MonoidHom.comp_apply, CFSG.RankThree.PerfectCover.comp_hopfLift]
    rw [h1, hx, map_one]
  have hxker : x ∈ p₀.ker := by
    have hxM' : e₀ (e₀.symm x) ∈ Subgroup.map e₀.toMonoidHom
        (CFSG.RankThree.PerfectCover.hopfMultiplier S) :=
      Subgroup.mem_map_of_mem e₀.toMonoidHom hxM
    rw [show Subgroup.map e₀.toMonoidHom (CFSG.RankThree.PerfectCover.hopfMultiplier S) = p₀.ker
      from CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift p₀ hp₀ hker₀] at hxM'
    rwa [e₀.apply_symm_apply] at hxM'
  exact hxker

def diagTorusFourGL {F : Type} [Field F] [Fintype F] (r : ℕ) : Subgroup (GL (Fin 4) F) :=
  (torusDiag.comp ((diagVecSuccHom (F := F) 3).comp (rootsPiHom (F := F) 3 r))).range

theorem diagTorusFourGL_le_SL {F : Type} [Field F] [Fintype F] (r : ℕ) :
    diagTorusFourGL (F := F) r ≤ StatedSL 4 F := by
  rintro _ ⟨u, rfl⟩
  refine torusDiag_mem_SL ?_
  show ∏ i, diagVecSucc 3 (fun j => ((u j : rootsOfUnity r F) : Fˣ)) i = 1
  exact prod_diagVecSucc 3 _

theorem card_diagTorusFourGL {F : Type} [Field F] [Fintype F] (r : ℕ) [NeZero r]
    (hrd : r ∣ Nat.card F - 1) :
    Nat.card (diagTorusFourGL (F := F) r) = r ^ 3 := by
  have hinj : Function.Injective
      ⇑(torusDiag.comp ((diagVecSuccHom (F := F) 3).comp (rootsPiHom (F := F) 3 r))) :=
    torusDiag_injective.comp ((diagVecSucc_injective 3).comp (rootsPiHom_injective 3 r))
  rw [diagTorusFourGL, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (K := ⊤) (f := torusDiag.comp
      ((diagVecSuccHom (F := F) 3).comp (rootsPiHom (F := F) 3 r))) hinj,
    Subgroup.card_top, Nat.card_fun, Nat.card_fin]
  rw [CFSG.LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd r,
    Nat.gcd_eq_left (by rwa [← Nat.card_eq_fintype_card])]

theorem isElemAbelian_diagTorusFourGL {F : Type} [Field F] [Fintype F] (r : ℕ) (hr : r.Prime) :
    IsElemAbelian r (diagTorusFourGL (F := F) r) := by
  have htop : IsElemAbelian r (⊤ : Subgroup (Fin 3 → rootsOfUnity r F)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (funext fun i => mul_comm (a.val i) (b.val i))
    · funext i
      exact Subtype.ext (by
        simpa using (mem_rootsOfUnity r ((x i : rootsOfUnity r F) : Fˣ)).mp (x i).2)
  rw [diagTorusFourGL, MonoidHom.range_eq_map]
  exact htop.map _

theorem diagTorusFourGL_le_normalizer_rootSubgroupGL {F : Type} [Field F] [Fintype F] (r : ℕ) :
    diagTorusFourGL (F := F) r ≤
      Subgroup.normalizer (rootSubgroupGL (F := F) 4 : Set (GL (Fin 4) F)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro _ ⟨u, rfl⟩ x hx
  obtain ⟨s, hs⟩ := hx
  set v : Fin 4 → Fˣ := diagVecSucc 3 (fun j => ((u j : rootsOfUnity r F) : Fˣ)) with hv
  change torusDiag v * x * (torusDiag v)⁻¹ ∈ rootSubgroupGL 4
  refine ⟨Multiplicative.ofAdd (fun _ =>
    (v 0 : F) * s.toAdd ⟨0, 0⟩ * (((v 1)⁻¹ : Fˣ) : F)), ?_⟩
  rw [← hs, ← map_inv (torusDiag (K := F))]
  exact (torusDiag_mul_linHom_mul_inv 2 v s).symm

theorem exists_model_psl_of_isLabel {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hM : MarkedModel lab (K ⧸ Subgroup.center K)) {d n : ℕ}
    (ht : markTag lab = .PSL) (hr : markRank lab = d) (hc : markChar lab = 2)
    (hd : markDeg lab = n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (K ⧸ Subgroup.center K ≃* StatedProj (StatedSL d F)) := by
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL d 2 n := by
    simpa [CFSG.StandardType.MarkedModel, ht, hr, hc, hd] using hM
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  exact ⟨F, hF, hFin, hcard, ⟨e⟩⟩

theorem card_hopfMultiplier_statedProj_of_three_le {F : Type} [Field F] [Fintype F] {d : ℕ}
    (hd : 3 ≤ d) (hq : 3 ≤ Fintype.card F) (h34 : ¬ (d = 3 ∧ Fintype.card F = 4)) :
    Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSL d F))) =
      Nat.gcd d (Fintype.card F - 1) := by
  obtain ⟨e⟩ := (CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
    (k := F) hd hq h34).2
  let ψ : ProjectiveSpecialLinearGroup (Fin d) F ≃* StatedProj (StatedSL d F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d F
  have h1 : Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSL d F))) =
      Nat.card (Multiplicative (ZMod (Nat.gcd d (Fintype.card F - 1)))) :=
    Nat.card_congr ((CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr ψ.symm).trans e)
  rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h1

theorem card_hopfMultiplier_statedProj_of_five_le {F : Type} [Field F] [Fintype F] {d : ℕ}
    (hd : 5 ≤ d) :
    Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSL d F))) =
      Nat.gcd d (Fintype.card F - 1) := by
  obtain ⟨e⟩ := (CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_five_le
    (k := F) hd).2
  let ψ : ProjectiveSpecialLinearGroup (Fin d) F ≃* StatedProj (StatedSL d F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d F
  have h1 : Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSL d F))) =
      Nat.card (Multiplicative (ZMod (Nat.gcd d (Fintype.card F - 1)))) :=
    Nat.card_congr ((CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr ψ.symm).trans e)
  rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h1

theorem card_center_specialLinearGroup_eq_gcd {F : Type} [Field F] [Fintype F] {d : ℕ} (hd : 1 ≤ d) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin d) F)) =
      Nat.gcd d (Fintype.card F - 1) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [Nat.card_congr
    (SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin d) (R := F)).toEquiv]
  rw [show max (Fintype.card (Fin d)) 1 = d by simp [max_eq_left hd]]
  exact CFSG.LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd d

theorem exists_surjective_statedSL_of_model {K : Type} [Group K] [Finite K] {d : ℕ} {F : Type}
    [Field F] [Fintype F] (hQ : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL d F)) (hd : 3 ≤ d)
    (hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (StatedProj (StatedSL d F))) =
      Nat.card (Subgroup.center (SpecialLinearGroup (Fin d) F))) :
    ∃ φ : ↥(StatedSL d F) →* K, Function.Surjective φ ∧
      φ.ker ≤ (StatedScalars (Fin d) F).subgroupOf (StatedSL d F) := by
  classical
  let ψ : ProjectiveSpecialLinearGroup (Fin d) F ≃* StatedProj (StatedSL d F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d F
  haveI : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin d) F) :=
    CFSG.LinearGroups.linear_projective_perfect (by omega) (Or.inl hd)
  haveI hSperf : Group.IsPerfect (StatedProj (StatedSL d F)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  haveI hKperf : Group.IsPerfect K := hQ.1
  haveI : Group.IsPerfect (SpecialLinearGroup (Fin d) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hd
  haveI hSLperf : Group.IsPerfect ↥(StatedSL d F) :=
    Group.IsPerfect.ofSurjective
      (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d F).toMonoidHom)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d F).surjective
  let p : K →* StatedProj (StatedSL d F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : p.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : QuotientGroup.mk' (Subgroup.center K) x = 1 := by
      apply e.injective
      simpa [p] using hx
    exact (QuotientGroup.eq_one_iff _).mp h1
  let p₀ : ↥(StatedSL d F) →* StatedProj (StatedSL d F) :=
    QuotientGroup.mk' ((StatedScalars (Fin d) F).subgroupOf (StatedSL d F))
  have hp₀ : Function.Surjective p₀ := QuotientGroup.mk'_surjective _
  have hker₀ : p₀.ker ≤ Subgroup.center ↥(StatedSL d F) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hx' : (x : GL (Fin d) F) ∈ StatedScalars (Fin d) F := by
      have h := hx
      rw [show p₀.ker = (StatedScalars (Fin d) F).subgroupOf (StatedSL d F) from
        QuotientGroup.ker_mk' _] at h
      exact h
    obtain ⟨c, hc⟩ := hx'
    have hmem : GeneralLinearGroup.scalar (Fin d) c ∈ Subgroup.center (GL (Fin d) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have hcomm := Subgroup.mem_center_iff.mp hmem (y : GL (Fin d) F)
    rw [← hc]
    exact hcomm
  have hp₀ker : Nat.card p₀.ker = Nat.card (Subgroup.center (SpecialLinearGroup (Fin d) F)) := by
    rw [show p₀.ker = (StatedScalars (Fin d) F).subgroupOf (StatedSL d F) from
      QuotientGroup.ker_mk' _,
      ← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars d F,
      Subgroup.card_map_of_injective
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d F).injective]
  obtain ⟨φ, hφ, hφker⟩ :=
    exists_surjective_of_card_hopfMultiplier hp hker hp₀ hker₀ (by rw [hp₀ker]; exact hcard)
  exact ⟨φ, hφ, by simpa [p₀] using hφker⟩

theorem le_evenRank_of_surjective_statedSL_torus {K : Type} [Group K] [Finite K] {r k : ℕ}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ Nat.card F - 1) {φ : ↥(StatedSL (k + 2) F) →* K}
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ (StatedScalars (Fin (k + 2)) F).subgroupOf (StatedSL (k + 2) F)) :
    k ≤ evenRank K := by
  classical
  haveI : NeZero r := ⟨hr.ne_zero⟩
  let D : Subgroup ↥(StatedSL (k + 2) F) := (diagTorusGL (F := F) k r).subgroupOf _
  let X : Subgroup ↥(StatedSL (k + 2) F) := (rootSubgroupGL (F := F) (k + 2)).subgroupOf _
  have hD : D ⊓ φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ (diagTorusGL (F := F) k r).subgroupOf (StatedSL (k + 2) F) ⊓
        (StatedScalars (Fin (k + 2)) F).subgroupOf (StatedSL (k + 2) F) :=
      ⟨hz.1, hker hz.2⟩
    rwa [diagTorusGL_subgroupOf_inf_scalars k r, Subgroup.mem_bot] at hz'
  have hX : X ⊓ φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ (rootSubgroupGL (F := F) (k + 2)).subgroupOf (StatedSL (k + 2) F) ⊓
        (StatedScalars (Fin (k + 2)) F).subgroupOf (StatedSL (k + 2) F) :=
      ⟨hz.1, hker hz.2⟩
    rwa [rootSubgroupGL_subgroupOf_inf_scalars (k + 2) (by omega), Subgroup.mem_bot] at hz'
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card X = Nat.card (rootSubgroupGL (F := F) (k + 2)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSubgroupGL_le_SL (k + 2))).toEquiv
    have hgt : 1 < Nat.card X := by
      rw [hcard, card_rootSubgroupGL (by omega), Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    exact (Subgroup.one_lt_card_iff_ne_bot X).1 hgt hbot
  have hX2 : IsPGroup 2 X :=
    (isPGroup_two_rootSubgroupGL (k + 2)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (rootSubgroupGL_le_SL (k + 2))).symm
  have hDab : IsElemAbelian r D :=
    (isElemAbelian_diagTorusGL k r hr).subgroupOf (StatedSL (k + 2) F)
  have hDcard : Nat.card D = r ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (diagTorusGL_le_SL k r)).toEquiv,
      card_diagTorusGL k r hrd]
  have hDnormGL := diagTorusGL_le_normalizer_rootSubgroupGL (F := F) k r
  have hDX : D ≤ Subgroup.normalizer (X : Set ↥(StatedSL (k + 2) F)) := by
    rw [Subgroup.le_normalizer_iff] at hDnormGL ⊢
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb ⊢
    simpa using hDnormGL (a : GL (Fin (k + 2)) F) ha (b : GL (Fin (k + 2)) F) hb
  refine le_evenRank_of_map φ hr hr2 hX2 ?_ hDab hDcard hD hDX
  intro hbot
  have hXle : X ≤ φ.ker := (Subgroup.map_eq_bot_iff X).mp hbot
  have hXbot : X = ⊥ := le_bot_iff.mp (by rw [← hX]; exact le_inf le_rfl hXle)
  exact hXne hXbot

theorem le_evenRank_of_injective_statedSL_six {K : Type} [Group K] [Finite K] {r : ℕ}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ Nat.card F - 1) {φ : ↥(StatedSL 6 F) →* K}
    (hφ : Function.Injective φ) :
    5 ≤ evenRank K := by
  classical
  haveI : NeZero r := ⟨hr.ne_zero⟩
  let D : Subgroup ↥(StatedSL 6 F) := (diagTorusSixGL (F := F) r).subgroupOf _
  let X : Subgroup ↥(StatedSL 6 F) := (rootSubgroupGL (F := F) 6).subgroupOf _
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card X = Nat.card (rootSubgroupGL (F := F) 6) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSubgroupGL_le_SL 6)).toEquiv
    have hgt : 1 < Nat.card X := by
      rw [hcard, card_rootSubgroupGL (by omega), Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    exact (Subgroup.one_lt_card_iff_ne_bot X).1 hgt hbot
  have hX2 : IsPGroup 2 X :=
    (isPGroup_two_rootSubgroupGL 6).of_equiv
      (Subgroup.subgroupOfEquivOfLe (rootSubgroupGL_le_SL 6)).symm
  have hDab : IsElemAbelian r D :=
    (isElemAbelian_diagTorusSixGL r hr).subgroupOf (StatedSL 6 F)
  have hDcard : Nat.card D = r ^ 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (diagTorusSixGL_le_SL r)).toEquiv,
      card_diagTorusSixGL r hrd]
  have hDnormGL := diagTorusSixGL_le_normalizer_rootSubgroupGL (F := F) r
  have hDX : D ≤ Subgroup.normalizer (X : Set ↥(StatedSL 6 F)) := by
    rw [Subgroup.le_normalizer_iff] at hDnormGL ⊢
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb ⊢
    simpa using hDnormGL (a : GL (Fin 6) F) ha (b : GL (Fin 6) F) hb
  have hker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr hφ
  refine le_evenRank_of_map φ hr hr2 hX2 ?_ hDab hDcard ?_ hDX
  · intro hbot
    rw [Subgroup.map_eq_bot_iff, hker, le_bot_iff] at hbot
    exact hXne hbot
  · rw [hker, inf_bot_eq]

theorem le_evenRank_of_injective_statedSL_four {K : Type} [Group K] [Finite K] {r : ℕ}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ Nat.card F - 1) {φ : ↥(StatedSL 4 F) →* K}
    (hφ : Function.Injective φ) :
    3 ≤ evenRank K := by
  classical
  haveI : NeZero r := ⟨hr.ne_zero⟩
  let D : Subgroup ↥(StatedSL 4 F) := (diagTorusFourGL (F := F) r).subgroupOf _
  let X : Subgroup ↥(StatedSL 4 F) := (rootSubgroupGL (F := F) 4).subgroupOf _
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card X = Nat.card (rootSubgroupGL (F := F) 4) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSubgroupGL_le_SL 4)).toEquiv
    have hgt : 1 < Nat.card X := by
      rw [hcard, card_rootSubgroupGL (by omega), Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    exact (Subgroup.one_lt_card_iff_ne_bot X).1 hgt hbot
  have hX2 : IsPGroup 2 X :=
    (isPGroup_two_rootSubgroupGL 4).of_equiv
      (Subgroup.subgroupOfEquivOfLe (rootSubgroupGL_le_SL 4)).symm
  have hDab : IsElemAbelian r D :=
    (isElemAbelian_diagTorusFourGL r hr).subgroupOf (StatedSL 4 F)
  have hDcard : Nat.card D = r ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (diagTorusFourGL_le_SL r)).toEquiv,
      card_diagTorusFourGL r hrd]
  have hDnormGL := diagTorusFourGL_le_normalizer_rootSubgroupGL (F := F) r
  have hDX : D ≤ Subgroup.normalizer (X : Set ↥(StatedSL 4 F)) := by
    rw [Subgroup.le_normalizer_iff] at hDnormGL ⊢
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb ⊢
    simpa using hDnormGL (a : GL (Fin 4) F) ha (b : GL (Fin 4) F) hb
  have hker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr hφ
  refine le_evenRank_of_map φ hr hr2 hX2 ?_ hDab hDcard ?_ hDX
  · intro hbot
    rw [Subgroup.map_eq_bot_iff, hker, le_bot_iff] at hbot
    exact hXne hbot
  · rw [hker, inf_bot_eq]

theorem card_hopfMultiplier_statedProj_eq_center {F : Type} [Field F] [Fintype F] {d : ℕ}
    (hd : 3 ≤ d) (hq : 4 ≤ Fintype.card F) (h34 : ¬ (d = 3 ∧ Fintype.card F = 4)) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSL d F))) =
      Nat.card (Subgroup.center (SpecialLinearGroup (Fin d) F)) := by
  have h1 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSL d F))) =
      Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSL d F))) :=
    Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv
  rw [h1]
  rcases Nat.lt_or_ge d 5 with hlt | hge
  · have hq3 : 3 ≤ Fintype.card F := by omega
    rw [card_hopfMultiplier_statedProj_of_three_le hd hq3 h34,
      card_center_specialLinearGroup_eq_gcd (by omega)]
  · rw [card_hopfMultiplier_statedProj_of_five_le hge, card_center_specialLinearGroup_eq_gcd (by omega)]

theorem one_le_evenRank_of_central_prime {G : Type} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hZ : ∃ z ∈ Subgroup.center G, orderOf z = r) (h2 : Even (Nat.card G)) :
    1 ≤ evenRank G := by
  obtain ⟨z, hz, hzord⟩ := hZ
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h2)
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  have hX : Subgroup.zpowers t ≠ ⊥ := by
    rwa [Ne, Subgroup.zpowers_eq_bot]
  have hX2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht, pow_one]
  have hE : IsElemAbelian r (Subgroup.zpowers z) := by
    have hzr : z ^ r = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, ← _root_.zpow_add,
        ← _root_.zpow_add, add_comm]
    · have hcard : Nat.card (Subgroup.zpowers z) = r := by rw [Nat.card_zpowers, hzord]
      have hdvd : orderOf x ∣ r := hcard ▸ Subgroup.orderOf_dvd_natCard _ hx
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hEcard : Nat.card (Subgroup.zpowers z) = r ^ 1 := by
    rw [Nat.card_zpowers, hzord, pow_one]
  have hEnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    have hsub : Subgroup.zpowers z ≤
        Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hcenter : a ∈ Subgroup.center G := Subgroup.zpowers_le.mpr hz ha
      exact Subgroup.mem_center_iff.mp hcenter b
    exact hsub.trans (Subgroup.centralizer_le_normalizer _)
  exact le_evenRank_of_normalizer hr hr2 hX hX2 hE hEcard hEnorm


section PSLThreePoint

open CFSG.RankThree.PartTwo.Census CFSG.Assembly.RankThreeEven

def pslThreeBlock {F : Type} [Field F] (B : Matrix (Fin 2) (Fin 1) F) :
    Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) F :=
  fromBlocks 1 B 0 1

theorem pslThreeBlock_mul {F : Type} [Field F] (B B' : Matrix (Fin 2) (Fin 1) F) :
    pslThreeBlock B * pslThreeBlock B' = pslThreeBlock (B + B') := by
  have h := fromBlocks_multiply
    (A := (1 : Matrix (Fin 2) (Fin 2) F)) (B := B)
    (C := (0 : Matrix (Fin 1) (Fin 2) F)) (D := (1 : Matrix (Fin 1) (Fin 1) F))
    (A' := (1 : Matrix (Fin 2) (Fin 2) F)) (B' := B')
    (C' := (0 : Matrix (Fin 1) (Fin 2) F)) (D' := (1 : Matrix (Fin 1) (Fin 1) F))
  simpa [pslThreeBlock, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, add_comm] using h

theorem det_pslThreeBlock {F : Type} [Field F] (B : Matrix (Fin 2) (Fin 1) F) :
    (pslThreeBlock B).det = 1 := by
  have h := det_fromBlocks_zero₂₁
    (A := (1 : Matrix (Fin 2) (Fin 2) F)) (B := B)
    (D := (1 : Matrix (Fin 1) (Fin 1) F))
  simpa [pslThreeBlock, det_one] using h

@[expose] def pslThreeUHom {F : Type} [Field F] [CharP F 2] :
    Multiplicative (Matrix (Fin 2) (Fin 1) F) →* SpecialLinearGroup (Fin 2 ⊕ Fin 1) F where
  toFun B := ⟨pslThreeBlock B.toAdd, det_pslThreeBlock B.toAdd⟩
  map_one' := Subtype.ext (by
    change pslThreeBlock (0 : Matrix (Fin 2) (Fin 1) F) = 1
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [pslThreeBlock, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.one_apply])
  map_mul' B B' := Subtype.ext (by
    change pslThreeBlock (B.toAdd + B'.toAdd) = pslThreeBlock B.toAdd * pslThreeBlock B'.toAdd
    rw [pslThreeBlock_mul])

theorem coe_pslThreeUHom {F : Type} [Field F] [CharP F 2]
    (B : Multiplicative (Matrix (Fin 2) (Fin 1) F)) :
    ((pslThreeUHom B : SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) :
      Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) F) = pslThreeBlock B.toAdd := rfl

theorem isPGroup_two_pslThreeUHom_range {F : Type} [Field F] [CharP F 2] :
    IsPGroup 2 (pslThreeUHom (F := F)).range := by
  intro y
  obtain ⟨B, hB⟩ := y.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, pow_two, Subgroup.coe_mul, ← hB, ← map_mul, OneMemClass.coe_one]
  have hBB : B * B = 1 := by
    apply Multiplicative.toAdd.injective
    ext i j
    simp only [toAdd_mul, toAdd_one, Matrix.add_apply, Matrix.zero_apply,
      CharTwo.add_self_eq_zero]
  rw [hBB, map_one]

theorem pslThreeUHom_range_ne_bot {F : Type} [Field F] [CharP F 2] :
    (pslThreeUHom (F := F)).range ≠ ⊥ := by
  intro hbot
  have h1 : pslThreeUHom (F := F) (Multiplicative.ofAdd (Matrix.of fun _ _ => (1 : F))) ∈
      (⊥ : Subgroup (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F)) := by
    rw [← hbot]
    exact ⟨_, rfl⟩
  rw [Subgroup.mem_bot] at h1
  have h2 := congrArg (fun x : SpecialLinearGroup (Fin 2 ⊕ Fin 1) F =>
    (x : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) F) (Sum.inl 0) (Sum.inr 0)) h1
  simp [coe_pslThreeUHom, pslThreeBlock, fromBlocks_apply₁₂] at h2

theorem pslThreeUHom_range_inf_center {F : Type} [Field F] [CharP F 2] :
    (pslThreeUHom (F := F)).range ⊓
      Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨B, rfl⟩, hx⟩
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hB : B = 1 := by
    apply Multiplicative.toAdd.injective
    ext i j
    have h1 := congrFun (congrFun hc (Sum.inl i)) (Sum.inr j)
    rw [coe_pslThreeUHom] at h1
    have h2 : pslThreeBlock B.toAdd (Sum.inl i) (Sum.inr j) = B.toAdd i j := by
      rw [pslThreeBlock, fromBlocks_apply₁₂]
    rw [h2] at h1
    have h3 : (scalar (Fin 2 ⊕ Fin 1) c) (Sum.inl i) (Sum.inr j) = 0 := by
      rw [Matrix.scalar_apply]
      exact Matrix.diagonal_apply_ne (fun _ => c) (by simp)
    rw [h3] at h1
    simpa using h1.symm
  rw [hB, map_one, Subgroup.mem_bot]

@[expose] def pslThreeDiag {F : Type} [Field F] [CharP F 2] (a : ZMod 3) :
    Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) F :=
  fromBlocks (threeCycleMat F ^ a.val) 0 0 1

theorem coe_pslThreeDiag {F : Type} [Field F] [CharP F 2] (a : ZMod 3) :
    (pslThreeDiag a : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) F) =
      fromBlocks (threeCycleMat F ^ a.val) 0 0 1 := rfl

theorem det_pslThreeDiag {F : Type} [Field F] [CharP F 2] (a : ZMod 3) :
    (pslThreeDiag (F := F) a).det = 1 := by
  have h := det_fromBlocks_zero₂₁
    (A := (threeCycleMat F ^ a.val)) (B := (0 : Matrix (Fin 2) (Fin 1) F))
    (D := (1 : Matrix (Fin 1) (Fin 1) F))
  rw [pslThreeDiag, h, det_pow, det_threeCycleMat, one_pow, det_one, mul_one]

@[expose] def pslThreeSHom {F : Type} [Field F] [CharP F 2] :
    Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2 ⊕ Fin 1) F where
  toFun a := ⟨pslThreeDiag (F := F) a.toAdd, det_pslThreeDiag (F := F) a.toAdd⟩
  map_one' := Subtype.ext (by
    change pslThreeDiag (F := F) (0 : ZMod 3) = 1
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [pslThreeDiag, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.one_apply])
  map_mul' a b := Subtype.ext (by
    change pslThreeDiag (F := F) (a.toAdd + b.toAdd) =
      pslThreeDiag (F := F) a.toAdd * pslThreeDiag (F := F) b.toAdd
    have h := fromBlocks_multiply
      (A := (threeCycleMat F ^ a.toAdd.val)) (B := (0 : Matrix (Fin 2) (Fin 1) F))
      (C := (0 : Matrix (Fin 1) (Fin 2) F)) (D := (1 : Matrix (Fin 1) (Fin 1) F))
      (A' := (threeCycleMat F ^ b.toAdd.val)) (B' := (0 : Matrix (Fin 2) (Fin 1) F))
      (C' := (0 : Matrix (Fin 1) (Fin 2) F)) (D' := (1 : Matrix (Fin 1) (Fin 1) F))
    rw [pslThreeDiag, pslThreeDiag, pslThreeDiag, h, ← threeCycleMat_pow_val_add]
    simp)

theorem coe_pslThreeSHom {F : Type} [Field F] [CharP F 2] (a : Multiplicative (ZMod 3)) :
    ((pslThreeSHom a : SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) :
      Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) F) = pslThreeDiag a.toAdd := rfl

theorem pslThreeSHom_range_inf_center {F : Type} [Field F] [CharP F 2] :
    (pslThreeSHom (F := F)).range ⊓
      Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, rfl⟩, hx⟩
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have h1 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 1)
  rw [coe_pslThreeSHom] at h1
  have h2 : pslThreeDiag (F := F) a.toAdd (Sum.inl 0) (Sum.inl 1) =
      (threeCycleMat F ^ a.toAdd.val) 0 1 := by
    rw [pslThreeDiag, fromBlocks_apply₁₁]
  rw [h2] at h1
  have h3 : (scalar (Fin 2 ⊕ Fin 1) c) (Sum.inl 0) (Sum.inl 1) = 0 := by
    rw [Matrix.scalar_apply]
    exact Matrix.diagonal_apply_ne (fun _ => c) (by simp)
  rw [h3] at h1
  have ha : a.toAdd = 0 := threeCycleMat_pow_val_zero_one h1.symm
  rw [Subgroup.mem_bot, show a = 1 from Multiplicative.toAdd.injective (by simpa using ha),
    map_one]

theorem pslThreeSHom_injective {F : Type} [Field F] [CharP F 2] :
    Function.Injective (pslThreeSHom (F := F)) := by
  intro a b h
  apply Multiplicative.toAdd.injective
  have hmat : threeCycleMat F ^ a.toAdd.val = threeCycleMat F ^ b.toAdd.val := by
    ext i j
    have h1 := congrFun (congrFun (congrArg (fun x :
      SpecialLinearGroup (Fin 2 ⊕ Fin 1) F =>
        (x : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) F)) h) (Sum.inl i)) (Sum.inl j)
    simpa [coe_pslThreeSHom, coe_pslThreeDiag, fromBlocks_apply₁₁] using h1
  have hpow : threeCycleMat F ^ (a.toAdd - b.toAdd).val = 1 := by
    rw [sub_eq_add_neg, threeCycleMat_pow_val_add, hmat]
    rw [← threeCycleMat_pow_val_add, add_neg_cancel, ZMod.val_zero, pow_zero]
  have hz : (threeCycleMat F ^ (a.toAdd - b.toAdd).val) 0 1 = 0 := by
    rw [hpow]
    simp
  exact sub_eq_zero.mp (threeCycleMat_pow_val_zero_one hz)

theorem card_pslThreeSHom_range {F : Type} [Field F] [CharP F 2] :
    Nat.card (pslThreeSHom (F := F)).range = 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (pslThreeSHom_injective (F := F))).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem pslThreeDiag_mul_pslThreeBlock {F : Type} [Field F] [CharP F 2]
    (a : ZMod 3) (B : Matrix (Fin 2) (Fin 1) F) :
    pslThreeDiag (F := F) a * pslThreeBlock B * pslThreeDiag (F := F) (-a) =
      pslThreeBlock (threeCycleMat F ^ a.val * B) := by
  have h1 := fromBlocks_multiply
    (A := (threeCycleMat F ^ a.val)) (B := (0 : Matrix (Fin 2) (Fin 1) F))
    (C := (0 : Matrix (Fin 1) (Fin 2) F)) (D := (1 : Matrix (Fin 1) (Fin 1) F))
    (A' := (1 : Matrix (Fin 2) (Fin 2) F)) (B' := B)
    (C' := (0 : Matrix (Fin 1) (Fin 2) F)) (D' := (1 : Matrix (Fin 1) (Fin 1) F))
  have h2 := fromBlocks_multiply
    (A := (threeCycleMat F ^ a.val)) (B := (threeCycleMat F ^ a.val * B))
    (C := (0 : Matrix (Fin 1) (Fin 2) F)) (D := (1 : Matrix (Fin 1) (Fin 1) F))
    (A' := (threeCycleMat F ^ (-a).val)) (B' := (0 : Matrix (Fin 2) (Fin 1) F))
    (C' := (0 : Matrix (Fin 1) (Fin 2) F)) (D' := (1 : Matrix (Fin 1) (Fin 1) F))
  simp only [pslThreeDiag, pslThreeBlock, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add] at h1 h2 ⊢
  rw [h1, h2]
  rw [show threeCycleMat F ^ a.val * threeCycleMat F ^ (-a).val = 1 by
    rw [← threeCycleMat_pow_val_add, add_neg_cancel, ZMod.val_zero, pow_zero]]

theorem pslThreeSHom_range_le_normalizer {F : Type} [Field F] [CharP F 2] :
    (pslThreeSHom (F := F)).range ≤ Subgroup.normalizer
      ((pslThreeUHom (F := F)).range : Set (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F)) := by
  refine le_normalizer_of_conj_mem ?_
  rintro _ ⟨a, rfl⟩ _ ⟨B, rfl⟩
  refine ⟨Multiplicative.ofAdd (threeCycleMat F ^ a.toAdd.val * B.toAdd), ?_⟩
  have hinv : ((pslThreeSHom (F := F) a)⁻¹ : SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) =
      ⟨pslThreeDiag (F := F) (-a.toAdd), det_pslThreeDiag (F := F) (-a.toAdd)⟩ := by
    rw [← map_inv]
    rfl
  apply Subtype.ext
  rw [hinv]
  simp only [Subgroup.coe_mul, coe_pslThreeSHom, coe_pslThreeUHom, coe_pslThreeDiag]
  exact (pslThreeDiag_mul_pslThreeBlock a.toAdd B.toAdd).symm

theorem exists_elemAbelian_le_normalizer_PSL_three {F : Type} [Field F] [Finite F] [CharP F 2] :
    ∃ E X : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 1 ∧
        E ≤ Subgroup.normalizer (X : Set (ProjectiveSpecialLinearGroup (Fin 3) F)) := by
  haveI : Fintype F := Fintype.ofFinite F
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : SpecialLinearGroup (Fin 2 ⊕ Fin 1) F →*
      ProjectiveSpecialLinearGroup (Fin 2 ⊕ Fin 1) F :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F))
  let E₀ : Subgroup (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) := (pslThreeSHom (F := F)).range
  let X₀ : Subgroup (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) := (pslThreeUHom (F := F)).range
  have hE : IsElemAbelian 3 E₀ := by
    refine isElemAbelian_range (fun a => ?_) (pslThreeSHom (F := F))
    have hcard3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    simpa [hcard3] using pow_card_eq_one' (x := a)
  have hEcard : Nat.card E₀ = 3 ^ 1 := by
    rw [show E₀ = (pslThreeSHom (F := F)).range from rfl, card_pslThreeSHom_range]
    norm_num
  have hX2 : IsPGroup 2 X₀ := isPGroup_two_pslThreeUHom_range
  have hXbot : X₀ ⊓ π.ker = ⊥ := by
    rw [show π.ker = Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) from
      QuotientGroup.ker_mk' _]
    exact pslThreeUHom_range_inf_center
  have hXne : X₀.map π ≠ ⊥ := by
    intro hbot
    have hXle : X₀ ≤ π.ker := (Subgroup.map_eq_bot_iff X₀).mp hbot
    have : X₀ = ⊥ := le_bot_iff.mp (by rw [← hXbot]; exact le_inf le_rfl hXle)
    exact pslThreeUHom_range_ne_bot this
  have hEcent : E₀ ⊓ π.ker = ⊥ := by
    rw [show π.ker = Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) from
      QuotientGroup.ker_mk' _]
    exact pslThreeSHom_range_inf_center
  have hE1 : IsElemAbelian 3 (E₀.map π) := hE.map π
  have hEcent' : E₀ ⊓ Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) = ⊥ := by
    rwa [show π.ker = Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) from
      QuotientGroup.ker_mk' _] at hEcent
  have hE1card : Nat.card (E₀.map π) = 3 ^ 1 := by
    rw [card_map_mk_of_inf_eq_bot (Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ Fin 1) F))
      hEcent', hEcard]
  have hX1_2 : IsPGroup 2 (X₀.map π) := hX2.map π
  have hE1norm : E₀.map π ≤ Subgroup.normalizer (X₀.map π :
      Set (ProjectiveSpecialLinearGroup (Fin 2 ⊕ Fin 1) F)) :=
    (Subgroup.map_mono pslThreeSHom_range_le_normalizer).trans (Subgroup.le_normalizer_map π)
  have hcard : Fintype.card (Fin 2 ⊕ Fin 1) = 3 := by simp
  let e : (Fin 2 ⊕ Fin 1) ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let ψ : ProjectiveSpecialLinearGroup (Fin 2 ⊕ Fin 1) F ≃*
      ProjectiveSpecialLinearGroup (Fin 3) F := pslReindex F e
  refine ⟨(E₀.map π).map ψ.toMonoidHom, (X₀.map π).map ψ.toMonoidHom, ?_,
    hX1_2.map _, hE1.map _, ?_, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff, (MonoidHom.ker_eq_bot_iff ψ.toMonoidHom).mpr ψ.injective,
      le_bot_iff] at hbot
    exact hXne hbot
  · rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hE1card]
  · exact (Subgroup.map_mono hE1norm).trans (Subgroup.le_normalizer_map ψ.toMonoidHom)

theorem exists_elemAbelian_le_normalizer_statedProj_three {F : Type} [Field F] [Fintype F]
    [CharP F 2] :
    ∃ E X : Subgroup (StatedProj (StatedSL 3 F)),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 1 ∧
        E ≤ Subgroup.normalizer (X : Set (StatedProj (StatedSL 3 F))) := by
  obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
    exists_elemAbelian_le_normalizer_PSL_three (F := F)
  let ψ : ProjectiveSpecialLinearGroup (Fin 3) F ≃* StatedProj (StatedSL 3 F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F
  refine ⟨E.map ψ.toMonoidHom, X.map ψ.toMonoidHom, ?_, hX2.map _, hE.map _, ?_, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff, (MonoidHom.ker_eq_bot_iff ψ.toMonoidHom).mpr ψ.injective,
      le_bot_iff] at hbot
    exact hX hbot
  · rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hEcard]
  · exact (Subgroup.map_mono hEX).trans (Subgroup.le_normalizer_map ψ.toMonoidHom)

end PSLThreePoint

theorem not_three_dvd_center_of_psl_two_one {K : Type} [Group K] [Finite K] {d : ℕ}
    (hQ : CFSG.IsQuasisimple K)
    (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL d 2 1) :
    ¬ 3 ∣ Nat.card (Subgroup.center K) := by
  have hdvd := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) .PSL d 2 1 hM
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      ((CFSG.Blueprint.Multiplier.genericOrders .PSL d 2 1).1 *
        (CFSG.Blueprint.Multiplier.genericOrders .PSL d 2 1).2) *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSL d 2 1).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL d 2 1).2) := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional']
  rw [hcard] at hdvd
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL d 2 1 = (1, 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders]
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL d 2 1 = (1, 1) ∨
      CFSG.Blueprint.Multiplier.exceptionalOrders .PSL d 2 1 = (2, 1) := by
    by_cases h2 : d = 2
    · left; subst h2; decide
    by_cases h3 : d = 3
    · right; subst h3; decide
    by_cases h4 : d = 4
    · right; subst h4; decide
    left
    simp [CFSG.Blueprint.Multiplier.exceptionalOrders, h2, h3, h4]
  rintro h3dvd
  rcases he with he | he <;> rw [hg, he] at hdvd
  · exact absurd (h3dvd.trans hdvd) (by norm_num)
  · exact absurd (h3dvd.trans hdvd) (by norm_num)



theorem rk2_low_a_ge (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .A) (hn : 2 ≤ lab.n) :
    lab.rank - 1 ≤ evenRank K := by
  rcases Nat.lt_or_ge lab.rank 2 with hlt | hrank
  · omega
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hn1 : 1 ≤ lab.n := by omega
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := lab.rank + 1) (n := lab.n)
      (by simp [markTag, htag]) (by simp [markRank, htag])
      (by simp [markChar, htag]) (by simp [markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hcardF
  have hdim : lab.rank + 1 = (lab.rank - 1) + 2 := by omega
  have e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL ((lab.rank - 1) + 2) F) := by
    rw [← hdim]
    exact e₀
  by_cases h34 : (lab.rank - 1) + 2 = 3 ∧ Nat.card F = 4
  ·
    have hd3 : (lab.rank - 1) + 2 = 3 := h34.1
    have hcardF4 : Nat.card F = 4 := h34.2
    rw [hd3] at e
    have hrk : lab.rank - 1 = 1 := by omega
    rw [hrk]
    by_cases hZ3 : 3 ∣ Nat.card (Subgroup.center K)
    · obtain ⟨z, hzord⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center K)) 3 hZ3
      have hzeq : orderOf ((z : Subgroup.center K) : K) = 3 := by
        rw [Subgroup.orderOf_coe]; exact hzord
      have hZ : ∃ w ∈ Subgroup.center K, orderOf w = 3 :=
        ⟨(z : Subgroup.center K), z.2, hzeq⟩
      have h2 : Even (Nat.card K) := by
        rw [even_iff_two_dvd, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)]
        refine dvd_mul_of_dvd_left ?_ _
        rw [Nat.card_congr e.toEquiv]
        have hSC : CFSG.Open.StatedClassicalModel (StatedProj (StatedSL 3 F)) .PSL 3 2 2 :=
          ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
            F, inferInstance, inferInstance, by rw [hcardF4]; norm_num, ⟨MulEquiv.refl _⟩⟩
        exact CFSG.Quasithin.SteinbergBY.two_dvd_card_of_statedPSL hSC
      exact one_le_evenRank_of_central_prime Nat.prime_three (by norm_num) hZ h2
    · have hrd : 3 ∣ Nat.card F - 1 := by rw [hcardF4]
      obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
        exists_elemAbelian_le_normalizer_statedProj 1 3 Nat.prime_three (by norm_num) hrd
      exact le_evenRank_of_center_quotient e Nat.prime_three (by norm_num) hZ3 hX hX2 hE
        hEcard hEX
  ·
    have hd3 : 3 ≤ (lab.rank - 1) + 2 := by omega
    have hq : 4 ≤ Fintype.card F := by rw [Fintype.card_eq_nat_card]; exact hF4
    have h34' : ¬ ((lab.rank - 1) + 2 = 3 ∧ Fintype.card F = 4) := by
      rintro ⟨h1, h2⟩
      exact h34 ⟨h1, by rwa [Fintype.card_eq_nat_card] at h2⟩
    have hmult := card_hopfMultiplier_statedProj_eq_center hd3 hq h34'
    obtain ⟨φ, hφ, hφker⟩ := exists_surjective_statedSL_of_model hQ' e hd3 hmult
    obtain ⟨r, hr, hr2, -, hrd0⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one hn
    have hrd : r ∣ Nat.card F - 1 := by rw [hcardF]; exact hrd0
    exact le_evenRank_of_surjective_statedSL_torus hr hr2 hrd hφ hφker


theorem card_center_dvd_center_specialLinearGroup {K : Type} [Group K] [Finite K] {d : ℕ}
    {F : Type} [Field F] [Fintype F] (hQ : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL d F))
    (hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (StatedProj (StatedSL d F))) =
      Nat.card (Subgroup.center (SpecialLinearGroup (Fin d) F))) :
    Nat.card (Subgroup.center K) ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin d) F)) := by
  have h1 := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ e
  rwa [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    hcard] at h1


theorem exists_elemAbelian_le_normalizer_statedProj_six {F : Type} [Field F] [Fintype F]
    [CharP F 2] (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ Nat.card F - 1)
    (hr6 : ¬ r ∣ 6) :
    ∃ E X : Subgroup (StatedProj (StatedSL 6 F)),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 5 ∧
        E ≤ Subgroup.normalizer (X : Set (StatedProj (StatedSL 6 F))) := by
  classical
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hscal : ∀ z : ↥(StatedSL 6 F), (z : GL (Fin 6) F) ∈ diagTorusSixGL (F := F) r →
      (z : GL (Fin 6) F) ∈ StatedScalars (Fin 6) F → (z : GL (Fin 6) F) = 1 := by
    rintro z hzD hzK
    obtain ⟨u, hu⟩ := hzD
    obtain ⟨c, hc⟩ := hzK
    have heq : torusDiag (K := F) (diagVecSucc 5
        (fun j => ((u j : rootsOfUnity r F) : Fˣ))) =
        GeneralLinearGroup.scalar (Fin 6) c := hu.trans hc.symm
    have hentries : ∀ i : Fin 6,
        ((diagVecSucc 5 (fun j => ((u j : rootsOfUnity r F) : Fˣ))) i : Fˣ) = c := by
      intro i
      have h2 := congrFun (congrFun (congrArg
        (fun x : GL (Fin 6) F => (x : Matrix (Fin 6) (Fin 6) F)) heq) i) i
      rw [coe_torusDiag, Matrix.diagonal_apply_eq, GeneralLinearGroup.coe_scalar] at h2
      exact Units.ext (by simpa using h2)
    have hprod6 : c ^ 6 = 1 := by
      have h1 : ∏ i : Fin 6,
          ((diagVecSucc 5 (fun j => ((u j : rootsOfUnity r F) : Fˣ))) i : Fˣ) = 1 :=
        prod_diagVecSucc 5 _
      calc c ^ 6 = ∏ _i : Fin 6, c := by simp
        _ = ∏ i : Fin 6,
            ((diagVecSucc 5 (fun j => ((u j : rootsOfUnity r F) : Fˣ))) i : Fˣ) := by
            exact (Finset.prod_congr rfl fun i _ => hentries i).symm
        _ = 1 := h1
    have hcr : c ^ r = 1 := by
      have h3 : ((u 0 : rootsOfUnity r F) : Fˣ) = c := by
        simpa [diagVecSucc] using hentries (1 : Fin 6)
      rw [← h3]
      exact (u 0).2
    have hgcd : Nat.gcd r 6 = 1 :=
      (Nat.Prime.coprime_iff_not_dvd hr).2 hr6 |>.gcd_eq_one
    have hdvd : orderOf c ∣ Nat.gcd r 6 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcr) (orderOf_dvd_of_pow_eq_one hprod6)
    have hc1 : c = 1 := by
      rw [← orderOf_eq_one_iff]
      exact Nat.dvd_one.mp (hgcd ▸ hdvd)
    rw [← hc, hc1, map_one]
  exact exists_elemAbelian_le_normalizer_statedProj_of 6 r 5 (by omega) hr hr2
    (diagTorusSixGL (F := F) r) (diagTorusSixGL_le_SL r) hscal (card_diagTorusSixGL r hrd)
    (isElemAbelian_diagTorusSixGL r hr) (diagTorusSixGL_le_normalizer_rootSubgroupGL r)

theorem rk2_low_a_five_of_three_le (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .A) (hrank : lab.rank = 5) (hn : 3 ≤ lab.n) :
    5 ≤ evenRank K := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hn1 : 1 ≤ lab.n := by omega
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := 6) (n := lab.n)
      (by simp [markTag, htag]) (by simp [markRank, htag, hrank])
      (by simp [markChar, htag]) (by simp [markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hcardF
  obtain ⟨p, hp, hp5, hpd⟩ :=
    CFSG.RankThree.PartTwo.Census.exists_prime_five_le_dvd_two_pow_sub_one hn
  have hpd' : p ∣ Nat.card F - 1 := by rw [hcardF]; exact hpd
  have hp6 : ¬ p ∣ 6 := by
    intro h
    have hp23 : p = 2 ∨ p = 3 := by
      have h' : p ∣ 2 * 3 := by norm_num at h ⊢; exact h
      rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
    omega
  have hq : 4 ≤ Fintype.card F := by rw [Fintype.card_eq_nat_card]; exact hF4
  have h34 : ¬ ((6 : ℕ) = 3 ∧ Fintype.card F = 4) := by norm_num
  have hmult := card_hopfMultiplier_statedProj_eq_center (d := 6) (by norm_num) hq h34
  have hdvd := card_center_dvd_center_specialLinearGroup hQ' e₀ hmult
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    intro h
    have hdvd' : p ∣ Nat.gcd 6 (Fintype.card F - 1) := by
      rw [card_center_specialLinearGroup_eq_gcd (by norm_num : 1 ≤ 6)] at hdvd
      exact dvd_trans h hdvd
    have hp6' : p ∣ 6 := dvd_trans hdvd' (Nat.gcd_dvd_left _ _)
    exact hp6 hp6' 
  have hp2 : p ≠ 2 := by omega
  obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
    exists_elemAbelian_le_normalizer_statedProj_six p hp hp2 hpd' hp6
  exact le_evenRank_of_center_quotient e₀ hp hp2 hpZ hX hX2 hE hEcard hEX


theorem rk2_low_a_five_of_two (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .A) (hrank : lab.rank = 5) (hn : lab.n = 2)
    (hc : ¬ Subgroup.center K = ⊥) : 5 ≤ evenRank K := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hn1 : 1 ≤ lab.n := by omega
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := 6) (n := lab.n)
      (by simp [markTag, htag]) (by simp [markRank, htag, hrank])
      (by simp [markChar, htag]) (by simp [markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hcardF
  have hFcard : Nat.card F = 4 := by rw [hcardF, hn]; norm_num
  have hq : 4 ≤ Fintype.card F := by rw [Fintype.card_eq_nat_card]; omega
  have h34 : ¬ ((6 : ℕ) = 3 ∧ Fintype.card F = 4) := by norm_num
  have hmult := card_hopfMultiplier_statedProj_eq_center (d := 6) (by norm_num) hq h34
  have hdvd := card_center_dvd_center_specialLinearGroup hQ' e₀ hmult
  have hZ3 : Nat.card (Subgroup.center K) = 3 := by
    have h3 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 6) F)) = 3 := by
      rw [card_center_specialLinearGroup_eq_gcd (by norm_num : 1 ≤ 6)]
      have hF' : Fintype.card F = 4 := by rw [Fintype.card_eq_nat_card]; exact hFcard
      rw [hF']; norm_num
    rw [h3] at hdvd
    have h1 : 1 < Nat.card (Subgroup.center K) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 (by simpa using hc)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · omega
    · exact h
  have hmult' := hmult
  rw [card_center_specialLinearGroup_eq_gcd (by norm_num : 1 ≤ 6)] at hmult'
  obtain ⟨φ, hφ, hφker⟩ := exists_surjective_statedSL_of_model hQ' e₀ (by norm_num) hmult
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff φ, eq_bot_iff]
    intro x hx
    have hcardker := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top] at hcardker
    have hKcard : Nat.card K = Nat.card (StatedProj (StatedSL 6 F)) * 3 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hZ3,
        Nat.card_congr e₀.toEquiv]
    have hSLcard : Nat.card ↥(StatedSL 6 F) = Nat.card (StatedProj (StatedSL 6 F)) * 3 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((StatedScalars (Fin 6) F).subgroupOf (StatedSL 6 F))
      rw [show Nat.card (↥(StatedSL 6 F) ⧸ (StatedScalars (Fin 6) F).subgroupOf
          (StatedSL 6 F)) = Nat.card (StatedProj (StatedSL 6 F)) from rfl] at h
      have hN : Nat.card ↥((StatedScalars (Fin 6) F).subgroupOf (StatedSL 6 F)) = 3 := by
        rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 6 F,
          Subgroup.card_map_of_injective
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 6 F).injective,
          card_center_specialLinearGroup_eq_gcd (by norm_num : 1 ≤ 6)]
        have hF' : Fintype.card F = 4 := by rw [Fintype.card_eq_nat_card]; exact hFcard
        rw [hF']
        norm_num
      rw [hN] at h
      exact h
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h1 : Nat.card φ.ker * Nat.card K = 1 * Nat.card K := by
      rw [one_mul]
      calc Nat.card φ.ker * Nat.card K = Nat.card ↥(StatedSL 6 F) := hcardker
        _ = Nat.card (StatedProj (StatedSL 6 F)) * 3 := hSLcard
        _ = Nat.card K := hKcard.symm
    have hk1 : Nat.card φ.ker = 1 := Nat.mul_right_cancel hpos h1
    rw [Subgroup.card_eq_one.mp hk1] at hx
    exact hx
  have hrd : 3 ∣ Nat.card F - 1 := by rw [hFcard]
  exact le_evenRank_of_injective_statedSL_six Nat.prime_three (by norm_num) hrd hinj

theorem rk2_low_a_five (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (h : lab.tag = .A ∧ lab.rank = 5 ∧ 2 ≤ lab.n)
    (h' : 3 ≤ lab.n ∨ ¬ Subgroup.center K = ⊥) : 5 ≤ evenRank K := by
  obtain ⟨htag, hrank, hn⟩ := h
  rcases h' with h3 | hc
  · exact rk2_low_a_five_of_three_le K lab hK htag hrank h3
  · by_cases hn2 : lab.n = 2
    · exact rk2_low_a_five_of_two K lab hK htag hrank hn2 hc
    · exact rk2_low_a_five_of_three_le K lab hK htag hrank (by omega)

theorem rk2_low_d_three_ge (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .D) (hrank : lab.rank = 3) (hn : 2 ≤ lab.n) :
    3 ≤ evenRank K := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hn1 : 1 ≤ lab.n := by omega
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := 4) (n := lab.n)
      (by simp [markTag, htag, hrank]) (by simp [markRank, htag, hrank])
      (by simp [markChar, htag]) (by simp [markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hcardF
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
  have hq : 4 ≤ Fintype.card F := by rw [Fintype.card_eq_nat_card]; exact hF4
  have h34 : ¬ ((4 : ℕ) = 3 ∧ Fintype.card F = 4) := by norm_num
  have hmult := card_hopfMultiplier_statedProj_eq_center (d := 4) (by norm_num) hq h34
  have hdvd := card_center_dvd_center_specialLinearGroup hQ' e₀ hmult
  have hZSL : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 4) F)) = 1 := by
    rw [card_center_specialLinearGroup_eq_gcd (by norm_num : 1 ≤ 4)]
    have hF' : Fintype.card F = 2 ^ lab.n := by rw [Fintype.card_eq_nat_card, hcardF]
    have hodd : Odd (Fintype.card F - 1) := by
      rw [hF']
      have heven : Even (2 ^ lab.n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
      have hpos : 0 < 2 ^ lab.n := by positivity
      exact Nat.Even.sub_odd hpos heven odd_one
    have hcop : Nat.Coprime 4 (Fintype.card F - 1) := by
      have h := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
      simpa using h
    rw [Nat.Coprime.gcd_eq_one hcop]
  have hZ1 : Nat.card (Subgroup.center K) = 1 := by
    rw [hZSL] at hdvd
    exact Nat.dvd_one.mp hdvd
  obtain ⟨φ, hφ, hφker⟩ := exists_surjective_statedSL_of_model hQ' e₀ (by norm_num) hmult
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff φ, eq_bot_iff]
    intro x hx
    have hcardker := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top] at hcardker
    have hKcard : Nat.card K = Nat.card (StatedProj (StatedSL 4 F)) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hZ1,
        Nat.card_congr e₀.toEquiv, mul_one]
    have hSLcard : Nat.card ↥(StatedSL 4 F) = Nat.card (StatedProj (StatedSL 4 F)) := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F))
      rw [show Nat.card (↥(StatedSL 4 F) ⧸ (StatedScalars (Fin 4) F).subgroupOf
          (StatedSL 4 F)) = Nat.card (StatedProj (StatedSL 4 F)) from rfl] at h
      have hN : Nat.card ↥((StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F)) = 1 := by
        rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 4 F,
          Subgroup.card_map_of_injective
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 F).injective,
          hZSL]
      rw [hN, mul_one] at h
      exact h
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h1 : Nat.card φ.ker * Nat.card K = 1 * Nat.card K := by
      rw [one_mul]
      calc Nat.card φ.ker * Nat.card K = Nat.card ↥(StatedSL 4 F) := hcardker
        _ = Nat.card (StatedProj (StatedSL 4 F)) := hSLcard
        _ = Nat.card K := hKcard.symm
    have hk1 : Nat.card φ.ker = 1 := Nat.mul_right_cancel hpos h1
    rw [Subgroup.card_eq_one.mp hk1] at hx
    exact hx
  obtain ⟨r, hr, hr2, -, hrd0⟩ :=
    CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one hn
  have hrd : r ∣ Nat.card F - 1 := by rw [hcardF]; exact hrd0
  exact le_evenRank_of_injective_statedSL_four hr hr2 hrd hinj

section BlockLevi

open CFSG.RankThree.PartTwo.Census CFSG.Assembly.RankThreeEven

variable {K : Type} [Field K] [CharP K 2]

@[expose] def kBlockMat (k : ℕ) (a : Fin k → ZMod 3) :
    Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) K :=
  blockDiagonal fun b => CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a b).val

theorem kBlockMat_add (k : ℕ) (a a' : Fin k → ZMod 3) :
    kBlockMat (K := K) k (a + a') = kBlockMat k a * kBlockMat k a' := by
  rw [kBlockMat, kBlockMat, kBlockMat, ← blockDiagonal_mul]
  congr 1
  funext b
  rw [Pi.add_apply, threeCycleMat_pow_val_add]

theorem det_kBlockMat (k : ℕ) (a : Fin k → ZMod 3) :
    (kBlockMat (K := K) k a).det = 1 := by
  rw [kBlockMat, det_blockDiagonal]
  exact Finset.prod_eq_one fun b _ => by rw [det_pow, det_threeCycleMat, one_pow]

abbrev KBlockIdx (k m : ℕ) : Type := (Fin 2 × Fin k) ⊕ Fin m

@[expose] def kSHom (k m : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Fin k → ZMod 3) →* SpecialLinearGroup (KBlockIdx k m) K where
  toFun a := ⟨fromBlocks (kBlockMat k a.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_kBlockMat, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (kBlockMat k (0 : Fin k → ZMod 3)) 0 0 1 = (1 : Matrix (KBlockIdx k m) _ K)
    rw [← fromBlocks_one, kBlockMat]
    congr 1
    rw [← blockDiagonal_one]
    congr 1)
  map_mul' a b := Subtype.ext (by
    change fromBlocks (kBlockMat k (a.toAdd + b.toAdd)) 0 0 1 =
      fromBlocks (kBlockMat k a.toAdd) 0 0 1 * fromBlocks (kBlockMat k b.toAdd) 0 0 1
    rw [fromBlocks_multiply, kBlockMat_add]
    simp)

theorem coe_kSHom (k m : ℕ) (a : Multiplicative (Fin k → ZMod 3)) :
    ((kSHom k m K a : SpecialLinearGroup (KBlockIdx k m) K) :
      Matrix (KBlockIdx k m) (KBlockIdx k m) K) = fromBlocks (kBlockMat k a.toAdd) 0 0 1 :=
  rfl

@[expose] def kYMat (k : ℕ) [NeZero k] (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) K :=
  Matrix.of fun ib jb => if ib.2 = 0 ∧ jb.2 = 1 then X ib.1 jb.1 else 0

theorem kYMat_mul_kYMat (k : ℕ) [NeZero k] (hk : 2 ≤ k) (X X' : Matrix (Fin 2) (Fin 2) K) :
    kYMat (K := K) k X * kYMat k X' = 0 := by
  ext ib jb
  simp only [mul_apply, kYMat, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun kc _ => ?_
  by_cases h : kc.2 = 1
  · have : ¬ (kc.2 = 0 ∧ jb.2 = 1) := by
      rintro ⟨h0, -⟩
      have h01 : (0 : Fin k) = 1 := h0.symm.trans h
      have hval := congrArg Fin.val h01
      rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < k)] at hval
      omega
    rw [ite_eq_right this, mul_zero]
  · have : ¬ (ib.2 = 0 ∧ kc.2 = 1) := fun h' => h h'.2
    rw [ite_eq_right this, zero_mul]

theorem kYMat_add (k : ℕ) [NeZero k] (X X' : Matrix (Fin 2) (Fin 2) K) :
    kYMat (K := K) k (X + X') = kYMat k X + kYMat k X' := by
  ext ib jb
  simp only [kYMat, of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem one_add_kYMat_mul (k : ℕ) [NeZero k] (hk : 2 ≤ k) (X X' : Matrix (Fin 2) (Fin 2) K) :

    (1 + kYMat (K := K) k X) * (1 + kYMat k X') = 1 + kYMat k (X + X') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, kYMat_mul_kYMat k hk, add_zero,
    kYMat_add]
  abel

theorem det_one_add_kYMat (k : ℕ) [NeZero k] (hk : 2 ≤ k) (X : Matrix (Fin 2) (Fin 2) K) :
    (1 + kYMat (K := K) k X).det = 1 := by
  have hX : X + X = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
  refine eq_one_of_mul_self_eq_one ?_
  rw [← det_mul, one_add_kYMat_mul k hk, hX]
  have hzero : kYMat (K := K) k (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    ext i j
    simp [kYMat]
  rw [hzero, add_zero, det_one]

@[expose] def kUHom (k m : ℕ) [NeZero k] (hk : 2 ≤ k) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Matrix (Fin 2) (Fin 2) K) →* SpecialLinearGroup (KBlockIdx k m) K where
  toFun X := ⟨fromBlocks (1 + kYMat k X.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_one_add_kYMat k hk, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (1 + kYMat k (0 : Matrix (Fin 2) (Fin 2) K)) 0 0 1 =
      (1 : Matrix (KBlockIdx k m) _ K)
    rw [← fromBlocks_one]
    congr 1
    ext i j
    simp [kYMat])
  map_mul' X X' := Subtype.ext (by
    change fromBlocks (1 + kYMat k (X.toAdd + X'.toAdd)) 0 0 1 =
      fromBlocks (1 + kYMat (K := K) k X.toAdd) 0 0 1 *
        fromBlocks (1 + kYMat k X'.toAdd) 0 0 1
    rw [fromBlocks_multiply, one_add_kYMat_mul k hk]
    simp)

theorem kBlockMat_mul_kYMat {k : ℕ} [NeZero k] (hk : 2 ≤ k) (a : Fin k → ZMod 3)
    (X : Matrix (Fin 2) (Fin 2) K) :
    kBlockMat k a * kYMat k X =
      kYMat k (threeCycleMat K ^ (a 0).val * X * threeCycleMat K ^ (-(a 1)).val) *
        kBlockMat k a := by
  set X' := threeCycleMat K ^ (a 0).val * X * threeCycleMat K ^ (-(a 1)).val with hX'
  have key : threeCycleMat K ^ (a 0).val * X = X' * threeCycleMat K ^ (a 1).val := by
    rw [hX', mul_assoc _ (threeCycleMat K ^ (-(a 1)).val), ← threeCycleMat_pow_val_add,
      show -(a 1) + a 1 = 0 from neg_add_cancel _, ZMod.val_zero, pow_zero, mul_one]
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp only [mul_apply, Fintype.sum_prod_type, kBlockMat, blockDiagonal_apply, kYMat, of_apply]
  by_cases h : b = 0 ∧ b' = 1
  · obtain ⟨rfl, rfl⟩ := h
    have := congrFun (congrFun key i) j
    simp only [mul_apply] at this
    simpa [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
  · have h1 : ∀ kk c, (if b = c then (threeCycleMat K ^ (a b).val) i kk else 0) *
        (if c = 0 ∧ b' = 1 then X kk j else 0) = 0 := by
      intro kk c
      by_cases hbc : b = c
      · subst hbc
        rw [ite_eq_right h, mul_zero]
      · rw [ite_eq_right hbc, zero_mul]
    have h2 : ∀ kk c, (if b = 0 ∧ c = 1 then X' i kk else 0) *
        (if c = b' then (threeCycleMat K ^ (a c).val) kk j else 0) = 0 := by
      intro kk c
      by_cases hc : c = b'
      · subst hc
        rw [ite_eq_right h, zero_mul]
      · rw [ite_eq_right hc, mul_zero]
    simp only [h1, h2, Finset.sum_const_zero]

theorem eq_one_of_kSHom_entry {k m : ℕ} {a : Multiplicative (Fin k → ZMod 3)}
    (h : ∀ b : Fin k, ((kSHom k m K a : SpecialLinearGroup (KBlockIdx k m) K) :
      Matrix (KBlockIdx k m) (KBlockIdx k m) K) (.inl (0, b)) (.inl (1, b)) = 0) :
    a = 1 := by
  apply Multiplicative.toAdd.injective
  funext b
  have hb := h b
  rw [coe_kSHom, fromBlocks_apply₁₁, kBlockMat, blockDiagonal_apply] at hb
  simp only [ite_true] at hb
  exact threeCycleMat_pow_val_zero_one hb

open CFSG.RankThree.PartTwo.Census CFSG.Assembly.RankThreeEven in
theorem exists_elemAbelian_le_normalizer_PSL_blocks [Finite K] (m : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    ∃ E X : Subgroup (ProjectiveSpecialLinearGroup (KBlockIdx k m) K),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧
        E ≤ Subgroup.normalizer (X : Set (ProjectiveSpecialLinearGroup (KBlockIdx k m) K)) := by
  haveI : NeZero k := ⟨by omega⟩
  set φ := kSHom k m K
  set ψ := kUHom k m hk K
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr fun a ha =>
      eq_one_of_kSHom_entry (K := K) (m := m) fun b => ?_
    rw [ha]
    simp
  have hE : IsElemAbelian 3 φ.range := by
    refine isElemAbelian_range (fun a => ?_) φ
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext b
    change 3 • (Multiplicative.toAdd a b) = 0
    generalize Multiplicative.toAdd a b = x
    revert x
    decide
  have hEcard : Nat.card φ.range = 3 ^ k := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hEcent : φ.range ⊓ Subgroup.center (SpecialLinearGroup (KBlockIdx k m) K) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, hxc⟩
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    have ha : a = 1 := eq_one_of_kSHom_entry (K := K) (m := m) fun b => by
      rw [← hc]
      simp
    rw [Subgroup.mem_bot, ha, map_one]
  have hX2 : IsPGroup 2 ψ.range := by
    intro y
    obtain ⟨X, hX⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hX, ← map_mul, OneMemClass.coe_one]
    have hXX : X * X = 1 := by
      apply Multiplicative.toAdd.injective
      ext i j
      simp only [toAdd_mul, toAdd_one, Matrix.add_apply, Matrix.zero_apply,
        CharTwo.add_self_eq_zero]
    rw [hXX, map_one]
  have hXcent : ¬ ψ.range ≤ Subgroup.center (SpecialLinearGroup (KBlockIdx k m) K) := by
    intro hP
    have h1 : ψ (Multiplicative.ofAdd 1) ∈ ψ.range := ⟨_, rfl⟩
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hP h1)
    have this : (scalar (KBlockIdx k m) c) (.inl (0, 0)) (.inl (0, 1)) =
        (fromBlocks (1 + kYMat k (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 1 :
          Matrix (KBlockIdx k m) (KBlockIdx k m) K) (.inl (0, 0)) (.inl (0, 1)) := by
      rw [hc]
      rfl
    have h01 : (0 : Fin k) ≠ 1 := by
      intro h
      have hval := congrArg Fin.val h
      rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < k)] at hval
      omega
    simp [Matrix.scalar_apply, kYMat, Matrix.one_apply, h01, Prod.mk.injEq] at this
  have hEnorm : φ.range ≤ Subgroup.normalizer (ψ.range : Set
      (SpecialLinearGroup (KBlockIdx k m) K)) := by
    refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨a, rfl⟩ _ ⟨X, rfl⟩
    refine ⟨Multiplicative.ofAdd (threeCycleMat K ^ (a.toAdd 0).val * X.toAdd *
      threeCycleMat K ^ (-(a.toAdd 1)).val), ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    refine Subtype.ext ?_
    change fromBlocks (1 + kYMat k _) 0 0 1 * fromBlocks (kBlockMat k a.toAdd) 0 0 1 =
      fromBlocks (kBlockMat k a.toAdd) 0 0 1 * fromBlocks (1 + kYMat k X.toAdd) 0 0 1
    rw [fromBlocks_multiply, fromBlocks_multiply, mul_add, add_mul, kBlockMat_mul_kYMat hk]
    simp
  let π : SpecialLinearGroup (KBlockIdx k m) K →* ProjectiveSpecialLinearGroup (KBlockIdx k m) K :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (KBlockIdx k m) K))
  have hX0 : ψ.range.map π ≠ ⊥ := by
    intro h
    apply hXcent
    intro x hx
    have : π x ∈ ψ.range.map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  refine ⟨φ.range.map π, ψ.range.map π, hX0, hX2.map π, hE.map π, ?_, ?_⟩
  · rw [card_map_mk_of_inf_eq_bot (Subgroup.center (SpecialLinearGroup (KBlockIdx k m) K))
      hEcent, hEcard]
  · exact (Subgroup.map_mono hEnorm).trans (Subgroup.le_normalizer_map π)

open CFSG.RankThree.PartTwo.Census CFSG.Assembly.RankThreeEven in
theorem exists_elemAbelian_le_normalizer_PSL_of_card [Finite K] {n k m : ℕ}
    (hn : n = 2 * k + m) (hk : 2 ≤ k) :
    ∃ E X : Subgroup (ProjectiveSpecialLinearGroup (Fin n) K),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧
        E ≤ Subgroup.normalizer (X : Set (ProjectiveSpecialLinearGroup (Fin n) K)) := by
  obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ := exists_elemAbelian_le_normalizer_PSL_blocks (K := K) m hk
  have hcard : Fintype.card (KBlockIdx k m) = n := by
    simp only [KBlockIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  let e : KBlockIdx k m ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let φ : ProjectiveSpecialLinearGroup (KBlockIdx k m) K →*
      ProjectiveSpecialLinearGroup (Fin n) K := (pslReindex K e).toMonoidHom
  have hφ : Function.Injective φ := (pslReindex K e).injective
  refine ⟨E.map φ, X.map φ, ?_, hX2.map φ, hE.map φ, ?_, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff, (MonoidHom.ker_eq_bot_iff φ).mpr hφ, le_bot_iff] at hbot
    exact hX hbot
  · rw [Subgroup.card_map_of_injective hφ, hEcard]
  · exact (Subgroup.map_mono hEX).trans (Subgroup.le_normalizer_map φ)

end BlockLevi

theorem rk2_low_a_one (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .A) (hn : lab.n = 1) :
    (lab.rank + 1) / 2 ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hlab' := hlab
  simp only [CFSG.Assembly.LargeEvenInLambda2, htag] at hlab'
  obtain ⟨-, hrank1, hrankone⟩ := hlab'
  have hrank2 : 2 ≤ lab.rank := by
    by_contra h
    have hr1 : lab.rank = 1 := by omega
    have := hrankone hr1
    omega
  have hn1 : 1 ≤ lab.n := by omega
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := lab.rank + 1) (n := lab.n)
      (by simp [markTag, htag]) (by simp [markRank, htag])
      (by simp [markChar, htag]) (by simp [markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hcardF
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL (lab.rank + 1) 2 1 := by
    simpa [CFSG.StandardType.MarkedModel, markTag, markRank, markChar, markDeg, htag, hn]
      using hM
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) :=
    not_three_dvd_center_of_psl_two_one hQ' hM'
  by_cases hrank_two : lab.rank = 2
  · have eP : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL 3 F) := by
      have h3 : lab.rank + 1 = 3 := by omega
      exact h3 ▸ e₀
    obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
      exists_elemAbelian_le_normalizer_statedProj_three (F := F)
    have h1 : 1 ≤ evenRank K :=
      le_evenRank_of_center_quotient eP Nat.prime_three (by norm_num) hZ hX hX2 hE hEcard hEX
    rw [hrank_two]
    simpa using h1
  · have hrank3 : 3 ≤ lab.rank := by omega
    set d := lab.rank + 1 with hd_def
    have hd4 : 4 ≤ d := by omega
    obtain ⟨k, m, hk, hm, hkm⟩ : ∃ k m : ℕ, 2 ≤ k ∧ m < 2 ∧ d = 2 * k + m := by
      refine ⟨d / 2, d % 2, ?_, ?_, ?_⟩
      · exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
      · exact Nat.mod_lt _ (by norm_num)
      · have h := Nat.div_add_mod d 2
        omega
    obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
      exists_elemAbelian_le_normalizer_PSL_of_card (K := F) (n := d) (k := k) (m := m) hkm hk
    let eP : K ⧸ Subgroup.center K ≃* ProjectiveSpecialLinearGroup (Fin d) F :=
      e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d F).symm
    have hbound : k ≤ evenRank K :=
      le_evenRank_of_center_quotient eP Nat.prime_three (by norm_num) hZ hX hX2 hE hEcard hEX
    have hgoal : (lab.rank + 1) / 2 = k := by
      rw [← hd_def]
      omega
    rwa [hgoal]

theorem rk2_low_d_three_one (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .D) (hrank : lab.rank = 3) (hn : lab.n = 1) :
    lab.rank - 1 ≤ evenRank K := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hn1 : 1 ≤ lab.n := by omega
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := 4) (n := lab.n)
      (by simp [markTag, htag, hrank]) (by simp [markRank, htag, hrank])
      (by simp [markChar, htag]) (by simp [markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hcardF
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL 4 2 1 := by
    simpa [CFSG.StandardType.MarkedModel, markTag, markRank, markChar, markDeg, htag, hrank, hn]
      using hM
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) :=
    not_three_dvd_center_of_psl_two_one hQ' hM'
  obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
    exists_elemAbelian_le_normalizer_PSL_of_card (K := F) (n := 4) (k := 2) (m := 0)
      (by norm_num) (by norm_num)
  let eP : K ⧸ Subgroup.center K ≃* ProjectiveSpecialLinearGroup (Fin 4) F :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F).symm
  have h2 : 2 ≤ evenRank K :=
    le_evenRank_of_center_quotient eP Nat.prime_three (by norm_num) hZ hX hX2 hE hEcard hEX
  rw [hrank]
  simpa using h2

end CFSG.LocalAnalysis.GLTheoremA
