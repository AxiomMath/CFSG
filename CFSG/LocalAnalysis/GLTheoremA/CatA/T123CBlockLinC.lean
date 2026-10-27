module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinPSL
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.S11d.LayerDecomp
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCUnitaryPlane

section GeneralLinear

open scoped _root_.Classical

variable {n : ℕ} {K : Type} [Field K]

theorem commute_toLin'_of_mul_eq {g h : GL (Fin n) K} (hgh : g * h = h * g) :
    Commute (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K))
      (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)) := by
  rw [← toLinAlgEquiv'_eq_toLin', ← toLinAlgEquiv'_eq_toLin']
  exact (Commute.units_val hgh).map Matrix.toLinAlgEquiv'

theorem comap_toGL_of_le {X : Set (SpecialLinearGroup (Fin n) K)} {G : Subgroup (GL (Fin n) K)}
    (hr : G ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range)
    (hq : CFSG.IsQuasisimple ↥G)
    (hc : ∀ x ∈ X, ∀ β ∈ G, SpecialLinearGroup.toGL x * β = β * SpecialLinearGroup.toGL x)
    (hN : ∀ g : GL (Fin n) K,
      (∀ x ∈ X, g * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * g) →
      ∀ β ∈ G, g * β * g⁻¹ ∈ G) :
    G.comap SpecialLinearGroup.toGL ≤ Subgroup.centralizer X ∧
      (∀ g ∈ Subgroup.centralizer X, ∀ y ∈ G.comap SpecialLinearGroup.toGL,
        g * y * g⁻¹ ∈ G.comap SpecialLinearGroup.toGL) ∧
      CFSG.IsQuasisimple ↥(G.comap SpecialLinearGroup.toGL) := by
  have hinj : Function.Injective
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K) :=
    SpecialLinearGroup.toGL_injective
  refine ⟨fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hinj ?_,
    fun g hg y hy => ?_, ?_⟩
  · rw [map_mul, map_mul]
    exact hc x hx _ hy
  · have hg' : ∀ x ∈ X, SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL x =
        SpecialLinearGroup.toGL x * SpecialLinearGroup.toGL g := fun x hx => by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hg x hx]
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hN _ hg' _ hy
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hr)).symm.trans
        (Subgroup.equivMapOfInjective _ _ hinj).symm) hq

theorem dvd_card_comap_toGL {p : ℕ} {G : Subgroup (GL (Fin n) K)}
    (hr : G ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range)
    (hq : CFSG.IsQuasisimple ↥(G.comap SpecialLinearGroup.toGL))
    (hd : p ∣ Nat.card (↥G ⧸ Subgroup.center ↥G)) :
    p ∣ Nat.card (↥(G.comap SpecialLinearGroup.toGL) ⧸
      Subgroup.center ↥(G.comap SpecialLinearGroup.toGL)) := by
  have h := card_center_quot_map SpecialLinearGroup.toGL (fun g hg => by
      rw [SpecialLinearGroup.toGL_injective (hg.trans (map_one _).symm)]
      exact Subgroup.one_mem _)
    (I142N.comm_self_eq_of_commutator_top hq.1.commutator_eq_top)
  rw [Subgroup.map_comap_eq_self hr] at h
  rwa [← h]

theorem goodBlock_of_le_blockImage [Finite K] {y : Module.End K (Fin n → K)}
    (hy : Squarefree (minpoly K y)) {b : primaryFactors y} {P : Subgroup (GL (Fin n) K)}
    (hP : CFSG.IsQuasisimple ↥P) (hPb : P ≤ blockImage hy b) : GoodBlock b := by
  by_contra hg
  haveI := isSolvable_of_not_goodBlock hg
  haveI : Group.IsSolvable (SpecialLinearGroup (Fin (mult y b)) (Efac y b)) :=
    Group.isSolvable_of_isSolvable_injective SpecialLinearGroup.toGL_injective
  set φ : SpecialLinearGroup (Fin (mult y b)) (Efac y b) →* GL (Fin n) K :=
    (blockTheta hy).comp (blockEmbed (Efac y) (mult y) b) with hφ
  have hle : P ≤ φ.range := fun g hg => by
    obtain ⟨s, hs⟩ := mem_blockImage.mp (hPb hg)
    exact ⟨s, hs⟩
  haveI : Group.IsSolvable ↥φ.range := Group.isSolvable_of_surjective φ.rangeRestrict_surjective
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  haveI := hP.1
  haveI := hP.2.1
  obtain ⟨u, v, huv⟩ := exists_pair_ne (↥P ⧸ Subgroup.center ↥P)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  have hu : u = 1 := eq_one_of_perfect_of_isSolvable (MonoidHom.id ↥P) u
  have hv : v = 1 := eq_one_of_perfect_of_isSolvable (MonoidHom.id ↥P) v
  rw [hu, hv] at huv
  exact huv rfl

end GeneralLinear

section Perfect

private theorem exists_derivedSeries_succ_eq (G : Type*) [Group G] [Finite G] :
    ∃ k : ℕ, derivedSeries G (k + 1) = derivedSeries G k := by
  by_contra h
  push Not at h
  have hlt : ∀ k, Nat.card (derivedSeries G (k + 1)) < Nat.card (derivedSeries G k) := by
    intro k
    have hle : derivedSeries G (k + 1) ≤ derivedSeries G k := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_le_left _ _
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (h k))
  have hbound : ∀ k, Nat.card (derivedSeries G k) + k ≤ Nat.card G := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hlt k
      omega
  have h1 := hbound (Nat.card G + 1)
  have h2 : 0 < Nat.card (derivedSeries G (Nat.card G + 1)) := Nat.card_pos
  omega

private theorem exists_isPerfect_ne_bot {G : Type*} [Group G] [Finite G]
    (h : ¬ Group.IsSolvable G) : ∃ D : Subgroup G, Group.IsPerfect ↥D ∧ D ≠ ⊥ := by
  obtain ⟨k, hk⟩ := exists_derivedSeries_succ_eq G
  refine ⟨derivedSeries G k, ?_, fun hbot => h ⟨⟨k, hbot⟩⟩⟩
  rw [Subgroup.isPerfect_iff, ← derivedSeries_succ, hk]

end Perfect

section Plane

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] {E0 : Subgroup (SpecialLinearGroup (Fin n) K)}
  [Fintype E0] [IsMulCommutative E0]

local notation "ρ₀" => planeRep E0

variable (hP : IsPlane p E0)
include hP

omit [IsMulCommutative E0] in
theorem not_mem_zpowers_of_mem {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {a' : ↥E0}
    (ha'L : a' ∈ L) (ha'1 : a' ≠ 1) {b : ↥E0} (hbL : b ∉ L) : a' ∉ Subgroup.zpowers b := by
  intro h
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h
    exact ha'1 h
  have heq : Subgroup.zpowers a' = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h) (le_of_eq (by
      rw [mem_lines.mp (hP.zpowers_mem_lines hb1), mem_lines.mp (hP.zpowers_mem_lines ha'1)]))
  exact hbL (Subgroup.zpowers_le.mpr ha'L (heq ▸ Subgroup.mem_zpowers b))

omit [IsMulCommutative E0] in
theorem eq_zpowers_of_mem {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {b : ↥E0} (hbL : b ∈ L)
    (hb1 : b ≠ 1) : L = Subgroup.zpowers b :=
  (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbL) (le_of_eq (by
    rw [mem_lines.mp hL, mem_lines.mp (hP.zpowers_mem_lines hb1)]))).symm

variable (hpK : (p : K) ≠ 0)
include hpK

theorem not_exists_aeval_fixed [Finite K] (hq1 : ¬ p ∣ Nat.card K - 1) {L' : Subgroup ↥E0}
    (hL' : L' ∈ lines p E0) {a' : ↥E0} (ha' : a' ∈ L') {b : ↥E0} (hb : b ∉ L') {y : Fin n → K}
    (hy : y ∈ LinearMap.range (projLine ρ₀ L')) (hy0 : y ≠ 0) :
    ¬ ∃ f : K[X], ∀ v ∈ primaryComponent (act ρ₀ a') (X - C 1),
      act ρ₀ b v = aeval (act ρ₀ a') f v := by
  rintro ⟨f, hf⟩
  have hfix : act ρ₀ a' y = y := fix_range_projLine E0 ha' y hy
  have hyc : y ∈ primaryComponent (act ρ₀ a') (X - C 1) := by
    rw [mem_primaryComponent]
    simp [hfix]
  have hby : act ρ₀ b y = f.eval 1 • y := by
    rw [hf y hyc, aeval_apply_of_apply_eq hfix]
  have hpow : ∀ k : ℕ, act ρ₀ (b ^ k) y = f.eval 1 ^ k • y := by
    intro k
    induction k with
    | zero => simp [act_one]
    | succ k ih =>
      rw [pow_succ' b k, act_mul, Module.End.mul_apply, ih, map_smul, hby, smul_smul, ← pow_succ]
  have h1 : f.eval 1 ^ p = 1 := by
    have h2 := hpow p
    rw [hP.pow b, act_one, Module.End.one_apply] at h2
    by_contra hne
    have h3 : (f.eval 1 ^ p - 1) • y = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact hy0 ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne))
  letI : Fintype K := Fintype.ofFinite K
  have h4 : f.eval 1 = 1 :=
    eq_one_of_pow_eq_one_of_not_dvd hP.prime (by rwa [← Nat.card_eq_fintype_card]) h1
  rw [h4, one_smul] at hby
  exact hy0 (eq_zero_of_mem_range_projLine hP hpK hL' hb hy hby)

theorem not_exists_aeval_mixed {L M : Subgroup ↥E0} (hM : M ∈ lines p E0) {b : ↥E0}
    (hbL : b ∈ L) (hbM : b ∉ M) {a' : ↥E0} {h : K[X]} (hh : h ∈ primaryFactors (act ρ₀ a'))
    {u : Fin n → K} (hu : u ∈ primaryComponent (act ρ₀ a') h)
    (huL : u ∈ LinearMap.range (projLine ρ₀ L)) (hu0 : u ≠ 0) {y : Fin n → K}
    (hy : y ∈ primaryComponent (act ρ₀ a') h) (hyM : y ∈ LinearMap.range (projLine ρ₀ M))
    (hy0 : y ≠ 0) :
    ¬ ∃ f : K[X], ∀ v ∈ primaryComponent (act ρ₀ a') h, act ρ₀ b v = aeval (act ρ₀ a') f v := by
  rintro ⟨f, hf⟩
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hfu : aeval (act ρ₀ a') f u = u := by
    rw [← hf u hu]
    exact fix_range_projLine E0 hbL u huL
  have ht : AdjoinRoot.mk h f = 1 := by
    by_contra hne
    have h1 : (AdjoinRoot.mk h f - 1) • (⟨u, hu⟩ : primaryComponent (act ρ₀ a') h) = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]
      exact Subtype.ext ((coe_mk_smul_primaryComponent (act ρ₀ a') h f ⟨u, hu⟩).trans hfu)
    have h2 := congrArg ((AdjoinRoot.mk h f - 1)⁻¹ • ·) h1
    simp only [smul_zero, inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h2
    exact hu0 (congrArg Subtype.val h2)
  have hfy : aeval (act ρ₀ a') f y = y := by
    have h3 := coe_mk_smul_primaryComponent (act ρ₀ a') h f ⟨y, hy⟩
    rw [ht, one_smul] at h3
    exact h3.symm
  rw [← hf y hy] at hfy
  exact hy0 (eq_zero_of_mem_range_projLine hP hpK hM hbM hyM hfy)

theorem primaryComponent_auxEnd_le {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {b c : ↥E0}
    (hbL : b ∈ L) (hcL : c ∉ L) (j : ℕ) {h : K[X]} (hh : h ∈ primaryFactors (auxEnd E0 c 1 L))
    (hX : h ≠ X - C 1) :
    primaryComponent (auxEnd E0 c 1 L) h ≤ primaryComponent (act ρ₀ (b ^ j * c)) h := by
  intro v hv
  have hvL := mem_range_projLine_of_mem_primaryComponent hP hpK hL hcL hh hX hv
  have hagree : ∀ w ∈ LinearMap.range (projLine ρ₀ L),
      act ρ₀ (b ^ j * c) w = auxEnd E0 c 1 L w := by
    intro w hw
    rw [auxEnd_apply_of_mem_range hP hpK hL c 1 hw, act_mul, Module.End.mul_apply]
    exact fix_range_projLine E0 (L.pow_mem hbL j) _ (stable_range_projLine E0 c L w hw)
  rw [mem_primaryComponent, aeval_apply_eq_of_agree (stable_range_projLine E0 _ L) hagree h hvL]
  exact mem_primaryComponent.mp hv

omit hP hpK in
theorem mem_primaryComponent_mul_pow {M : Subgroup ↥E0} {b c : ↥E0} (hcM : c ∈ M) {j : ℕ}
    {h h₂ : K[X]} (hdvd : h₂ ∣ h.comp (X ^ j)) {y : Fin n → K}
    (hyM : y ∈ LinearMap.range (projLine ρ₀ M)) (hy : y ∈ primaryComponent (act ρ₀ b) h₂) :
    y ∈ primaryComponent (act ρ₀ (b ^ j * c)) h := by
  have hagree : ∀ w ∈ LinearMap.range (projLine ρ₀ M),
      act ρ₀ (b ^ j * c) w = (act ρ₀ b ^ j) w := by
    intro w hw
    rw [act_mul, Module.End.mul_apply, fix_range_projLine E0 hcM w hw, act_pow]
  have h5 : aeval (act ρ₀ b ^ j) h = aeval (act ρ₀ b) (h.comp (X ^ j)) := by
    rw [aeval_comp]
    simp
  obtain ⟨q, hq⟩ := hdvd
  rw [mem_primaryComponent, aeval_apply_eq_of_agree (stable_range_projLine E0 _ M) hagree h hyM,
    h5, hq, mul_comm h₂ q, map_mul, Module.End.mul_apply, mem_primaryComponent.mp hy, map_zero]

theorem exists_blocks_of_goodBlock [Finite K] (hp2 : p ≠ 2) (hq1 : ¬ p ∣ Nat.card K - 1)
    (hq2 : p ∣ Nat.card K ^ 2 - 1) {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (c d : ↥E0)
    {a : K[X]} (ha : a ∈ primaryFactors (auxEnd E0 c d L))
    (hg : GoodBlock (⟨a, ha⟩ : primaryFactors (auxEnd E0 c d L)))
    (hEa : ∀ e : ↥E0, ∃ f : K[X], ∀ v ∈ primaryComponent (auxEnd E0 c d L) a,
      act ρ₀ e v = aeval (auxEnd E0 c d L) f v)
    (â a' : ↥E0) {b : K[X]} (hb : b ∈ primaryFactors (act ρ₀ a'))
    (hab : primaryComponent (auxEnd E0 c d L) a ≤ primaryComponent (act ρ₀ a') b)
    (hâb : ¬ ∃ f : K[X], ∀ v ∈ primaryComponent (act ρ₀ a') b,
      act ρ₀ â v = aeval (act ρ₀ a') f v) :
    ∃ P M : Subgroup (SpecialLinearGroup (Fin n) K),
      P ≤ Subgroup.centralizer (E0 : Set (SpecialLinearGroup (Fin n) K)) ∧
      (∀ g ∈ Subgroup.centralizer (E0 : Set (SpecialLinearGroup (Fin n) K)), ∀ y ∈ P,
        g * y * g⁻¹ ∈ P) ∧ CFSG.IsQuasisimple ↥P ∧
      M ≤ Subgroup.centralizer ({(a' : SpecialLinearGroup (Fin n) K)} : Set _) ∧
      (∀ g ∈ Subgroup.centralizer ({(a' : SpecialLinearGroup (Fin n) K)} : Set _), ∀ y ∈ M,
        g * y * g⁻¹ ∈ M) ∧ CFSG.IsQuasisimple ↥M ∧
      P ≤ M ∧ p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) ∧
      (â : SpecialLinearGroup (Fin n) K) ∉ Subgroup.centralizer (M : Set _) := by
  have hp0 : p ≠ 0 := hP.prime.ne_zero
  have hx := squarefree_minpoly_auxEnd hP hpK hL c d
  have hxp := auxEnd_pow_eq_one hP hpK hL c d
  have hyp : act ρ₀ a' ^ p = 1 := by rw [← act_pow, hP.pow a', act_one]
  have hy := squarefree_minpoly_of_pow_eq_one hpK hyp
  have hPq := isQuasisimple_blockImage_of_good hx ⟨a, ha⟩ hg
  have hPr := blockImage_le_range_toGL_of_good hx ⟨a, ha⟩ hg
  have hPc : ∀ e : ↥E0, ∀ β ∈ blockImage hx ⟨a, ha⟩,
      SpecialLinearGroup.toGL (e : SpecialLinearGroup (Fin n) K) * β =
        β * SpecialLinearGroup.toGL (e : SpecialLinearGroup (Fin n) K) := by
    intro e β hβ
    obtain ⟨f, hf⟩ := hEa e
    exact commute_of_mem_blockImage hx
      (g := SpecialLinearGroup.toGL (e : Matrix.SpecialLinearGroup (Fin n) K))
      (commute_act_auxEnd E0 e c d L) f hf hβ
  have hPN : ∀ g : GL (Fin n) K, (∀ e : ↥E0,
      g * SpecialLinearGroup.toGL (e : SpecialLinearGroup (Fin n) K) =
        SpecialLinearGroup.toGL (e : SpecialLinearGroup (Fin n) K) * g) →
      ∀ β ∈ blockImage hx ⟨a, ha⟩, g * β * g⁻¹ ∈ blockImage hx ⟨a, ha⟩ := by
    intro g hg β hβ
    refine conj_mem_blockImage hx ⟨a, ha⟩ ?_ hβ
    rw [range_commutantUnitsToGL_eq_centralizer _ (toLin'_glOfPow _ hxp hp0)]
    refine mem_centralizer_of_commute_toLin' ?_
    rw [toLin'_glOfPow]
    exact commute_auxEnd_of_commute E0 (fun e => commute_toLin'_of_mul_eq (hg e)) c d L
  have hPM : blockImage hx ⟨a, ha⟩ ≤ blockImage hy ⟨b, hb⟩ :=
    blockImage_le_blockImage hx hy (commute_act_auxEnd E0 a' c d L).symm
      (y₀ := SpecialLinearGroup.toGL (a' : SpecialLinearGroup (Fin n) K)) rfl ⟨a, ha⟩ ⟨b, hb⟩
      hab hPq.1 fun β hβ => (hPc a' β hβ).symm
  have hMg := goodBlock_of_le_blockImage hy hPq hPM
  have hMq := isQuasisimple_blockImage_of_good hy ⟨b, hb⟩ hMg
  have hMr := blockImage_le_range_toGL_of_good hy ⟨b, hb⟩ hMg
  have hMc : ∀ β ∈ blockImage hy ⟨b, hb⟩,
      SpecialLinearGroup.toGL (a' : SpecialLinearGroup (Fin n) K) * β =
        β * SpecialLinearGroup.toGL (a' : SpecialLinearGroup (Fin n) K) := fun β hβ =>
    (Subgroup.mem_centralizer_singleton_iff.mp (mem_centralizer_of_commute_toLin'
      (a₀ := SpecialLinearGroup.toGL (a' : SpecialLinearGroup (Fin n) K))
      (commute_toLin'_of_mem_blockImage hy hβ))).symm
  have hMN : ∀ g : GL (Fin n) K,
      g * SpecialLinearGroup.toGL (a' : SpecialLinearGroup (Fin n) K) =
        SpecialLinearGroup.toGL (a' : SpecialLinearGroup (Fin n) K) * g →
      ∀ β ∈ blockImage hy ⟨b, hb⟩, g * β * g⁻¹ ∈ blockImage hy ⟨b, hb⟩ := by
    intro g hg β hβ
    refine conj_mem_blockImage hy ⟨b, hb⟩ ?_ hβ
    rw [range_commutantUnitsToGL_eq_centralizer (x := act ρ₀ a')
      (SpecialLinearGroup.toGL (a' : SpecialLinearGroup (Fin n) K)) rfl]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hg
  obtain ⟨s, hs, hsc⟩ := exists_pow_not_mem_center_of_goodBlock hP.prime hp2 hq1 hq2 hxp hg
  have hPd := dvd_card_center_quot_blockImage hx ⟨a, ha⟩ hP.prime hs hsc
  have hâM : ¬ ∀ β ∈ blockImage hy ⟨b, hb⟩,
      SpecialLinearGroup.toGL (â : SpecialLinearGroup (Fin n) K) * β =
        β * SpecialLinearGroup.toGL (â : SpecialLinearGroup (Fin n) K) := fun hc =>
    hâb (exists_aeval_of_commute_blockImage hy ⟨b, hb⟩
      (a₀ := SpecialLinearGroup.toGL (a' : SpecialLinearGroup (Fin n) K))
      (g := SpecialLinearGroup.toGL (â : SpecialLinearGroup (Fin n) K)) rfl
      (by
        rw [← map_mul, ← map_mul]
        exact congrArg (fun t => SpecialLinearGroup.toGL t)
          (congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥E0)).comm â a'))) hc)
  obtain ⟨hPC, hPN', hPq'⟩ := comap_toGL_of_le (X := (E0 : Set (SpecialLinearGroup (Fin n) K)))
    hPr hPq (fun x hx' β hβ => hPc ⟨x, hx'⟩ β hβ) fun g hg β hβ =>
      hPN g (fun e => hg e e.2) β hβ
  obtain ⟨hMC, hMN', hMq'⟩ := comap_toGL_of_le
    (X := ({(a' : SpecialLinearGroup (Fin n) K)} : Set (SpecialLinearGroup (Fin n) K)))
    hMr hMq (fun x hx' β hβ => by rw [Set.mem_singleton_iff.mp hx']; exact hMc β hβ)
    fun g hg β hβ => hMN g (hg _ (Set.mem_singleton _)) β hβ
  refine ⟨_, _, hPC, hPN', hPq', hMC, hMN', hMq', Subgroup.comap_mono hPM,
    dvd_card_comap_toGL hPr hPq' hPd, fun hcen => hâM fun β hβ => ?_⟩
  obtain ⟨y, rfl⟩ := hMr hβ
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hcen y hβ]

end Plane

section Main

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem slInnerBlockAt [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hq1 : ¬ p ∣ Nat.card K - 1) (hq2 : p ∣ Nat.card K ^ 2 - 1) : SLInnerBlockAt p n K := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  intro E0 hE0 hcard a haE ha1 hns
  haveI := hE0
  letI : Fintype ↥E0 := Fintype.ofFinite _
  have hP : IsPlane p ↥E0 := isPlane E0 hp hcard
  set â : ↥E0 := ⟨a, haE⟩ with hâdef
  have hâ1 : â ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  obtain ⟨D, hDp, hD⟩ := exists_isPerfect_ne_bot hns
  haveI := hDp
  set R : Subgroup (GL (Fin n) K) := D.map (SpecialLinearGroup.toGL.comp
    (Subgroup.centralizer (E0 : Set (SpecialLinearGroup (Fin n) K))).subtype) with hR
  haveI : Group.IsPerfect ↥R := Group.IsPerfect.map _
  have hinj : Function.Injective (SpecialLinearGroup.toGL.comp
      (Subgroup.centralizer (E0 : Set (SpecialLinearGroup (Fin n) K))).subtype) :=
    fun x y h => Subtype.ext (SpecialLinearGroup.toGL_injective h)
  have hR0 : R ≠ ⊥ := fun h => hD ((Subgroup.map_eq_bot_iff_of_injective D hinj).mp h)
  have hRc : ∀ g ∈ R, ∀ e : ↥E0, Commute (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K))
      (act (planeRep E0) e) := by
    rintro _ ⟨d, -, rfl⟩ e
    refine commute_toLin'_of_mul_eq
      (h := SpecialLinearGroup.toGL (e : SpecialLinearGroup (Fin n) K)) ?_
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp d.2 e e.2]
  obtain ⟨M₁, hM₁, hM₁0, hâM₁⟩ := exists_active_not_mem hP hpK hâ1
  obtain ⟨c₁, hc₁M₁, hc₁1⟩ := RankThree.PartOne.KCLinPlane.exists_ne_one_mem E0 hM₁ hP
  have hc₁â : c₁ ∉ Subgroup.zpowers â := not_mem_zpowers_of_mem hP hM₁ hc₁M₁ hc₁1 hâM₁
  have hne : ∀ {L : Subgroup ↥E0}, projLine (planeRep E0) L ≠ 0 →
      ∃ y ∈ LinearMap.range (projLine (planeRep E0) L), y ≠ 0 := by
    intro L hL0
    by_contra hcon
    push Not at hcon
    exact hL0 (LinearMap.ext fun v => hcon _ (LinearMap.mem_range_self _ v))
  obtain ⟨cL, hcL, hcLâ⟩ : ∃ cL : Subgroup ↥E0 → ↥E0, (∀ L ∈ lines p ↥E0, cL L ∉ L) ∧
      cL (Subgroup.zpowers â) = c₁ := by
    refine ⟨fun L => if L = Subgroup.zpowers â then c₁ else
      if h : ∃ c : ↥E0, c ∉ L then h.choose else 1, fun L hL => ?_, if_pos rfl⟩
    dsimp only
    by_cases hLa : L = Subgroup.zpowers â
    · rw [if_pos hLa, hLa]
      exact hc₁â
    · have hex : ∃ c : ↥E0, c ∉ L := by
        obtain ⟨M, hM, hML, c, hcM, hc1⟩ := exists_other_line E0 hP L
        refine ⟨c, fun hcL => hc1 ?_⟩
        have hc : c ∈ L ⊓ M := ⟨hcL, hcM⟩
        rwa [hP.inf_eq_bot (mem_lines.mp hL) (mem_lines.mp hM) (Ne.symm hML),
          Subgroup.mem_bot] at hc
      rw [if_neg hLa, dif_pos hex]
      exact hex.choose_spec
  have hzp : ∀ y : ↥E0, y ∉ Subgroup.zpowers â →
      (y : SpecialLinearGroup (Fin n) K) ∉ Subgroup.zpowers a := by
    intro y hy hya
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hya
    exact hy (Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩)
  rcases exists_goodBlock_of_perfect hP hpK hR0 hRc hM₁ hâM₁ hc₁M₁ hc₁1 cL hcL with
    ⟨hX, hg⟩ | ⟨L, hL, h, hh, hX, hg⟩
  ·
    obtain ⟨y, hy, hy0⟩ := hne hM₁0
    have hyc : y ∈ primaryComponent (act (planeRep E0) c₁) (X - C 1) := by
      rw [mem_primaryComponent]
      simp [fix_range_projLine E0 hc₁M₁ y hy]
    have hb := mem_primaryFactors_of_ne_zero (irreducible_X_sub_C 1) (monic_X_sub_C 1) hy0 hyc
    have hV0 := primaryComponent_auxEnd_X_sub_one hP hpK hM₁ hâM₁ hc₁M₁ hc₁1
    have hEa : ∀ e : ↥E0, ∃ f : K[X], ∀ v ∈ primaryComponent (auxEnd E0 â c₁ M₁) (X - C 1),
        act (planeRep E0) e v = aeval (auxEnd E0 â c₁ M₁) f v := by
      intro e
      refine ⟨1, fun v hv => ?_⟩
      rw [hV0] at hv
      obtain ⟨u, rfl⟩ := hv
      rw [map_one, Module.End.one_apply]
      exact avgOp_apply_mem_fixedSpace (planeRep E0) ⊤ u e (Subgroup.mem_top e)
    have hab : primaryComponent (auxEnd E0 â c₁ M₁) (X - C 1) ≤
        primaryComponent (act (planeRep E0) c₁) (X - C 1) := by
      rw [hV0]
      rintro _ ⟨u, rfl⟩
      rw [mem_primaryComponent]
      simp only [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero]
      exact avgOp_apply_mem_fixedSpace (planeRep E0) ⊤ u c₁ (Subgroup.mem_top c₁)
    exact ⟨c₁, c₁.2, hzp c₁ hc₁â, exists_blocks_of_goodBlock hP hpK hp2 hq1 hq2 hM₁ â c₁ hX hg
      hEa â c₁ hb hab (not_exists_aeval_fixed hP hpK hq1 hM₁ hc₁M₁ hâM₁ hy hy0)⟩
  ·
    have hxL := squarefree_minpoly_auxEnd hP hpK hL (cL L) 1
    obtain ⟨u, hu, hu0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hxL hh)
    have hVL : ∀ v ∈ primaryComponent (auxEnd E0 (cL L) 1 L) h,
        v ∈ LinearMap.range (projLine (planeRep E0) L) := fun v hv =>
      mem_range_projLine_of_mem_primaryComponent hP hpK hL (hcL L hL) hh hX hv
    have hEa : ∀ e : ↥E0, ∃ f : K[X], ∀ v ∈ primaryComponent (auxEnd E0 (cL L) 1 L) h,
        act (planeRep E0) e v = aeval (auxEnd E0 (cL L) 1 L) f v := by
      intro e
      obtain ⟨j, hj⟩ := exists_act_eq_auxEnd_pow hP hpK hL (hcL L hL) 1 e
      exact ⟨X ^ j, fun v hv => by rw [hj v (hVL v hv), aeval_X_pow]⟩
    by_cases hâL : â ∈ L
    ·
      have hcL₁ : cL L = c₁ := by
        rw [eq_zpowers_of_mem hP hL hâL hâ1]
        exact hcLâ
      have hcM : cL L ∈ M₁ := hcL₁ ▸ hc₁M₁
      have hM₁L : M₁ ≠ L := fun h => hâM₁ (h ▸ hâL)
      obtain ⟨h₂, hh₂, hX₂, hne₂⟩ := exists_factor E0 hP hpK hM₁ hL hM₁L hM₁0 hâL hâ1
      obtain ⟨v₂, hv₂⟩ : ∃ v, (projLine (planeRep E0) M₁ *
          primaryProjection (act (planeRep E0) â) h₂) v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne₂ (LinearMap.ext hcon)
      have hâp : act (planeRep E0) â ^ p = 1 := by rw [← act_pow, hP.pow â, act_one]
      have hsqâ := squarefree_minpoly_of_pow_eq_one hpK hâp
      set y₂ := projLine (planeRep E0) M₁ (primaryProjection (act (planeRep E0) â) h₂ v₂)
        with hy₂
      have hy₂0 : y₂ ≠ 0 := hv₂
      have hy₂M : y₂ ∈ LinearMap.range (projLine (planeRep E0) M₁) :=
        LinearMap.mem_range_self _ _
      have hy₂h : y₂ ∈ primaryComponent (act (planeRep E0) â) h₂ :=
        apply_mem_primaryComponent (commute_act_projLine E0 â M₁).symm
          (primaryProjection_mem hsqâ hh₂ v₂)
      have hxp := auxEnd_pow_eq_one hP hpK hL (cL L) 1
      have hd₁ : h ∣ X ^ p - 1 :=
        (mem_primaryFactors.mp hh).2.2.trans (minpoly.dvd K _ (by simp [hxp]))
      have hd₂ : h₂ ∣ X ^ p - 1 :=
        (mem_primaryFactors.mp hh₂).2.2.trans (minpoly.dvd K _ (by simp [hâp]))
      obtain ⟨j, hj⟩ := exists_dvd_comp_pow hp (irreducible_of_mem_primaryFactors hh₂)
        (monic_of_mem_primaryFactors hh₂) hd₁ hd₂ hX₂
        (irreducible_of_mem_primaryFactors hh).natDegree_pos
      have hab := primaryComponent_auxEnd_le hP hpK hL hâL (hcL L hL) j hh hX
      have hb := mem_primaryFactors_of_ne_zero (irreducible_of_mem_primaryFactors hh)
        (monic_of_mem_primaryFactors hh) hu0 (hab hu)
      have hy₂' := mem_primaryComponent_mul_pow hcM hj hy₂M hy₂h
      have hzâ : â ^ j * cL L ∉ Subgroup.zpowers â := by
        intro hz
        apply hc₁â
        rw [← hcL₁]
        have := (Subgroup.zpowers â).mul_mem ((Subgroup.zpowers â).inv_mem
          ((Subgroup.zpowers â).pow_mem (Subgroup.mem_zpowers â) j)) hz
        rwa [inv_mul_cancel_left] at this
      exact ⟨_, (â ^ j * cL L).2, hzp _ hzâ, exists_blocks_of_goodBlock hP hpK hp2 hq1 hq2 hL
        (cL L) 1 hh hg hEa â (â ^ j * cL L) hb hab (not_exists_aeval_mixed hP hpK hM₁ hâL hâM₁
          hb (hab hu) (hVL u hu) hu0 hy₂' hy₂M hy₂0)⟩
    ·
      obtain ⟨a', ha'L, ha'1⟩ := RankThree.PartOne.KCLinPlane.exists_ne_one_mem E0 hL hP
      have hab : primaryComponent (auxEnd E0 (cL L) 1 L) h ≤
          primaryComponent (act (planeRep E0) a') (X - C 1) := by
        intro v hv
        rw [mem_primaryComponent]
        simp [fix_range_projLine E0 ha'L v (hVL v hv)]
      have hb :=
        mem_primaryFactors_of_ne_zero (irreducible_X_sub_C 1) (monic_X_sub_C 1) hu0 (hab hu)
      exact ⟨a', a'.2, hzp a' (not_mem_zpowers_of_mem hP hL ha'L ha'1 hâL),
        exists_blocks_of_goodBlock hP hpK hp2 hq1 hq2 hL (cL L) 1 hh hg hEa â a' hb hab
          (not_exists_aeval_fixed hP hpK hq1 hL ha'L hâL (hVL u hu) hu0)⟩

theorem innerBlockAt_projectiveSL_of_dvd_succ [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 1 ≤ n) (hdvd : p ∣ Nat.card K + 1) : InnerBlockAt p (projectiveSL n K) := by
  letI : Fintype K := Fintype.ofFinite K
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq1 : ¬ p ∣ Nat.card K - 1 := by
    intro h
    have h2 : p ∣ Nat.card K + 1 - (Nat.card K - 1) := Nat.dvd_sub hdvd h
    rw [show Nat.card K + 1 - (Nat.card K - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hq2 : p ∣ Nat.card K ^ 2 - 1 := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 := ⟨Nat.card K - 1, by omega⟩
    have h1 : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
    rw [hr, h1, Nat.add_sub_cancel]
    rw [hr] at hdvd
    exact Dvd.dvd.mul_right hdvd r
  have hpK : (p : K) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := hdvd
    have h1 : ((Nat.card K + 1 : ℕ) : K) = 0 := by rw [hm, Nat.cast_mul, h0, zero_mul]
    rw [Nat.cast_add, Nat.cast_one, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero,
      zero_add] at h1
    exact one_ne_zero h1
  refine innerBlockAt_projectiveSL_of_sl hp hn (fun c hc _ => ?_)
    (slInnerBlockAt hp hp2 hpK hq1 hq2)
  refine Units.ext (eq_one_of_pow_eq_one_of_not_dvd hp (by rwa [← Nat.card_eq_fintype_card]) ?_)
  rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]

end Main

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
