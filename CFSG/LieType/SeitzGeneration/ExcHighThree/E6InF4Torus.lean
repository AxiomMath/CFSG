module

public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2Fixed
public import CFSG.HardMathSupport.Lang.AnisoE6.F4GraphFixed
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem rootChar_single_apply {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (i : Fin τ.rank) : rootChar a (Pi.single i 1) = a i := by
  simp [rootChar, Pi.single_apply]

theorem rootChar_neg_single_apply {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (i : Fin τ.rank) : rootChar a (-Pi.single i 1) = (a i)⁻¹ := by
  simp [rootChar, Pi.single_apply]

theorem rootDiagUnit_conj_xUnit {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (i : Fin τ.rank) (c : K) :
    rootDiagUnit τ a * xUnit τ K i c * (rootDiagUnit τ a)⁻¹ = xUnit τ K i ((a i : K) * c) := by
  have hα : IsRoot τ (Pi.single i 1) := isRoot_single τ i
  rw [← pinnedX_single τ K i c, ← pinnedX_single τ K i ((a i : K) * c)]
  rw [rootDiagUnit_conj_pinnedX a hα c, rootChar_single_apply]

theorem rootDiagUnit_conj_yUnit {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (i : Fin τ.rank) (c : K) :
    rootDiagUnit τ a * yUnit τ K i c * (rootDiagUnit τ a)⁻¹ =
      yUnit τ K i (((a i)⁻¹ : Kˣ) * c) := by
  have hα : IsRoot τ (-Pi.single i 1) := isRoot_neg_single τ i
  rw [← pinnedX_neg_single τ K i c, ← pinnedX_neg_single τ K i (((a i)⁻¹ : Kˣ) * c)]
  rw [rootDiagUnit_conj_pinnedX a hα c, rootChar_neg_single_apply]

@[expose] def fixE6 (K : Type) [Field K] : Subgroup (adjointGroup .E6 K) :=
  (twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subgroupOf _

@[expose] noncomputable def isoE6F4 (K : Type) [Field K] : adjointGroup .F4 K ≃* fixE6 K :=
  (e6FixedF4EquivAll K).symm.trans
    (Subgroup.subgroupOfEquivOfLe (twistedFixedGroup_le_adjointGroup TwistTag.E6 K (RingHom.id K))).symm

@[expose] noncomputable def embE6F4 (K : Type) [Field K] :
    adjointGroup .F4 K →* adjointGroup .E6 K :=
  (fixE6 K).subtype.comp (isoE6F4 K).toMonoidHom

abbrev node4 : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩

def dOmega {K : Type} [Field K] (ω : Kˣ) : Fin TwistTag.E6.tag.rank → Kˣ := Pi.mulSingle node4 ω

theorem perm_node4_fixed : TwistTag.E6.perm node4 = node4 := by
  rfl

theorem perm_node4_iff (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm i = node4 ↔ i = node4 := by
  constructor
  · intro h
    exact (TwistTag.E6.perm).injective (h.trans perm_node4_fixed.symm)
  · intro h
    subst h
    exact perm_node4_fixed

theorem dOmega_compat (K : Type) [Field K] (ω : Kˣ) :
    ∀ i : Fin TwistTag.E6.tag.rank,
      dOmega ω (TwistTag.E6.perm i) = Units.map (RingHom.id K).toMonoidHom (dOmega ω i) := by
  intro i
  by_cases hi : i = node4
  · have hp : TwistTag.E6.perm i = node4 := (perm_node4_iff i).mpr hi
    rw [hp]
    simp [dOmega, hi]
  · have hp : TwistTag.E6.perm i ≠ node4 := fun h => hi ((perm_node4_iff i).mp h)
    simp only [dOmega]
    rw [Pi.mulSingle_eq_of_ne hp, Pi.mulSingle_eq_of_ne hi]
    simp

theorem zpow_eq_of_emod_three {K : Type} [Field K] (ω : Kˣ) (hω : orderOf ω = 3) (m n : ℤ)
    (h : m % 3 = n % 3) : ω ^ m = ω ^ n := by
  have h3 : ω ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hω, pow_orderOf_eq_one]
  have hmn : m = n + 3 * ((m - n) / 3) := by omega
  rw [hmn, zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem dOmega_eq_torus (K : Type) [Field K] (ω : Kˣ) (hω : orderOf ω = 3) :
    rootDiagUnit TwistTag.E6.tag (dOmega ω) =
      torusElt TwistTag.E6.tag K ⟨4, by decide⟩ (ω ^ 2) *
        torusElt TwistTag.E6.tag K ⟨5, by decide⟩ ω := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  have hcart : ∀ j : Fin TwistTag.E6.tag.rank,
      (2 * TwistTag.E6.tag.cartan ⟨4, by decide⟩ j + TwistTag.E6.tag.cartan ⟨5, by decide⟩ j) % 3 =
        (if j = node4 then 1 else 0) % 3 := by
    decide +kernel
  have hd : dOmega ω j = ω ^ (if j = node4 then (1 : ℤ) else 0) := by
    by_cases hj : j = node4
    · simp [dOmega, hj]
    · simp [dOmega, hj, Pi.mulSingle_eq_of_ne hj]
  have h1 : ∀ c : ℤ, (ω ^ 2) ^ c = ω ^ (2 * c) := by
    intro c
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  simp only [Pi.mul_apply]
  rw [h1, ← zpow_add, hd]
  exact zpow_eq_of_emod_three ω hω _ _ (hcart j).symm

theorem dOmega_mem_adjointGroup (K : Type) [Field K] (ω : Kˣ) (hω : orderOf ω = 3) :
    rootDiagUnit TwistTag.E6.tag (dOmega ω) ∈ adjointGroup TwistTag.E6.tag K := by
  rw [dOmega_eq_torus K ω hω]
  exact mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _)

theorem dOmega_mem_fixed (K : Type) [Field K] (ω : Kˣ) (hω : orderOf ω = 3) :
    rootDiagUnit TwistTag.E6.tag (dOmega ω) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  rw [mem_twistedFixedGroup_iff_twistHom]
  exact ⟨dOmega_mem_adjointGroup K ω hω, twistHom_rootDiagUnit (dOmega_compat K ω)⟩

def Tω (K : Type) [Field K] (ω : Kˣ) (hω : orderOf ω = 3) :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
  ⟨_, dOmega_mem_fixed K ω hω⟩

@[expose] def OX {K : Type} [Field K] (j : Fin Tag.F4.rank) (c : K) :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
  ⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩

@[expose] def OY {K : Type} [Field K] (j : Fin Tag.F4.rank) (c : K) :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
  ⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩

@[expose] def xE (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨xUnit τ K i c, xUnit_mem_adjointGroup i c⟩

@[expose] def yE (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩

theorem conj_orbitX (K : Type) [Field K] (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (j : Fin Tag.F4.rank) (c : K) :
    rootDiagUnit TwistTag.E6.tag a * f4OrbitXUnit K j c * (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
      ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun i =>
        xUnit TwistTag.E6.tag K i ((a i : K) * c)).prod := by
  unfold f4OrbitXUnit
  set d := rootDiagUnit TwistTag.E6.tag a with hd
  have key : ∀ L : List (Fin TwistTag.E6.tag.rank),
      d * (L.map fun i => xUnit TwistTag.E6.tag K i c).prod * d⁻¹ =
        (L.map fun i => d * xUnit TwistTag.E6.tag K i c * d⁻¹).prod := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← ih]
      group
  rw [key]
  congr 1
  apply List.map_congr_left
  intro i _
  exact rootDiagUnit_conj_xUnit a i c

theorem conj_orbitY (K : Type) [Field K] (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (j : Fin Tag.F4.rank) (c : K) :
    rootDiagUnit TwistTag.E6.tag a * f4OrbitYUnit K j c * (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
      ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun i =>
        yUnit TwistTag.E6.tag K i (((a i)⁻¹ : Kˣ) * c)).prod := by
  unfold f4OrbitYUnit
  set d := rootDiagUnit TwistTag.E6.tag a with hd
  have key : ∀ L : List (Fin TwistTag.E6.tag.rank),
      d * (L.map fun i => yUnit TwistTag.E6.tag K i c).prod * d⁻¹ =
        (L.map fun i => d * yUnit TwistTag.E6.tag K i c * d⁻¹).prod := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← ih]
      group
  rw [key]
  congr 1
  apply List.map_congr_left
  intro i _
  exact rootDiagUnit_conj_yUnit a i c

theorem orbitWord_ne_node4 : ∀ j : Fin Tag.F4.rank, j ≠ (⟨1, by decide⟩ : Fin Tag.F4.rank) →
    ∀ i ∈ TwistTag.E6.orbitWord (f4FoldedIndex j), i ≠ node4 := by
  decide +kernel

def uF4 (K : Type) [Field K] (ω : Kˣ) : Fin Tag.F4.rank → Kˣ := Pi.mulSingle (1 : Fin Tag.F4.rank) ω

theorem orbitWord_f4_one' :
    TwistTag.E6.orbitWord (f4FoldedIndex (1 : Fin Tag.F4.rank)) = [node4] :=
  orbitWord_f4_one

theorem dOmega_node4 {K : Type} [Field K] (ω : Kˣ) : dOmega ω node4 = ω := by
  unfold dOmega
  rw [Pi.mulSingle_apply, if_pos rfl]

theorem dOmega_node4_val {K : Type} [Field K] (ω : Kˣ) :
    ((dOmega ω node4 : Kˣ) : K) = (ω : K) := by
  rw [dOmega_node4]

theorem conj_Tω_OX (K : Type) [Field K] (ω : Kˣ) (hω : orderOf ω = 3) (j : Fin Tag.F4.rank) (c : K) :
    Tω K ω hω * OX j c * (Tω K ω hω)⁻¹ = OX j (((uF4 K ω j : Kˣ) : K) * c) := by
  apply Subtype.ext
  show rootDiagUnit TwistTag.E6.tag (dOmega ω) * f4OrbitXUnit K j c *
      (rootDiagUnit TwistTag.E6.tag (dOmega ω))⁻¹ = f4OrbitXUnit K j (((uF4 K ω j : Kˣ) : K) * c)
  rw [conj_orbitX]
  by_cases hj : j = (1 : Fin Tag.F4.rank)
  · subst hj
    unfold f4OrbitXUnit uF4
    rw [orbitWord_f4_one']
    simp [dOmega_node4_val]
  · have hu : uF4 K ω j = 1 := by
      unfold uF4
      exact Pi.mulSingle_eq_of_ne hj _
    rw [hu, Units.val_one, one_mul]
    unfold f4OrbitXUnit
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne := orbitWord_ne_node4 j hj i hi
    have hdi : dOmega ω i = 1 := by
      unfold dOmega
      exact Pi.mulSingle_eq_of_ne hne _
    rw [hdi, Units.val_one, one_mul]

theorem conj_Tω_OY (K : Type) [Field K] (ω : Kˣ) (hω : orderOf ω = 3) (j : Fin Tag.F4.rank) (c : K) :
    Tω K ω hω * OY j c * (Tω K ω hω)⁻¹ = OY j ((((uF4 K ω j)⁻¹ : Kˣ) : K) * c) := by
  apply Subtype.ext
  show rootDiagUnit TwistTag.E6.tag (dOmega ω) * f4OrbitYUnit K j c *
      (rootDiagUnit TwistTag.E6.tag (dOmega ω))⁻¹ = f4OrbitYUnit K j ((((uF4 K ω j)⁻¹ : Kˣ) : K) * c)
  rw [conj_orbitY]
  by_cases hj : j = (1 : Fin Tag.F4.rank)
  · subst hj
    unfold f4OrbitYUnit uF4
    rw [orbitWord_f4_one']
    simp [dOmega_node4]
  · have hu : uF4 K ω j = 1 := by
      unfold uF4
      exact Pi.mulSingle_eq_of_ne hj _
    rw [hu, inv_one, Units.val_one, one_mul]
    unfold f4OrbitYUnit
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne := orbitWord_ne_node4 j hj i hi
    have hdi : dOmega ω i = 1 := by
      unfold dOmega
      exact Pi.mulSingle_eq_of_ne hne _
    rw [hdi, inv_one, Units.val_one, one_mul]

theorem psi_OX (K : Type) [Field K] (j : Fin Tag.F4.rank) (c : K) :
    e6FixedF4EquivAll K (OX j c) = xE Tag.F4 K j c := by
  apply Subtype.ext
  rw [coe_e6FixedF4EquivAll]
  exact e6FixedToF4_f4OrbitXUnit_all j c

theorem psi_OY (K : Type) [Field K] (j : Fin Tag.F4.rank) (c : K) :
    e6FixedF4EquivAll K (OY j c) = yE Tag.F4 K j c := by
  apply Subtype.ext
  rw [coe_e6FixedF4EquivAll]
  exact e6FixedToF4_f4OrbitYUnit_all j c

theorem psi_conj_xE (K : Type) [Field K] [Finite K] (ω : Kˣ) (hω : orderOf ω = 3)
    (i : Fin Tag.F4.rank) (c : K) :
    e6FixedF4EquivAll K (Tω K ω hω) * xE Tag.F4 K i c * (e6FixedF4EquivAll K (Tω K ω hω))⁻¹ =
      xE Tag.F4 K i (((uF4 K ω i : Kˣ) : K) * c) := by
  calc e6FixedF4EquivAll K (Tω K ω hω) * xE Tag.F4 K i c *
        (e6FixedF4EquivAll K (Tω K ω hω))⁻¹
      = e6FixedF4EquivAll K (Tω K ω hω) * e6FixedF4EquivAll K (OX i c) *
          (e6FixedF4EquivAll K (Tω K ω hω))⁻¹ := by rw [psi_OX]
    _ = e6FixedF4EquivAll K (Tω K ω hω * OX i c * (Tω K ω hω)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
    _ = e6FixedF4EquivAll K (OX i (((uF4 K ω i : Kˣ) : K) * c)) := by rw [conj_Tω_OX]
    _ = xE Tag.F4 K i (((uF4 K ω i : Kˣ) : K) * c) := psi_OX K i _

theorem psi_conj_yE (K : Type) [Field K] [Finite K] (ω : Kˣ) (hω : orderOf ω = 3)
    (i : Fin Tag.F4.rank) (c : K) :
    e6FixedF4EquivAll K (Tω K ω hω) * yE Tag.F4 K i c * (e6FixedF4EquivAll K (Tω K ω hω))⁻¹ =
      yE Tag.F4 K i ((((uF4 K ω i)⁻¹ : Kˣ) : K) * c) := by
  calc e6FixedF4EquivAll K (Tω K ω hω) * yE Tag.F4 K i c *
        (e6FixedF4EquivAll K (Tω K ω hω))⁻¹
      = e6FixedF4EquivAll K (Tω K ω hω) * e6FixedF4EquivAll K (OY i c) *
          (e6FixedF4EquivAll K (Tω K ω hω))⁻¹ := by rw [psi_OY]
    _ = e6FixedF4EquivAll K (Tω K ω hω * OY i c * (Tω K ω hω)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
    _ = e6FixedF4EquivAll K (OY i ((((uF4 K ω i)⁻¹ : Kˣ) : K) * c)) := by rw [conj_Tω_OY]
    _ = yE Tag.F4 K i ((((uF4 K ω i)⁻¹ : Kˣ) : K) * c) := psi_OY K i _

theorem zSplit_conj_xE (K : Type) [Field K] (ω : Kˣ) (i : Fin Tag.F4.rank) (c : K) :
    zSplit K ω * xE Tag.F4 K i c * (zSplit K ω)⁻¹ = xE Tag.F4 K i (((uF4 K ω i : Kˣ) : K) * c) := by
  apply Subtype.ext
  show rootDiagUnit Tag.F4 (uF4 K ω) * xUnit Tag.F4 K i c * (rootDiagUnit Tag.F4 (uF4 K ω))⁻¹ =
    xUnit Tag.F4 K i (((uF4 K ω i : Kˣ) : K) * c)
  exact rootDiagUnit_conj_xUnit (uF4 K ω) i c

theorem zSplit_conj_yE (K : Type) [Field K] (ω : Kˣ) (i : Fin Tag.F4.rank) (c : K) :
    zSplit K ω * yE Tag.F4 K i c * (zSplit K ω)⁻¹ = yE Tag.F4 K i ((((uF4 K ω i)⁻¹ : Kˣ) : K) * c) := by
  apply Subtype.ext
  show rootDiagUnit Tag.F4 (uF4 K ω) * yUnit Tag.F4 K i c * (rootDiagUnit Tag.F4 (uF4 K ω))⁻¹ =
    yUnit Tag.F4 K i ((((uF4 K ω i)⁻¹ : Kˣ) : K) * c)
  exact rootDiagUnit_conj_yUnit (uF4 K ω) i c

theorem eq_top_of_simpleRootOps_gen {τ : Tag} {K : Type} [Field K] (M : Subgroup (adjointGroup τ K))
    (h : ∀ (i : Fin τ.rank) (c : K), xE τ K i c ∈ M ∧ yE τ K i c ∈ M) : M = ⊤ := by
  rw [eq_top_iff]
  set N : Subgroup (ModGL τ K) := M.map (adjointGroup τ K).subtype with hN
  have hgen : adjointGroup τ K ≤ N := by
    unfold adjointGroup
    rw [Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit τ K i c := Units.ext hg
      refine ⟨xE τ K i c, (h i c).1, ?_⟩
      simp only [Subgroup.coe_subtype, xE]
      exact hg'.symm
    · have hg' : g = yUnit τ K i c := Units.ext hg
      refine ⟨yE τ K i c, (h i c).2, ?_⟩
      simp only [Subgroup.coe_subtype, yE]
      exact hg'.symm
  intro x _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hgen x.2)
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem mem_center_of_simpleRootOps {τ : Tag} {K : Type} [Field K] (w : adjointGroup τ K)
    (h : ∀ (i : Fin τ.rank) (c : K), Commute w (xE τ K i c) ∧ Commute w (yE τ K i c)) :
    w ∈ Subgroup.center (adjointGroup τ K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hM : Subgroup.centralizer ({w} : Set (adjointGroup τ K)) = ⊤ := by
    apply eq_top_of_simpleRootOps_gen
    intro i c
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (h i c).1.symm,
      Subgroup.mem_centralizer_singleton_iff.mpr (h i c).2.symm⟩
  have hg : g ∈ Subgroup.centralizer ({w} : Set (adjointGroup τ K)) := by
    rw [hM]
    exact Subgroup.mem_top g
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

theorem psi_Tω_eq_zSplit (K : Type) [Field K] [Finite K] (ω : Kˣ) (hω : orderOf ω = 3) :
    e6FixedF4EquivAll K (Tω K ω hω) = zSplit K ω := by
  set ψ := e6FixedF4EquivAll K (Tω K ω hω) with hψ
  set z := zSplit K ω with hz
  have hcomm : ∀ (i : Fin Tag.F4.rank) (c : K),
      Commute (z⁻¹ * ψ) (xE Tag.F4 K i c) ∧ Commute (z⁻¹ * ψ) (yE Tag.F4 K i c) := by
    intro i c
    have hx : ψ * xE Tag.F4 K i c * ψ⁻¹ = z * xE Tag.F4 K i c * z⁻¹ := by
      rw [hψ, hz, psi_conj_xE, zSplit_conj_xE]
    have hy : ψ * yE Tag.F4 K i c * ψ⁻¹ = z * yE Tag.F4 K i c * z⁻¹ := by
      rw [hψ, hz, psi_conj_yE, zSplit_conj_yE]
    constructor
    · show (z⁻¹ * ψ) * xE Tag.F4 K i c = xE Tag.F4 K i c * (z⁻¹ * ψ)
      calc (z⁻¹ * ψ) * xE Tag.F4 K i c = z⁻¹ * (ψ * xE Tag.F4 K i c * ψ⁻¹) * ψ := by group
        _ = z⁻¹ * (z * xE Tag.F4 K i c * z⁻¹) * ψ := by rw [hx]
        _ = xE Tag.F4 K i c * (z⁻¹ * ψ) := by group
    · show (z⁻¹ * ψ) * yE Tag.F4 K i c = yE Tag.F4 K i c * (z⁻¹ * ψ)
      calc (z⁻¹ * ψ) * yE Tag.F4 K i c = z⁻¹ * (ψ * yE Tag.F4 K i c * ψ⁻¹) * ψ := by group
        _ = z⁻¹ * (z * yE Tag.F4 K i c * z⁻¹) * ψ := by rw [hy]
        _ = yE Tag.F4 K i c * (z⁻¹ * ψ) := by group
  have hw := mem_center_of_simpleRootOps (z⁻¹ * ψ) hcomm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hw
  exact hw.symm

theorem embE6F4_zSplit (K : Type) [Field K] [Finite K] (ω : Kˣ) (hω : orderOf ω = 3) :
    ((embE6F4 K (zSplit K ω) : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      rootDiagUnit TwistTag.E6.tag (dOmega ω) := by
  have hT : (e6FixedF4EquivAll K).symm (zSplit K ω) = Tω K ω hω := by
    rw [MulEquiv.symm_apply_eq, psi_Tω_eq_zSplit]
  have h1 : ((embE6F4 K (zSplit K ω) : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      ((((e6FixedF4EquivAll K).symm (zSplit K ω)) : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
        ModGL TwistTag.E6.tag K) := by
    unfold embE6F4 isoE6F4
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      Subgroup.coe_subtype]
    rfl
  rw [h1, hT]
  rfl

theorem hCent_proved : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
    ∀ ω : Kˣ, orderOf ω = 3 → ∀ (i : Fin Tag.E6.rank), i ≠ e6Index 3 → ∀ c : K,
      Commute (embE6F4 K (zSplit K ω)) (xE Tag.E6 K i c) ∧
        Commute (embE6F4 K (zSplit K ω)) (yE Tag.E6 K i c) := by
  intro K _ _ _ ω hω i hi c
  have hd := embE6F4_zSplit K ω hω
  have hni : (i : Fin TwistTag.E6.tag.rank) ≠ node4 := hi
  have hu : dOmega ω i = 1 := by
    unfold dOmega
    exact Pi.mulSingle_eq_of_ne hni _
  have hxc : ((xE Tag.E6 K i c : adjointGroup .E6 K) : ModGL Tag.E6 K) = xUnit TwistTag.E6.tag K i c := by
    rfl
  have hyc : ((yE Tag.E6 K i c : adjointGroup .E6 K) : ModGL Tag.E6 K) = yUnit TwistTag.E6.tag K i c := by
    rfl
  constructor
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hd, hxc]
    have key := rootDiagUnit_conj_xUnit (τ := TwistTag.E6.tag) (dOmega ω) i c
    rw [hu, Units.val_one, one_mul] at key
    calc rootDiagUnit TwistTag.E6.tag (dOmega ω) * xUnit TwistTag.E6.tag K i c
        = (rootDiagUnit TwistTag.E6.tag (dOmega ω) * xUnit TwistTag.E6.tag K i c *
            (rootDiagUnit TwistTag.E6.tag (dOmega ω))⁻¹) * rootDiagUnit TwistTag.E6.tag (dOmega ω) := by
          group
      _ = xUnit TwistTag.E6.tag K i c * rootDiagUnit TwistTag.E6.tag (dOmega ω) := by rw [key]
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hd, hyc]
    have key := rootDiagUnit_conj_yUnit (τ := TwistTag.E6.tag) (dOmega ω) i c
    rw [hu, inv_one, Units.val_one, one_mul] at key
    calc rootDiagUnit TwistTag.E6.tag (dOmega ω) * yUnit TwistTag.E6.tag K i c
        = (rootDiagUnit TwistTag.E6.tag (dOmega ω) * yUnit TwistTag.E6.tag K i c *
            (rootDiagUnit TwistTag.E6.tag (dOmega ω))⁻¹) * rootDiagUnit TwistTag.E6.tag (dOmega ω) := by
          group
      _ = yUnit TwistTag.E6.tag K i c * rootDiagUnit TwistTag.E6.tag (dOmega ω) := by rw [key]

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
