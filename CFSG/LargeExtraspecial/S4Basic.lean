module

public import CFSG.LargeExtraspecial.S4Defs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LargeExtraspecial.S3Fusion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

theorem exists_fixed_ne_zero {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (hH : IsPGroup 2 H) (φ : H →* (V ≃ₗ[ZMod 2] V)) {U : Submodule (ZMod 2) V}
    (hU : ∀ x u, u ∈ U → φ x u ∈ U) (hne : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ x, φ x u = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction H U :=
    { smul := fun x u => ⟨φ x u, hU x u u.2⟩
      one_smul := fun u => Subtype.ext (by show φ 1 u = u; simp)
      mul_smul := fun x y u => Subtype.ext (by show φ (x * y) u = φ x (φ y u); rw [map_mul]; rfl) }
  have hsmul : ∀ (x : H) (u : U), ((x • u : U) : V) = φ x u := fun _ _ => rfl
  have h0 : (0 : U) ∈ MulAction.fixedPoints H U := fun x =>
    Subtype.ext (by rw [hsmul]; simp)
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hdvd : 2 ∣ Nat.card U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have : finrank (ZMod 2) U ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.mp h)
    exact dvd_pow_self 2 this
  obtain ⟨b, hb, hb0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdvd h0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun x => ?_⟩
  have := congrArg Subtype.val (hb x)
  rwa [hsmul] at this

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem Lbar_comm {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {x y : S.O} (hx : x ∈ S.Lbar g)
    (hy : y ∈ S.Lbar g) : x * y = y * x := by
  have := S.isElementaryAbelian_Lbar haQ
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := S.Lbar g)).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isPGroup_Lbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) : IsPGroup 2 (S.Lbar g) := by
  have := S.isElementaryAbelian_Lbar haQ
  exact CFSG.IsElementaryAbelian.isPGroup 2 _

theorem mul_self_of_mem_Lbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {x : S.O}
    (hx : x ∈ S.Lbar g) : x * x = 1 := by
  have := S.isElementaryAbelian_Lbar haQ
  rw [← pow_two]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx

theorem exists_fixed_of_isPGroup {X : Subgroup S.O} (hX : IsPGroup 2 X)
    {U : Submodule (ZMod 2) S.Qt} (hU : ∀ x ∈ X, ∀ u ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U)
    (hne : U ≠ ⊥) : ∃ u ∈ U, u ≠ 0 ∧ ∀ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
  obtain ⟨u, huU, hu0, hfix⟩ := exists_fixed_ne_zero hX (S.O.subtype.comp X.subtype)
    (fun x u hu => hU x x.2 u hu) hne
  exact ⟨u, huU, hu0, fun x hx => hfix ⟨x, hx⟩⟩

variable {S}

theorem mem_Dset {g : G} {t : S.O} {X : Subgroup S.O} :
    X ∈ Dset S g t ↔ ∃ h : S.M, X = S.Lbar ((h : G) * g) ∧ t ∈ X :=
  Iff.rfl

theorem Lbar_mul_mem_Dset {g : G} {t : S.O} {h : S.M} (ht : t ∈ S.Lbar ((h : G) * g)) :
    S.Lbar ((h : G) * g) ∈ Dset S g t :=
  ⟨h, rfl, ht⟩

theorem Lbar_mem_Dset {g : G} {t : S.O} (ht : t ∈ S.Lbar g) : S.Lbar g ∈ Dset S g t :=
  ⟨1, by simp, ht⟩

theorem le_Rbar {g : G} {t : S.O} {X : Subgroup S.O} (hX : X ∈ Dset S g t) :
    X ≤ Rbar S g t :=
  le_sSup hX

theorem Lbar_mul_le_Rbar {g : G} {t : S.O} {h : S.M} (ht : t ∈ S.Lbar ((h : G) * g)) :
    S.Lbar ((h : G) * g) ≤ Rbar S g t :=
  le_Rbar (Lbar_mul_mem_Dset ht)

theorem Lbar_le_Rbar {g : G} {t : S.O} (ht : t ∈ S.Lbar g) : S.Lbar g ≤ Rbar S g t :=
  le_Rbar (Lbar_mem_Dset ht)

theorem Rbar_le_Mbar {g : G} {t : S.O} : Rbar S g t ≤ S.Mbar :=
  sSup_le fun _ ⟨_, hX, _⟩ => hX ▸ S.Lbar_le_Mbar _

theorem Rbar_le_centralizer {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} :
    Rbar S g t ≤ centralizer ({t} : Set S.O) := by
  refine sSup_le fun X ⟨h, hX, ht⟩ => ?_
  subst hX
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact Lbar_comm S (conj_mem_QG' S h.2 haQ) hx ht

theorem commute_of_mem_Rbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t x : S.O}
    (hx : x ∈ Rbar S g t) : x * t = t * x :=
  mem_centralizer_singleton_iff.mp (Rbar_le_centralizer haQ hx)

theorem conj_mem_Dset {g : G} {t : S.O} {k : S.M} (hk : S.ρ k * t = t * S.ρ k)
    {X : Subgroup S.O} (hX : X ∈ Dset S g t) :
    X.map (MulAut.conj (S.ρ k)).toMonoidHom ∈ Dset S g t := by
  obtain ⟨h, rfl, ht⟩ := hX
  refine ⟨k * h, ?_, ?_⟩
  · rw [show (((k * h : S.M) : G) * g) = (k : G) * ((h : G) * g) by simp [mul_assoc],
      Lbar_mul S k]
  · refine ⟨t, ht, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hk, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_mem_Rbar {g : G} {t : S.O} {k : S.M} (hk : S.ρ k * t = t * S.ρ k) {x : S.O}
    (hx : x ∈ Rbar S g t) : S.ρ k * x * (S.ρ k)⁻¹ ∈ Rbar S g t := by
  have hle : (Rbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom ≤ Rbar S g t := by
    rw [map_le_iff_le_comap]
    refine sSup_le fun X hX => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup (conj_mem_Dset hk hX)
  exact hle ⟨x, hx, rfl⟩

theorem La_mul_le_R {g : G} {t : S.O} {h : S.M} (ht : t ∈ S.Lbar ((h : G) * g)) :
    S.La ((h : G) * g) ≤ R S g t :=
  le_iSup₂_of_le (f := fun (h : S.M) (_ : t ∈ S.Lbar ((h : G) * g)) => S.La ((h : G) * g)) h ht
    le_rfl

theorem La_le_R {g : G} {t : S.O} (ht : t ∈ S.Lbar g) : S.La g ≤ R S g t := by
  have := La_mul_le_R (S := S) (g := g) (h := 1) (by simpa using ht)
  simpa using this

theorem R_le_M {g : G} {t : S.O} : R S g t ≤ S.M :=
  iSup₂_le fun _ _ => La_le_M S _

theorem QG_le_R {g : G} {t : S.O} (ht : t ∈ S.Lbar g) : S.QG ≤ R S g t :=
  (QG_le_La S g).trans (La_le_R ht)

theorem map_R_eq_Rbar {g : G} {t : S.O} :
    ((R S g t).subgroupOf S.M).map S.ρ = Rbar S g t := by
  refine le_antisymm ?_ (sSup_le fun X ⟨h, hX, ht⟩ => ?_)
  · rw [map_le_iff_le_comap]
    intro x hx
    have hx' : (x : G) ∈ R S g t := mem_subgroupOf.mp hx
    have key : R S g t ≤ ((Rbar S g t).comap S.ρ).map S.M.subtype := by
      refine iSup₂_le fun h ht => ?_
      intro y hy
      have hyM : y ∈ S.M := La_le_M S _ hy
      refine ⟨⟨y, hyM⟩, ?_, rfl⟩
      show S.ρ ⟨y, hyM⟩ ∈ Rbar S g t
      refine Lbar_mul_le_Rbar ht ?_
      rw [← S.map_La_eq_Lbar]
      exact ⟨⟨y, hyM⟩, mem_subgroupOf.mpr hy, rfl⟩
    obtain ⟨y, hy, hyx⟩ := key hx'
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · subst hX
    rw [← S.map_La_eq_Lbar]
    exact map_mono fun y hy => mem_subgroupOf.mpr (La_mul_le_R ht (mem_subgroupOf.mp hy))

theorem mem_R_iff {g : G} {t : S.O} (ht : t ∈ S.Lbar g) {x : G} :
    x ∈ R S g t ↔ ∃ hx : x ∈ S.M, S.ρ ⟨x, hx⟩ ∈ Rbar S g t := by
  constructor
  · intro hx
    refine ⟨R_le_M hx, ?_⟩
    rw [← map_R_eq_Rbar]
    exact ⟨⟨x, R_le_M hx⟩, mem_subgroupOf.mpr hx, rfl⟩
  · rintro ⟨hxM, hx⟩
    rw [← map_R_eq_Rbar] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hQ : (y⁻¹ * ⟨x, hxM⟩ : S.M) ∈ S.Q := by
      rw [← S.ker_ρ, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hxy : x = (y : G) * ((y⁻¹ * ⟨x, hxM⟩ : S.M) : G) := by simp
    rw [hxy]
    exact mul_mem (mem_subgroupOf.mp hy) (QG_le_R ht ⟨_, hQ, rfl⟩)

theorem mem_N_iff {g : G} {t : S.O} (ht : t ∈ S.Lbar g) {x : G} :
    x ∈ N S g t ↔ ∃ hx : x ∈ S.M, S.ρ ⟨x, hx⟩ ∈ Nbar S g t := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, -⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hxM, hx⟩
    exact ⟨⟨⟨x, hxM⟩, hx, rfl⟩, (mem_R_iff ht).mpr ⟨hxM, hx.1⟩⟩

theorem Nbar_le_Rbar {g : G} {t : S.O} : Nbar S g t ≤ Rbar S g t := fun _ hx => hx.1

theorem mem_Nbar {g : G} {t : S.O} {x : S.O} :
    x ∈ Nbar S g t ↔ x ∈ Rbar S g t ∧ ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  Iff.rfl

theorem cl_mem_Vt {g : G} {t : S.O} {h : S.M} (ht : t ∈ S.Lbar ((h : G) * g)) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t :=
  Submodule.subset_span ⟨h, ht, rfl⟩

theorem cl_a_mem_Vt {g : G} {t : S.O} (ht : t ∈ S.Lbar g) : S.cl (g * S.z * g⁻¹) ∈ Vt S g t := by
  have := cl_mem_Vt (S := S) (g := g) (t := t) (h := 1) (by simpa using ht)
  simpa using this

theorem apply_mem_Vt {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {k : S.M}
    (hk : S.ρ k * t = t * S.ρ k) {v : S.Qt} (hv : v ∈ Vt S g t) :
    ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, ht, rfl⟩ := hv
    have hmem := conj_mem_Dset hk (Lbar_mul_mem_Dset (S := S) ht)
    rw [← Lbar_mul S k, show (k : G) * ((h : G) * g) = ((k * h : S.M) : G) * g by
      simp [mul_assoc]] at hmem
    obtain ⟨-, -, ht'⟩ := hmem
    have := cl_mem_Vt ht'
    rwa [S.ρ_cl k (conj_mem_QG' S h.2 haQ), show (k : G) * ((h : G) * g * S.z * ((h : G) * g)⁻¹) *
      (k : G)⁻¹ = ((k * h : S.M) : G) * g * S.z * (((k * h : S.M) : G) * g)⁻¹ by
      simp only [Subgroup.coe_mul]; group]
  | zero => simp
  | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

theorem apply_mem_Vt_of_mem_Rbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t x : S.O}
    (hx : x ∈ Rbar S g t) {v : S.Qt} (hv : v ∈ Vt S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  exact apply_mem_Vt haQ (commute_of_mem_Rbar haQ hx) hv

theorem conj_mem_Nbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {k : S.M}
    (hk : S.ρ k * t = t * S.ρ k) {x : S.O} (hx : x ∈ Nbar S g t) :
    S.ρ k * x * (S.ρ k)⁻¹ ∈ Nbar S g t := by
  refine ⟨conj_mem_Rbar hk hx.1, fun v hv => ?_⟩
  have hk' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
    rw [map_inv]
    calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hk]
      _ = t * (S.ρ k)⁻¹ := by group
  have hv' := apply_mem_Vt haQ hk' hv
  rw [map_inv] at hv'
  rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    hx.2 _ hv', ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

theorem Lbar_mul_mul_eq_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {h k : S.M}
    (hfix : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) :
    S.Lbar ((k : G) * ((h : G) * g)) = S.Lbar ((h : G) * g) := by
  have haQ' := conj_mem_QG' S h.2 haQ
  refine Lbar_eq_of_cl_eq S haQ' (conj_ne_z' S h.2 hne) (conj_mem_QG' S k.2 haQ') ?_
  rw [← ρ_cl_conj_z S k haQ', hfix]

theorem mem_normalizer_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {h : S.M} {x : S.O} (hxM : x ∈ S.Mbar)
    (hfix : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) :
    x ∈ normalizer (S.Lbar ((h : G) * g) : Set S.O) := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hxM
  have e := Lbar_mul_mul_eq_of_fix haQ hne hfix
  rw [Lbar_mul S k] at e
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← e]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← e] at hy
    obtain ⟨y', hy', hyy'⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyy'
    have : y' = y := by
      have := congrArg (fun w => (S.ρ k)⁻¹ * w * S.ρ k) hyy'
      simpa [mul_assoc] using this
    rw [← this]
    exact hy'

theorem Nbar_le_normalizer {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {t : S.O} {X : Subgroup S.O} (hX : X ∈ Dset S g t) :
    Nbar S g t ≤ normalizer (X : Set S.O) := by
  obtain ⟨h, rfl, ht⟩ := hX
  intro x hx
  exact mem_normalizer_of_fix haQ hne (Rbar_le_Mbar hx.1) (hx.2 _ (cl_mem_Vt ht))

end CFSG.LargeExtraspecial.S4
