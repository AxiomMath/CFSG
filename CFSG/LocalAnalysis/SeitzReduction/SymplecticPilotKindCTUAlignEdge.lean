module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignRigid

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Overlap

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem card_compl_singleton_ctua (k : Fin N) : ({k} : Finset (Fin N))ᶜ.card = N - 1 := by
  rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]

theorem card_compl_pair_ctua {k l : Fin N} (hkl : k ≠ l) :
    ({k, l} : Finset (Fin N))ᶜ.card = N - 2 := by
  rw [Finset.card_compl, Finset.card_pair hkl, Fintype.card_fin]

theorem CtuParam.injOn_ctuBlock (hF : Nat.card F = (2 ^ f) ^ 2) (hN : 3 ≤ N) {k l : Fin N}
    (hkl : k ≠ l) (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    {x y : ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))}
    (hx : (x : SU (unitaryInvolution F 2 f) (2 * N + ε)) ∈
      ctuBlock (unitaryInvolution F 2 f) ε ({l} : Finset (Fin N)))
    (hy : (y : SU (unitaryInvolution F 2 f) (2 * N + ε)) ∈
      ctuBlock (unitaryInvolution F 2 f) ε ({l} : Finset (Fin N)))
    (hxy : P.Φ x = P.Φ y) : x = y := by
  have hc := card_compl_singleton_ctua k
  have hker : x * y⁻¹ ∈ P.Φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have h1 := eq_one_of_mem_center_ctuBlock hF hε (by omega)
    (fun h => by have := (Prod.mk.inj h).1; omega) (P.ker_le hker) (k := l)
    (by simpa using Ne.symm hkl) (mul_mem hx (inv_mem hy))
  exact mul_inv_eq_one.1 h1

omit [CharP K 2] [Finite F] [CharP F 2] in
theorem rootTorusSp_le_spBlock_compl {k l : Fin N} (hkl : k ≠ l) {y : StatedSp N K}
    (hy : y ∈ rootTorusSp K l) : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ := by
  have h1 : y ∈ spBlock K ({l} : Finset (Fin N)) := by
    rw [spBlock_singleton]
    exact rootTorusSp_le_longRootSp2 l hy
  exact spBlock_mono (by simpa using hkl) h1

theorem CtuParam.map_rootTorus_eq {k : Fin N} (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    {l : Fin N} (hkl : k ≠ l) :
    (((rootTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι)).subgroupOf
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))).map P.Φ =
        modelToG e (rootTorusSp K l) := by
  ext g
  constructor
  · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
    have hx : x = ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y,
        ctuEmbed_mem_ctuBlock_iff.2 (rootTorusSp_le_spBlock_compl hkl hy)⟩ := Subtype.ext hyx.symm
    rw [hx, P.N1 y (rootTorusSp_le_spBlock_compl hkl hy)]
    exact UnitaryPilot.symm_mem_modelToG e hy
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
    exact ⟨⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y,
      ctuEmbed_mem_ctuBlock_iff.2 (rootTorusSp_le_spBlock_compl hkl hy)⟩, ⟨y, hy, rfl⟩,
      P.N1 y (rootTorusSp_le_spBlock_compl hkl hy)⟩

theorem CtuParam.map_overlap_eq [Finite G] [Finite K] (hF : Nat.card F = (2 ^ f) ^ 2)
    (hK : 4 ≤ Nat.card K) (hN : 4 ≤ N) {k : Fin N}
    (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k) {l : Fin N} (hkl : k ≠ l) :
    ((ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))).subgroupOf
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))).map P.Φ =
        centralizerPerfectCore (modelToG e (rootTorusSp K k) ⊔ modelToG e (rootTorusSp K l)) := by
  have hc := card_compl_pair_ctua hkl
  rw [F4Pilot.centralizerPerfectCore_sup,
    show centralizerPerfectCore (modelToG e (rootTorusSp K k)) = neighbourCore e k from rfl,
    ← P.range_eq, ← P.map_rootTorus_eq hkl,
    perfectCore_range_inf_centralizer_map P.Φ P.ker_le]
  congr 1
  apply Subgroup.map_injective
    (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype_injective
  have hXle : (rootTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) ≤
      ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ctuEmbed_mem_ctuBlock_iff.2 (rootTorusSp_le_spBlock_compl hkl hy)
  have hA : (((rootTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι)).subgroupOf
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))).map
        (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype =
      (rootTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hXle]
  have hB : ((ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))).subgroupOf
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))).map
        (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype =
      ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (ctuBlock_pair_le_left _ k l)]
  rw [hB, CFSG.Quasithin.map_perfectCore, ← ct_inf_centralizer_map_subtype_eq, hA,
    perfectCore_ctuBlock_inf_centralizer_rootTorus hF hε hι hK (by omega)
      (fun h => by have := h.1; omega)]

end Overlap

section TwistBy

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {F : Type} [Field F] {hε : ε ≤ 1} {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}
  {e : L ≃* StatedSp N K}

@[expose] noncomputable def CtuaAdmissible.restrict {T : MulAut (SU σ (2 * N + ε))}
    (hT : CtuaAdmissible hε σ ι hι T) (R : Finset (Fin N)) : MulAut (ctuBlock σ ε R) where
  toFun x := ⟨T x, (hT.mem_iff R x).2 x.2⟩
  invFun x := ⟨T⁻¹ x, (hT.inv.mem_iff R x).2 x.2⟩
  left_inv x := Subtype.ext (by
    change T⁻¹ (T (x : SU σ (2 * N + ε))) = x
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply])
  right_inv x := Subtype.ext (by
    change T (T⁻¹ (x : SU σ (2 * N + ε))) = x
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply])
  map_mul' x y := Subtype.ext (map_mul T (x : SU σ (2 * N + ε)) y)

theorem CtuaAdmissible.coe_restrict {T : MulAut (SU σ (2 * N + ε))}
    (hT : CtuaAdmissible hε σ ι hι T) (R : Finset (Fin N)) (x : ctuBlock σ ε R) :
    ((hT.restrict R x : ctuBlock σ ε R) : SU σ (2 * N + ε)) = T x := rfl

@[expose] noncomputable def CtuParam.twistBy {k : Fin N} (P : CtuParam ε hε σ ι hι e k)
    {T : MulAut (SU σ (2 * N + ε))} (hT : CtuaAdmissible hε σ ι hι T) :
    CtuParam ε hε σ ι hι e k where
  Φ := P.Φ.comp (hT.restrict {k}).toMonoidHom
  ker_le := by
    intro x hx
    have hx' : hT.restrict {k} x ∈ P.Φ.ker := hx
    have h1 := P.ker_le hx'
    rw [mem_center_iff] at h1 ⊢
    intro g
    apply (hT.restrict {k}).injective
    rw [map_mul, map_mul]
    exact h1 _
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, P.range_eq]
  N1 y hy := by
    change P.Φ (hT.restrict {k} ⟨ctuEmbed ε hε σ ι hι y, _⟩) = _
    have h1 : hT.restrict {k} ⟨ctuEmbed ε hε σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ⟨ctuEmbed ε hε σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ := Subtype.ext (hT.fix y)
    rw [h1]
    exact P.N1 y hy

theorem CtuParam.twistBy_Φ_apply {k : Fin N} (P : CtuParam ε hε σ ι hι e k)
    {T : MulAut (SU σ (2 * N + ε))} (hT : CtuaAdmissible hε σ ι hι T) (x : ctuBlock σ ε {k}) :
    (P.twistBy hT).Φ x = P.Φ (hT.restrict {k} x) := rfl

end TwistBy

section Edge

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem CtuParam.exists_twist_of_overlap (hKc : Nat.card K = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hN : 4 ≤ N) {k l : Fin N} (hkl : k ≠ l)
    (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (Q : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e l) :
    ∃ (ν : Fˣ) (hν : unitaryInvolution F 2 f ν * ν = 1) (b : Bool),
      ∀ (x : SU (unitaryInvolution F 2 f) (2 * N + ε))
        (hx : x ∈ ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))),
        P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ =
          Q.Φ ⟨ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b x,
            ctuBlock_pair_le_right _ k l ((ctuaTwist_mem_ctuBlock_iff hν b _ x).2 hx)⟩ := by
  have hK : 4 ≤ Nat.card K := hKc ▸ CFSG.SeitzReduction.SymplecticPilot.four_le_two_pow hf
  have hc := card_compl_pair_ctua hkl
  set φP : ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) →* G :=
    P.Φ.comp (Subgroup.inclusion (ctuBlock_pair_le_left _ k l)) with hφP
  set φQ : ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) →* G :=
    Q.Φ.comp (Subgroup.inclusion (ctuBlock_pair_le_right _ k l)) with hφQ
  have hPinj : Function.Injective φP := fun x y h => by
    have h' := P.injOn_ctuBlock hF (by omega) hkl (ctuBlock_pair_le_right _ k l x.2)
      (ctuBlock_pair_le_right _ k l y.2) h
    exact Subtype.ext (congrArg (fun w : ctuBlock (unitaryInvolution F 2 f) ε
      ({k} : Finset (Fin N)) => (w : SU (unitaryInvolution F 2 f) (2 * N + ε))) h')
  have hQinj : Function.Injective φQ := fun x y h => by
    have h' := Q.injOn_ctuBlock hF (by omega) (Ne.symm hkl) (ctuBlock_pair_le_left _ k l x.2)
      (ctuBlock_pair_le_left _ k l y.2) h
    exact Subtype.ext (congrArg (fun w : ctuBlock (unitaryInvolution F 2 f) ε
      ({l} : Finset (Fin N)) => (w : SU (unitaryInvolution F 2 f) (2 * N + ε))) h')
  have hrange : ∀ {m : Fin N} (Φ : ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N)) →* G)
      (h : ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) ≤
        ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N))),
      (Φ.comp (Subgroup.inclusion h)).range =
        ((ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))).subgroupOf
          (ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N)))).map Φ := by
    intro m Φ h
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion h y, mem_subgroupOf.2 y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, mem_subgroupOf.1 hy⟩, rfl⟩
  have hr : φP.range = φQ.range := by
    rw [hφP, hφQ, hrange P.Φ, hrange Q.Φ, P.map_overlap_eq hF hK hN hkl]
    have h3 := Q.map_overlap_eq hF hK hN (Ne.symm hkl)
    rw [show ({l, k} : Finset (Fin N)) = {k, l} from Finset.pair_comm l k] at h3
    rw [h3, sup_comm]
  set θ : MulAut (ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))) :=
    ((MonoidHom.ofInjective hPinj).trans (MulEquiv.subgroupCongr hr)).trans
      (MonoidHom.ofInjective hQinj).symm with hθdef
  have hθ : ∀ y, φQ (θ y) = φP y := by
    intro y
    have h := (MonoidHom.ofInjective hQinj).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective hPinj y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hfix : ∀ (y : StatedSp N K) (hy : y ∈ spBlock K ({k, l} : Finset (Fin N))ᶜ),
      θ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ := by
    intro y hy
    have hyk : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have hyl : y ∈ spBlock K ({l} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    apply hQinj
    rw [hθ]
    exact (P.N1 y hyk).trans (Q.N1 y hyl).symm
  obtain ⟨ν, hν, b, htw⟩ := exists_ctuaTwist_of_mulAut_fix hKc hF (by omega) hε hι
    (R := ({k, l} : Finset (Fin N))) (by omega) θ hfix
  refine ⟨ν, hν, b, fun x hx => ?_⟩
  have h1 := hθ ⟨x, hx⟩
  rw [hφP, hφQ, MonoidHom.comp_apply, MonoidHom.comp_apply] at h1
  exact h1.symm.trans (congrArg Q.Φ (Subtype.ext (htw ⟨x, hx⟩)))

end Edge

end CFSG.SeitzReduction.SymplecticPilot
