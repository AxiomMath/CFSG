module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallCore
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL3U3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocGL2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG.CGT.PushingUpLit.SolKNA.R4
open CFSG CFSG.Open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Q3.TA3
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)
open CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open scoped MatrixGroups commutatorElement

theorem twinCyc4_l2 {F : Type} [Group F] [Finite F] (h : SmallL2 F) : TwinCyc4 F := by
  obtain ⟨p, f, K, _, _, hp, hpodd, hf, h3, hK, ⟨e⟩⟩ := soc_l2_data h
  haveI : Fact p.Prime := ⟨hp⟩
  intro z hz
  have ht : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  obtain ⟨m, hm, ⟨ψ⟩⟩ := soc_l2_centralizer_dihedral K hK hpodd hf h3 ht
  haveI := hm
  obtain ⟨c, hc⟩ : ∃ c : Subgroup.centralizer ({e z} : Set (PSL2 K)),
      ψ c = DihedralGroup.r (1 : ZMod m) :=
    ⟨ψ.symm (DihedralGroup.r (1 : ZMod m)), ψ.apply_symm_apply _⟩
  refine ⟨Subgroup.zpowers (e.symm (c : PSL2 K)), Subgroup.isCyclic_zpowers _, ?_⟩
  intro X _ hX u huX hou
  have hgz : u * z = z * u :=
    Subgroup.mem_centralizer_singleton_iff.mp (hX.le huX)
  have hhC : e u ∈ Subgroup.centralizer ({e z} : Set (PSL2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := congrArg e hgz
    rw [map_mul, map_mul] at h2
    exact h2
  have hh4 : 4 ≤ orderOf (e u) := by
    rw [MulEquiv.orderOf_eq, hou]
  obtain ⟨k, hk⟩ := soc_l2_centralizer_mem_zpowers ψ c hc hhC hh4
  have h2 : e.symm ((c : PSL2 K) ^ k) = u := by
    rw [hk, MulEquiv.symm_apply_apply]
  rw [map_zpow] at h2
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩

theorem mem_scalar_of_solvable_subnormal {K : Type} [Field K] [Finite K]
    {H : Subgroup (GL (Fin 2) K)} {F : Type} [Group F] [Finite F] {z : F} {π : H →* F}
    (hrange : π.range = Subgroup.centralizer ({z} : Set F)) (hk : CubeKer π)
    (hcs : SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀]
    (h4 : 4 ≤ Nat.card F₀) (eJ : slPart H ≃* SL(2, F₀)) {X : Subgroup F}
    (hXs : Group.IsSolvable ↥X)
    (hX : CFSG.Open.IsSubnormal X (Subgroup.centralizer ({z} : Set F))) {m : H}
    (hm : π m ∈ X) :
    ∃ c : Kˣ, (m : GL (Fin 2) K) = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  set M : Subgroup H := X.comap π with hM
  have hCtop : (Subgroup.centralizer ({z} : Set F)).comap π = ⊤ := by
    rw [eq_top_iff]
    intro x _
    show π x ∈ Subgroup.centralizer ({z} : Set F)
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hMsub : M.IsSubnormal := by
    have := hX.comap π
    rw [hCtop] at this
    exact CFSG.Open.IsSubnormal.top_iff.mp this
  have hMsolv : Group.IsSolvable ↥M := by
    let φ : ↥M →* ↥X :=
      { toFun := fun x => ⟨π (x : H), x.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp) }
    have hker : Group.IsSolvable ↥φ.ker := by
      apply isSolvable_of_comm
      intro a b
      obtain ⟨ωa, -, ha⟩ := hk (a : ↥M) (by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
        exact this)
      obtain ⟨ωb, -, hb⟩ := hk (b : ↥M) (by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp b.2)
        exact this)
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      show ((a : ↥M) : H).1 * ((b : ↥M) : H).1 = ((b : ↥M) : H).1 * ((a : ↥M) : H).1
      rw [ha, hb]
      exact scalar_mul_comm ωa _
    haveI := hker
    haveI := hXs
    exact solvable_of_ker_le_range φ.ker.subtype φ (by simp)
  have hSn : (slPart H).Normal := MonoidHom.normal_ker _
  have hQS : CFSG.IsQuasisimple ↥(slPart H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4)
  have hcomp : CFSG.IsComponent (slPart H) := ⟨hQS, hSn.isSubnormal⟩
  have hcent := (CFSG.LocalCores.component_solvable_centralizer hMsolv hMsub).1 _ hcomp
  have hmM : m ∈ M := hm
  have hcomm : ∀ s ∈ slPart H, s * m = m * s := by
    intro s hs
    have h1 : ⁅s, m⁆ ∈ ⁅slPart H, M⁆ := Subgroup.commutator_mem_commutator hs hmM
    rw [hcent, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  exact hcs (m : GL (Fin 2) K) (fun B hB => congrArg Subtype.val (hcomm B hB).symm)

theorem twinCyc4_of_gl2 {F : Type} [Group F] [Finite F] {K : Type} [Field K] [Finite K]
    {z : F} {H : Subgroup (GL (Fin 2) K)} (π : H →* F)
    (hrange : π.range = Subgroup.centralizer ({z} : Set F)) (hk : CubeKer π)
    (hcs : SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀]
    (h4 : 4 ≤ Nat.card F₀) (eJ : slPart H ≃* SL(2, F₀)) :
    ∃ A : Subgroup F, IsCyclic ↥A ∧ ∀ X : Subgroup F, Group.IsSolvable ↥X →
      CFSG.Open.IsSubnormal X (Subgroup.centralizer ({z} : Set F)) →
        ∀ u ∈ X, orderOf u = 4 → u ∈ A := by
  have hHsc : IsCyclic (socScalarPart H) := soc_isCyclic_scalarPart H
  refine ⟨(π.comp (socScalarPart H).subtype).range, ?_, ?_⟩
  · exact isCyclic_of_surjective (π.comp (socScalarPart H).subtype).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  · intro X hXs hX u huX _
    have hnr : u ∈ π.range := by
      rw [hrange]
      exact hX.le huX
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hnr
    obtain ⟨c, hc⟩ := mem_scalar_of_solvable_subnormal hrange hk hcs h4 eJ hXs hX
      (m := m) (by rw [hm]; exact huX)
    exact MonoidHom.mem_range.mpr ⟨⟨m, Subgroup.mem_subgroupOf.mpr
      (MonoidHom.mem_range.mpr ⟨c, hc.symm⟩)⟩, hm⟩

theorem twinCyc4_l3 {F : Type} [Group F] [Finite F] (h : SmallL3Ne3 F) : TwinCyc4 F := by
  obtain ⟨p, f, hp, hp2, hf, h3, -, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  obtain ⟨hodd, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  have hK' : Odd (Nat.card K) := by
    rw [hK]
    exact hodd
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    omega
  let e0 : F ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K))
  intro z hz
  let e' : ↥(⊤ : Subgroup F) ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    Subgroup.topEquiv.trans e0
  obtain ⟨-, π, hπr, hk, -⟩ := Q5L3.exists_frame hK' e' (Subgroup.mem_top z) hz
  have hrange : π.range = Subgroup.centralizer ({z} : Set F) := by
    rw [hπr, top_inf_eq]
  exact twinCyc4_of_gl2 π hrange hk Q5L3.slCentScalar_top h4 Q5L3.slPartTopEquiv


theorem twinCyc4_u3 {F : Type} [Group F] [Finite F] (h : SmallU3Ne3 F) : TwinCyc4 F := by
  obtain ⟨p, f, hp, hp2, hf, h3, -, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  obtain ⟨-, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := hU.charP
  have hcardF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) = p ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  have h4 : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) := by
    rw [hcardF]
    omega
  obtain ⟨eJ⟩ := Q5U3.nonempty_slPart_equiv hU
  intro z hz
  let e' : ↥(⊤ : Subgroup F) ≃* StatedProj (StatedSU 3 (p ^ f) K) :=
    Subgroup.topEquiv.trans e
  obtain ⟨π, hπr, hk, -⟩ := Q5U3.exists_frame hU hp2 e' (Subgroup.mem_top z) hz
  have hrange : π.range = Subgroup.centralizer ({z} : Set F) := by
    rw [hπr, top_inf_eq]
  exact twinCyc4_of_gl2 π hrange hk (Q5U3.slCentScalar_GU2 hU) h4 eJ


theorem false_of_l2 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) (hF : SmallL2 ↥(genFittingFStar Y)) :
    False :=
  false_of_twinCyc4 hr h (socleOutAbelian_l2 hF).comm2 (twinCyc4_l2 hF)

theorem false_of_l3 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) (hF : SmallL3Ne3 ↥(genFittingFStar Y)) :
    False :=
  false_of_twinCyc4 hr h (socleOutAbelian_l3 hF).comm2 (twinCyc4_l3 hF)

theorem false_of_u3 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) (hF : SmallU3Ne3 ↥(genFittingFStar Y)) :
    False :=
  false_of_twinCyc4 hr h (socleOutAbelian_u3 hF).comm2 (twinCyc4_u3 hF)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
