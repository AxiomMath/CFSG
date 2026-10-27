module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCover
public import CFSG.LargeExtraspecial.DWFldOrth
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaDickson
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding Subgroup CFSG.RankThree.OrthogonalInvolutions
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

theorem commSpace_orthLeviRes {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A]
    {r t : ℕ} (ht : t ≤ r) (B : ((Fin (r - t) ⊕ Fin (r - t) → K) × A) ≃ₗ[K]
      ((Fin (r - t) ⊕ Fin (r - t) → K) × A)) :
    commSpace (LeviBlock.orthLeviRes K A ht B) =
      (commSpace B).map (LeviBlock.orthResIncl K A ht) := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, rfl⟩ := mem_commSpace.1 hv
    rw [LeviBlock.orthLeviRes_apply, LeviBlock.orthResExt_apply, add_sub_cancel_left]
    exact Submodule.mem_map_of_mem (mem_commSpace.mpr ⟨LeviBlock.orthResProj K A ht u, rfl⟩)
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    obtain ⟨y, rfl⟩ := mem_commSpace.1 hw
    rw [mem_commSpace]
    refine ⟨LeviBlock.orthResIncl K A ht y, ?_⟩
    rw [LeviBlock.orthLeviRes_apply, LeviBlock.orthResExt_apply,
      LeviBlock.orthResProj_orthResIncl, add_sub_cancel_left]
    rfl

theorem isResPerp_of_mem_perp_tailFlag {K : Type*} [Field K] {A : Type*} [AddCommGroup A]
    [Module K A] {r t : ℕ} (ht : t ≤ r) {qA : QuadraticForm K A}
    (hQ : (QuadraticMap.polarBilin (quadTail r qA)).Nondegenerate)
    {v : (Fin r ⊕ Fin r → K) × A}
    (hv : v ∈ (CFSG.RankThree.OrthogonalInvolutions.toQuadForm (quadTail r qA)
      hQ).polar.perp (tailFlag K A r t)) : LeviBlock.IsResPerp ht v := by
  rw [CFSG.RankThree.OrthogonalInvolutions.toQuadForm_perp] at hv
  refine (CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.polar_tailFlag_eq_zero_iff
    (qB := qA) ht).1 fun w hw => ?_
  have h := (LinearMap.BilinForm.mem_orthogonal_iff.1 hv) w hw
  rwa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] at h


theorem sub_mem_tailFlag_of_orthParab_orthLeviRes_inv {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ} (hd : LeviBlock.OrthCuts r d)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (x : ↥(LeviBlock.orthParab r (minusTailForm K b c) d))
    {v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)}
    (hv : v ∈ (CFSG.RankThree.OrthogonalInvolutions.toQuadForm
      (quadTail r (minusTailForm K b c))
      (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))).polar.perp
        (tailFlag K (Fin 2 → K) r (d (Fin.last s)))) :
    (((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
        (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) *
      (LeviBlock.orthLeviRes K (Fin 2 → K) hd.last
        (LeviBlock.orthResHom (minusTailForm K b c) hd x))⁻¹) v - v ∈
      tailFlag K (Fin 2 → K) r (d (Fin.last s)) := by
  classical
  have hvperp : LeviBlock.IsResPerp hd.last v :=
    isResPerp_of_mem_perp_tailFlag hd.last _ hv
  let u : (Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K) :=
    LeviBlock.orthResProj K (Fin 2 → K) hd.last v
  let z : (Fin r ⊕ Fin r → K) × (Fin 2 → K) :=
    v - LeviBlock.orthResIncl K (Fin 2 → K) hd.last u
  have hz : z ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) :=
    LeviBlock.sub_orthResIncl_mem hd.last hvperp
  let B : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) :=
    LeviBlock.orthLeviRes K (Fin 2 → K) hd.last (LeviBlock.orthResHom (minusTailForm K b c) hd x)
  let w : (Fin r ⊕ Fin r → K) × (Fin 2 → K) := B⁻¹ v
  have hBinv : B⁻¹ = LeviBlock.orthLeviRes K (Fin 2 → K) hd.last
      (LeviBlock.orthResHom (minusTailForm K b c) hd x).symm := by
    show (LeviBlock.orthLeviRes K (Fin 2 → K) hd.last
      (LeviBlock.orthResHom (minusTailForm K b c) hd x))⁻¹ = _
    rw [← map_inv]
    rfl
  have hwr : LeviBlock.IsResPerp hd.last w := by
    show LeviBlock.IsResPerp hd.last (B⁻¹ v)
    rw [hBinv]
    exact LeviBlock.isResPerp_map hd.last
      (LeviBlock.orthLeviRes_mem_orthogonalGroup hd.last
        (Subgroup.inv_mem _ (LeviBlock.orthResHom_mem_orthogonalGroup hd x)))
      (LeviBlock.map_tailFlag_orthLeviRes hd.last le_rfl _) hvperp
  have hpiw : LeviBlock.orthResProj K (Fin 2 → K) hd.last w =
      (LeviBlock.orthResHom (minusTailForm K b c) hd x).symm u := by
    show LeviBlock.orthResProj K (Fin 2 → K) hd.last (B⁻¹ v) = _
    rw [hBinv, LeviBlock.orthLeviRes_apply, LeviBlock.orthResProj_orthResExt]
    rfl
  have hgwperp : LeviBlock.IsResPerp hd.last
      (((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
        (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) w) :=
    LeviBlock.isResPerp_of_mem_orthParab hd x.2 hwr
  have hpi_gw : LeviBlock.orthResProj K (Fin 2 → K) hd.last
      (((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
        (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) w) =
      LeviBlock.orthResHom (minusTailForm K b c) hd x
        (LeviBlock.orthResProj K (Fin 2 → K) hd.last w) := by
    have hz' : w - LeviBlock.orthResIncl K (Fin 2 → K) hd.last
        (LeviBlock.orthResProj K (Fin 2 → K) hd.last w) ∈
        tailFlag K (Fin 2 → K) r (d (Fin.last s)) :=
      LeviBlock.sub_orthResIncl_mem hd.last hwr
    have hsplit : (((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
        (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) w) =
        (((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
          (quadTail r (minusTailForm K b c)))) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
          (LeviBlock.orthResIncl K (Fin 2 → K) hd.last
            (LeviBlock.orthResProj K (Fin 2 → K) hd.last w))) +
        (((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
          (quadTail r (minusTailForm K b c)))) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
          (w - LeviBlock.orthResIncl K (Fin 2 → K) hd.last
            (LeviBlock.orthResProj K (Fin 2 → K) hd.last w))) := by
      rw [← map_add]
      abel
    rw [hsplit, map_add]
    have h0 : LeviBlock.orthResProj K (Fin 2 → K) hd.last
        (((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
          (quadTail r (minusTailForm K b c)))) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
          (w - LeviBlock.orthResIncl K (Fin 2 → K) hd.last
            (LeviBlock.orthResProj K (Fin 2 → K) hd.last w))) = 0 :=
      LeviBlock.orthResProj_eq_zero_of_mem hd.last
        (LeviBlock.mapsTo_of_mem_orthParab
          (x := (x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
            (quadTail r (minusTailForm K b c))))) x.2 (Fin.last s) _ hz')
    rw [h0, add_zero]
    exact ((LeviBlock.orthResMat_apply hd.last _ _).symm).trans
      (LeviBlock.orthResHom_apply hd x _).symm
  have hpi_diff : LeviBlock.orthResProj K (Fin 2 → K) hd.last
      ((((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
        (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) w) - v) =
      0 := by
    rw [map_sub, hpi_gw, hpiw, LinearEquiv.apply_symm_apply]
    exact sub_self u
  have hdiff : ((((x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
      (quadTail r (minusTailForm K b c)))) :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) w) - v) ∈
      tailFlag K (Fin 2 → K) r (d (Fin.last s)) := by
    refine LeviBlock.mem_tailFlag_of_orthResProj_eq_zero hd.last ?_ hpi_diff
    intro i
    rw [Prod.fst_sub, Pi.sub_apply, hgwperp i, hvperp i, sub_zero]
  rw [LinearEquiv.mul_apply]
  exact hdiff

theorem orthResHom_mem_omegaGroup {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    {r s : ℕ} {d : Fin (s + 1) → ℕ} (hd : LeviBlock.OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (x : ↥(LeviBlock.orthParab r (minusTailForm K b c) d)) :
    LeviBlock.orthResHom (minusTailForm K b c) hd x ∈
      omegaGroup (quadTail (r - d (Fin.last s)) (minusTailForm K b c))
        (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)) := by
  classical
  have hQ : (QuadraticMap.polarBilin (quadTail r (minusTailForm K b c))).Nondegenerate :=
    nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)
  let g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) :=
    (x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
      (quadTail r (minusTailForm K b c))))
  let B : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) :=
    LeviBlock.orthLeviRes K (Fin 2 → K) hd.last
      (LeviBlock.orthResHom (minusTailForm K b c) hd x)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)) :=
    LeviBlock.mem_orthogonalGroup_of_mem_orthParab
  have hgE : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c))⁆ := by
    rw [LeviBlock.commutator_orthogonalGroup_quadTail_minus hr hirr]
    exact (x : ↥(CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup
      (quadTail r (minusTailForm K b c)))).2
  have hgω : g ∈ omegaGroup (quadTail r (minusTailForm K b c)) hQ :=
    CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup hQ hgE
  have hZ : (CFSG.RankThree.OrthogonalInvolutions.toQuadForm
      (quadTail r (minusTailForm K b c)) hQ).IsTotallySingular
      (tailFlag K (Fin 2 → K) r (d (Fin.last s))) := by
    intro z hz
    rw [CFSG.RankThree.OrthogonalInvolutions.toQuadForm_Q]
    exact quadTail_eq_zero_of_mem_tailFlag hz
  have htriv : ∀ v ∈ (CFSG.RankThree.OrthogonalInvolutions.toQuadForm
      (quadTail r (minusTailForm K b c)) hQ).polar.perp
        (tailFlag K (Fin 2 → K) r (d (Fin.last s))),
      (g * B⁻¹) v - v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) := by
    intro v hv
    exact sub_mem_tailFlag_of_orthParab_orthLeviRes_inv hd hirr x hv
  have hBinvO : B⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)) :=
    Subgroup.inv_mem _ (LeviBlock.orthLeviRes_mem_orthogonalGroup hd.last
      (LeviBlock.orthResHom_mem_orthogonalGroup hd x))
  have hg' : g * B⁻¹ ∈ omegaGroup (quadTail r (minusTailForm K b c)) hQ :=
    CFSG.StandardType.GGOppRadOmega.mem_omegaGroup_of_triv hQ
      (Subgroup.mul_mem _ hgO hBinvO) hZ htriv
  have hlev : B ∈ omegaGroup (quadTail r (minusTailForm K b c)) hQ := by
    have h1 : (g * B⁻¹)⁻¹ * g = B := by group
    rw [← h1]
    exact (omegaGroup (quadTail r (minusTailForm K b c)) hQ).mul_mem
      ((omegaGroup (quadTail r (minusTailForm K b c)) hQ).inv_mem hg') hgω
  have hEvenB : Even (Module.finrank K (commSpace B)) := (mem_omegaGroup.1 hlev).2
  have hinj : Function.Injective (LeviBlock.orthResIncl K (Fin 2 → K) hd.last) := by
    intro u v huv
    have h := congrArg (LeviBlock.orthResProj K (Fin 2 → K) hd.last) huv
    simpa only [LeviBlock.orthResProj_orthResIncl] using h
  have hfin : Module.finrank K (commSpace (LeviBlock.orthResHom (minusTailForm K b c) hd x)) =
      Module.finrank K (commSpace B) := by
    have hB : B = LeviBlock.orthLeviRes K (Fin 2 → K) hd.last
        (LeviBlock.orthResHom (minusTailForm K b c) hd x) := rfl
    rw [hB, commSpace_orthLeviRes hd.last]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq
  refine mem_omegaGroup.mpr ⟨LeviBlock.orthResHom_mem_orthogonalGroup hd x, ?_⟩
  rw [hfin]
  exact hEvenB

theorem le_normalizer_pi_of_forall {ι : Type} {G : ι → Type} [∀ j, Group (G j)]
    {S : ∀ j, Subgroup (G j)} {H : Subgroup (∀ j, G j)}
    (h : ∀ g ∈ H, ∀ j, g j ∈ Subgroup.normalizer (S j : Set (G j))) :
    H ≤ Subgroup.normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_pi] at hx ⊢
    intro j _
    have hj := (Subgroup.mem_normalizer_iff.1 (h g hg j)) (x j)
    simpa using hj.1 (hx j trivial)
  · intro hx
    rw [Subgroup.mem_pi] at hx ⊢
    intro j _
    have hj := (Subgroup.mem_normalizer_iff.1 (h g hg j)) (x j)
    simpa using hj.2 (hx j trivial)

theorem relIndex_orthResDer_omegaGroup {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    {f m : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 1 ≤ m)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) :
    (LeviBlock.orthResDer K b c m).relIndex
      (omegaGroup (quadTail m (minusTailForm K b c))
        (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))) = 1 := by
  classical
  have hQ : (QuadraticMap.polarBilin (quadTail m (minusTailForm K b c))).Nondegenerate :=
    nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)
  have hST : LeviBlock.orthResDer K b c m ≤ omegaGroup (quadTail m (minusTailForm K b c)) hQ :=
    CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup hQ
  have hΩO : omegaGroup (quadTail m (minusTailForm K b c)) hQ ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)) :=
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le _ hQ
  have hidxO : (LeviBlock.orthResDer K b c m).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))) = 2 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.orthMinus_index_orthResDer_subgroupOf
      hK hm hirr
  have hrelO : (omegaGroup (quadTail m (minusTailForm K b c)) hQ).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))) = 2 :=
    CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup _ hQ
  have hmul := Subgroup.relIndex_mul_relIndex (LeviBlock.orthResDer K b c m)
    (omegaGroup (quadTail m (minusTailForm K b c)) hQ)
    (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))) hST hΩO
  rw [hidxO, hrelO] at hmul
  omega

theorem odd_card_omegaGroup_tail_zero {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) :
    Odd (Nat.card ↥(omegaGroup (quadTail 0 (minusTailForm K b c))
      (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)))) := by
  classical
  have hQ : (QuadraticMap.polarBilin (quadTail 0 (minusTailForm K b c))).Nondegenerate :=
    nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)
  have hO :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.orthMinus_card_orthogonalGroup_tail_zero
      (K := K) (b := b) (c := c) hirr
  have hrel := CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup
    (quadTail 0 (minusTailForm K b c)) hQ
  have hle := CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le
    (quadTail 0 (minusTailForm K b c)) hQ
  have hmul := Subgroup.relIndex_mul_card
    (omegaGroup (quadTail 0 (minusTailForm K b c)) hQ)
    (TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K b c)))
  rw [inf_eq_left.mpr hle, hrel, hO] at hmul
  have hcard : Nat.card ↥(omegaGroup (quadTail 0 (minusTailForm K b c)) hQ) =
      Nat.card K + 1 := by omega
  obtain ⟨f, hf, hK⟩ := card_eq_two_pow_of_charP_two (K := K)
  rw [hcard, hK]
  exact (Even.pow_of_ne_zero (show Even (2 : ℕ) from even_two) hf).add_odd odd_one

theorem odd_card_omegaGroup_tail_of_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    {m : ℕ} (hm : m = 0) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) :
    Odd (Nat.card ↥(omegaGroup (quadTail m (minusTailForm K b c))
      (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)))) := by
  subst hm
  exact odd_card_omegaGroup_tail_zero hirr

theorem hasLeviCensus_idxTwistedD (hZ : OddCenterRest) {X : Type} [Group X] [Finite X]
    {L J : Subgroup X} (hCP : CompParab L J) (h : IsLieOf IdxTwistedD (↥L ⧸ center ↥L)) :
    HasLeviCensus ↥J IsWBlock := by
  unfold IsLieOf at h
  obtain ⟨dI, hdI, ⟨eL⟩⟩ := h
  obtain ⟨K, hKf, hKfin, hKchar, b, c, r, s, d, ρ, hr, hirr, hd, hρ, hq⟩ :=
    LeviBlock.exists_orthCover_of_twistedD hZ hCP dI hdI eL
  classical
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    LeviBlock.finite_orthLinearEquiv
  obtain ⟨f, -, hK⟩ := card_eq_two_pow_of_charP_two (K := K)
  let β : ↥((J.subgroupOf L).comap ρ.toMonoidHom) →*
      ∀ j : Fin s ⊕ Unit, LeviBlock.orthLeviGroup K r d j :=
    (LeviBlock.orthLeviHom b c hd).comp (MulEquiv.subgroupCongr hρ).toMonoidHom
  have hrange : β.range = (LeviBlock.orthLeviHom b c hd).range := by
    dsimp only [β]
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulEquiv.subgroupCongr hρ).surjective, Subgroup.map_top]
  have hβ : IsPGroup 2 β.ker := by
    have hker_eq : β.ker = Subgroup.comap (MulEquiv.subgroupCongr hρ).toMonoidHom
        (LeviBlock.orthLeviHom b c hd).ker := rfl
    rw [hker_eq]
    exact IsPGroup.comap_of_injective (p := 2) (LeviBlock.isPGroup_ker_orthLeviHom hd)
      (MulEquiv.subgroupCongr hρ).toMonoidHom (MulEquiv.injective _)
  let T : ∀ j : Fin s ⊕ Unit, Subgroup (LeviBlock.orthLeviGroup K r d j) := fun j =>
    match j with
    | .inl _ => ⊤
    | .inr _ => omegaGroup (quadTail (r - d (Fin.last s)) (minusTailForm K b c))
        (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))
  have h2 : β.range ≤ Subgroup.pi Set.univ T := by
    intro y hy
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [Subgroup.mem_pi]
    intro j _
    rcases j with l | u
    · exact Subgroup.mem_top _
    · obtain rfl : u = () := rfl
      have happ : β z = LeviBlock.orthLeviHom b c hd ((MulEquiv.subgroupCongr hρ) z) := rfl
      rw [happ, LeviBlock.orthLeviHom_inr]
      exact orthResHom_mem_omegaGroup hd hr hirr _
  have hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ
      (LeviBlock.orthLeviBlock K r d b c) := by
    rw [hrange]
    exact LeviBlock.commutator_range_orthLeviHom_le hd
  by_cases hm0 : r - d (Fin.last s) = 0
  ·
    let S : ∀ j : Fin s ⊕ Unit, Subgroup (LeviBlock.orthLeviGroup K r d j) := fun j =>
      match j with
      | .inl l => LeviBlock.orthLeviBlock K r d b c (.inl l)
      | .inr _ => ⊥
    have hST : ∀ j, S j ≤ T j := by
      intro j
      rcases j with l | u
      · exact le_top
      · obtain rfl : u = () := rfl
        exact bot_le
    have hSle : ∀ j, S j ≤ LeviBlock.orthLeviBlock K r d b c j := by
      intro j
      rcases j with l | u
      · exact le_rfl
      · obtain rfl : u = () := rfl
        exact bot_le
    have hle : Subgroup.pi Set.univ S ≤ β.range := by
      have hmapi : Subgroup.pi Set.univ S ≤
          Subgroup.pi Set.univ (LeviBlock.orthLeviBlock K r d b c) := by
        intro x hx
        rw [Subgroup.mem_pi] at hx ⊢
        intro j hj
        exact hSle j (hx j hj)
      refine hmapi.trans ?_
      rw [hrange]
      exact LeviBlock.pi_orthLeviBlock_le_range hd hr
        (LeviBlock.commutator_orthogonalGroup_quadTail_minus hr hirr)
    have hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range := by
      refine not_two_dvd_relIndex_pi_of_finite (S := S) (T := T) hST hle h2 ?_
      intro j
      rcases j with l | u
      · change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
            GL (Fin (d l.succ - d l.castSucc)) K).range).relIndex ⊤
        rw [Subgroup.relIndex_top_right]
        exact not_two_dvd_index_range_toGL _
      · obtain rfl : u = () := rfl
        show ¬ 2 ∣ (⊥ : Subgroup (LeviBlock.orthLeviGroup K r d (.inr ()))).relIndex
          (omegaGroup (quadTail (r - d (Fin.last s)) (minusTailForm K b c))
            (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)))
        rw [Subgroup.relIndex_bot_left]
        exact (odd_card_omegaGroup_tail_of_eq_zero hm0 hirr).not_two_dvd_nat
    have hnorm_inl : ∀ l : Fin s, Subgroup.normalizer
        (S (.inl l) : Set (LeviBlock.orthLeviGroup K r d (.inl l))) = ⊤ := by
      intro l
      rw [Subgroup.normalizer_eq_top_iff]
      change (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
          GL (Fin (d l.succ - d l.castSucc)) K).range.Normal
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact MonoidHom.normal_ker _
    have hnorm_inr : Subgroup.normalizer
        (S (.inr ()) : Set (LeviBlock.orthLeviGroup K r d (.inr ()))) = ⊤ := by
      rw [Subgroup.normalizer_eq_top_iff]
      change (⊥ : Subgroup (LeviBlock.orthLeviGroup K r d (.inr ()))).Normal
      infer_instance
    have hn : β.range ≤ Subgroup.normalizer (Subgroup.pi Set.univ S :
        Set (∀ j, LeviBlock.orthLeviGroup K r d j)) := by
      refine le_normalizer_pi_of_forall fun g _ j => ?_
      rcases j with l | u
      · rw [hnorm_inl l]
        exact Subgroup.mem_top _
      · obtain rfl : u = () := rfl
        rw [hnorm_inr]
        exact Subgroup.mem_top _
    have hS : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j) := by
      intro j
      rcases j with l | u
      · change (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
              GL (Fin (d l.succ - d l.castSucc)) K).range = ⊥ ∨
          IsWBlock ↥(Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
              GL (Fin (d l.succ - d l.castSucc)) K).range
        rcases range_toGL_cases (K := K) (d l.succ - d l.castSucc) with
          hbot | ⟨-, -, hs⟩ | ⟨hq, hodd⟩
        · exact Or.inl hbot
        · exact Or.inr (Or.inr hs)
        · exact Or.inr (Or.inl ⟨hq, hodd⟩)
      · obtain rfl : u = () := rfl
        exact Or.inl rfl
    exact hasLeviCensus_of_mulEquiv_of_finite hCP.parab.1 ρ β hβ hle hn hi hS
  ·
    have hm1 : 1 ≤ r - d (Fin.last s) := by omega
    let S : ∀ j : Fin s ⊕ Unit, Subgroup (LeviBlock.orthLeviGroup K r d j) :=
      LeviBlock.orthLeviBlock K r d b c
    have hST : ∀ j, S j ≤ T j := by
      intro j
      rcases j with l | u
      · exact le_top
      · obtain rfl : u = () := rfl
        exact CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup _
    have hle : Subgroup.pi Set.univ S ≤ β.range := by
      rw [hrange]
      exact LeviBlock.pi_orthLeviBlock_le_range hd hr
        (LeviBlock.commutator_orthogonalGroup_quadTail_minus hr hirr)
    have hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range := by
      refine not_two_dvd_relIndex_pi_of_finite (S := S) (T := T) hST hle h2 ?_
      intro j
      rcases j with l | u
      · change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
            GL (Fin (d l.succ - d l.castSucc)) K).range).relIndex ⊤
        rw [Subgroup.relIndex_top_right]
        exact not_two_dvd_index_range_toGL _
      · obtain rfl : u = () := rfl
        show ¬ 2 ∣ (LeviBlock.orthResDer K b c (r - d (Fin.last s))).relIndex
          (omegaGroup (quadTail (r - d (Fin.last s)) (minusTailForm K b c))
            (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)))
        rw [relIndex_orthResDer_omegaGroup hK hm1 hirr]
        norm_num
    have hn : β.range ≤ Subgroup.normalizer (Subgroup.pi Set.univ S :
        Set (∀ j, LeviBlock.orthLeviGroup K r d j)) :=
      le_normalizer_of_commutator_le hle hcomm
    have hS : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j) := by
      intro j
      rcases j with l | u
      · change (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
              GL (Fin (d l.succ - d l.castSucc)) K).range = ⊥ ∨
          IsWBlock ↥(Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
              GL (Fin (d l.succ - d l.castSucc)) K).range
        rcases range_toGL_cases (K := K) (d l.succ - d l.castSucc) with
          hbot | ⟨-, -, hs⟩ | ⟨hq, hodd⟩
        · exact Or.inl hbot
        · exact Or.inr (Or.inr hs)
        · exact Or.inr (Or.inl ⟨hq, hodd⟩)
      · obtain rfl : u = () := rfl
        show LeviBlock.orthResDer K b c (r - d (Fin.last s)) = ⊥ ∨
          IsWBlock ↥(LeviBlock.orthResDer K b c (r - d (Fin.last s)))
        obtain ⟨hsimple, hna, -⟩ := LeviBlock.orthResDer_facts (K := K) (b := b) (c := c)
          (f := f) (m := r - d (Fin.last s)) hK hm1 hirr
        haveI := hsimple
        obtain ⟨hq, hcenter⟩ := LeviBlock.orthMinus_isQuasisimple_of_simple hna
        exact Or.inr (Or.inl ⟨hq, by rw [hcenter, Subgroup.card_bot]; exact odd_one⟩)
    exact hasLeviCensus_of_mulEquiv_of_finite hCP.parab.1 ρ β hβ hle hn hi hS

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
