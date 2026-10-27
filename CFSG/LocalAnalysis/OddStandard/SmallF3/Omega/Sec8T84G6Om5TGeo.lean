module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private noncomputable def sec8t84g6t_phi {t : OGroup Q} (htt : t * t = 1) :
    OGroup (Q.restrict (commSp t)) →* ProjOrth Q :=
  (toProj Q).comp ((blockHom htt).comp (MonoidHom.inr _ _))

private theorem sec8t84g6t_phi_apply {t : OGroup Q} (htt : t * t = 1)
    (b : OGroup (Q.restrict (commSp t))) :
    sec8t84g6t_phi htt b = toProj Q (blockHom htt (1, b)) := rfl

private theorem sec8t84g6t_phi_injective {t : OGroup Q} (htt : t * t = 1)
    (hW : 0 < Module.finrank (ZMod 3) (fixSp t)) : Function.Injective (sec8t84g6t_phi htt) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hmem : blockHom htt (1, b) ∈ piGroup Q := (QuotientGroup.eq_one_iff _).mp hb
  rcases mem_piGroup_iff.mp hmem with h | h
  · have h' : ((1 : OGroup (Q.restrict (fixSp t))), b) = 1 :=
      blockHom_injective htt (h.trans (map_one (blockHom htt)).symm)
    exact (Prod.mk_eq_one.mp h').2
  · exfalso
    have h' : ((1 : OGroup (Q.restrict (fixSp t))), b) =
        (piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) :=
      blockHom_injective htt (h.trans (blockHom_piOrth_piOrth htt).symm)
    exact piOrth_ne_one hW (Prod.ext_iff.mp h').1.symm

private theorem sec8t84g6t_phi_mem {t : OGroup Q} (hQ : Q.Nondegenerate) (htt : t * t = 1)
    (b : OGroup (Q.restrict (commSp t))) :
    sec8t84g6t_phi htt b ∈ Subgroup.centralizer ({toProj Q t} : Set (ProjOrth Q)) := by
  have h1 : blockHom htt (1, b) ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) := by
    rw [← range_blockHom hQ htt]
    exact ⟨_, rfl⟩
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp h1
  rw [Subgroup.mem_centralizer_singleton_iff, sec8t84g6t_phi_apply, ← map_mul, ← map_mul, h2]

private noncomputable def sec8t84g6t_phiC {t : OGroup Q} (hQ : Q.Nondegenerate)
    (htt : t * t = 1) :
    OGroup (Q.restrict (commSp t)) →* Subgroup.centralizer ({toProj Q t} : Set (ProjOrth Q)) :=
  (sec8t84g6t_phi htt).codRestrict _ (sec8t84g6t_phi_mem hQ htt)

private theorem sec8t84g6t_phiC_bijective (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {t : OGroup Q} (htt : t * t = 1)
    (hty : invType t = (4, -1)) (hy : HasType (toProj Q t) 4 (-1)) :
    Function.Bijective (sec8t84g6t_phiC hQ htt) := by
  have hr : invDim t = 4 := congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp t)) = -1 := congrArg Prod.snd hty
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hU : Module.finrank (ZMod 3) (commSp t) = 4 := hr
  have hinj : Function.Injective (sec8t84g6t_phiC hQ htt) := by
    intro a b hab
    exact sec8t84g6t_phi_injective htt (by omega) (congrArg Subtype.val hab)
  refine hinj.bijective_of_nat_card_le ?_
  rw [natCard_centralizer_hasType_four_minus hQ hdim hy,
    natCard_oGroup_four_minus (nondegenerate_restrict_commSp hQ htt) hU hs]

theorem sec8t84g6t_outer (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5)
    {y : ProjOrth Q} (hy : HasType y 4 (-1)) :
    ∃ ε : ↥(Subgroup.centralizer ({y} : Set (ProjOrth Q))) →* (ZMod 3)ˣ,
      ∃ (u : ProjOrth Q) (hu : u ∈ Subgroup.centralizer ({y} : Set (ProjOrth Q))),
        u * u = 1 ∧ u ∈ omegaProj hQ ∧ ε ⟨u, hu⟩ = -1 := by
  have hy' := hy
  obtain ⟨-, t, htt, hty, rfl⟩ := hy
  have hr : invDim t = 4 := congrArg Prod.fst hty
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hU : Module.finrank (ZMod 3) (commSp t) = 4 := hr
  have hRU : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
  have hbij := sec8t84g6t_phiC_bijective hQ hdim htt hty hy'
  let e := MulEquiv.ofBijective (sec8t84g6t_phiC hQ htt) hbij
  let ε : ↥(Subgroup.centralizer ({toProj Q t} : Set (ProjOrth Q))) →* (ZMod 3)ˣ :=
    (QuadraticMap.orthogonalDet (Q.restrict (commSp t))).comp e.symm.toMonoidHom
  have hε : ∀ b : OGroup (Q.restrict (commSp t)),
      ε (sec8t84g6t_phiC hQ htt b) = QuadraticMap.orthogonalDet (Q.restrict (commSp t)) b := by
    intro b
    show QuadraticMap.orthogonalDet (Q.restrict (commSp t))
      (e.symm (sec8t84g6t_phiC hQ htt b)) = _
    rw [show sec8t84g6t_phiC hQ htt b = e b from rfl, MulEquiv.symm_apply_apply]
  obtain ⟨b₀, hb₀, hb₀ty⟩ := (exists_involution_of_type hRU 1 1).mpr
    ⟨by omega, fun h => by omega, fun h => by omega⟩
  have hb₀d : QuadraticMap.orthogonalDet (Q.restrict (commSp t)) b₀ = -1 := by
    rw [orthogonalDet_involution hb₀, show invDim b₀ = 1 from congrArg Prod.fst hb₀ty, pow_one]
  have hπU : QuadraticMap.orthogonalDet (Q.restrict (commSp t))
      (piOrth (Q.restrict (commSp t))) = 1 := by
    rw [orthogonalDet_piOrth, hU]
    decide
  have hd₁sq : sec8t84g6t_phi htt b₀ * sec8t84g6t_phi htt b₀ = 1 := by
    rw [← map_mul, hb₀, map_one]
  have hd₂sq : sec8t84g6t_phi htt (piOrth (Q.restrict (commSp t)) * b₀) *
      sec8t84g6t_phi htt (piOrth (Q.restrict (commSp t)) * b₀) = 1 := by
    rw [← map_mul]
    have hc : b₀ * piOrth (Q.restrict (commSp t)) = piOrth (Q.restrict (commSp t)) * b₀ :=
      Subgroup.mem_center_iff.mp piOrth_mem_center b₀
    have : piOrth (Q.restrict (commSp t)) * b₀ * (piOrth (Q.restrict (commSp t)) * b₀) = 1 := by
      calc piOrth (Q.restrict (commSp t)) * b₀ * (piOrth (Q.restrict (commSp t)) * b₀)
          = piOrth (Q.restrict (commSp t)) * (b₀ * piOrth (Q.restrict (commSp t))) * b₀ := by
            group
        _ = piOrth (Q.restrict (commSp t)) * (piOrth (Q.restrict (commSp t)) * b₀) * b₀ := by
            rw [hc]
        _ = (piOrth (Q.restrict (commSp t)) * piOrth (Q.restrict (commSp t))) *
            (b₀ * b₀) := by group
        _ = 1 := by rw [piOrth_mul_self, hb₀, one_mul]
    rw [this, map_one]
  have hd₂ : sec8t84g6t_phi htt (piOrth (Q.restrict (commSp t)) * b₀) =
      toProj Q t * sec8t84g6t_phi htt b₀ := by
    rw [map_mul, sec8t84g6t_phi_apply htt (piOrth (Q.restrict (commSp t))),
      blockHom_one_piOrth htt]
  have hindex : (omegaProj hQ).index = 2 :=
    index_omegaProj_of_odd hQ (by rw [hdim]; norm_num) (by rw [hdim]; decide)
  have hyX : toProj Q t ∉ omegaProj hQ := by
    intro h
    rcases (hasType_mem_omegaProj_iff_five hQ hdim hy' (Or.inr rfl)).mp h with h | h
    · exact absurd h.2 (by decide)
    · exact absurd h.1 (by decide)
  by_cases hd : sec8t84g6t_phi htt b₀ ∈ omegaProj hQ
  · refine ⟨ε, sec8t84g6t_phi htt b₀, sec8t84g6t_phi_mem hQ htt b₀, hd₁sq, hd, ?_⟩
    rw [show (⟨sec8t84g6t_phi htt b₀, sec8t84g6t_phi_mem hQ htt b₀⟩ : ↥(Subgroup.centralizer
      ({toProj Q t} : Set (ProjOrth Q)))) = sec8t84g6t_phiC hQ htt b₀ from rfl, hε, hb₀d]
  · have hd₂X : sec8t84g6t_phi htt (piOrth (Q.restrict (commSp t)) * b₀) ∈ omegaProj hQ := by
      rw [hd₂]
      exact (Subgroup.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hyX hd)
    refine ⟨ε, sec8t84g6t_phi htt (piOrth (Q.restrict (commSp t)) * b₀),
      sec8t84g6t_phi_mem hQ htt _, hd₂sq, hd₂X, ?_⟩
    rw [show (⟨sec8t84g6t_phi htt (piOrth (Q.restrict (commSp t)) * b₀),
      sec8t84g6t_phi_mem hQ htt _⟩ : ↥(Subgroup.centralizer
      ({toProj Q t} : Set (ProjOrth Q)))) =
      sec8t84g6t_phiC hQ htt (piOrth (Q.restrict (commSp t)) * b₀) from rfl, hε, map_mul, hπU,
      hb₀d, one_mul]

end CFSG.OddStandard.SmallF3.Omega
