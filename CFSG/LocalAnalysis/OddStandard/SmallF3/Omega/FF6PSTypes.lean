module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSTypesAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_simHasType_ne_one {x : ProjSim Q} {r : ℕ} {α : ℤˣ} (h : SimHasType x r α) :
    x ≠ 1 := by
  rintro hx
  obtain ⟨y, hyx, hy1, -⟩ := h
  exact hy1 (projOrthToProjSim_injective (by rw [hyx, hx, map_one]))

theorem ff_simHasType_rank (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {x : ProjSim Q} {r r' : ℕ} {α β : ℤˣ} (h : SimHasType x r α) (h' : SimHasType x r' β) :
    r' = r ∨ r' + r = 6 := by
  obtain ⟨y, hyx, hy1, t, htt, hty, htoy⟩ := h
  obtain ⟨y', hy'x, hy'1, t', ht't', ht'y', ht'oy'⟩ := h'
  have hyy : y' = y := projOrthToProjSim_injective (by rw [hy'x, hyx])
  have hto : toProj Q t' = toProj Q t := by rw [ht'oy', hyy, htoy]
  have hrt : invDim t = r := by simpa [invType] using congrArg Prod.fst hty
  have hrt' : invDim t' = r' := by simpa [invType] using congrArg Prod.fst ht'y'
  rcases ffOutFF6PSTypes_toProj_eq_or_eq_piOrth hto with h1 | h1
  · left
    rw [h1] at hrt'
    omega
  · right
    have hpi : invDim t' = 6 - invDim t := by
      rw [h1]
      have h := congrArg Prod.fst (invType_piOrth_mul hQ htt)
      simp only [invType] at h
      simpa only [hdim] using h
    have hle : invDim t ≤ 6 := by
      have hle := invDim_le t
      rwa [hdim] at hle
    omega

theorem ff_simHasType_one_unique (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {x : ProjSim Q} {α β : ℤˣ} (h : SimHasType x 1 α) (h' : SimHasType x 1 β) : α = β := by
  obtain ⟨y, hyx, hy1, t, htt, hty, htoy⟩ := h
  obtain ⟨y', hy'x, hy'1, t', ht't', ht'y', ht'oy'⟩ := h'
  have hyy : y' = y := projOrthToProjSim_injective (by rw [hy'x, hyx])
  have hto : toProj Q t' = toProj Q t := by rw [ht'oy', hyy, htoy]
  rcases ffOutFF6PSTypes_toProj_eq_or_eq_piOrth hto with h1 | h1
  · rw [h1] at ht'y'
    exact congrArg Prod.snd (hty.symm.trans ht'y')
  · exfalso
    have hrt : invDim t = 1 := by simpa [invType] using congrArg Prod.fst hty
    have hrt' : invDim t' = 1 := by simpa [invType] using congrArg Prod.fst ht'y'
    have hpi : invDim t' = 6 - invDim t := by
      rw [h1]
      have h := congrArg Prod.fst (invType_piOrth_mul hQ htt)
      simp only [invType] at h
      simpa only [hdim] using h
    rw [hrt', hrt] at hpi
    norm_num at hpi

theorem ff_simHasType_conj_outer (hQ : Q.Nondegenerate) {ξ x : ProjSim Q} {r : ℕ} {α : ℤˣ}
    (hξ : ¬ SimInGStar ξ) (hr : Odd r) (hx : SimHasType x r α) :
    SimHasType (ξ * x * ξ⁻¹) r (-α) := by
  obtain ⟨y, hyx, hy1, t, htt, hty, hty'⟩ := hx
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective ξ
  obtain ⟨c, hc⟩ := γ.2
  have hγt : simAct Q γ t = simConj hc t := Subtype.ext (by rw [coe_simAct, coe_simConj])
  obtain ⟨hsq, htype⟩ := invType_simConj hQ hc htt
  simp only [invType, Prod.mk.injEq] at hty
  have hx_eq : QuotientGroup.mk (orthToSim Q t) = x := by
    rw [← projOrthToProjSim_toProj t, hty', hyx]
  have hc1 : c = -1 := by
    rcases aux_unit_eq_one_or_neg_one c with h1 | h1
    · exfalso
      have hrpos : 0 < r := by
        rcases hr with ⟨k, hk⟩
        omega
      have h0 : 0 < Module.finrank (ZMod 3) V :=
        lt_of_lt_of_le hrpos (by rw [← hty.1]; exact invDim_le t)
      have hsub : γ ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q) :=
        (aux_mem_subgroupOf_iff hQ h0 hc).mpr h1
      let g : OGroup Q := ⟨(γ : V ≃ₗ[ZMod 3] V), Subgroup.mem_subgroupOf.mp hsub⟩
      apply hξ
      refine ⟨toProj Q g, ?_⟩
      rw [projOrthToProjSim_toProj, show orthToSim Q g = γ from Subtype.ext rfl]
    · exact h1
  have hr' : Odd (invDim t) := by rw [hty.1]; exact hr
  refine ⟨toProj Q (simConj hc t), ?_, ?_⟩
  · calc projOrthToProjSim Q (toProj Q (simConj hc t))
        = projOrthToProjSim Q (toProj Q (simAct Q γ t)) := by rw [hγt]
      _ = QuotientGroup.mk (orthToSim Q (simAct Q γ t)) := projOrthToProjSim_toProj _
      _ = QuotientGroup.mk (γ * orthToSim Q t * γ⁻¹) := by rw [sec9u_orthToSim_simAct]
      _ = QuotientGroup.mk γ * QuotientGroup.mk (orthToSim Q t) * (QuotientGroup.mk γ)⁻¹ := by
            simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = QuotientGroup.mk γ * x * (QuotientGroup.mk γ)⁻¹ := by rw [hx_eq]
  · refine ⟨?_, simConj hc t, hsq, ?_, rfl⟩
    · intro h1
      have hkey : toProj Q (simConj hc t) = projSimAct Q (QuotientGroup.mk γ) y := by
        rw [← hγt, ← projSimActO_mk, toProj_projSimActO, hty']
      have hconj : projSimAct Q (QuotientGroup.mk γ) y = 1 := by rw [← hkey]; exact h1
      exact hy1 ((projSimAct Q (QuotientGroup.mk γ)).map_eq_one_iff.mp hconj)
    · rw [htype]
      refine Prod.ext hty.1 ?_
      rw [hc1, aux_toSign_neg_one, hr'.neg_one_pow, hty.2, neg_one_mul]

theorem ff_simHasType_odd_not_simInOmegaStar (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) {x : ProjSim Q} {r : ℕ} {α : ℤˣ} (hr : Odd r)
    (hx : SimHasType x r α) : ¬ SimInOmegaStar hQ x := by
  rintro ⟨y, hy, hyx⟩
  obtain ⟨y', hy'x, hy'1, t, htt, hty, htoy⟩ := hx
  have hyy : y' = y := projOrthToProjSim_injective (by rw [hy'x, hyx])
  have hyproj : toProj Q t = y := by rw [htoy, hyy]
  have hrt : invDim t = r := by simpa [invType] using congrArg Prod.fst hty
  have hodd_t : Odd (invDim t) := by rw [hrt]; exact hr
  obtain ⟨g, hg, hgy⟩ := (mem_omegaProj_iff hQ).mp hy
  have hgt : toProj Q g = toProj Q t := by rw [hgy, hyproj]
  rcases ffOutFF6PSTypes_toProj_eq_or_eq_piOrth hgt with h1 | h1
  · have htΩ : t ∈ omegaGroup hQ := h1 ▸ hg
    exact (Nat.not_odd_iff_even.mpr ((involution_mem_omegaGroup_iff hQ htt).mp htΩ).1) hodd_t
  · have hptΩ : piOrth Q * t ∈ omegaGroup hQ := h1 ▸ hg
    have hptt : (piOrth Q * t) * (piOrth Q * t) = 1 := piOrth_mul_mul_self htt
    have hev : Even (invDim (piOrth Q * t)) :=
      ((involution_mem_omegaGroup_iff hQ hptt).mp hptΩ).1
    have hfin : invDim (piOrth Q * t) = 6 - invDim t := by
      have h := congrArg Prod.fst (invType_piOrth_mul hQ htt)
      simp only [invType] at h
      simpa only [hdim] using h
    have hodd' : Odd (invDim (piOrth Q * t)) := by
      rw [hfin]
      exact Nat.Even.sub_odd (by rw [← hdim]; exact invDim_le t) (by decide) hodd_t
    exact (Nat.not_odd_iff_even.mpr hev) hodd'

theorem ff6p_simHasType_signChange (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {K : Finset (Option (Fin 5))} (hK0 : K ≠ ∅) (hKu : K ≠ Finset.univ) :
    SimHasType (projOrthToProjSim Q (toProj Q (fr.signChange K))) K.card
      ((if none ∈ K then (-1 : ℤˣ) else 1) * (-1) ^ (K.card / 2)) := by
  refine simHasType_projOrthToProjSim ?_
  simp only [HasType]
  refine ⟨?_, fr.signChange K, fr.signChange_mul_self K, PFrame.invType_signChange hQ fr K, rfl⟩
  rintro h1
  have h1' : toProj Q (fr.signChange K) =
      toProj Q (fr.signChange (∅ : Finset (Option (Fin 5)))) := by
    rw [fr.signChange_empty, map_one]
    exact h1
  rcases (ff6p_toProj_signChange_eq_iff fr K ∅).mp h1' with h | h
  · exact hK0 h
  · apply hKu
    rw [h]
    simp

theorem ffTs_hasType (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    SimHasType (ffTs fr) 1 (-1) := by
  have hne0 : ({none} : Finset (Option (Fin 5))) ≠ ∅ := by decide
  have hneu : ({none} : Finset (Option (Fin 5))) ≠ Finset.univ := by decide
  have h := ff6p_simHasType_signChange hQ fr
    (K := ({none} : Finset (Option (Fin 5)))) hne0 hneu
  have hcard : ({none} : Finset (Option (Fin 5))).card = 1 := by simp
  have hif : (if none ∈ ({none} : Finset (Option (Fin 5))) then (-1 : ℤˣ) else 1) = -1 := by
    simp
  rw [hcard] at h
  rw [hif] at h
  have hpow : (-1 : ℤˣ) ^ (1 / 2) = 1 := by decide
  rw [hpow, mul_one] at h
  rw [ffTs]
  exact h

theorem ffTs_not_simInOmegaStar (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (fr : PFrame Q (Option (Fin 5)) ffC) : ¬ SimInOmegaStar hQ (ffTs fr) :=
  ff_simHasType_odd_not_simInOmegaStar hQ hdim (show Odd 1 from ⟨0, rfl⟩) (ffTs_hasType hQ fr)

theorem ffZ0s_hasType (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    SimHasType (ffOmegaToSim hQ (ffZ0s hQ fr)) 4 1 := by
  have hne0 : ffOpt ({0, 1, 2, 3} : Finset (Fin 5)) ≠ ∅ := by decide
  have hneu : ffOpt ({0, 1, 2, 3} : Finset (Fin 5)) ≠ Finset.univ := by decide
  have h := ff6p_simHasType_signChange hQ fr
    (K := ffOpt ({0, 1, 2, 3} : Finset (Fin 5))) hne0 hneu
  have hcard : (ffOpt ({0, 1, 2, 3} : Finset (Fin 5))).card = 4 := by
    rw [ffOpt_card]
    decide
  have hif : (if none ∈ ffOpt ({0, 1, 2, 3} : Finset (Fin 5)) then (-1 : ℤˣ) else 1) = 1 :=
    if_neg (none_notMem_ffOpt ({0, 1, 2, 3} : Finset (Fin 5)))
  rw [hcard] at h
  rw [hif] at h
  have hpow : (-1 : ℤˣ) ^ (4 / 2) = 1 := by decide
  rw [hpow, mul_one] at h
  rw [ffOutFF6PSTypes_ffOmegaToSim_ffZ0s]
  exact h

theorem ff6p_tsz0_hasType (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    SimHasType (ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr)) 1 1 := by
  have hne0 : ({some 4} : Finset (Option (Fin 5))) ≠ ∅ := by decide
  have hneu : ({some 4} : Finset (Option (Fin 5))) ≠ Finset.univ := by decide
  have h := ff6p_simHasType_signChange hQ fr
    (K := ({some 4} : Finset (Option (Fin 5)))) hne0 hneu
  have hcard : ({some 4} : Finset (Option (Fin 5))).card = 1 := by simp
  have hif : (if none ∈ ({some 4} : Finset (Option (Fin 5))) then (-1 : ℤˣ) else 1) = 1 := by
    simp
  rw [hcard] at h
  rw [hif] at h
  have hpow : (-1 : ℤˣ) ^ (1 / 2) = 1 := by decide
  rw [hpow, mul_one] at h
  rw [ffOutFF6PSTypes_tsz0_eq]
  exact h

theorem ff6p_i1_cases (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q} {α : ℤˣ} (hx : SimHasType x 1 α) :
    (∃ n : ↥(omegaProj hQ),
        x = ffOmegaToSim hQ n * ffTs fr * (ffOmegaToSim hQ n)⁻¹) ∨
      ∃ n : ↥(omegaProj hQ), x = ffOmegaToSim hQ n *
        (ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr)) * (ffOmegaToSim hQ n)⁻¹ := by
  rcases Int.units_eq_one_or α with hα | hα
  · right
    rw [hα] at hx
    exact ffOutFF6PSTypes_i1_conj hQ hdim fr (z := ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr))
      (fr.signChange_mul_self {some 4}) (ffOutFF6PSTypes_invType_some4 hQ fr)
      (ffOutFF6PSTypes_tsz0_eq hQ fr) rfl hx
  · left
    rw [hα] at hx
    exact ffOutFF6PSTypes_i1_conj hQ hdim fr (z := ffTs fr)
      (fr.signChange_mul_self {none}) (ffOutFF6PSTypes_invType_tnone hQ fr) rfl rfl hx

theorem ff6p_exists_conj_ts (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q} {α : ℤˣ} (hx : SimHasType x 1 α) :
    ∃ y : ProjSim Q, x = y * ffTs fr * y⁻¹ := by
  rcases ff6p_i1_cases hQ hdim fr hx with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact ⟨ffOmegaToSim hQ n, hn⟩
  · obtain ⟨ξ, hξ⟩ := ff_exists_outer hQ hdim
    have htype : SimHasType (ξ * (ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr)) * ξ⁻¹) 1 (-1) :=
      ff_simHasType_conj_outer hQ hξ (show Odd 1 from ⟨0, rfl⟩) (ff6p_tsz0_hasType hQ fr)
    obtain ⟨m, hm⟩ := ffOutFF6PSTypes_i1_conj hQ hdim fr (z := ffTs fr)
      (fr.signChange_mul_self {none}) (ffOutFF6PSTypes_invType_tnone hQ fr) rfl rfl htype
    refine ⟨ffOmegaToSim hQ n * ξ⁻¹ * ffOmegaToSim hQ m, ?_⟩
    have hS : ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) =
        ξ⁻¹ * (ffOmegaToSim hQ m * ffTs fr * (ffOmegaToSim hQ m)⁻¹) * ξ := by
      rw [← hm]
      group
    rw [hn, hS]
    group

end CFSG.OddStandard.SmallF3.Omega
