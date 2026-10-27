module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSNorm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6p_map_normalE16 (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {y : ProjSim Q}
    (hy : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom = ffP1p hQ fr)
    {U : Subgroup ↥(omegaProj hQ)} (hU : IsNormalE16In (ffP1p hQ fr) U) :
    IsNormalE16In (ffP1p hQ fr) (U.map (ffSimOmegaAct hQ h2 y).toMonoidHom) := by
  have hle : U.map (ffSimOmegaAct hQ h2 y).toMonoidHom ≤ ffP1p hQ fr := by
    rw [← hy]
    exact Subgroup.map_mono hU.1
  refine ⟨hle, isElemAb2_map_mulEquiv (ffSimOmegaAct hQ h2 y) hU.2.1, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro v p hv hp
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
  have hp' : p ∈ (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
    rwa [hy]
  obtain ⟨p', hpP, rfl⟩ := Subgroup.mem_map.mp hp'
  exact Subgroup.mem_map.mpr ⟨p' * u * p'⁻¹,
    (Subgroup.normal_subgroupOf_iff hU.1).mp hU.2.2 u p' hu hpP,
    by simp only [map_mul, map_inv]⟩

theorem ff6p_exists_y0 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    ∃ y0 : ProjSim Q, ¬ SimInGStar y0 ∧
      (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y0).toMonoidHom = ffP1p hQ fr := by
  haveI : Finite (↥(omegaProj hQ)) := Nat.finite_of_card_ne_zero
    (by rw [ff_natCard_omegaProj_six_plus hQ hdim hsgn]; norm_num)
  obtain ⟨ξ, hξ⟩ := ff_exists_outer hQ hdim
  let α : MulAut ↥(omegaProj hQ) := ffSimOmegaAct hQ h2 ξ
  let U₁ : Subgroup ↥(omegaProj hQ) := (ffP1p hQ fr).map α.toMonoidHom
  have hU₁p : IsPGroup 2 U₁ := (ffP1p_sylow hQ hdim hsgn fr).2.1.map α.toMonoidHom
  obtain ⟨U₁syl, hU₁syl, hU₁le⟩ := exists_isSylow2Of_ge hU₁p (le_top : U₁ ≤ ⊤)
  obtain ⟨a, -, hconj⟩ := IsSylow2Of.exists_conj_mem (ffP1p_sylow hQ hdim hsgn fr) hU₁syl
  have hcardU₁ : Nat.card ↥U₁ = Nat.card ↥(ffP1p hQ fr) := by
    dsimp only [U₁]
    exact Nat.card_congr (((ffP1p hQ fr).equivMapOfInjective α.toMonoidHom
      α.injective).toEquiv.symm)
  have hcardmap : Nat.card ↥(U₁.map (MulAut.conj a⁻¹).toMonoidHom) = Nat.card ↥U₁ :=
    Nat.card_congr ((U₁.equivMapOfInjective (MulAut.conj a⁻¹).toMonoidHom
      (MulAut.conj a⁻¹).injective).toEquiv.symm)
  have hU₁map : U₁.map (MulAut.conj a⁻¹).toMonoidHom = ffP1p hQ fr := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      have h1 := (hconj u).mp (hU₁le hu)
      have hc : (MulAut.conj a⁻¹).toMonoidHom u = a⁻¹ * u * a := by
        change MulAut.conj a⁻¹ u = a⁻¹ * u * a
        rw [MulAut.conj_apply]
        group
      rwa [hc]
    · rw [hcardmap, hcardU₁]
  dsimp only [U₁] at hU₁map
  let y0 : ProjSim Q := projOrthToProjSim Q (↑(a⁻¹) : ProjOrth Q) * ξ
  have hy0 : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y0).toMonoidHom = ffP1p hQ fr := by
    have hcomp : ((MulAut.conj a⁻¹).toMonoidHom.comp α.toMonoidHom) =
        (ffSimOmegaAct hQ h2 y0).toMonoidHom := by
      have hy : ffSimOmegaAct hQ h2 y0 = MulAut.conj a⁻¹ * α := by
        rw [show y0 = projOrthToProjSim Q (↑(a⁻¹) : ProjOrth Q) * ξ from rfl, map_mul,
          ffSimOmegaAct_projOrthToProjSim, MulAut.conjNormal_val]
      rw [hy]
      ext x
      rfl
    rw [← hcomp, ← Subgroup.map_map]
    exact hU₁map
  refine ⟨y0, ?_, hy0⟩
  intro hy0G
  obtain ⟨y', hy'⟩ := hy0G
  refine hξ ⟨(↑a : ProjOrth Q) * y', ?_⟩
  have hxi : projOrthToProjSim Q (↑a : ProjOrth Q) * y0 = ξ := by
    rw [show y0 = projOrthToProjSim Q (↑(a⁻¹) : ProjOrth Q) * ξ from rfl]
    rw [← mul_assoc, ← map_mul]
    simp
  rw [map_mul, hy', hxi]

theorem ff6p_B2_ne (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {y : ProjSim Q} (hy : ¬ SimInGStar y) :
    (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom ≠ ffB1p hQ fr := by
  intro h
  exact hy (ff6p_star_normalizes_simInGStar hQ h2 fr h)

theorem ff6p_normalE16_cases (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {y : ProjSim Q} (hyG : ¬ SimInGStar y)
    (hy : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom = ffP1p hQ fr)
    {U : Subgroup ↥(omegaProj hQ)} (hU : IsNormalE16In (ffP1p hQ fr) U) :
    U = ffB1p hQ fr ∨ U = (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hB₂ : IsNormalE16In (ffP1p hQ fr)
      ((ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom) :=
    ff6p_map_normalE16 hQ h2 fr hy (ffB1p_normalE16 hQ hπ fr)
  by_cases hUB : U = ffB1p hQ fr
  · exact Or.inl hUB
  · exact Or.inr (ffP1p_E16_unique hQ hπ fr hU hB₂ hUB (ff6p_B2_ne hQ h2 fr hyG))

theorem ff6p_outer_swap (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {y : ProjSim Q} (hyG : ¬ SimInGStar y)
    (hy : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom = ffP1p hQ fr) :
    ((ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom).map
      (ffSimOmegaAct hQ h2 y).toMonoidHom = ffB1p hQ fr := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hB₂ : IsNormalE16In (ffP1p hQ fr)
      ((ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom) :=
    ff6p_map_normalE16 hQ h2 fr hy (ffB1p_normalE16 hQ hπ fr)
  have hB₃ : IsNormalE16In (ffP1p hQ fr)
      (((ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom).map
        (ffSimOmegaAct hQ h2 y).toMonoidHom) :=
    ff6p_map_normalE16 hQ h2 fr hy hB₂
  rcases ff6p_normalE16_cases hQ hdim hsgn h2 fr hyG hy hB₃ with h | h
  · exact h
  · exact absurd (Subgroup.map_injective (f := (ffSimOmegaAct hQ h2 y).toMonoidHom)
      (ffSimOmegaAct hQ h2 y).injective h) (ff6p_B2_ne hQ h2 fr hyG)

theorem ff6p_inG_normalizes_B1p (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q} (hxG : SimInGStar x)
    (hx : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffP1p hQ fr) :
    (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1p hQ fr := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  obtain ⟨y0, hy0G, hy0⟩ := ff6p_exists_y0 hQ hdim hsgn h2 fr
  have hB' : IsNormalE16In (ffP1p hQ fr)
      ((ffB1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom) :=
    ff6p_map_normalE16 hQ h2 fr hx (ffB1p_normalE16 hQ hπ fr)
  rcases ff6p_normalE16_cases hQ hdim hsgn h2 fr hy0G hy0 hB' with h | h
  · exact h
  · exfalso
    let z : ProjSim Q := y0⁻¹ * x
    have hsymm : (((ffSimOmegaAct hQ h2 y0))⁻¹).toMonoidHom.comp
        (ffSimOmegaAct hQ h2 y0).toMonoidHom = MonoidHom.id _ := by
      rw [MulAut.inv_def]
      ext w
      simp
    have hz : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 z).toMonoidHom = ffB1p hQ fr := by
      have hcz : ffSimOmegaAct hQ h2 z =
          (ffSimOmegaAct hQ h2 y0)⁻¹ * ffSimOmegaAct hQ h2 x := by
        rw [show z = y0⁻¹ * x from rfl, map_mul, map_inv]
      have hcomp : (((ffSimOmegaAct hQ h2 y0))⁻¹).toMonoidHom.comp
          (ffSimOmegaAct hQ h2 x).toMonoidHom = (ffSimOmegaAct hQ h2 z).toMonoidHom := by
        rw [hcz]
        ext w
        rfl
      calc (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 z).toMonoidHom
          = (ffB1p hQ fr).map ((((ffSimOmegaAct hQ h2 y0))⁻¹).toMonoidHom.comp
              (ffSimOmegaAct hQ h2 x).toMonoidHom) := by rw [← hcomp]
        _ = ((ffB1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom).map
              ((ffSimOmegaAct hQ h2 y0))⁻¹.toMonoidHom := by rw [Subgroup.map_map]
        _ = ((ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y0).toMonoidHom).map
              ((ffSimOmegaAct hQ h2 y0))⁻¹.toMonoidHom := by rw [h]
        _ = ffB1p hQ fr := by rw [Subgroup.map_map, hsymm, Subgroup.map_id]
    have hzG : SimInGStar z := ff6p_star_normalizes_simInGStar hQ h2 fr hz
    obtain ⟨x', hx'⟩ := hxG
    obtain ⟨z', hz'⟩ := hzG
    refine hy0G ⟨x' * z'⁻¹, ?_⟩
    have hzx : x * z⁻¹ = y0 := by
      dsimp only [z]
      group
    rw [map_mul, map_inv, hx', hz', hzx]

end CFSG.OddStandard.SmallF3.Omega
