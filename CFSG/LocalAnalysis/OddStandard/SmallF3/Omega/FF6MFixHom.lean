module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def ff6mFixHom (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {t : OGroup Q} (htt : t * t = 1)
    (hnc : ¬ IsConj (piOrth Q * t) t) :
    ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))) →*
      ↥(ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t))) :=
  ((omegaToProj hQ).comp (Subgroup.inclusion inf_le_left)).codRestrict _ (fun g =>
    (ff6m_mem_ffFix_iff_of_not_conj hQ hdim hsgn htt hnc _).mpr ⟨g.1, g.2, rfl⟩)

theorem ff6mFixHom_coe (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {t : OGroup Q} (htt : t * t = 1) (hnc : ¬ IsConj (piOrth Q * t) t)
    (g : ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)))) :
    (((ff6mFixHom hQ hdim hsgn htt hnc g : ↥(ffFix hQ (by omega)
      (projOrthToProjSim Q (toProj Q t)))) : ↥(omegaProj hQ)) : ProjOrth Q) =
        toProj Q (g : OGroup Q) := rfl

theorem ff6mFixHom_surjective (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {t : OGroup Q} (htt : t * t = 1)
    (hnc : ¬ IsConj (piOrth Q * t) t) : Function.Surjective (ff6mFixHom hQ hdim hsgn htt hnc) := by
  intro w
  obtain ⟨g, hg, hgw⟩ :=
    (ff6m_mem_ffFix_iff_of_not_conj hQ hdim hsgn htt hnc (w : ↥(omegaProj hQ))).mp w.2
  exact ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext hgw)⟩

theorem ff6mFixHom_eq_one_iff (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {t : OGroup Q} (htt : t * t = 1) (hnc : ¬ IsConj (piOrth Q * t) t)
    (g : ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)))) :
    ff6mFixHom hQ hdim hsgn htt hnc g = 1 ↔
      (g : OGroup Q) = 1 ∨ (g : OGroup Q) = piOrth Q := by
  rw [← omegaToProj_eq_one_iff hQ ⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem ff6m_omegaToProj_mem_ffFix (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {t w : OGroup Q}
    (hw : w ∈ omegaGroup hQ) (hcomm : t * w = w * t) :
    omegaToProj hQ ⟨w, hw⟩ ∈ ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)) := by
  refine (ff6m_mem_ffFix_iff hQ hdim hsgn _).mpr ⟨w, hw, Or.inl ?_, rfl⟩
  calc t * w * t⁻¹ = (w * t) * t⁻¹ := by rw [hcomm]
    _ = w := by group

theorem ff6m_cover_of_conj (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {t w g : OGroup Q} (htt : t * t = 1) (hw : w ∈ omegaGroup hQ) (hg : g ∈ omegaGroup hQ)
    (hconj : g * t * g⁻¹ = t * w ∨ g * t * g⁻¹ = piOrth Q * (t * w)) :
    ∃ a : ↥(omegaProj hQ),
      ffSimOmegaAct hQ (by omega) (projOrthToProjSim Q (toProj Q t)) a * a⁻¹ =
        omegaToProj hQ ⟨w, hw⟩ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have key : t * g * t⁻¹ * g⁻¹ = w ∨ t * g * t⁻¹ * g⁻¹ = piOrth Q * w := by
    have h0 : t * g * t⁻¹ * g⁻¹ = t * (g * t * g⁻¹) := by rw [hti]; group
    rcases hconj with h | h
    · left
      rw [h0, h, ← mul_assoc, htt, one_mul]
    · right
      have hc : t * piOrth Q = piOrth Q * t :=
        Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t
      calc t * g * t⁻¹ * g⁻¹ = t * (g * t * g⁻¹) := h0
        _ = t * (piOrth Q * (t * w)) := by rw [h]
        _ = (t * piOrth Q) * (t * w) := by rw [mul_assoc]
        _ = (piOrth Q * t) * (t * w) := by rw [hc]
        _ = piOrth Q * ((t * t) * w) := by simp only [mul_assoc]
        _ = piOrth Q * w := by rw [htt, one_mul]
  refine ⟨omegaToProj hQ ⟨g, hg⟩, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, coe_ffSimOmegaAct, projSimAct_projOrthToProjSim, Subgroup.coe_inv,
    coe_omegaToProj, coe_omegaToProj]
  have e1 : toProj Q t * toProj Q g * (toProj Q t)⁻¹ * (toProj Q g)⁻¹ =
      toProj Q (t * g * t⁻¹ * g⁻¹) := by simp only [map_mul, map_inv]
  rw [e1]
  rcases key with h | h
  · rw [h]
  · rw [h, map_mul, toProj_piOrth, one_mul]

end Model

section Transfer

theorem ff6m_layerModel_of_surj {S F : Type} [Group S] [Group F] (φ : S →* F)
    (hφ : Function.Surjective φ) {tg : CFSG.Open.StatedLieTag} {n k : ℕ} (E₀ : Subgroup S)
    [E₀.Normal] (hE₀ : LieModel ↥E₀ tg n 3 k) (h2 : IsPGroup 2 (S ⧸ E₀))
    (hinj : ∀ g ∈ E₀, φ g = 1 → g = 1) : LayerModel F tg n k := by
  haveI hE : (E₀.map φ).Normal := Subgroup.Normal.map ‹_› φ hφ
  have hinj' : Function.Injective (φ.comp E₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hinj g.1 g.2 hg)
  let ψ : ↥E₀ →* ↥(E₀.map φ) :=
    (φ.comp E₀.subtype).codRestrict (E₀.map φ) (fun g => ⟨g.1, g.2, rfl⟩)
  have hψ : Function.Bijective ψ := by
    constructor
    · intro a b hab
      exact hinj' (congrArg Subtype.val hab)
    · rintro ⟨y, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  refine ⟨E₀.map φ, hE, LieModel.of_mulEquiv (MulEquiv.ofBijective ψ hψ) hE₀, ?_⟩
  refine h2.of_surjective (QuotientGroup.map E₀ (E₀.map φ) φ
    (fun x hx => Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)) (fun y => ?_)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, rfl⟩ := hφ b
  exact ⟨QuotientGroup.mk a, rfl⟩

end Transfer

section Simple

theorem ff6m_mem_twoRes_of_simple {G : Type} [Group G] [Finite G] (C : Subgroup G)
    (E : Subgroup ↥C) (hs : IsSimpleGroup ↥E) (hnc : ∃ a b : ↥E, a * b ≠ b * a) {w : G}
    (hw : w ∈ E.map C.subtype) (hw2 : w * w = 1) : w ∈ twoRes C := by
  let e : ↥E ≃* ↥(E.map C.subtype) :=
    Subgroup.equivMapOfInjective E C.subtype C.subtype_injective
  haveI : IsSimpleGroup ↥(E.map C.subtype) := (MulEquiv.isSimpleGroup_congr e).mp hs
  have hnc' : ∃ a b : ↥(E.map C.subtype), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hEC : E.map C.subtype ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have h := ff_mem_X_of_simple C (E.map C.subtype) hEC inferInstance hnc' hw hw2
  have hle : twoPrimeRes (twoRes C) ≤ twoRes C :=
    (Subgroup.closure_le (twoRes C)).mpr fun g hg => hg.1
  exact hle h

end Simple

end CFSG.OddStandard.SmallF3.Omega
