module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentInv2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

theorem fg_lieModel_quot_iff_map [Finite G] {L X : Subgroup G} {P : Type} [Group P] [Finite P]
    {ρ : ↥L →* P} (h : OddCentralCover ρ) (hXL : X ≤ L) {t : CFSG.Open.StatedLieTag}
    {n p f : ℕ} :
    LieModel (↥X ⧸ oddCore ↥X) t n p f ↔
      LieModel (↥((X.subgroupOf L).map ρ) ⧸ oddCore ↥((X.subgroupOf L).map ρ)) t n p f := by
  let V₀ : Subgroup ↥L := X.subgroupOf L
  let ψ : ↥V₀ →* ↥X := (Subgroup.subgroupOfEquivOfLe hXL).toMonoidHom
  have hψs : Function.Surjective ψ := (Subgroup.subgroupOfEquivOfLe hXL).surjective
  have hψk : Odd (Nat.card ψ.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr (Subgroup.subgroupOfEquivOfLe hXL).injective,
      Subgroup.card_bot]
    exact odd_one
  have hc := sec63PT_oddCentralCover_subgroupMap h V₀
  have e1 := sec63PT_oddCoreQuotientEquiv ψ hψs hψk
  have e2 := sec63PT_oddCoreQuotientEquiv (ρ.subgroupMap V₀) hc.surjective hc.odd_card_ker
  exact ⟨fun hX => LieModel.of_mulEquiv (e1.symm.trans e2) hX,
    fun hJ => LieModel.of_mulEquiv (e2.symm.trans e1) hJ⟩

theorem fg_isL29_of_model [Finite G] {L X : Subgroup G} {P : Type} [Group P] [Finite P]
    {ρ : ↥L →* P} (h : OddCentralCover ρ) (hXL : X ≤ L)
    (hJ : LieModel ↥((X.subgroupOf L).map ρ) .PSL 2 3 2) : IsL29 X :=
  (fg_lieModel_quot_iff_map (t := .PSL) (n := 2) (p := 3) (f := 2) h hXL).mpr
    (ff_isL29_of_lieModel hJ)

theorem fg_isU33_of_model [Finite G] {L X : Subgroup G} {P : Type} [Group P] [Finite P]
    {ρ : ↥L →* P} (h : OddCentralCover ρ) (hXL : X ≤ L)
    (hJ : LieModel ↥((X.subgroupOf L).map ρ) .PSU 3 3 1) : IsU33 X :=
  (fg_lieModel_quot_iff_map (t := .PSU) (n := 3) (p := 3) (f := 1) h hXL).mpr
    (ff_isU33_of_lieModel hJ)

theorem fg_quotEquivTo_of_range (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    {L : Subgroup G} (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hLp : commutator ↥L = ⊤) {R : Subgroup G} (hR : R ≤ normalizer (L : Set G)) {F : Type}
    [Group F] (hF : Nonempty (↥(fgThetaR hQ h e hR).range ≃* F)) :
    QuotEquivTo R (R ⊓ centralizer (L : Set G)) F := by
  obtain ⟨φ⟩ := hF
  refine ⟨φ.toMonoidHom.comp (fgThetaR hQ h e hR).rangeRestrict,
    φ.surjective.comp (fgThetaR hQ h e hR).rangeRestrict_surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, MonoidHom.ker_rangeRestrict,
    fg_thetaR_ker hQ h e hLp hR, Subgroup.inf_subgroupOf_left]

theorem fg_simInOmegaStar_of_hyp62 [Finite G] {L : Subgroup G} (hL : IsOm6P L) (hH : Hyp62At L)
    (hQ : Q.Nondegenerate) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hx : SimInGStar x) :
    SimInOmegaStar hQ x := by
  have hEq : oddCore ↥L = Subgroup.center ↥L := (ff_center_eq_oddCore_six_plus hL).symm
  let e' : ↥L ⧸ oddCore ↥L ≃* omegaProj hQ := (QuotientGroup.quotientMulEquivOfEq hEq).trans e
  have he' : ∀ l : ↥L, e' (QuotientGroup.mk l) = e (QuotientGroup.mk l) := fun _ => rfl
  have hvia' : InducesViaP L (oddCore ↥L) hQ e' s x := by
    refine ⟨hs.1, fun l l' hl => ?_⟩
    simp only [he']
    exact hs.2 l l' hl
  exact hH V Q hQ e' hdim hsgn s x hvia' hx

@[expose] def FGCentModel (hQ : Q.Nondegenerate) (J : Subgroup ↥(omegaProj hQ))
    (A : Subgroup (ProjSim Q)) : Prop :=
  Nat.card A ≤ 2 ∨
    (quadSign Q = -1 ∧ LieModel ↥J .PSL 2 3 2 ∧
      Nonempty (↥A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
    (quadSign Q = -1 ∧ LieModel ↥J .PSU 3 3 1 ∧ Nonempty (↥A ≃* Multiplicative (ZMod 4))) ∨
    (quadSign Q = 1 ∧ LieModel ↥J .PSL 2 3 2 ∧ Nonempty (↥A ≃* Multiplicative (ZMod 4)))

theorem fg_aut_cent_of_model [Finite G] {L : Subgroup G} (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (hLp : commutator ↥L = ⊤)
    (hsgn : (quadSign Q = 1 ∧ IsOm6P L) ∨ (quadSign Q = -1 ∧ IsOm6M L)) {X : Subgroup G}
    (hXL : X ≤ L) {R : Subgroup G} (hR : R ≤ normalizer (L : Set G))
    (hmodel : FGCentModel hQ ((X.subgroupOf L).map (fgRho hQ e)) (fgThetaR hQ h e hR).range) :
    (centralizer (L : Set G)).relIndex R ≤ 2 ∨
      (IsL29 X ∧ IsOm6M L ∧ QuotEquivTo R (R ⊓ centralizer (L : Set G))
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
      (IsU33 X ∧ IsOm6M L ∧
        QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) ∨
      (IsL29 X ∧ IsOm6P L ∧
        QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) := by
  have hcov := fg_oddCentralCover_rho hQ e hodd
  have hP : quadSign Q = -1 → IsOm6M L := fun hs =>
    hsgn.elim (fun hp => absurd (hp.1.symm.trans hs) (by decide)) (fun hm => hm.2)
  have hM : quadSign Q = 1 → IsOm6P L := fun hs =>
    hsgn.elim (fun hp => hp.2) (fun hm => absurd (hm.1.symm.trans hs) (by decide))
  rw [fg_relIndex_eq_card_range hQ h e hLp hR]
  rcases hmodel with h1 | ⟨hs, hl, hA⟩ | ⟨hs, hl, hA⟩ | ⟨hs, hl, hA⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨fg_isL29_of_model hcov hXL hl, hP hs,
      fg_quotEquivTo_of_range hQ h e hLp hR hA⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨fg_isU33_of_model hcov hXL hl, hP hs,
      fg_quotEquivTo_of_range hQ h e hLp hR hA⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fg_isL29_of_model hcov hXL hl, hM hs,
      fg_quotEquivTo_of_range hQ h e hLp hR hA⟩))

theorem fg_lift_invol (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {x : ProjSim Q} (hx1 : x ≠ 1) {t : OGroup Q} (htt : t * t = 1)
    (htx : projOrthToProjSim Q (toProj Q t) = x) :
    0 < Module.finrank (ZMod 3) (fixSp t) ∧ 0 < Module.finrank (ZMod 3) (commSp t) ∧
      ffSimOmegaAct hQ h2 x = projAut hQ t := by
  subst htx
  have hαA : ffSimOmegaAct hQ h2 (projOrthToProjSim Q (toProj Q t)) = projAut hQ t := by
    rw [ffSimOmegaAct_projOrthToProjSim]
    rfl
  have hA1 : t ≠ 1 := by
    intro h1
    apply hx1
    rw [h1, map_one, map_one]
  have hAπ : t ≠ piOrth Q := by
    intro hπ'
    apply hx1
    rw [hπ', toProj_piOrth, map_one]
  have hfix_ne : fixSp t ≠ ⊥ := by
    intro hfix
    apply hAπ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have htop : commSp t = ⊤ := by
      have hc : fixSp t ⊔ commSp t = ⊤ := codisjoint_iff.mp
        (isCompl_fixSp_commSp (Q := Q) htt).2
      rwa [hfix, bot_sup_eq] at hc
    have hv : v ∈ commSp t := by rw [htop]; exact Submodule.mem_top
    rw [mem_commSp_iff htt] at hv
    rw [coe_piOrth_apply]
    exact hv
  have hcomm_ne : commSp t ≠ ⊥ := fun h => hA1 ((commSp_eq_bot_iff htt).mp h)
  refine ⟨?_, ?_, hαA⟩
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hfix_ne (Submodule.finrank_eq_zero.mp h0)
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hcomm_ne (Submodule.finrank_eq_zero.mp h0)

theorem fg_centModel_of_lift (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {x : ProjSim Q} (hx1 : x ≠ 1) {t : OGroup Q}
    (htt : t * t = 1) (htx : projOrthToProjSim Q (toProj Q t) = x) {J : Subgroup ↥(omegaProj hQ)}
    (hJ : IsComponentIn J (ffFix hQ h2 x)) {A : Subgroup (ProjSim Q)}
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q))
    (hyp62 : quadSign Q = 1 → ∀ a ∈ A, SimInGStar a → SimInOmegaStar hQ a) :
    FGCentModel hQ J A := by
  obtain ⟨hF, hC, hα⟩ := fg_lift_invol hQ h2 hx1 htt htx
  have hJ' : IsComponentIn J (fixSub (projAut hQ t)) := by
    rw [← hα]
    exact hJ
  rcases fg_cent_invol hQ (Or.inr hdim) htt hF hC hJ' hAJ (fun _ => hyp62) with
    h1 | ⟨-, hs, hl, hA⟩ | ⟨-, hs, hl, hA⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨hs, hl, hA⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hs, hl, hA⟩))

end CFSG.OddStandard.SmallF3.Omega
