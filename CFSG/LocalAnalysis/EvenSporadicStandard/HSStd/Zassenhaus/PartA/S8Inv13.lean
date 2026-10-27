module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv12
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv11
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Main

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem inv_A_props :
    ∃ A : Subgroup (↥K ⧸ center ↥K), CFSG.IsQuasisimple ↥A ∧
      Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 6)) ∧
      (∀ x ∈ A, ∀ y ∈ A, x * tauHat hb a hK hcj hall y = tauHat hb a hK hcj hall y * x) := by
  let mk : ↥K →* ↥K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  set M := M1K a K with hM
  have hq : CFSG.IsQuasisimple ↥M := M1K_qs hb a hK hcj hall
  have hP : Group.IsPerfect ↥M := hq.1
  have hnker : ¬ M ≤ mk.ker := by
    intro h
    have hc : ∀ x ∈ M, x ∈ center ↥K := fun x hx => by
      have := h hx
      rwa [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hnt : Nontrivial ↥M := isQuasisimple_nontrivial hq
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥M)
    have hab : ∀ y z : ↥M, y * z = z * y := fun y z =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hc z z.2) (y : ↥K))
    have h1 : commutator ↥M = ⊥ := by
      rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro y _ z _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab y z
    rw [Group.isPerfect_def.mp hP] at h1
    exact hx (Subgroup.mem_bot.1 (h1 ▸ mem_top x))
  refine ⟨M.map mk, isQuasisimple_map hq mk hnker, ?_, ?_⟩
  · have hker : (mk.subgroupMap M).ker ≤ center ↥M := by
      rcases quasisimple_normal_subgroups hq (mk.subgroupMap M).normal_ker with h | h
      · exfalso
        apply hnker
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥M) ∈ (mk.subgroupMap M).ker := by rw [h]; exact mem_top _
        rw [MonoidHom.mem_ker] at hx' ⊢
        exact congrArg Subtype.val hx'
      · exact h
    have hg : Function.Surjective (mk.subgroupMap M) := mk.subgroupMap_surjective M
    have hcomap := comap_center_eq_of_perfect hP (mk.subgroupMap M) hg hker
    let h : ↥M →* ↥(M.map mk) ⧸ center ↥(M.map mk) :=
      (QuotientGroup.mk' (center ↥(M.map mk))).comp (mk.subgroupMap M)
    have hhs : Function.Surjective h := (QuotientGroup.mk'_surjective _).comp hg
    have hhker : h.ker = center ↥M := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
    let eA : ↥M ⧸ center ↥M ≃* ↥(M.map mk) ⧸ center ↥(M.map mk) :=
      (QuotientGroup.quotientMulEquivOfEq hhker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective h hhs)
    let e := M1K_equiv hb a hK hcj hall
    let eM : ↥M ⧸ center ↥M ≃* ↥a.M₁ ⧸ center ↥a.M₁ :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    obtain ⟨f, hf, hkerf⟩ := a.M₁_cover
    have hcA : center (alternatingGroup (Fin 6)) = ⊥ := center_eq_bot_of_simple s8_A6_simple s8_A6_nonab
    have hkerf' : f.ker = center ↥a.M₁ := by
      refine le_antisymm hkerf (fun z hz => ?_)
      rw [MonoidHom.mem_ker]
      have : f z ∈ center (alternatingGroup (Fin 6)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := hf y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
      rwa [hcA, Subgroup.mem_bot] at this
    let eF : ↥a.M₁ ⧸ center ↥a.M₁ ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.quotientMulEquivOfEq hkerf'.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)
    exact ⟨eA.symm.trans (eM.trans eF)⟩
  · rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
    show (QuotientGroup.mk m : ↥K ⧸ center ↥K) *
      tauHat hb a hK hcj hall (QuotientGroup.mk m') = tauHat hb a hK hcj hall
        (QuotientGroup.mk m') * QuotientGroup.mk m
    rw [tauHat_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have hm1 : (((m : ↥K) : ↥(Cen a.ub)) : G) ∈ a.M₁ := hm
    have hm1' : (((m' : ↥K) : ↥(Cen a.ub)) : G) ∈ a.M₁ := hm'
    have := a.M₁_comm _ hm1 _ hm1'
    apply Subtype.ext; apply Subtype.ext
    show (((m : ↥K) : ↥(Cen a.ub)) : G) * (t * (((m' : ↥K) : ↥(Cen a.ub)) : G) * t⁻¹) =
      (t * (((m' : ↥K) : ↥(Cen a.ub)) : G) * t⁻¹) * (((m : ↥K) : ↥(Cen a.ub)) : G)
    exact this

theorem inv_false (hKG : KGA6Sq) : False := by
  have hq : CFSG.IsQuasisimple ↥K := hK.1
  let e1 : ↥K ≃* ↥(K.map (Cen a.ub).subtype) :=
    Subgroup.equivMapOfInjective K (Cen a.ub).subtype (Cen a.ub).subtype_injective
  have hqg : CFSG.IsQuasisimple ↥(K.map (Cen a.ub).subtype) := isQuasisimple_of_mulEquiv e1 hq
  have hKgtop : K.map (Cen a.ub).subtype ≠ ⊤ := by
    intro h
    apply Cen_ne_top hb a.toPA6.toPA5
    rw [eq_top_iff]
    rw [eq_top_iff] at h
    intro x _
    have := h (mem_top x)
    obtain ⟨k, -, hk⟩ := this
    rw [← hk]; exact k.2
  have hCatg := catalog_quot_center hb.setting.1.kProper (K.map (Cen a.ub).subtype) hKgtop hqg
  have hcen : (center ↥K).map (e1 : ↥K →* ↥(K.map (Cen a.ub).subtype)) =
      center ↥(K.map (Cen a.ub).subtype) := Subgroup.map_center_eq e1
  have hCat : CFSG.Blueprint.Catalog (↥K ⧸ center ↥K) :=
    CFSG.SectionRank.catalog_of_mulEquiv (QuotientGroup.congr _ _ e1 hcen) hCatg
  obtain ⟨A, hAq, hA6, hAc⟩ := inv_A_props hb a hK hcj hall
  exact hKG (↥K ⧸ center ↥K) hCat hq.2.1 (tauHat hb a hK hcj hall)
    (tauHat_sq hb a hK hcj hall) (inv_card_le hb a hK hcj hall) (inv_derived hb a hK hcj hall)
    A hAq hA6 hAc

end Final

theorem s8_invariant (hKG : KGA6Sq) : S8Invariant :=
  fun _ _ _ _ _ _ _ _ hb a _ hK hcj hall => inv_false hb a hK hcj hall hKG

theorem s8 (hKG : KGA6Sq) : StepS8 :=
  s8_of_invariant (s8_invariant hKG)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
