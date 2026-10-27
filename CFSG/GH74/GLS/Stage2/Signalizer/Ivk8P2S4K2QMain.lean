module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2QSyl
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2QSq
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
import CFSG.GH74.GLS.C3.Layer1.BkIvk73Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2Alt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2L2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53M
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L55B

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
  CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.TwoGroups
open scoped MatrixGroups

section Narrow

variable {G : Type} [Group G] [Finite G]

theorem kaTwoY_of_narrow (hL : Lemma31Narrow) {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) {H J J' : Subgroup G} (hH : H ≠ ⊤) (hJ : IsCompIn H J)
    (hJ' : IsCompIn H J') (hne : J ≠ J') : KATwoY (↥J ⧸ center ↥J) := by
  classical
  have hq : IsQuasisimple ↥J := K0.quasisimple_of_isCompIn hJ
  have hq' : IsQuasisimple ↥J' := K0.quasisimple_of_isCompIn hJ'
  obtain ⟨u, hu⟩ := exists_orderOf_eq_two_of_isQuasisimple hq
  obtain ⟨u', hu'⟩ := exists_orderOf_eq_two_of_isQuasisimple hq'
  have hev : 2 ∣ Nat.card ↥J := hu ▸ orderOf_dvd_natCard u
  have hev' : 2 ∣ Nat.card ↥J' := hu' ▸ orderOf_dvd_natCard u'
  have hPC' : IsPCompIn 2 H J' :=
    CFSG.GH74.GLS.C3.Layer1.Bk.isPCompIn_two_of_isCompIn_of_even hJ' hev'
  have hcomm : ∀ a ∈ J', ∀ b ∈ J, a * b = b * a := comps_commute hJ' hJ hne.symm
  set C : Subgroup G := H ⊓ centralizerSection J' (pPrimeCoreOf 2 J') with hC
  have hJC : J ≤ C := le_inf hJ.1 (le_centralizerSection (TwoThin.pPrimeCoreOf_le J') hcomm)
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  let ι₀ : ↥J →* ↥C := Subgroup.inclusion hJC
  have hι₀ : Function.Injective ι₀ := Subgroup.inclusion_injective hJC
  let T'' : Subgroup ↥C := (T : Subgroup ↥J).map ι₀
  have hT''p : IsPGroup 2 ↥T'' :=
    IsPGroup.of_equiv T.isPGroup' (Subgroup.equivMapOfInjective (T : Subgroup ↥J) ι₀ hι₀)
  obtain ⟨Q, hQ⟩ := hT''p.exists_le_sylow
  let R : Subgroup G := (Q : Subgroup ↥C).map C.subtype
  have hRsyl : IsSylowOf 2 R C := ⟨Q, rfl⟩
  have hCev : 2 ∣ Nat.card ↥C := hev.trans (Subgroup.card_dvd_of_le hJC)
  have hQ1 : (Q : Subgroup ↥C) ≠ ⊥ := Q.ne_bot_of_dvd_card hCev
  have hR1 : R ≠ ⊥ := fun h =>
    hQ1 ((Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h)
  have ha := (hL G z k S hctx H J' R hH hPC' hRsyl hR1).1
  have hTR : ∀ t : ↥(T : Subgroup ↥J), (((t : ↥J) : G)) ∈ R := fun t =>
    ⟨ι₀ t, hQ (Subgroup.mem_map_of_mem ι₀ t.2), rfl⟩
  let ιR : ↥(T : Subgroup ↥J) →* ↥R :=
    ((J.subtype).comp (T : Subgroup ↥J).subtype).codRestrict R hTR
  have hιR : Function.Injective ιR := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (fun w : ↥R => (w : G)) hxy))
  have hTnc : ¬ IsCyclic ↥(T : Subgroup ↥J) := perfect_sylow_two_not_cyclic hq.1 hev T
  have hP : ∃ P : Sylow 2 (↥J ⧸ center ↥J), ∃ n : ℕ,
      Nonempty (↥(P : Subgroup (↥J ⧸ center ↥J)) ≃* DihedralGroup n) := by
    rcases ha with hc | hQuat | hDih
    · have := hc
      exact absurd (isCyclic_of_injective ιR hιR) hTnc
    · obtain ⟨n, hn3, ⟨e⟩⟩ := hQuat
      have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
      let ι : ↥(T : Subgroup ↥J) →* QuaternionGroup (2 ^ (n - 2)) := e.toMonoidHom.comp ιR
      have hι : Function.Injective ι := e.injective.comp hιR
      exact exists_sylow_dihedral hq hev T _ index_zpowers_a_one quaternion_hinv ι hι
        fun u hu => sq_mem_center_of_quaternion hq hev T hTnc ι hι hu
    · obtain ⟨m, k', hm, hk', ⟨e⟩⟩ := hDih
      have : NeZero k' := ⟨by omega⟩
      let ι : ↥(T : Subgroup ↥J) →* DihedralGroup k' := e.toMonoidHom.comp ιR
      have hι : Function.Injective ι := e.injective.comp hιR
      refine exists_sylow_dihedral hq hev T _ index_zpowers_r_one dihedral_hinv ι hι ?_
      intro u hu
      obtain ⟨j, hj⟩ : ∃ j, ι u = DihedralGroup.sr j := by
        cases hu' : ι u with
        | r j =>
          exact absurd (by rw [hu']; exact (mem_zpowers_r_one_iff _).2 ⟨j, rfl⟩) hu
        | sr j => exact ⟨j, rfl⟩
      have h1 : u ^ 2 = 1 := hι (by rw [map_pow, hj, sq, DihedralGroup.sr_mul_self, map_one])
      rw [show (u : ↥J) ^ 2 = 1 from congrArg Subtype.val h1]
      exact Subgroup.one_mem _
  obtain ⟨P, n, hdih⟩ := hP
  have hsimple : IsSimpleGroup (↥J ⧸ center ↥J) := hq.2.1
  have hnonab : ∃ a b : ↥J ⧸ center ↥J, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    exact ⟨a, b, hab⟩
  rcases CFSG.GorensteinWalter.gorenstein_walter (↥J ⧸ center ↥J) hnonab P ⟨n, hdih⟩ with
    hA7 | ⟨p, k', hp, hpodd, h5, hL2⟩
  · obtain ⟨e⟩ := hA7
    exact KATwoY.of_mulEquiv e.symm kaTwoY_alt7
  · obtain ⟨e⟩ := hL2
    have hk0 : k' ≠ 0 := by
      rintro rfl
      simp at h5
    have hcard : Nat.card (GaloisField p k') = p ^ k' := GaloisField.card p k' hk0
    have hF : IVK.L2Field (GaloisField p k') := by
      refine ⟨?_, ?_⟩
      · rw [hcard]
        exact hpodd.pow
      · rw [hcard]
        omega
    exact kaTwoY_L2 hF (e.trans (IVK.L2.equivPSL (GaloisField p k')).symm)

end Narrow

theorem ivk_8_13_two_of_narrow (hL : Lemma31Narrow) : IVK_8_13_two :=
  ivk_8_13_two_of_KA fun _ _ _ _ _ _ hctx _ _ _ hH hJ hJ' hne =>
    kaTwoY_of_narrow hL hctx hH hJ hJ' hne

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
