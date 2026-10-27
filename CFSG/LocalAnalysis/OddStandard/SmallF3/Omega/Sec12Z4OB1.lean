module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4ODefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aVec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Inputs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4ORho
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OSqr
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OCount
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EFrame
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aX
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Yc
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPCtx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem z4o_outer_involution (hp : Asc82Pre11) (hSp : Asc82FactSplit5) {G : Type} [Group G]
    [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 E : Subgroup G}
    (hctx : Sec12Ctx G t L S z K1 K2 E) (hZ : IsZ4Pow4 (secV t S L E))
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)))
    {y : G} (hy : y ∈ (secM t S L ⊓ L) ⊔ S) {a b : Fin 5} (hab : a ≠ b)
    (hyσ : SecActs φ y (Equiv.swap a b)) :
    ∃ c ∈ (secM t S L ⊓ L) ⊔ S, c * c = 1 ∧ SecActs φ c (Equiv.swap a b) := by
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  obtain ⟨hPSp, -, htL, htS, -, hSyl⟩ := hp.basic G t L S z hctx.toSec10Ctx.toSec10Z
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  obtain ⟨X0, hX0B, hX0sup⟩ := hSp G t L S z K1 K2 hctx.toSec10Ctx hPSp
    (sec122_S_le_normalizer_L F hS.1) (sec122_centralizer_inf_S F hS htS) hSyl htL
  have hφ : SecNatCoord φ (secB S L) :=
    ⟨fun v hv => (hperm.2.2.1 _).mpr ⟨v, hv, rfl⟩, hperm.1, hperm.2.1,
      fun x hx => (hperm.2.2.1 x).mp hx⟩
  obtain ⟨c, hcY, hcσ, hcc⟩ :=
    z4o_exists_c F hS hX0B hX0sup hperm hy (Equiv.swap_mul_self a b) hyσ
  rcases hcc with h1 | ⟨b', hb', hbt⟩
  · exact ⟨c, hcY, h1, hcσ⟩
  · exact (z4o_not_sq_mul_t hctx F hZ hφ hcY hab hcσ hb' hbt).elim

theorem z4o_exists_outer_involution (hp : Asc82Pre11) (hSp : Asc82FactSplit5) {G : Type}
    [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 E : Subgroup G}
    (hctx : Sec12Ctx G t L S z K1 K2 E) (hZ : IsZ4Pow4 (secV t S L E)) {g : G} (hgS : g ∈ S)
    (hgK : g ∉ L ⊔ centralizer (L : Set G)) :
    ∃ s ∈ S, s * s = 1 ∧ s ∉ L ⊔ centralizer (L : Set G) := by
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  obtain ⟨φ, hperm0, -, -, hS5⟩ := F.bdata.2.2.2.2.2
  have hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)) := by
    rw [F.bdata.2.2.2.2.1]
    exact hperm0
  have hφ : SecNatCoord φ (secB S L) :=
    ⟨fun v hv => (hperm.2.2.1 _).mpr ⟨v, hv, rfl⟩, hperm.1, hperm.2.1,
      fun x hx => (hperm.2.2.1 x).mp hx⟩
  obtain ⟨y, hyY, hyσ⟩ := z4o_exists_swap F hS hperm hS5 hgS hgK
  obtain ⟨c, hcY, hcc, hcσ⟩ :=
    z4o_outer_involution hp hSp hctx hZ hperm hyY (by decide : (0 : Fin 5) ≠ 1) hyσ
  have hcle := sec123_Y_le F hS hcY
  have hcK : c ∉ L ⊔ centralizer (L : Set G) :=
    sec123_not_mem_sup hφ F.bdata.1 (fun l hl => hperm0.2.2.2.1 l hl) hcle.1.2 hcσ
      (Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1))
  have hc2 : c ^ 2 = 1 := by rw [sq]; exact hcc
  obtain ⟨Q, hQ, hcQ⟩ := exists_isSylow2Of_ge (CFSG.Open.isElemAbelian_zpowers hc2).isPGroup
    (zpowers_le.mpr hcle.2)
  obtain ⟨a, haC, haQ⟩ := IsSylow2Of.exists_conj_mem hS hQ
  have hsS : a⁻¹ * c * a ∈ S := (haQ c).mp (hcQ (mem_zpowers c))
  refine ⟨a⁻¹ * c * a, hsS, ?_, ?_⟩
  · calc a⁻¹ * c * a * (a⁻¹ * c * a) = a⁻¹ * (c * c) * a := by group
      _ = 1 := by rw [hcc]; group
  · intro hsK
    apply hcK
    have haN : a ∈ normalizer (L : Set G) := F.hCt haC
    have h := sec10A_conj_sup (X := L) (Y := centralizer (L : Set G)) (c := a)
      (fun x hx => (Subgroup.mem_normalizer_iff.mp haN x).mp hx)
      (fun x hx => kl_centralizer_conj haN hx) _ hsK
    rwa [show a * (a⁻¹ * c * a) * a⁻¹ = c by group] at h

theorem asc82StepZ4Out_of_noOuterInv (hp : Asc82Pre11) (hSp : Asc82FactSplit5)
    (hI : Asc82StepZ4NoOuterInv) : Asc82StepZ4Out := by
  intro G _ _ t L S z K1 K2 E hctx hZ g hgS
  by_contra hgK
  obtain ⟨s, hsS, hss, hsK⟩ := z4o_exists_outer_involution hp hSp hctx hZ hgS hgK
  exact hsK (hI G t L S z K1 K2 E hctx hZ s hsS hss)

end CFSG.OddStandard.SmallF3.Omega
