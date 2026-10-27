module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Cfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Cmm
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Cases
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3C
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3B

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Cent

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_le_of_comm {z : G} {J : Subgroup G} (hq : IsQuasisimple ↥J)
    (hJz : ⁅J, zpowers z⁆ = J) : ¬ J ≤ centralizer ({z} : Set G) := by
  intro hle
  have h1 : J ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : x * z = z * x :=
      (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm ▸ rfl
    have hcz : Commute z x := (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
    exact ((hcz.zpow_left n).eq)
  have h2 : ⁅J, zpowers z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
  rw [hJz] at h2
  have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact (Subgroup.nontrivial_iff_ne_bot J).mp this h2

theorem J_le_Em_cent (hB12 : Bender12) (h184 : Lemma18_4ac) (h171 : Prop17_1) {z : G} {k : Kind}
    {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) {d : G}
    (hdE : d ∈ E) (hd1 : d ≠ 1) (hdM : ¬ centralizer ({d} : Set G) ≤ M) {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hJC : J ≤ centralizer ({d} : Set G)) (hJz : ⁅J, zpowers z⁆ = J) :
    J ≤ Em (centralizer ({d} : Set G)) := by
  have hF := S5Facts.of_ctx h171 hctx
  have hz2' : z * z = 1 := mul_self_eq_one_of_orderOf hF.hz2
  obtain ⟨hzC, hVC, hF1, hF2⟩ := centralizer_facts hB12 h171 hctx hdE
  have hc2 := comm2_le_XdR hB12 h184 h171 hctx hdE hd1 hdM
  have hJX : J ≤ XdR M d := le_XdR_of_comp hc2 hJC hJz
  have hzN : z ∈ normalizer ((centralizer ({d} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hzC
  obtain ⟨hinv, -⟩ := inverts_F1 hF.hMz hz2' hzN hF1
  exact perfect_le_of_sup (A := Em (centralizer ({d} : Set G)))
    (B := Fpi (piF' M) (centralizer ({d} : Set G))) hJ hJX (abelian_of_inverts hinv)
    (fun a ha b hb => Fm_commute_Em' (centralizer ({d} : Set G)) b (Fpi_le_Fm _ _ hb) a ha)

theorem comps_no3 (h183 : Lemma18_3a) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) {K : Subgroup G}
    (hKv : ∀ v ∈ Vof M E, v ∈ normalizer (K : Set G)) (hKM : ¬ K ≤ M) (hKG : K ≠ ⊤) :
    ∀ I₁ I₂ I₃ : Subgroup G, IsCompIn K I₁ → IsCompIn K I₂ → IsCompIn K I₃ →
      I₁ = I₂ ∨ I₁ = I₃ ∨ I₂ = I₃ := by
  intro I₁ I₂ I₃ h₁ h₂ h₃
  have h3 := (h183 G z k S M p E t hctx K hKv hKM hKG I₁ h₁).1
  by_contra hcon
  push Not at hcon
  have h2 : 2 < Set.ncard {K' : Subgroup G | IsCompIn K K'} :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mpr
      ⟨I₁, I₂, I₃, h₁, h₂, h₃, hcon.1, hcon.2.1, hcon.2.2⟩
  omega

theorem no_involution_cent (hMin : MinIndexL34) (hInv : InvSec)
    {z : G} {k : Kind} {S : Subgroup G} (hS2 : Stage2Ctx G z k S) {J : Subgroup G}
    (hq : IsQuasisimple ↥J) (hLie : IsL34Quotient ↥J) :
    ∀ d : G, orderOf d = 2 → ¬ J ≤ centralizer ({d} : Set G) := by
  intro d hd hle
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hq
  have hsec : IsSection (↥J ⧸ center ↥J) ↥(centralizer ({d} : Set G)) :=
    ⟨J.subgroupOf _, (QuotientGroup.mk' (center ↥J)).comp
      (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom,
      (QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hle).surjective⟩
  have := hs
  exact not_kindFactorAll_l34 hMin k hLie (hInv G z k S hS2 d hd _ hns hsec)

theorem exists_elem_four (hkb : KB813) {J : Subgroup G} (hLie : IsL34Quotient ↥J)
    (hZ : Odd (Nat.card ↥(center ↥J))) :
    ∃ A : Subgroup G, A ≤ J ∧ IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ 4 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrk : 4 ≤ pRank 2 (↥J ⧸ center ↥J) := (hkb _ hLie).1
  obtain ⟨Ē, hĒ, hĒc⟩ := P2S3.exists_elementaryAbelian_card Nat.prime_two hrk
  obtain ⟨W, -, hWmap, hWN⟩ := exists_two_lift (center ↥J) hZ Ē
    (IsElementaryAbelian.isPGroup 2 ↥Ē)
  let f : ↥W →* ↥J ⧸ center ↥J := (QuotientGroup.mk' (center ↥J)).comp W.subtype
  have hfE : ∀ w : ↥W, f w ∈ Ē := fun w => by
    rw [← hWmap]; exact ⟨w, w.2, rfl⟩
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (w : ↥J) ∈ center ↥J := (QuotientGroup.eq_one_iff _).mp hw
    have h3 : (w : ↥J) ∈ W ⊓ center ↥J := ⟨w.2, h1⟩
    rw [hWN, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hWel : IsElementaryAbelian 2 ↥W := P2S3.isElementaryAbelian_of_injective hĒ f hf hfE
  have hWc : Nat.card ↥W = 2 ^ 4 := by
    rw [← hĒc]
    refine Nat.card_congr (Equiv.ofBijective (fun w : ↥W => (⟨f w, hfE w⟩ : ↥Ē)) ⟨?_, ?_⟩)
    · intro a b hab
      exact hf (congrArg Subtype.val hab)
    · rintro ⟨e, he⟩
      have : e ∈ W.map (QuotientGroup.mk' (center ↥J)) := hWmap ▸ he
      obtain ⟨w, hw, hwe⟩ := this
      exact ⟨⟨w, hw⟩, Subtype.ext hwe⟩
  refine ⟨W.map J.subtype, Subgroup.map_subtype_le W, IsElementaryAbelian.map_subtype, ?_⟩
  rw [Subgroup.card_map_of_injective J.subtype_injective, hWc]

theorem exists_cent_elem (hMin : MinIndexL34) (hInv : InvSec)
    (hstar : KStarL34) (h171 : Prop17_1) (hL31 : Lemma31Narrow) (h183 : Lemma18_3a) {z : G}
    {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) {X : Subgroup G}
    (hXv : ∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) (hXM : ¬ X ≤ M) (hXG : X ≠ ⊤)
    {J : Subgroup G} (hJ : IsCompIn X J) (hLie : IsL34Quotient ↥J) :
    ∃ e ∈ E, e ≠ 1 ∧ J ≤ centralizer ({e} : Set G) := by
  have hq : IsQuasisimple ↥J := P2S3.quasisimple_of_isCompIn hJ
  have hperf : Group.IsPerfect ↥J := hq.1
  obtain ⟨hJz, hzN, hJZ, hVN⟩ := cfg_basic h171 hL31 h183 hctx hXv hXM hXG hJ
  obtain ⟨hzN', hp3, -, -, h9, -⟩ :=
    cfg_star hMin hInv hstar h171 hL31 h183 hctx hXv hXM hXG hJ hLie
  have hF := S5Facts.of_ctx h171 hctx
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.odd
  have hEN : E ≤ normalizer (J : Set G) := fun x hx =>
    hVN x (hF.hEV hx) (odd_orderOf_of_mem_elem hp hp2 hctx.E_elem hx)
  have hEle : E ≤ Op p M ⊓ normalizer (J : Set G) := fun x hx => ⟨hctx.E_le hx, hEN hx⟩
  have hle9 : Nat.card ↥(Pbar J E) ≤ 9 := by
    rw [← h9]
    exact Subgroup.card_le_of_le (by
      rintro e ⟨n, hn, rfl⟩
      exact ⟨n, hEle hn, rfl⟩)
  have hrel := relIndex_eq_card_Pbar (J := J) (P := E) hEN
  have hE27 : 27 ≤ Nat.card ↥E := by
    obtain ⟨F, -, hFc⟩ := P2S3.exists_elementaryAbelian_card hp (Y := ↥E) hctx.E_rank
    have h1 := Subgroup.card_le_card_group F
    rw [hFc, hp3] at h1
    omega
  by_contra hcon
  push Not at hcon
  have hbot : E ⊓ centralizer (J : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rw [Subgroup.mem_bot]
    by_contra he1
    refine hcon e he.1 he1 fun j hj => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp he.2 j hj)
  rw [hbot, Subgroup.relIndex_bot_left] at hrel
  omega

end Cent

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
