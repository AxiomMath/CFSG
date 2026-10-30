module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed3
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointRankFour
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.PGroupNormalE4
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Sec12c

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowIn_above {p : ℕ} [Fact p.Prime] {X P : Subgroup G} (hPX : P ≤ X)
    (hP : IsPGroup p ↥P) : ∃ Q : Subgroup G, IsSylowIn p X Q ∧ P ≤ Q := by
  obtain ⟨Q, hPQ, hQmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ X ∧ IsPGroup p ↥R}).exists_le_maximal ⟨hPX, hP⟩
  exact ⟨Q, ⟨hQmax.1.1, hQmax.1.2, fun R' hR'X hR'p hQR' =>
    le_antisymm (hQmax.2 ⟨hR'X, hR'p⟩ hQR') hQR'⟩, hPQ⟩

theorem join_zpowers_isElemAbelian {C : Subgroup G} {x : G} (hC : CFSG.Open.IsElemAbelian 3 C)
    (hx3 : x ^ 3 = 1) (hCx : ∀ c ∈ C, c * x = x * c) :
    CFSG.Open.IsElemAbelian 3 (C ⊔ Subgroup.zpowers x : Subgroup G) := by
  haveI : IsElementaryAbelian 3 C :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 C).2 hC
  haveI : IsElementaryAbelian 3 (Subgroup.zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx3
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer (C : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 fun c hc => hCx c hc
  have hY : IsElementaryAbelian 3 (C ⊔ Subgroup.zpowers x : Subgroup G) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
  exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 hY

theorem join_zpowers_card {C : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxC : x ∉ C)
    (hCx : ∀ c ∈ C, c * x = x * c) :
    Nat.card ↥(C ⊔ Subgroup.zpowers x : Subgroup G) = Nat.card C * 3 :=
  CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three C hx3 hxC hCx

theorem nine_le_card_inf_centralizer {F : Subgroup G} {x : G} (hFel : CFSG.Open.IsElemAbelian 3 F)
    (hFc : Nat.card F = 3 ^ 4) (hFn : x ∈ Subgroup.normalizer (F : Set G)) (hx3 : x ^ 3 = 1) :
    9 ≤ Nat.card ↥(F ⊓ Subgroup.centralizer ({x} : Set G)) := by
  classical
  have hcomm : ∀ a b : F, a * b = b * a := fun a b => hFel.1.is_comm.comm a b
  let _ : CommGroup F := { (inferInstance : Group F) with mul_comm := hcomm }
  let α : F →* F := MonoidHom.mk'
    (fun e => ⟨x * e * x⁻¹, (Subgroup.mem_normalizer_iff.1 hFn e).1 e.2⟩)
    (by
      intro a b
      apply Subtype.ext
      simp [mul_assoc])
  have hx111 : x * x * x = 1 := by simpa [pow_succ] using hx3
  have hα : ∀ e, α (α (α e)) = e := by
    intro e
    apply Subtype.ext
    change x * (x * (x * (e : G) * x⁻¹) * x⁻¹) * x⁻¹ = e
    have : x * (x * (x * (e : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * e * (x * x * x)⁻¹ := by
      group
    rw [this, hx111]
    simp
  have h3 : ∀ y : F, y ^ 3 = 1 := fun y => Subtype.ext (by simpa using hFel.2 y y.2)
  have h9 := CFSG.LocalAnalysis.RankFourTheoremC.nine_le_card_eqLocus (E := F) hFc h3 α hα
  refine h9.trans ?_
  calc Nat.card (MonoidHom.eqLocus α (MonoidHom.id F))
      = Nat.card ((MonoidHom.eqLocus α (MonoidHom.id F)).map F.subtype) :=
        (Subgroup.card_map_of_injective F.subtype_injective).symm
    _ ≤ Nat.card ↥(F ⊓ Subgroup.centralizer ({x} : Set G)) := by
        refine Subgroup.card_le_of_le ?_
        rintro _ ⟨f, hf, rfl⟩
        refine ⟨f.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have hf' : α f = f := hf
        have := congrArg Subtype.val hf'
        change x * (f : G) * x⁻¹ = f at this
        calc (f : G) * x = (x * (f : G) * x⁻¹) * x := by rw [this]
          _ = x * (f : G) := by group

theorem pCoreOf_conj_mem {M : Subgroup G} {g n : G} (hg : g ∈ M) (hn : n ∈ pCoreOf 2 M) :
    g * n * g⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hn
  have hc := (CFSG.pCore_normal (p := 2) (G := ↥M)).conj_mem q hq ⟨g, hg⟩
  exact Subgroup.mem_map.2 ⟨_, hc, by simp⟩

theorem centralizer_conj_mem' {x g c : G} (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hgi : g⁻¹ * x = x * g⁻¹ := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.inv_mem _ hg)
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * c * g⁻¹ * x = g * c * (g⁻¹ * x) := by group
    _ = g * c * (x * g⁻¹) := by rw [hgi]
    _ = g * (c * x) * g⁻¹ := by group
    _ = g * (x * c) * g⁻¹ := by rw [hcx]
    _ = (g * x) * c * g⁻¹ := by group
    _ = (x * g) * c * g⁻¹ := by rw [hgx]
    _ = x * (g * c * g⁻¹) := by group

theorem pCore_inter_le_alpha (M : Subgroup G) (x : G) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({x} : Set G) ≤
      pCoreOf 2 (alphaOf 3 M ⊓ Subgroup.centralizer ({x} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hsub : pCoreOf 2 M ≤ alphaOf 3 M := by
    unfold alphaOf
    exact le_sup_left
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ (hO2.to_le inf_le_left)
  · exact inf_le_inf_right _ hsub
  · intro g hg
    have hgM : g ∈ M := alphaOf_le 3 M hg.1
    have hgC : g ∈ Subgroup.centralizer ({x} : Set G) := hg.2
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact ⟨pCoreOf_conj_mem hgM hn.1, centralizer_conj_mem' hgC hn.2⟩
    · intro hn
      have hgi : g⁻¹ ∈ M := M.inv_mem hgM
      have hgiC : g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.inv_mem _ hgC
      have h : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({x} : Set G) :=
        ⟨pCoreOf_conj_mem hgi hn.1, centralizer_conj_mem' hgiC hn.2⟩
      have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rw [e] at h
      exact h

theorem card_le_of_rank_le_three {M X : Subgroup G} {x : G} (hX : X ≤ M ⊓ Subgroup.centralizer ({x} : Set G))
    (hXel : CFSG.Open.IsElemAbelian 3 X)
    (hr : CFSG.Open.pRank 3 (M ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 3) :
    Nat.card X ≤ 3 ^ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := exists_card_eq_pow (CFSG.Open.IsElemAbelian.isPGroup hXel)
  have hjle : j ≤ CFSG.Open.pRank 3 (M ⊓ Subgroup.centralizer ({x} : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hX hXel hj
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num) (hjle.trans hr)

end Helpers

variable {G : Type} [Group G] [Finite G]

theorem inD_of_rank4 {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A)
    (hA : CFSG.Open.pRank 3 A = 3) {W : Subgroup G} (hWM : W ≤ M)
    (hWel : CFSG.Open.IsElemAbelian 3 W) (hWc : Nat.card W = 3 ^ 4) :
    ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ W ≤ A₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hWR⟩ := exists_isSylowIn_above hWM (CFSG.Open.IsElemAbelian.isPGroup hWel)
  have hW4 : IsEkIn 3 4 R W := ⟨hWR, hWel, hWc⟩
  obtain ⟨hW0, -⟩ := lemma104_v_holds h.toSec10Fails h.pair (Or.inr hA) hR
  obtain ⟨-, -, A₁, hA₁, hWA₁⟩ := hW0 W hW4
  exact ⟨A₁, hA₁, hWA₁⟩

theorem concl_of_mem {M A₁ : Subgroup G} {x : G} (hA₁ : inD 3 M A₁) (hxA : x ∈ A₁) (hx1 : x ≠ 1) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({x} : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) :=
  (pCore_inter_le_alpha M x).trans (hA₁.2.clause_b x hxA hx1)

variable {m : ℕ} {B M E A : Subgroup G}

theorem prop126_exists_sylow (h : Sec11 G m 3 B M E A) :
    ∃ R : Subgroup G, IsSylowIn 3 M R ∧ E ⊔ A ≤ R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEA : IsDDpStar 3 M E A := h.pair
  have hp : IsPGroup 3 ↥(E ⊔ A) := lemma104_i_holds h.toSec10Fails hEA
  have hEAM : E ⊔ A ≤ M := sup_le hEA.1.1.1.1.1 hEA.1.2.1.1.1.1
  exact exists_isSylowIn_above hEAM hp

theorem prop126_central_mem (h : Sec11 G m 3 B M E A) {R : Subgroup G} (hER : E ⊔ A ≤ R)
    {z : G} (hz : z ∈ centerOf R) (hz3 : orderOf z = 3) : z ∈ E ⊓ A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hscE, hscA⟩ := lemma104_ii_holds h.toSec10Fails h.pair
  have hz3' : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hcent : ∀ r ∈ R, r * z = z * r := by
    intro r hr
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz
    have hcr := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨r, hr⟩)
    have hc' : (c : G) = z := hcz
    have h3 : r * (c : G) = (c : G) * r := by simpa using hcr
    rw [← hc']
    exact h3
  have hEz : z ∈ E := by
    have hjoin := join_zpowers_isElemAbelian (x := z) hscE.2.1 hz3'
      (fun c hc => hcent c (hER (Subgroup.mem_sup_left hc)))
    have hmax := hscE.2.2 (E ⊔ Subgroup.zpowers z) le_top hjoin le_sup_left
    have hmem : z ∈ E ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    rwa [hmax] at hmem
  have hAz : z ∈ A := by
    have hjoin := join_zpowers_isElemAbelian (x := z) hscA.2.1 hz3'
      (fun c hc => hcent c (hER (Subgroup.mem_sup_right hc)))
    have hmax := hscA.2.2 (A ⊔ Subgroup.zpowers z) le_top hjoin le_sup_left
    have hmem : z ∈ A ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    rwa [hmax] at hmem
  exact ⟨hEz, hAz⟩

end Sec12c

open Sec12c

theorem lemma128_of_inputs (h121 : Prop121_corStatement) : Lemma128Statement := by
  intro G _ _ m B M E A h _hE hA x hx hx3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx3
    norm_num at hx3
  have hx3' : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hEA : IsDDpStar 3 M E A := h.pair
  have hEd : inD 3 M E := hEA.1.1
  have hEpr : 3 ≤ CFSG.Open.pRank 3 E := hEd.1.2
  have hEAle2 : CFSG.Open.pRank 3 (E ⊓ A) ≤ 2 :=
    c104_rank_inf_le_two_of_DD Nat.prime_three hEA (Or.inr hA)
  have hEA2 : 2 ≤ CFSG.Open.pRank 3 (E ⊓ A) := hEA.1.2.2
  have hS : GLStanding G m 3 := h.standing
  have hBel : CFSG.Open.IsElemAbelian 3 B := (lemma23_proved G m 3 hS B h.bOne).2.1
  have hBcard : Nat.card B = 3 ^ m := hS.card_eq h.bOne
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS h.bOne h.pre
  have hm4 : 4 ≤ m := hS.four_le
  have hzM : Subgroup.zpowers x ≤ M := Subgroup.zpowers_le.2 hx
  have hzp : IsPGroup 3 ↥(Subgroup.zpowers x) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hx3]; norm_num⟩
  obtain ⟨y, -, S, hSp, hSM, hzS, hBS⟩ :=
    exists_conj_le_pGroup' (p := 3) hzM hzp hBM (CFSG.Open.IsElemAbelian.isPGroup hBel)
  obtain ⟨R, hR, hSR⟩ := Sec12c.exists_isSylowIn_above hSM hSp
  have hxR : x ∈ R := hSR (hzS (Subgroup.mem_zpowers x))
  have hBy : CFSG.Open.IsElemAbelian 3 (GLBConj y B) :=
    CFSG.Open.IsElemAbelian.map hBel _
  have hBycard : Nat.card (GLBConj y B) = 3 ^ m := by
    rw [GLBConj, Subgroup.card_map_of_injective (f := (MulAut.conj y⁻¹).toMonoidHom)
      (MulAut.conj y⁻¹).injective, hBcard]
  have hm4R : 4 ≤ CFSG.Open.pRank 3 R :=
    le_trans hm4 (CFSG.SectionRank.le_pRank (by norm_num) (hBS.trans hSR) hBy hBycard)
  obtain ⟨F, hFR, hRN, hFel, hFc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.gl83NormalElementaryRankFour_holds G R
      hR.2.1 hm4R
  have hFM : F ≤ M := hFR.trans hR.1
  have hxN : x ∈ Subgroup.normalizer (F : Set G) := hRN hxR
  by_cases hcase : 4 ≤ CFSG.Open.pRank 3 (M ⊓ Subgroup.centralizer ({x} : Set G))
  ·
    obtain ⟨U, hUle, hUel, hUc⟩ :=
      exists_elemAbelian_card_pow_of_le_pRank' (p := 3)
        (H := M ⊓ Subgroup.centralizer ({x} : Set G)) (k := 4) hcase
    have hUM : U ≤ M := hUle.trans inf_le_left
    have hUC : ∀ u ∈ U, u * x = x * u := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.1 (hUle hu).2
    have hW : ∃ W : Subgroup G, x ∈ W ∧ W ≤ M ∧ CFSG.Open.IsElemAbelian 3 W ∧
        Nat.card W = 3 ^ 4 := by
      by_cases hxU : x ∈ U
      · exact ⟨U, hxU, hUM, hUel, hUc⟩
      · obtain ⟨U', hU'U, hU'el, hU'c⟩ :=
          exists_le_isElemAbelian_card hUel (n := 3)
            (by rw [hUc]; exact pow_dvd_pow 3 (by norm_num))
        have hxU' : x ∉ U' := fun hh => hxU (hU'U hh)
        have hU'C : ∀ c ∈ U', c * x = x * c := fun c hc => hUC c (hU'U hc)
        refine ⟨U' ⊔ Subgroup.zpowers x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x),
          sup_le (hU'U.trans hUM) hzM, join_zpowers_isElemAbelian hU'el hx3' hU'C, ?_⟩
        rw [join_zpowers_card hx3' hxU' hU'C, hU'c]
        norm_num
    obtain ⟨W, hxW, hWM, hWel, hWc⟩ := hW
    obtain ⟨A₁, hA₁, hWA₁⟩ := inD_of_rank4 h hA hWM hWel hWc
    exact concl_of_mem hA₁ (hWA₁ hxW) hx1
  ·
    have hcaseB : CFSG.Open.pRank 3 (M ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 3 := by
      omega
    have hxF : x ∉ F := by
      intro hxF
      have hFC : F ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := by
        intro f hf
        refine ⟨hFM hf, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have := congrArg Subtype.val (hFel.1.is_comm.comm (⟨f, hf⟩ : F) ⟨x, hxF⟩)
        simpa using this
      have h4 := CFSG.SectionRank.le_pRank (by norm_num) hFC hFel hFc
      omega
    have h9 := nine_le_card_inf_centralizer hFel hFc hxN hx3'
    set C : Subgroup G := F ⊓ Subgroup.centralizer ({x} : Set G)
    have hCF : C ≤ F := inf_le_left
    have hCx : ∀ c ∈ C, c * x = x * c := fun c hc => Subgroup.mem_centralizer_singleton_iff.1 hc.2
    have hxC : x ∉ C := fun hh => hxF hh.1
    have hCel : CFSG.Open.IsElemAbelian 3 C := isElemAbelian_mono hFel hCF
    set As : Subgroup G := C ⊔ Subgroup.zpowers x
    have hAsel : CFSG.Open.IsElemAbelian 3 As := join_zpowers_isElemAbelian hCel hx3' hCx
    have hAsc : Nat.card As = Nat.card C * 3 := join_zpowers_card hx3' hxC hCx
    have hAsM : As ≤ M := sup_le (hCF.trans hFM) hzM
    have hAsC : As ≤ Subgroup.centralizer ({x} : Set G) := by
      apply sup_le
      · intro c hc
        exact Subgroup.mem_centralizer_singleton_iff.2 (hCx c hc)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hAsMC : As ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hAsM hAsC
    have hAs27 : Nat.card As = 3 ^ 3 := by
      have hge : 27 ≤ Nat.card As := by
        rw [hAsc]
        omega
      have hle := card_le_of_rank_le_three hAsMC hAsel hcaseB
      norm_num at hge hle ⊢
      omega
    have hAsrank : CFSG.Open.pRank 3 As = 3 := by
      apply le_antisymm
      · unfold CFSG.Open.pRank
        apply csSup_le'
        rintro k ⟨E', hE'As, hE'el, hE'c⟩
        by_contra hk
        push Not at hk
        have h1 : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        have h2 : Nat.card E' ≤ Nat.card As := Subgroup.card_le_of_le hE'As
        rw [hE'c, hAs27] at h2
        norm_num at h1 h2
        omega
      · exact CFSG.SectionRank.le_pRank (by norm_num) (le_refl As) hAsel hAs27
    have hAsSC : IsSCp 3 M As := by
      refine ⟨hAsM, hAsel, fun X hXM hXel hAX => ?_⟩
      have hxX : x ∈ X := hAX (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
      have hXC : X ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := by
        intro y hy
        refine ⟨hXM hy, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have := congrArg Subtype.val (hXel.1.is_comm.comm (⟨y, hy⟩ : X) ⟨x, hxX⟩)
        simpa using this
      have hXle := card_le_of_rank_le_three hXC hXel hcaseB
      exact (Subgroup.eq_of_le_of_card_ge hAX (by rw [hAs27]; norm_num; omega)).symm
    have hAsStar : IsSCstar 3 M As := ⟨hAsSC, by omega⟩
    by_cases huAs : IsUniquenessTwoLocal 3 As M
    · exact concl_of_mem ⟨hAsStar, huAs⟩ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) hx1
    ·
      have hAsDp : inDp 3 M As := ⟨hAsStar, huAs⟩
      obtain ⟨A₁, hA₁, hFA₁⟩ := inD_of_rank4 h hA hFM hFel hFc
      have hA₁el : CFSG.Open.IsElemAbelian 3 A₁ := hA₁.1.1.2.1
      have hA₁pr4 : 4 ≤ CFSG.Open.pRank 3 A₁ :=
        CFSG.SectionRank.le_pRank (by norm_num) hFA₁ hFel hFc
      have hdd : inDDp 3 M A₁ As := by
        refine ⟨hA₁, hAsDp, ?_⟩
        have hCsub : C ≤ A₁ ⊓ As := le_inf (hCF.trans hFA₁) le_sup_left
        obtain ⟨jC, hjC⟩ := exists_card_eq_pow (CFSG.Open.IsElemAbelian.isPGroup hCel)
        have hjC2 : 2 ≤ jC := by
          by_contra hlt
          push Not at hlt
          have h3le : 3 ^ jC ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [← hjC] at h3le
          norm_num at h3le
          omega
        exact hjC2.trans (CFSG.SectionRank.le_pRank (by norm_num) hCsub hCel hjC)
      have hle := hEA.2 A₁ As hdd
      unfold ddKey at hle
      have hA₁As2 : 2 ≤ CFSG.Open.pRank 3 (A₁ ⊓ As) := hdd.2.2
      have hfirst_le : CFSG.Open.pRank 3 (A₁ ⊓ As) ≤ CFSG.Open.pRank 3 (E ⊓ A) := by
        rcases Prod.Lex.toLex_le_toLex.1 hle with h1 | ⟨h1, -⟩ <;> omega
      have hA₁le : CFSG.Open.pRank 3 A₁ ≤ CFSG.Open.pRank 3 E := by
        rcases Prod.Lex.toLex_le_toLex.1 hle with h1 | ⟨h1, h2⟩
        · omega
        rcases Prod.Lex.toLex_le_toLex.1 h2 with h3 | ⟨h3, h4⟩
        · omega
        rcases Prod.Lex.toLex_le_toLex.1 h4 with h5 | ⟨h5, -⟩
        · omega
        · omega
      have hA₁el' : CFSG.Open.IsElemAbelian 3 A₁ := hA₁el
      have hA₁F : A₁ = F := by
        obtain ⟨j₁, hj₁⟩ := exists_card_eq_pow (CFSG.Open.IsElemAbelian.isPGroup hA₁el')
        have hj₁le : j₁ ≤ CFSG.Open.pRank 3 A₁ :=
          CFSG.SectionRank.le_pRank (by norm_num) (le_refl A₁) hA₁el' hj₁
        have hcardle : Nat.card A₁ ≤ Nat.card F := by
          rw [hj₁, hFc]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        exact (Subgroup.eq_of_le_of_card_ge hFA₁ hcardle).symm
      have hA₁R : A₁ ≤ R := by
        rw [hA₁F]
        exact hFR
      have hAsR : As ≤ R := sup_le (hCF.trans hFR) (Subgroup.zpowers_le.2 hxR)
      have hAsP : IsPGroup 3 ↥(A₁ ⊔ As : Subgroup G) := hR.2.1.to_le (sup_le hA₁R hAsR)
      have hkey : ddKey 3 E A ≤ ddKey 3 A₁ As := by
        unfold ddKey
        have hfirst : CFSG.Open.pRank 3 (E ⊓ A) = CFSG.Open.pRank 3 (A₁ ⊓ As) := by
          omega
        have hmin : min (CFSG.Open.pRank 3 E) (CFSG.Open.pRank 3 A) =
            min (CFSG.Open.pRank 3 A₁) (CFSG.Open.pRank 3 As) := by
          omega
        have hdA : CFSG.Open.pRank 3 A = CFSG.Open.pRank 3 As := by
          omega
        apply Prod.Lex.toLex_le_toLex.2
        right
        refine ⟨hfirst, ?_⟩
        apply Prod.Lex.toLex_le_toLex.2
        right
        refine ⟨hmin, ?_⟩
        apply Prod.Lex.toLex_le_toLex.2
        rcases lt_or_eq_of_le (show CFSG.Open.pRank 3 E ≤ CFSG.Open.pRank 3 A₁ by omega)
          with hc | hc
        · left
          exact hc
        · right
          refine ⟨hc, ?_⟩
          apply Prod.Lex.toLex_le_toLex.2
          right
          refine ⟨hdA, ?_⟩
          rw [if_pos hAsP]
          split_ifs <;> omega
      have hpair : IsDDpStar 3 M A₁ As :=
        ⟨hdd, fun E' A' hE' => (hEA.2 E' A' hE').trans hkey⟩
      exact h121 { toSec10Fails := h.toSec10Fails, pair := hpair }
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) hx1

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

