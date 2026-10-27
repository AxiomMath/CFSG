module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1XBase
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1Basic
import CFSG.LocalAnalysis.GLTheoremB.BaseCase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {f : ℕ} {X Q : Subgroup G}

@[expose] noncomputable def k631aBarHom (f : ℕ) {X J : Subgroup G} (hJX : J ≤ X) :
    ↥J →* ↥(barX f X J) :=
  ((QuotientGroup.mk' (GLAPPrimeCore f ↥X)).comp (Subgroup.inclusion hJX)).codRestrict
    (barX f X J) (fun x => ⟨⟨x, hJX x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)

omit [Finite G] in
theorem k631a_barHom_surjective {X J : Subgroup G} (hJX : J ≤ X) :
    Function.Surjective (k631aBarHom f hJX) := by
  rintro ⟨_, ⟨⟨l, hlX⟩, hl, rfl⟩⟩
  exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩

theorem k631a_lift (h : k631aHyp f X Q) {J : Subgroup G} (hJ : GLAPComponent f X J)
    {z : ↥X ⧸ GLAPPrimeCore f ↥X} (hzQ : z ∈ barX f X Q) (hzJ : z ∈ barX f X J) :
    ∃ (s : G) (hs : s ∈ X), s ∈ Q ∧ s ∈ J ∧ k631aMk f X s hs = z := by
  have := Fact.mk h.prime
  have hB := k631a_bhyp_barX h
  have hJc := k631a_isComponent_barX hJ
  obtain ⟨P, hP⟩ := k631a_sylow_comp h hJ
  obtain ⟨P', hP'⟩ := k631a_sylow_inf hB hJc.2
  have hθ := k631a_barHom_surjective (f := f) hJ.1
  let T : Sylow f ↥(barX f X J) := P.mapSurjective hθ
  have hTle : (T : Subgroup ↥(barX f X J)) ≤ P' := by
    rintro _ ⟨x, hx, rfl⟩
    refine (k631a_mem_sylow_iff hP' _).2 ?_
    have hxQ : (x : G) ∈ Q := ((k631a_mem_sylow_iff hP x).1 hx)
    exact k631a_mk_mem_barX (K := Q) (hJ.1 x.2) hxQ
  have hPT : (P' : Subgroup ↥(barX f X J)) ≤ T := (T.is_maximal' P'.isPGroup' hTle).le
  have hzP : (⟨z, hzJ⟩ : ↥(barX f X J)) ∈ P' := (k631a_mem_sylow_iff hP' _).2 hzQ
  obtain ⟨x, hxP, hx⟩ := hPT hzP
  have hxQ : (x : G) ∈ Q := (k631a_mem_sylow_iff hP x).1 hxP
  exact ⟨(x : G), hJ.1 x.2, hxQ, x.2, congrArg Subtype.val hx⟩

theorem k631a_comp_sylow (h : k631aHyp f X Q) {J : Subgroup G} (hJ : GLAPComponent f X J) :
    ¬ f ∣ ((Q ⊓ J).subgroupOf J).index := by
  have := Fact.mk h.prime
  obtain ⟨P, hP⟩ := k631a_sylow_comp h hJ
  have e : (Q ⊓ J).subgroupOf J = (P : Subgroup J) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  rw [e]
  exact P.not_dvd_index

theorem k631a_comp_inner (hInn : KFactInnerAction) (h : k631aHyp f X Q) {J : Subgroup G}
    (hJ : GLAPComponent f X J) {q : G} (hq : q ∈ Q) :
    ∃ s ∈ Q ⊓ J, q * s⁻¹ ∈ k631Triv (GLAPPrimeCoreOf f X) J := by
  have hqX : q ∈ X := h.le hq
  obtain ⟨z, hzQJ, hz⟩ := k631a_inner hInn (k631a_bhyp_barX h) (k631a_isComponent_barX hJ)
    (k631a_mk_mem_barX (K := Q) hqX hq)
  obtain ⟨s, hsX, hsQ, hsJ, rfl⟩ := k631a_lift h hJ hzQJ.1 hzQJ.2
  refine ⟨s, ⟨hsQ, hsJ⟩, ?_⟩
  have hqsX : q * s⁻¹ ∈ X := X.mul_mem hqX (X.inv_mem hsX)
  have hN : q * s⁻¹ ∈ normalizer (J : Set G) :=
    Subgroup.mul_mem _ (k631a_normalized h hJ hq)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hsJ))
  rw [k631a_mem_triv_iff hJ.1 hqsX hN]
  intro j hj
  have hb : k631aMk f X s hsX ∈ barX f X J := k631a_mk_mem_barX hsX hsJ
  have hj' : (k631aMk f X s hsX)⁻¹ * j * k631aMk f X s hsX ∈ barX f X J :=
    (barX f X J).mul_mem ((barX f X J).mul_mem ((barX f X J).inv_mem hb) hj) hb
  have e := hz _ hj'
  have hm : k631aMk f X (q * s⁻¹) hqsX = k631aMk f X q hqX * (k631aMk f X s hsX)⁻¹ := by
    rw [← k631a_mk_inv hsX, ← k631a_mk_mul hqX (X.inv_mem hsX)]
  rw [hm]
  set a := k631aMk f X q hqX
  set b := k631aMk f X s hsX
  calc a * b⁻¹ * j = (a * (b⁻¹ * j * b) * a⁻¹) * (a * b⁻¹) := by group
    _ = (b * (b⁻¹ * j * b) * b⁻¹) * (a * b⁻¹) := by rw [e]
    _ = j * (a * b⁻¹) := by group

theorem k631a_triv_inf (h : k631aHyp f X Q) {J : Subgroup G} (hJ : GLAPComponent f X J) :
    Q ⊓ J ⊓ k631Triv (GLAPPrimeCoreOf f X) J = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨hgQ, hgJ⟩, hgT⟩
  have hgX : g ∈ X := h.le hgQ
  have hgT' : g ∈ normalizer (GLAPPrimeCoreOf f X : Set G) ∧ g ∈ normalizer (J : Set G) ∧
      ∀ j ∈ J, ⁅g, j⁆ ∈ GLAPPrimeCoreOf f X := hgT
  have hc := (k631a_mem_triv_iff hJ.1 hgX hgT'.2.1).1 hgT
  have h1 : k631aMk f X g hgX = 1 :=
    k631a_eq_one_of_central (k631a_bhyp_barX h) (k631a_isComponent_barX hJ)
      (k631a_mk_mem_barX hgX hgJ) hc
  have hgO : g ∈ GLAPPrimeCoreOf f X := (k631a_mem_core_iff hgX).2 h1
  have hcop : Nat.Coprime f (Nat.card (GLAPPrimeCoreOf f X)) :=
    (Nat.Prime.coprime_iff_not_dvd h.prime).2 (not_dvd_card_glaPPrimeCoreOf h.prime X)
  exact (Subgroup.mem_bot).2 (k631a_eq_one_of_mem_inf h.pgroup hcop hgQ hgO)

theorem k631a_decomp (hInn : KFactInnerAction) (h : k631aHyp f X Q) {J : Subgroup G}
    (hJ : GLAPComponent f X J) :
    Q ≤ (Q ⊓ J) ⊔ (Q ⊓ k631Triv (GLAPPrimeCoreOf f X) J) := by
  intro q hq
  obtain ⟨s, hs, hsT⟩ := k631a_comp_inner hInn h hJ hq
  have h1 : q * s⁻¹ ∈ Q ⊓ k631Triv (GLAPPrimeCoreOf f X) J :=
    ⟨Q.mul_mem hq (Q.inv_mem hs.1), hsT⟩
  have e : q = (q * s⁻¹) * s := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hs)

end CFSG.LocalAnalysis.RankThreeTheoremC
