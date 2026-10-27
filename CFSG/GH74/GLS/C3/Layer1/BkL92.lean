module

public import CFSG.GH74.GLS.C3.Layer1.BkL92Stmt
public import CFSG.GH74.GLS.C3.Layer1.BkL92Lift
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer2.GenLemmas

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

theorem pRank_two_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : CFSG.pRank 2 A = CFSG.pRank 2 B := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def actV {L M : Subgroup G} (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (V : Subgroup G) (hVM : V ≤ M) : ↥V →* MulAut (kBar L) :=
  (Back.actHom hLn).comp (Subgroup.inclusion hVM)

theorem actV_mk {L M : Subgroup G} (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) {V : Subgroup G}
    (hVM : V ≤ M) (v : ↥V) (l : ↥L) :
    actV hLn V hVM v (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨(v : G) * l * (v : G)⁻¹, hLn v (hVM v.2) l l.2⟩ : ↥L) := rfl

theorem actV_injective {L M V : Subgroup G} (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hVM : V ≤ M) (hbot : V ⊓ CMK M L = ⊥) : Function.Injective (actV hLn V hVM) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have h2 : Subgroup.inclusion hVM v ∈ (Back.actHom hLn).ker := hv
  rw [Back.actHom_ker hLn, Subgroup.mem_subgroupOf] at h2
  have h3 : (v : G) ∈ V ⊓ CMK M L := ⟨v.2, h2⟩
  rw [hbot] at h3
  exact Subtype.ext (Subgroup.mem_bot.1 h3)

@[expose] def barImg (L S : Subgroup G) : Subgroup (kBar L) :=
  (S.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L))

theorem mem_barImg_iff {L S : Subgroup G} {kb : kBar L} :
    kb ∈ barImg L S ↔ ∃ l : ↥L, (l : G) ∈ S ∧ (QuotientGroup.mk l : kBar L) = kb := by
  unfold barImg
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply]

theorem le_of_barImg_eq_top {L S : Subgroup G} (hO : pPrimeCoreOf 2 L ≤ S)
    (h : barImg L S = ⊤) : L ≤ S := by
  intro l hl
  have hmem : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : kBar L) ∈ barImg L S := by
    rw [h]
    trivial
  obtain ⟨g, hgS, hgl⟩ := mem_barImg_iff.1 hmem
  have h1 : g⁻¹ * (⟨l, hl⟩ : ↥L) ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.1 hgl
  have h2 : (g : G)⁻¹ * l ∈ pPrimeCoreOf 2 L :=
    Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨L.mul_mem (L.inv_mem g.2) hl, h1⟩
  have e : l = (g : G) * ((g : G)⁻¹ * l) := by group
  rw [e]
  exact S.mul_mem hgS (hO h2)

theorem gammaAut_le_barImg [Finite G] {L M V : Subgroup G}
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hVM : V ≤ M)
    (hψ : Function.Injective (actV hLn V hVM)) :
    gammaAut (kBar L) (actV hLn V hVM).range ≤ barImg L (gammaIn L V) := by
  have hfix : ∀ w ∈ (actV hLn V hVM).range, orderOf w = 2 →
      fixSub (kBar L) w ≤ barImg L (gammaIn L V) := by
    intro w hw ho kb hk
    obtain ⟨v, rfl⟩ := hw
    have hv2 : orderOf (v : G) = 2 := by
      rw [Subgroup.orderOf_coe, ← orderOf_injective _ hψ v]
      exact ho
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective kb
    have hk' : actV hLn V hVM v (QuotientGroup.mk l') = QuotientGroup.mk l' := hk
    rw [actV_mk, QuotientGroup.eq_iff_div_mem] at hk'
    have hdiv : ((⟨(v : G) * l' * (v : G)⁻¹, hLn v (hVM v.2) l' l'.2⟩ : ↥L) / l' : ↥L) =
        ⟨(v : G) * l' * (v : G)⁻¹ * (l' : G)⁻¹,
          L.mul_mem (hLn v (hVM v.2) l' l'.2) (L.inv_mem l'.2)⟩ :=
      Subtype.ext (by simp [div_eq_mul_inv])
    rw [hdiv] at hk'
    have hfixO : (v : G) * l' * (v : G)⁻¹ * (l' : G)⁻¹ ∈ pPrimeCoreOf 2 L :=
      Back.Setup91.mem_pPrimeCoreOf_iff.2
        ⟨L.mul_mem (hLn v (hVM v.2) l' l'.2) (L.inv_mem l'.2), hk'⟩
    obtain ⟨c, hcγ, hcO⟩ := exists_mem_gammaIn_of_fixed hLn hVM v.2 hv2 l'.2 hfixO
    have hcL : c ∈ L := gammaIn_le L V hcγ
    refine mem_barImg_iff.2 ⟨⟨c, hcL⟩, hcγ, ?_⟩
    obtain ⟨hh, hh2⟩ := Back.Setup91.mem_pPrimeCoreOf_iff.1 hcO
    exact (QuotientGroup.eq.2 hh2).symm
  exact iSup_le fun w => iSup_le fun hw => iSup_le fun ho => hfix w hw ho

theorem gammaAut_ne_top [Finite G] {L M V : Subgroup G}
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hVM : V ≤ M) (hV : 2 ≤ pRank 2 ↥V)
    (hΓ : gammaIn L V ≠ L) (hψ : Function.Injective (actV hLn V hVM)) :
    gammaAut (kBar L) (actV hLn V hVM).range ≠ ⊤ := by
  intro htop
  apply hΓ
  refine le_antisymm (gammaIn_le L V) (le_of_barImg_eq_top (pPrimeCoreOf_le_gammaIn hLn hVM hV) ?_)
  have := gammaAut_le_barImg hLn hVM hψ
  rw [htop] at this
  exact top_le_iff.1 this

theorem le_sup_of_range_le_conj {L M V : Subgroup G} (hLM : L ≤ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hVM : V ≤ M)
    (hc : (actV hLn V hVM).range ≤ (MulAut.conj : kBar L →* MulAut (kBar L)).range) :
    V ≤ L ⊔ CMK M L := by
  intro v hv
  obtain ⟨kb, hkb⟩ := hc (MonoidHom.mem_range.2 ⟨⟨v, hv⟩, rfl⟩)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective kb
  have hlM : (l : G) ∈ M := hLM l.2
  have h1 : Back.actHom hLn (Subgroup.inclusion hVM ⟨v, hv⟩) = Back.actHom hLn ⟨(l : G), hlM⟩ := by
    rw [Back.actHom_of_mem hLn l.2 hlM]
    exact hkb.symm
  have h2 : (Subgroup.inclusion hVM ⟨v, hv⟩ : ↥M) * (⟨(l : G), hlM⟩ : ↥M)⁻¹ ∈
      (Back.actHom hLn).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  rw [Back.actHom_ker hLn, Subgroup.mem_subgroupOf] at h2
  have e : v = (v * (l : G)⁻¹) * l := by group
  rw [e]
  exact (L ⊔ CMK M L).mul_mem (mem_sup_right h2) (mem_sup_left l.2)

theorem range_le_conj_of_le_sup {L M V : Subgroup G} (hLM : L ≤ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hVM : V ≤ M) (hV : V ≤ L ⊔ CMK M L) :
    (actV hLn V hVM).range ≤ (MulAut.conj : kBar L →* MulAut (kBar L)).range := by
  rintro _ ⟨v, rfl⟩
  have hCN : CMK M L ≤ normalizer (L : Set G) := fun c hc => (U1a.mem_CMK_iff.1 hc).2.1
  have hv : (v : G) ∈ ((L ⊔ CMK M L : Subgroup G) : Set G) := hV v.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L (CMK M L) hCN] at hv
  obtain ⟨l, hl, c, hc, hlc⟩ := hv
  have hlM : l ∈ M := hLM hl
  have hcM : c ∈ M := (U1a.mem_CMK_iff.1 hc).1
  have hvmem : (Subgroup.inclusion hVM v : ↥M) = ⟨l, hlM⟩ * ⟨c, hcM⟩ := Subtype.ext hlc.symm
  have hρc : Back.actHom hLn ⟨c, hcM⟩ = 1 := by
    rw [← MonoidHom.mem_ker, Back.actHom_ker hLn, Subgroup.mem_subgroupOf]
    exact hc
  show Back.actHom hLn (Subgroup.inclusion hVM v) ∈ _
  rw [hvmem, map_mul, Back.actHom_of_mem hLn hl hlM, hρc, mul_one]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

end Action

theorem b_lemma92_of_ivk6 (h6 : B_ivk_6) : B_lemma92 := by
  intro G _ _ L M V hLM hLn hshape hV2 hVM hV hΓ
  have hbot : V ⊓ CMK M L = ⊥ := inf_CMK_eq_bot hLn hV2 hVM hV hΓ
  have hψ := actV_injective hLn hVM hbot
  have e : ↥V ≃* ↥(actV hLn V hVM).range := MonoidHom.ofInjective hψ
  have hW2 : IsPGroup 2 ↥(actV hLn V hVM).range :=
    hV2.of_surjective (actV hLn V hVM).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have hWr : 2 ≤ CFSG.pRank 2 ↥(actV hLn V hVM).range := by
    have : Finite ↥(actV hLn V hVM).range := Finite.of_equiv _ e.toEquiv
    rw [← pRank_two_eq_of_mulEquiv e]
    exact hV
  obtain ⟨ha, ⟨hb1, hb2⟩, hc⟩ := h6 (kBar L) (actV hLn V hVM).range hshape hW2 hWr
    (gammaAut_ne_top hLn hVM hV hΓ hψ)
  refine ⟨ha, ⟨?_, ?_⟩, le_sup_of_range_le_conj hLM hLn hVM hc, hbot⟩
  · have := hb1
    exact C3.Layer2.isElementaryAbelian_of_mulEquiv e.symm
  · rw [Nat.card_congr e.toEquiv]
    exact hb2

end CFSG.GH74.GLS.C3.Layer1.Bk
