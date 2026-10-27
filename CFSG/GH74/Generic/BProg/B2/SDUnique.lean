module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.B2.SDOrders

import CFSG.GH74.GLS.SP.Local.SPLRankTools
import CFSG.GH74.Generic.BProg.B2.SDRank
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyBasic

public section

namespace CFSG.GH74.Generic.BProg.B2.SD2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.BProg.B2.SD (centBarK)

namespace SDUnique

theorem exists_surjective_sup {X : Type} [Group X] [Finite X] {J₁ J₂ : Subgroup X}
    (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) :
    ∃ (Y : Subgroup X) (π : ↥Y →* (↥J₁ ⧸ center ↥J₁) × (↥J₂ ⧸ center ↥J₂)),
      Y ≤ J₁ ⊔ J₂ ∧ Function.Surjective π := by
  classical
  let θ : ↥J₁ × ↥J₂ →* X :=
    MonoidHom.noncommCoprod J₁.subtype J₂.subtype (fun a b => hc a a.2 b b.2)
  let ρ : ↥J₁ × ↥J₂ →* (↥J₁ ⧸ center ↥J₁) × (↥J₂ ⧸ center ↥J₂) :=
    (QuotientGroup.mk' (center ↥J₁)).prodMap (QuotientGroup.mk' (center ↥J₂))
  have hker : θ.rangeRestrict.ker ≤ ρ.ker := by
    rintro ⟨a, b⟩ hab
    have h1 : (a : X) * (b : X) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.1 hab)
      have e : θ (a, b) = (a : X) * (b : X) := rfl
      exact e ▸ h
    have ha2 : (a : X) ∈ J₂ := by
      have : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact J₂.inv_mem b.2
    have hb1 : (b : X) ∈ J₁ := by
      have : (b : X) = (a : X)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact J₁.inv_mem a.2
    have ha : a ∈ center ↥J₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2 a ha2)
    have hb : b ∈ center ↥J₂ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc b hb1 g g.2).symm
    rw [MonoidHom.mem_ker]
    exact Prod.ext ((QuotientGroup.eq_one_iff a).2 ha) ((QuotientGroup.eq_one_iff b).2 hb)
  have hρ : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).prodMap (QuotientGroup.mk'_surjective _)
  let π := MonoidHom.liftOfSurjective θ.rangeRestrict θ.rangeRestrict_surjective ⟨ρ, hker⟩
  refine ⟨θ.range, π, ?_, ?_⟩
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact Subgroup.mul_mem_sup a.2 b.2
  · intro y
    obtain ⟨z, rfl⟩ := hρ y
    exact ⟨θ.rangeRestrict z, by simp [π]⟩

theorem isQuasisimple_quotient_center {J : Type} [Group J] (hJ : IsQuasisimple J) :
    IsQuasisimple (J ⧸ center J) := by
  have : IsSimpleGroup (J ⧸ center J) := hJ.2.1
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hJ.2.2).1

theorem lt_card_of_qShape3 {Kt : Type} [Group Kt] [Finite Kt] (h : QShape3 Kt) :
    7920 < Nat.card Kt := by
  obtain ⟨p, f, hp, hp2, hq, h | h⟩ := h
  · rw [card_of_lieModel_PSL (by norm_num) h]
    exact SDOrders.lt_ordA hq
  · rw [card_of_lieModel_PSU (by norm_num) hp2 h]
    exact SDOrders.lt_ordTwistedA hq

variable {G : Type} [Group G] [Finite G]

theorem perfect_of_setup {x : G} {K A M P Q : Subgroup G} (hs : Stage2Setup G x K A M P Q) :
    ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hs.pair.1.1.1.2.2
  have hp : Group.IsPerfect (K.subgroupOf (centralizer ({x} : Set G))) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hK.2
  have hp' : Group.IsPerfect ↥K := by
    have e := Subgroup.subgroupOfEquivOfLe hK.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.isPerfect_def.1 hp'

end SDUnique

variable {G : Type} [Group G] [Finite G]

theorem component_eq_of_ne_barK {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hc1 : barIn M H = barIn M K) {J₁ J₂ : Subgroup (Mbar M)} (hJ₁ : IsComponent J₁)
    (hJ₂ : IsComponent J₂) (h₁ : J₁ ≠ barIn M K) (h₂ : J₂ ≠ barIn M K) : J₁ = J₂ := by
  classical
  by_contra hne
  obtain ⟨-, hother⟩ := Thm2AssemblyBasic.components_c1 hs h1 hc1
  have hle₁ : J₁ ≤ centBarK M K := hother J₁ hJ₁ h₁
  have hle₂ : J₂ ≤ centBarK M K := hother J₂ hJ₂ h₂
  have hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := by
    have h := (CFSG.LocalCores.distinct_components_commute hJ₁ hJ₂).resolve_left hne
    have hle : J₁ ≤ centralizer (J₂ : Set (Mbar M)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm
  obtain ⟨Y, π, hY, hπ⟩ := SDUnique.exists_surjective_sup hcomm
  have hrank : SectionalTwoRankLE ↥Y 2 :=
    SD.sectionalRank_le_two_of_le_centBarK hs h1 h3 (hY.trans (sup_le hle₁ hle₂))
  have hrank' := SectionalTwoRankLE.of_surjective π hπ hrank
  have hq₁ := SDUnique.isQuasisimple_quotient_center hJ₁.1
  have hq₂ := SDUnique.isQuasisimple_quotient_center hJ₂.1
  have hcert := ((GLS.SP.Local.rankCertified_one_of_quasisimple hq₁).prod
    (GLS.SP.Local.rankCertified_one_of_quasisimple hq₂)).mono (show 2 ≤ 1 + 1 + 1 by norm_num)
  exact hcert.not_sectionalTwoRankLE hrank'

theorem normal_of_smallAut {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) (hc1 : barIn M H = barIn M K) {J : Subgroup (Mbar M)}
    (hJ : IsComponent J) (hJK : J ≠ barIn M K) (hJs : SmallAut ↥J) : J.Normal := by
  classical
  obtain ⟨φ, hφ, -⟩ := SD.SDRank.exists_cover h1.K_le
  have key : ∀ d : Mbar M, conjugate J d = J := by
    intro d
    by_cases hd : conjugate J d = barIn M K
    · exfalso
      let e : ↥J ≃* ↥(barIn M K) :=
        (Subgroup.equivMapOfInjective J (MulAut.conj d⁻¹).toMonoidHom
          (MulAut.conj d⁻¹).injective).trans (MulEquiv.subgroupCongr hd)
      let ψ : ↥K →* ↥J ⧸ center ↥J :=
        (QuotientGroup.mk' (center ↥J)).comp (e.symm.toMonoidHom.comp φ)
      have hψ : Function.Surjective ψ :=
        (QuotientGroup.mk'_surjective _).comp (e.symm.surjective.comp hφ)
      have hsimp : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) :=
        B1.PilotS3.isSimpleGroup_of_qShape3 h3
      have hcard : Nat.card (MulAut (↥J ⧸ center ↥J)) < Nat.card (↥K ⧸ pPrimeCore 2 ↥K) :=
        (card_mulAut_le_of_smallAut hJs).trans_lt (SDUnique.lt_card_of_qShape3 h3)
      have h1' : (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).comp ψ = 1 :=
        eq_one_of_card_lt (SDUnique.perfect_of_setup hs) hsimp hcard _
      obtain ⟨-, -, a, b, hab⟩ := hJ.1
      obtain ⟨ka, rfl⟩ := hψ a
      obtain ⟨kb, rfl⟩ := hψ b
      apply hab
      have h2 := DFunLike.congr_fun (DFunLike.congr_fun h1' ka) (ψ kb)
      simp only [MonoidHom.comp_apply, MulAut.conj_apply, MonoidHom.one_apply,
        MulAut.one_apply] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2
    · exact component_eq_of_ne_barK hs h1 h3 hc1 (Thm2AssemblyBasic.isComponent_conjugate hJ d)
        hJ hd hJK
  refine ⟨fun n hn g => ?_⟩
  have hmem : g * n * g⁻¹ ∈ conjugate J g⁻¹ := ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rwa [key g⁻¹] at hmem

end CFSG.GH74.Generic.BProg.B2.SD2
