module

import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Layer
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.TBLit

section Transport

variable {Y T : Type} [Group Y] [Group T]

theorem congr_conj_iso (e : Y ≃* T) (g : Y) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem hbar_map (e : Y ≃* T) (V : Subgroup (MulAut Y)) (z : MulAut Y) :
    hbar T (V.map (MulAut.congr e).toMonoidHom) (MulAut.congr e z) =
      (hbar Y V z).map (MulAut.congr e).toMonoidHom := by
  unfold hbar
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
  congr 2
  ext φ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨MulAut.conj (e.symm g), ⟨e.symm g, rfl⟩, by
      simp only [MulEquiv.coe_toMonoidHom, congr_conj_iso, MulEquiv.apply_symm_apply]⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, by simp only [MulEquiv.coe_toMonoidHom, congr_conj_iso]⟩

theorem no911_of_mulEquiv (e : Y ≃* T) (h : No911 T) : No911 Y := by
  rintro p V z ⟨hp, hpodd, hVe, hVc, hz1, hzz, hVz, ⟨O, hOH, hVO, hOodd, hOz, hON⟩, hH2⟩
  have : Fact p.Prime := ⟨hp⟩
  set F : MulAut Y ≃* MulAut T := MulAut.congr e with hF
  refine h p (V.map F.toMonoidHom) (F z) ⟨hp, hpodd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hVe
    exact IsElementaryAbelian.map F.toMonoidHom
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective V F.toMonoidHom F.injective).toEquiv, hVc]
  · exact fun h1 => hz1 (F.injective (by rw [h1, map_one]))
  · rw [← map_mul, hzz, map_one]
  · rintro _ ⟨v, hv, rfl⟩
    show F v * F z = F z * F v
    rw [← map_mul, ← map_mul, hVz v hv]
  · refine ⟨O.map F.toMonoidHom, ?_, Subgroup.map_mono hVO, ?_, ?_, ?_⟩
    · rw [hF, hbar_map]
      exact Subgroup.map_mono hOH
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective O F.toMonoidHom F.injective).toEquiv]
      exact hOodd
    · rintro _ ⟨o, ho, rfl⟩
      show F o * F z = F z * F o
      rw [← map_mul, ← map_mul, hOz o ho]
    · intro c' hc' hcz o' ho'
      rw [hF, hbar_map] at hc'
      obtain ⟨c, hc, rfl⟩ := hc'
      obtain ⟨o, ho, rfl⟩ := ho'
      have hcz' : c * z = z * c := by
        apply F.injective
        rw [map_mul, map_mul]
        exact hcz
      exact ⟨c * o * c⁻¹, hON c hc hcz' o ho, by
        show F (c * o * c⁻¹) = F c * F o * (F c)⁻¹
        rw [map_mul, map_mul, map_inv]⟩
  · rintro _ ⟨v, hv, rfl⟩ hne
    have hne' : v ≠ 1 := fun h1 => hne (by rw [h1, map_one])
    have h1 := hH2 v hv hne'
    have hfix : fixSub (F.toMonoidHom v) = (fixSub v).map e.toMonoidHom :=
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.fixSub_congr e v).symm
    rw [hfix]
    exact layer_eq_bot_of_mulEquiv_of_layer_eq_bot
      (Subgroup.equivMapOfInjective (fixSub v) e.toMonoidHom e.injective) h1

end Transport

section Cyclic

@[expose] def OddCoreCyclic (T : Type) [Group T] : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B → ∀ t ∈ B, orderOf t = 2 →
    IsCyclic ↥(oddCoreIn B t)

theorem isCyclic_of_le_range {M C : Type} [Group M] [Group C] [IsCyclic C] (φ : C →* M)
    {W : Subgroup M} (hW : W ≤ φ.range) : IsCyclic ↥W := by
  have h1 : IsCyclic ↥φ.range := isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have h2 : IsCyclic ↥(W.subgroupOf φ.range) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hW).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hW).surjective

theorem oddCoreIn_eq_bot_of_forall {G : Type} [Group G] [Finite G] {B : Subgroup G} {t : G}
    (ht : t ∈ B)
    (h : ∀ Y : Subgroup ↥B, Y ≤ oddCentralizerCore (⟨t, ht⟩ : ↥B) → Y = ⊥) :
    oddCoreIn B t = ⊥ := by
  have hinj : Function.Injective B.subtype := Subtype.val_injective
  have h1 := map_oddCentralizerCore_of_injective hinj (⟨t, ht⟩ : ↥B)
  rw [Subgroup.range_subtype] at h1
  have h2 : oddCentralizerCore (⟨t, ht⟩ : ↥B) = ⊥ := h _ le_rfl
  have h3 : oddCoreIn B t = (oddCentralizerCore (⟨t, ht⟩ : ↥B)).map B.subtype := h1.symm
  rw [h3, h2, Subgroup.map_bot]

theorem no911_of_oddCoreCyclic {Y : Type} [Group Y] [Finite Y] (h : OddCoreCyclic Y) :
    No911 Y := by
  rintro p V z ⟨hp, hpodd, hVe, hVc, hz1, hzz, hVz, ⟨O, hOH, hVO, hOodd, hOz, hON⟩, -⟩
  have : Fact p.Prime := ⟨hp⟩
  have hinn : (MulAut.conj : Y →* MulAut Y).range ≤ hbar Y V z := le_trans le_sup_left le_sup_left
  have hzH : z ∈ hbar Y V z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hord : orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hcyc := h (hbar Y V z) hinn z hzH hord
  set C : Subgroup (MulAut Y) := hbar Y V z ⊓ centralizer ({z} : Set (MulAut Y)) with hC
  have hOC : O ≤ C := by
    intro o ho
    exact ⟨hOH ho, Subgroup.mem_centralizer_singleton_iff.mpr (hOz o ho)⟩
  have hnorm : (O.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgz : (g : MulAut Y) * z = z * (g : MulAut Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp g.2.2
    exact hON _ g.2.1 hgz _ hn
  have hodd' : Odd (Nat.card ↥(O.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv]
    exact hOodd
  have hle : O.subgroupOf C ≤ pPrimeCore 2 ↥C :=
    le_sSup ⟨hnorm, Nat.coprime_two_left.mpr hodd'⟩
  have hOW : O ≤ oddCoreIn (hbar Y V z) z := by
    intro o ho
    have h1 : (⟨o, hOC ho⟩ : ↥C) ∈ O.subgroupOf C := ho
    exact ⟨⟨o, hOC ho⟩, hle h1, rfl⟩
  have hVW : V ≤ oddCoreIn (hbar Y V z) z := hVO.trans hOW
  have hVcyc : IsCyclic ↥V := by
    have : IsCyclic ↥((V.subgroupOf (oddCoreIn (hbar Y V z) z))) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hVW).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hVW).surjective
  have hfin : Finite ↥V :=
    Nat.finite_of_card_ne_zero (by rw [hVc]; exact pow_ne_zero 2 hp.ne_zero)
  have := hVe
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hVc hVcyc

end Cyclic

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
