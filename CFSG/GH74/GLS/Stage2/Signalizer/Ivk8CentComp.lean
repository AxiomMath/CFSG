module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8CompNC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools

namespace CentComp

theorem not_le_centralizer_self {A : Type*} [Group A] {J : Subgroup A} (hq : IsQuasisimple ↥J) :
    ¬ J ≤ centralizer (J : Set A) := by
  intro h
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (h b'.2) a' a'.2

end CentComp

theorem AFrame.cent_comp_cases {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hu : ∀ K : Subgroup A, IsComponent K → K = J)
    (hzc : Nat.card ↥(Sb ⊓ centralizer (J : Set A)) ≤ 2) :
    centralizer (J : Set A) = ⊥ ∨ centralizer (J : Set A) = Subgroup.zpowers zb := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJn : J.Normal := Gen.normal_of_unique_comp hJ hu
  set C : Subgroup A := centralizer (J : Set A) with hC
  have hCn : C.Normal := by
    rw [hC]
    infer_instance
  have hcoreC : pPrimeCore 2 ↥C = ⊥ := by
    have hN : (pPrimeCore 2 ↥C).map C.subtype ≤ pPrimeCore 2 A := by
      refine le_sSup ⟨inferInstance, ?_⟩
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact pPrimeCore_coprime_card
    rw [hfr.core, le_bot_iff] at hN
    exact (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥C) C.subtype_injective).mp hN
  have hlayerC : layer ↥C = ⊥ := by
    refine CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => ?_
    have hK'q : IsQuasisimple ↥(K.map C.subtype) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (K.equivMapOfInjective C.subtype C.subtype_injective) hK.1
    have hsub : (K.map C.subtype).subgroupOf C = K :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective K
    have hK'sn : (K.map C.subtype).IsSubnormal :=
      Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le K) (by rw [hsub]; exact hK.2)
        (Subgroup.Normal.isSubnormal hCn)
    have hKJ : K.map C.subtype = J := hu _ ⟨hK'q, hK'sn⟩
    have hJC : J ≤ centralizer (J : Set A) := by
      have h1 : K.map C.subtype ≤ C := Subgroup.map_subtype_le K
      rw [hKJ] at h1
      exact h1
    exact CentComp.not_le_centralizer_self hJ.1 hJC
  have hchar : IsCharacteristicP 2 ↥C :=
    isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥C 2 hcoreC hlayerC
  have hQn : ((pCore 2 ↥C).map C.subtype).Normal := inferInstance
  have hQ2 : IsPGroup 2 ↥((pCore 2 ↥C).map C.subtype) := pCore_isPGroup.map C.subtype
  have hQSb : (pCore 2 ↥C).map C.subtype ≤ Sb := by
    obtain ⟨Qs, hQs⟩ := CompNC.exists_sylow_of_isSylowOf_top hfr.sylow
    rw [← hQs]
    exact IsPGroup.le_sylow_of_normal hQ2 Qs
  have hQC : (pCore 2 ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hcard : Nat.card ↥((pCore 2 ↥C).map C.subtype) ≤ 2 :=
    (Subgroup.card_le_of_le (le_inf hQSb hQC)).trans hzc
  have hcent : ∀ c : ↥C, (∀ h ∈ pCore 2 ↥C, h * c = c * h) → c ∈ pCore 2 ↥C := fun c hc =>
    hchar (Subgroup.mem_centralizer_iff.mpr hc)
  have hpos : 0 < Nat.card ↥((pCore 2 ↥C).map C.subtype) := Nat.card_pos
  have hcases : Nat.card ↥((pCore 2 ↥C).map C.subtype) = 1 ∨
      Nat.card ↥((pCore 2 ↥C).map C.subtype) = 2 := by omega
  rcases hcases with h1 | h2'
  ·
    left
    have hQ' : (pCore 2 ↥C).map C.subtype = ⊥ := Subgroup.card_eq_one.mp h1
    have hQ : pCore 2 ↥C = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (pCore 2 ↥C) C.subtype_injective).mp hQ'
    refine eq_bot_iff.mpr fun c hc => ?_
    have hc1 : (⟨c, hc⟩ : ↥C) ∈ pCore 2 ↥C := by
      refine hcent _ fun h hh => ?_
      rw [hQ, Subgroup.mem_bot] at hh
      rw [hh]
      simp
    rw [hQ, Subgroup.mem_bot] at hc1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hc1)
  ·
    right
    set Q' := (pCore 2 ↥C).map C.subtype with hQ'def
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q') 2 (by rw [h2'])
    have hq2 : orderOf (x : A) = 2 := by rw [Subgroup.orderOf_coe, hx]
    have hqQ : (x : A) ∈ Q' := x.2
    have hzp : Subgroup.zpowers (x : A) = Q' := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · exact Subgroup.zpowers_le.mpr hqQ
      · rw [Nat.card_zpowers, hq2, h2']
    have hx1 : (x : ↥Q') ≠ 1 := by
      intro h
      have : (x : A) = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hq2
      exact absurd hq2 (by norm_num)
    have hqc : ∀ a : A, a * (x : A) = (x : A) * a := by
      intro a
      obtain ⟨y₀, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥Q')).mp h2'
      have hconj : a * (x : A) * a⁻¹ ∈ Q' := hQn.conj_mem _ hqQ a
      have hne : (⟨a * (x : A) * a⁻¹, hconj⟩ : ↥Q') ≠ 1 := by
        intro h
        apply hx1
        have h' : a * (x : A) * a⁻¹ = 1 := congrArg Subtype.val h
        apply Subtype.ext
        calc (x : A) = a⁻¹ * (a * (x : A) * a⁻¹) * a := by group
          _ = 1 := by rw [h']; group
      have heq := (huniq _ hne).trans (huniq _ hx1).symm
      have h'' : a * (x : A) * a⁻¹ = (x : A) := congrArg Subtype.val heq
      calc a * (x : A) = a * (x : A) * a⁻¹ * a := by group
        _ = (x : A) * a := by rw [h'']
    have hzb : (x : A) = zb := hfr.zcen _ (hQSb hqQ) (fun s _ => hqc s) hq2
    have hQcen : Q' ≤ center A := by
      rw [← hzp]
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hqc)
    have hCle : C ≤ Q' := by
      intro c hc
      have hc1 : (⟨c, hc⟩ : ↥C) ∈ pCore 2 ↥C := by
        refine hcent _ fun h hh => ?_
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (hQcen (show (h : A) ∈ Q' from ⟨h, hh, rfl⟩)) c).symm
      exact ⟨⟨c, hc⟩, hc1, rfl⟩
    have hzbQ : Subgroup.zpowers zb = Q' := by rw [← hzb]; exact hzp
    exact le_antisymm (hCle.trans hzbQ.ge) (hzbQ.le.trans hQC)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
