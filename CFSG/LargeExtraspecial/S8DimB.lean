module

public import CFSG.LargeExtraspecial.S8DimA
public import CFSG.LargeExtraspecial.S8Mod
public import CFSG.LargeExtraspecial.S8Std

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

universe u

section Product

variable {X : Type*} [Group X]

theorem card_sup_mul_card_inf_of_normal' (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup X}
    (hB : B ≤ normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set X)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

end Product

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_commQW_eq (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (r : Rbar S g t) :
    finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) S.Qt).map
      (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map (Wt S g t).mkQ) =
      finrank (ZMod 2) (commSpace (resV H.conj_mem t r)) := by
  set χ := chi H C ht ht1 hVQ with hχ
  have e : (((⊤ : Submodule (ZMod 2) S.Qt).map
      (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map (Wt S g t).mkQ).map
        (χ : (S.Qt ⧸ Wt S g t) →ₗ[ZMod 2] Vt S g t) = commSpace (resV H.conj_mem t r) := by
    ext y
    rw [mem_commSpace]
    constructor
    · rintro ⟨_, ⟨_, ⟨v, -, rfl⟩, rfl⟩, rfl⟩
      refine ⟨χ (Submodule.Quotient.mk v), ?_⟩
      change _ = χ (Submodule.Quotient.mk (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v))
      rw [Submodule.Quotient.mk_sub, map_sub, chi_equivariant H C ht ht1 hVQ r v]
    · rintro ⟨w, rfl⟩
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective (Wt S g t) (χ.symm w)
      have hw : χ (Submodule.Quotient.mk v) = w := by rw [hv, LinearEquiv.apply_symm_apply]
      refine ⟨_, ⟨_, ⟨v, Submodule.mem_top, rfl⟩, rfl⟩, ?_⟩
      change χ (Submodule.Quotient.mk (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v)) = _
      rw [Submodule.Quotient.mk_sub, map_sub, chi_equivariant H C ht ht1 hVQ r v, hw]
  rw [← e, LinearEquiv.finrank_map_eq]

theorem finrank_commSpace_ge {t τ : S.O}
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t)
    (hτW : ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t)
    (hVW : Vt S g t ≤ Wt S g t) :
    finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) S.Qt).map
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map (Wt S g t).mkQ) +
      finrank (ZMod 2) (commWV S g t τ) +
      finrank (ZMod 2) ((Vt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) ≤
      finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  set f := (τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1 with hf
  have hC : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = (⊤ : Submodule (ZMod 2) S.Qt).map f := by
    rw [Submodule.map_top]
  have h1 := finrank_map_add_finrank_inf_ker (Wt S g t).mkQ ((⊤ : Submodule (ZMod 2) S.Qt).map f)
  rw [Submodule.ker_mkQ] at h1
  set K := (Wt S g t).map f with hK
  have hKle : K ≤ (⊤ : Submodule (ZMod 2) S.Qt).map f ⊓ Wt S g t := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨⟨w, Submodule.mem_top, rfl⟩, ?_⟩
    change (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Wt S g t
    exact (Wt S g t).sub_mem (hτW w hw) hw
  have h2 := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ K
  rw [Submodule.ker_mkQ] at h2
  have hVK : (Vt S g t).map f ≤ K ⊓ Vt S g t := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨⟨v, hVW hv, rfl⟩, ?_⟩
    change (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t
    exact (Vt S g t).sub_mem (hτV v hv) hv
  have h3 := Submodule.finrank_mono hKle
  have h4 := Submodule.finrank_mono hVK
  change finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) S.Qt).map f).map (Wt S g t).mkQ) +
    finrank (ZMod 2) (K.map (Vt S g t).mkQ) + finrank (ZMod 2) ((Vt S g t).map f) ≤ _
  rw [hC]
  omega

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem resV_mem_pointRadical (D : Std H C ht ht1 hVQ) {τ : S.O} (hτL : τ ∈ S.Lbar g) :
    resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩ ∈ pointRadical D.Q (aV ht) := by
  rw [← D.hE]
  exact ⟨τ, hτL, fun v => coe_resV_apply H.conj_mem _ v⟩

theorem finrank_commSpace_resV_eq_two (D : Std H C ht ht1 hVQ) {τ : S.O} (hτL : τ ∈ S.Lbar g)
    (hτN : τ ∉ Nbar S g t) :
    finrank (ZMod 2) (commSpace (resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩)) = 2 := by
  have hx := resV_mem_pointRadical D hτL
  have hx1 : resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩ ≠ 1 := fun h =>
    hτN ((resV_eq_one_iff H.conj_mem _).mp h)
  obtain ⟨u, huK, hu0, hxu⟩ := exists_eichler_of_mem_pointRadical D.hQ (aV_ne_zero H ht) D.hQa
    D.polar_aV_bV hx hx1
  obtain ⟨-, hau, hbu⟩ := mem_perp_sup_span_pair.mp huK
  have hli : LinearIndependent (ZMod 2) ![aV ht, u] := by
    refine (LinearIndependent.pair_iff' (aV_ne_zero H ht)).mpr fun c hc => ?_
    have h0 : polar D.Q (bV (mem_Lbar_of_pair H ht D.hh)) (c • aV ht) = 0 := by rw [hc, hbu]
    rw [polar_smul_right, polar_comm, D.polar_aV_bV, smul_eq_mul, mul_one] at h0
    rw [h0, zero_smul] at hc
    exact hu0 hc.symm
  rw [hxu, commSpace_eichler D.hQ D.hQa hau hli, finrank_span_pair hli]

theorem finrank_commWV_eq (D : Std H C ht ht1 hVQ)
    {ρ : omegaGroup D.Q D.hQ →*
      (↥((Wt S g t).map (Vt S g t).mkQ) ≃ₗ[ZMod 2] ↥((Wt S g t).map (Vt S g t).mkQ))}
    (hρ : ∀ (e : omegaGroup D.Q D.hQ) (x : Rbar S g t),
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x →
      ∀ w (hw : w ∈ Wt S g t), ((ρ e (secMk (Vt S g t) hw) :
        ↥((Wt S g t).map (Vt S g t).mkQ)) : S.Qt ⧸ Vt S g t) =
          (Vt S g t).mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w))
    (r : Rbar S g t) (e : omegaGroup D.Q D.hQ)
    (he : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t r) :
    finrank (ZMod 2) (commWV S g t (r : S.O)) = finrank (ZMod 2) (commSpace (ρ e)) := by
  have e1 : (commSpace (ρ e)).map ((Wt S g t).map (Vt S g t).mkQ).subtype =
      commWV S g t (r : S.O) := by
    ext y
    constructor
    · rintro ⟨_, hz, rfl⟩
      obtain ⟨z, rfl⟩ := mem_commSpace.mp hz
      obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp z.2
      have hz' : z = secMk (Vt S g t) hw := Subtype.ext hwz.symm
      refine mem_commWV.mpr ⟨w, hw, ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, hz', hρ e r he w hw, map_sub]
      rfl
    · intro hy
      obtain ⟨w, hw, rfl⟩ := mem_commWV.mp hy
      refine ⟨ρ e (secMk (Vt S g t) hw) - secMk (Vt S g t) hw, sub_mem_commSpace _ _, ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, hρ e r he w hw, map_sub]
      rfl
  rw [← e1, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (Submodule.injective_subtype _) _).symm]


theorem finrank_WV_add_sixteen_le (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hgen : 3 ≤ D.m ∨ D.IsMinus)
    {x τ : S.O} (hxτ : τ = x * t * x⁻¹) (hτL : τ ∈ S.Lbar g) (hτN : τ ∉ Nbar S g t) :
    finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) + 16 ≤ 8 * D.m := by
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
  set r : Rbar S g t := ⟨τ, Lbar_le_Rbar ht hτL⟩ with hr
  have heΩ : resV H.conj_mem t r ∈ omegaGroup D.Q D.hQ := by
    rw [← D.hX, ← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  set e : omegaGroup D.Q D.hQ := ⟨_, heΩ⟩ with he
  have h1 := finrank_commWV_eq D hρ r e rfl
  have hgen' : 3 ≤ D.m ∨ IsMinusType D.Q ⊥ D.m :=
    hgen.imp id fun hmin T _ hT => hmin T hT
  have hx := resV_mem_pointRadical D hτL
  have hx1 : resV H.conj_mem t r ≠ 1 := fun h => hτN ((resV_eq_one_iff H.conj_mem _).mp h)
  have h4 := finrank_le_four_mul_finrank_commSpace ρ D.hm D.hdim hgen' (aV_ne_zero H ht) D.hQa
    D.Q_bV D.polar_aV_bV hD e hx hx1
  have hQW := finrank_commQW_eq H C ht ht1 hVQ r
  rw [finrank_commSpace_resV_eq_two D hτL hτN] at hQW
  have hV2 :
      finrank (ZMod 2) ((Vt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) = 2 := by
    have e2 : (Vt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) =
        (commSpace (resV H.conj_mem t r)).map (Vt S g t).subtype := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨resV H.conj_mem t r ⟨v, hv⟩ - ⟨v, hv⟩, sub_mem_commSpace _ _, ?_⟩
        rw [Submodule.subtype_apply, Submodule.coe_sub, coe_resV_apply]
        rfl
      · rintro ⟨_, hz, rfl⟩
        obtain ⟨z, rfl⟩ := mem_commSpace.mp hz
        refine ⟨z, z.2, ?_⟩
        rw [Submodule.subtype_apply, Submodule.coe_sub, coe_resV_apply]
        rfl
    rw [e2, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (Submodule.injective_subtype _) _).symm]
    exact finrank_commSpace_resV_eq_two D hτL hτN
  have hτt : τ * t = t * τ := commute_of_mem_Rbar H.conj_mem (Lbar_le_Rbar ht hτL)
  have hτC : τ ∈ CMt S t := mem_CMt.mpr ⟨Rbar_le_Mbar (Lbar_le_Rbar ht hτL), hτt⟩
  have hfilt := finrank_commSpace_ge (S := S) (g := g) (t := t) (τ := τ)
    (fun v hv => apply_mem_Vt_of_mem_CMt H.conj_mem hτC hv)
    (fun w hw => apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hw) (Vt_le_Wt H ht1)
  rw [finrank_commSpace_conj H C ht ht1 hVQ hxτ, D.hdim] at hfilt
  change finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) S.Qt).map
      (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map (Wt S g t).mkQ) +
    finrank (ZMod 2) (commWV S g t (r : S.O)) +
    finrank (ZMod 2) ((Vt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) ≤ _ at hfilt
  rw [hQW, hV2, h1] at hfilt
  omega

theorem Std.card_Nbar (D : Std H C ht ht1 hVQ) :
    Nat.card (Nbar S g t) = 2 ^ (2 * S.width - 4 * D.m + 1) := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  obtain ⟨hNAB, hLL⟩ := timmesfeld_6_5_bar H C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb
  set A := S.Lbar g ⊓ Nbar S g t with hA
  set B := S.Lbar ((D.h : G) * g) ⊓ Nbar S g t with hB
  have htN := self_mem_Nbar H ht
  have hinf : A ⊓ B = zpowers t := by
    have e : A ⊓ B = (S.Lbar g ⊓ S.Lbar ((D.h : G) * g)) ⊓ Nbar S g t := by
      rw [hA, hB]
      ext y
      simp only [mem_inf]
      tauto
    rw [e, hLL, inf_eq_left.mpr ((zpowers_le).mpr htN)]
  have hnorm : B ≤ normalizer (A : Set S.O) := by
    intro b hb
    have hbN : b ∈ Nbar S g t := hb.2
    rw [mem_normalizer_iff]
    intro a
    have htA : zpowers t ≤ A := (zpowers_le).mpr ⟨ht, htN⟩
    constructor
    · intro ha
      have hc := D.hNc b hbN a ha.2
      have e : b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact A.mul_mem (htA hc) ha
    · intro ha
      have hbi : b⁻¹ ∈ Nbar S g t := inv_mem hbN
      have hc := D.hNc b⁻¹ hbi _ ha.2
      have e : a = (b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ * (b * a * b⁻¹)⁻¹) * (b * a * b⁻¹) := by group
      rw [e]
      exact A.mul_mem (htA hc) ha
  have hprod := card_sup_mul_card_inf_of_le_normalizer' hnorm
  rw [← hNAB, hinf, Nat.card_zpowers, hto] at hprod
  have hBA : Nat.card B = Nat.card A := card_Lbar_mul_inf_Nbar H D.hh
  rw [hBA] at hprod
  have hAc := D.hA
  rw [D.hdim] at hAc
  obtain ⟨k, hk, hAk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ hAc)
  rw [hAk, ← pow_add] at hAc
  have hk' : k + (2 * D.m - 1) = S.width := Nat.pow_right_injective (le_refl 2) hAc
  rw [hAk, ← pow_add] at hprod
  have hm := D.hm
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hAk
    have hbot := Subgroup.card_eq_one.mp hAk
    apply ht1
    have htA : t ∈ S.Lbar g ⊓ Nbar S g t := ⟨ht, htN⟩
    rw [hbot, Subgroup.mem_bot] at htA
    exact htA
  have hk2 : k + k = (2 * S.width - 4 * D.m + 1) + 1 := by
    generalize S.width = w at hk' ⊢
    omega
  rw [hk2, pow_succ] at hprod
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) hprod

end CFSG.LargeExtraspecial.S8
