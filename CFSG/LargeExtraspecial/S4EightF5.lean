module

public import CFSG.LargeExtraspecial.S2SpLevi
public import CFSG.LargeExtraspecial.S4EightF3
public import CFSG.LargeExtraspecial.S4EightG
public import CFSG.LargeExtraspecial.S4SevenAMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] noncomputable def FhatV (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) (F : Subgroup S.O) :
    Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  (F.subgroupOf (Rbar S g t)).map (resV haQ t)

theorem resV_mem_FhatV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {F : Subgroup S.O} {f : S.O}
    (hf : f ∈ F) (hfR : f ∈ Rbar S g t) : resV haQ t ⟨f, hfR⟩ ∈ FhatV S haQ t F :=
  ⟨⟨f, hfR⟩, hf, rfl⟩

theorem odd_card_FhatV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {F : Subgroup S.O}
    (hFodd : Odd (Nat.card F)) (hFR : F ≤ Rbar S g t) : Odd (Nat.card (FhatV S haQ t F)) := by
  have h1 := Subgroup.card_map_dvd (F.subgroupOf (Rbar S g t)) (resV haQ t)
  have h2 : Nat.card (F.subgroupOf (Rbar S g t)) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFR).toEquiv
  rw [h2] at h1
  exact Odd.of_dvd_nat hFodd h1

theorem LmodN_le_normalizer_FhatV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    {F : Subgroup S.O} (hLF : S.Lbar g ≤ normalizer (F : Set S.O)) :
    LmodN S g t ≤ normalizer (FhatV S haQ t F : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  intro e he
  rw [← map_subgroupOf_resV haQ ht] at he
  obtain ⟨l, hl, rfl⟩ := he
  refine mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨f, hf, rfl⟩ := hx
  refine ⟨l * f * l⁻¹, (mem_normalizer_iff.mp (hLF hl) f).mp hf, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem map_conj_spPointRadical {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {β : LinearMap.BilinForm (ZMod 2) V} (hβ : β.IsAlt) {x : V ≃ₗ[ZMod 2] V}
    (hx : x ∈ TauCeti.BilinForm.isometryGroup β) (a : V) :
    (spPointRadical β a).map (MulAut.conj x).toMonoidHom = spPointRadical β (x a) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact conj_mem_spPointRadical hβ hx hu
  · intro u hu
    refine ⟨x⁻¹ * u * x⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
    have := conj_mem_spPointRadical hβ (inv_mem hx) hu
    rwa [show x⁻¹ (x a) = a from x.symm_apply_apply a] at this

theorem exists_mem_perp_not_mem_span {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (β : LinearMap.BilinForm (ZMod 2) V)
    (h3 : 3 ≤ finrank (ZMod 2) V) (a : V) : ∃ d, β a d = 0 ∧ d ∉ (ZMod 2) ∙ a := by
  by_contra h
  push Not at h
  have hle : LinearMap.ker (β a) ≤ (ZMod 2) ∙ a := fun d hd => h d (LinearMap.mem_ker.mp hd)
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker (β a)
  have h3' : finrank (ZMod 2) (LinearMap.range (β a)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (β a))
    rwa [finrank_self] at this
  have h4 : finrank (ZMod 2) ((ZMod 2) ∙ a) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({a} : Set V)
    simpa using this
  omega

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {F : Subgroup S.O} (hFodd : Odd (Nat.card F))
  (hFR : F ≤ Rbar S g t) (hLF : S.Lbar g ≤ normalizer (F : Set S.O))
include H C ht ht1 hVQ hFodd hFR hLF

theorem false_of_spCase_of_beta_ne_zero (hNo : NoA2 S g) (hSp : SpCase H C ht ht1 hVQ)
    {f₁ f₂ : S.O} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (hβne : beta H C ht ht1 hVQ (orbV H.conj_mem ht (hFR hf₁))
      (orbV H.conj_mem ht (hFR hf₂)) ≠ 0) : False := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hβ := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  set β := beta H C ht ht1 hVQ with hβdef
  set Fh := FhatV S H.conj_mem t F with hFh
  have hFh2 := odd_card_FhatV H.conj_mem hFodd hFR
  have hEN := LmodN_le_normalizer_FhatV H.conj_mem ht (F := F) hLF
  have hE : LmodN S g t = spPointRadical β (aV ht) := hSp.LmodN_eq
  have hU : ∀ {f : S.O} (hf : f ∈ F), spPointRadical β (orbV H.conj_mem ht (hFR hf)) ≤
      Fh ⊔ LmodN S g t := by
    intro f hf
    have hxI : resV H.conj_mem t ⟨f, hFR hf⟩ ∈ TauCeti.BilinForm.isometryGroup β :=
      RmodN_le_isometryGroup H C ht ht1 hVQ ⟨f, hFR hf, fun v => coe_resV_apply H.conj_mem _ v⟩
    rw [orbV, ← map_conj_spPointRadical hβ hxI, ← hE]
    rintro _ ⟨u, hu, rfl⟩
    have hx := resV_mem_FhatV H.conj_mem hf (hFR hf)
    exact mul_mem (mul_mem (mem_sup_left hx) (mem_sup_right hu)) (inv_mem (mem_sup_left hx))
  have hβ1 : β (orbV H.conj_mem ht (hFR hf₁)) (orbV H.conj_mem ht (hFR hf₂)) = 1 :=
    zmod2_eq_one_of_ne_zero hβne
  obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
  have hSpgen := S2.spFix_eq_closure_spRadFix hβ hnd (F := ⊥) (bot_inf_eq _) (m := k)
    (by rw [S2.spPerp_bot, finrank_top, hk]; ring) (by rw [S2.spPerp_bot]; trivial)
    (by rw [S2.spPerp_bot]; trivial) hβ1
  rw [S2.spFix_bot, S2.spRadFix_bot, S2.spRadFix_bot] at hSpgen
  have hSpFE : TauCeti.BilinForm.isometryGroup β ≤ Fh ⊔ LmodN S g t := by
    rw [hSpgen, closure_le]
    rintro u (hu | hu)
    · exact hU hf₁ hu
    · exact hU hf₂ hu
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  obtain ⟨d, had, hdP⟩ := exists_mem_perp_not_mem_span β (by omega) (aV ht)
  obtain ⟨x, hax, -, hdx⟩ := exists_dual_triple hβ hnd (b := aV ht) (c := aV ht) (e := d)
    (by rwa [Set.pair_eq_singleton])
  set τ := spTransvection β hβ d with hτdef
  have hτI : τ ∈ TauCeti.BilinForm.isometryGroup β := spTransvection_mem_isometryGroup hβ d
  have hτa : τ (aV ht) = aV ht := by
    rw [hτdef, spTransvection_apply, had, zero_smul, add_zero]
  have hτN : τ ∈ normalizer (spPointRadical β (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) :=
    mem_normalizer_of_conj_le fun u hu => by
      have := conj_mem_spPointRadical hβ hτI hu
      rwa [hτa] at this
  have hτ2 : IsPGroup 2 (zpowers τ) := by
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two, hτdef, spTransvection_mul_self])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hP : IsPGroup 2 (spPointRadical β (aV ht) ⊔ zpowers τ :
      Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hτ2
      (IsPGroup.of_card (card_spPointRadical hβ hnd (aV_ne_zero H ht)))
      ((zpowers_le (G := Vt S g t ≃ₗ[ZMod 2] Vt S g t)).mpr hτN)
  have hτU : τ ∉ spPointRadical β (aV ht) := by
    intro hτU
    have h1 := hτU.2.2.1 x hax
    rw [hτdef, spTransvection_apply, add_sub_cancel_left, isAlt_symm hβ, hdx, one_smul] at h1
    exact hdP h1
  have hlt : spPointRadical β (aV ht) < spPointRadical β (aV ht) ⊔ zpowers τ :=
    lt_of_le_of_ne le_sup_left fun h => hτU (h ▸ mem_sup_right (mem_zpowers τ))
  have hc1 := Subgroup.card_lt_of_lt hlt
  have hPle : spPointRadical β (aV ht) ⊔ zpowers τ ≤ Fh ⊔ LmodN S g t :=
    sup_le (hE.symm.le.trans le_sup_right) (zpowers_le.mpr (hSpFE hτI))
  have hc3 := card_le_of_isPGroup_le_sup hFh2 hEN hP hPle
  rw [hE] at hc3
  omega

end CFSG.LargeExtraspecial.S4
