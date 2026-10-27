module

public import CFSG.LargeExtraspecial.S6ThreeC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_Abar (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hL : Nat.card (LmodN S g t) = 2 ^ (finrank (ZMod 2) (Vt S g t) - 2))
    (h2 : 2 ≤ finrank (ZMod 2) (Vt S g t)) :
    Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) =
      2 ^ S.width := by
  have h1 := card_Lbar_eq_mul H.conj_mem ht
  rw [C.card_Lbar, hL] at h1
  have hw := H.two_lt_width
  have e1 : 2 ^ S.width = 2 * 2 ^ (S.width - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e2 : 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) =
      2 * 2 ^ (finrank (ZMod 2) (Vt S g t) - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [e1, e2, h1]
  ring

theorem card_LmodN_of_omegaCase (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ) :
    Nat.card (LmodN S g t) = 2 ^ (finrank (ZMod 2) (Vt S g t) - 2) := by
  obtain ⟨Q, hQ, -, -, hE, hsing⟩ := hΩ.exists_form
  rw [hE, card_pointRadical hQ (aV_ne_zero H ht)
    ((hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩)]

theorem card_Abar_of_omegaCase (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) :
    Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) =
      2 ^ S.width :=
  card_Abar H C ht (card_LmodN_of_omegaCase H C ht ht1 hVQ hΩ)
    (by have := four_le_finrank_Vt H C ht ht1 hVQ hNo; omega)

theorem card_Abar_mul (H : Hyp4 S g) {t : S.O} {k : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width) :
    Nat.card (S.Lbar ((k : G) * g) ⊓ Nbar S ((k : G) * g) t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S ((k : G) * g) t) - 1) = 2 ^ S.width := by
  rw [Nbar_mul, Vt_mul, card_Lbar_mul_inf_Nbar H hk]
  exact hA

variable (S g) in
@[expose] noncomputable def nqImage (t : S.O) [NQHyp S g t] (K : Subgroup S.O) :
    Submodule (ZMod 2) (NQ S g t) where
  carrier := {m | ∃ n : Nbar S g t, (n : S.O) ∈ K ∧ nqMk n = m}
  add_mem' := by
    rintro _ _ ⟨n₁, hn₁, rfl⟩ ⟨n₂, hn₂, rfl⟩
    exact ⟨n₁ * n₂, K.mul_mem hn₁ hn₂, nqMk_mul n₁ n₂⟩
  zero_mem' := ⟨1, K.one_mem, (nqMk_eq_zero_iff 1).mpr (one_mem _)⟩
  smul_mem' := by
    rintro c _ ⟨n, hn, rfl⟩
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · exact ⟨1, K.one_mem, by rw [zero_smul]; exact (nqMk_eq_zero_iff 1).mpr (one_mem _)⟩
    · exact ⟨n, hn, by rw [one_smul]⟩

theorem mem_nqImage_mk {t : S.O} [NQHyp S g t] {K : Subgroup S.O} (htK : t ∈ K)
    (n : Nbar S g t) : nqMk n ∈ nqImage S g t K ↔ (n : S.O) ∈ K := by
  constructor
  · rintro ⟨n', hn', e⟩
    have h1 := (nqMk_eq_iff n' n).mp e
    have h2 : (n : S.O) = n' * ((n' : S.O)⁻¹ * n) := by group
    rw [h2]
    exact K.mul_mem hn' ((zpowers_le.mpr htK) h1)
  · intro hn
    exact ⟨n, hn, rfl⟩

section Fix

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
include H C ht ht1 hVQ

theorem clSub_inf_fixSub_Abar
    (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width) :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) =
      S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
  have h1 := card_mul_two_pow_finrank_fix H C (K := S.Lbar g ⊓ Nbar S g t) inf_le_left
  have h2 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t ≤
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) :=
    inf_le_inf_left _ fun v hv => (mem_fixSub S).mpr fun x hx => (mem_Nbar.mp hx.2).2 v hv
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := Nat.card_pos
  have h3 : 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓
      fixSub S (S.Lbar g ⊓ Nbar S g t)) = 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) := by
    have := h1.trans hA.symm
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h4 := Nat.pow_right_injective (le_refl 2) h3
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  omega

theorem mem_Abar_of_fix
    (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width)
    {x : S.O} (hx : x ∈ S.Lbar g)
    (hfix : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    x ∈ S.Lbar g ⊓ Nbar S g t := by
  set K : Subgroup S.O := S.Lbar g ⊓
    (S2.fixGroup (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t)).comap S.O.subtype with hK
  have hAK : S.Lbar g ⊓ Nbar S g t ≤ K := fun y hy =>
    ⟨hy.1, S2.mem_fixGroup.mpr fun v hv => (mem_Nbar.mp hy.2).2 v hv.2⟩
  have hxK : x ∈ K := ⟨hx, S2.mem_fixGroup.mpr hfix⟩
  have h1 := card_mul_two_pow_finrank_fix H C (K := K) inf_le_left
  have h2 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K := by
    refine le_inf inf_le_left fun v hv => (mem_fixSub S).mpr fun y hy => ?_
    exact S2.mem_fixGroup.mp hy.2 v hv
  have h3 := Submodule.finrank_mono hle
  have hcard : Nat.card K ≤ Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    have e : Nat.card K * 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) =
        Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
          2 ^ (finrank (ZMod 2) (Vt S g t) - 1) := h1.trans hA.symm
    have hp : 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) ≤
        2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) := by
      positivity
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul_of_lt_of_le hlt hp hpos
    omega
  have heq := Subgroup.eq_of_le_of_card_ge hAK hcard
  rw [heq]
  exact hxK

theorem mem_zpowers_of_fix_Wt {x : S.O} (hx : x ∈ S.Lbar g)
    (hfix : ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : x ∈ zpowers t := by
  set K : Subgroup S.O := S.Lbar g ⊓ (S2.fixGroup (Wt S g t)).comap S.O.subtype with hK
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have htK : zpowers t ≤ K := by
    rw [zpowers_le]
    refine ⟨ht, S2.mem_fixGroup.mpr fun w hw => ?_⟩
    have hW := (commSpace_t_eq H C ht ht1 hVQ).2
    rw [← hW] at hw
    exact mem_fixSpace.mp hw
  have hxK : x ∈ K := ⟨hx, S2.mem_fixGroup.mpr hfix⟩
  have h1 := card_mul_two_pow_finrank_fix H C (K := K) inf_le_left
  have h2 := finrank_clSub_inf_Wt H C ht ht1 hVQ
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K := by
    refine le_inf inf_le_left fun v hv => (mem_fixSub S).mpr fun y hy => ?_
    exact S2.mem_fixGroup.mp hy.2 v hv.2
  have h3 := Submodule.finrank_mono hle
  have hcard : Nat.card K ≤ Nat.card (zpowers t) := by
    rw [Nat.card_zpowers, hto]
    have hp : 2 ^ (S.width - 1) ≤
        2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hw : 2 ^ S.width = 2 * 2 ^ (S.width - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    by_contra hlt
    push Not at hlt
    have hpos : 0 < 2 ^ (S.width - 1) := by positivity
    have := Nat.mul_le_mul hlt hp
    rw [h1, hw] at this
    omega
  have heq := Subgroup.eq_of_le_of_card_ge htK hcard
  rw [heq]
  exact hxK

theorem mem_zpowers_of_mem_Nbar_of_fix_Wt (hgen : PairGen S g t)
    (hN0 : Nbar S g t = N0bar S g t) (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t)) {x : S.O}
    (hx : x ∈ Nbar S g t) (hfix : ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) :
    x ∈ zpowers t := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  obtain ⟨K, hKmem⟩ : ∃ K : Subgroup S.O,
      ∀ y, y ∈ K ↔ ∀ w ∈ Wt S g t, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w :=
    ⟨(S2.fixGroup (Wt S g t)).comap S.O.subtype, fun y => S2.mem_fixGroup⟩
  have htK : t ∈ K := (hKmem t).mpr fun w hw => by
    rw [← (commSpace_t_eq H C ht ht1 hVQ).2] at hw
    exact mem_fixSpace.mp hw
  have hKR : ∀ r ∈ Rbar S g t, ∀ y ∈ K, r * y * r⁻¹ ∈ K := by
    intro r hr y hy
    refine (hKmem _).mpr fun w hw => ?_
    have hw' := apply_mem_Wt H (inv_mem hr) hw
    change ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) * (y : S.Qt ≃ₗ[ZMod 2] S.Qt) *
      ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) w = w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, (hKmem y).mp hy _ hw',
      apply_inv_apply_O]
  by_contra hxt
  have hne : nqImage S g t K ≠ ⊥ := by
    intro hbot
    have hmem : nqMk (⟨x, hx⟩ : Nbar S g t) ∈ nqImage S g t K :=
      (mem_nqImage_mk htK _).mpr ((hKmem x).mpr hfix)
    rw [hbot, Submodule.mem_bot, nqMk_eq_zero_iff] at hmem
    exact hxt hmem
  have hLp : IsPGroup 2 ((S.Lbar g).subgroupOf (Rbar S g t)) :=
    (isPGroup_Lbar S H.conj_mem).comap_of_injective _ Subtype.coe_injective
  obtain ⟨φ, hφapp⟩ : ∃ φ : (S.Lbar g).subgroupOf (Rbar S g t) →*
      (NQ S g t ≃ₗ[ZMod 2] NQ S g t), ∀ (l : (S.Lbar g).subgroupOf (Rbar S g t))
        (n : Nbar S g t), φ l (nqMk n) = nqMk (nConj (l : Rbar S g t) n) :=
    ⟨(nqHom S g t).comp (Subgroup.subtype _), fun l n => nqHom_mk _ n⟩
  have hU : ∀ l u, u ∈ nqImage S g t K → φ l u ∈ nqImage S g t K := by
    rintro l _ ⟨n, hn, rfl⟩
    refine ⟨nConj (l : Rbar S g t) n, ?_, (hφapp l n).symm⟩
    rw [coe_nConj]
    exact hKR _ (l : Rbar S g t).2 _ hn
  obtain ⟨_, ⟨n, hnW, rfl⟩, hu0, hufix⟩ := exists_fixed_ne_zero hLp φ hU hne
  have hcomm : ∀ l ∈ S.Lbar (((1 : S.M) : G) * g), l * n * l⁻¹ * (n : S.O)⁻¹ ∈ zpowers t := by
    intro l hl
    rw [Subgroup.coe_one, one_mul] at hl
    have hlR : l ∈ Rbar S g t := Lbar_le_Rbar ht hl
    have h1 := hufix ⟨⟨l, hlR⟩, mem_subgroupOf.mpr hl⟩
    rw [hφapp] at h1
    exact (nqMk_nConj_eq_iff (⟨l, hlR⟩ : Rbar S g t) n).mp h1
  have hk1 : S.ρ 1 ∈ Rbar S g t := by rw [map_one]; exact one_mem _
  have hnL := mem_Lbar_of_comm_mem H C ht ht1 hVQ hgen hN0 h3 hh hb hk1 n.2 hcomm
  rw [Subgroup.coe_one, one_mul] at hnL
  exact hu0 ((nqMk_eq_zero_iff n).mpr
    (mem_zpowers_of_fix_Wt H C ht ht1 hVQ hnL ((hKmem _).mp hnW)))

end Fix

end CFSG.LargeExtraspecial.S8
