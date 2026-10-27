module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP3

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin.B6
open scoped commutatorElement

section Sylow

variable {H : Type*} [Group H] {L₀ : Subgroup H}

theorem actOf_pow {n : H} (hn : n ∈ normL L₀) (k : ℕ) :
    actOf L₀ (n ^ k) = (actOf L₀ n) ^ k := by
  rw [actOf_of_mem hn, actOf_of_mem ((normL L₀).pow_mem hn k)]
  exact map_pow L₀.normalizerMonoidHom ⟨n, hn⟩ k

theorem actImg_normL_conj_mem {a d : MulAut ↥L₀} (ha : a ∈ actImg L₀ (normL L₀))
    (hd : d ∈ innGroup L₀) : a * d * a⁻¹ ∈ innGroup L₀ := by
  obtain ⟨n, -, hn, rfl⟩ := mem_actImg.1 ha
  exact actImg_conj_mem hn hd

variable [Finite H]

theorem isSylowOf_actImg {p : ℕ} (hp : p.Prime) {P K : Subgroup H} (hK : K ≤ normL L₀)
    (h : IsSylowOf p P K) : IsSylowOf p (actImg L₀ P) (actImg L₀ K) := by
  have := Fact.mk hp
  have hP : P ≤ normL L₀ := (isSylowOf_iff.1 h).1.trans hK
  have h' : IsSylowOf p (P.subgroupOf (normL L₀)) (K.subgroupOf (normL L₀)) := by
    rw [← isSylowOf_map_subtype_iff (normL L₀), Subgroup.map_subgroupOf_eq_of_le hP,
      Subgroup.map_subgroupOf_eq_of_le hK]
    exact h
  exact isSylowOf_map hp L₀.normalizerMonoidHom h'

end Sylow

section Setting

variable {H : Type*} [Group H] [Finite H] {p : ℕ} {T M : Subgroup H} {ι : Type*}
  {L : ι → Subgroup H}

theorem CPSetting.sylow_actImg (hS : CPSetting p T M L) (i₀ : ι) :
    IsSylowOf p (actImg (L i₀) (normT T (L i₀))) (actImg (L i₀) (normL (L i₀))) :=
  isSylowOf_actImg hS.prime le_rfl (hS.sylow_TL i₀)

theorem CPSetting.actImg_inf_inn (hS : CPSetting p T M L) (i₀ : ι) :
    actImg (L i₀) (normT T (L i₀)) ⊓ innGroup (L i₀) = actImg (L i₀) (T ⊓ L i₀) := by
  have := Fact.mk hS.prime
  have hsyl : IsSylowOf p (actImg (L i₀) (T ⊓ L i₀)) (actImg (L i₀) (L i₀)) :=
    isSylowOf_actImg hS.prime Subgroup.le_normalizer (hS.sylow_L i₀)
  rw [actImg_self] at hsyl
  have hle : actImg (L i₀) (T ⊓ L i₀) ≤ actImg (L i₀) (normT T (L i₀)) ⊓ innGroup (L i₀) := by
    refine le_inf (actImg_mono (inf_le_inf_left T Subgroup.le_normalizer)) ?_
    rw [← actImg_self]
    exact actImg_mono inf_le_right
  have hpg : IsPGroup p ↥(actImg (L i₀) (normT T (L i₀)) ⊓ innGroup (L i₀)) :=
    (hS.sylow_actImg i₀).isPGroup.to_le inf_le_left
  exact hsyl.eq_of_le hle inf_le_right hpg

theorem CPSetting.opCore (hS : CPSetting p T M L) (i₀ : ι) {Y : Subgroup (MulAut ↥(L i₀))}
    (hYA : Y ≤ actImg (L i₀) (normL (L i₀)))
    (hYn : (Y.subgroupOf (actImg (L i₀) (normL (L i₀)))).Normal) (hYp : IsPGroup p ↥Y) :
    Y = ⊥ :=
  opCore_inn_trivial hS.prime (hS.qs i₀) (innGroup_le_actImg _)
    (fun _ ha _ hd => actImg_normL_conj_mem ha hd) hYA
    (fun a ha y hy => (Subgroup.normal_subgroupOf_iff hYA).1 hYn y a hy ha) hYp

omit [Finite H] in
theorem CPSetting.centralizer_inn (hS : CPSetting p T M L) (i₀ : ι) :
    actImg (L i₀) (normL (L i₀)) ⊓ Subgroup.centralizer (innGroup (L i₀) : Set (MulAut ↥(L i₀))) =
      ⊥ := by
  rw [eq_bot_iff]
  intro β hβ
  exact Subgroup.mem_bot.2 (eq_one_of_centralizes_inn (hS.qs i₀).1 hβ.2)

theorem CPSetting.actImg_normT_ne_bot (hS : CPSetting p T M L) (i₀ : ι) {E : Subgroup H}
    (hEp : IsPGroup p ↥E) (hEn : E ≤ normL (L i₀)) (hEc : ⁅L i₀, E⁆ ≠ ⊥) :
    actImg (L i₀) (normT T (L i₀)) ≠ ⊥ := by
  intro hbot
  have hp := hS.prime
  have hsyl := hS.sylow_actImg i₀
  rw [hbot] at hsyl
  have hndvd : ¬ p ∣ Nat.card ↥(actImg (L i₀) (normL (L i₀))) := by
    have := Fact.mk hp
    have h1 := (isSylowOf_iff.1 hsyl).2.2
    rwa [Subgroup.relIndex_bot_left] at h1
  have hex : ∃ e ∈ E, e ∉ centL (L i₀) := by
    by_contra hcon
    apply hEc
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2
      fun e he => by_contra fun h => hcon ⟨e, he, h⟩
  obtain ⟨e, heE, hec⟩ := hex
  have heN : e ∈ normL (L i₀) := hEn heE
  have hne : actOf (L i₀) e ≠ 1 := fun h => hec ((actOf_eq_one_iff heN).1 h)
  obtain ⟨n, hn⟩ := hEp ⟨e, heE⟩
  have hen : e ^ p ^ n = 1 := congrArg Subtype.val hn
  have hpow : (actOf (L i₀) e) ^ p ^ n = 1 := by
    rw [← actOf_pow heN, hen]
    rw [actOf_of_mem (Subgroup.one_mem _)]
    exact map_one _
  have hmemA : actOf (L i₀) e ∈ actImg (L i₀) (normL (L i₀)) := actOf_mem_actImg heN heN
  have hdvdA : orderOf (⟨actOf (L i₀) e, hmemA⟩ : ↥(actImg (L i₀) (normL (L i₀)))) ∣
      Nat.card ↥(actImg (L i₀) (normL (L i₀))) := orderOf_dvd_natCard _
  have hord : orderOf (⟨actOf (L i₀) e, hmemA⟩ : ↥(actImg (L i₀) (normL (L i₀)))) =
      orderOf (actOf (L i₀) e) := Subgroup.orderOf_mk _ _
  rw [hord] at hdvdA
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hpow)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.1 (by simpa using hk))
  exact hndvd ((hk ▸ dvd_pow_self p hk0).trans hdvdA)

theorem CPSetting.actImg_normT_not_normal (hS : CPSetting p T M L) (i₀ : ι) {E : Subgroup H}
    (hEp : IsPGroup p ↥E) (hEn : E ≤ normL (L i₀)) (hEc : ⁅L i₀, E⁆ ≠ ⊥) :
    ¬ ((actImg (L i₀) (normT T (L i₀))).subgroupOf (actImg (L i₀) (normL (L i₀)))).Normal := by
  intro hn
  have hle : actImg (L i₀) (normT T (L i₀)) ≤ actImg (L i₀) (normL (L i₀)) :=
    actImg_mono inf_le_right
  exact hS.actImg_normT_ne_bot i₀ hEp hEn hEc
    (hS.opCore i₀ hle hn (hS.sylow_actImg i₀).isPGroup)

end Setting

end CFSG.QuasithinUnique.Setup.Layer
