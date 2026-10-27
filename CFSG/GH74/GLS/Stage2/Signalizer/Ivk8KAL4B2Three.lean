module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4OutC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Odd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls1Frame

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.TBlocks
  CFSG.ComponentClassification.CatFactsL4U4.HBlocks
  CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.LieType.HighestRoot (three_eq_zero card_eq_24 eight_le_card_of_normal
  mem_center_iff_of_mulEquiv slEquivSL23 closure_orderOf_three_eq_top
  exists_mul_of_mem_sup_of_commute conj_mul_commutator)
open scoped MatrixGroups

section Field

variable {F : Type} [Field F] [Finite F]

theorem kaL4B2T_two_ne_zero (hK : Nat.card F = 3) : (2 : F) ≠ 0 := by
  intro h2
  have h3 := three_eq_zero hK
  have : (1 : F) = 0 := by linear_combination h3 - h2
  exact one_ne_zero this

theorem kaL4B2T_ringChar_ne_two (hK : Nat.card F = 3) : ringChar F ≠ 2 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).2 (by rw [h])
  exact kaL4B2T_two_ne_zero hK (by exact_mod_cast h')

theorem kaL4B2T_sq_eq_one (hK : Nat.card F = 3) {a : F} (ha : a ≠ 0) : a * a = 1 := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.card_eq_fintype_card, hK] at h
  simpa [sq] using h

end Field

section CentralProduct

variable {F : Type} [Field F] [Finite F]

theorem kaL4B2T_sq_eq_one_of_mem_center (hK : Nat.card F = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) {z : J} (hz : z ∈ Subgroup.center J) :
    z * z = 1 := by
  rw [mem_center_iff_of_mulEquiv hK e] at hz
  apply (e.trans (slEquivSL23 hK)).injective
  rcases hz with h | h <;> simp [map_mul, h]

theorem kaL4B2T_normal_odd_eq_bot (hK : Nat.card F = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) (N : Subgroup J) [N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  by_cases hNZ : N ≤ Subgroup.center J
  · rw [eq_bot_iff]
    intro z hz
    have hsq := kaL4B2T_sq_eq_one_of_mem_center hK e (hNZ hz)
    exact ka_odd_mem_of_sq_mem (R := ⊥) (by rw [hsq]; exact one_mem _)
      (hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hz))
  · exfalso
    have h8 := eight_le_card_of_normal hK e N hNZ
    have h24 := card_eq_24 hK e
    have hdvd : Nat.card N ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card N
    have hle : Nat.card N ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hodd
    generalize Nat.card N = n at hdvd h8 hk hle
    interval_cases n <;> omega

theorem kaL4B2T_inf_eq_bot (hK : Nat.card F = 3) {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup Y} (hX : IsPGroup p ↥X) (hAX : ∀ a ∈ A, a ∈ normalizer (X : Set Y)) :
    X ⊓ A = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  let N : Subgroup ↥A := (X ⊓ A).subgroupOf A
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, (g * n * g⁻¹ : ↥A).2⟩
    have := (Subgroup.mem_normalizer_iff.1 (hAX g g.2) n).1 hn.1
    simpa using this
  have hodd : Odd (Nat.card N) := by
    have h1 : Nat.card N = Nat.card ↥(X ⊓ A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ A ≤ A)).toEquiv
    have h2 : IsPGroup p ↥(X ⊓ A) := hX.to_le inf_le_left
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    rw [h1, hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hbot : N = ⊥ := kaL4B2T_normal_odd_eq_bot hK e N hodd
  rw [eq_bot_iff]
  intro y hy
  have hyN : (⟨y, hy.2⟩ : ↥A) ∈ N := Subgroup.mem_subgroupOf.mpr hy
  rw [hbot, Subgroup.mem_bot] at hyN
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hyN)

theorem kaL4B2T_eq_bot_of_central_product (hK : Nat.card F = 3) {Y : Type} [Group Y] [Finite Y]
    {J L₀ : Subgroup Y} (eJ : J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (eL : L₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hcomm : ∀ a ∈ J, ∀ b ∈ L₀, a * b = b * a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup Y} (hX : IsPGroup p ↥X) (hXle : X ≤ J ⊔ L₀)
    (hXJ : ∀ g ∈ J, g ∈ normalizer (X : Set Y)) (hXL : ∀ g ∈ L₀, g ∈ normalizer (X : Set Y)) :
    X = ⊥ := by
  have hJ := kaL4B2T_inf_eq_bot hK eJ hp hp2 hX hXJ
  have hL := kaL4B2T_inf_eq_bot hK eL hp hp2 hX hXL
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨j, hj, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (hXle hx)
  have hjl : j * l = l * j := hcomm j hj l hl
  have hjc : (⟨j, hj⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (g : Y) * (j * l) * (g : Y)⁻¹ * (j * l)⁻¹ ∈ X :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (hXJ g g.2) _).1 hx) (inv_mem hx)
    rw [conj_mul_commutator (hcomm _ g.2 _ hl)] at h1
    have h3 : (g : Y) * j * (g : Y)⁻¹ * j⁻¹ ∈ J :=
      mul_mem (mul_mem (mul_mem g.2 hj) (inv_mem g.2)) (inv_mem hj)
    have h2 : (g : Y) * j * (g : Y)⁻¹ * j⁻¹ ∈ X ⊓ J := ⟨h1, h3⟩
    rw [hJ, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact Subtype.ext h2
  have hlc : (⟨l, hl⟩ : L₀) ∈ Subgroup.center L₀ := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hx' : l * j ∈ X := hjl ▸ hx
    have h1 : (g : Y) * (l * j) * (g : Y)⁻¹ * (l * j)⁻¹ ∈ X :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (hXL g g.2) _).1 hx') (inv_mem hx')
    rw [conj_mul_commutator (hcomm _ hj _ g.2).symm] at h1
    have h3 : (g : Y) * l * (g : Y)⁻¹ * l⁻¹ ∈ L₀ :=
      mul_mem (mul_mem (mul_mem g.2 hl) (inv_mem g.2)) (inv_mem hl)
    have h2 : (g : Y) * l * (g : Y)⁻¹ * l⁻¹ ∈ X ⊓ L₀ := ⟨h1, h3⟩
    rw [hL, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact Subtype.ext h2
  have hj2 : j * j = 1 := congrArg Subtype.val (kaL4B2T_sq_eq_one_of_mem_center hK eJ hjc)
  have hl2 : l * l = 1 := congrArg Subtype.val (kaL4B2T_sq_eq_one_of_mem_center hK eL hlc)
  have hsq : j * l * (j * l) = 1 := by
    calc j * l * (j * l) = j * (l * j) * l := by group
      _ = j * (j * l) * l := by rw [hjl]
      _ = j * j * (l * l) := by group
      _ = 1 := by rw [hj2, hl2, one_mul]
  exact ka_odd_mem_of_sq_mem (R := ⊥) (by rw [hsq]; exact one_mem _)
    (ka_odd_of_mem_pGroup hp hp2 hX hx)

end CentralProduct

section Blocks

variable {F : Type} [Field F]

@[expose] def kaL4B2TInl (F : Type) [Field F] : SL(2, F) →* projectiveSL 4 F :=
  (proj 4 F).comp iota1

@[expose] def kaL4B2TInr (F : Type) [Field F] : SL(2, F) →* projectiveSL 4 F :=
  (proj 4 F).comp iota2

@[expose] def kaL4B2TL (F : Type) [Field F] : Subgroup (projectiveSL 4 F) :=
  ((proj 4 F).comp (bdSL (F := F))).range

theorem kaL4B2T_phi (s t : SL(2, F)) :
    proj 4 F (bdSL (s, t)) = kaL4B2TInl F s * kaL4B2TInr F t := by
  show proj 4 F (bdSL (s, t)) = proj 4 F (bdSL (s, 1)) * proj 4 F (bdSL (1, t))
  rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem kaL4B2T_comm (s t : SL(2, F)) :
    kaL4B2TInl F s * kaL4B2TInr F t = kaL4B2TInr F t * kaL4B2TInl F s := by
  have h2 : proj 4 F (bdSL (s, t)) = kaL4B2TInr F t * kaL4B2TInl F s := by
    show proj 4 F (bdSL (s, t)) = proj 4 F (bdSL (1, t)) * proj 4 F (bdSL (s, 1))
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [← kaL4B2T_phi, h2]

theorem kaL4B2T_inl_mem (s : SL(2, F)) : kaL4B2TInl F s ∈ kaL4B2TL F := ⟨(s, 1), rfl⟩

theorem kaL4B2T_inr_mem (t : SL(2, F)) : kaL4B2TInr F t ∈ kaL4B2TL F := ⟨(1, t), rfl⟩

theorem kaL4B2T_L_le_sup :
    kaL4B2TL F ≤ (kaL4B2TInl F).range ⊔ (kaL4B2TInr F).range := by
  rintro _ ⟨⟨s, t⟩, rfl⟩
  change proj 4 F (bdSL (s, t)) ∈ _
  rw [kaL4B2T_phi]
  exact mul_mem (Subgroup.mem_sup_left ⟨s, rfl⟩) (Subgroup.mem_sup_right ⟨t, rfl⟩)

theorem kaL4B2T_inl_injective : Function.Injective (kaL4B2TInl F) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hk' : proj 4 F (iota1 k) = 1 := hk
  obtain ⟨u, -, hu⟩ := mem_scalars.1 (proj_eq_one_iff.1 hk')
  rw [coe_iota1] at hu
  have e00 := congrFun (congrFun hu 0) 0
  have e01 := congrFun (congrFun hu 0) 1
  have e10 := congrFun (congrFun hu 1) 0
  have e11 := congrFun (congrFun hu 1) 1
  have e22 := congrFun (congrFun hu 2) 2
  simp [bd, Matrix.scalar_apply] at e00 e01 e10 e11 e22
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11, ← e22]

theorem kaL4B2T_inr_injective : Function.Injective (kaL4B2TInr F) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hk' : proj 4 F (iota2 k) = 1 := hk
  obtain ⟨u, -, hu⟩ := mem_scalars.1 (proj_eq_one_iff.1 hk')
  have hu' : bd (1 : Matrix (Fin 2) (Fin 2) F) (k : Matrix (Fin 2) (Fin 2) F) =
      scalar (Fin 4) (u : F) := hu
  have e00 := congrFun (congrFun hu' 0) 0
  have e22 := congrFun (congrFun hu' 2) 2
  have e23 := congrFun (congrFun hu' 2) 3
  have e32 := congrFun (congrFun hu' 3) 2
  have e33 := congrFun (congrFun hu' 3) 3
  simp [bd, Matrix.scalar_apply] at e00 e22 e23 e32 e33
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e22, e23, e32, e33, ← e00]

theorem kaL4B2T_mem_cent {g : SL(4, F)} (hg : g ∈ kaSlCent (B0 F)) :
    (g : Matrix (Fin 4) (Fin 4) F) * X1 1 = X1 1 * (g : Matrix (Fin 4) (Fin 4) F) := by
  rw [kaSlCent, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hg
  have h1 := congrArg Units.val (hg (B0 F) (Set.mem_singleton _))
  rw [Units.val_mul, Units.val_mul, coe_B0] at h1
  exact h1.symm

theorem kaL4B2T_L_le_fix : kaL4B2TL F ≤ fixSub (conjAut 4 F (B0 F)) := by
  rintro _ ⟨⟨s, t⟩, rfl⟩
  exact proj_mem_fixSub_of_comm (bdSL_comm (s, t))

theorem kaL4B2T_B0_mul_self : B0 F * B0 F = GeneralLinearGroup.scalar (Fin 4) 1 := by
  rw [map_one]
  exact Units.ext (by rw [Units.val_mul, coe_B0, X1_one_mul_self, Units.val_one])

end Blocks

section Odd

variable {F : Type} [Field F] [Finite F]

theorem kaL4B2T_sq_mem (hK : Nat.card F = 3) {g : SL(4, F)} (hg : g ∈ kaSlCent (B0 F)) :
    ∃ s t : SL(2, F), g * g = bdSL (s, t) := by
  have hB : IsBD (g : Matrix (Fin 4) (Fin 4) F) :=
    isBD_of_comm_X1 (kaL4B2T_two_ne_zero hK) one_ne_zero (kaL4B2T_mem_cent hg)
  obtain ⟨a, b, hab⟩ : ∃ a b : Matrix (Fin 2) (Fin 2) F, (g : Matrix (Fin 4) (Fin 4) F) = bd a b :=
    ⟨_, _, eq_bd hB⟩
  have hdet : a.det * b.det = 1 := by
    rw [← det_bd, ← hab]
    exact g.2
  refine ⟨⟨a * a, ?_⟩, ⟨b * b, ?_⟩, ?_⟩
  · rw [Matrix.det_mul]
    exact kaL4B2T_sq_eq_one hK (left_ne_zero_of_mul_eq_one hdet)
  · rw [Matrix.det_mul]
    exact kaL4B2T_sq_eq_one hK (right_ne_zero_of_mul_eq_one hdet)
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hab, bd_mul]
    rfl

theorem kaL4B2T_odd_mem (hK : Nat.card F = 3) {y : projectiveSL 4 F}
    (hy : y ∈ (kaSlCent (B0 F)).map (proj 4 F)) (ho : Odd (orderOf y)) : y ∈ kaL4B2TL F := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨s, t, hst⟩ := kaL4B2T_sq_mem hK hg
  refine ka_odd_mem_of_sq_mem ?_ ho
  rw [← map_mul, hst]
  exact ⟨(s, t), rfl⟩

theorem kaL4B2T_mem_closure_odd (hK : Nat.card F = 3) (f : SL(2, F) →* projectiveSL 4 F)
    (hf : ∀ g, f g ∈ kaL4B2TL F) (g : SL(2, F)) :
    f g ∈ Subgroup.closure {x : projectiveSL 4 F | x ∈ kaL4B2TL F ∧ Odd (orderOf x)} := by
  have hg : g ∈ Subgroup.closure {y : SL(2, F) | orderOf y = 3} := by
    rw [closure_orderOf_three_eq_top hK]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨hf y, ?_⟩
    have hd : orderOf (f y) ∣ orderOf y := orderOf_map_dvd f y
    rw [hy] at hd
    exact Odd.of_dvd_nat (by decide) hd
  | one =>
    rw [map_one]
    exact one_mem _
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact inv_mem ha

theorem kaL4B2T_gen (hK : Nat.card F = 3) :
    Subgroup.closure {x : projectiveSL 4 F | x ∈ kaL4B2TL F ∧ Odd (orderOf x)} =
      kaL4B2TL F := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  rintro _ ⟨⟨s, t⟩, rfl⟩
  change proj 4 F (bdSL (s, t)) ∈ _
  rw [kaL4B2T_phi]
  exact mul_mem (kaL4B2T_mem_closure_odd hK (kaL4B2TInl F) kaL4B2T_inl_mem s)
    (kaL4B2T_mem_closure_odd hK (kaL4B2TInr F) kaL4B2T_inr_mem t)

theorem kaL4B2T_hRp (hK : Nat.card F = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (projectiveSL 4 F)} (hX : IsPGroup p ↥X) (hXle : X ≤ kaL4B2TL F)
    (hnorm : ∀ r ∈ kaL4B2TL F, r ∈ normalizer (X : Set (projectiveSL 4 F))) : X = ⊥ := by
  refine kaL4B2T_eq_bot_of_central_product hK
    (MonoidHom.ofInjective (kaL4B2T_inl_injective (F := F))).symm
    (MonoidHom.ofInjective (kaL4B2T_inr_injective (F := F))).symm ?_ hp hp2 hX
    (hXle.trans kaL4B2T_L_le_sup) (fun g hg => ?_) (fun g hg => ?_)
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact kaL4B2T_comm s t
  · obtain ⟨s, rfl⟩ := hg
    exact hnorm _ (kaL4B2T_inl_mem s)
  · obtain ⟨t, rfl⟩ := hg
    exact hnorm _ (kaL4B2T_inr_mem t)

end Odd

section Class

variable {F : Type} [Field F] [Finite F]

theorem kaL4B2T_congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) :
    MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem kaL4B2T_B0 (hK : Nat.card F = 3) : KAAll (conjAut 4 F (B0 F)) := by
  have hodd : ringChar F ≠ 2 := kaL4B2T_ringChar_ne_two hK
  have hA : B0 F * B0 F = GeneralLinearGroup.scalar (Fin 4) 1 := kaL4B2T_B0_mul_self
  refine ka_all_of_oddcore (ka_conj_inj_pl4 hodd) (kaL4B2TL F) kaL4B2T_L_le_fix
    (kaL4B2T_gen hK) ?_ ?_ (ka_outCyc_pl4 hodd) (ka_outCentral_pl4 hodd (B0 F) 1 hA)
  · intro c hc ho
    exact kaL4B2T_odd_mem hK (ka_odd_mem_map_cent_pl4 (B0 F) 1 hA (mem_fixSub.1 hc) ho) ho
  · intro p hp hp2 X hX hXle hnorm
    exact kaL4B2T_hRp hK hp hp2 hX hXle hnorm

end Class

theorem kaL4B2Three_thm : KAL4B2Three := by
  intro F _ _ hK B hB hr
  obtain ⟨P, rfl⟩ := exists_frame_cls1 (kaL4B2T_two_ne_zero hK) hB hr
  have h := KAAll.of_mulEquiv (conjAut 4 F P : projectiveSL 4 F ≃* projectiveSL 4 F)
    (kaL4B2T_B0 hK)
  have e : MulAut.congr (conjAut 4 F P : projectiveSL 4 F ≃* projectiveSL 4 F)
      (conjAut 4 F (B0 F)) = conjAut 4 F (P * B0 F * P⁻¹) := by
    rw [kaL4B2T_congr_eq_mul, map_mul, map_mul, map_inv]
  rwa [e] at h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
