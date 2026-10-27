module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEnd
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalTwelve

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem isElemAbelian_bot {X : Type*} [Group X] : IsElemAbelian 2 (⊥ : Subgroup X) := by
  exact CFSG.Open.isElemAbelian_bot _

theorem conj_le_sup_zStar_of_wclZ (hC : Counterexample G D r Abar) {a : Fin r}
    (d : DeltaDatum D Abar a)
    (hwclZ : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤ d.S ⊔ AschbacherTheorem3.omegaOne d.T →
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a)
    {c : G} (hc : c ∈ aschbacherThm5Preimage D (Abar a))
    (hle : rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      d.S ⊔ AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a) :
    rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a)
  set U := AschbacherTheorem3.omegaOne d.T
  set Z := factorZStar D Abar a
  have hZA : Z ≤ A := inf_le_left
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := factor_le_normalizer_factorZStar a
  have hUZ : U ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
    le_normalizer_factorZStar a (EndHyp.U_le_H hC hu) (EndHyp.U_le_normalizer_A hu)
  have hSU2 : IsPGroup 2 (d.S ⊔ U : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' (d.sylowT.isPGroup.to_le EndHyp.U_le_T)
      d.sylowS.isPGroup EndHyp.U_le_normalizer_S
  have hSUZ : d.S ⊔ U ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le (d.sylowS.le.trans hAZ) hUZ
  have hSUA : (d.S ⊔ U) ⊓ A ≤ d.S := by
    intro x ⟨hx, hxA⟩
    have hx' : x ∈ ((U ⊔ d.S : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U d.S EndHyp.U_le_normalizer_S] at hx'
    obtain ⟨u, hu, s, hs, rfl⟩ := Set.mem_mul.mp hx'
    have huA : u ∈ A := by
      have : u = (u * s) * s⁻¹ := by group
      rw [this]
      exact A.mul_mem hxA (A.inv_mem (d.sylowS.le hs))
    have hu1 : u ∈ U ⊓ A := ⟨hu, huA⟩
    rw [EndHyp.U_inf_A hC, Subgroup.mem_bot] at hu1
    rw [hu1, one_mul]
    exact hs
  have hsylZ : IsSylowOf 2 ((d.S ⊔ U) ⊓ Z) Z := by
    have heq : (d.S ⊔ U) ⊓ Z = d.S ⊓ Z := by
      apply le_antisymm
      · exact le_inf (le_trans (inf_le_inf_left _ hZA) hSUA) inf_le_right
      · exact inf_le_inf_right _ le_sup_left
    rw [heq]
    exact d.sylowS.inf_of_le_normalizer hZA hAZ
  have hR2 : IsPGroup 2 (rightConjugate U c) :=
    AschbacherTheorem3.isPGroup_rightConjugate (d.sylowT.isPGroup.to_le EndHyp.U_le_T) c
  obtain ⟨z, hz, hzle⟩ := le_rightConjugate_of_le_sup hSU2 hSUZ hsylZ hR2 hle
  have hle' : rightConjugate U (c * z⁻¹) ≤ d.S ⊔ U := by
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hzle z⁻¹
    rwa [rightConjugate_mul, rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
  have hcz : c * z⁻¹ ∈ A := A.mul_mem hc (A.inv_mem (hZA hz))
  have h2 := hwclZ _ hcz hle'
  have h3 : rightConjugate U c ≤ rightConjugate (U ⊔ Z) z := by
    have h4 := AschbacherTheorem3.rightConjugate_le_rightConjugate h2 z
    rwa [rightConjugate_mul, inv_mul_cancel_right] at h4
  rwa [AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_right hz)] at h3

theorem bar_conj_le_central (hC : Counterexample G D r Abar) {a : Fin r}
    {d : DeltaDatum D Abar a}
    (hwclZ : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤ d.S ⊔ AschbacherTheorem3.omegaOne d.T →
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a)
    (c : Subgroup.normalizer (D : Set G)) (hc : (c : G) ∈ aschbacherThm5Preimage D (Abar a))
    (hle : rightConjugate (bar D (AschbacherTheorem3.omegaOne d.T)) (toBar D c) ≤
      bar D d.S ⊔ bar D (AschbacherTheorem3.omegaOne d.T) ⊔
        centerBar D (aschbacherThm5Preimage D (Abar a))) :
    rightConjugate (bar D (AschbacherTheorem3.omegaOne d.T)) (toBar D c) ≤
      bar D (AschbacherTheorem3.omegaOne d.T) ⊔
        centerBar D (aschbacherThm5Preimage D (Abar a)) := by
  have hZH : factorZStar D Abar a ≤ Subgroup.normalizer (D : Set G) :=
    inf_le_left.trans EndHyp.A_le_H
  rw [← bar_rightConjugate, ← bar_factorZStar, ← bar_sup EndHyp.S_le_H (EndHyp.U_le_H hC),
    ← bar_sup (sup_le EndHyp.S_le_H (EndHyp.U_le_H hC)) hZH] at hle
  rw [← bar_rightConjugate, ← bar_factorZStar, ← bar_sup (EndHyp.U_le_H hC) hZH]
  have hUcH : rightConjugate (AschbacherTheorem3.omegaOne d.T) (c : G) ≤
      Subgroup.normalizer (D : Set G) := rightConjugate_le_normalizer (EndHyp.U_le_H hC) c
  have h1 := BarTools.le_sup_core_of_bar_le hUcH hle
  rw [sup_eq_left.mpr (core_le_factorZStar a |>.trans le_sup_right)] at h1
  exact bar_mono D (conj_le_sup_zStar_of_wclZ hC d hwclZ hc h1)

theorem barA_inf_centralizer_le_of_comm (hC : Counterexample G D r Abar) {a : Fin r}
    {d : DeltaDatum D Abar a} (hT : IsMulCommutative d.T) {u : G}
    (hu : u ∈ AschbacherTheorem3.omegaOne d.T) (hu1 : u ≠ 1) :
    bar D (aschbacherThm5Preimage D (Abar a)) ⊓
        Subgroup.centralizer ({toBar D ⟨u, EndHyp.U_le_H hC hu⟩} : Set (Bar D)) ≤
      bar D (aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g) := by
  have hu2 : orderOf u = 2 := orderOf_eq_prime ((isElemAbelian_omegaOne hT).2 u hu) hu1
  rw [← BarTools.bar_inf_centralizer (core_le_preimage D _) (EndHyp.U_le_H hC hu) hu2]
  refine bar_mono D (inf_le_inf_left _ ?_)
  exact centralizer_le_conj hC a d.g (twoElt_of_mem (d.sylowT.isPGroup.to_le EndHyp.U_le_T) hu)
    hu1 (EndHyp.U_le_L hu)

theorem end_of_6_4_central (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hcommZ : ∀ u ∈ AschbacherTheorem3.omegaOne d.T, ∀ s ∈ d.S,
      u⁻¹ * s⁻¹ * u * s ∈ factorZStar D Abar a)
    (hwclZ : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤ d.S ⊔ AschbacherTheorem3.omegaOne d.T →
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set Ab := bar D A with hAbdef
  set Ub := bar D U with hUbdef
  set Sb := bar D d.S with hSbdef
  set Zb := centerBar D A with hZbdef
  set Y₀ := Ab ⊔ Ub with hY₀def
  have hAbY : Ab ≤ Y₀ := le_sup_left
  have hUbY : Ub ≤ Y₀ := le_sup_right
  have hSbA : Sb ≤ Ab := EndHyp.isSylowOf_barS.le
  have hUbN : Ub ≤ Subgroup.normalizer (Ab : Set (Bar D)) := EndHyp.barU_le_normalizer
  have hY₀N : Y₀ ≤ Subgroup.normalizer (Ab : Set (Bar D)) := sup_le Subgroup.le_normalizer hUbN
  have hZbA : Zb ≤ Ab := centerBar_le A
  have hZbY : Zb ≤ Y₀ := hZbA.trans hAbY
  have hY₀Z : Y₀ ≤ Subgroup.normalizer (Zb : Set (Bar D)) := fun x hx =>
    le_normalizer_centerBar (hY₀N hx)
  have : (Zb.subgroupOf Y₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZbY).mpr hY₀Z
  have hUA : Ub ⊓ Ab = ⊥ := EndHyp.barU_inf_barA hC
  obtain ⟨m, K, -, hK, hKcomm, hKgen⟩ := bar_factor_components hC.hyp a
  replace hKgen : ⨆ l, K l = Ab := hKgen
  have hKA : ∀ l, K l ≤ Ab := fun l => (hK l).2
  have hKY : ∀ l, K l ≤ Y₀ := fun l => (hKA l).trans hAbY
  set Ah := SubQuot.img Y₀ Zb Ab with hAhdef
  set Eh := SubQuot.img Y₀ Zb Ub with hEhdef
  set Sh := SubQuot.img Y₀ Zb Sb with hShdef
  set Vh : Subgroup (Y₀ ⧸ Zb.subgroupOf Y₀) := ⊥ with hVhdef
  set Xh : Fin m → Subgroup (Y₀ ⧸ Zb.subgroupOf Y₀) := fun l => SubQuot.img Y₀ Zb (K l)
    with hXhdef
  have hker : ∀ l, ∀ k ∈ K l, (k ∈ Zb ↔ ∀ x ∈ K l, k * x = x * k) := by
    intro l k hk
    constructor
    · intro hkZ x hx
      exact centerBar_comm A hkZ x (hKA l hx)
    · intro hkc
      refine ⟨hKA l hk, ?_⟩
      show k ∈ Subgroup.centralizer (Ab : Set (Bar D))
      rw [Subgroup.mem_centralizer_iff]
      have hle : Ab ≤ Subgroup.centralizer ({k} : Set (Bar D)) := by
        rw [← hKgen]
        refine iSup_le fun l' y hy => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        by_cases hll : l' = l
        · subst hll
          exact (hkc y hy).symm
        · exact hKcomm l' l hll y hy k hk
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  have hsimple := fun l => SubQuot.simple_img (hKY l) (hK l).1.2.2 (hker l)
  have f_normal : Ah.Normal := SubQuot.img_normal hAbY hY₀N
  have f_sup : Ah ⊔ Eh = ⊤ := by
    rw [hAhdef, hEhdef, ← SubQuot.img_sup hAbY hUbY]
    exact SubQuot.img_self
  have f_inf : Eh ⊓ Ah = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyA⟩
    obtain ⟨x, hxU, rfl⟩ := SubQuot.mem_img.mp hyE
    obtain ⟨x', hx'A, hxx'⟩ := SubQuot.mem_img.mp hyA
    have hmem := (SubQuot.proj_eq_proj_iff x' x).mp hxx'
    have hxA : (x : Bar D) ∈ Ab := by
      have : (x : Bar D) = (x' : Bar D) * ((x' : Bar D)⁻¹ * x) := by group
      rw [this]
      exact Ab.mul_mem hx'A (hZbA hmem)
    have h1 : (x : Bar D) ∈ Ub ⊓ Ab := ⟨hxU, hxA⟩
    rw [hUA, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, SubQuot.proj_eq_one_iff, h1]
    exact Zb.one_mem
  have f_elem : IsElemAbelian 2 Eh :=
    SubQuot.isElemAbelian_img (isElemAbelian_map_subgroupOf (isElemAbelian_omegaOne hT) (toBar D))
  have f_comm : ∀ l l', l ≠ l' → ∀ x ∈ Xh l, ∀ y ∈ Xh l', x * y = y * x := by
    intro l l' hll x hx y hy
    obtain ⟨x₁, hx₁, rfl⟩ := SubQuot.mem_img.mp hx
    obtain ⟨y₁, hy₁, rfl⟩ := SubQuot.mem_img.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKcomm l l' hll _ hx₁ _ hy₁)
  have f_gen : ⨆ l, Xh l = Ah := by
    rw [hAhdef, ← hKgen, SubQuot.img_iSup K hKY]
  have f_perm : ∀ e ∈ Eh, ∀ l, ∃ l', rightConjugate (Xh l) e = Xh l' := by
    intro e he l
    obtain ⟨u₁, hu₁, rfl⟩ := SubQuot.mem_img.mp he
    have hc := isComponentOf_rightConjugate (hK l).1 (u₁ : Bar D)
    have hcle : rightConjugate (K l) (u₁ : Bar D) ≤ ⨆ l, K l := by
      rw [hKgen]
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate (hKA l) (u₁ : Bar D)
      rwa [(rightConjugate_eq_self_iff Ab (u₁ : Bar D)).mpr (hUbN hu₁)] at h1
    obtain ⟨l', hl'⟩ := component_eq_of_le (fun l => (hK l).1) hc hcle
    exact ⟨l', by rw [← SubQuot.img_rightConjugate, hl']⟩
  have f_sylow : IsSylowOf 2 Sh Ah := SubQuot.isSylowOf_img hAbY EndHyp.isSylowOf_barS
  have f_sylowN : Eh ≤ Subgroup.normalizer (Sh : Set (Y₀ ⧸ Zb.subgroupOf Y₀)) :=
    SubQuot.img_le_normalizer fun x hx => EndHyp.barU_le_normalizer_S hx.1
  have f_Vle : Vh ≤ Sh := bot_le
  have f_Velem : IsElemAbelian 2 Vh := isElemAbelian_bot
  have f_Vcl : ∀ v ∈ Vh, ∀ x ∈ Ah, x⁻¹ * v * x ∈ Sh → x⁻¹ * v * x ∈ Vh := by
    intro v hv x _ _
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv, mul_one, inv_mul_cancel]
  have f_Vcomm : ∀ e ∈ Eh, ∀ v ∈ Vh, e * v = v * e := by
    intro e _ v hv
    rw [Subgroup.mem_bot.mp hv, mul_one, one_mul]
  have f_comm_le : ∀ e ∈ Eh, ∀ x ∈ Sh, e⁻¹ * x⁻¹ * e * x ∈ Vh := by
    intro e he x hx
    obtain ⟨e₁, he₁, rfl⟩ := SubQuot.mem_img.mp he
    obtain ⟨x₁, hx₁, rfl⟩ := SubQuot.mem_img.mp hx
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, Subgroup.mem_bot,
      SubQuot.proj_eq_one_iff]
    obtain ⟨u, hu, hue⟩ := (mem_bar_iff D U (e₁ : Bar D)).mp he₁
    obtain ⟨s, hs, hsx⟩ := (mem_bar_iff D d.S (x₁ : Bar D)).mp hx₁
    have hcoe : ((e₁⁻¹ * x₁⁻¹ * e₁ * x₁ : Y₀) : Bar D) =
        toBar D (u⁻¹ * s⁻¹ * u * s) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hue, hsx]
    rw [hcoe, hZbdef, ← bar_factorZStar]
    exact toBar_mem_bar D (hcommZ u hu s hs)
  have f_wcl : ∀ x ∈ Ah, rightConjugate Eh x ≤ Sh ⊔ Eh → rightConjugate Eh x ≤ Eh ⊔ Vh := by
    intro x hx hle
    obtain ⟨x₁, hx₁, rfl⟩ := SubQuot.mem_img.mp hx
    obtain ⟨c, hc, hcx⟩ := (mem_bar_iff D A (x₁ : Bar D)).mp hx₁
    have hUx : rightConjugate Ub (x₁ : Bar D) ≤ Y₀ := by
      intro y hy
      rw [mem_rightConjugate_iff] at hy
      have : y = (x₁ : Bar D)⁻¹ * ((x₁ : Bar D) * y * (x₁ : Bar D)⁻¹) * x₁ := by group
      rw [this]
      exact Y₀.mul_mem (Y₀.mul_mem (Y₀.inv_mem x₁.2) (hUbY hy)) x₁.2
    rw [hEhdef, ← SubQuot.img_rightConjugate, hShdef, ← SubQuot.img_sup (hSbA.trans hAbY)
      hUbY] at hle
    have h1 := SubQuot.le_sup_of_img_le hUx hle
    rw [← hcx] at h1
    have h2 := bar_conj_le_central hC hwclZ c hc h1
    rw [hcx] at h2
    rw [hEhdef, ← SubQuot.img_rightConjugate, hVhdef, sup_bot_eq]
    refine (SubQuot.img_mono h2).trans ?_
    rw [SubQuot.img_sup hUbY hZbY, SubQuot.img_eq_bot le_rfl, sup_bot_eq]
  have f_card : Nat.card Vh < Nat.card Eh := by
    have hE1 := SubQuot.card_img_mul (N := Zb) hUbY
    have hUZ : Ub ⊓ Zb = ⊥ := le_bot_iff.mp (hUA ▸ inf_le_inf_left Ub hZbA)
    rw [hUZ, Subgroup.card_bot, mul_one, EndHyp.card_barU hC] at hE1
    rw [← hEhdef] at hE1
    rw [hE1, hVhdef, Subgroup.card_bot]
    have := four_le_card_U hloc hC d
    omega
  have hset : EndSetting Ah Eh Sh Vh Xh :=
    { normal := f_normal
      sup_eq := f_sup
      inf_eq := f_inf
      elem := f_elem
      simple := fun l => (hsimple l).1
      nonabelian := fun l => (hsimple l).2
      le := fun l => SubQuot.img_mono (hKA l)
      comm := f_comm
      gen := f_gen
      perm := f_perm
      sylow := f_sylow
      sylow_normalizer := f_sylowN
      V_le := f_Vle
      V_elem := f_Velem
      V_closed := f_Vcl
      V_comm := f_Vcomm
      comm_le := f_comm_le
      wcl := f_wcl
      card_lt := f_card }
  have hKle : ∀ l, K l ≤ bar D (A ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g) := by
    intro l
    obtain ⟨e, he, he1, hecomm⟩ := hset.exists_centralizing hin l
    obtain ⟨u₁, hu₁, rfl⟩ := SubQuot.mem_img.mp he
    obtain ⟨u₂, hu₂U, hu₂⟩ := (mem_bar_iff D U (u₁ : Bar D)).mp hu₁
    have hu1 : (u₂ : G) ≠ 1 := by
      intro h1
      apply he1
      have h2 : u₂ = 1 := Subtype.ext h1
      have h3 : u₁ = 1 := by
        apply Subtype.ext
        rw [← hu₂, h2, map_one]
        rfl
      rw [h3, map_one]
    have : Group.IsPerfect (K l) := component_perfect (hK l).1
    set X := Subgroup.zpowers (u₁ : Bar D) with hXdef
    have hXK : ⁅X, K l⁆ ≤ Zb := by
      rw [Subgroup.commutator_le]
      intro x hx k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hcomm : SubQuot.proj Y₀ Zb (u₁ ^ n) * SubQuot.proj Y₀ Zb ⟨k, hKY l hk⟩ =
          SubQuot.proj Y₀ Zb ⟨k, hKY l hk⟩ * SubQuot.proj Y₀ Zb (u₁ ^ n) := by
        rw [map_zpow]
        exact ((Commute.zpow_left (hecomm _ (SubQuot.proj_mem_img (x := ⟨k, hKY l hk⟩) hk))
          n)).eq
      have hker1 : SubQuot.proj Y₀ Zb ⁅u₁ ^ n, ⟨k, hKY l hk⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm
      have h1 := (SubQuot.proj_eq_one_iff _).mp hker1
      have hcoe : ((⁅u₁ ^ n, ⟨k, hKY l hk⟩⁆ : Y₀) : Bar D) = ⁅(u₁ : Bar D) ^ n, k⁆ := by
        simp [commutatorElement_def]
      rwa [hcoe] at h1
    have hZK : ⁅Zb, K l⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (centerBar_comm A hz k (hKA l hk)).symm
    have h3 : ⁅⁅X, K l⁆, K l⁆ = ⊥ :=
      le_bot_iff.mp (hZK ▸ Subgroup.commutator_mono hXK le_rfl)
    have h4 := AschbacherComponentAction.perfect_three_subgroup_action (K l) X h3
    have hKC : K l ≤ bar D A ⊓ Subgroup.centralizer
        ({toBar D ⟨(u₂ : G), EndHyp.U_le_H hC hu₂U⟩} : Set (Bar D)) := by
      intro k hk
      refine ⟨hKA l hk, ?_⟩
      show k ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h5 := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers (u₁ : Bar D)) hk
      rw [h4, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h5
      have h6 : toBar D ⟨(u₂ : G), EndHyp.U_le_H hC hu₂U⟩ = (u₁ : Bar D) := hu₂
      rw [h6]
      exact h5.symm
    exact hKC.trans (barA_inf_centralizer_le_of_comm hC hT hu₂U hu1)
  apply EndHyp.false_of_barA_le (d := d) hC
  show Ab ≤ _
  rw [← hKgen]
  exact iSup_le hKle


end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
