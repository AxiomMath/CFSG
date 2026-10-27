module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelGlobalAut
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Main
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Fischer
open scoped commutatorElement

structure U52Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop where
  setting : CFSG.EvenSmallLie.StandardSetting G L
  center : center L = ⊥
  model : LieModel L .PSU 5 2 1

structure Data (G : Type) [Group G] where
  L : Subgroup G
  t : G
  η : L ≃* SU52

namespace Data

variable {G : Type} [Group G] (d : Data G)

@[expose] def ι : SU52 →* G := d.L.subtype.comp d.η.symm.toMonoidHom

@[expose] def pull (M : Subgroup SU52) : Subgroup G := M.map d.ι

@[expose] def H : Subgroup G := centralizer ({d.t} : Set G)

@[expose] def withT (X : Subgroup G) : Subgroup G := X ⊔ zpowers d.t

@[expose] def S : Subgroup G := d.pull Ssub

@[expose] def R : Subgroup G := d.withT d.S

@[expose] def A₁ : Subgroup G := d.pull A₁sub

@[expose] def A₂ : Subgroup G := d.pull A₂sub

@[expose] def F : Subgroup G := d.pull Fsub

@[expose] def X₂ : Subgroup G := d.pull X₂sub

@[expose] def X₃ : Subgroup G := d.pull X₃sub

@[expose] def X₄ : Subgroup G := d.pull X₄sub

@[expose] def ZX₄ : Subgroup G := d.pull ZX₄sub

@[expose] def K₂ : Subgroup G := d.pull K₂sub

@[expose] def K₃ : Subgroup G := d.pull K₃sub

@[expose] def e₁ : G := d.ι e₁SU

@[expose] def e₂ : G := d.ι e₂SU

@[expose] def u : G := d.ι uSU

@[expose] def v : G := d.ι vSU

theorem ι_mem (g : SU52) : d.ι g ∈ d.L := (d.η.symm g).2

theorem ι_injective : Function.Injective d.ι :=
  d.L.subtype_injective.comp d.η.symm.injective

@[simp] theorem ι_η (l : d.L) : d.ι (d.η l) = l := by
  simp [ι]

theorem range_ι : d.ι.range = d.L := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact d.ι_mem g
  · intro hx
    exact ⟨d.η ⟨x, hx⟩, by rw [ι_η]⟩

theorem pull_le_L (M : Subgroup SU52) : d.pull M ≤ d.L := by
  rintro _ ⟨g, -, rfl⟩
  exact d.ι_mem g

theorem card_pull (M : Subgroup SU52) : Nat.card (d.pull M) = Nat.card M :=
  Subgroup.card_map_of_injective d.ι_injective

theorem pull_mono {M M' : Subgroup SU52} (h : M ≤ M') : d.pull M ≤ d.pull M' :=
  Subgroup.map_mono h

theorem ι_mem_pull_iff {M : Subgroup SU52} {g : SU52} : d.ι g ∈ d.pull M ↔ g ∈ M :=
  ⟨fun ⟨_, hg, e⟩ => d.ι_injective e ▸ hg, fun hg => ⟨g, hg, rfl⟩⟩

theorem pull_sup (M M' : Subgroup SU52) : d.pull (M ⊔ M') = d.pull M ⊔ d.pull M' :=
  Subgroup.map_sup M M' d.ι

theorem pull_inf (M M' : Subgroup SU52) : d.pull (M ⊓ M') = d.pull M ⊓ d.pull M' :=
  Subgroup.map_inf M M' d.ι d.ι_injective

theorem F_le_A₂ : d.F ≤ d.A₂ := d.pull_mono Fsub_le_A₂sub

theorem A₂_le_S : d.A₂ ≤ d.S := d.pull_mono A₂sub_le_Ssub

theorem A₁_le_S : d.A₁ ≤ d.S := d.pull_mono A₁sub_le_Ssub

theorem card_S : Nat.card d.S = 2 ^ 10 := by rw [S, card_pull, card_Ssub]

theorem card_A₁ : Nat.card d.A₁ = 2 ^ 7 := by rw [A₁, card_pull, card_A₁sub]

theorem card_A₂ : Nat.card d.A₂ = 2 ^ 8 := by rw [A₂, card_pull, card_A₂sub]

theorem card_F : Nat.card d.F = 2 ^ 4 := by rw [F, card_pull, card_Fsub]

end Data

structure Data.Hyp {G : Type} [Group G] [Finite G] (d : Data G) : Prop where
  setting : U52Setting G d.L
  t_mem : d.t ∈ centralizer (d.L : Set G)
  t_two : orderOf d.t = 2

theorem exists_data {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : U52Setting G L) :
    ∃ d : Data G, d.L = L ∧ d.Hyp := by
  obtain ⟨η⟩ := modelEquiv h.model
  have heven : Even (Nat.card (centralizer (L : Set G))) := h.setting.standard.2.1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2
    (even_iff_two_dvd.1 heven)
  exact ⟨⟨L, t, η⟩, rfl, h, t.2, by rw [← ht, orderOf_coe]⟩

theorem u52CenterlessExclusion_of_hyp
    (h : ∀ (G : Type) [Group G] [Finite G] (d : Data G), d.Hyp → False) :
    U52CenterlessExclusion := by
  intro G _ _ L hset hZ hm
  obtain ⟨d, -, hd⟩ := exists_data ⟨hset, hZ, hm⟩
  exact h G d hd

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem simple (h : d.Hyp) : IsSimpleGroup G := h.setting.setting.simple

theorem nonab (h : d.Hyp) : ∃ a b : G, a * b ≠ b * a := h.setting.setting.nonab

theorem standard (h : d.Hyp) : standardComponentIsStandard d.L := h.setting.setting.standard

theorem core (h : d.Hyp) (x : G) (hx : orderOf x = 2) :
    standardComponentOddCore (centralizer ({x} : Set G)) = ⊥ :=
  h.setting.setting.core x hx

theorem center_eq_bot (h : d.Hyp) : center d.L = ⊥ := h.setting.center

theorem inf_centralizer_eq_bot (h : d.Hyp) : d.L ⊓ centralizer (d.L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : d.L) ∈ center d.L :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)
  rw [h.center_eq_bot, mem_bot] at hx
  exact mem_bot.2 (congrArg Subtype.val hx)

theorem t_ne_one (h : d.Hyp) : d.t ≠ 1 := fun h1 => by
  have := h.t_two
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem t_mul_t (h : d.Hyp) : d.t * d.t = 1 := by
  rw [← sq, ← h.t_two, pow_orderOf_eq_one]

theorem t_inv (h : d.Hyp) : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right h.t_mul_t

theorem t_not_mem_L (h : d.Hyp) : d.t ∉ d.L := fun htL => by
  have : d.t ∈ d.L ⊓ centralizer (d.L : Set G) := ⟨htL, h.t_mem⟩
  rw [h.inf_centralizer_eq_bot, mem_bot] at this
  exact h.t_ne_one this

theorem card_zpowers_t (h : d.Hyp) : Nat.card (zpowers d.t) = 2 := by
  rw [Nat.card_zpowers, h.t_two]

theorem H_le_normalizer (h : d.Hyp) : d.H ≤ normalizer (d.L : Set G) :=
  (ComponentInitial.standard_involution_centralizer_normality h.standard h.t_mem h.t_two).1

theorem L_le_H (h : d.Hyp) : d.L ≤ d.H :=
  (ComponentInitial.standard_involution_centralizer_normality h.standard h.t_mem h.t_two).2.1

theorem normal_subgroupOf (h : d.Hyp) : (d.L.subgroupOf d.H).Normal :=
  (ComponentInitial.standard_involution_centralizer_normality h.standard h.t_mem h.t_two).2.2.1

theorem t_mem_H (_h : d.Hyp) : d.t ∈ d.H := mem_centralizer_singleton_iff.2 rfl

theorem isCyclic_sylow (h : d.Hyp) (P : Sylow 2 (centralizer (d.L : Set G))) :
    IsCyclic (P : Subgroup (centralizer (d.L : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := h.setting.setting.cyclic
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (centralizer (d.L : Set G)) P₀ P
  rw [Sylow.coe_subgroup_smul]
  exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap
    (P₀ : Subgroup (centralizer (d.L : Set G)))) (MonoidHom.subgroupMap_surjective _ _)

theorem kernel (h : d.Hyp) :
    IsCyclic (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) ∧
      IsPGroup 2 (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) ∧
      (∀ x ∈ centralizer (d.L : Set G) ⊓ d.H, orderOf x = 2 → x = d.t) ∧
      ((centralizer (d.L : Set G) ⊓ d.H).subgroupOf d.H).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tc : centralizer (d.L : Set G) := ⟨d.t, h.t_mem⟩ with htc
  have htc2 : orderOf tc = 2 := by rw [← orderOf_coe]; exact h.t_two
  have hz : IsPGroup 2 (zpowers tc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htc2, pow_one])
  obtain ⟨P, hPt⟩ := hz.exists_le_sylow
  have htP : tc ∈ P := hPt (mem_zpowers _)
  have hPc := h.isCyclic_sylow P
  obtain ⟨-, huniq, -, -, -, -, hR, hRn, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      h.standard P hPc htP htc2 (h.core d.t h.t_two)
  have hR' : centralizer (d.L : Set G) ⊓ d.H =
      (P : Subgroup (centralizer (d.L : Set G))).map (centralizer (d.L : Set G)).subtype := hR
  rw [hR']
  refine ⟨isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _),
    P.isPGroup'.map _, ?_, hRn⟩
  rintro _ ⟨y, hy, rfl⟩ hy2
  rw [Subgroup.subtype_apply, orderOf_coe] at hy2
  exact congrArg Subtype.val (huniq y hy hy2)

theorem t_mem_kernel (h : d.Hyp) : d.t ∈ centralizer (d.L : Set G) ⊓ d.H :=
  ⟨h.t_mem, h.t_mem_H⟩

theorem kernel_comm (h : d.Hyp) {c c' : G} (hc : c ∈ centralizer (d.L : Set G) ⊓ d.H)
    (hc' : c' ∈ centralizer (d.L : Set G) ⊓ d.H) : c * c' = c' * c := by
  have := h.kernel.1
  exact congrArg Subtype.val (mul_comm' (⟨c, hc⟩ :
    (centralizer (d.L : Set G) ⊓ d.H : Subgroup G)) ⟨c', hc'⟩)

theorem eq_t_of_mem_kernel (h : d.Hyp) {x : G} (hx : x ∈ centralizer (d.L : Set G) ⊓ d.H)
    (hx2 : orderOf x = 2) : x = d.t :=
  h.kernel.2.2.1 x hx hx2

theorem eq_one_or_eq_t_of_mem_kernel (h : d.Hyp) {x : G}
    (hx : x ∈ centralizer (d.L : Set G) ⊓ d.H) (hx2 : x * x = 1) : x = 1 ∨ x = d.t := by
  by_cases h1 : x = 1
  · exact Or.inl h1
  · right
    exact h.eq_t_of_mem_kernel hx (orderOf_eq_prime (by rw [sq, hx2]) h1)

@[expose] def act (h : d.Hyp) : d.H →* MulAut SU52 :=
  (UnitaryFiveTwo.act d.L d.η).comp (inclusion h.H_le_normalizer)

theorem coe_symm_act_apply (h : d.Hyp) (x : d.H) (g : SU52) :
    ((d.η.symm (h.act x g) : d.L) : G) = x * (d.η.symm g : G) * (x : G)⁻¹ :=
  UnitaryFiveTwo.coe_symm_act_apply d.L d.η _ g

theorem ι_act_apply (h : d.Hyp) (x : d.H) (g : SU52) :
    d.ι (h.act x g) = x * d.ι g * (x : G)⁻¹ :=
  h.coe_symm_act_apply x g

theorem act_eq_one_iff (h : d.Hyp) (x : d.H) :
    h.act x = 1 ↔ (x : G) ∈ centralizer (d.L : Set G) :=
  UnitaryFiveTwo.act_eq_one_iff d.L d.η _

theorem act_of_mem (h : d.Hyp) {l : G} (hl : l ∈ d.L) :
    h.act ⟨l, h.L_le_H hl⟩ = MulAut.conj (d.η ⟨l, hl⟩) :=
  UnitaryFiveTwo.act_mem d.L d.η ⟨l, hl⟩

@[expose] def fieldFactor (h : d.Hyp) : d.H →* (F4 ≃+* F4) :=
  UnitaryFiveTwo.fieldFactor.comp h.act

theorem fieldFactor_eq_one_iff (h : d.Hyp) (x : d.H) :
    h.fieldFactor x = 1 ↔ ∃ l ∈ d.L, ∃ c ∈ centralizer (d.L : Set G) ⊓ d.H, (x : G) = l * c := by
  change fieldFactorG d.L d.η _ = 1 ↔ _
  rw [fieldFactorG_eq_one_iff]
  constructor
  · rintro ⟨l, hl, c, hc, hx⟩
    change (x : G) = l * c at hx
    refine ⟨l, hl, c, ⟨hc, ?_⟩, hx⟩
    have := mul_mem (inv_mem (h.L_le_H hl)) x.2
    rwa [show l⁻¹ * (x : G) = c by rw [hx]; group] at this
  · rintro ⟨l, hl, c, hc, hx⟩
    exact ⟨l, hl, c, hc.1, hx⟩

theorem mem_L_sup_kernel_iff (_h : d.Hyp) {x : G} :
    x ∈ d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H) ↔
      ∃ l ∈ d.L, ∃ c ∈ centralizer (d.L : Set G) ⊓ d.H, x = l * c := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.L
    (centralizer (d.L : Set G) ⊓ d.H) fun l hl c hc => mem_centralizer_iff.1 hc.1 l hl).2
  have e : x ∈ d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H) ↔
      x ∈ ((d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H) : Subgroup G) : Set G) := Iff.rfl
  rw [e, hset]
  constructor
  · rintro ⟨l, hl, c, hc, hlc⟩
    exact ⟨l, hl, c, hc, hlc.symm⟩
  · rintro ⟨l, hl, c, hc, rfl⟩
    exact ⟨l, hl, c, hc, rfl⟩

theorem ker_fieldFactor (h : d.Hyp) :
    h.fieldFactor.ker = (d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H)).subgroupOf d.H := by
  ext x
  rw [MonoidHom.mem_ker, fieldFactor_eq_one_iff, mem_subgroupOf, h.mem_L_sup_kernel_iff]

theorem index_le_two (h : d.Hyp) :
    ((d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H)).subgroupOf d.H).index ≤ 2 := by
  rw [← h.ker_fieldFactor, Subgroup.index_ker]
  calc Nat.card (Set.range h.fieldFactor) ≤ Nat.card (F4 ≃+* F4) :=
        Nat.card_le_card_of_injective (fun x => (x : F4 ≃+* F4)) Subtype.val_injective
    _ = 2 := card_ringEquiv_F4

theorem commutator_L (h : d.Hyp) : ⁅d.L, d.L⁆ = d.L := by
  have h1 : commutator d.L = ⊤ := h.standard.1.1
  have h2 := congrArg (Subgroup.map d.L.subtype) h1
  rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2

omit [Finite G] in
theorem commutatorElement_mul_mul_eq {a b c e : G} (hcb : c * b = b * c) (hce : c * e = e * c)
    (hea : e * a = a * e) : ⁅a * c, b * e⁆ = ⁅a, b⁆ := by
  have hea' : e * a⁻¹ = a⁻¹ * e := (Commute.inv_right (hea : Commute e a)).eq
  calc ⁅a * c, b * e⁆ = a * (c * b) * e * c⁻¹ * a⁻¹ * e⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (c * e) * c⁻¹ * a⁻¹ * e⁻¹ * b⁻¹ := by rw [hcb]; group
    _ = a * b * (e * a⁻¹) * e⁻¹ * b⁻¹ := by rw [hce]; group
    _ = ⁅a, b⁆ := by rw [hea', commutatorElement_def]; group

theorem perfect_le (h : d.Hyp) {P : Subgroup G} (hP : ⁅P, P⁆ = P) (hPH : P ≤ d.H) : P ≤ d.L := by
  have hcomm : ∀ φ ψ : F4 ≃+* F4, φ * ψ = ψ * φ := by
    intro φ ψ
    rcases ringEquiv_eq_one_or_eq_barEquiv φ with rfl | rfl <;>
      rcases ringEquiv_eq_one_or_eq_barEquiv ψ with rfl | rfl <;> simp
  have hdec : ∀ p ∈ P, ∃ l ∈ d.L, ∃ c ∈ centralizer (d.L : Set G) ⊓ d.H, p = l * c := by
    have hker : P ≤ (h.fieldFactor.ker).map d.H.subtype := by
      rw [← hP, commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, hPH ha⟩ : d.H), ⟨b, hPH hb⟩⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    intro p hp
    obtain ⟨x, hx, rfl⟩ := hker hp
    exact (h.fieldFactor_eq_one_iff x).1 hx
  rw [← hP, commutator_le]
  intro a ha b hb
  obtain ⟨l, hl, c, hc, rfl⟩ := hdec a ha
  obtain ⟨l', hl', c', hc', rfl⟩ := hdec b hb
  rw [commutatorElement_mul_mul_eq (mem_centralizer_iff.1 hc.1 l' hl').symm
    (h.kernel_comm hc hc') (mem_centralizer_iff.1 hc'.1 l hl).symm]
  have hll := commutator_mem_commutator hl hl'
  rwa [h.commutator_L] at hll

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
