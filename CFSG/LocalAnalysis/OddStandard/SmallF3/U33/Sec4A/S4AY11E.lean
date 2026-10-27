module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AS3Rec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma38
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11B
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Abstract

theorem m11_card_mul_le_sup {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (h : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) := by
  let Φ : ↥A × ↥B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hEq
    have hEq' : (a₁ : G) * (b₁ : G) = (a₂ : G) * (b₂ : G) := congrArg Subtype.val hEq
    have hu : (a₂ : G)⁻¹ * (a₁ : G) = (b₂ : G) * (b₁ : G)⁻¹ := by
      calc (a₂ : G)⁻¹ * (a₁ : G)
          = (a₂ : G)⁻¹ * ((a₁ : G) * (b₁ : G)) * (b₁ : G)⁻¹ := by group
        _ = (a₂ : G)⁻¹ * ((a₂ : G) * (b₂ : G)) * (b₁ : G)⁻¹ := by rw [hEq']
        _ = (b₂ : G) * (b₁ : G)⁻¹ := by group
    have hmem : (a₂ : G)⁻¹ * (a₁ : G) ∈ A ⊓ B := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a₂.2) a₁.2, ?_⟩
      rw [hu]
      exact Subgroup.mul_mem _ b₂.2 (Subgroup.inv_mem _ b₁.2)
    rw [h, Subgroup.mem_bot] at hmem
    have e1 : (a₁ : G) = (a₂ : G) := (inv_mul_eq_one.mp hmem).symm
    have e2 : (b₁ : G) = (b₂ : G) := by
      rw [hmem] at hu
      exact (mul_inv_eq_one.mp hu.symm).symm
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  have := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_prod] at this

theorem m11_closure_stab {Y : Type} [Group Y] [Finite Y] (W : Subgroup Y)
    {S : Set (MulAut Y)} (hS : ∀ g ∈ S, ∀ w ∈ W, g w ∈ W) :
    ∀ g ∈ Subgroup.closure S, ∀ w ∈ W, g w ∈ W := by
  let Stab : Subgroup (MulAut Y) :=
    { carrier := {g | ∀ w ∈ W, g w ∈ W}
      one_mem' := fun w hw => hw
      mul_mem' := fun {f g} hf hg w hw => hf _ (hg w hw)
      inv_mem' := fun {f} hf w hw => by
        have hinj : Function.Injective (fun u : W => (⟨f u, hf u u.2⟩ : W)) := by
          intro u v huv
          apply Subtype.ext
          exact f.injective (congrArg Subtype.val huv)
        obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.mp hinj ⟨w, hw⟩
        have hfu : f u = w := congrArg Subtype.val hu
        rw [← hfu, MulAut.inv_apply_self]
        exact u.2 }
  exact fun g hg => (Subgroup.closure_le Stab).mpr hS hg

theorem m11_inf_eq_bot {Y : Type} [Group Y] [Finite Y] (a : MulAut Y)
    (hfix : ∀ y : Y, a y = y → y = 1) {W₀ W₁ : Subgroup Y} (h0 : Nat.card W₀ = 4)
    (h1 : Nat.card W₁ = 4) (ha0 : ∀ w ∈ W₀, a w ∈ W₀) (ha1 : ∀ w ∈ W₁, a w ∈ W₁)
    (hne : W₀ ≠ W₁) : W₀ ⊓ W₁ = ⊥ := by
  have hdvd : Nat.card ↥(W₀ ⊓ W₁) ∣ 4 := h0 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hle : Nat.card ↥(W₀ ⊓ W₁) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card ↥(W₀ ⊓ W₁) := Nat.card_pos
  have hcases : Nat.card ↥(W₀ ⊓ W₁) = 1 ∨ Nat.card ↥(W₀ ⊓ W₁) = 2 ∨
      Nat.card ↥(W₀ ⊓ W₁) = 4 := by
    generalize Nat.card ↥(W₀ ⊓ W₁) = n at hdvd hle hpos ⊢
    interval_cases n <;> omega
  rcases hcases with hc | hc | hc
  · exact Subgroup.eq_bot_of_card_eq _ hc
  · exfalso
    obtain ⟨u, hu, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(W₀ ⊓ W₁))).mp hc
    have hau : a (u : Y) ∈ W₀ ⊓ W₁ :=
      Subgroup.mem_inf.mpr ⟨ha0 _ (Subgroup.mem_inf.mp u.2).1, ha1 _ (Subgroup.mem_inf.mp u.2).2⟩
    have hne1 : (⟨a (u : Y), hau⟩ : ↥(W₀ ⊓ W₁)) ≠ 1 := by
      intro h'
      apply hu
      apply Subtype.ext
      have h3 : a (u : Y) = 1 := congrArg Subtype.val h'
      have h4 : a (u : Y) = a 1 := by rw [h3, map_one]
      exact a.injective h4
    have hfix' : a (u : Y) = u := congrArg Subtype.val (huniq _ hne1)
    exact hu (Subtype.ext (hfix _ hfix'))
  · exfalso
    apply hne
    have e0 : W₀ ⊓ W₁ = W₀ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, h0])
    have e1 : W₀ ⊓ W₁ = W₁ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hc, h1])
    rw [← e0, e1]

end Abstract

section Complement

variable {G : Type} [Group G] [Finite G]

theorem m11_exists_complement (Y F₂ : Subgroup G) (hY16 : Nat.card Y = 16)
    (hY2 : ∀ y ∈ Y, y * y = 1) {ρ τ : G}
    (hρY : ρ ∈ normalizer (Y : Set G)) (hτY : τ ∈ normalizer (Y : Set G))
    (hρ3 : ρ ^ 3 = 1) (hτ2 : τ * τ = 1) (hτρ : τ * ρ * τ⁻¹ = ρ⁻¹)
    (hfix : ∀ y ∈ Y, ρ * y = y * ρ → y = 1)
    (hF₂Y : F₂ ≤ Y) (hF₂ : Nat.card F₂ = 4)
    (hF₂ρ : ∀ x ∈ F₂, ρ * x * ρ⁻¹ ∈ F₂) (hF₂τ : ∀ x ∈ F₂, τ * x * τ⁻¹ ∈ F₂) :
    ∃ F' : Subgroup G, F' ≤ Y ∧ Nat.card F' = 4 ∧ F₂ ⊓ F' = ⊥ ∧
      (∀ f ∈ F', ρ * f * ρ⁻¹ ∈ F') ∧ (∀ f ∈ F', τ * f * τ⁻¹ ∈ F') := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : MulAut ↥Y, a = Y.normalizerMonoidHom ⟨ρ, hρY⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : MulAut ↥Y, b = Y.normalizerMonoidHom ⟨τ, hτY⟩ := ⟨_, rfl⟩
  have ha_apply : ∀ y : ↥Y, ((a y : ↥Y) : G) = ρ * y * ρ⁻¹ := fun y => by rw [ha]; rfl
  have hb_apply : ∀ y : ↥Y, ((b y : ↥Y) : G) = τ * y * τ⁻¹ := fun y => by rw [hb]; rfl
  have ha3 : a ^ 3 = 1 := by
    have h1 : (⟨ρ, hρY⟩ : ↥(normalizer (Y : Set G))) ^ 3 = 1 := Subtype.ext hρ3
    rw [ha, ← map_pow, h1, map_one]
  have hb2 : b * b = 1 := by
    have h1 : (⟨τ, hτY⟩ : ↥(normalizer (Y : Set G))) * ⟨τ, hτY⟩ = 1 := Subtype.ext hτ2
    rw [hb, ← map_mul, h1, map_one]
  have hba : b * a * b⁻¹ = a⁻¹ := by
    have h1 : (⟨τ, hτY⟩ : ↥(normalizer (Y : Set G))) * ⟨ρ, hρY⟩ * ⟨τ, hτY⟩⁻¹ =
        ⟨ρ, hρY⟩⁻¹ := Subtype.ext hτρ
    have h2 := congrArg Y.normalizerMonoidHom h1
    rw [ha, hb]
    simpa only [map_mul, map_inv] using h2
  have hfixa : ∀ y : ↥Y, a y = y → y = 1 := by
    intro y hy
    have h2 := congrArg Subtype.val hy
    rw [ha_apply] at h2
    exact Subtype.ext (hfix _ y.2 (mul_inv_eq_iff_eq_mul.mp h2))
  have hord : orderOf a = 3 := by
    refine orderOf_eq_prime ha3 ?_
    intro h1
    obtain ⟨y, hy⟩ : ∃ y : ↥Y, y ≠ 1 := by
      haveI : Nontrivial ↥Y := Finite.one_lt_card_iff_nontrivial.mp (by rw [hY16]; norm_num)
      exact exists_ne 1
    have h2 : a y = y := by rw [h1]; rfl
    exact hy (hfixa y h2)
  haveI : Finite (MulAut ↥Y) := MulEquiv.finite_left
  obtain ⟨e⟩ := nonempty_closure_mulEquiv_perm_three hord hb2 hba
  set H : Subgroup (MulAut ↥Y) := closure ({a, b} : Set (MulAut ↥Y)) with hH
  have haH : a ∈ H := Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := Subgroup.subset_closure (by simp)
  have hnorm : H ≤ normalizer ((zpowers a : Subgroup (MulAut ↥Y)) : Set (MulAut ↥Y)) := by
    rw [hH, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.le_normalizer (Subgroup.mem_zpowers a)
    · rw [hg]
      apply mem_normalizer_of_conj_mem
      intro w hw
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← conj_zpow, hba]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) m
  have hzH : zpowers a ≤ H := Subgroup.zpowers_le.mpr haH
  have hKnormal : ((zpowers a).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hzH).mpr hnorm
  have hKp : IsPGroup 3 ↥((zpowers a).subgroupOf H) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzH).toEquiv, Nat.card_zpowers, hord]
    norm_num
  have hKle : (zpowers a).subgroupOf H ≤ CFSG.pCore 3 ↥H := le_sSup ⟨hKnormal, hKp⟩
  have haP : a ∈ CFSG.Open.pCoreOf 3 H :=
    Subgroup.mem_map.mpr ⟨⟨a, haH⟩,
      hKle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a)), rfl⟩
  have hV : actFixed (MonoidHom.id (MulAut ↥Y))
      (CFSG.Open.pCoreOf 3 H : Set (MulAut ↥Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact Subgroup.mem_bot.mpr (hfixa v (hv a haP))
  have hρ16 : IsAutE16 (MonoidHom.id (MulAut ↥Y)) :=
    isAutE16_id hY16 (fun v => Subtype.ext (by
      show (v : G) ^ 2 = 1
      rw [pow_two]
      exact hY2 _ v.2))
  let T := {W : Subgroup ↥Y // Nat.card W = 4 ∧
    ∀ g ∈ H, ∀ w ∈ W, (MonoidHom.id (MulAut ↥Y)) g w ∈ W}
  have h3 : Nat.card T = 3 := lemma38 hρ16 ⟨e⟩ hV
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
  haveI : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by rw [h3]; norm_num)
  set W₀ : Subgroup ↥Y := F₂.subgroupOf Y with hW₀
  have hW₀card : Nat.card W₀ = 4 := by
    rw [hW₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₂Y).toEquiv]
    exact hF₂
  have hW₀a : ∀ w ∈ W₀, a w ∈ W₀ := fun w hw => by
    rw [hW₀, Subgroup.mem_subgroupOf] at hw ⊢
    rw [ha_apply]
    exact hF₂ρ _ hw
  have hW₀b : ∀ w ∈ W₀, b w ∈ W₀ := fun w hw => by
    rw [hW₀, Subgroup.mem_subgroupOf] at hw ⊢
    rw [hb_apply]
    exact hF₂τ _ hw
  have hW₀H : ∀ g ∈ H, ∀ w ∈ W₀, g w ∈ W₀ := by
    refine m11_closure_stab W₀ (S := {a, b}) ?_
    intro g hg w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact hW₀a w hw
    · rw [hg]
      exact hW₀b w hw
  let w₀ : T := ⟨W₀, hW₀card, fun g hg w hw => hW₀H g hg w hw⟩
  obtain ⟨⟨W₁, hW₁card, hW₁H⟩, hne⟩ := exists_ne w₀
  have hne' : W₀ ≠ W₁ := fun heq => hne (Subtype.ext heq.symm)
  have hW₁a : ∀ w ∈ W₁, a w ∈ W₁ := fun w hw => hW₁H a haH w hw
  have hW₁b : ∀ w ∈ W₁, b w ∈ W₁ := fun w hw => hW₁H b hbH w hw
  have hinf : W₀ ⊓ W₁ = ⊥ := m11_inf_eq_bot a hfixa hW₀card hW₁card hW₀a hW₁a hne'
  refine ⟨W₁.map Y.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact hW₁card
  · rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu₂, hu'⟩ := Subgroup.mem_inf.mp hu
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu'
    have hw₀ : w ∈ W₀ := by
      rw [hW₀, Subgroup.mem_subgroupOf]
      exact hu₂
    have hw' : w ∈ W₀ ⊓ W₁ := Subgroup.mem_inf.mpr ⟨hw₀, hw⟩
    rw [hinf, Subgroup.mem_bot] at hw'
    rw [Subgroup.mem_bot, hw']
    rfl
  · intro f hf
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hf
    exact Subgroup.mem_map.mpr ⟨a w, hW₁a w hw, ha_apply w⟩
  · intro f hf
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hf
    exact Subgroup.mem_map.mpr ⟨b w, hW₁b w hw, hb_apply w⟩

end Complement

section Y11E

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m11_lamt_conj_F2 (h : L41GPh8 t L S x₁ x₂ lam rho) {x : G} (hx : x ∈ fourGrp x₁ x₂) :
    lam * t * x * (lam * t)⁻¹ ∈ fourGrp x₁ x₂ := by
  have hlamN : lam ∈ l41N t x₁ x₂ := n4_K_le_N h.toL41GPh1 (Subgroup.subset_closure (by simp))
  have htN : t ∈ l41N t x₁ x₂ := m13_t_mem_N h.toL41GPh3
  exact h.normalizerFacts.normal_F2.2 (lam * t) (Subgroup.mul_mem _ hlamN htN) x hx

theorem m11_exists_F (h : L41GPh10 t L S x₁ x₂ lam rho) :
    ∃ F' : Subgroup G, F' ≤ l41R t x₁ x₂ rho ∧ CFSG.Open.IsElemAbelian 2 F' ∧
      Nat.card F' = 4 ∧ baseGrp x₁ x₂ ⊓ F' = ⊥ ∧ baseGrp x₁ x₂ ⊔ F' = l41R t x₁ x₂ rho ∧
      (∀ g ∈ closure ({rho, t * lam} : Set G), ∀ f ∈ F', g * f * g⁻¹ ∈ F') ∧
      l41Y t x₁ x₂ rho = fourGrp x₁ x₂ ⊔ F' := by
  have htl : t * lam = lam * t := m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2
  rw [htl]
  obtain ⟨hρN, hlamN, htN⟩ := n4_mem_normalizer_R h.toL41GPh8
  obtain ⟨F', hF'Y, hF'card, hF'inf, hF'ρ, hF'τ⟩ := m11_exists_complement (l41Y t x₁ x₂ rho)
    (fourGrp x₁ x₂) (m11_card_Y h) (fun y hy => ((m11_mem_Y_iff h).mp hy).2) (ρ := rho)
    (τ := lam * t) (m11_mem_normalizer_Y h hρN)
    (m11_mem_normalizer_Y h (Subgroup.mul_mem _ hlamN htN)) (n4_rho_cube h.toCtx0)
    (m11_lamt_sq h.toL41GPh5) (m11_lamt_rho h.toL41GPh5)
    (fun y hy hyρ => m11_fix_R h.toL41GPh8 (m13_Y_le_R t x₁ x₂ rho hy) hyρ)
    (m11_fourGrp_le_Y h) (n4_card_four h.toCtx0)
    (fun x hx => m11_rho_conj_F2 h.toL41GPh8 hx) (fun x hx => m11_lamt_conj_F2 h.toL41GPh8 hx)
  have hF'R : F' ≤ l41R t x₁ x₂ rho := hF'Y.trans (m13_Y_le_R t x₁ x₂ rho)
  have hBinf : baseGrp x₁ x₂ ⊓ F' = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huB, huF⟩ := Subgroup.mem_inf.mp hu
    have hut : u ∈ invCent t := by
      rw [← h.rfacts.cent_t] at huB
      exact (Subgroup.mem_inf.mp huB).2
    have huF₂ : u ∈ fourGrp x₁ x₂ := by
      rw [← m11_Y_inf_cent_t h]
      exact Subgroup.mem_inf.mpr ⟨hF'Y huF, hut⟩
    have hu' : u ∈ fourGrp x₁ x₂ ⊓ F' := Subgroup.mem_inf.mpr ⟨huF₂, huF⟩
    rwa [hF'inf] at hu'
  have hBF : baseGrp x₁ x₂ ⊔ F' = l41R t x₁ x₂ rho := by
    have hle : baseGrp x₁ x₂ ⊔ F' ≤ l41R t x₁ x₂ rho := sup_le (n4_base_le_R h.toL41GPh3) hF'R
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hc := m11_card_mul_le_sup hBinf
    rw [m13_card_B h.toCtx0, hF'card] at hc
    rw [h.rfacts.card_R]
    omega
  have hYF : l41Y t x₁ x₂ rho = fourGrp x₁ x₂ ⊔ F' := by
    have hle : fourGrp x₁ x₂ ⊔ F' ≤ l41Y t x₁ x₂ rho := sup_le (m11_fourGrp_le_Y h) hF'Y
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have hc := m11_card_mul_le_sup hF'inf
    rw [n4_card_four h.toCtx0, hF'card] at hc
    rw [m11_card_Y h]
    omega
  have hF'el : CFSG.Open.IsElemAbelian 2 F' := by
    refine ⟨isMulCommutative_iff.mpr fun u v => Subtype.ext (m11_comm_Y h (hF'Y u.2) (hF'Y v.2)),
      ?_⟩
    intro x hx
    rw [pow_two]
    exact ((m11_mem_Y_iff h).mp (hF'Y hx)).2
  have hF'cl : ∀ g ∈ closure ({rho, lam * t} : Set G), ∀ f ∈ F', g * f * g⁻¹ ∈ F' := by
    have hle : closure ({rho, lam * t} : Set G) ≤ normalizer (F' : Set G) := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · rw [hg]
        exact mem_normalizer_of_conj_mem hF'ρ
      · rw [hg]
        exact mem_normalizer_of_conj_mem hF'τ
    intro g hg f hf
    exact (Subgroup.mem_normalizer_iff.mp (hle hg) f).mp hf
  exact ⟨F', hF'R, hF'el, hF'card, hBinf, hBF, hF'cl, hYF⟩

end Y11E

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
