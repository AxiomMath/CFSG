module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocWiel

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open

theorem odd_orderOf_mul_of_subnormal {Y : Type} [Group Y] [Finite Y] {C K : Subgroup Y}
    (hK : CFSG.Open.IsSubnormal K C) (hK22 : IsTwoPrimeTwo K) {x : Y} (hx : x ∈ K) {g₁ g₂ : Y}
    (hg₁ : g₁ ∈ C) (hg₂ : g₂ ∈ C) {a b : Y}
    (ha : a ∈ Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set Y))
    (hb : b ∈ Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set Y))
    (hao : Odd (orderOf a)) (hbo : Odd (orderOf b)) : Odd (orderOf (a * b)) := by
  have hKC : K ≤ C := hK.le
  set K₀ : Subgroup ↥C := K.subgroupOf C with hK₀
  have hK₀sub : K₀.IsSubnormal := hK.subgroupOf
  have hK₀22 : IsTwoPrimeTwo K₀ := by
    obtain ⟨O, hOK, hOn, hodd, hq⟩ := hK22
    have hOC : O ≤ C := hOK.trans hKC
    have hle : O.subgroupOf C ≤ K₀ := fun o ho => hOK ho
    refine ⟨O.subgroupOf C, hle, ?_, ?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff hle]
      intro h k hh hk
      exact (Subgroup.normal_subgroupOf_iff hOK).mp hOn h k hh hk
    · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv] at hodd
      exact hodd
    · intro g hg
      obtain ⟨k, hk⟩ := hq (g : Y) hg
      exact ⟨k, hk⟩
  obtain ⟨M, hKM, hMn, hM22⟩ := exists_normal_twoPrimeTwo_of_subnormal hK₀sub hK₀22
  let x₀ : ↥C := ⟨x, hKC hx⟩
  let h₁ : ↥C := ⟨g₁, hg₁⟩
  let h₂ : ↥C := ⟨g₂, hg₂⟩
  have hx₀ : x₀ ∈ M := hKM hx
  have hxM : ∀ h : ↥C, h * x₀ * h⁻¹ ∈ M := fun h => hMn.conj_mem x₀ hx₀ h
  have hclos : Subgroup.closure ({x₀, h₁ * x₀ * h₁⁻¹, h₂ * x₀ * h₂⁻¹} : Set ↥C) ≤ M := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hx₀
    · exact hxM h₁
    · exact hxM h₂
  have himg : (Subgroup.closure ({x₀, h₁ * x₀ * h₁⁻¹, h₂ * x₀ * h₂⁻¹} : Set ↥C)).map C.subtype =
      Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set Y) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [x₀, h₁, h₂, Set.image_insert_eq, Set.image_singleton]
  rw [← himg] at ha hb
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have hord : ∀ c : ↥C, orderOf (C.subtype c) = orderOf c := fun c =>
    orderOf_injective C.subtype C.subtype_injective c
  rw [← map_mul, hord]
  rw [hord] at hao hbo
  exact odd_orderOf_mul_of_isTwoPrimeTwo hM22 (hclos ha₀) (hclos hb₀) hao hbo

@[expose] def PairWit {W : Type*} [Group W] (F₀ : Subgroup W) (x t : W) : Prop :=
  ∃ g₁ ∈ F₀, ∃ g₂ ∈ F₀, g₁ * t = t * g₁ ∧ g₂ * t = t * g₂ ∧
    ∃ a ∈ Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set W),
      ∃ b ∈ Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set W),
        Odd (orderOf a) ∧ Odd (orderOf b) ∧ Even (orderOf (a * b))

theorem PairWit.conj {W : Type*} [Group W] {F₀ : Subgroup W} (hF₀ : F₀.Normal) {x t : W}
    (h : PairWit F₀ x t) (s : W) : PairWit F₀ (s * x * s⁻¹) (s * t * s⁻¹) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hc₁, hc₂, a, ha, b, hb, hao, hbo, hab⟩ := h
  have hcj : Function.Injective (MulAut.conj s : W →* W) := (MulAut.conj s).injective
  have hord : ∀ c : W, orderOf (MulAut.conj s c) = orderOf c := fun c =>
    orderOf_injective (MulAut.conj s : W →* W) hcj c
  have himg : (Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set W)).map
      (MulAut.conj s : W →* W) =
      Subgroup.closure ({s * x * s⁻¹, (s * g₁ * s⁻¹) * (s * x * s⁻¹) * (s * g₁ * s⁻¹)⁻¹,
        (s * g₂ * s⁻¹) * (s * x * s⁻¹) * (s * g₂ * s⁻¹)⁻¹} : Set W) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, MulAut.conj_apply, map_mul, map_inv]
    simp [mul_assoc]
  refine ⟨s * g₁ * s⁻¹, hF₀.conj_mem g₁ hg₁ s, s * g₂ * s⁻¹, hF₀.conj_mem g₂ hg₂ s, ?_, ?_,
    s * a * s⁻¹, ?_, s * b * s⁻¹, ?_, ?_, ?_, ?_⟩
  · calc s * g₁ * s⁻¹ * (s * t * s⁻¹) = s * (g₁ * t) * s⁻¹ := by group
      _ = s * (t * g₁) * s⁻¹ := by rw [hc₁]
      _ = s * t * s⁻¹ * (s * g₁ * s⁻¹) := by group
  · calc s * g₂ * s⁻¹ * (s * t * s⁻¹) = s * (g₂ * t) * s⁻¹ := by group
      _ = s * (t * g₂) * s⁻¹ := by rw [hc₂]
      _ = s * t * s⁻¹ * (s * g₂ * s⁻¹) := by group
  · rw [← himg]
    exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  · rw [← himg]
    exact ⟨b, hb, by simp [MulAut.conj_apply]⟩
  · have := hord a
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hao
  · have := hord b
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hbo
  · have := hord (a * b)
    rw [MulAut.conj_apply] at this
    rw [show s * a * s⁻¹ * (s * b * s⁻¹) = s * (a * b) * s⁻¹ by group, this]
    exact hab

theorem orderOf_eq_eight_of {G : Type*} [Group G] {x : G} (h4 : x ^ 4 ≠ 1) (h8 : x ^ 8 = 1) :
    orderOf x = 8 := by
  have hd : orderOf x ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h8
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have : j = 3 := by
    by_contra hne
    have hj3 : j ≤ 2 := by omega
    apply h4
    have : orderOf x ∣ 4 := by
      rw [hj']
      calc 2 ^ j ∣ 2 ^ 2 := pow_dvd_pow 2 hj3
        _ = 4 := by norm_num
    exact orderOf_dvd_iff_pow_eq_one.mp this
  rw [hj', this]
  norm_num

theorem isPGroup_closure_pair {G : Type*} [Group G] {x t : G} (hx : orderOf x = 8)
    (ht : orderOf t = 2) (hc : x * t = t * x) :
    IsPGroup 2 ↥(Subgroup.closure ({x, t} : Set G)) := by
  have hX : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_zpowers, hx]
    norm_num
  have hT : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht]
    norm_num
  have hN : Subgroup.zpowers t ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute x t from hc) i j).eq
  have hsup := hX.to_sup_of_normal_left' hT hN
  have hcl : Subgroup.closure ({x, t} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers t := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  rw [hcl]
  exact hsup

theorem orderOf_conj_eq {W : Type*} [Group W] (g x : W) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g : W →* W) (MulAut.conj g).injective x

theorem pairWit_of_sylow {W : Type*} [Group W] [Finite W] {F₀ S : Subgroup W} (hF₀ : F₀.Normal)
    (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.index)
    (h : ∀ x ∈ S, ∀ t ∈ S, orderOf x = 8 → orderOf t = 2 → x * t = t * x → PairWit F₀ x t)
    {x t : W} (hx : orderOf x = 8) (ht : orderOf t = 2) (hc : x * t = t * x) :
    PairWit F₀ x t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := (isPGroup_closure_pair hx ht hc).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W (hS.toSylow hidx) T
  have hmem : ∀ z : W, z ∈ Subgroup.closure ({x, t} : Set W) → g⁻¹ * z * g ∈ S := by
    intro z hz
    have hzT : z ∈ (T : Subgroup W) := hT hz
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hzT
    obtain ⟨s, hs, hsz⟩ := hzT
    have hs' : s = g⁻¹ * z * g := by
      rw [← hsz]
      simp [MulAut.conj_apply, mul_assoc]
    rw [← hs']
    exact hs
  have hx' := hmem x (Subgroup.subset_closure (by simp))
  have ht' := hmem t (Subgroup.subset_closure (by simp))
  have hord : ∀ z : W, orderOf (g⁻¹ * z * g) = orderOf z := fun z => by
    have := orderOf_conj_eq g⁻¹ z
    rwa [inv_inv] at this
  have hw := h _ hx' _ ht' (by rw [hord, hx]) (by rw [hord, ht])
    (by
      calc g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
        _ = g⁻¹ * (t * x) * g := by rw [hc]
        _ = g⁻¹ * t * g * (g⁻¹ * x * g) := by group)
  have := hw.conj hF₀ g
  simpa [mul_assoc] using this

theorem not_order_eight_of_pairWit {Y : Type} [Group Y] [Finite Y] {W : Type*} [Group W]
    (ρ : Y →* W) (hρ : Function.Injective ρ) {F₀ : Subgroup W} (hF₀ : F₀ ≤ ρ.range)
    (H : ∀ x t : W, orderOf x = 8 → orderOf t = 2 → x * t = t * x → PairWit F₀ x t)
    {t : Y} (ht : orderOf t = 2) {K : Subgroup Y}
    (hK : CFSG.Open.IsSubnormal K (Subgroup.centralizer ({t} : Set Y))) (hK22 : IsTwoPrimeTwo K)
    {x : Y} (hx : x ∈ K) : orderOf x ≠ 8 := by
  intro h8
  have hxC : x ∈ Subgroup.centralizer ({t} : Set Y) := hK.le hx
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hord : ∀ y : Y, orderOf (ρ y) = orderOf y := fun y => orderOf_injective ρ hρ y
  obtain ⟨g₁, hg₁, g₂, hg₂, hc₁, hc₂, a, ha, b, hb, hao, hbo, hab⟩ :=
    H (ρ x) (ρ t) (by rw [hord, h8]) (by rw [hord, ht]) (by rw [← map_mul, ← map_mul, hxt])
  obtain ⟨y₁, rfl⟩ := hF₀ hg₁
  obtain ⟨y₂, rfl⟩ := hF₀ hg₂
  have hy₁ : y₁ ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hρ (by rw [map_mul, map_mul]; exact hc₁)
  have hy₂ : y₂ ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hρ (by rw [map_mul, map_mul]; exact hc₂)
  have himg : (Subgroup.closure ({x, y₁ * x * y₁⁻¹, y₂ * x * y₂⁻¹} : Set Y)).map ρ =
      Subgroup.closure ({ρ x, ρ y₁ * ρ x * (ρ y₁)⁻¹, ρ y₂ * ρ x * (ρ y₂)⁻¹} : Set W) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_inv]
  rw [← himg] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  rw [hord] at hao hbo
  rw [← map_mul, hord] at hab
  exact (Nat.not_even_iff_odd.mpr (odd_orderOf_mul_of_subnormal hK hK22 hx hy₁ hy₂ ha' hb' hao hbo))
    hab

theorem localNoQ16Q16_of_pairWit {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → ∀ x t : MulAut F, orderOf x = 8 → orderOf t = 2 →
      x * t = t * x → PairWit (MulAut.conj : F →* MulAut F).range x t) : LocalNoQ16Q16 P := by
  intro F _ hF Y _ _ N _ hN hC t ht K K' hK hK' h22 h22' x hx y hy x' hx' y' hy' hq
  obtain ⟨e⟩ := hN
  have hinj : Function.Injective (MulAut.conjNormal : Y →* MulAut ↥N) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : y ∈ Subgroup.centralizer (N : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have := congrArg (fun α : MulAut ↥N => ((α ⟨m, hm⟩ : ↥N) : Y)) hy
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc m * y = (y * m * y⁻¹) * y := by rw [this]
        _ = y * m := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact h1
  let ρ : Y →* MulAut F := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥N)
  have hρ : Function.Injective ρ := (MulAut.congr e).injective.comp hinj
  have hF₀ : (MulAut.conj : F →* MulAut F).range ≤ ρ.range := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨m, rfl⟩ := e.surjective f
    refine ⟨(m : Y), ?_⟩
    ext z
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulAut.conjNormal_val, MulAut.conj_apply]
    simp
  have hx8 : orderOf x = 8 := orderOf_eq_eight_of hq.1.1 hq.1.2.1
  exact not_order_eight_of_pairWit ρ hρ hF₀ (h F hF) ht hK h22 hx hx8

theorem PairWit.mono {W : Type*} [Group W] {F₀ F₁ : Subgroup W} (hle : F₀ ≤ F₁) {x t : W}
    (h : PairWit F₀ x t) : PairWit F₁ x t := by
  obtain ⟨g₁, hg₁, g₂, hg₂, rest⟩ := h
  exact ⟨g₁, hle hg₁, g₂, hle hg₂, rest⟩

theorem PairWit.map {W W' : Type*} [Group W] [Group W'] (f : W →* W')
    (hf : Function.Injective f) {F₀ : Subgroup W} {x t : W} (h : PairWit F₀ x t) :
    PairWit (F₀.map f) (f x) (f t) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hc₁, hc₂, a, ha, b, hb, hao, hbo, hab⟩ := h
  have hord : ∀ c : W, orderOf (f c) = orderOf c := fun c => orderOf_injective f hf c
  have himg : (Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set W)).map f =
      Subgroup.closure ({f x, f g₁ * f x * (f g₁)⁻¹, f g₂ * f x * (f g₂)⁻¹} : Set W') := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_inv]
  refine ⟨f g₁, Subgroup.mem_map_of_mem f hg₁, f g₂, Subgroup.mem_map_of_mem f hg₂,
    by rw [← map_mul, ← map_mul, hc₁], by rw [← map_mul, ← map_mul, hc₂],
    f a, ?_, f b, ?_, ?_, ?_, ?_⟩
  · rw [← himg]
    exact Subgroup.mem_map_of_mem f ha
  · rw [← himg]
    exact Subgroup.mem_map_of_mem f hb
  · rw [hord]
    exact hao
  · rw [hord]
    exact hbo
  · rw [← map_mul, hord]
    exact hab

theorem pairWit_of_equiv {F F' : Type} [Group F] [Group F'] (e : F ≃* F')
    (h : ∀ x t : MulAut F', orderOf x = 8 → orderOf t = 2 → x * t = t * x →
      PairWit (MulAut.conj : F' →* MulAut F').range x t) :
    ∀ x t : MulAut F, orderOf x = 8 → orderOf t = 2 → x * t = t * x →
      PairWit (MulAut.conj : F →* MulAut F).range x t := by
  intro x t hx ht hxt
  let φ : MulAut F ≃* MulAut F' := MulAut.congr e
  have hord : ∀ c : MulAut F, orderOf (φ c) = orderOf c := fun c =>
    orderOf_injective φ.toMonoidHom φ.injective c
  have h1 := h (φ x) (φ t) (by rw [hord, hx]) (by rw [hord, ht])
    (by rw [← map_mul, ← map_mul, hxt])
  have h2 := h1.map φ.symm.toMonoidHom φ.symm.injective
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h2
  refine h2.mono ?_
  rintro _ ⟨_, ⟨f', rfl⟩, rfl⟩
  refine ⟨e.symm f', ?_⟩
  ext z
  simp [φ, MulAut.conj_apply, MulAut.congr_symm_apply]

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
