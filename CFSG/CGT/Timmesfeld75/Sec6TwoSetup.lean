module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.Sec6Four

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.of_isUIdx (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ n m) {h : G} (hh : IsUIdx T T₁ h) :
    Sec6Ctx T (conjSubgroup h T) n m := by
  have := hc.finite
  have hP := hc.hy.pair
  have hy' : StepHyp T (conjSubgroup h T) := hh.stepHyp hc.hy hc.hS
  have hcard : Nat.card (normIn T (conjSubgroup h T)) = Nat.card (normIn T T₁) :=
    hh.card_normIn hP hc.hS
  have hHeq : hSub T (normIn (conjSubgroup h T) T) = hSub T (normIn T₁ T) := by
    rw [← sec58 h1 hy' hc.hS hc.hI, ← sec58 h1 hc.hy hc.hS hc.hI]
    have hiff : ∀ k, IsUIdx T (conjSubgroup h T) k ↔ IsUIdx T T₁ k := fun k => by
      simp only [IsUIdx, hcard]
    simp only [hSubU, hiff]
  refine ⟨hy', hc.hS, hc.hI, by rw [hcard]; exact hc.hq, hc.hT, ?_⟩
  have hcase := hc.hcase
  unfold Sec6Case at hcase ⊢
  rw [hHeq]
  exact hcase

theorem exists_mem_conj_of_mem_classD {y : G} (hy : y ∈ classD T) :
    ∃ k : G, y ∈ conjSubgroup k T := by
  obtain ⟨g, t, ht, -, hyg⟩ := hy
  refine ⟨g⁻¹, mem_conjSubgroup.2 ?_⟩
  have e : g⁻¹⁻¹ * y * g⁻¹ = t := by rw [hyg]; group
  rw [e]
  exact ht

structure Sec62Data (T T₁ : Subgroup G) (x l : G) (T₂ : Subgroup G) : Prop where
  hx : x ∈ normIn T₁ T
  hx1 : x ≠ 1
  hl : l ∈ T
  hD : x * l ∈ classD T
  hT₂ : ∃ k : G, T₂ = conjSubgroup k T
  hyT₂ : x * l ∈ T₂

theorem mem_normIn_of_mul_mul_self (hc : Sec6Ctx T T₁ n m) {x l : G} (hx : x ∈ normIn T₁ T)
    (hx1 : x ≠ 1) (hl : l ∈ T) (hyy : (x * l) * (x * l) = 1) : l ∈ normIn T T₁ := by
  have hS3 := hc.sec3
  have hxT₁ : x ∈ T₁ := normIn_le _ _ hx
  have hxx : x * x = 1 := elemAbelian_mul_self hS3.cfg.wc₁.1 hxT₁
  have hll : l * l = 1 := elemAbelian_mul_self hc.hy.pair.wc.1 hl
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  have h2 : x * l * x = l := by
    have h3 : (x * l * x) * l = 1 := by simpa [mul_assoc] using hyy
    rw [eq_inv_of_mul_eq_one_left h3, hli]
  have hcomm : l * x = x * l := by
    calc l * x = (x * l * x) * x := by rw [h2]
      _ = x * l := by rw [mul_assoc (x * l) x x, hxx, mul_one]
  have : l ∈ T ⊓ Subgroup.centralizer ({x} : Set G) :=
    ⟨hl, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  rwa [hS3.cfg.inf_centralizer_eq_normIn hx hx1] at this

section Data

variable {l : G} {x : G} {T₂ : Subgroup G}

theorem Sec62Data.l_mem (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    l ∈ normIn T T₁ :=
  mem_normIn_of_mul_mul_self hc d.hx d.hx1 d.hl (mul_self_eq_one_of_mem_classD hc.hy.pair.wc.1 d.hD)

theorem Sec62Data.y_mem_normalizer (d : Sec62Data T T₁ x l T₂) :
    x * l ∈ Subgroup.normalizer (T : Set G) :=
  (Subgroup.normalizer (T : Set G)).mul_mem (mem_normIn.1 d.hx).2 (Subgroup.le_normalizer d.hl)

theorem Sec62Data.y_mem_cfgM (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    x * l ∈ cfgM T T₁ :=
  (cfgM T T₁).mul_mem (Cfg.normIn_le_cfgM_right T T₁ d.hx)
    (Cfg.normIn_le_cfgM_left T T₁ (d.l_mem hc))

theorem Sec62Data.y_ne_one (d : Sec62Data T T₁ x l T₂) : x * l ≠ 1 :=
  ne_one_of_mem_classD d.hD

theorem Sec62Data.y_not_mem (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    x * l ∉ T := by
  intro hy
  have hxT : x ∈ T := by
    have := T.mul_mem hy (T.inv_mem d.hl)
    simpa using this
  have : x ∈ T ⊓ T₁ := ⟨hxT, normIn_le _ _ d.hx⟩
  rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at this
  exact d.hx1 this

theorem Sec62Data.T₂_ne (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) : T₂ ≠ T :=
  fun h => d.y_not_mem hc (h ▸ d.hyT₂)

theorem Sec62Data.mem_normIn₂ (d : Sec62Data T T₁ x l T₂) : x * l ∈ normIn T₂ T :=
  mem_normIn.2 ⟨d.hyT₂, d.y_mem_normalizer⟩

variable [Finite G]

theorem Sec62Data.normIn_ne_bot₂ (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    normIn T T₂ ≠ ⊥ := by
  have hne := d.T₂_ne hc
  have hbot : normIn T₂ T ≠ ⊥ := fun hb =>
    d.y_ne_one (Subgroup.mem_bot.1 (hb ▸ d.mem_normIn₂))
  obtain ⟨k, rfl⟩ := d.hT₂
  exact normIn_ne_bot_of_conj hc.hy.pair.wc hne hbot

theorem Sec62Data.sec3₂ (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) : Sec3 T T₂ := by
  have hne := d.T₂_ne hc
  have hbot := d.normIn_ne_bot₂ hc
  obtain ⟨k, rfl⟩ := d.hT₂
  exact hc.hS k hne hbot

omit [Finite G] in
theorem Sec62Data.centralizer_eq (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    T ⊓ Subgroup.centralizer ({x * l} : Set G) = normIn T T₁ := by
  rw [← hc.sec3.cfg.inf_centralizer_eq_normIn d.hx d.hx1]
  ext t
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨htT, ht⟩
    exact ⟨htT, (mul_comm_mul_iff hc.hy.pair.wc.1 htT d.hl x).1 ht⟩
  · rintro ⟨htT, ht⟩
    exact ⟨htT, (mul_comm_mul_iff hc.hy.pair.wc.1 htT d.hl x).2 ht⟩

theorem Sec62Data.normIn_T₂ (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    normIn T T₂ = normIn T T₁ := by
  rw [← (d.sec3₂ hc).cfg.inf_centralizer_eq_normIn d.mem_normIn₂ d.y_ne_one, d.centralizer_eq hc]

theorem Sec62Data.card_L₂ (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    Nat.card (normIn T₂ T) = Nat.card (normIn T T₁) := by
  rw [(d.sec3₂ hc).card_normIn_swap, d.normIn_T₂ hc]

omit [Finite G] in
theorem Sec62Data.L₁_le_normalizer (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    normIn T₁ T ≤ Subgroup.normalizer (T₂ : Set G) := by
  intro u hu
  have hcomm : u * (x * l) = (x * l) * u :=
    elemAbelian_mul_comm hc.sec3.cfg.isElemAbelian_cfgM (Cfg.normIn_le_cfgM_right T T₁ hu)
      (d.y_mem_cfgM hc)
  obtain ⟨k, rfl⟩ := d.hT₂
  exact (hc.hy.pair.wc.conj k).centralizer_le_normalizer d.hyT₂ d.y_ne_one
    (Subgroup.mem_centralizer_singleton_iff.2 hcomm)

theorem Sec62Data.x_mem_cfgM₂ (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    x ∈ cfgM T T₂ := by
  have hl : l ∈ normIn T T₂ := by rw [d.normIn_T₂ hc]; exact d.l_mem hc
  have hll : l * l = 1 := elemAbelian_mul_self hc.hy.pair.wc.1 d.hl
  have e : x = (x * l) * l := by rw [mul_assoc, hll, mul_one]
  rw [e]
  exact (cfgM T T₂).mul_mem (Cfg.normIn_le_cfgM_right T T₂ d.mem_normIn₂)
    (Cfg.normIn_le_cfgM_left T T₂ hl)

theorem Sec62Data.L₂_le_normalizer (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) :
    normIn T₂ T ≤ Subgroup.normalizer (T₁ : Set G) := by
  intro z hz
  have hcomm : z * x = x * z :=
    elemAbelian_mul_comm (d.sec3₂ hc).cfg.isElemAbelian_cfgM (Cfg.normIn_le_cfgM_right T T₂ hz)
      (d.x_mem_cfgM₂ hc)
  exact hc.sec3.cfg.wc₁.centralizer_le_normalizer (normIn_le _ _ d.hx) d.hx1
    (Subgroup.mem_centralizer_singleton_iff.2 hcomm)

theorem Sec62Data.inf_T₁_T₂ (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂) (hne : T₂ ≠ T₁) :
    T₁ ⊓ T₂ = ⊥ := by
  obtain ⟨x₀, hx₀⟩ := hc.hy.pair.conj
  have hL : normIn T₁ T₂ ≠ ⊥ := fun hb =>
    d.hx1 (Subgroup.mem_bot.1 (hb ▸ mem_normIn.2 ⟨normIn_le _ _ d.hx,
      d.L₁_le_normalizer hc d.hx⟩))
  exact (cfg_of_conj_conj hc.hy.pair.wc ⟨x₀, hx₀⟩ d.hT₂ hne hL).inf

theorem Sec62Data.comm_L₁_L₂ (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂)
    (hne : T₂ ≠ T₁) : ∀ u ∈ normIn T₁ T, ∀ z ∈ normIn T₂ T, u * z = z * u := by
  intro u hu z hz
  have h1 := d.inf_T₁_T₂ hc hne
  have huT₂ : u * z * u⁻¹ ∈ T₂ :=
    conj_mem_of_mem_normalizer (d.L₁_le_normalizer hc hu) (normIn_le _ _ hz)
  have a2 : u * z * u⁻¹ * z⁻¹ ∈ T₂ := T₂.mul_mem huT₂ (T₂.inv_mem (normIn_le _ _ hz))
  have hzu : z * u⁻¹ * z⁻¹ ∈ T₁ :=
    conj_mem_of_mem_normalizer (d.L₂_le_normalizer hc hz) (T₁.inv_mem (normIn_le _ _ hu))
  have a1 : u * z * u⁻¹ * z⁻¹ ∈ T₁ := by
    have e : u * z * u⁻¹ * z⁻¹ = u * (z * u⁻¹ * z⁻¹) := by group
    rw [e]
    exact T₁.mul_mem (normIn_le _ _ hu) hzu
  have h3 : u * z * u⁻¹ * z⁻¹ ∈ T₁ ⊓ T₂ := ⟨a1, a2⟩
  rw [h1, Subgroup.mem_bot] at h3
  have h4 : u * z * u⁻¹ = z := mul_inv_eq_one.1 h3
  calc u * z = (u * z * u⁻¹) * u := by group
    _ = z * u := by rw [h4]

omit [Finite G] in
theorem isPGroup_barSub_sup_of_comm {L₁ L₂ : Subgroup G} (h₁ : IsPGroup 2 L₁)
    (h₂ : IsPGroup 2 L₂) (hcomm : ∀ u ∈ L₁, ∀ z ∈ L₂, u * z = z * u) :
    IsPGroup 2 ↥(barSub T L₁ ⊔ barSub T L₂) := by
  refine (isPGroup_barSub h₁).to_sup_of_normal_right' (isPGroup_barSub h₂) ?_
  intro a ha
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨u, huN, huL, rfl⟩ := exists_eq_barElt_of_mem_barSub ha
  obtain ⟨z, hzN, hzL, rfl⟩ := exists_eq_barElt_of_mem_barSub hb
  show barElt T hzN * barElt T huN = barElt T huN * barElt T hzN
  rw [barElt_mul, barElt_mul]
  exact congrArg QuotientGroup.mk (Subtype.ext (hcomm u huL z hzL).symm)

theorem Sec62Data.L₂_le_sup (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ n m)
    (d : Sec62Data T T₁ x l T₂) (hne : T₂ ≠ T₁) : normIn T₂ T ≤ T ⊔ normIn T₁ T := by
  have hcard := d.card_L₂ hc
  have hT₂ne := d.T₂_ne hc
  have hcomm := d.comm_L₁_L₂ hc hne
  have hL₁2 : IsPGroup 2 ↥(normIn T₁ T) :=
    (isPGroup_two_of_isElemAbelian hc.sec3.cfg.wc₁.1).to_le (normIn_le _ _)
  have hL₂2 : IsPGroup 2 ↥(normIn T₂ T) := by
    obtain ⟨k, rfl⟩ := d.hT₂
    exact (isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hc.hy.pair.wc.1 k)).to_le
      (normIn_le _ _)
  have hS₂ := isPGroup_barSub_sup_of_comm (T := T) hL₁2 hL₂2 hcomm
  obtain ⟨k, hk⟩ := d.hT₂
  subst hk
  exact sec58_le h1 hc.hy hc.hS hc.hI ⟨hT₂ne, hcard⟩ hS₂

theorem Sec62Data.L₂_le_cfgM (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ n m)
    (d : Sec62Data T T₁ x l T₂) (hne : T₂ ≠ T₁) : normIn T₂ T ≤ cfgM T T₁ := by
  intro z hz
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  have hzT₂ : z ∈ T₂ := normIn_le _ _ hz
  have hzz : z * z = 1 := by
    obtain ⟨k, rfl⟩ := d.hT₂
    exact elemAbelian_mul_self (isElemAbelian_conjSubgroup hc.hy.pair.wc.1 k) hzT₂
  have hz' : z ∈ normIn T₁ T ⊔ T := by
    rw [sup_comm]
    exact d.L₂_le_sup h1 hc hne hz
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T₁ T) T hL₁N
  have hz'' : z ∈ ((normIn T₁ T : Set G) * (T : Set G)) := by
    rw [← hmul]
    exact hz'
  obtain ⟨u, hu, t, ht, hzut⟩ := hz''
  have hzut : u * t = z := hzut
  by_cases hu1 : u = 1
  · subst hu1
    have hzT : z ∈ T := by rw [← hzut, one_mul]; exact ht
    have : z ∈ T ⊓ T₂ := ⟨hzT, hzT₂⟩
    rw [(d.sec3₂ hc).cfg.inf, Subgroup.mem_bot] at this
    rw [this]
    exact (cfgM T T₁).one_mem
  · have ht' : t ∈ normIn T T₁ :=
      mem_normIn_of_mul_mul_self hc hu hu1 ht (by rw [hzut]; exact hzz)
    rw [← hzut]
    exact (cfgM T T₁).mul_mem (Cfg.normIn_le_cfgM_right T T₁ hu)
      (Cfg.normIn_le_cfgM_left T T₁ ht')

theorem Sec62Data.cfgM_T₂_eq (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ n m)
    (d : Sec62Data T T₁ x l T₂) (hne : T₂ ≠ T₁) : cfgM T T₂ = cfgM T T₁ := by
  have hS₂ := d.sec3₂ hc
  have hle : cfgM T T₂ ≤ cfgM T T₁ := by
    refine sup_le ?_ (d.L₂_le_cfgM h1 hc hne)
    rw [d.normIn_T₂ hc]
    exact Cfg.normIn_le_cfgM_left T T₁
  have hcard : Nat.card (cfgM T T₁) ≤ Nat.card (cfgM T T₂) := by
    rw [hc.sec3.card_cfgM_eq_sq, hS₂.card_cfgM_eq_sq, d.normIn_T₂ hc]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem Sec62Data.T₂_le_normalizer (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ n m)
    (d : Sec62Data T T₁ x l T₂) (hne : T₂ ≠ T₁) :
    T₂ ≤ Subgroup.normalizer (cfgM T T₁ : Set G) := by
  rw [← d.cfgM_T₂_eq h1 hc hne]
  exact fun z hz => (d.sec3₂ hc).cfg.le_normalizer_cfgM (Subgroup.mem_sup_right hz)

end Data

end CFSG.CGT.Timmesfeld75
