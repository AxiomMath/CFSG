module

public import CFSG.CGT.Timmesfeld75.WeaklyClosed
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

@[expose] def normIn (T U : Subgroup G) : Subgroup G := T ⊓ Subgroup.normalizer (U : Set G)

theorem mem_normIn {T U : Subgroup G} {x : G} :
    x ∈ normIn T U ↔ x ∈ T ∧ x ∈ Subgroup.normalizer (U : Set G) := Subgroup.mem_inf

theorem normIn_le (T U : Subgroup G) : normIn T U ≤ T := inf_le_left

@[expose] def cfgM (T T₁ : Subgroup G) : Subgroup G := normIn T T₁ ⊔ normIn T₁ T

structure Cfg (T T₁ : Subgroup G) : Prop where
  wc : IsWC T
  wc₁ : IsWC T₁
  inf : T ⊓ T₁ = ⊥
  ne : normIn T T₁ ≠ ⊥
  ne₁ : normIn T₁ T ≠ ⊥

section Basic

variable {T T₁ : Subgroup G}

theorem Cfg.symm (c : Cfg T T₁) : Cfg T₁ T :=
  ⟨c.wc₁, c.wc, by rw [inf_comm]; exact c.inf, c.ne₁, c.ne⟩

theorem elemAbelian_mul_self {T : Subgroup G} (hT : IsElemAbelian 2 T) {x : G} (hx : x ∈ T) :
    x * x = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hT hx

theorem elemAbelian_inv {T : Subgroup G} (hT : IsElemAbelian 2 T) {x : G} (hx : x ∈ T) :
    x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (elemAbelian_mul_self hT hx)

theorem Cfg.comm_L_L₁ (c : Cfg T T₁) {l x : G} (hl : l ∈ normIn T T₁) (hx : x ∈ normIn T₁ T) :
    l * x = x * l := by
  obtain ⟨hlT, hlN⟩ := mem_normIn.1 hl
  obtain ⟨hxT, hxN⟩ := mem_normIn.1 hx
  have h1 : l * x * l⁻¹ * x⁻¹ ∈ T₁ :=
    T₁.mul_mem (conj_mem_of_mem_normalizer hlN hxT) (T₁.inv_mem hxT)
  have h2 : l * x * l⁻¹ * x⁻¹ ∈ T := by
    have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
    rw [e]
    exact T.mul_mem hlT (conj_mem_of_mem_normalizer hxN (T.inv_mem hlT))
  have h3 : l * x * l⁻¹ * x⁻¹ ∈ T ⊓ T₁ := ⟨h2, h1⟩
  rw [c.inf, Subgroup.mem_bot] at h3
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem Cfg.normIn_le_normalizer (c : Cfg T T₁) :
    normIn T T₁ ≤ Subgroup.normalizer (normIn T₁ T : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ n ∈ normIn T₁ T, l * n * l⁻¹ = n := fun n hn => by
    rw [c.comm_L_L₁ hl hn]; group
  constructor
  · intro hx; rw [key x hx]; exact hx
  · intro hx
    have h2 := key _ hx
    have h3 : l * x * l⁻¹ = x := by
      have e : l * x * l⁻¹ = l⁻¹ * (l * (l * x * l⁻¹) * l⁻¹) * l := by group
      rw [e, h2]; group
    rw [h3] at hx
    exact hx

theorem Cfg.mem_cfgM_iff (c : Cfg T T₁) {m : G} :
    m ∈ cfgM T T₁ ↔ ∃ l ∈ normIn T T₁, ∃ x ∈ normIn T₁ T, m = l * x := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T T₁) (normIn T₁ T)
    c.normIn_le_normalizer
  constructor
  · intro hm
    have hm' : m ∈ ((normIn T T₁ : Set G) * (normIn T₁ T : Set G)) := by
      rw [← hmul]; exact hm
    obtain ⟨l, hl, x, hx, rfl⟩ := hm'
    exact ⟨l, hl, x, hx, rfl⟩
  · rintro ⟨l, hl, x, hx, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hx)

theorem Cfg.normIn_le_cfgM_left (T T₁ : Subgroup G) : normIn T T₁ ≤ cfgM T T₁ := le_sup_left

theorem Cfg.normIn_le_cfgM_right (T T₁ : Subgroup G) : normIn T₁ T ≤ cfgM T T₁ := le_sup_right

theorem Cfg.isElemAbelian_cfgM (c : Cfg T T₁) : IsElemAbelian 2 (cfgM T T₁) := by
  have hL : ∀ l ∈ normIn T T₁, l ∈ T := fun l hl => (mem_normIn.1 hl).1
  have hL₁ : ∀ x ∈ normIn T₁ T, x ∈ T₁ := fun x hx => (mem_normIn.1 hx).1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun m hm => ?_⟩
  · apply Subtype.ext
    obtain ⟨l, hl, x, hx, ha⟩ := c.mem_cfgM_iff.1 a.2
    obtain ⟨l', hl', x', hx', hb⟩ := c.mem_cfgM_iff.1 b.2
    change (a : G) * b = b * a
    rw [ha, hb]
    have e1 : l * l' = l' * l := elemAbelian_mul_comm c.wc.1 (hL l hl) (hL l' hl')
    have e2 : x * x' = x' * x := elemAbelian_mul_comm c.wc₁.1 (hL₁ x hx) (hL₁ x' hx')
    have e3 : x * l' = l' * x := (c.comm_L_L₁ hl' hx).symm
    have e4 : l * x' = x' * l := c.comm_L_L₁ hl hx'
    calc l * x * (l' * x') = l * (x * l') * x' := by simp only [mul_assoc]
      _ = l * (l' * x) * x' := by rw [e3]
      _ = (l * l') * (x * x') := by simp only [mul_assoc]
      _ = (l' * l) * (x' * x) := by rw [e1, e2]
      _ = l' * (l * x') * x := by simp only [mul_assoc]
      _ = l' * (x' * l) * x := by rw [e4]
      _ = l' * x' * (l * x) := by simp only [mul_assoc]
  · obtain ⟨l, hl, x, hx, rfl⟩ := c.mem_cfgM_iff.1 hm
    have e3 : x * l = l * x := (c.comm_L_L₁ hl hx).symm
    have hl2 := elemAbelian_mul_self c.wc.1 (hL l hl)
    have hx2 := elemAbelian_mul_self c.wc₁.1 (hL₁ x hx)
    calc (l * x) ^ 2 = l * x * (l * x) := pow_two _
      _ = l * (x * l) * x := by simp only [mul_assoc]
      _ = l * (l * x) * x := by rw [e3]
      _ = (l * l) * (x * x) := by simp only [mul_assoc]
      _ = 1 := by rw [hl2, hx2, mul_one]

theorem Cfg.inf_cfgM (c : Cfg T T₁) : T ⊓ cfgM T T₁ = normIn T T₁ := by
  apply le_antisymm
  · rintro m ⟨hmT, hmM⟩
    obtain ⟨l, hl, x, hx, rfl⟩ := c.mem_cfgM_iff.1 hmM
    have hlT : l ∈ T := (mem_normIn.1 hl).1
    have hxT₁ : x ∈ T₁ := (mem_normIn.1 hx).1
    have hxT : x ∈ T := by
      have := T.mul_mem (T.inv_mem hlT) hmT
      simpa using this
    have hx1 : x ∈ T ⊓ T₁ := ⟨hxT, hxT₁⟩
    rw [c.inf, Subgroup.mem_bot] at hx1
    subst hx1
    simpa using hl
  · exact le_inf (normIn_le _ _) (Cfg.normIn_le_cfgM_left T T₁)

theorem Cfg.inf_cfgM_right (c : Cfg T T₁) : T₁ ⊓ cfgM T T₁ = normIn T₁ T := by
  have := c.symm.inf_cfgM
  rwa [cfgM, sup_comm, ← cfgM] at this

theorem comm_commute_of_sq {x y : G} (hxi : x⁻¹ = x) (hyi : y⁻¹ = y)
    (hd2 : ⁅x, y⁆ * ⁅x, y⁆ = 1) :
    y * ⁅x, y⁆ = ⁅x, y⁆ * y ∧ x * ⁅x, y⁆ = ⁅x, y⁆ * x := by
  have hd : ⁅x, y⁆ = x * y * x * y := by rw [commutatorElement_def, hxi, hyi]
  have hdinv : ⁅x, y⁆⁻¹ = ⁅x, y⁆ := inv_eq_of_mul_eq_one_right hd2
  have hdinv' : ⁅x, y⁆⁻¹ = y * x * y * x := by
    rw [hd]; simp only [mul_inv_rev, hxi, hyi, mul_assoc]
  have key : y * x * y * x = x * y * x * y := by rw [← hdinv', hdinv, hd]
  constructor
  · calc y * ⁅x, y⁆ = y * (x * y * x * y) := by rw [hd]
      _ = (y * x * y * x) * y := by simp only [mul_assoc]
      _ = (x * y * x * y) * y := by rw [key]
      _ = ⁅x, y⁆ * y := by rw [hd]
  · calc x * ⁅x, y⁆ = x * (y * x * y * x) := by rw [key, ← hd]
      _ = (x * y * x * y) * x := by simp only [mul_assoc]
      _ = ⁅x, y⁆ * x := by rw [hd]

theorem Cfg.comm_mem_normIn (c : Cfg T T₁) {x y : G} (hx : x ∈ T) (hy : y ∈ normIn T₁ T) :
    ⁅x, y⁆ ∈ normIn T T₁ := by
  obtain ⟨hyT₁, hyN⟩ := mem_normIn.1 hy
  have hmemT : ⁅x, y⁆ ∈ T := by
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact T.mul_mem hx (conj_mem_of_mem_normalizer hyN (T.inv_mem hx))
  refine mem_normIn.2 ⟨hmemT, ?_⟩
  by_cases hy1 : y = 1
  · subst hy1
    simp [commutatorElement_def]
  · have hxi := elemAbelian_inv c.wc.1 hx
    have hyi := elemAbelian_inv c.wc₁.1 hyT₁
    have hd2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := elemAbelian_mul_self c.wc.1 hmemT
    have hdy := (comm_commute_of_sq hxi hyi hd2).1
    exact c.wc₁.centralizer_le_normalizer hyT₁ hy1
      (Subgroup.mem_centralizer_iff.2 fun k hk => by
        rw [Set.mem_singleton_iff] at hk; subst hk; exact hdy)

theorem Cfg.conj_mem_cfgM_of_mem_left (c : Cfg T T₁) {z m : G} (hz : z ∈ T)
    (hm : m ∈ cfgM T T₁) : z * m * z⁻¹ ∈ cfgM T T₁ := by
  obtain ⟨l, hl, y, hy, rfl⟩ := c.mem_cfgM_iff.1 hm
  have hlT : l ∈ T := (mem_normIn.1 hl).1
  have h1 : z * l * z⁻¹ = l := by
    rw [elemAbelian_mul_comm c.wc.1 hz hlT]; group
  have h2 : z * y * z⁻¹ = ⁅z, y⁆ * y := by rw [commutatorElement_def]; group
  have e : z * (l * y) * z⁻¹ = l * ⁅z, y⁆ * y := by
    calc z * (l * y) * z⁻¹ = (z * l * z⁻¹) * (z * y * z⁻¹) := by group
      _ = l * (⁅z, y⁆ * y) := by rw [h1, h2]
      _ = l * ⁅z, y⁆ * y := by simp only [mul_assoc]
  rw [e]
  exact (c.mem_cfgM_iff).2
    ⟨l * ⁅z, y⁆, (normIn T T₁).mul_mem hl (c.comm_mem_normIn hz hy), y, hy, rfl⟩

theorem cfgM_symm (T T₁ : Subgroup G) : cfgM T₁ T = cfgM T T₁ := sup_comm _ _

theorem Cfg.le_normalizer_cfgM (c : Cfg T T₁) :
    T ⊔ T₁ ≤ Subgroup.normalizer (cfgM T T₁ : Set G) := by
  have hT : T ≤ Subgroup.normalizer (cfgM T T₁ : Set G) := fun z hz => by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm; exact c.conj_mem_cfgM_of_mem_left hz hm
    · intro hm
      have h := c.conj_mem_cfgM_of_mem_left (T.inv_mem hz) hm
      have e : z⁻¹ * (z * m * z⁻¹) * z⁻¹⁻¹ = m := by group
      rwa [e] at h
  have hT₁ : T₁ ≤ Subgroup.normalizer (cfgM T T₁ : Set G) := fun z hz => by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm
      have := c.symm.conj_mem_cfgM_of_mem_left hz (by rwa [cfgM_symm])
      rwa [cfgM_symm] at this
    · intro hm
      have h := c.symm.conj_mem_cfgM_of_mem_left (T₁.inv_mem hz) (by rwa [cfgM_symm])
      rw [cfgM_symm] at h
      have e : z⁻¹ * (z * m * z⁻¹) * z⁻¹⁻¹ = m := by group
      rwa [e] at h
  exact sup_le hT hT₁

theorem Cfg.conj_mem_cfgM (c : Cfg T T₁) {z m : G} (hz : z ∈ T ⊔ T₁) (hm : m ∈ cfgM T T₁) :
    z * m * z⁻¹ ∈ cfgM T T₁ :=
  (Subgroup.mem_normalizer_iff.1 (c.le_normalizer_cfgM hz) m).1 hm

theorem Cfg.cfgM_inf_centralizer (c : Cfg T T₁) {x : G} (hx : x ∈ T) (hxM : x ∉ cfgM T T₁) :
    cfgM T T₁ ⊓ Subgroup.centralizer ({x} : Set G) = normIn T T₁ := by
  apply le_antisymm
  · rintro m ⟨hmM, hmC⟩
    obtain ⟨l, hl, y, hy, rfl⟩ := c.mem_cfgM_iff.1 hmM
    have hlT : l ∈ T := (mem_normIn.1 hl).1
    have hyT₁ : y ∈ T₁ := (mem_normIn.1 hy).1
    have hxm : x * (l * y) = (l * y) * x :=
      Subgroup.mem_centralizer_iff.1 hmC x (Set.mem_singleton x)
    have hxy : x * y = y * x := by
      have h1 : x * (l * y) = l * (x * y) := by
        rw [← mul_assoc, elemAbelian_mul_comm c.wc.1 hx hlT, mul_assoc]
      have h2 : (l * y) * x = l * (y * x) := by rw [mul_assoc]
      rw [h1, h2] at hxm
      exact mul_left_cancel hxm
    by_cases hy1 : y = 1
    · subst hy1; simpa using hl
    · exfalso
      have hxN : x ∈ Subgroup.normalizer (T₁ : Set G) :=
        c.wc₁.centralizer_le_normalizer hyT₁ hy1
          (Subgroup.mem_centralizer_iff.2 fun k hk => by
            rw [Set.mem_singleton_iff] at hk; subst hk; exact hxy.symm)
      exact hxM (Cfg.normIn_le_cfgM_left T T₁ (mem_normIn.2 ⟨hx, hxN⟩))
  · intro l hl
    refine ⟨Cfg.normIn_le_cfgM_left T T₁ hl, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    rw [Set.mem_singleton_iff] at hk; subst hk
    exact elemAbelian_mul_comm c.wc.1 hx (normIn_le _ _ hl)

theorem Cfg.strongly_closed_star (c : Cfg T T₁) {x t h : G} (hx : x ∈ T)
    (hxM : x ∉ cfgM T T₁) (hh : h ∈ T ⊔ T₁) (ht : t ∈ T) (htL : t ∉ normIn T T₁)
    (hcomm : ⁅h⁻¹ * t * h, x⁆ ∈ cfgM T T₁) : h⁻¹ * t * h ∈ T := by
  by_contra hyT
  set y := h⁻¹ * t * h with hy
  set T' := conjSubgroup h⁻¹ T with hT'
  have hwc' : IsWC T' := c.wc.conj h⁻¹
  have hyT' : y ∈ T' := by
    rw [hT', mem_conjSubgroup]
    simpa [hy, mul_assoc] using ht
  have hne : T' ≠ T := fun heq => hyT (heq ▸ hyT')
  have hinf : T ⊓ T' = ⊥ := c.wc.inf_conj_eq_bot hne
  have htM : t ∉ cfgM T T₁ := fun hM => htL (by
    have h1 : t ∈ T ⊓ cfgM T T₁ := ⟨ht, hM⟩
    rwa [c.inf_cfgM] at h1)
  have hCt := c.cfgM_inf_centralizer ht htM
  have hth : t = h * y * h⁻¹ := by simp [hy, mul_assoc]
  have hCy : ∀ m ∈ cfgM T T₁, y * m = m * y → m ∈ T' := by
    intro m hm hcm
    have hm' : h * m * h⁻¹ ∈ cfgM T T₁ := c.conj_mem_cfgM hh hm
    have hct : t * (h * m * h⁻¹) = (h * m * h⁻¹) * t := by
      rw [hth]
      calc h * y * h⁻¹ * (h * m * h⁻¹) = h * (y * m) * h⁻¹ := by group
        _ = h * (m * y) * h⁻¹ := by rw [hcm]
        _ = (h * m * h⁻¹) * (h * y * h⁻¹) := by group
    have hL : h * m * h⁻¹ ∈ normIn T T₁ := by
      rw [← hCt]
      refine ⟨hm', Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      rw [Set.mem_singleton_iff] at hk; subst hk; exact hct
    rw [hT', mem_conjSubgroup]
    simpa using normIn_le _ _ hL
  have hx2 := elemAbelian_mul_self c.wc.1 hx
  have hxi := elemAbelian_inv c.wc.1 hx
  have hyi := elemAbelian_inv hwc'.1 hyT'
  have hm₀2 : ⁅y, x⁆ * ⁅y, x⁆ = 1 := elemAbelian_mul_self c.isElemAbelian_cfgM hcomm
  obtain ⟨hxc, hyc⟩ := comm_commute_of_sq hyi hxi hm₀2
  have hm₀L : ⁅y, x⁆ ∈ normIn T T₁ := by
    rw [← c.cfgM_inf_centralizer hx hxM]
    refine ⟨hcomm, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    rw [Set.mem_singleton_iff] at hk; subst hk; exact hxc
  have hm₀1 : ⁅y, x⁆ = 1 := by
    have h1 : ⁅y, x⁆ ∈ T ⊓ T' := ⟨normIn_le _ _ hm₀L, hCy _ hcomm hyc⟩
    rwa [hinf, Subgroup.mem_bot] at h1
  have hyx : y * x = x * y := by
    rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hm₀1
    exact hm₀1
  have hx1 : x ≠ 1 := fun h1 => hxM (h1 ▸ (cfgM T T₁).one_mem)
  have hy1 : y ≠ 1 := fun h1 => htL (by
    have ht1 : t = 1 := by rw [hth, h1]; simp
    rw [ht1]; exact (normIn T T₁).one_mem)
  have hyN : y ∈ Subgroup.normalizer (T : Set G) :=
    c.wc.centralizer_le_normalizer hx hx1
      (Subgroup.mem_centralizer_iff.2 fun k hk => by
        rw [Set.mem_singleton_iff] at hk; subst hk; exact hyx.symm)
  obtain ⟨ℓ'', hℓ''⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.ne
  have hℓ''L : (ℓ'' : G) ∈ normIn T T₁ := ℓ''.2
  have hℓ''1 : (ℓ'' : G) ≠ 1 := fun h1 => hℓ'' (Subtype.ext h1)
  have hℓ'T' : h⁻¹ * (ℓ'' : G) * h ∈ T' := by
    rw [hT', mem_conjSubgroup]
    simpa [mul_assoc] using normIn_le _ _ hℓ''L
  have hℓ'M : h⁻¹ * (ℓ'' : G) * h ∈ cfgM T T₁ := by
    have := c.conj_mem_cfgM ((T ⊔ T₁).inv_mem hh) (Cfg.normIn_le_cfgM_left T T₁ hℓ''L)
    simpa using this
  have hℓ'1 : h⁻¹ * (ℓ'' : G) * h ≠ 1 := fun h1 => hℓ''1 (by
    have e : (ℓ'' : G) = h * (h⁻¹ * (ℓ'' : G) * h) * h⁻¹ := by group
    rw [e, h1]; simp)
  have hLnorm : ∀ ℓ ∈ normIn T T₁, ℓ ∈ Subgroup.normalizer (T' : Set G) := by
    intro ℓ hℓ
    have hcomm' : (h⁻¹ * (ℓ'' : G) * h) * ℓ = ℓ * (h⁻¹ * (ℓ'' : G) * h) :=
      elemAbelian_mul_comm c.isElemAbelian_cfgM hℓ'M (Cfg.normIn_le_cfgM_left T T₁ hℓ)
    exact hwc'.centralizer_le_normalizer hℓ'T' hℓ'1
      (Subgroup.mem_centralizer_iff.2 fun k hk => by
        rw [Set.mem_singleton_iff] at hk; subst hk; exact hcomm')
  have hyL : ∀ ℓ ∈ normIn T T₁, y * ℓ = ℓ * y := by
    intro ℓ hℓ
    have hℓT : ℓ ∈ T := normIn_le _ _ hℓ
    have h1 : ⁅y, ℓ⁆ ∈ T := by
      have e : ⁅y, ℓ⁆ = (y * ℓ * y⁻¹) * ℓ⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact T.mul_mem (conj_mem_of_mem_normalizer hyN hℓT) (T.inv_mem hℓT)
    have h2 : ⁅y, ℓ⁆ ∈ T' := by
      have e : ⁅y, ℓ⁆ = y * (ℓ * y⁻¹ * ℓ⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact T'.mul_mem hyT' (conj_mem_of_mem_normalizer (hLnorm ℓ hℓ) (T'.inv_mem hyT'))
    have h3 : ⁅y, ℓ⁆ ∈ T ⊓ T' := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at h3
    exact h3
  apply c.ne
  rw [eq_bot_iff]
  intro ℓ hℓ
  have h1 : ℓ ∈ T ⊓ T' :=
    ⟨normIn_le _ _ hℓ, hCy ℓ (Cfg.normIn_le_cfgM_left T T₁ hℓ) (hyL ℓ hℓ)⟩
  rwa [hinf] at h1

end Basic

end CFSG.CGT.Timmesfeld75
