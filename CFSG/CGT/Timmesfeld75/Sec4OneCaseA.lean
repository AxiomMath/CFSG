module

public import CFSG.CGT.Timmesfeld75.Sec4OneCommon

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section CaseA

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem Sec4Hyp.eq_one_of_comm (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) {l : G} (hl : l ∈ normIn T₁ T)
    (hla : a * l = l * a) : l = 1 := by
  by_contra hl1
  apply hA
  have haN₁ : a ∈ Subgroup.normalizer (T₁ : Set G) :=
    h.isWC₁.centralizer_le_normalizer (normIn_le _ _ hl) hl1
      (Subgroup.mem_centralizer_singleton_iff.2 hla)
  refine mem_normalizer_of_conjSubgroup_eq ?_
  rw [← normIn_conj, mem_normalizer_iff_conjSubgroup_eq.1 haN₁,
    mem_normalizer_iff_conjSubgroup_eq.1 h.mem_normalizer]

omit [Finite G] in
theorem Sec4Hyp.conj_le_sup (h : Sec4Hyp T T₁ a T₂) :
    conjSubgroup a (normIn T₁ T) ≤ normIn T₁ T ⊔ T := by
  refine conjSubgroup_le_of_forall_mem fun l hl => ?_
  have e : a * l * a⁻¹ = ⁅a, l⁆ * l := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (normIn T₁ T ⊔ T).mul_mem (Subgroup.mem_sup_right (h.hcomm l hl))
    (Subgroup.mem_sup_left hl)

omit [Finite G] in
theorem Sec4Hyp.commute_conj (h : Sec4Hyp T T₁ a T₂) :
    (∀ x ∈ conjSubgroup a (normIn T₁ T), ∀ y ∈ normIn T₁ T, x * y = y * x) ∧
      (∀ x ∈ conjSubgroup a (normIn T₁ T), ∀ y ∈ normIn T T₁, x * y = y * x) := by
  refine h.sec3.cfg.commute_conj_L₁ h.mem_normalizer ?_
  rw [inf_eq_left.2 h.conj_le_sup]
  exact fun h' => h.sec3.cfg.ne₁ (conjSubgroup_eq_bot_iff.1 h')

omit [Finite G] in
theorem Sec4Hyp.mul_conj_inv_mem (h : Sec4Hyp T T₁ a T₂) {l : G} (hl : l ∈ normIn T₁ T) :
    l * (a * l⁻¹ * a⁻¹) ∈ normIn T T₁ := by
  have hlN := (mem_normIn.1 hl).2
  have hlinv := (normIn T₁ T).inv_mem hl
  have hT : l * (a * l⁻¹ * a⁻¹) ∈ T := by
    have e : l * (a * l⁻¹ * a⁻¹) = l * ⁅a, l⁻¹⁆ * l⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_of_mem_normalizer hlN (h.hcomm _ hlinv)
  rw [← h.sec3.cfg.inf_centralizer_normIn]
  refine ⟨hT, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have hz : a * l⁻¹ * a⁻¹ ∈ conjSubgroup a (normIn T₁ T) := conj_mem_conjSubgroup a hlinv
  have h1 : l * y = y * l := elemAbelian_mul_comm h.isWC₁.1 (normIn_le _ _ hl) (normIn_le _ _ hy)
  have h2 := h.commute_conj.1 _ hz y hy
  generalize a * l⁻¹ * a⁻¹ = z at h2 ⊢
  calc y * (l * z) = (y * l) * z := (mul_assoc _ _ _).symm
    _ = (l * y) * z := by rw [h1]
    _ = l * (y * z) := mul_assoc _ _ _
    _ = l * (z * y) := by rw [h2]
    _ = (l * z) * y := (mul_assoc _ _ _).symm

theorem Sec4Hyp.exists_eq_comm_of_mem_normIn (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) {u : G} (hu : u ∈ normIn T T₁) :
    ∃ l ∈ normIn T₁ T, u = l * (a * l⁻¹ * a⁻¹) := by
  let f : normIn T₁ T → normIn T T₁ := fun l => ⟨l * (a * l⁻¹ * a⁻¹), h.mul_conj_inv_mem l.2⟩
  have hinj : Function.Injective f := by
    intro l l' hll
    have h1 : (l : G) * (a * (l : G)⁻¹ * a⁻¹) = l' * (a * (l' : G)⁻¹ * a⁻¹) :=
      congrArg Subtype.val hll
    have hm : (l' : G)⁻¹ * l ∈ normIn T₁ T :=
      (normIn T₁ T).mul_mem ((normIn T₁ T).inv_mem l'.2) l.2
    have hconj : (l' : G)⁻¹ * l = a * ((l' : G)⁻¹ * l) * a⁻¹ :=
      calc (l' : G)⁻¹ * l = (l' : G)⁻¹ * (l * (a * (l : G)⁻¹ * a⁻¹)) * (a * l * a⁻¹) := by group
        _ = (l' : G)⁻¹ * (l' * (a * (l' : G)⁻¹ * a⁻¹)) * (a * l * a⁻¹) := by rw [h1]
        _ = a * ((l' : G)⁻¹ * l) * a⁻¹ := by group
    have hcomm : a * ((l' : G)⁻¹ * l) = ((l' : G)⁻¹ * l) * a :=
      (eq_mul_inv_iff_mul_eq.1 hconj).symm
    exact Subtype.ext (inv_mul_eq_one.1 (h.eq_one_of_comm hA hm hcomm)).symm
  have hcard : Nat.card (normIn T T₁) ≤ Nat.card (normIn T₁ T) := by rw [h.card_normIn₁]
  obtain ⟨l, hl⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨u, hu⟩
  exact ⟨l, l.2, (congrArg Subtype.val hl).symm⟩

theorem Sec4Hyp.comm_normIn_of_not_normalizer (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) {u : G} (hu : u ∈ normIn T T₁) :
    a * u = u * a := by
  have haa := h.mul_self_eq_one
  obtain ⟨l, hl, rfl⟩ := h.exists_eq_comm_of_mem_normIn hA hu
  have h1 : a * (l * (a * l⁻¹ * a⁻¹)) * a⁻¹ = (l * (a * l⁻¹ * a⁻¹))⁻¹ :=
    calc a * (l * (a * l⁻¹ * a⁻¹)) * a⁻¹ = (a * l * a⁻¹) * (a * a) * l⁻¹ * (a * a)⁻¹ := by group
      _ = (l * (a * l⁻¹ * a⁻¹))⁻¹ := by rw [haa]; group
  rw [elemAbelian_inv h.pair.wc.1 (normIn_le _ _ hu)] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem Sec4Hyp.normIn_eq_of_not_normalizer (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) : normIn T T₂ = normIn T T₁ := by
  refine (Subgroup.eq_of_le_of_card_ge (fun u hu => ?_) h.card_normIn_le).symm
  rw [← h.inf_centralizer_eq]
  exact ⟨(mem_normIn.1 hu).1,
    Subgroup.mem_centralizer_singleton_iff.2 (h.comm_normIn_of_not_normalizer hA hu).symm⟩

theorem Sec4Hyp.inf_centralizer_eq_of_not_normalizer (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) :
    T ⊓ Subgroup.centralizer ({a} : Set G) = normIn T T₁ := by
  rw [h.inf_centralizer_eq, h.normIn_eq_of_not_normalizer hA]

omit [Finite G] in
theorem Sec4Hyp.conj_le_cfgM (h : Sec4Hyp T T₁ a T₂) :
    conjSubgroup a (normIn T₁ T) ≤ cfgM T T₁ := by
  refine conjSubgroup_le_of_forall_mem fun l hl => ?_
  have h1 := h.mul_conj_inv_mem ((normIn T₁ T).inv_mem hl)
  have e : a * l * a⁻¹ = l * (l⁻¹ * (a * l⁻¹⁻¹ * a⁻¹)) := by group
  rw [e]
  exact (cfgM T T₁).mul_mem (Cfg.normIn_le_cfgM_right T T₁ hl) (Cfg.normIn_le_cfgM_left T T₁ h1)

theorem Sec4Hyp.mem_normalizer_cfgM (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) :
    a ∈ Subgroup.normalizer (cfgM T T₁ : Set G) := by
  have hle : conjSubgroup a (cfgM T T₁) ≤ cfgM T T₁ := by
    change conjSubgroup a (normIn T T₁ ⊔ normIn T₁ T) ≤ _
    rw [conjSubgroup_sup_eq_sup]
    refine sup_le ?_ h.conj_le_cfgM
    refine conjSubgroup_le_of_forall_mem fun u hu => ?_
    rw [mul_inv_eq_iff_eq_mul.2 (h.comm_normIn_of_not_normalizer hA hu)]
    exact Cfg.normIn_le_cfgM_left T T₁ hu
  refine mem_normalizer_of_conjSubgroup_eq (le_antisymm hle ?_)
  rwa [conjSubgroup_le_iff, inv_eq_of_mul_eq_one_right h.mul_self_eq_one] at hle

theorem Sec4Hyp.cfgM_inf_centralizer_of_not_normalizer (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) :
    cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G) = normIn T T₁ := by
  apply le_antisymm
  · rintro m ⟨hm, hmC⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := h.sec3.cfg.mem_cfgM_iff.1 hm
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hmC
    have hau := h.comm_normIn_of_not_normalizer hA hu
    have hav : a * v = v * a := by
      have : u * (a * v) = u * (v * a) :=
        calc u * (a * v) = (a * u) * v := by rw [hau, mul_assoc]
          _ = a * (u * v) := mul_assoc _ _ _
          _ = (u * v) * a := hc.symm
          _ = u * (v * a) := mul_assoc _ _ _
      exact mul_left_cancel this
    rw [h.eq_one_of_comm hA hv hav, mul_one]
    exact hu
  · intro u hu
    exact ⟨Cfg.normIn_le_cfgM_left T T₁ hu,
      Subgroup.mem_centralizer_singleton_iff.2 (h.comm_normIn_of_not_normalizer hA hu).symm⟩

omit [Finite G] in
theorem Sec4Hyp.exists_ne_one_mem_normIn (h : Sec4Hyp T T₁ a T₂) :
    ∃ l ∈ normIn T₁ T, l ≠ 1 := by
  obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.sec3.cfg.ne₁
  exact ⟨l, hl, fun h' => hl1 (Subtype.ext h')⟩

omit [Finite G] in
theorem Sec4Hyp.conj_ne (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) : conjSubgroup a T₁ ≠ T₁ := fun h' =>
  hA (by
    refine mem_normalizer_of_conjSubgroup_eq ?_
    rw [← normIn_conj, h', mem_normalizer_iff_conjSubgroup_eq.1 h.mem_normalizer])

omit [Finite G] in
theorem Sec4Hyp.conj_conj (h : Sec4Hyp T T₁ a T₂) :
    ∃ g : G, conjSubgroup a T₁ = conjSubgroup g T := by
  obtain ⟨x, hx⟩ := h.pair.conj
  exact ⟨a * x, by rw [hx, conjSubgroup_conjSubgroup]⟩

omit [Finite G] in
theorem Sec4Hyp.normIn_le_normalizer_conj (h : Sec4Hyp T T₁ a T₂) :
    normIn T₁ T ≤ Subgroup.normalizer (conjSubgroup a T₁ : Set G) := by
  obtain ⟨l₀, hl₀, hl₀1⟩ := h.exists_ne_one_mem_normIn
  have hy : a * l₀ * a⁻¹ ∈ conjSubgroup a T₁ := conj_mem_conjSubgroup a (normIn_le _ _ hl₀)
  have hy1 : a * l₀ * a⁻¹ ≠ 1 := fun h' => hl₀1 (by
    have : l₀ = a⁻¹ * (a * l₀ * a⁻¹) * a := by group
    rw [this, h']
    group)
  intro l hl
  exact (h.isWC₁.conj a).centralizer_le_normalizer hy hy1 (Subgroup.mem_centralizer_singleton_iff.2
    ((h.commute_conj.1 _ (conj_mem_conjSubgroup a hl₀) l hl).symm))

omit [Finite G] in
theorem Sec4Hyp.conj_le_normalizer (h : Sec4Hyp T T₁ a T₂) :
    conjSubgroup a (normIn T₁ T) ≤ Subgroup.normalizer (T₁ : Set G) := by
  obtain ⟨l₀, hl₀, hl₀1⟩ := h.exists_ne_one_mem_normIn
  intro x hx
  exact h.isWC₁.centralizer_le_normalizer (normIn_le _ _ hl₀) hl₀1
    (Subgroup.mem_centralizer_singleton_iff.2 (h.commute_conj.1 x hx l₀ hl₀))

theorem Sec4Hyp.normIn_conj_eq (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) :
    normIn T₁ (conjSubgroup a T₁) = normIn T₁ T := by
  have hle : normIn T₁ T ≤ normIn T₁ (conjSubgroup a T₁) := fun l hl =>
    mem_normIn.2 ⟨(mem_normIn.1 hl).1, h.normIn_le_normalizer_conj hl⟩
  have hcard : Nat.card (normIn T₁ (conjSubgroup a T₁)) ≤ Nat.card (normIn T₁ T) := by
    rw [h.card_normIn₁]
    exact h.pair.card_normIn_le h.pair.conj h.conj_conj (h.conj_ne hA)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem Sec4Hyp.cfg₁a (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) : Cfg T₁ (conjSubgroup a T₁) :=
  cfg_of_conj_conj h.pair.wc h.pair.conj h.conj_conj (h.conj_ne hA) (by
    rw [h.normIn_conj_eq hA]
    exact h.sec3.cfg.ne₁)

theorem Sec4Hyp.normIn_conj_left_eq (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) :
    normIn (conjSubgroup a T₁) T₁ = conjSubgroup a (normIn T₁ T) := by
  have hle : conjSubgroup a (normIn T₁ T) ≤ normIn (conjSubgroup a T₁) T₁ := fun x hx =>
    mem_normIn.2 ⟨conjSubgroup_mono (normIn_le T₁ T) hx, h.conj_le_normalizer hx⟩
  have hcard : Nat.card (normIn (conjSubgroup a T₁) T₁) ≤ Nat.card (conjSubgroup a (normIn T₁ T)) :=
    le_of_eq (by
      rw [card_conjSubgroup, ← (h.cfg₁a hA).card_normIn_eq ⟨a, rfl⟩, h.normIn_conj_eq hA])
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem Sec4Hyp.cfgM_conj_eq (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) :
    cfgM T₁ (conjSubgroup a T₁) = cfgM T T₁ := by
  have hle : cfgM T₁ (conjSubgroup a T₁) ≤ cfgM T T₁ := by
    rw [cfgM, h.normIn_conj_eq hA, h.normIn_conj_left_eq hA]
    exact sup_le (Cfg.normIn_le_cfgM_right T T₁) h.conj_le_cfgM
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h.sec3.cfg.card_cfgM, (h.cfg₁a hA).card_cfgM, h.normIn_conj_eq hA,
    h.normIn_conj_left_eq hA, card_conjSubgroup, h.card_normIn₁]

end CaseA

end CFSG.CGT.Timmesfeld75
