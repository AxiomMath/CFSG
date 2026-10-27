module

public import CFSG.CGT.Timmesfeld75.Sec3Def
public import CFSG.CGT.Timmesfeld75.Config214

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

section Conjugation

theorem conjSubgroup_mono {g : G} {A B : Subgroup G} (h : A ≤ B) :
    conjSubgroup g A ≤ conjSubgroup g B :=
  Subgroup.map_mono h

private theorem conjSubgroup_sup_eq (g : G) (A B : Subgroup G) :
    conjSubgroup g (A ⊔ B) = conjSubgroup g A ⊔ conjSubgroup g B :=
  Subgroup.map_sup _ _ _

theorem conjSubgroup_inf (g : G) (A B : Subgroup G) :
    conjSubgroup g (A ⊓ B) = conjSubgroup g A ⊓ conjSubgroup g B :=
  Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem conjSubgroup_eq_bot_iff {g : G} {A : Subgroup G} : conjSubgroup g A = ⊥ ↔ A = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective

theorem conjSubgroup_conjSubgroup_eq (x y : G) (T : Subgroup G) :
    conjSubgroup y (conjSubgroup x T) = conjSubgroup x (conjSubgroup (x⁻¹ * y * x) T) := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
    show x * (x⁻¹ * y * x) = y * x by group]

theorem mem_conjSubgroup_sup {g y : G} {A B : Subgroup G} :
    y ∈ conjSubgroup g A ⊔ conjSubgroup g B ↔ g⁻¹ * y * g ∈ A ⊔ B := by
  rw [← conjSubgroup_sup_eq, mem_conjSubgroup]

theorem mem_normalizer_conjSubgroup_iff {x y : G} {U : Subgroup G} :
    y ∈ Subgroup.normalizer (conjSubgroup x U : Set G) ↔
      x⁻¹ * y * x ∈ Subgroup.normalizer (U : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, mem_normalizer_iff_conjSubgroup_eq,
    conjSubgroup_conjSubgroup, show y * x = x * (x⁻¹ * y * x) by group,
    ← conjSubgroup_conjSubgroup, conjSubgroup_inj]

theorem normIn_conj (x : G) (T U : Subgroup G) :
    normIn (conjSubgroup x T) (conjSubgroup x U) = conjSubgroup x (normIn T U) := by
  ext y
  rw [mem_normIn, mem_normalizer_conjSubgroup_iff, mem_conjSubgroup, mem_conjSubgroup, mem_normIn]

theorem cfgM_conj (x : G) (T T₁ : Subgroup G) :
    cfgM (conjSubgroup x T) (conjSubgroup x T₁) = conjSubgroup x (cfgM T T₁) := by
  rw [cfgM, cfgM, normIn_conj, normIn_conj, conjSubgroup_sup_eq]

theorem Cfg.conj_gen (c : Cfg T T₁) (x : G) : Cfg (conjSubgroup x T) (conjSubgroup x T₁) where
  wc := c.wc.conj x
  wc₁ := c.wc₁.conj x
  inf := by
    rw [← conjSubgroup_inf, c.inf]
    exact conjSubgroup_eq_bot_iff.2 rfl
  ne := by
    rw [normIn_conj]
    exact fun h => c.ne (conjSubgroup_eq_bot_iff.1 h)
  ne₁ := by
    rw [normIn_conj]
    exact fun h => c.ne₁ (conjSubgroup_eq_bot_iff.1 h)

theorem Sec3.conj_gen (h : Sec3 T T₁) (x : G) : Sec3 (conjSubgroup x T) (conjSubgroup x T₁) := by
  have hmem : ∀ z ∈ T ⊔ T₁, x * z * x⁻¹ ∈ conjSubgroup x T ⊔ conjSubgroup x T₁ := fun z hz => by
    rw [mem_conjSubgroup_sup]
    simpa [mul_assoc] using hz
  refine ⟨h.cfg.conj_gen x, ?_, ?_, ?_⟩
  · obtain ⟨z, hz, hz'⟩ := h.conj
    refine ⟨x * z * x⁻¹, hmem z hz, ?_⟩
    rw [conjSubgroup_conjSubgroup, show x * z * x⁻¹ * x = x * z by group,
      ← conjSubgroup_conjSubgroup, ← hz']
  · intro a ha haa haM
    have ha' : x⁻¹ * a * x ∈ T ⊔ T₁ := mem_conjSubgroup_sup.1 ha
    have haa' : (x⁻¹ * a * x) * (x⁻¹ * a * x) = 1 := by
      calc (x⁻¹ * a * x) * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
        _ = 1 := by rw [haa]; group
    have haM' : x⁻¹ * a * x ∉ cfgM T T₁ := fun hM => haM (by
      rw [cfgM_conj, mem_conjSubgroup]
      exact hM)
    obtain ⟨z, hz, hz'⟩ := h.invol _ ha' haa' haM'
    refine ⟨x * z * x⁻¹, hmem z hz, ?_⟩
    rw [conjSubgroup_conjSubgroup, show x * z * x⁻¹ * x = x * z by group,
      ← conjSubgroup_conjSubgroup, mem_conjSubgroup]
    exact hz'
  · intro y hy hne
    have hz : x⁻¹ * y * x ∈ T ⊔ T₁ := mem_conjSubgroup_sup.1 hy
    rw [conjSubgroup_conjSubgroup_eq] at hne ⊢
    have hne' : conjSubgroup (x⁻¹ * y * x) T ≠ T := fun h' => hne (by rw [h'])
    rw [normIn_conj, cfgM_conj]
    exact conjSubgroup_mono (h.trans _ hz hne')

end Conjugation

section CfgConj

theorem cfgM_le_normalizer (T T₁ : Subgroup G) :
    cfgM T T₁ ≤ Subgroup.normalizer (T : Set G) :=
  sup_le ((normIn_le T T₁).trans Subgroup.le_normalizer) inf_le_right

theorem cfgM_le_sup (T T₁ : Subgroup G) : cfgM T T₁ ≤ T ⊔ T₁ :=
  sup_le_sup (normIn_le T T₁) (normIn_le T₁ T)

theorem Cfg.left_ne_bot (c : Cfg T T₁) : T ≠ ⊥ := fun h =>
  c.ne (le_bot_iff.1 ((normIn_le T T₁).trans h.le))

theorem Cfg.left_ne_right (c : Cfg T T₁) : T ≠ T₁ := fun h => by
  have := c.inf
  rw [← h, inf_idem] at this
  exact c.left_ne_bot this

theorem Cfg.cfgM_le_normalizer_conj (c : Cfg T T₁) {x : G} (hx : x ∈ T ⊔ T₁) :
    cfgM T T₁ ≤ Subgroup.normalizer (conjSubgroup x T : Set G) := by
  intro m hm
  rw [mem_normalizer_conjSubgroup_iff]
  exact cfgM_le_normalizer T T₁ (by simpa using c.conj_mem_cfgM ((T ⊔ T₁).inv_mem hx) hm)

theorem Cfg.mem_cfgM_conj_iff (c : Cfg T T₁) {z a : G} (hz : z ∈ T ⊔ T₁) :
    z * a * z⁻¹ ∈ cfgM T T₁ ↔ a ∈ cfgM T T₁ := by
  refine ⟨fun h => ?_, c.conj_mem_cfgM hz⟩
  have := c.conj_mem_cfgM ((T ⊔ T₁).inv_mem hz) h
  simpa [mul_assoc] using this

theorem Cfg.inv_mul_mul_mem_cfgM_iff (c : Cfg T T₁) {x y : G} (hx : x ∈ T ⊔ T₁) :
    x⁻¹ * y * x ∈ cfgM T T₁ ↔ y ∈ cfgM T T₁ := by
  simpa using c.mem_cfgM_conj_iff ((T ⊔ T₁).inv_mem hx) (a := y)

theorem Cfg.conjSubgroup_normIn_le_cfgM (c : Cfg T T₁) {x : G} (hx : x ∈ T ⊔ T₁) :
    conjSubgroup x (normIn T T₁) ≤ cfgM T T₁ := by
  intro u hu
  rw [mem_conjSubgroup] at hu
  exact (c.inv_mul_mul_mem_cfgM_iff hx).1 (Cfg.normIn_le_cfgM_left T T₁ hu)

theorem Cfg.inf_cfgM_conj (c : Cfg T T₁) {x : G} (hx : x ∈ T ⊔ T₁) :
    conjSubgroup x T ⊓ cfgM T T₁ = conjSubgroup x (normIn T T₁) := by
  ext y
  rw [Subgroup.mem_inf, mem_conjSubgroup, mem_conjSubgroup, ← c.inf_cfgM, Subgroup.mem_inf,
    c.inv_mul_mul_mem_cfgM_iff hx]

theorem Cfg.cfgM_inf_centralizer_conj (c : Cfg T T₁) {x a : G} (hx : x ∈ T ⊔ T₁)
    (ha : a ∈ conjSubgroup x T) (haM : a ∉ cfgM T T₁) :
    cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G) = conjSubgroup x (normIn T T₁) := by
  have hs : x⁻¹ * a * x ∈ T := mem_conjSubgroup.1 ha
  have hsM : x⁻¹ * a * x ∉ cfgM T T₁ := fun h => haM ((c.inv_mul_mul_mem_cfgM_iff hx).1 h)
  have key := c.cfgM_inf_centralizer hs hsM
  ext y
  rw [mem_conjSubgroup, ← key, Subgroup.mem_inf, Subgroup.mem_inf, c.inv_mul_mul_mem_cfgM_iff hx,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · calc x⁻¹ * y * x * (x⁻¹ * a * x) = x⁻¹ * (y * a) * x := by group
      _ = x⁻¹ * (a * y) * x := by rw [h]
      _ = x⁻¹ * a * x * (x⁻¹ * y * x) := by group
  · exact mul_comm_of_conj_mul_comm (g := x) h

end CfgConj

section Sec3Conj

theorem Sec3.cfgM_le_normalizer_conj (hS : Sec3 T T₁) {x : G} (hx : x ∈ T ⊔ T₁) :
    cfgM T T₁ ≤ Subgroup.normalizer (conjSubgroup x T : Set G) :=
  hS.cfg.cfgM_le_normalizer_conj hx

theorem Sec3.mem_cfgM_conj_iff (hS : Sec3 T T₁) {z a : G} (hz : z ∈ T ⊔ T₁) :
    z * a * z⁻¹ ∈ cfgM T T₁ ↔ a ∈ cfgM T T₁ :=
  hS.cfg.mem_cfgM_conj_iff hz

theorem Sec3.inf_cfgM_conj (hS : Sec3 T T₁) {x : G} (hx : x ∈ T ⊔ T₁) :
    conjSubgroup x T ⊓ cfgM T T₁ = conjSubgroup x (normIn T T₁) :=
  hS.cfg.inf_cfgM_conj hx

theorem Sec3.cfgM_inf_centralizer_conj (hS : Sec3 T T₁) {x a : G} (hx : x ∈ T ⊔ T₁)
    (ha : a ∈ conjSubgroup x T) (haM : a ∉ cfgM T T₁) :
    cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G) = conjSubgroup x (normIn T T₁) :=
  hS.cfg.cfgM_inf_centralizer_conj hx ha haM

theorem Sec3.normIn_conj_eq (hS : Sec3 T T₁) {x y : G} (hx : x ∈ T ⊔ T₁) (hy : y ∈ T ⊔ T₁)
    (hxy : conjSubgroup x T ≠ conjSubgroup y T) :
    normIn (conjSubgroup x T) (conjSubgroup y T) = conjSubgroup x (normIn T T₁) := by
  rw [← hS.inf_cfgM_conj hx]
  apply le_antisymm
  · rintro u ⟨huT, huN⟩
    refine ⟨huT, ?_⟩
    have hu1 : y⁻¹ * u * y ∈ Subgroup.normalizer (T : Set G) :=
      mem_normalizer_conjSubgroup_iff.1 huN
    have hu2 : y⁻¹ * u * y ∈ conjSubgroup (y⁻¹ * x) T := by
      rw [mem_conjSubgroup]
      have := mem_conjSubgroup.1 huT
      convert this using 1
      group
    have hne : conjSubgroup (y⁻¹ * x) T ≠ T := fun h => hxy (by
      calc conjSubgroup x T = conjSubgroup (y * (y⁻¹ * x)) T := by rw [mul_inv_cancel_left]
        _ = conjSubgroup y (conjSubgroup (y⁻¹ * x) T) := (conjSubgroup_conjSubgroup _ _ _).symm
        _ = conjSubgroup y T := by rw [h])
    have hyx : y⁻¹ * x ∈ T ⊔ T₁ := (T ⊔ T₁).mul_mem ((T ⊔ T₁).inv_mem hy) hx
    have hM : y⁻¹ * u * y ∈ cfgM T T₁ := hS.trans _ hyx hne ⟨hu2, hu1⟩
    exact (hS.cfg.inv_mul_mul_mem_cfgM_iff hy).1 hM
  · rintro u ⟨huT, huM⟩
    exact ⟨huT, hS.cfgM_le_normalizer_conj hy huM⟩

theorem Sec3.cfg_conj (hS : Sec3 T T₁) {x y : G} (hx : x ∈ T ⊔ T₁) (hy : y ∈ T ⊔ T₁)
    (hxy : conjSubgroup x T ≠ conjSubgroup y T) :
    Cfg (conjSubgroup x T) (conjSubgroup y T) where
  wc := hS.cfg.wc.conj x
  wc₁ := hS.cfg.wc.conj y
  inf := by
    have hne : conjSubgroup (y * x⁻¹) (conjSubgroup x T) ≠ conjSubgroup x T := by
      rw [conjSubgroup_conjSubgroup, show y * x⁻¹ * x = y by group]
      exact fun h => hxy h.symm
    have := (hS.cfg.wc.conj x).inf_conj_eq_bot hne
    rwa [conjSubgroup_conjSubgroup, show y * x⁻¹ * x = y by group] at this
  ne := by
    rw [hS.normIn_conj_eq hx hy hxy]
    exact fun h => hS.cfg.ne (conjSubgroup_eq_bot_iff.1 h)
  ne₁ := by
    rw [hS.normIn_conj_eq hy hx hxy.symm]
    exact fun h => hS.cfg.ne (conjSubgroup_eq_bot_iff.1 h)

end Sec3Conj

section NotLeCfgM

variable [Finite G]

theorem Sec3.not_le_cfgM (hS : Sec3 T T₁) : ¬ T ≤ cfgM T T₁ := by
  intro hle
  obtain ⟨x, -, hx⟩ := hS.conj
  apply (hS.cfg.normIn_lt ⟨x, hx⟩).ne
  rw [← hS.cfg.inf_cfgM]
  exact inf_eq_left.2 hle

theorem Sec3.not_conj_le_cfgM (hS : Sec3 T T₁) {x : G} (hx : x ∈ T ⊔ T₁) :
    ¬ conjSubgroup x T ≤ cfgM T T₁ := by
  intro hle
  refine hS.not_le_cfgM fun t ht => ?_
  have h1 : x * t * x⁻¹ ∈ cfgM T T₁ := hle (by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using ht)
  exact (hS.mem_cfgM_conj_iff hx).1 h1

end NotLeCfgM

section ExistsConjNe

theorem Sec3.exists_conj_ne (hS : Sec3 T T₁) {x : G} (_hx : x ∈ T ⊔ T₁) :
    ∃ z ∈ T ⊔ T₁, conjSubgroup z T ≠ conjSubgroup x T := by
  by_cases h : conjSubgroup x T = T
  · obtain ⟨z, hz, hz'⟩ := hS.conj
    refine ⟨z, hz, ?_⟩
    rw [← hz', h]
    exact hS.cfg.left_ne_right.symm
  · refine ⟨1, (T ⊔ T₁).one_mem, ?_⟩
    rw [conjSubgroup_one]
    exact fun h' => h h'.symm

end ExistsConjNe

end CFSG.CGT.Timmesfeld75
