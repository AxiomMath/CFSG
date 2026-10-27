module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIJBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Fam

variable {G : Type} [Group G] {T T₁ T₂ T₃ : Subgroup G}

@[expose] def sec4Fam (T T₁ T₂ T₃ : Subgroup G) : Fin 4 → Subgroup G := ![T, T₁, T₂, T₃]

theorem mem_iInf_normIn_sec4Fam {A : Subgroup G} {u : G} :
    u ∈ (⨅ i, normIn A (sec4Fam T T₁ T₂ T₃ i)) ↔ u ∈ A ∧ u ∈ Subgroup.normalizer (T : Set G) ∧
      u ∈ Subgroup.normalizer (T₁ : Set G) ∧ u ∈ Subgroup.normalizer (T₂ : Set G) ∧
      u ∈ Subgroup.normalizer (T₃ : Set G) := by
  rw [Subgroup.mem_iInf]
  constructor
  · intro h
    exact ⟨(mem_normIn.1 (h 0)).1, (mem_normIn.1 (h 0)).2, (mem_normIn.1 (h 1)).2,
      (mem_normIn.1 (h 2)).2, (mem_normIn.1 (h 3)).2⟩
  · rintro ⟨hA, h0, h1, h2, h3⟩ i
    refine mem_normIn.2 ⟨hA, ?_⟩
    fin_cases i
    exacts [h0, h1, h2, h3]

end Fam

section Ext

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ T₃ : Subgroup G} {a x : G}

structure Sec4Ext (T T₁ T₂ : Subgroup G) (a x : G) (T₃ : Subgroup G) : Prop where
  hyp : Sec4Hyp T T₁ a T₂
  conj : ∃ g : G, T₃ = conjSubgroup g T
  mem : x ∈ T₃
  ne_one : x ≠ 1
  normT : x ∈ Subgroup.normalizer (T : Set G)
  acts : Sec4ActsTriv T T₁ T₂ x
  notle : ¬ T₃ ≤ sec4Y T T₁ T₂

omit [Finite G] in
theorem Sec4Ext.isWC₃ (e : Sec4Ext T T₁ T₂ a x T₃) : IsWC T₃ := by
  obtain ⟨g, hg⟩ := e.conj
  exact hg ▸ e.hyp.pair.wc.conj g

omit [Finite G] in
theorem Sec4Ext.mul_self_eq_one (e : Sec4Ext T T₁ T₂ a x T₃) : x * x = 1 :=
  elemAbelian_mul_self e.isWC₃.1 e.mem

theorem Sec4Ext.normT₁ (e : Sec4Ext T T₁ T₂ a x T₃) : x ∈ Subgroup.normalizer (T₁ : Set G) :=
  e.acts.mem_normalizer_of_le e.hyp e.hyp.isWC₁ mid_le_sec4Y

theorem Sec4Ext.normT₂ (e : Sec4Ext T T₁ T₂ a x T₃) : x ∈ Subgroup.normalizer (T₂ : Set G) :=
  e.acts.mem_normalizer_of_le e.hyp e.hyp.isWC₂ right_le_sec4Y

omit [Finite G] in
theorem Sec4Ext.normalizer_of_comm (e : Sec4Ext T T₁ T₂ a x T₃) {u : G} (hu : x * u = u * x) :
    u ∈ Subgroup.normalizer (T₃ : Set G) :=
  e.isWC₃.centralizer_le_normalizer e.mem e.ne_one
    (Subgroup.mem_centralizer_singleton_iff.2 hu.symm)

theorem Sec4Ext.sec4N_le_normalizer₂ (e : Sec4Ext T T₁ T₂ a x T₃) :
    sec4N T T₁ T₂ ≤ Subgroup.normalizer (T₂ : Set G) := by
  obtain ⟨y, hy, hy2⟩ := e.hyp.exists_mem_sec4Y_conj₂
  have hle := e.hyp.sec4N_le_normalizer_conj (e.hyp.sec4Y_le_normalizer hy)
  rwa [← hy2] at hle

theorem Sec4Ext.exists_L (e : Sec4Ext T T₁ T₂ a x T₃) :
    ∃ u ∈ normIn T T₁, u ≠ 1 ∧ x * u = u * x :=
  exists_ne_one_mem_centralizer_of_involution
    (isElemAbelian_of_le e.hyp.pair.wc.1 (normIn_le _ _)) e.hyp.sec3.cfg.ne e.mul_self_eq_one
    fun _ hv => (conjSubgroup_normIn_eq_of_mem_normalizer e.normT e.normT₁) ▸
      conj_mem_conjSubgroup x hv

theorem Sec4Ext.exists_L₁ (e : Sec4Ext T T₁ T₂ a x T₃) :
    ∃ u ∈ normIn T₁ T, u ≠ 1 ∧ x * u = u * x :=
  exists_ne_one_mem_centralizer_of_involution
    (isElemAbelian_of_le e.hyp.isWC₁.1 (normIn_le _ _)) e.hyp.sec3.cfg.ne₁ e.mul_self_eq_one
    fun _ hv => (conjSubgroup_normIn_eq_of_mem_normalizer e.normT₁ e.normT) ▸
      conj_mem_conjSubgroup x hv

theorem Sec4Ext.exists_L₂ (e : Sec4Ext T T₁ T₂ a x T₃) :
    ∃ u ∈ normIn T₂ T, u ≠ 1 ∧ x * u = u * x :=
  exists_ne_one_mem_centralizer_of_involution
    (isElemAbelian_of_le e.hyp.isWC₂.1 (normIn_le _ _)) e.hyp.normIn₂_ne_bot e.mul_self_eq_one
    fun _ hv => (conjSubgroup_normIn_eq_of_mem_normalizer e.normT₂ e.normT) ▸
      conj_mem_conjSubgroup x hv

theorem Sec4Ext.fam_ne_bot (e : Sec4Ext T T₁ T₂ a x T₃) (j : Fin 4) :
    (⨅ i, normIn (sec4Fam T T₁ T₂ T₃ j) (sec4Fam T T₁ T₂ T₃ i)) ≠ ⊥ := by
  refine Subgroup.ne_bot_iff_exists_ne_one.2 ?_
  fin_cases j
  · obtain ⟨u, hu, hu1, hxu⟩ := e.exists_L
    refine ⟨⟨u, mem_iInf_normIn_sec4Fam.2 ⟨normIn_le _ _ hu,
      Subgroup.le_normalizer (normIn_le _ _ hu), (mem_normIn.1 hu).2,
      e.sec4N_le_normalizer₂ (normIn_le_sec4N_left hu), e.normalizer_of_comm hxu⟩⟩,
      fun h => hu1 (congrArg Subtype.val h)⟩
  · obtain ⟨u, hu, hu1, hxu⟩ := e.exists_L₁
    refine ⟨⟨u, mem_iInf_normIn_sec4Fam.2 ⟨normIn_le _ _ hu, (mem_normIn.1 hu).2,
      Subgroup.le_normalizer (normIn_le _ _ hu),
      e.sec4N_le_normalizer₂ (normIn_le_sec4N_mid hu), e.normalizer_of_comm hxu⟩⟩,
      fun h => hu1 (congrArg Subtype.val h)⟩
  · obtain ⟨u, hu, hu1, hxu⟩ := e.exists_L₂
    refine ⟨⟨u, mem_iInf_normIn_sec4Fam.2 ⟨normIn_le _ _ hu, (mem_normIn.1 hu).2,
      e.hyp.sec4N_le_normalizer_mid (normIn_le_sec4N_right hu),
      Subgroup.le_normalizer (normIn_le _ _ hu), e.normalizer_of_comm hxu⟩⟩,
      fun h => hu1 (congrArg Subtype.val h)⟩
  · exact ⟨⟨x, mem_iInf_normIn_sec4Fam.2 ⟨e.mem, e.normT, e.normT₁, e.normT₂,
      Subgroup.le_normalizer e.mem⟩⟩, fun h => e.ne_one (congrArg Subtype.val h)⟩

omit [Finite G] in
theorem Sec4Ext.fam_injective (e : Sec4Ext T T₁ T₂ a x T₃) :
    Function.Injective (sec4Fam T T₁ T₂ T₃) := by
  have h01 : T ≠ T₁ := fun h' => e.hyp.pair.ne h'.symm
  have h02 : T ≠ T₂ := fun h' => e.hyp.ne_left h'.symm
  have h03 : T ≠ T₃ := fun h' => e.notle (h' ▸ left_le_sec4Y)
  have h12 : T₁ ≠ T₂ := fun h' => e.hyp.ne_right h'.symm
  have h13 : T₁ ≠ T₃ := fun h' => e.notle (h' ▸ mid_le_sec4Y)
  have h23 : T₂ ≠ T₃ := fun h' => e.notle (h' ▸ right_le_sec4Y)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [sec4Fam, h01.symm, h02.symm, h03.symm, h12.symm,
    h13.symm, h23.symm]

omit [Finite G] in
theorem Sec4Ext.ne_left (e : Sec4Ext T T₁ T₂ a x T₃) : T₃ ≠ T := fun h' =>
  e.notle (h' ▸ left_le_sec4Y)

theorem Sec4Ext.sec3₃ (e : Sec4Ext T T₁ T₂ a x T₃) : Sec3 T T₃ := by
  obtain ⟨u, hu, hu1, hxu⟩ := e.exists_L
  obtain ⟨g, hg⟩ := e.conj
  refine sec3_of_conj_conj e.hyp.glob ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, hg⟩ e.ne_left ?_
  refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨u, mem_normIn.2 ⟨normIn_le _ _ hu,
    e.normalizer_of_comm hxu⟩⟩, fun h => hu1 (congrArg Subtype.val h)⟩

theorem Sec4Ext.exists_conj₃ (e : Sec4Ext T T₁ T₂ a x T₃) :
    ∃ y ∈ T ⊔ T₃, T₃ = conjSubgroup y T := e.sec3₃.conj

end Ext

end CFSG.CGT.Timmesfeld75
