module

public import CFSG.CGT.Timmesfeld75.Sec63Count

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Bar

variable {G : Type} [Group G] {T U U' : Subgroup G}

theorem barSub_mono (h : U ≤ U') : barSub T U ≤ barSub T U' := fun y hy => by
  obtain ⟨u, hu, huU, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
  exact barElt_mem_barSub hu (h huU)

end Bar

section Fixed

variable {G : Type} [Group G] {T T₁ T₃ : Subgroup G} {n m : ℕ} {x : G}

theorem Sec63Cfg.exists_fixed_bar (h48 : Sec48) (c : Sec63Cfg T T₁ n m x T₃)
    (hW : IsPGroup 2 ↥(normIn T₃ T ⊔ normIn T₁ T)) :
    ∃ y ∈ normIn T₁ T, y ≠ 1 ∧ ∀ a ∈ normIn T₃ T, ⁅a, y⁆ ∈ T := by
  have := c.ctx.finite
  have hP := c.ctx.hy.pair
  have hS3 := c.ctx.sec3
  obtain ⟨x₀, hx₀⟩ := hP.conj
  obtain ⟨g, hg⟩ := c.conj
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := inf_le_right
  have hA'N : normIn T₃ T ≤ Subgroup.normalizer (T : Set G) := inf_le_right
  have hL₁T : normIn T₁ T ⊓ T = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc normIn T₁ T ⊓ T ≤ T ⊓ T₁ := le_inf inf_le_right (inf_le_left.trans (normIn_le T₁ T))
      _ = ⊥ := hS3.cfg.inf
  have hT₁ab : IsElemAbelian 2 T₁ := hx₀ ▸ isElemAbelian_conjSubgroup hP.wc.1 x₀
  have hT₃ab : IsElemAbelian 2 T₃ := hg ▸ isElemAbelian_conjSubgroup hP.wc.1 g
  have hVab : IsElemAbelian 2 (barSub T (normIn T₁ T)) :=
    isElemAbelian_barSub (isElemAbelian_subgroup_of_le hT₁ab (normIn_le _ _))
  have hL₁2 : IsPGroup 2 (normIn T₁ T) :=
    (isPGroup_two_of_isElemAbelian hT₁ab).to_le (normIn_le _ _)
  have hA'2 : IsPGroup 2 (normIn T₃ T) :=
    (isPGroup_two_of_isElemAbelian hT₃ab).to_le (normIn_le _ _)
  have hWC : IsWC (barSub T (normIn T₁ T)) := h48 G T T₁ c.ctx.hy c.ctx.hS c.ctx.hI
  have hU : IsPGroup 2 ↥(barSub T (normIn T₃ T) ⊔ barSub T (normIn T₁ T)) :=
    (isPGroup_barSub hW).to_le (sup_le (barSub_mono le_sup_left) (barSub_mono le_sup_right))
  have hnorm : ∀ (a : G) (haN : a ∈ Subgroup.normalizer (T : Set G)), a ∈ normIn T₃ T →
      ∀ t ∈ barSub T (normIn T₁ T),
        barElt T haN * t * (barElt T haN)⁻¹ ∈ barSub T (normIn T₁ T) := by
    intro a haN ha t ht
    have haU : barElt T haN ∈ barSub T (normIn T₃ T) ⊔ barSub T (normIn T₁ T) :=
      Subgroup.mem_sup_left (barElt_mem_barSub haN ha)
    have hle : conjSubgroup (barElt T haN) (barSub T (normIn T₁ T)) ≤
        barSub T (normIn T₃ T) ⊔ barSub T (normIn T₁ T) := by
      intro w hw
      have hw' := mem_conjSubgroup.1 hw
      have e : w = barElt T haN * ((barElt T haN)⁻¹ * w * barElt T haN) * (barElt T haN)⁻¹ := by
        group
      rw [e]
      exact (barSub T (normIn T₃ T) ⊔ barSub T (normIn T₁ T)).mul_mem
        ((barSub T (normIn T₃ T) ⊔ barSub T (normIn T₁ T)).mul_mem haU
          (Subgroup.mem_sup_right hw'))
        ((barSub T (normIn T₃ T) ⊔ barSub T (normIn T₁ T)).inv_mem haU)
    have heq := eq_of_conj_le_pGroup hWC hU le_sup_right hle
    have := conj_mem_conjSubgroup (barElt T haN) ht
    rwa [heq] at this
  have hLne : barSub T (normIn T₁ T) ≠ ⊥ := by
    intro hbot
    have h1 := card_barSub hL₁N hL₁T
    rw [hbot, Subgroup.card_bot] at h1
    exact hS3.cfg.ne₁ (Subgroup.card_eq_one.1 h1.symm)
  obtain ⟨h, hhL, hh1, hhfix⟩ := exists_fixed_mod_of_pGroup (T := barSub T (normIn T₁ T))
    (A := barSub T (normIn T₃ T)) (C := ⊥) (isPGroup_barSub hL₁2)
    (fun u hu v hv => elemAbelian_mul_comm hVab hu hv) (isPGroup_barSub hA'2)
    (fun a ha t ht => by
      obtain ⟨a', haN, ha'A, rfl⟩ := exists_eq_barElt_of_mem_barSub ha
      exact hnorm a' haN ha'A t ht) bot_le (Ne.symm hLne)
    (fun a _ cc hc => by rw [Subgroup.mem_bot.1 hc]; simp)
  obtain ⟨y, hyN, hyL, rfl⟩ := exists_eq_barElt_of_mem_barSub hhL
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hh1 (Subgroup.mem_bot.2 barElt_one)
  refine ⟨y, hyL, hy1, fun a ha => ?_⟩
  have haN : a ∈ Subgroup.normalizer (T : Set G) := hA'N ha
  have hcomm := hhfix _ (barElt_mem_barSub haN ha)
  rw [Subgroup.mem_bot] at hcomm
  exact commutator_mem_of_bar_comm haN hyN (commutatorElement_eq_one_iff_mul_comm.1 hcomm)

theorem Sec63Cfg.exists_conj_of_fixed (h62 : Sec62) (c : Sec63Cfg T T₁ n m x T₃) {y : G}
    (hy : y ∈ normIn T₁ T) (hy1 : y ≠ 1) {a : G} (hc : ⁅a, y⁆ ∈ T) :
    ∃ s ∈ T, a * y * a⁻¹ = s⁻¹ * y * s := by
  have := c.ctx.finite
  have hP := c.ctx.hy.pair
  have hS3 := c.ctx.sec3
  obtain ⟨hyT₁, hyN⟩ := mem_normIn.1 hy
  obtain ⟨k, hk⟩ := hP.conj
  have hyk : y ∈ conjSubgroup k T := hk ▸ hyT₁
  have hyD : y ∈ normD T := mem_normD_of_mem_conjSubgroup hyk hy1 hyN
  have hyT : y ∉ T := by
    intro hyT
    have : y ∈ T ⊓ T₁ := ⟨hyT, hyT₁⟩
    rw [hS3.cfg.inf, Subgroup.mem_bot] at this
    exact hy1 this
  have hcard : Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) = Nat.card ↥(normIn T T₁) := by
    rw [hS3.cfg.inf_centralizer_eq_normIn hy hy1]
  have hD : a * y * a⁻¹ ∈ classD T := by
    have := classD_conj hyD.1 a⁻¹
    rwa [inv_inv] at this
  have ht : y⁻¹ * (a * y * a⁻¹) ∈ T := by
    have h1 := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hyN) hc
    have e : y⁻¹ * (a * y * a⁻¹) = y⁻¹ * ⁅a, y⁆ * y⁻¹⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact h1
  exact h62 G T T₁ n m c.ctx y hyD hyT hcard (a * y * a⁻¹) hD _ ht (by group)

theorem Sec63Cfg.exists_comm_pair (h48 : Sec48) (h62 : Sec62) (c : Sec63Cfg T T₁ n m x T₃)
    (hW : IsPGroup 2 ↥(normIn T₃ T ⊔ normIn T₁ T)) :
    ∃ y ∈ normIn T₁ T, ∃ a ∈ normIn T₃ T, y ≠ 1 ∧ a ≠ 1 ∧ a * y = y * a := by
  obtain ⟨y, hy, hy1, hfix⟩ := c.exists_fixed_bar h48 hW
  obtain ⟨a, ha, ha1, hcomm⟩ := c.exists_comm hy hy1 fun a ha =>
    c.exists_conj_of_fixed h62 hy hy1 (hfix a ha)
  exact ⟨y, hy, a, ha, hy1, ha1, hcomm⟩

theorem Sec63Cfg.nonempty_F (h48 : Sec48) (h62 : Sec62) (c : Sec63Cfg T T₁ n m x T₃)
    (hW : IsPGroup 2 ↥(normIn T₃ T ⊔ normIn T₁ T)) :
    ∀ j : Fin 3, (⨅ i, normIn (sec63Fam T T₁ T₃ j) (sec63Fam T T₁ T₃ i)) ≠ ⊥ := by
  obtain ⟨y, hy, a, ha, hy1, ha1, hcomm⟩ := c.exists_comm_pair h48 h62 hW
  have hP := c.ctx.hy.pair
  obtain ⟨x₀, hx₀⟩ := hP.conj
  obtain ⟨g, hg⟩ := c.conj
  have hyT₁ : y ∈ T₁ := (mem_normIn.1 hy).1
  have haT₃ : a ∈ T₃ := (mem_normIn.1 ha).1
  have hwc₁ : IsWC T₁ := hx₀ ▸ hP.wc.conj x₀
  have hwc₃ : IsWC T₃ := hg ▸ hP.wc.conj g
  have hyN₃ : y ∈ Subgroup.normalizer (T₃ : Set G) :=
    hwc₃.centralizer_le_normalizer haT₃ ha1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  have haN₁ : a ∈ Subgroup.normalizer (T₁ : Set G) :=
    hwc₁.centralizer_le_normalizer hyT₁ hy1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
  intro j
  fin_cases j
  · obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.inf_ne_bot
    have hwT : w ∈ T := (mem_normIn.1 hw.1).1
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨w, Subgroup.mem_iInf.2 fun i => ?_⟩,
      fun h => hw1 (Subtype.ext (show w = 1 from congrArg Subtype.val h))⟩
    fin_cases i
    · exact mem_normIn.2 ⟨hwT, Subgroup.le_normalizer hwT⟩
    · exact hw.1
    · exact hw.2
  · refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨y, Subgroup.mem_iInf.2 fun i => ?_⟩,
      fun h => hy1 (congrArg Subtype.val h)⟩
    fin_cases i
    · exact hy
    · exact mem_normIn.2 ⟨hyT₁, Subgroup.le_normalizer hyT₁⟩
    · exact mem_normIn.2 ⟨hyT₁, hyN₃⟩
  · refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨a, Subgroup.mem_iInf.2 fun i => ?_⟩,
      fun h => ha1 (congrArg Subtype.val h)⟩
    fin_cases i
    · exact ha
    · exact mem_normIn.2 ⟨haT₃, haN₁⟩
    · exact mem_normIn.2 ⟨haT₃, Subgroup.le_normalizer haT₃⟩

end Fixed

end CFSG.CGT.Timmesfeld75
