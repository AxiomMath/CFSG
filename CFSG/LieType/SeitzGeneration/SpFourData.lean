module

public import CFSG.LieType.SeitzGeneration.SpFourFix

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

theorem eq_one_of_spEnd_fix {g : StatedSp r K} (h : ∀ v, spEnd g v = v) : g = 1 := by
  have : spEnd g = spEnd 1 := LinearMap.ext fun v => by rw [spEnd_one_apply]; exact h v
  exact spLin_injective (Units.ext this)

theorem linearIndependent_pair_of_spForm {w w' : Fin r ⊕ Fin r → K}
    (h : spForm r K w w' ≠ 0) : LinearIndependent K ![w, w'] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h2 : spForm r K w (s • w + t • w') = 0 := by rw [hst, map_zero]
  rw [map_add, map_smul, map_smul, spForm_isAlt w, smul_eq_mul, smul_eq_mul, mul_zero,
    zero_add] at h2
  have ht : t = 0 := (mul_eq_zero.mp h2).resolve_right h
  refine ⟨?_, ht⟩
  rw [ht, zero_smul, add_zero] at hst
  refine (smul_eq_zero.mp hst).resolve_right fun hw => h ?_
  rw [hw, map_zero, LinearMap.zero_apply]

omit [Field K] in
theorem range_pair_eq {w w' : Fin r ⊕ Fin r → K} : Set.range ![w, w'] = {w, w'} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem span_pair_eq_of_rank_two {P : Submodule K (Fin r ⊕ Fin r → K)}
    (hrank : Module.finrank K P = 2) {w w' : Fin r ⊕ Fin r → K} (hw : w ∈ P) (hw' : w' ∈ P)
    (hli : LinearIndependent K ![w, w']) : Submodule.span K {w, w'} = P := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · intro x hx
    rcases hx with rfl | rfl
    · exact hw
    · exact hw'
  · rw [← range_pair_eq, finrank_span_eq_card hli, hrank]
    simp

theorem eq_fix_of_rank_two (h3 : (3 : K) ≠ 0) {z : StatedSp r K} (hz : z ^ 3 = 1)
    {P : Submodule K (Fin r ⊕ Fin r → K)} (hstab : ∀ v ∈ P, spEnd z v ∈ P)
    (hrank : Module.finrank K P = 2) (hnd : ((spForm r K).restrict P).Nondegenerate)
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ P) (hw0 : w ≠ 0) (hzw : spEnd z w = w) :
    P ≤ fixSub z := by
  obtain ⟨w', hw', hc⟩ : ∃ w' ∈ P, spForm r K w w' ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (congrArg Subtype.val (hnd.1 ⟨w, hw⟩ fun y => h y y.2))
  have hli := linearIndependent_pair_of_spForm hc
  have hS := span_pair_eq_of_rank_two hrank hw hw' hli
  have hzw' : spEnd z w' ∈ Submodule.span K {w, w'} := by
    rw [hS]
    exact hstab w' hw'
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hzw'
  have hβ : β = 1 := by
    have h1 : spForm r K w (spEnd z w') = spForm r K w w' := by
      have := spEnd_isometry z w w'
      rwa [hzw] at this
    rw [← hαβ, map_add, map_smul, map_smul, spForm_isAlt w, smul_eq_mul, smul_eq_mul, mul_zero,
      zero_add] at h1
    exact mul_right_cancel₀ hc (by rw [one_mul]; exact h1)
  subst hβ
  rw [one_smul] at hαβ
  have e1 : spEnd z w' = α • w + w' := hαβ.symm
  have e2 : spEnd z (spEnd z w') = α • w + (α • w + w') := by
    rw [e1]
    simp only [map_add, map_smul, hzw, e1]
  have e3 : spEnd z (spEnd z (spEnd z w')) = α • w + (α • w + (α • w + w')) := by
    rw [e2]
    simp only [map_add, map_smul, hzw, e1]
  have hcube : α • w + (α • w + (α • w + w')) = w' := e3.symm.trans (spEnd_cube_apply hz w')
  have h3α : (3 * α) • w = 0 := by linear_combination (norm := module) hcube
  have hα : α = 0 :=
    (mul_eq_zero.mp ((smul_eq_zero.mp h3α).resolve_right hw0)).resolve_left h3
  have e1' : spEnd z w' = w' := by rw [e1, hα, zero_smul, zero_add]
  rw [← hS]
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with rfl | rfl
  · exact mem_fixSub.2 hzw
  · exact mem_fixSub.2 e1'

section Blocks

variable {K : Type} [Field K]

structure PlaneBlocks (E : Subgroup (StatedSp 2 K)) (a b : StatedSp 2 K)
    (P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)) : Prop where
  ha : a ∈ E
  hb : b ∈ E
  ha1 : a ≠ 1
  hb1 : b ≠ 1
  sup : P₀ ⊔ P₁ = ⊤
  orth : ∀ u ∈ P₀, ∀ v ∈ P₁, spForm 2 K u v = 0
  nd₀ : ((spForm 2 K).restrict P₀).Nondegenerate
  nd₁ : ((spForm 2 K).restrict P₁).Nondegenerate
  rank₀ : Module.finrank K P₀ = 2
  rank₁ : Module.finrank K P₁ = 2
  fix_a : ∀ v ∈ P₁, spEnd a v = v
  fix_b : ∀ v ∈ P₀, spEnd b v = v
  stab_a₀ : ∀ v ∈ P₀, spEnd a v ∈ P₀
  stab_a₁ : ∀ v ∈ P₁, spEnd a v ∈ P₁
  stab_b₀ : ∀ v ∈ P₀, spEnd b v ∈ P₀
  stab_b₁ : ∀ v ∈ P₁, spEnd b v ∈ P₁
  norm_a : ∀ v ∈ P₀, v + spEnd a v + spEnd a (spEnd a v) = 0
  norm_b : ∀ v ∈ P₁, v + spEnd b v + spEnd b (spEnd b v) = 0

theorem exists_planeBlocks (h3 : (3 : K) ≠ 0) {E : Subgroup (StatedSp 2 K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    ∃ (a b : StatedSp 2 K) (P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)), PlaneBlocks E a b P₀ P₁ := by
  obtain ⟨a, ha, ha1, u, -, hu0, hau⟩ := exists_fixed_of_plane hcomm hexp hcard h3
    (U := ⊤) (fun _ _ _ _ => trivial) top_ne_bot
  have ha3 := hexp a ha
  have hsup : normKer a ⊔ fixSub a = ⊤ := by rw [sup_comm]; exact fixSub_sup_normKer h3 ha3
  have horth : ∀ u ∈ normKer a, ∀ v ∈ fixSub a, spForm 2 K u v = 0 := fun u hu v hv => by
    rw [← spForm_isAlt.neg_eq v u, spForm_fixSub_normKer h3 a hv hu, neg_zero]
  have hP₁ne : fixSub a ≠ ⊥ := fun h => hu0 (by
    have : u ∈ fixSub a := mem_fixSub.2 hau
    rw [h] at this
    exact (Submodule.mem_bot K).1 this)
  have hP₀ne : normKer a ≠ ⊥ := by
    intro h
    apply ha1
    refine eq_one_of_spEnd_fix fun v => ?_
    have hv : v ∈ normKer a ⊔ fixSub a := by rw [hsup]; trivial
    rw [h, bot_sup_eq] at hv
    exact mem_fixSub.1 hv
  obtain ⟨hr₀, hr₁⟩ := finrank_eq_two_of_orth_sup hsup horth hP₀ne hP₁ne
  have hcomm' : ∀ e ∈ E, ∀ v, spEnd a (spEnd e v) = spEnd e (spEnd a v) := fun e he v => by
    rw [← spEnd_comp_apply, ← spEnd_comp_apply, hcomm a ha e he]
  have hstab_fix : ∀ e ∈ E, ∀ v ∈ fixSub a, spEnd e v ∈ fixSub a := fun e he v hv => by
    rw [mem_fixSub] at hv ⊢
    rw [hcomm' e he, hv]
  have hstab_norm : ∀ e ∈ E, ∀ v ∈ normKer a, spEnd e v ∈ normKer a := fun e he v hv => by
    rw [mem_normKer] at hv ⊢
    have h2 : spEnd a (spEnd a (spEnd e v)) = spEnd e (spEnd a (spEnd a v)) := by
      rw [hcomm' e he, hcomm' e he]
    rw [h2, hcomm' e he, ← map_add, ← map_add, hv, map_zero]
  obtain ⟨b, hb, hb1, w, hwP, hw0, hbw⟩ := exists_fixed_of_plane hcomm hexp hcard h3
    (U := normKer a) hstab_norm hP₀ne
  have hb3 := hexp b hb
  have hP₀fix : normKer a ≤ fixSub b :=
    eq_fix_of_rank_two h3 hb3 (hstab_norm b hb) hr₀ (nondegenerate_normKer h3 ha3) hwP hw0 hbw
  have hnormb : ∀ v ∈ fixSub a, v + spEnd b v + spEnd b (spEnd b v) = 0 := by
    intro v hv
    by_contra h0
    have hbv : spEnd b v ∈ fixSub a := hstab_fix b hb v hv
    have hmem : v + spEnd b v + spEnd b (spEnd b v) ∈ fixSub a :=
      (fixSub a).add_mem ((fixSub a).add_mem hv hbv) (hstab_fix b hb _ hbv)
    have hP₁fix : fixSub a ≤ fixSub b :=
      eq_fix_of_rank_two h3 hb3 (hstab_fix b hb) hr₁ (nondegenerate_fixSub h3 ha3) hmem h0
        (spEnd_norm_fixed hb3 v)
    apply hb1
    refine eq_one_of_spEnd_fix fun v => ?_
    have hv' : v ∈ normKer a ⊔ fixSub a := by rw [hsup]; trivial
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hv'
    rw [map_add, mem_fixSub.1 (hP₀fix hp), mem_fixSub.1 (hP₁fix hp')]
  exact ⟨a, b, normKer a, fixSub a, ⟨ha, hb, ha1, hb1, hsup, horth, nondegenerate_normKer h3 ha3,
    nondegenerate_fixSub h3 ha3, hr₀, hr₁, fun v hv => mem_fixSub.1 hv,
    fun v hv => mem_fixSub.1 (hP₀fix hv), hstab_norm a ha, hstab_fix a ha, hstab_norm b hb,
    hstab_fix b hb, fun v hv => mem_normKer.1 hv, hnormb⟩⟩

end Blocks

end CFSG.LieType.SeitzGeneration
