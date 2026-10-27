module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Decomp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

variable {E : Type} [Group E]

private theorem orderOf_conj' {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (x := x) (y := g * x * g⁻¹) (by
    show g * x = (g * x * g⁻¹) * g
    group)).symm

theorem sec8t84d1_exists_order5 {A : Subgroup (MulAut E)}
    (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6))) : ∃ a ∈ A, orderOf a = 5 := by
  obtain ⟨e⟩ := hA
  refine ⟨e.symm c5, (e.symm c5).2, ?_⟩
  rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, orderOf_c5]

theorem sec8t84d1_exists_order4 {A : Subgroup (MulAut E)}
    (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6))) : ∃ a ∈ A, orderOf a = 4 := by
  obtain ⟨e⟩ := hA
  refine ⟨e.symm u4, (e.symm u4).2, ?_⟩
  rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, orderOf_u4]

theorem sec8t84d1_le_of_order5 {A B : Subgroup (MulAut E)}
    (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6)))
    (hB : ∀ a ∈ A, orderOf a = 5 → a ∈ B) : A ≤ B := by
  obtain ⟨e⟩ := hA
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (α := Fin 6) (by rw [Nat.card_fin]; norm_num)
  haveI : IsSimpleGroup ↥A := e.isSimpleGroup
  let S : Set ↥A := {x | orderOf ((x : MulAut E)) = 5}
  have hS : ∀ x : ↥A, x ∈ S ↔ orderOf ((x : MulAut E)) = 5 := fun x => Iff.rfl
  have hKnormal : (Subgroup.closure S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.closure_induction (k := S)
      (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure S) ?_ ?_ ?_ ?_ hn
    · intro x hx
      exact Subgroup.subset_closure ((hS _).2 (by
        have hconj : orderOf (((g * x * g⁻¹ : ↥A) : MulAut E)) =
            orderOf (((x : ↥A) : MulAut E)) := by
          calc orderOf (((g * x * g⁻¹ : ↥A) : MulAut E))
              = orderOf (g * x * g⁻¹ : ↥A) := Subgroup.orderOf_coe _
            _ = orderOf (x : ↥A) := orderOf_conj' g x
            _ = orderOf (((x : ↥A) : MulAut E)) := (Subgroup.orderOf_coe _).symm
        rw [hconj]
        exact (hS x).1 hx))
    · simpa using (Subgroup.closure S).one_mem
    · intro x y hx hy ihx ihy
      have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [hxy]
      exact (Subgroup.closure S).mul_mem ihx ihy
    · intro x hx ihx
      have hxinv : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [hxinv]
      exact (Subgroup.closure S).inv_mem ihx
  haveI : (Subgroup.closure S).Normal := hKnormal
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.closure S) with hbot | htop
  · exfalso
    have hordE : orderOf (((e.symm c5 : ↥A) : MulAut E)) = 5 := by
      rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, orderOf_c5]
    have hmem : (e.symm c5 : ↥A) ∈ Subgroup.closure S :=
      Subgroup.subset_closure ((hS _).2 hordE)
    rw [hbot] at hmem
    have h1 : (e.symm c5 : ↥A) = 1 := by simpa using hmem
    rw [h1] at hordE
    simp only [Subgroup.coe_one, orderOf_one] at hordE
    omega
  · have hKB : Subgroup.closure S ≤ B.subgroupOf A := by
      rw [Subgroup.closure_le]
      intro x hx
      change (x : MulAut E) ∈ B
      exact hB (x : MulAut E) x.2 (by simpa using (hS x).1 hx)
    intro a ha
    have hmemK : (⟨a, ha⟩ : ↥A) ∈ Subgroup.closure S := by
      rw [htop]; exact Subgroup.mem_top _
    have hthis : ((⟨a, ha⟩ : ↥A) : MulAut E) ∈ B :=
      (Subgroup.mem_subgroupOf).1 (hKB hmemK)
    simpa using hthis

theorem sec8t84d1_inf_eq_bot {A B : Subgroup (MulAut E)}
    (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ⊓ B = ⊥ := by
  obtain ⟨e⟩ := hA
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (α := Fin 6) (by rw [Nat.card_fin]; norm_num)
  haveI : IsSimpleGroup ↥A := e.isSimpleGroup
  have hNnormal : ((A ⊓ B).subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : MulAut E) ∈ A ⊓ B := hn
    rw [Subgroup.mem_inf] at hn'
    obtain ⟨hnA, hnB⟩ := hn'
    change ((g * n * g⁻¹ : ↥A) : MulAut E) ∈ A ⊓ B
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact A.mul_mem (A.mul_mem g.2 hnA) (A.inv_mem g.2)
    · have hcomm' : (g : MulAut E) * (n : MulAut E) = (n : MulAut E) * (g : MulAut E) :=
        hcomm (g : MulAut E) g.2 (n : MulAut E) hnB
      have hgn : ((g * n * g⁻¹ : ↥A) : MulAut E) = (n : MulAut E) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcomm']
        group
      rw [hgn]
      exact hnB
  haveI : ((A ⊓ B).subgroupOf A).Normal := hNnormal
  rcases Subgroup.Normal.eq_bot_or_eq_top ((A ⊓ B).subgroupOf A) with hbot | htop
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A := hx
    rw [hbot] at hxN
    have h1 : (⟨x, hx.1⟩ : ↥A) = 1 := by simpa using hxN
    exact Subtype.ext_iff.1 h1
  · exfalso
    have hle : A ≤ B := by
      intro x hx
      have hxN : (⟨x, hx⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A := by
        rw [htop]; exact Subgroup.mem_top _
      have hxAB : x ∈ A ⊓ B := hxN
      exact hxAB.2
    have hcommA : ∀ a b : ↥A, a * b = b * a := fun a b =>
      Subtype.ext (hcomm (a : MulAut E) a.2 (b : MulAut E) (hle b.2))
    have hxy : ∀ x y : alternatingGroup (Fin 6), x * y = y * x := by
      intro x y
      have h := hcommA (e.symm x) (e.symm y)
      have h' := congrArg e h
      simpa using h'
    have hcomm_alt : IsMulCommutative (alternatingGroup (Fin 6)) := IsMulCommutative.of_comm hxy
    rw [alternatingGroup.isMulCommutative_iff_card_le_three] at hcomm_alt
    rw [Nat.card_fin] at hcomm_alt
    omega

theorem sec8t84d1_card_fixSub [Finite E] (hc : ∀ x y : E, x * y = y * x)
    (hs : ∀ x : E, x * x = 1) (hcard : Nat.card E = 2 ^ 8) {A B : Subgroup (MulAut E)}
    (hB : Nonempty (↥B ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {δ : MulAut E} (hδA : δ ∈ A)
    (hδ : orderOf δ = 5) : Nat.card (fixSub δ) = 16 := by
  have hW : Nat.card E = 256 := by rw [hcard]; norm_num
  have h5 : δ ^ 5 = 1 := hδ ▸ pow_orderOf_eq_one δ
  rcases card_fixSub_five_256 hW h5 with h1 | h16 | h256
  · exfalso
    have hbot : fixSub δ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨u, huB, hu4⟩ := sec8t84d1_exists_order4 hB
    have hcu : δ * u = u * δ := hcomm δ hδA u huB
    have hu2 : u ^ (2 ^ 2) = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu4] at this
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact this
    have hsq := sq_eq_one_of_comm_of_fixSub_eq_bot hc hs hW h5 hbot hcu hu2
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hu4] at hdvd
    omega
  · exact h16
  · exfalso
    have h1 : δ = 1 := eq_one_of_card_fixSub (by rw [h256, hW])
    rw [h1, orderOf_one] at hδ
    omega

theorem sec8t84d1_pair [Finite E] (hc : ∀ x y : E, x * y = y * x) (hs : ∀ x : E, x * x = 1)
    (hcard : Nat.card E = 2 ^ 8) {A B : Subgroup (MulAut E)}
    (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6)))
    (hB : Nonempty (↥B ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {δ γ : MulAut E} (hδA : δ ∈ A) (hγB : γ ∈ B)
    (hδ : orderOf δ = 5) (hγ : orderOf γ = 5) :
    fixSub δ ⊓ fixSub γ = ⊥ ∧ fixSub γ = normSub hc δ ∧ fixSub δ = normSub hc γ := by
  have hW : Nat.card E = 256 := by rw [hcard]; norm_num
  have h5δ : δ ^ 5 = 1 := hδ ▸ pow_orderOf_eq_one δ
  have h5γ : γ ^ 5 = 1 := hγ ▸ pow_orderOf_eq_one γ
  have hcommδγ : δ * γ = γ * δ := hcomm δ hδA γ hγB
  have hinfAB : A ⊓ B = ⊥ := sec8t84d1_inf_eq_bot hA hcomm
  have hind : ∀ i j : ℤ, δ ^ i * γ ^ j = 1 → δ ^ i = 1 ∧ γ ^ j = 1 := by
    intro i j h
    have hδB : δ ^ i ∈ B := by
      rw [eq_inv_of_mul_eq_one_left h]
      exact B.inv_mem (B.zpow_mem hγB j)
    have hmem : δ ^ i ∈ A ⊓ B := ⟨A.zpow_mem hδA i, hδB⟩
    have hδi : δ ^ i = 1 := by
      have := hmem; rw [hinfAB] at this; simpa using this
    refine ⟨hδi, ?_⟩
    rw [hδi, one_mul] at h
    exact h
  have h16δ : Nat.card (fixSub δ) = 16 :=
    sec8t84d1_card_fixSub hc hs hcard hB hcomm hδA hδ
  have h16γ : Nat.card (fixSub γ) = 16 :=
    sec8t84d1_card_fixSub (A := B) (B := A) hc hs hcard hA
      (fun a ha b hb => (hcomm b hb a ha).symm) hγB hγ
  have hinf : fixSub δ ⊓ fixSub γ = ⊥ :=
    fixSub_inf_eq_bot_of_indep hc hs hW (MonoidHom.id (MulAut E)) Function.injective_id
      hδ hγ hcommδγ hind h16δ
  refine ⟨hinf, ?_, ?_⟩
  · exact fixSub_eq_normSub hc hs hW h5δ hcommδγ h16δ h16γ (by rw [inf_comm]; exact hinf)
  · exact fixSub_eq_normSub hc hs hW h5γ hcommδγ.symm h16γ h16δ hinf

end CFSG.OddStandard.SmallF3.Omega
