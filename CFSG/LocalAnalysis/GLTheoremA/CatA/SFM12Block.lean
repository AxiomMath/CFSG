module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_one_of_commutator_eq_top {K M : Type} [Group K] [Group M] (hK : commutator K = ⊤)
    (c : K → M) (hmul : ∀ x y, c (x * y) = c x * c y) (hcomm : ∀ x y, Commute (c x) (c y)) (x : K) :
    c x = 1 := by
  have hone : c 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have h2 : c 1 * c 1 = c 1 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h2
  have hinv : ∀ a, c a⁻¹ = (c a)⁻¹ := by
    intro a
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  let S : Subgroup K :=
    { carrier := {a | c a = 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hmul, ha, hb, mul_one]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact hone
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hinv, ha, inv_one] }
  have hS : commutator K ≤ S := by
    unfold commutator
    rw [Subgroup.commutator_le]
    intro a _ b _
    show c ⁅a, b⁆ = 1
    rw [commutatorElement_def, hmul, hmul, hmul, hinv, hinv]
    have hc := (hcomm a b).eq
    calc c a * c b * (c a)⁻¹ * (c b)⁻¹ = (c b * c a) * (c a)⁻¹ * (c b)⁻¹ := by rw [hc]
      _ = 1 := by group
  rw [hK] at hS
  exact hS (Subgroup.mem_top x)

theorem exists_noncentral_of_quasisimple {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    ∃ x : K, x ∉ Subgroup.center K := by
  haveI : Nontrivial (K ⧸ Subgroup.center K) := hK.2.toNontrivial
  obtain ⟨y, hy⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) y
  exact ⟨x, fun hx => hy ((QuotientGroup.eq_one_iff x).2 hx)⟩

theorem not_all_commute_of_quasisimple {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    ¬ ∀ x y : K, x * y = y * x := by
  intro h
  obtain ⟨x, hx⟩ := exists_noncentral_of_quasisimple hK
  exact hx (Subgroup.mem_center_iff.2 fun g => h g x)

theorem quasisimple_dichot {J : Subgroup G} (hJ : CFSG.Open.IsQuasisimple J) {M : Subgroup G}
    (hMJ : M ≤ J) (hM : ∀ j ∈ J, ∀ m ∈ M, j * m * j⁻¹ ∈ M) :
    (∀ m ∈ M, ∀ j ∈ J, m * j = j * m) ∨
      (∀ j ∈ J, ∃ m ∈ M, ∃ z ∈ J, (∀ k ∈ J, z * k = k * z) ∧ j = m * z) := by
  classical
  let Mj : Subgroup J := M.subgroupOf J
  have hMn : Mj.Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hM (g : G) g.2 (n : G) hn
    simpa using this
  let Z : Subgroup J := Subgroup.center J
  let K : Subgroup (J ⧸ Z) := Mj.map (QuotientGroup.mk' Z)
  haveI hKn : K.Normal :=
    Subgroup.Normal.map hMn (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  rcases hJ.2.eq_bot_or_eq_top_of_normal K with hK | hK
  · left
    intro m hm j hj
    have hmJ : (⟨m, hMJ hm⟩ : J) ∈ Mj := Subgroup.mem_subgroupOf.2 hm
    have hmem : QuotientGroup.mk' Z (⟨m, hMJ hm⟩ : J) ∈ K := Subgroup.mem_map_of_mem _ hmJ
    rw [hK, Subgroup.mem_bot] at hmem
    have hcen : (⟨m, hMJ hm⟩ : J) ∈ Subgroup.center J := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    have := (Subgroup.mem_center_iff.1 hcen) ⟨j, hj⟩
    exact (congrArg Subtype.val this).symm
  · right
    intro j hj
    have hmem : QuotientGroup.mk' Z (⟨j, hj⟩ : J) ∈ K := by
      rw [hK]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hmem
    obtain ⟨n, hn, hnj⟩ := hmem
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq] at hnj
    have hz : (n⁻¹ * ⟨j, hj⟩ : J) ∈ Subgroup.center J := hnj
    refine ⟨(n : G), Subgroup.mem_subgroupOf.1 hn, ((n⁻¹ * ⟨j, hj⟩ : J) : G),
      (n⁻¹ * ⟨j, hj⟩ : J).2, fun k hk => ?_, ?_⟩
    · have := (Subgroup.mem_center_iff.1 hz) ⟨k, hk⟩
      exact (congrArg Subtype.val this).symm
    · simp

theorem block_mem_of_block {Λ : Type} {C N J : Subgroup G} {U : Λ → Subgroup G} {ψ : Λ → G → G}
    (hJq : CFSG.Open.IsQuasisimple J) (hJN : J ≤ N) (hNC : N ≤ C)
    (hJC : ∀ c ∈ C, ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hUN : ∀ l, U l ≤ N) (hUC : ∀ l, ∀ c ∈ C, ∀ u ∈ U l, c * u * c⁻¹ ∈ U l)
    (hψmul : ∀ l, ∀ x ∈ N, ∀ y ∈ N, ψ l (x * y) = ψ l x * ψ l y)
    (hψmem : ∀ l, ∀ x ∈ N, ψ l x ∈ U l)
    (hψid : ∀ l, ∀ u ∈ U l, ψ l u = u)
    (hψzero : ∀ l m, l ≠ m → ∀ u ∈ U m, ψ l u = 1)
    (hψinj : ∀ x ∈ N, (∀ l, ψ l x = 1) → x = 1) :
    ∃ l0, J ≤ U l0 := by
  classical
  have hdich : ∀ l, (∀ m ∈ J ⊓ U l, ∀ j ∈ J, m * j = j * m) ∨
      (∀ j ∈ J, ∃ m ∈ J ⊓ U l, ∃ z ∈ J, (∀ k ∈ J, z * k = k * z) ∧ j = m * z) := by
    intro l
    refine quasisimple_dichot hJq inf_le_left ?_
    intro j hj m hm
    exact ⟨J.mul_mem (J.mul_mem hj hm.1) (J.inv_mem hj), hUC l j (hNC (hJN hj)) m hm.2⟩
  have hfirst_cent : ∀ l, (∀ m ∈ J ⊓ U l, ∀ j ∈ J, m * j = j * m) →
      ∀ b ∈ U l, ∀ x ∈ J, b * x = x * b := by
    intro l hF b hb x hx
    have hbC : b ∈ C := hNC (hUN l hb)
    let c : J → G := fun y => b * (y : G) * b⁻¹ * (y : G)⁻¹
    have hmemc : ∀ y : J, c y ∈ J ⊓ U l := by
      intro y
      have h1 : (y : G) * b⁻¹ * (y : G)⁻¹ ∈ U l :=
        hUC l (y : G) (hNC (hJN y.2)) b⁻¹ ((U l).inv_mem hb)
      have h2 : c y = b * ((y : G) * b⁻¹ * (y : G)⁻¹) := by simp only [c]; group
      refine ⟨?_, ?_⟩
      · show b * (y : G) * b⁻¹ * (y : G)⁻¹ ∈ J
        exact J.mul_mem (hJC b hbC (y : G) y.2) (J.inv_mem y.2)
      · rw [h2]
        exact (U l).mul_mem hb h1
    have hcomm : ∀ y z : J, Commute (c y) (c z) := fun y z =>
      hF (c y) (hmemc y) (c z) (hmemc z).1
    have hmul : ∀ y z : J, c (y * z) = c y * c z := by
      intro y z
      have hu : (b * (y : G) * b⁻¹) * c z = c z * (b * (y : G) * b⁻¹) :=
        (hF (c z) (hmemc z) (b * (y : G) * b⁻¹) (hJC b hbC (y : G) y.2)).symm
      have hcz : c z * c y = c y * c z := (hcomm z y).eq
      rw [← hcz]
      show b * ((y : G) * (z : G)) * b⁻¹ * ((y : G) * (z : G))⁻¹ = c z * c y
      calc b * ((y : G) * (z : G)) * b⁻¹ * ((y : G) * (z : G))⁻¹
          = (b * (y : G) * b⁻¹) * c z * (y : G)⁻¹ := by simp only [c]; group
        _ = c z * (b * (y : G) * b⁻¹) * (y : G)⁻¹ := by rw [hu]
        _ = c z * c y := by simp only [c]; group
    have key := eq_one_of_commutator_eq_top (K := ↥J) hJq.1 c hmul hcomm ⟨x, hx⟩
    have key' : b * x * b⁻¹ * x⁻¹ = 1 := key
    have h1 : b * x * b⁻¹ = x := mul_inv_eq_one.1 key'
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [h1]
  have hfirst_kill : ∀ l, (∀ m ∈ J ⊓ U l, ∀ j ∈ J, m * j = j * m) → ∀ x ∈ J, ψ l x = 1 := by
    intro l hF x hx
    have hcen := hfirst_cent l hF
    have hpsi_comm : ∀ b ∈ U l, ∀ y ∈ J, b * ψ l y = ψ l y * b := by
      intro b hb y hy
      have h1 := congrArg (ψ l) (hcen b hb y hy)
      rw [hψmul l b (hUN l hb) y (hJN hy), hψmul l y (hJN hy) b (hUN l hb), hψid l b hb] at h1
      exact h1
    have hcomm : ∀ y z : J, Commute (ψ l y) (ψ l z) := fun y z =>
      (hpsi_comm (ψ l z) (hψmem l z (hJN z.2)) y y.2).symm
    have hmul : ∀ y z : J, ψ l (y * z : J) = ψ l y * ψ l z := by
      intro y z
      exact hψmul l y (hJN y.2) z (hJN z.2)
    exact eq_one_of_commutator_eq_top (K := ↥J) hJq.1 (fun y : J => ψ l (y : G)) hmul hcomm ⟨x, hx⟩
  have hsecond_kill : ∀ l m, l ≠ m →
      (∀ j ∈ J, ∃ n ∈ J ⊓ U l, ∃ z ∈ J, (∀ k ∈ J, z * k = k * z) ∧ j = n * z) →
      ∀ x ∈ J, ψ m x = 1 := by
    intro l m hlm hS
    have hz : ∀ y ∈ J, ∃ z ∈ J, (∀ k ∈ J, z * k = k * z) ∧ ψ m y = ψ m z := by
      intro y hy
      obtain ⟨n, hn, z, hzJ, hcen, rfl⟩ := hS y hy
      refine ⟨z, hzJ, hcen, ?_⟩
      rw [hψmul m n (hJN hn.1) z (hJN hzJ), hψzero m l (Ne.symm hlm) n hn.2, one_mul]
    have hcomm : ∀ y z : J, Commute (ψ m y) (ψ m z) := by
      intro y z
      obtain ⟨zy, hzy, hcy, hyeq⟩ := hz (y : G) y.2
      obtain ⟨zz, hzz, hcz, hzeq⟩ := hz (z : G) z.2
      show ψ m y * ψ m z = ψ m z * ψ m y
      rw [hyeq, hzeq, ← hψmul m zy (hJN hzy) zz (hJN hzz), ← hψmul m zz (hJN hzz) zy (hJN hzy),
        hcy zz hzz]
    have hmul : ∀ y z : J, ψ m (y * z : J) = ψ m y * ψ m z := by
      intro y z
      exact hψmul m y (hJN y.2) z (hJN z.2)
    intro x hx
    exact eq_one_of_commutator_eq_top (K := ↥J) hJq.1 (fun y : J => ψ m (y : G)) hmul hcomm ⟨x, hx⟩
  have huniq : ∀ l m, l ≠ m →
      (∀ j ∈ J, ∃ n ∈ J ⊓ U l, ∃ z ∈ J, (∀ k ∈ J, z * k = k * z) ∧ j = n * z) →
      (∀ j ∈ J, ∃ n ∈ J ⊓ U m, ∃ z ∈ J, (∀ k ∈ J, z * k = k * z) ∧ j = n * z) → False := by
    intro l m hlm hSl hSm
    have hxc : ∀ x ∈ J, ∀ k ∈ J, x * k = k * x := by
      intro x hx k hk
      obtain ⟨n, hn, z, hzJ, hcen, hxeq⟩ := hSm x hx
      have hz1 : ψ m z = 1 := hsecond_kill l m hlm hSl z hzJ
      have hx1 : ψ m x = 1 := hsecond_kill l m hlm hSl x hx
      have hn1 : n = 1 := by
        have h2 : ψ m x = ψ m n * ψ m z := by
          rw [hxeq, hψmul m n (hJN hn.1) z (hJN hzJ)]
        rw [hz1, mul_one, hψid m n hn.2] at h2
        exact h2.symm.trans hx1
      rw [hxeq, hn1, one_mul]
      exact hcen k hk
    apply not_all_commute_of_quasisimple hJq
    intro x y
    exact Subtype.ext (by simpa only [Subgroup.coe_mul] using hxc x x.2 y y.2)
  have hexists : ∃ l, ∀ j ∈ J, ∃ n ∈ J ⊓ U l, ∃ z ∈ J, (∀ k ∈ J, z * k = k * z) ∧ j = n * z := by
    by_contra hcon
    have hF : ∀ l, ∀ m ∈ J ⊓ U l, ∀ j ∈ J, m * j = j * m := fun l =>
      (hdich l).resolve_right (fun h => hcon ⟨l, h⟩)
    obtain ⟨x, hxnc⟩ := exists_noncentral_of_quasisimple hJq
    have hx1 : (x : G) = 1 := by
      apply hψinj (x : G) (hJN x.2)
      intro l
      exact hfirst_kill l (hF l) (x : G) x.2
    apply hxnc
    have : x = 1 := Subtype.ext hx1
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨l0, hl0⟩ := hexists
  refine ⟨l0, fun j hj => ?_⟩
  have hkill : ∀ m, m ≠ l0 → ∀ i ∈ J, ψ m i = 1 := fun m hm =>
    hfirst_kill m ((hdich m).resolve_right (fun h => huniq l0 m (Ne.symm hm) hl0 h))
  obtain ⟨w, hw⟩ : ∃ w, w = ψ l0 j := ⟨_, rfl⟩
  have hwU : w ∈ U l0 := by
    rw [hw]
    exact hψmem l0 j (hJN hj)
  have hwN : w ∈ N := hUN l0 hwU
  have hn1 : j * w⁻¹ = 1 := by
    apply hψinj (j * w⁻¹) (N.mul_mem (hJN hj) (N.inv_mem hwN))
    intro m
    rcases eq_or_ne m l0 with hm | hm
    · rw [hm, hψmul l0 j (hJN hj) w⁻¹ (N.inv_mem hwN), hψid l0 w⁻¹ ((U l0).inv_mem hwU), ← hw,
        mul_inv_cancel]
    · rw [hψmul m j (hJN hj) w⁻¹ (N.inv_mem hwN), hkill m hm j hj,
        hψzero m l0 hm w⁻¹ ((U l0).inv_mem hwU), one_mul]
  have hjw : j = w := mul_inv_eq_one.1 hn1
  rw [hjw]
  exact hwU

end CFSG.LocalAnalysis.GLTheoremA.SFM12
