module

public import CFSG.Fischer.Classification.Unitary.Star
public import CFSG.Fischer.Classification.Unitary.Cayley
public import CFSG.Fischer.Classification.Unitary.Coords

public section

namespace CFSG.Fischer.Classification.Unitary

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer CFSG.Fischer

section Transport

variable {X : Type} [Group X] {E : Set X}

theorem mem_ySet_map (ψ : X ≃* X) (hE : ψ '' E = E) {e x y : X} (hy : y ∈ ySet E e x) :
    ψ y ∈ ySet E (ψ e) (ψ x) := by
  refine ⟨hE ▸ ⟨y, hy.1, rfl⟩, fun s hs => ?_⟩
  rw [muSet_congr ψ hE] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [localClass_congr ψ hE rfl]
  exact ⟨t, hy.2 ht, rfl⟩

theorem Pair.image_conj (hP : Pair X E) (c : X) : MulAut.conj c '' E = E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Pair.conj_mem hP hy c
  · intro hx
    refine ⟨c⁻¹ * x * c, by simpa using Pair.conj_mem hP hx c⁻¹, ?_⟩
    rw [MulAut.conj_apply]
    group

end Transport

variable {n : ℕ}

theorem ι_ne_smul_v₀ {z : Fin n → K} (hz : z ≠ 0) (c : K) : ι n z ≠ c • v₀ n := fun h =>
  hz (by rw [← π_ι z, h, map_smul, π_v₀, smul_zero])

theorem ι_ne_smul_u₀ {z : Fin n → K} (hz : z ≠ 0) (c : K) : ι n z ≠ c • u₀ n := fun h =>
  hz (by rw [← π_ι z, h, map_smul, π_u₀, smul_zero])

theorem ι_ne_zero {z : Fin n → K} (hz : z ≠ 0) : ι n z ≠ 0 := fun h =>
  hz (ι_injective (by rw [h, map_zero]))

theorem tq_ι_mem_muSet (hn : 1 ≤ n) {z : Fin n → K} (hz0 : z ≠ 0) (hz : herm frob z z = 0) :
    tq (ι n z) ∈ muSet (DG (n + 2)) (tq (v₀ n)) (tq (u₀ n)) := by
  have hιz : herm frob (ι n z) (ι n z) = 0 := by rw [herm_ι_ι, hz]
  exact ⟨(tq_mem_localClass_iff (by omega) v₀_ne_zero herm_v₀_v₀ (ι_ne_zero hz0) hιz).2
      ⟨herm_v₀_ι z, ι_ne_smul_v₀ hz0⟩,
    (tq_mem_localClass_iff (by omega) u₀_ne_zero herm_u₀_u₀ (ι_ne_zero hz0) hιz).2
      ⟨herm_u₀_ι z, ι_ne_smul_u₀ hz0⟩⟩

theorem frob_eq_zero_iff {c : K} : frob c = 0 ↔ c = 0 := map_eq_zero_iff frob frob.injective

theorem ySet_std (hn : 2 ≤ n) {y : PG (n + 2)}
    (hy : y ∈ ySet (DG (n + 2)) (tq (v₀ n)) (tq (u₀ n))) :
    y ∈ ({tq (v₀ n), tq (u₀ n), tq (v₀ n) * tq (u₀ n) * tq (v₀ n)} : Set (PG (n + 2))) := by
  obtain ⟨c, hc0, hc, rfl⟩ := hy.1
  have hπ : π n c = 0 := by
    refine eq_zero_of_forall_isotropic hn fun z hz => ?_
    by_cases hz0 : z = 0
    · rw [hz0, herm_zero_left]
    have hιz : herm frob (ι n z) (ι n z) = 0 := by rw [herm_ι_ι, hz]
    have h := (tq_mem_localClass_iff (by omega) hc0 hc (ι_ne_zero hz0) hιz).1
      (hy.2 (tq_ι_mem_muSet (by omega) hz0 hz))
    rw [herm_ι_right] at h
    exact herm_eq_zero_comm frob frob_frob h.1
  have hdec := decomp c
  rw [hπ, map_zero, add_zero] at hdec
  have hcc := herm_eq_coords c c
  rw [hπ, herm_zero_left, add_zero, hc] at hcc
  set α := herm frob (u₀ n) c with hα
  set β := herm frob (v₀ n) c with hβ
  have ht : frob α * β + frob (frob α * β) = 0 := by
    rw [map_mul, frob_frob, mul_comm α, hcc]
  rcases (add_frob_eq_zero_iff _).1 ht with h0 | h1
  · rcases mul_eq_zero.1 h0 with hα0 | hβ0
    · rw [frob_eq_zero_iff] at hα0
      rw [hα0, zero_smul, zero_add] at hdec
      have hβ0 : β ≠ 0 := by rintro hb; rw [hb, zero_smul] at hdec; exact hc0 hdec
      refine Or.inr (Or.inl ?_)
      rw [hdec]
      exact congrArg QuotientGroup.mk (tvU_smul_vec herm_u₀_u₀ hβ0)
    · rw [hβ0, zero_smul, add_zero] at hdec
      have hα0 : α ≠ 0 := by rintro ha; rw [ha, zero_smul] at hdec; exact hc0 hdec
      refine Or.inl ?_
      rw [hdec]
      exact congrArg QuotientGroup.mk (tvU_smul_vec herm_v₀_v₀ hα0)
  · have hα0 : α ≠ 0 := by rintro ha; rw [ha, map_zero, zero_mul] at h1; exact zero_ne_one h1
    have hβα : β = α := by
      rw [frob_eq_inv hα0] at h1
      exact (eq_inv_of_mul_eq_one_right h1).trans (inv_inv α)
    refine Or.inr (Or.inr ?_)
    rw [Set.mem_singleton_iff, tq_mul_tq_mul_tq herm_v₀_v₀ herm_u₀_u₀, tvU_smul herm_v₀_v₀,
      herm_v₀_u₀, one_smul, hdec, hβα, ← smul_add, add_comm (u₀ n) (v₀ n)]
    exact congrArg QuotientGroup.mk (tvU_smul_vec (by
      rw [herm_add_left, herm_add_right, herm_add_right, herm_u₀_u₀, herm_v₀_v₀, herm_u₀_v₀,
        herm_v₀_u₀, add_zero, zero_add, add_self_K]) hα0)

theorem tripleProperty_DG (hn : 2 ≤ n) : TripleProperty (DG (n + 2)) := by
  rintro _ _ ⟨a, ha0, ha, rfl⟩ ⟨b, hb0, hb, rfl⟩ hex y hy
  have hab : herm frob a b ≠ 0 := fun h => hex ((tq_commute_iff (by omega) ha0 ha hb0 hb).2 h)
  have hb' : herm frob ((herm frob a b)⁻¹ • b) ((herm frob a b)⁻¹ • b) = 0 :=
    herm_smul_smul_self hb _
  have hab' : herm frob a ((herm frob a b)⁻¹ • b) = 1 := by
    rw [herm_smul_right, inv_mul_cancel₀ hab]
  have htq : tq ((herm frob a b)⁻¹ • b) = tq b :=
    congrArg QuotientGroup.mk (tvU_smul_vec hb (inv_ne_zero hab))
  obtain ⟨g, hga, hgb⟩ := exists_smul_eq_hyp (by omega) ha0 ha hb' hab'
  set ψ := MulAut.conj (QuotientGroup.mk g : PG (n + 2)) with hψdef
  have hψ : ∀ v : Fin (n + 2) → K, herm frob v v = 0 → ψ (tq v) = tq (g • v) := fun v hv => by
    rw [hψdef, MulAut.conj_apply, conj_tq g hv]
  have hψE : ψ '' DG (n + 2) = DG (n + 2) := Pair.image_conj (pair_DG (by omega)) _
  have h1 := mem_ySet_map ψ hψE hy
  rw [hψ a ha, hga, ← htq, hψ _ hb', hgb] at h1
  have h2 := ySet_std hn h1
  have e1 : tq (v₀ n) = ψ (tq a) := by rw [hψ a ha, hga]
  have e2 : tq (u₀ n) = ψ (tq b) := by rw [← htq, hψ _ hb', hgb]
  rw [e1, e2, ← map_mul, ← map_mul] at h2
  rcases h2 with h | h | h
  · exact Or.inl (ψ.injective h)
  · exact Or.inr (Or.inl (ψ.injective h))
  · exact Or.inr (Or.inr (ψ.injective h))

section MuFamily

variable {m : ℕ}

theorem ne_smul_of_herm {a b w : Fin m → K} (hw0 : w ≠ 0) (hbw : herm frob b w = 0)
    (hba : herm frob b a ≠ 0) (c : K) : w ≠ c • a := by
  rintro rfl
  rw [herm_smul_right] at hbw
  rcases mul_eq_zero.1 hbw with h | h
  · exact hw0 (by rw [h, zero_smul])
  · exact hba h

theorem tq_mem_muSet_iff (hm : 3 ≤ m) {a b w : Fin m → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0)
    (hb0 : b ≠ 0) (hb : herm frob b b = 0) (hab : herm frob a b ≠ 0) (hw0 : w ≠ 0)
    (hw : herm frob w w = 0) :
    tq w ∈ muSet (DG m) (tq a) (tq b) ↔ herm frob a w = 0 ∧ herm frob b w = 0 := by
  have hba : herm frob b a ≠ 0 := fun h => hab (herm_eq_zero_comm frob frob_frob h)
  rw [muSet, Set.mem_inter_iff, tq_mem_localClass_iff hm ha0 ha hw0 hw,
    tq_mem_localClass_iff hm hb0 hb hw0 hw]
  exact ⟨fun h => ⟨h.1.1, h.2.1⟩, fun h => ⟨⟨h.1, ne_smul_of_herm hw0 h.2 hba⟩,
    ⟨h.2, ne_smul_of_herm hw0 h.1 hab⟩⟩⟩

theorem mem_DG_of_mem_muSet {d c q : PG m} (hq : q ∈ muSet (DG m) d c) : q ∈ DG m := hq.1.1

variable {n : ℕ}

theorem herm_eq_herm_of_perp {b b' w : Fin (n + 2) → K} (hb : herm frob (v₀ n) b = 1)
    (hb' : herm frob (v₀ n) b' = 1) (hπ : π n b = π n b') (hw : herm frob (v₀ n) w = 0) :
    herm frob b w = herm frob b' w := by
  rw [herm_eq_coords b w, herm_eq_coords b' w, hb, hb', hπ, hw]
  ring

theorem muSet_eq_of_π_eq (hn : 1 ≤ n) {b b' : Fin (n + 2) → K} (hb : herm frob b b = 0)
    (hb' : herm frob b' b' = 0) (hvb : herm frob (v₀ n) b = 1) (hvb' : herm frob (v₀ n) b' = 1)
    (hπ : π n b = π n b') :
    muSet (DG (n + 2)) (tq (v₀ n)) (tq b) = muSet (DG (n + 2)) (tq (v₀ n)) (tq b') := by
  have hb0 : b ≠ 0 := by rintro rfl; rw [herm_zero_right] at hvb; exact zero_ne_one hvb
  have hb0' : b' ≠ 0 := by rintro rfl; rw [herm_zero_right] at hvb'; exact zero_ne_one hvb'
  have hne : herm frob (v₀ n) b ≠ 0 := by rw [hvb]; exact one_ne_zero
  have hne' : herm frob (v₀ n) b' ≠ 0 := by rw [hvb']; exact one_ne_zero
  ext q
  constructor
  · intro hq
    obtain ⟨w, hw0, hw, rfl⟩ := mem_DG_of_mem_muSet hq
    rw [tq_mem_muSet_iff (by omega) v₀_ne_zero herm_v₀_v₀ hb0 hb hne hw0 hw] at hq
    rw [tq_mem_muSet_iff (by omega) v₀_ne_zero herm_v₀_v₀ hb0' hb' hne' hw0 hw]
    exact ⟨hq.1, by rw [← herm_eq_herm_of_perp hvb hvb' hπ hq.1]; exact hq.2⟩
  · intro hq
    obtain ⟨w, hw0, hw, rfl⟩ := mem_DG_of_mem_muSet hq
    rw [tq_mem_muSet_iff (by omega) v₀_ne_zero herm_v₀_v₀ hb0' hb' hne' hw0 hw] at hq
    rw [tq_mem_muSet_iff (by omega) v₀_ne_zero herm_v₀_v₀ hb0 hb hne hw0 hw]
    exact ⟨hq.1, by rw [herm_eq_herm_of_perp hvb hvb' hπ hq.1]; exact hq.2⟩

@[expose] noncomputable def γ (y : Fin n → K) : K := by
  classical
  exact if herm frob y y = 0 then 0 else ω

theorem γ_trace (y : Fin n → K) : γ y + frob (γ y) = herm frob y y := by
  unfold γ
  split_ifs with h
  · rw [h, map_zero, add_zero]
  · rw [(herm_self_eq_zero_or_one y).resolve_left h, omega_add_frob]

@[expose] noncomputable def uy (y : Fin n → K) : Fin (n + 2) → K :=
  u₀ n + ι n y + γ y • v₀ n

theorem herm_v₀_uy (y : Fin n → K) : herm frob (v₀ n) (uy y) = 1 := by
  rw [uy, herm_add_right, herm_add_right, herm_smul_right, herm_v₀_u₀, herm_v₀_ι, herm_v₀_v₀,
    mul_zero, add_zero, add_zero]

theorem herm_u₀_uy (y : Fin n → K) : herm frob (u₀ n) (uy y) = γ y := by
  rw [uy, herm_add_right, herm_add_right, herm_smul_right, herm_u₀_u₀, herm_u₀_ι, herm_u₀_v₀,
    mul_one, zero_add, zero_add]

theorem π_uy (y : Fin n → K) : π n (uy y) = y := by
  rw [uy, map_add, map_add, map_smul, π_u₀, π_ι, π_v₀, smul_zero, zero_add, add_zero]

theorem herm_uy_uy (y : Fin n → K) : herm frob (uy y) (uy y) = 0 := by
  rw [herm_eq_coords, herm_u₀_uy, herm_v₀_uy, map_one, mul_one, one_mul, π_uy, add_comm (frob _),
    γ_trace, add_self_K]

theorem uy_ne_zero (y : Fin n → K) : uy y ≠ 0 := by
  intro h
  have := herm_v₀_uy y
  rw [h, herm_zero_right] at this
  exact zero_ne_one this

noncomputable abbrev muY (y : Fin n → K) : Set (PG (n + 2)) :=
  muSet (DG (n + 2)) (tq (v₀ n)) (tq (uy y))

theorem tq_uy_not_commute (hn : 1 ≤ n) (y : Fin n → K) :
    tq (uy y) * tq (v₀ n) ≠ tq (v₀ n) * tq (uy y) := fun h => by
  have := (tq_commute_iff (by omega) v₀_ne_zero herm_v₀_v₀ (uy_ne_zero y) (herm_uy_uy y)).1 h.symm
  rw [herm_v₀_uy] at this
  exact one_ne_zero this

theorem muY_mem_muFamily (hn : 1 ≤ n) (y : Fin n → K) :
    muY y ∈ muFamily (DG (n + 2)) (tq (v₀ n)) :=
  muSet_mem_muFamily (tq_mem_DG (uy_ne_zero y) (herm_uy_uy y)) (tq_uy_not_commute hn y)

@[expose] noncomputable def wz (y z : Fin n → K) : Fin (n + 2) → K := herm frob y z • v₀ n + ι n z

theorem π_wz (y z : Fin n → K) : π n (wz y z) = z := by
  rw [wz, map_add, map_smul, π_v₀, smul_zero, zero_add, π_ι]

theorem herm_v₀_wz (y z : Fin n → K) : herm frob (v₀ n) (wz y z) = 0 := by
  rw [wz, herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_ι, mul_zero, add_zero]

theorem herm_u₀_wz (y z : Fin n → K) : herm frob (u₀ n) (wz y z) = herm frob y z := by
  rw [wz, herm_add_right, herm_smul_right, herm_u₀_v₀, herm_u₀_ι, mul_one, add_zero]

theorem herm_uy_wz (y z : Fin n → K) : herm frob (uy y) (wz y z) = 0 := by
  rw [herm_eq_coords, herm_v₀_wz, herm_u₀_wz, herm_v₀_uy, π_uy, π_wz, mul_zero, zero_add,
    map_one, one_mul, add_self_K]

theorem herm_wz_wz (y z : Fin n → K) : herm frob (wz y z) (wz y z) = herm frob z z := by
  rw [herm_eq_coords, herm_v₀_wz, π_wz, mul_zero, map_zero, zero_mul, zero_add, zero_add]

theorem wz_ne_zero (y : Fin n → K) {z : Fin n → K} (hz : z ≠ 0) : wz y z ≠ 0 := fun h =>
  hz (by rw [← π_wz y z, h, map_zero])

theorem tq_wz_mem_muY (hn : 1 ≤ n) (y : Fin n → K) {z : Fin n → K} (hz0 : z ≠ 0)
    (hz : herm frob z z = 0) : tq (wz y z) ∈ muY y :=
  (tq_mem_muSet_iff (by omega) v₀_ne_zero herm_v₀_v₀ (uy_ne_zero y) (herm_uy_uy y)
    (by rw [herm_v₀_uy]; exact one_ne_zero) (wz_ne_zero y hz0)
    (by rw [herm_wz_wz]; exact hz)).2 ⟨herm_v₀_wz y z, herm_uy_wz y z⟩

theorem exists_wz_of_mem_muY (hn : 1 ≤ n) {y : Fin n → K} {q : PG (n + 2)} (hq : q ∈ muY y) :
    ∃ z : Fin n → K, z ≠ 0 ∧ herm frob z z = 0 ∧ q = tq (wz y z) := by
  obtain ⟨w, hw0, hw, rfl⟩ := mem_DG_of_mem_muSet hq
  obtain ⟨h1, h2⟩ := (tq_mem_muSet_iff (by omega) v₀_ne_zero herm_v₀_v₀ (uy_ne_zero y)
    (herm_uy_uy y) (by rw [herm_v₀_uy]; exact one_ne_zero) hw0 hw).1 hq
  have hdec := decomp_of_perp h1
  rw [herm_eq_coords, h1, herm_v₀_uy, π_uy, mul_zero, zero_add, map_one, one_mul] at h2
  have hu : herm frob (u₀ n) w = herm frob y (π n w) := eq_of_add_eq_zero_K h2
  refine ⟨π n w, fun h => hw0 ?_, ?_, ?_⟩
  · rw [hdec, h, map_zero, add_zero, hu, h, herm_zero_right, zero_smul]
  · have := herm_eq_coords w w
    rw [h1, hw, mul_zero, map_zero, zero_mul, zero_add, zero_add] at this
    exact this.symm
  · rw [wz, ← hu, ← hdec]

theorem muY_injective (hn : 2 ≤ n) : Function.Injective (muY (n := n)) := by
  intro y y' h
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_isotropic hn fun z hz => ?_
  by_cases hz0 : z = 0
  · rw [hz0, herm_zero_left]
  have hmem := tq_wz_mem_muY (by omega) y hz0 hz
  rw [h] at hmem
  obtain ⟨z', hz0', hz', he⟩ := exists_wz_of_mem_muY (by omega) hmem
  obtain ⟨c, hc⟩ := (tq_eq_tq_iff (by omega) (wz_ne_zero y' hz0')
    (by rw [herm_wz_wz]; exact hz') (wz_ne_zero y hz0) (by rw [herm_wz_wz]; exact hz)).1 he.symm
  have hπ := congrArg (π n) hc
  rw [π_wz, map_smul, π_wz] at hπ
  have hu := congrArg (herm frob (u₀ n)) hc
  rw [herm_u₀_wz, herm_smul_right, herm_u₀_wz, hπ, herm_smul_right] at hu
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hπ; exact hz0 hπ
  have h1 : herm frob y z' = herm frob y' z' := mul_left_cancel₀ hc0 hu
  rw [herm_sub_right, hπ, herm_smul_left, herm_smul_left, herm_conj frob frob_frob y z', h1,
    ← herm_conj frob frob_frob y' z', sub_self]

theorem exists_muY_eq (hn : 1 ≤ n) {O : Set (PG (n + 2))}
    (hO : O ∈ muFamily (DG (n + 2)) (tq (v₀ n))) : ∃ y : Fin n → K, muY y = O := by
  obtain ⟨c, ⟨b, hb0, hb, rfl⟩, hcd, rfl⟩ := hO
  have hvb : herm frob (v₀ n) b ≠ 0 := fun h =>
    hcd ((tq_commute_iff (by omega) v₀_ne_zero herm_v₀_v₀ hb0 hb).2 h).symm
  set b' := (herm frob (v₀ n) b)⁻¹ • b with hb'
  have hb'b : tq b' = tq b := congrArg QuotientGroup.mk (tvU_smul_vec hb (inv_ne_zero hvb))
  have hvb' : herm frob (v₀ n) b' = 1 := by rw [hb', herm_smul_right, inv_mul_cancel₀ hvb]
  refine ⟨π n b', ?_⟩
  rw [← hb'b]
  exact muSet_eq_of_π_eq hn (herm_uy_uy _) (herm_smul_smul_self hb _) (herm_v₀_uy _) hvb'
    (π_uy _)

theorem image_conj_muY (hn : 2 ≤ n) (y : Fin n → K) (a : K) {x : Fin n → K}
    (hx : herm frob x x = 0) :
    (fun s => tq (a • v₀ n + ι n x) * s * tq (a • v₀ n + ι n x)) '' muY y =
      muY (y + (frob a + herm frob x y) • x) := by
  set w := a • v₀ n + ι n x with hw
  have hww : herm frob w w = 0 := by
    rw [hw, herm_add_self, herm_smul_self_eq, herm_v₀_v₀, herm_ι_ι, hx, herm_smul_left,
      herm_v₀_ι, mul_zero, mul_zero, trace_zero, add_zero, add_zero]
  have hvw : herm frob (v₀ n) w = 0 := by
    rw [hw, herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_ι, mul_zero, add_zero]
  have hwy : herm frob w (uy y) = frob a + herm frob x y := by
    rw [hw, herm_add_left, herm_smul_left, herm_v₀_uy, mul_one, herm_ι_left, π_uy]
  have hinv : (tq w)⁻¹ = tq w := by rw [← QuotientGroup.mk_inv, tvU_inv hww]
  have hcomm : tq w * tq (v₀ n) * (tq w)⁻¹ = tq (v₀ n) := by
    rw [conj_tq _ herm_v₀_v₀, tvU_smul_of_herm_eq_zero hww
      (herm_eq_zero_comm frob frob_frob hvw)]
  have h1 := Pair.image_conj_muSet (pair_DG (m := n + 2) (by omega)) (tq w) (tq (v₀ n))
    (tq (uy y))
  rw [hcomm, hinv, tq_mul_tq_mul_tq hww (herm_uy_uy y)] at h1
  rw [muY, h1]
  have hv1 : herm frob (v₀ n) (tvU w • uy y) = 1 := by
    rw [tvU_smul hww, herm_add_right, herm_smul_right, herm_v₀_uy, hvw, mul_zero, add_zero]
  apply muSet_eq_of_π_eq (by omega) (by rw [herm_smul_smul, herm_uy_uy]) (herm_uy_uy _) hv1
    (herm_v₀_uy _)
  rw [π_uy, tvU_smul hww, map_add, map_smul, π_uy, hwy, hw, map_add, map_smul, π_v₀, smul_zero,
    zero_add, π_ι]

end MuFamily

section Graph

variable {n : ℕ}

theorem muSet_eq_muY (hn : 1 ≤ n) {u : Fin (n + 2) → K} (hu : herm frob u u = 0)
    (hvu : herm frob (v₀ n) u = 1) :
    muSet (DG (n + 2)) (tq (v₀ n)) (tq u) = muY (π n u) :=
  muSet_eq_of_π_eq hn hu (herm_uy_uy _) hvu (herm_v₀_uy _) (π_uy _).symm

theorem isotropic_smul_v₀_add_ι (a : K) {x : Fin n → K} (hx : herm frob x x = 0) :
    herm frob (a • v₀ n + ι n x) (a • v₀ n + ι n x) = 0 := by
  rw [herm_add_self, herm_smul_self_eq, herm_v₀_v₀, herm_ι_ι, hx, herm_smul_left, herm_v₀_ι,
    mul_zero, mul_zero, trace_zero, add_zero, add_zero]

theorem muY_adj_iff (hn : 2 ≤ n) (y y' : Fin n → K) :
    (muGraph (DG (n + 2)) (tq (v₀ n))).Adj ⟨muY y, muY_mem_muFamily (by omega) y⟩
      ⟨muY y', muY_mem_muFamily (by omega) y'⟩ ↔ (cayleyGraph n).Adj y y' := by
  rw [Pair.muGraph_adj (pair_DG (by omega)), cayleyGraph_adj, Ne, Subtype.mk.injEq]
  constructor
  · rintro ⟨hne, f, hf, hfO, hQ⟩
    refine ⟨fun h => hne (by rw [h]), ?_⟩
    rw [localClass_DG (by omega) v₀_ne_zero herm_v₀_v₀] at hf
    obtain ⟨w, hw0, hw, hvw, hwv, rfl⟩ := hf
    have hdec := decomp_of_perp hvw
    have hx : herm frob (π n w) (π n w) = 0 := by
      have := herm_eq_coords w w
      rw [hvw, hw, mul_zero, map_zero, zero_mul, zero_add, zero_add] at this
      exact this.symm
    rw [hdec, image_conj_muY hn y _ hx] at hQ
    rw [← muY_injective hn hQ, add_sub_cancel_left, herm_smul_self_eq, hx, mul_zero]
  · rintro ⟨hyy, hq⟩
    refine ⟨fun h => hyy (muY_injective hn h), ?_⟩
    have hx0 : y' - y ≠ 0 := sub_ne_zero.2 (Ne.symm hyy)
    set a := frob (1 + herm frob (y' - y) y) with ha
    have hlam : frob a + herm frob (y' - y) y = 1 := by
      rw [ha, frob_frob, add_assoc, add_self_K, add_zero]
    have hw := isotropic_smul_v₀_add_ι (n := n) a hq
    have hw0 : a • v₀ n + ι n (y' - y) ≠ 0 := fun h => hx0 (by
      have := congrArg (π n) h
      rwa [map_add, map_smul, π_v₀, smul_zero, zero_add, π_ι, map_zero] at this)
    refine ⟨tq (a • v₀ n + ι n (y' - y)), ?_, fun hmem => ?_, ?_⟩
    · rw [localClass_DG (by omega) v₀_ne_zero herm_v₀_v₀]
      refine ⟨_, hw0, hw, ?_, fun c hc => hx0 ?_, rfl⟩
      · rw [herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_ι, mul_zero, add_zero]
      · have := congrArg (π n) hc
        rwa [map_add, map_smul, map_smul, π_v₀, smul_zero, zero_add, π_ι, smul_zero] at this
    · have h2 := ((tq_mem_muSet_iff (by omega) v₀_ne_zero herm_v₀_v₀ (uy_ne_zero y)
        (herm_uy_uy y) (by rw [herm_v₀_uy]; exact one_ne_zero) hw0 hw).1 hmem).2
      have h3 : herm frob (a • v₀ n + ι n (y' - y)) (uy y) = 1 := by
        rw [herm_add_left, herm_smul_left, herm_v₀_uy, mul_one, herm_ι_left, π_uy, hlam]
      rw [herm_eq_zero_comm frob frob_frob h2] at h3
      exact zero_ne_one h3
    · rw [image_conj_muY hn y a hq, hlam, one_smul, add_sub_cancel]

@[expose] noncomputable def muGraphIsoCayley (hn : 2 ≤ n) :
    cayleyGraph n ≃g muGraph (DG (n + 2)) (tq (v₀ n)) where
  toEquiv := Equiv.ofBijective (fun y => ⟨muY y, muY_mem_muFamily (by omega) y⟩)
    ⟨fun y y' h => muY_injective hn (congrArg Subtype.val h), fun O => by
      obtain ⟨y, hy⟩ := exists_muY_eq (by omega) O.2
      exact ⟨y, Subtype.ext hy⟩⟩
  map_rel_iff' := muY_adj_iff hn _ _

noncomputable def muGraphIsoCayleyU (hn : 2 ≤ n) :
    cayleyGraph n ≃g muGraph (DU (n + 2)) (tqU (v₀ n)) :=
  (muGraphIsoCayley hn).trans
    (muGraphCongr (u2Equiv (n + 2)).symm (symm_image_eq _ (image_DU _)) _)

end Graph

end CFSG.Fischer.Classification.Unitary

namespace CFSG.Fischer.Classification

open CFSG.Fischer.Classification.Unitary

theorem tripleProperty_DU {m : ℕ} (hm : 4 ≤ m) : TripleProperty (Unitary.DU m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact (tripleProperty_congr (u2Equiv (n + 2)) (image_DU (n + 2))).2
    (tripleProperty_DG (by omega))

theorem coverRigid_DU {m : ℕ} (hm : 4 ≤ m) {d : Unitary.U2 m} (hd : d ∈ Unitary.DU m) :
    ∃ r : muFamily (Unitary.DU m) d, CoverRigid (muGraph (Unitary.DU m) d) r := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hn : 2 ≤ n := by omega
  exact coverRigid_of_mem (pair_DU hm) (tqU_mem_DU v₀_ne_zero herm_v₀_v₀) hd
    ((coverRigid_cayleyGraph hn).map (muGraphIsoCayleyU hn))

end CFSG.Fischer.Classification
