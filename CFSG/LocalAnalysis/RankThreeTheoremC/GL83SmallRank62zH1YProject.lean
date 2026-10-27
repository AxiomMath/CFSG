module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1YLayer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.AGLEmbedding CFSG.LocalCores
open scoped commutatorElement

variable {B : Type} [Group B] [Finite B] {f : ℕ} {Q : Subgroup B}

@[expose] def k631aProj (Y₂ J : Subgroup B) : Subgroup B where
  carrier := {j | j ∈ J ∧ ∃ y ∈ Y₂, ∀ k ∈ J, y * k * y⁻¹ = j * k * j⁻¹}
  one_mem' := ⟨J.one_mem, 1, Y₂.one_mem, fun k _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haJ, y₁, hy₁, h₁⟩ ⟨hbJ, y₂, hy₂, h₂⟩
    refine ⟨J.mul_mem haJ hbJ, y₁ * y₂, Y₂.mul_mem hy₁ hy₂, fun k hk => ?_⟩
    have hb : b * k * b⁻¹ ∈ J := J.mul_mem (J.mul_mem hbJ hk) (J.inv_mem hbJ)
    calc y₁ * y₂ * k * (y₁ * y₂)⁻¹ = y₁ * (y₂ * k * y₂⁻¹) * y₁⁻¹ := by group
      _ = y₁ * (b * k * b⁻¹) * y₁⁻¹ := by rw [h₂ k hk]
      _ = a * (b * k * b⁻¹) * a⁻¹ := h₁ _ hb
      _ = (a * b) * k * (a * b)⁻¹ := by group
  inv_mem' := by
    rintro a ⟨haJ, y, hy, h⟩
    refine ⟨J.inv_mem haJ, y⁻¹, Y₂.inv_mem hy, fun k hk => ?_⟩
    have hk' : a⁻¹ * k * a ∈ J := J.mul_mem (J.mul_mem (J.inv_mem haJ) hk) haJ
    have h1 : y * (a⁻¹ * k * a) * y⁻¹ = k := by
      rw [h _ hk']
      group
    calc y⁻¹ * k * y⁻¹⁻¹ = y⁻¹ * (y * (a⁻¹ * k * a) * y⁻¹) * y⁻¹⁻¹ := by rw [h1]
      _ = a⁻¹ * k * a⁻¹⁻¹ := by group

omit [Finite B] in
theorem k631a_proj_le (Y₂ J : Subgroup B) : k631aProj Y₂ J ≤ J := fun _ hj => hj.1

theorem k631a_proj_pgroup (h : k631aBHyp f Q) {Y₂ J : Subgroup B} (hJ : IsComponent J)
    (hY2 : IsPGroup 2 Y₂) : IsPGroup 2 (k631aProj Y₂ J) := by
  rintro ⟨j, hjJ, y, hy, hyj⟩
  obtain ⟨m, hm⟩ := hY2 ⟨y, hy⟩
  refine ⟨m, ?_⟩
  have hym : y ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have key : ∀ n : ℕ, ∀ k ∈ J, y ^ n * k * (y ^ n)⁻¹ = j ^ n * k * (j ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro k _; simp
    | succ n ih =>
      intro k hk
      have hk' : j ^ n * k * (j ^ n)⁻¹ ∈ J :=
        J.mul_mem (J.mul_mem (J.pow_mem hjJ n) hk) (J.inv_mem (J.pow_mem hjJ n))
      calc y ^ (n + 1) * k * (y ^ (n + 1))⁻¹ = y * (y ^ n * k * (y ^ n)⁻¹) * y⁻¹ := by group
        _ = y * (j ^ n * k * (j ^ n)⁻¹) * y⁻¹ := by rw [ih k hk]
        _ = j * (j ^ n * k * (j ^ n)⁻¹) * j⁻¹ := hyj _ hk'
        _ = j ^ (n + 1) * k * (j ^ (n + 1))⁻¹ := by group
  have hjn : j ^ 2 ^ m = 1 := by
    refine k631a_eq_one_of_central h hJ (J.pow_mem hjJ _) fun k hk => ?_
    have h1 := key (2 ^ m) k hk
    rw [hym] at h1
    have h2 : j ^ 2 ^ m * k * (j ^ 2 ^ m)⁻¹ = k := by simpa using h1.symm
    calc j ^ 2 ^ m * k = (j ^ 2 ^ m * k * (j ^ 2 ^ m)⁻¹) * j ^ 2 ^ m := by group
      _ = k * j ^ 2 ^ m := by rw [h2]
  exact Subtype.ext (by simpa using hjn)

omit [Finite B] in
theorem k631a_proj_conj {Y₂ J : Subgroup B} {v : B} (hvY : v ∈ normalizer (Y₂ : Set B))
    (hvJ : v ∈ normalizer (J : Set B)) {x : B} (hx : x ∈ k631aProj Y₂ J) :
    v * x * v⁻¹ ∈ k631aProj Y₂ J := by
  obtain ⟨hxJ, y, hy, hyx⟩ := hx
  refine ⟨(mem_normalizer_iff.mp hvJ x).mp hxJ, v * y * v⁻¹,
    (mem_normalizer_iff.mp hvY y).mp hy, fun k hk => ?_⟩
  have hk' : v⁻¹ * k * v ∈ J := by
    have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hvJ) k).mp hk
    simpa using this
  have h1 := hyx _ hk'
  calc v * y * v⁻¹ * k * (v * y * v⁻¹)⁻¹ = v * (y * (v⁻¹ * k * v) * y⁻¹) * v⁻¹ := by group
    _ = v * (x * (v⁻¹ * k * v) * x⁻¹) * v⁻¹ := by rw [h1]
    _ = (v * x * v⁻¹) * k * (v * x * v⁻¹)⁻¹ := by group

theorem k631a_project_Y (hInn : KFactInnerAction) (h : k631aBHyp f Q) {Y₂ V : Subgroup B}
    (hY2 : IsPGroup 2 Y₂) (hY1 : Y₂ ≠ ⊥) (hVQ : V ≤ Q) (hVY : V ≤ normalizer (Y₂ : Set B))
    (hYV : ⁅Y₂, V⁆ = Y₂) :
    ∃ J : Subgroup B, IsComponent J ∧ ∃ T : Subgroup B, T ≤ J ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      ∃ s ∈ Q ⊓ J, s ≠ 1 ∧ s ∈ normalizer (T : Set B) := by
  have hL := k631a_layer_le hInn h hY2 hVQ hYV
  have hZ : ∀ K : ComponentIndex B, Subgroup.center ↥K.1 = ⊥ := fun K => k631a_center_bot h K.2
  have hex : ∃ K : ComponentIndex B, ∃ v ∈ V, ∃ t ∈ k631aProj Y₂ K.1, v * t ≠ t * v := by
    by_contra hno
    push Not at hno
    apply hY1
    have hcent : ∀ y ∈ Y₂, ∀ v ∈ V, v * y * v⁻¹ = y := by
      intro y hy v hv
      have hyl := hL hy
      have hy'Y : v * y * v⁻¹ ∈ Y₂ := (mem_normalizer_iff.mp (hVY hv) y).mp hy
      have hy'l := hL hy'Y
      have hc : ∀ K : ComponentIndex B, ∀ k ∈ K.1,
          (y⁻¹ * (v * y * v⁻¹)) * k = k * (y⁻¹ * (v * y * v⁻¹)) := by
        intro K k hk
        obtain ⟨j, hjK, hj⟩ := k631a_layer_acts hyl K
        have hjT : j ∈ k631aProj Y₂ K.1 := ⟨hjK, y, hy, hj⟩
        have hvn : v ∈ normalizer (K.1 : Set B) := k631a_normalizes h K.2 (hVQ hv)
        have hvk : v⁻¹ * k * v ∈ K.1 := by
          have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hvn) k).mp hk
          simpa using this
        have hvj : v * j * v⁻¹ = j := by
          rw [hno K v hv j hjT]
          group
        have e1 : (v * y * v⁻¹) * k * (v * y * v⁻¹)⁻¹ = y * k * y⁻¹ := by
          calc (v * y * v⁻¹) * k * (v * y * v⁻¹)⁻¹
              = v * (y * (v⁻¹ * k * v) * y⁻¹) * v⁻¹ := by group
            _ = v * (j * (v⁻¹ * k * v) * j⁻¹) * v⁻¹ := by rw [hj _ hvk]
            _ = (v * j * v⁻¹) * k * (v * j * v⁻¹)⁻¹ := by group
            _ = j * k * j⁻¹ := by rw [hvj]
            _ = y * k * y⁻¹ := (hj k hk).symm
        calc y⁻¹ * (v * y * v⁻¹) * k
            = y⁻¹ * ((v * y * v⁻¹) * k * (v * y * v⁻¹)⁻¹) * (v * y * v⁻¹) := by group
          _ = y⁻¹ * (y * k * y⁻¹) * (v * y * v⁻¹) := by rw [e1]
          _ = k * (y⁻¹ * (v * y * v⁻¹)) := by group
      have hcl : y⁻¹ * (v * y * v⁻¹) ∈ layer B :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hyl) hy'l
      have h1 := k631a_layer_eq_one hZ hcl hc
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    rw [← hYV, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 := hcent y hy v hv
    calc v * y = (v * y * v⁻¹) * v := by group
      _ = y * v := by rw [h1]
  obtain ⟨K, v, hv, t, ht, hvt⟩ := hex
  have hJ := K.2
  have hvQ := hVQ hv
  obtain ⟨s, hsQJ, hs⟩ := k631a_inner hInn h hJ hvQ
  refine ⟨K.1, hJ, k631aProj Y₂ K.1, k631a_proj_le _ _, ?_, k631a_proj_pgroup h hJ hY2, s, hsQJ,
    ?_, ?_⟩
  · intro hbot
    have ht1 : t = 1 := by
      rw [hbot] at ht
      exact ht
    subst ht1
    exact hvt (by simp)
  · intro hs1
    rw [hs1] at hs
    apply hvt
    have h1 := hs t ht.1
    calc v * t = (v * t * v⁻¹) * v := by group
      _ = t * v := by rw [h1]; group
  · rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hs x hx.1]
      exact k631a_proj_conj (hVY hv) (k631a_normalizes h hJ hvQ) hx
    · intro hx
      have hsJ : s ∈ K.1 := hsQJ.2
      have hxJ : x ∈ K.1 := by
        have e : x = s⁻¹ * (s * x * s⁻¹) * s := by group
        rw [e]
        exact K.1.mul_mem (K.1.mul_mem (K.1.inv_mem hsJ) hx.1) hsJ
      rw [← hs x hxJ] at hx
      have := k631a_proj_conj (hVY (V.inv_mem hv))
        (Subgroup.inv_mem _ (k631a_normalizes h hJ hvQ)) hx
      simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC
