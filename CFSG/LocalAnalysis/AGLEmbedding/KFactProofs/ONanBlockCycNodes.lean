module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

section Nodes

variable {K : Type*} [Group K] (D : UniversalRootDatum K)

@[expose] def HasOrderThreeNC (i : Fin D.rank) : Prop :=
  ∃ x ∈ D.rootGroup (Pi.single i 1), ∃ y ∈ D.rootGroup (-Pi.single i 1),
    (x * y) ^ 3 = 1 ∧ x * (x * y) ≠ (x * y) * x

variable {D}

theorem _root_.CFSG.AGLEmbedding.ParabHub.HasSL2Node.hasOrderThreeNC {i : Fin D.rank}
    {F : Type*} [Field F] [CharP F 2] (h : HasSL2Node D i F) : HasOrderThreeNC D i := by
  obtain ⟨φ, hφ, hx, hy⟩ := h
  refine ⟨φ (sl2Upper 1), hx 1, φ (sl2Lower 1), hy 1, ?_, fun hc => ?_⟩
  · rw [← map_mul, ← map_pow, sl2_upper_lower_cube, map_one]
  · refine sl2_upper_lower_not_commute (F := F) (hφ ?_)
    simpa [map_mul] using hc.symm

end Nodes

section Pairs

variable {K Y : Type*} [Group K] [Group Y]

theorem hasE9_of_commuting_orders (π : K →* Y) (hcen : ∀ z ∈ π.ker, z ∈ Subgroup.center K)
    {a₁ a₂ b₁ b₂ : K} (h₁ : a₁ ^ 3 = 1) (h₂ : a₂ ^ 3 = 1) (hcomm : a₁ * a₂ = a₂ * a₁)
    (hb : Commute b₂ a₁) (hb₂ : ¬ Commute b₂ a₂) (hb₁ : ¬ Commute b₁ a₁) : HasE9 Y := by
  have hgen : ∀ (a x : K), a ^ 3 = 1 → ∀ k : ℕ, 0 < k → k < 3 → Commute x (a ^ k) →
      Commute x a := by
    intro a x ha k hk0 hk3 hx
    interval_cases k
    · simpa using hx
    · have : a = (a ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ha, one_mul]
      rw [this]
      exact hx.pow_right 2
  refine hasE9_of_two_elements (e₁ := π a₁) (e₂ := π a₂) ?_ ?_ ?_ ?_
  · show π a₁ * π a₂ = π a₂ * π a₁
    rw [← map_mul, ← map_mul, hcomm]
  · rw [← map_pow, h₁, map_one]
  · rw [← map_pow, h₂, map_one]
  · intro s t hs ht hst
    have hker : a₁ ^ s * a₂ ^ t ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow]
      exact hst
    have hz := Subgroup.mem_center_iff.1 (hcen _ hker)
    have ht0 : t = 0 := by
      by_contra ht0
      have hc1 : Commute b₂ (a₁ ^ s) := hb.pow_right s
      have hc2 : Commute b₂ (a₁ ^ s * a₂ ^ t) := hz b₂
      have hxjt : Commute b₂ (a₂ ^ t) := by
        have : a₂ ^ t = (a₁ ^ s)⁻¹ * (a₁ ^ s * a₂ ^ t) := by group
        rw [this]
        exact hc1.inv_right.mul_right hc2
      exact hb₂ (hgen a₂ b₂ h₂ t (Nat.pos_of_ne_zero ht0) ht hxjt)
    subst ht0
    have hs0 : s = 0 := by
      by_contra hs0
      have hc2 : Commute b₁ (a₁ ^ s) := by
        have := hz b₁
        rw [pow_zero, mul_one] at this
        exact this
      exact hb₁ (hgen a₁ b₁ h₁ s (Nat.pos_of_ne_zero hs0) hs hc2)
    exact ⟨hs0, rfl⟩

end Pairs

section Quotient

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.hasE9_of_nodes
    (h : BorelQuotient D n H π M) {i j : Fin D.rank} (hc : D.cartan i j = 0) (hij : i ≠ j)
    (hi : HasOrderThree D i) (hj : HasOrderThreeNC D j) : HasE9 Y := by
  obtain ⟨xi, hxi, yi, hyi, hi3, ci, hinc⟩ := hi
  obtain ⟨xj, hxj, yj, hyj, hj3, hjnc⟩ := hj
  have hcomm := commutes_rankOne_of_cartan_eq_zero h.extras hij hc
  have hXi : xi ∈ rankOne D.rootGroup i := Subgroup.mem_sup_left hxi
  have hYi : yi ∈ rankOne D.rootGroup i := Subgroup.mem_sup_right hyi
  have hXj : xj ∈ rankOne D.rootGroup j := Subgroup.mem_sup_left hxj
  have hYj : yj ∈ rankOne D.rootGroup j := Subgroup.mem_sup_right hyj
  have hAi : xi * yi ∈ rankOne D.rootGroup i := Subgroup.mul_mem _ hXi hYi
  have hAj : xj * yj ∈ rankOne D.rootGroup j := Subgroup.mul_mem _ hXj hYj
  exact hasE9_of_commuting_orders π h.ker_central (a₁ := xi * yi) (a₂ := xj * yj) (b₁ := ci)
    (b₂ := xj) hi3 hj3 (hcomm _ hAi _ hAj) (hcomm _ hAi _ hXj).symm hjnc (fun hc' => hinc hc'.symm)

end Quotient

section Overgroups

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.exists_two_nodes
    (h : BorelQuotient D n H π M) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hJtop : J ≠ ⊤) :
    ∃ i j : Fin D.rank, i ≠ j := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hBJ' : borel D H ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hne : J.comap π' ≠ borel D H := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := negIndices_nonempty_of_ne hQ.ct hQ.extras hBJ' hne
  obtain ⟨j, hj⟩ := exists_node_not_mem_negIndices hQ hBJ hJtop
  exact ⟨i, j, fun e => hj (e ▸ hi)⟩

end Overgroups

end CFSG.AGLEmbedding.BlockCyc
