module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T0

public section

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25T

open CFSG.ClassicalInvolution.Q3.AE Wr

theorem aeNC4_iQ_mul_self : iQ * iQ = zQ := by decide +kernel

theorem aeNC4_d₁_symm_apply : ∀ i : Fin 4, d₁.symm i = d₁ i := by decide +kernel

theorem aeNC4_comm_embed_iQ_zOf {n : ℕ} (ι κ : Fin 4 ↪ Fin n)
    (h : ∀ i : Fin 4, ι i ∈ Set.range κ ↔ ι (d₁ i) ∈ Set.range κ) :
    embed ι iQ * zOf κ = zOf κ * embed ι iQ := by
  classical
  have key : ∀ x : Fin n, (zOf κ).vec ((embed ι iQ).perm.symm x) = (zOf κ).vec x := by
    intro x
    rw [embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      show (zOf κ).vec ((embedPerm ι d₁).symm (ι i)) = (zOf κ).vec (ι i)
      rw [embedPerm_symm_apply, aeNC4_d₁_symm_apply, zOf_vec_apply, zOf_vec_apply]
      simp only [h i]
    · show (zOf κ).vec ((embedPerm ι d₁).symm x) = (zOf κ).vec x
      rw [embedPerm_symm_of_not_mem ι _ hx]
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [mul_vec, mul_vec, zOf_perm, key x]
    exact add_comm _ _
  · rw [mul_perm, mul_perm, zOf_perm, mul_one, one_mul]

theorem aeNC4_exists_y {n : ℕ} (α β : Finset (Fin n)) (hα : α.card = 4) (hβ : β.card = 4)
    (f : Fin 4 → Fin n) (hf : ∀ i, f i ∈ α) (hm : StrictMono f)
    (hc : ∀ i : Fin 4, f i ∈ β ↔ f (d₁ i) ∈ β) :
    ∃ y : AEQ n, y ∈ memBar α hα true ∧ y * y = zBar α hα ∧
      y * zBar β hβ = zBar β hβ * y := by
  have hι : ∀ i, emb α hα i = f i := fun i =>
    (congrFun (Finset.orderEmbOfFin_unique hα hf hm) i).symm
  have hcomm : embed (emb α hα) iQ * zOf (emb β hβ) = zOf (emb β hβ) * embed (emb α hα) iQ := by
    refine aeNC4_comm_embed_iQ_zOf _ _ fun i => ?_
    rw [range_emb, hι, hι]
    exact hc i
  refine ⟨mkQ n (embed (emb α hα) iQ), ⟨_, ⟨iQ, (by decide +kernel : iQ ∈ kList), rfl⟩, rfl⟩,
    ?_, ?_⟩
  · show mkQ n (embed _ iQ) * mkQ n (embed _ iQ) = mkQ n (embed _ zQ)
    rw [← map_mul, ← map_mul, aeNC4_iQ_mul_self]
  · show mkQ n (embed _ iQ) * mkQ n (zOf _) = mkQ n (zOf _) * mkQ n (embed _ iQ)
    rw [← map_mul, ← map_mul, hcomm]

theorem aeNC4_of_pair {n : ℕ} {𝒜 : Set (Finset (Fin n))} (α β : Finset (Fin n))
    (hα : α.card = 4) (hβ : β.card = 4) (hαA : α ∈ 𝒜) (hβA : β ∈ 𝒜) (hne : α ≠ β)
    (f : Fin 4 → Fin n) (hf : ∀ i, f i ∈ α) (hm : StrictMono f)
    (hc : ∀ i : Fin 4, f i ∈ β ↔ f (d₁ i) ∈ β) : AENC4 n 𝒜 := by
  obtain ⟨y, hy1, hy2, hy3⟩ := aeNC4_exists_y α β hα hβ f hf hm hc
  unfold AENC4
  exact ⟨α, β, hα, hβ, hαA, hβA, hne, true, y, hy1, hy2, hy3⟩

theorem aeNC4_six : AENC4 6 Set.univ :=
  aeNC4_of_pair {0, 1, 2, 3} {0, 1, 4, 5} (by decide) (by decide) trivial trivial (by decide)
    ![0, 1, 2, 3] (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide)

theorem aeNC4_seven : AENC4 7 Set.univ :=
  aeNC4_of_pair {0, 1, 2, 3} {0, 1, 4, 5} (by decide) (by decide) trivial trivial (by decide)
    ![0, 1, 2, 3] (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide)

theorem aeNC4_e64 : AENC4 7 e64Sets :=
  aeNC4_of_pair ({0, 1, 3} : Finset (Fin 7))ᶜ ({1, 2, 4} : Finset (Fin 7))ᶜ (by decide) (by decide)
    ⟨{0, 1, 3}, by decide, rfl⟩ ⟨{1, 2, 4}, by decide, rfl⟩ (by decide)
    ![2, 4, 5, 6] (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide)

end CFSG.ClassicalInvolution.Q8P.Asc77.P25T
