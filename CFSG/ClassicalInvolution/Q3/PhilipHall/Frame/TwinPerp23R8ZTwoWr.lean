module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Cent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Perm

theorem perm_eq_one_of_centralizes (w : Wr 6)
    (h : ∀ x ∈ TwinThinPf8.Hn 6, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x) : w.perm = 1 := by
  have key : ∀ (α : Finset (Fin 6)) (hα : α.card = 4), ∀ x ∈ α, w.perm x = x := by
    intro α hα x hx
    obtain ⟨c, e, hw, he, hc⟩ := TwinThinPf10.exists_split (by norm_num) (by norm_num) α hα w
      (fun b x hx => h x (TwinThinPf8.memBar_le_Hn α hα b hx))
    have hxs : x ∉ (Set.range (emb α hα))ᶜ := by
      rw [Set.mem_compl_iff, not_not, range_emb]
      exact hx
    have h1 : w.perm = c.perm := by
      rw [hw, mul_perm]
      rcases he with rfl | rfl
      · rw [one_perm, mul_one]
      · rw [zOf_perm, mul_one]
    rw [h1]
    exact (hc x hxs).2
  have h1 := key {0, 1, 2, 3} (by decide)
  have h2 := key {2, 3, 4, 5} (by decide)
  refine Equiv.ext fun x => ?_
  have hcov : ∀ x : Fin 6, x ∈ ({0, 1, 2, 3} : Finset (Fin 6)) ∨ x ∈ ({2, 3, 4, 5} : Finset (Fin 6)) := by
    decide
  show w.perm x = x
  rcases hcov x with hx | hx
  · exact h1 x hx
  · exact h2 x hx

theorem perm_dichotomy {β : Finset (Fin 6)} {a b : Fin 6} (hab : a ≠ b) (ha : a ∉ β) (hb : b ∉ β)
    (hout : ∀ i, i ∉ β → i = a ∨ i = b) (σ : Equiv.Perm (Fin 6)) (hσ : ∀ x ∈ β, σ x = x) :
    σ = 1 ∨ σ = Equiv.swap a b := by
  have hfix : ∀ x, x ∉ β → σ x ∉ β := by
    intro x hx hσx
    apply hx
    have h1 := hσ _ hσx
    have : σ x = x := σ.injective h1
    rw [← this]
    exact hσx
  have hσa := hout _ (hfix a ha)
  have hσb := hout _ (hfix b hb)
  rcases hσa with hσa | hσa
  · left
    have hσb' : σ b = b := by
      rcases hσb with h | h
      · exact absurd (σ.injective (h.trans hσa.symm)) (Ne.symm hab)
      · exact h
    refine Equiv.ext fun x => ?_
    show σ x = x
    by_cases hx : x ∈ β
    · exact hσ x hx
    · rcases hout x hx with rfl | rfl
      · exact hσa
      · exact hσb'
  · right
    have hσb' : σ b = a := by
      rcases hσb with h | h
      · exact h
      · exact absurd (σ.injective (hσa.trans h.symm)) hab
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ β
    · have hxa : x ≠ a := fun h => ha (h ▸ hx)
      have hxb : x ≠ b := fun h => hb (h ▸ hx)
      rw [hσ x hx, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    · rcases hout x hx with rfl | rfl
      · rw [hσa, Equiv.swap_apply_left]
      · rw [hσb', Equiv.swap_apply_right]

theorem exists_compl_pair {β : Finset (Fin 6)} (hβ : β.card = 4) :
    ∃ a b : Fin 6, a ≠ b ∧ a ∉ β ∧ b ∉ β ∧ ∀ i, i ∉ β → i = a ∨ i = b := by
  have hc : βᶜ.card = 2 := by
    rw [Finset.card_compl, hβ]
    rfl
  obtain ⟨a, b, hab, hba⟩ := Finset.card_eq_two.mp hc
  refine ⟨a, b, hab, ?_, ?_, ?_⟩
  · have : a ∈ βᶜ := by rw [hba]; simp
    simpa using this
  · have : b ∈ βᶜ := by rw [hba]; simp
    simpa using this
  · intro i hi
    have : i ∈ βᶜ := by simpa using hi
    rw [hba] at this
    simpa using this

end Perm

section Vec

theorem ofVec_comm_of_const {n : ℕ} (x : Fin n → ZMod 2) (a : Wr n) (s : Set (Fin n))
    (ha : SupportedOn a s) (hx : ∀ i ∈ s, ∀ j ∈ s, x i = x j) : ofVec x * a = a * ofVec x := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, mul_vec]
    show x i + a.vec ((1 : Equiv.Perm (Fin n)).symm i) = a.vec i + x (a.perm.symm i)
    have hx' : x i = x (a.perm.symm i) := by
      by_cases hi : i ∈ s
      · exact hx i hi _ (ha.perm_mem hi)
      · rw [ha.perm_symm hi]
    rw [hx', add_comm]
    rfl
  · show 1 * a.perm = a.perm * 1
    rw [one_mul, mul_one]

theorem mkQ_eq_one_of_const {n : ℕ} (w : Wr n) (hp : w.perm = 1) (k : ZMod 2)
    (hv : ∀ i, w.vec i = k) : mkQ n w = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_piSub]
  have hk : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide
  rcases hk k with rfl | rfl
  · left
    exact Wr.ext (funext hv) hp
  · right
    exact Wr.ext (funext hv) hp

theorem zOf_comm_sq_eq_one {n : ℕ} (ι : Fin 4 ↪ Fin n) (a : Wr n) :
    (zOf ι * a * (zOf ι)⁻¹ * a⁻¹) * (zOf ι * a * (zOf ι)⁻¹ * a⁻¹) = 1 := by
  have hz : zOf ι ∈ vecSub n := zOf_perm ι
  have hz' : (zOf ι)⁻¹ ∈ vecSub n := (vecSub n).inv_mem hz
  have h1 : a * (zOf ι)⁻¹ * a⁻¹ ∈ vecSub n := vecSub_normal.conj_mem _ hz' a
  have h2 : zOf ι * a * (zOf ι)⁻¹ * a⁻¹ ∈ vecSub n := by
    have := (vecSub n).mul_mem hz h1
    simpa [mul_assoc] using this
  exact vecSub_mul_self h2

end Vec

section Classify

theorem classify {β : Finset (Fin 6)} (hβ : β.card = 4) (w : Wr 6)
    (h : ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x) :
    Equiv.Perm.sign w.perm = -1 ∨ mkQ 6 w = 1 ∨
      ∃ c₀ : Fin 6, c₀ ∉ β ∧ ∀ (γ : Finset (Fin 6)) (hγ : γ.card = 4), c₀ ∉ γ → ∀ b : Bool,
        ∀ x ∈ memBar γ hγ b,
          mkQ 6 (w * zOf (emb β hβ)) * x * (mkQ 6 (w * zOf (emb β hβ)))⁻¹ = x := by
  obtain ⟨c, e, hw, he, hc⟩ := TwinThinPf10.exists_split (by norm_num) (by norm_num) β hβ w h
  obtain ⟨a, b, hab, ha, hb, hout⟩ := exists_compl_pair hβ
  have hrange : Set.range (emb β hβ) = (β : Set (Fin 6)) := range_emb β hβ
  have hcβ : ∀ x ∈ β, c.vec x = 0 ∧ c.perm x = x := by
    intro x hx
    apply hc
    rw [hrange]
    simpa using hx
  have hcpb : ∀ x ∈ β, c.perm x = x := fun x hx => (hcβ x hx).2
  have hwperm : w.perm = c.perm := by
    rw [hw, mul_perm]
    rcases he with rfl | rfl
    · rw [one_perm, mul_one]
    · rw [zOf_perm, mul_one]
  rcases perm_dichotomy hab ha hb hout c.perm hcpb with hone | hswap
  swap
  · left
    rw [hwperm, hswap, Equiv.Perm.sign_swap hab]
  right
  set z := zOf (emb β hβ) with hzdef
  have hzon : ∀ i ∈ β, z.vec i = 1 := by
    intro i hi
    rw [hzdef, zOf_vec_apply, if_pos]
    rw [hrange]
    exact hi
  have hzoff : ∀ i, i ∉ β → z.vec i = 0 := by
    intro i hi
    rw [hzdef, zOf_vec_apply, if_neg]
    rw [hrange]
    exact hi
  have hwzperm : (w * z).perm = 1 := by
    rw [mul_perm, hwperm, hone, zOf_perm, mul_one]
  have hwperm1 : w.perm = 1 := hwperm.trans hone
  have hwvec : ∀ i, w.vec i = c.vec i + e.vec i := by
    intro i
    rw [hw, mul_vec, hone]
    rfl
  have hwzvec : ∀ i, (w * z).vec i = w.vec i + z.vec i := by
    intro i
    rw [mul_vec, hwperm1]
    rfl
  have hzz : ∀ i, z.vec i + z.vec i = 0 := fun i => zmod_two_add_self _
  have hcvβ : ∀ i ∈ β, c.vec i = 0 := fun i hi => (hcβ i hi).1
  have final : ∀ c₀ : Fin 6, c₀ ∉ β → (∀ i j, i ≠ c₀ → j ≠ c₀ → (w * z).vec i = (w * z).vec j) →
      ∃ c₀ : Fin 6, c₀ ∉ β ∧ ∀ (γ : Finset (Fin 6)) (hγ : γ.card = 4), c₀ ∉ γ → ∀ b : Bool,
        ∀ x ∈ memBar γ hγ b, mkQ 6 (w * z) * x * (mkQ 6 (w * z))⁻¹ = x := by
    intro c₀ hc₀ hconst
    refine ⟨c₀, hc₀, fun γ hγ hc₀γ b x hx => ?_⟩
    obtain ⟨a', ha', rfl⟩ := hx
    have hcomm : (w * z) * a' = a' * (w * z) := by
      have hwz : w * z = ofVec (w * z).vec := Wr.ext rfl hwzperm
      rw [hwz]
      refine ofVec_comm_of_const _ a' (Set.range (emb γ hγ)) (supportedOn_of_mem_memAt ha') ?_
      intro i hi j hj
      rw [range_emb] at hi hj
      refine hconst i j ?_ ?_
      · rintro rfl; exact hc₀γ hi
      · rintro rfl; exact hc₀γ hj
    calc mkQ 6 (w * z) * mkQ 6 a' * (mkQ 6 (w * z))⁻¹
        = mkQ 6 ((w * z) * a') * (mkQ 6 (w * z))⁻¹ := by rw [map_mul (mkQ 6) (w * z) a']
      _ = mkQ 6 (a' * (w * z)) * (mkQ 6 (w * z))⁻¹ := by rw [hcomm]
      _ = mkQ 6 a' := by rw [map_mul (mkQ 6) a' (w * z), mul_assoc, mul_inv_cancel, mul_one]
  have off_b : ∀ (f : Fin 6 → ZMod 2) (k : ZMod 2), (∀ i ∈ β, f i = k) → f a = k →
      ∀ i j, i ≠ b → j ≠ b → f i = f j := by
    intro f k hβk hak
    have hall : ∀ i, i ≠ b → f i = k := by
      intro i hi
      by_cases hiβ : i ∈ β
      · exact hβk i hiβ
      · rcases hout i hiβ with rfl | rfl
        · exact hak
        · exact absurd rfl hi
    intro i j hi hj
    rw [hall i hi, hall j hj]
  have off_a : ∀ (f : Fin 6 → ZMod 2) (k : ZMod 2), (∀ i ∈ β, f i = k) → f b = k →
      ∀ i j, i ≠ a → j ≠ a → f i = f j := by
    intro f k hβk hbk
    have hall : ∀ i, i ≠ a → f i = k := by
      intro i hi
      by_cases hiβ : i ∈ β
      · exact hβk i hiβ
      · rcases hout i hiβ with rfl | rfl
        · exact absurd rfl hi
        · exact hbk
    intro i j hi hj
    rw [hall i hi, hall j hj]
  have two : ∀ k : ZMod 2, k ≠ 0 → k = 1 := by
    intro k hk
    revert k
    decide
  have two' : ∀ k : ZMod 2, k ≠ 1 → k = 0 := by
    intro k hk
    revert k
    decide
  rcases he with he | he
  ·
    have hwe : ∀ i, w.vec i = c.vec i := by
      intro i
      rw [hwvec, he, one_vec, Pi.zero_apply, add_zero]
    by_cases hva : c.vec a = 0 ∧ c.vec b = 0
    · left
      refine mkQ_eq_one_of_const w hwperm1 0 fun i => ?_
      rw [hwe]
      by_cases hiβ : i ∈ β
      · exact hcvβ i hiβ
      · rcases hout i hiβ with rfl | rfl
        · exact hva.1
        · exact hva.2
    · right
      have hwz : ∀ i, (w * z).vec i = c.vec i + z.vec i := by
        intro i
        rw [hwzvec, hwe]
      by_cases hca : c.vec a = 0
      · have hcb : c.vec b = 1 := two _ fun h => hva ⟨hca, h⟩
        refine final a ha (off_a _ 1 (fun i hi => ?_) ?_)
        · rw [hwz, hcvβ i hi, hzon i hi, zero_add]
        · rw [hwz, hcb, hzoff b hb, add_zero]
      · have hca1 : c.vec a = 1 := two _ hca
        refine final b hb (off_b _ 1 (fun i hi => ?_) ?_)
        · rw [hwz, hcvβ i hi, hzon i hi, zero_add]
        · rw [hwz, hca1, hzoff a ha, add_zero]
  ·
    have hwe : ∀ i, w.vec i = c.vec i + z.vec i := by
      intro i
      rw [hwvec, he]
    have hwz : ∀ i, (w * z).vec i = c.vec i := by
      intro i
      rw [hwzvec, hwe, add_assoc, hzz, add_zero]
    by_cases hva : c.vec a = 1 ∧ c.vec b = 1
    · left
      refine mkQ_eq_one_of_const w hwperm1 1 fun i => ?_
      rw [hwe]
      by_cases hiβ : i ∈ β
      · rw [hcvβ i hiβ, hzon i hiβ, zero_add]
      · rcases hout i hiβ with rfl | rfl
        · rw [hva.1, hzoff _ hiβ, add_zero]
        · rw [hva.2, hzoff _ hiβ, add_zero]
    · right
      by_cases hca : c.vec a = 1
      · have hcb : c.vec b = 0 := two' _ fun h => hva ⟨hca, h⟩
        refine final a ha (off_a _ 0 (fun i hi => ?_) ?_)
        · rw [hwz, hcvβ i hi]
        · rw [hwz, hcb]
      · have hca0 : c.vec a = 0 := two' _ hca
        refine final b hb (off_b _ 0 (fun i hi => ?_) ?_)
        · rw [hwz, hcvβ i hi]
        · rw [hwz, hca0]

end Classify

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
