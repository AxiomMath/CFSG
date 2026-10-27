module

public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

open CFSG.ClassicalInvolution.Q3.AE Wr

abbrev miss (p : Fin 5) : Finset (Fin 5) := Finset.univ.erase p

theorem card_miss (p : Fin 5) : (miss p).card = 4 := by
  simp [miss]

theorem exists_miss {α : Finset (Fin 5)} (h : α.card = 4) : ∃ p, α = miss p := by
  have hc : αᶜ.card = 1 := by rw [Finset.card_compl]; simp [h]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  refine ⟨p, ?_⟩
  ext x
  have : x ∈ αᶜ ↔ x = p := by rw [hp]; simp
  simp only [miss, Finset.mem_erase, Finset.mem_univ, and_true]
  rw [← not_iff_not, ← Finset.mem_compl, this]
  simp

theorem miss_inj {p q : Fin 5} (h : miss p = miss q) : p = q := by
  by_contra hne
  have : q ∈ miss p := by simp [miss, Ne.symm hne]
  rw [h] at this
  simp [miss] at this

theorem conj_vec_of_perm_one {n : ℕ} (x w : Wr n) (hw : w.perm = 1) (y : Fin n) :
    (x * w * x⁻¹).vec y = w.vec (x.perm.symm y) := by
  rw [mul_vec, mul_vec, inv_vec, mul_perm, hw, mul_one]
  rw [Equiv.apply_symm_apply]
  generalize x.vec y = a
  generalize w.vec (x.perm.symm y) = b
  revert a b
  decide

theorem conj_zOf_miss (x : Wr 5) (p : Fin 5) :
    x * zOf (emb (miss p) (card_miss p)) * x⁻¹ = zOf (emb (miss (x.perm p)) (card_miss _)) := by
  refine Wr.ext (funext fun y => ?_) ?_
  · rw [conj_vec_of_perm_one x _ (zOf_perm _), zOf_vec_apply, zOf_vec_apply]
    have hr : ∀ q : Fin 5, Set.range (emb (miss q) (card_miss q)) = ↑(miss q) := fun q =>
      range_emb _ _
    have h1 : x.perm.symm y ∈ Set.range (emb (miss p) (card_miss p)) ↔
        y ∈ Set.range (emb (miss (x.perm p)) (card_miss _)) := by
      rw [hr, hr]
      simp [miss, Equiv.symm_apply_eq]
    simp only [h1]
  · rw [mul_perm, mul_perm, zOf_perm, zOf_perm, inv_perm, mul_one, mul_inv_cancel]

theorem zBar_conj_miss (x : Wr 5) (p : Fin 5) :
    mkQ 5 x * zBar (miss p) (card_miss p) * (mkQ 5 x)⁻¹ =
      zBar (miss (x.perm p)) (card_miss _) := by
  unfold zBar
  rw [← map_inv, ← map_mul, ← map_mul, conj_zOf_miss]

def threeCycle {n : ℕ} (a b c : Fin n) : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap b c

theorem sign_threeCycle {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) :
    Equiv.Perm.sign (threeCycle a b c) = 1 := by
  rw [threeCycle, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hbc]
  decide

theorem threeCycle_fst {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) :
    threeCycle a b c a = b := by
  simp [threeCycle, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]

theorem threeCycle_snd {n : ℕ} {a b c : Fin n} (hbc : b ≠ c) (hac : a ≠ c) :
    threeCycle a b c b = c := by
  simp [threeCycle, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hac)
    (Ne.symm hbc)]

theorem threeCycle_thd {n : ℕ} {a b c : Fin n} : threeCycle a b c c = a := by
  simp [threeCycle, Equiv.swap_apply_right]

theorem threeCycle_of_ne {n : ℕ} {a b c x : Fin n} (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
    threeCycle a b c x = x := by
  simp [threeCycle, Equiv.swap_apply_of_ne_of_ne hb hc, Equiv.swap_apply_of_ne_of_ne ha hb]

theorem threeCycle_cubed {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    threeCycle a b c ^ 3 = 1 := by
  ext x
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id]
  by_cases hxa : x = a
  · subst hxa
    rw [threeCycle_fst hab hac, threeCycle_snd hbc hac, threeCycle_thd]
  by_cases hxb : x = b
  · subst hxb
    rw [threeCycle_snd hbc hac, threeCycle_thd, threeCycle_fst hab hac]
  by_cases hxc : x = c
  · subst hxc
    rw [threeCycle_thd, threeCycle_fst hab hac, threeCycle_snd hbc hac]
  rw [threeCycle_of_ne hxa hxb hxc, threeCycle_of_ne hxa hxb hxc, threeCycle_of_ne hxa hxb hxc]

theorem ofPerm_threeCycle_mem {a b c : Fin 5} (hab : a ≠ b) (hbc : b ≠ c) :
    ofPerm (threeCycle a b c) ∈ aeSub 5 := by
  refine ⟨?_, ?_⟩
  · unfold wsum
    simp [ofPerm]
  · exact sign_threeCycle hab hbc

@[expose] def w0 : Wr 4 := ⟨vec4 [0, 1], 1⟩

theorem w0_mul_self : w0 * w0 = 1 := by decide +kernel

theorem w0_ne_one : w0 ≠ 1 := by decide +kernel

theorem exists_w0_prod : ∃ k ∈ kList, ∃ k' ∈ kStarList, k * k' = w0 := by decide +kernel

theorem embed_w0_vec_eq_one_iff {n : ℕ} (ι : Fin 4 ↪ Fin n) (x : Fin n) :
    (embed ι w0).vec x = 1 ↔ x = ι 0 ∨ x = ι 1 := by
  classical
  rw [embed_vec]
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedVec_apply]
    have : ∀ i : Fin 4, (w0.vec i = 1 ↔ i = 0 ∨ i = 1) := by decide +kernel
    rw [this i]
    simp [ι.injective.eq_iff]
  · rw [embedVec_of_not_mem ι _ hx]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro (rfl | rfl)
      · exact absurd (Set.mem_range_self _) hx
      · exact absurd (Set.mem_range_self _) hx

theorem ofPerm_comm_embed_w0 {n : ℕ} (ι : Fin 4 ↪ Fin n) {σ : Equiv.Perm (Fin n)}
    (h0 : σ (ι 0) = ι 0) (h1 : σ (ι 1) = ι 1) :
    ofPerm σ * embed ι w0 = embed ι w0 * ofPerm σ := by
  have key : ofPerm σ * embed ι w0 * (ofPerm σ)⁻¹ = embed ι w0 := by
    refine Wr.ext (funext fun x => ?_) ?_
    · rw [ofPerm_conj_vec]
      have hiff : (embed ι w0).vec (σ.symm x) = 1 ↔ (embed ι w0).vec x = 1 := by
        rw [embed_w0_vec_eq_one_iff, embed_w0_vec_eq_one_iff]
        have e0 : σ.symm x = ι 0 ↔ x = ι 0 := by
          rw [Equiv.symm_apply_eq, h0]
        have e1 : σ.symm x = ι 1 ↔ x = ι 1 := by
          rw [Equiv.symm_apply_eq, h1]
        rw [e0, e1]
      generalize (embed ι w0).vec (σ.symm x) = a at hiff
      generalize (embed ι w0).vec x = b at hiff
      revert a b
      decide
    · show σ * (embed ι w0).perm * σ⁻¹ = (embed ι w0).perm
      have : (embed ι w0).perm = 1 := by
        rw [embed_perm]; exact embedPerm_one ι
      rw [this]; group
  calc ofPerm σ * embed ι w0 = (ofPerm σ * embed ι w0 * (ofPerm σ)⁻¹) * ofPerm σ := by group
    _ = embed ι w0 * ofPerm σ := by rw [key]

theorem embed_w0_mul_self {n : ℕ} (ι : Fin 4 ↪ Fin n) : embed ι w0 * embed ι w0 = 1 := by
  rw [← map_mul, w0_mul_self, map_one]

theorem embed_w0_ne_one {n : ℕ} (ι : Fin 4 ↪ Fin n) : embed ι w0 ≠ 1 := by
  intro h
  exact w0_ne_one (embed_injective ι (by rw [h, map_one]))

theorem exists_vecA_prod (α : Finset (Fin 5)) (h : α.card = 4) {b b' : Bool} (hb : b ≠ b') :
    ∃ x ∈ memBar α h b, ∃ y ∈ memBar α h b', x * y = mkQ 5 (embed (emb α h) w0) := by
  obtain ⟨k, hk, k', hk', hkk⟩ := exists_w0_prod
  have hK : embed (emb α h) k ∈ memAt α h true := ⟨k, hk, rfl⟩
  have hK' : embed (emb α h) k' ∈ memAt α h false := ⟨k', hk', rfl⟩
  have hprod : embed (emb α h) k * embed (emb α h) k' = embed (emb α h) w0 := by
    rw [← map_mul, hkk]
  have hcomm : embed (emb α h) k' * embed (emb α h) k = embed (emb α h) w0 := by
    rw [← map_mul, ← comm_kQ_kQStar k hk k' hk', hkk]
  cases b <;> cases b' <;> simp at hb
  · exact ⟨mkQ 5 (embed (emb α h) k'), ⟨_, hK', rfl⟩, mkQ 5 (embed (emb α h) k), ⟨_, hK, rfl⟩,
      by rw [← map_mul, hcomm]⟩
  · exact ⟨mkQ 5 (embed (emb α h) k), ⟨_, hK, rfl⟩, mkQ 5 (embed (emb α h) k'), ⟨_, hK', rfl⟩,
      by rw [← map_mul, hprod]⟩


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model
