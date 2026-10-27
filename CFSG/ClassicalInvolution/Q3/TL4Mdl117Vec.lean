module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Inv
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Pair

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

variable {n : ℕ}

instance aeSub_normal : (aeSub n).Normal where
  conj_mem a ha g := by
    refine ⟨?_, ?_⟩
    · rw [wsum_mul, wsum_mul, wsum_inv, ha.1, add_zero, add_comm]
      exact zmod_two_add_self _
    · rw [mul_perm, mul_perm, inv_perm, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_inv, ha.2, mul_one, mul_comm]
      exact Int.units_mul_self _

instance GBar_normal : (GBar n).Normal :=
  (aeSub_normal (n := n)).map (mkQ n) (QuotientGroup.mk'_surjective _)

theorem zOf_emb_eq (α : Finset (Fin n)) (h : α.card = 4) : zOf (emb α h) = ofVec (indF α) := by
  refine Wr.ext (funext fun x => ?_) (zOf_perm _)
  have hr : x ∈ Set.range (emb α h) ↔ x ∈ α := by rw [range_emb]; rfl
  rw [zOf_vec_apply]
  show (if x ∈ Set.range (emb α h) then (1 : ZMod 2) else 0) = if x ∈ α then 1 else 0
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hr.mp h1) h2
  · exact absurd (hr.mpr h2) h1
  · rfl

theorem conj_ofVec (w : Wr n) (v : Fin n → ZMod 2) :
    w * ofVec v * w⁻¹ = ofVec fun i => v (w.perm.symm i) := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, mul_vec, inv_vec]
    show w.vec i + v (w.perm.symm i) + w.vec (w.perm ((w.perm * 1).symm i)) = v (w.perm.symm i)
    rw [mul_one, Equiv.apply_symm_apply, add_comm (w.vec i), add_assoc, zmod_two_add_self,
      add_zero]
  · rw [mul_perm, mul_perm, inv_perm]
    show w.perm * 1 * w.perm⁻¹ = 1
    rw [mul_one, mul_inv_cancel]

theorem zBar_conj (g : AEQ n) (α : Finset (Fin n)) (h : α.card = 4) :
    g * zBar α h * g⁻¹ =
      zBar (α.map (permQ n g).toEmbedding) (by rw [Finset.card_map]; exact h) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub n) g
  show mkQ n w * mkQ n (zOf (emb α h)) * (mkQ n w)⁻¹ = mkQ n (zOf (emb _ _))
  rw [← map_inv, ← map_mul, ← map_mul, zOf_emb_eq, zOf_emb_eq, conj_ofVec]
  congr 2
  funext i
  simp only [indF, Finset.mem_map_equiv, permQ_mkQ]

theorem perm_eq_one_of_map_eq (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)}
    (h : ∀ α : Finset (Fin n), α.card = 4 → α.map σ.toEmbedding = α) : σ = 1 := by
  refine Equiv.ext fun x => ?_
  by_contra hx
  have hc : 3 ≤ (Finset.univ \ {x, σ x}).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_two (a := x) (b := σ x)
    omega
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hc
  have hxt : x ∉ t := fun hx' => by simpa using ht hx'
  have hα : (insert x t).card = 4 := by rw [Finset.card_insert_of_notMem hxt, htc]
  have hmem : σ x ∈ (insert x t).map σ.toEmbedding :=
    Finset.mem_map_of_mem _ (Finset.mem_insert_self x t)
  rw [h _ hα, Finset.mem_insert] at hmem
  rcases hmem with h1 | h1
  · exact hx h1
  · simpa using ht h1

theorem permQ_eq_one_of_comm (hn5 : 5 ≤ n) (hn8 : n ≠ 8) {y : AEQ n}
    (hy : ∀ (α : Finset (Fin n)) (h : α.card = 4), y * zBar α h = zBar α h * y) :
    permQ n y = 1 := by
  refine perm_eq_one_of_map_eq hn5 fun α h => ?_
  have h1 := zBar_conj y α h
  rw [hy α h, mul_inv_cancel_right] at h1
  exact (eq_of_zBar_eq hn8 h1).symm

theorem exists_vec_of_permQ_eq_one {g : AEQ n} (hg : g ∈ GBar n) (hp : permQ n g = 1) :
    ∃ v : Fin n → ZMod 2, ∑ i, v i = 0 ∧ g = mkQ n (ofVec v) := by
  obtain ⟨w, hw, rfl⟩ := hg
  rw [permQ_mkQ] at hp
  exact ⟨w.vec, hw.1, congrArg (mkQ n) (Wr.ext rfl hp)⟩

theorem ofVec_mem_GBar {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0) : mkQ n (ofVec v) ∈ GBar n :=
  ⟨ofVec v, ⟨hv, by rw [show (ofVec v).perm = 1 from rfl, Equiv.Perm.sign_one]⟩, rfl⟩

theorem ofVec_add (v v' : Fin n → ZMod 2) : ofVec (v + v') = ofVec v * ofVec v' :=
  Wr.ext (funext fun _ => rfl) rfl

theorem fix_vec_of_fix_zBar (hS : spanProp n) {β₁ : MulAut ↥(GBar n)}
    (hβ₁ : ∀ (α : Finset (Fin n)) (h : α.card = 4),
      ((β₁ (zBarG α h) : ↥(GBar n)) : AEQ n) = zBar α h)
    {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0) (g : ↥(GBar n)) (hg : (g : AEQ n) = mkQ n (ofVec v)) :
    ((β₁ g : ↥(GBar n)) : AEQ n) = g := by
  have hz : ∀ (α : Finset (Fin n)) (h : α.card = 4), mkQ n (ofVec (indF α)) = zBar α h :=
    fun α h => by rw [zBar, zOf_emb_eq]
  rcases hS v hv with rfl | rfl | ⟨α, hα, rfl⟩ | ⟨α, hα, α', hα', rfl⟩
  · obtain rfl : g = 1 := Subtype.ext (by rw [hg]; rfl)
    rw [map_one]
  · obtain rfl : g = 1 := Subtype.ext (by
      rw [hg]
      exact (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl))
    rw [map_one]
  · have h4 := (Finset.mem_powersetCard.mp hα).2
    obtain rfl : g = zBarG α h4 := Subtype.ext (by rw [hg, hz α h4])
    exact hβ₁ α h4
  · have h4 := (Finset.mem_powersetCard.mp hα).2
    have h4' := (Finset.mem_powersetCard.mp hα').2
    obtain rfl : g = zBarG α h4 * zBarG α' h4' := Subtype.ext (by
      rw [hg, ofVec_add, map_mul, hz α h4, hz α' h4']
      rfl)
    rw [map_mul, Subgroup.coe_mul, hβ₁, hβ₁]
    rfl

theorem exists_vec_of_fix_zBar (hn5 : 5 ≤ n) (hn8 : n ≠ 8) {β₁ : MulAut ↥(GBar n)}
    (hβ₁ : ∀ (α : Finset (Fin n)) (h : α.card = 4),
      ((β₁ (zBarG α h) : ↥(GBar n)) : AEQ n) = zBar α h) (g : ↥(GBar n)) :
    ∃ v : Fin n → ZMod 2, ∑ i, v i = 0 ∧
      ((β₁ g : ↥(GBar n)) : AEQ n) = (g : AEQ n) * mkQ n (ofVec v) := by
  set y : AEQ n := (g : AEQ n)⁻¹ * ((β₁ g : ↥(GBar n)) : AEQ n) with hy
  have hyG : y ∈ GBar n := Subgroup.mul_mem _ (Subgroup.inv_mem _ g.2) (β₁ g).2
  have hcomm : ∀ (α : Finset (Fin n)) (h : α.card = 4), y * zBar α h = zBar α h * y := by
    intro α h
    have h4 : (α.map (permQ n g).toEmbedding).card = 4 := by rw [Finset.card_map]; exact h
    have hconj : g * zBarG α h * g⁻¹ = zBarG _ h4 := Subtype.ext (zBar_conj (g : AEQ n) α h)
    have hβ := congrArg (fun x : ↥(GBar n) => ((β₁ x : ↥(GBar n)) : AEQ n)) hconj
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hβ₁] at hβ
    have hg := zBar_conj (g : AEQ n) α h
    have key : ((β₁ g : ↥(GBar n)) : AEQ n) * zBar α h * ((β₁ g : ↥(GBar n)) : AEQ n)⁻¹ =
        (g : AEQ n) * zBar α h * (g : AEQ n)⁻¹ := by rw [hβ, hg]
    rw [hy]
    calc (g : AEQ n)⁻¹ * ((β₁ g : ↥(GBar n)) : AEQ n) * zBar α h
        = (g : AEQ n)⁻¹ * (((β₁ g : ↥(GBar n)) : AEQ n) * zBar α h *
            ((β₁ g : ↥(GBar n)) : AEQ n)⁻¹) * ((β₁ g : ↥(GBar n)) : AEQ n) := by group
      _ = (g : AEQ n)⁻¹ * ((g : AEQ n) * zBar α h * (g : AEQ n)⁻¹) *
            ((β₁ g : ↥(GBar n)) : AEQ n) := by rw [key]
      _ = zBar α h * ((g : AEQ n)⁻¹ * ((β₁ g : ↥(GBar n)) : AEQ n)) := by group
  obtain ⟨v, hv, hyv⟩ := exists_vec_of_permQ_eq_one hyG (permQ_eq_one_of_comm hn5 hn8 hcomm)
  refine ⟨v, hv, ?_⟩
  rw [← hyv, hy, mul_inv_cancel_left]

theorem exists_beta1 {β : MulAut ↥(GBar n)} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ (α : Finset (Fin n)) (h : α.card = 4),
      ((β (zBarG α h) : ↥(GBar n)) : AEQ n) =
        zBar (α.map σ.toEmbedding) (by rw [Finset.card_map]; exact h)) :
    ∀ (α : Finset (Fin n)) (h : α.card = 4),
      ((((MulAut.conjNormal (mkQ n (ofPerm σ)))⁻¹ * β : MulAut ↥(GBar n)) (zBarG α h) :
        ↥(GBar n)) : AEQ n) = zBar α h := by
  intro α h
  rw [MulAut.mul_apply, ← map_inv, MulAut.conjNormal_apply, hσ, zBar_conj]
  apply zBar_congr
  rw [map_inv, permQ_mkQ, Finset.map_map]
  show α.map (σ.toEmbedding.trans (σ⁻¹ : Equiv.Perm (Fin n)).toEmbedding) = α
  ext x
  simp

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
