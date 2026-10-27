module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoWr
public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Support

theorem supportedOn_of_mem_memAt_sup {β : Finset (Fin 6)} (hβ : β.card = 4) {a : Wr 6}
    (ha : a ∈ memAt β hβ true ⊔ memAt β hβ false) : SupportedOn a (Set.range (emb β hβ)) := by
  let S : Subgroup (Wr 6) :=
    { carrier := {a | SupportedOn a (Set.range (emb β hβ))}
      mul_mem' := fun ha hb => SupportedOn.mul ha hb
      one_mem' := supportedOn_one _
      inv_mem' := fun ha => SupportedOn.inv ha }
  have hle : memAt β hβ true ⊔ memAt β hβ false ≤ S :=
    sup_le (fun _ ha => supportedOn_of_mem_memAt ha) (fun _ ha => supportedOn_of_mem_memAt ha)
  exact hle ha

theorem eq_or_subset_of_zBar_mem {β γ : Finset (Fin 6)} (hβ : β.card = 4) (hγ : γ.card = 4)
    (h : zBar γ hγ ∈ memBar β hβ true ⊔ memBar β hβ false) : γ = β ∨ ∀ i, i ∉ β → i ∈ γ := by
  rw [memBar, memBar, ← Subgroup.map_sup] at h
  obtain ⟨a, ha, hae⟩ := h
  have hs : SupportedOn a (Set.range (emb β hβ)) := supportedOn_of_mem_memAt_sup hβ ha
  have hs' : SupportedOn a⁻¹ (Set.range (emb β hβ)) := hs.inv
  have hβr : ∀ x, x ∉ β → x ∉ Set.range (emb β hβ) := fun x hx => by
    rw [range_emb]
    exact hx
  have hγr : ∀ x, x ∈ γ → x ∈ Set.range (emb γ hγ) := fun x hx => by
    rw [range_emb]
    exact hx
  have hae' : mkQ 6 a = mkQ 6 (zOf (emb γ hγ)) := hae
  rcases mkQ_eq_iff.mp hae' with h1 | h1
  · left
    have h2 : a = zOf (emb γ hγ) := inv_mul_eq_one.mp h1
    have hsub : γ ⊆ β := by
      intro x hx
      by_contra hxβ
      have h3 := (hs x (hβr x hxβ)).1
      rw [h2, zOf_vec_apply, if_pos (hγr x hx)] at h3
      exact absurd h3 (by decide)
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hβ, hγ])
  · right
    intro x hxβ
    by_contra hxγ
    have hx' : x ∉ Set.range (emb γ hγ) := by
      rw [range_emb]
      exact hxγ
    have h3 := congrFun (congrArg Wr.vec h1) x
    rw [mul_vec, (hs' x (hβr x hxβ)).1, hs'.perm_symm (hβr x hxβ), zOf_vec_apply, zero_add,
      if_neg hx'] at h3
    have h5 : (allOnes 6).vec x = 1 := rfl
    rw [h5] at h3
    exact absurd h3 (by decide)

end Support

section Local

theorem conj_swap_kList : ∀ p q : Fin 4, p ≠ q → ∀ κ ε : ZMod 2, ∀ k ∈ kList,
    ofVec (fun i => if i = p ∨ i = q then κ else ε) * ofPerm (Equiv.swap p q) * k *
      (ofVec (fun i => if i = p ∨ i = q then κ else ε) * ofPerm (Equiv.swap p q))⁻¹ ∈ kStarList := by
  decide +kernel

theorem conj_swap_kStarList : ∀ p q : Fin 4, p ≠ q → ∀ κ ε : ZMod 2, ∀ k ∈ kStarList,
    ofVec (fun i => if i = p ∨ i = q then κ else ε) * ofPerm (Equiv.swap p q) * k *
      (ofVec (fun i => if i = p ∨ i = q then κ else ε) * ofPerm (Equiv.swap p q))⁻¹ ∈ kList := by
  decide +kernel

end Local

section Conj

variable {n : ℕ}

theorem ofVec_mul_embed_mul_ofVec (ι : Fin 4 ↪ Fin n) (V : Fin n → ZMod 2) (k : Wr 4) :
    ofVec V * embed ι k * ofVec V =
      embed ι (ofVec (fun i => V (ι i)) * k * ofVec (fun i => V (ι i))) := by
  classical
  refine Wr.ext (funext fun x => ?_) ?_
  · show V x + (embed ι k).vec x + V ((embed ι k).perm.symm x) =
      embedVec ι (fun i => V (ι i) + k.vec i + V (ι (k.perm.symm i))) x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, embed_vec, embedVec_apply, embed_perm, embedPerm_symm_apply]
    · rw [embedVec_of_not_mem ι _ hx, embed_vec, embedVec_of_not_mem ι _ hx, embed_perm,
        embedPerm_symm_of_not_mem ι _ hx, add_zero, zmod_two_add_self]
  · show 1 * embedPerm ι k.perm * 1 = embedPerm ι (1 * k.perm * 1)
    simp only [one_mul, mul_one]

theorem conj_embed_of_perm (ι : Fin 4 ↪ Fin n) (w : Wr n) (c : Equiv.Perm (Fin 4))
    (hσ : ∀ i, w.perm (ι i) = ι (c i)) (k : Wr 4) :
    w * embed ι k * w⁻¹ = embed ι (ofVec (fun i => w.vec (ι i)) * ofPerm c * k *
      (ofVec (fun i => w.vec (ι i)) * ofPerm c)⁻¹) := by
  have hw : w = ofVec w.vec * ofPerm w.perm := by
    refine Wr.ext (funext fun i => ?_) ?_
    · show w.vec i = w.vec i + 0
      rw [add_zero]
    · show w.perm = 1 * w.perm
      rw [one_mul]
  have hv : (ofVec w.vec)⁻¹ = ofVec w.vec :=
    inv_eq_of_mul_eq_one_right (TwinThinPf10.ofVec_mul_self _)
  have hv' : (ofVec fun i => w.vec (ι i))⁻¹ = ofVec fun i => w.vec (ι i) :=
    inv_eq_of_mul_eq_one_right (TwinThinPf10.ofVec_mul_self _)
  calc w * embed ι k * w⁻¹
      = ofVec w.vec * (ofPerm w.perm * embed ι k * (ofPerm w.perm)⁻¹) * (ofVec w.vec)⁻¹ := by
        conv_lhs => rw [hw]
        group
    _ = ofVec w.vec * embed ι (ofPerm c * k * (ofPerm c)⁻¹) * ofVec w.vec := by
        rw [ofPerm_conj_embed hσ, hv]
    _ = embed ι (ofVec (fun i => w.vec (ι i)) * (ofPerm c * k * (ofPerm c)⁻¹) *
          ofVec (fun i => w.vec (ι i))) := ofVec_mul_embed_mul_ofVec ι w.vec _
    _ = _ := by
        rw [mul_inv_rev, hv']
        congr 1
        group

end Conj

section Swap

theorem map_conj_memBar_of_odd {β γ : Finset (Fin 6)} (hβ : β.card = 4) (hγ : γ.card = 4) (w : Wr 6)
    (hcent : ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x)
    (hsign : Equiv.Perm.sign w.perm = -1) (hsq : mkQ 6 (w * w) = 1)
    (hγβ : ∀ i, i ∉ β → i ∈ γ) (b : Bool) :
    (memBar γ hγ b).map (MulAut.conj (mkQ 6 w)).toMonoidHom = memBar γ hγ (!b) := by
  obtain ⟨c, e, hw, he, hc⟩ := TwinThinPf10.exists_split (by norm_num) (by norm_num) β hβ w hcent
  obtain ⟨a₁, a₂, ha₁₂, ha₁, ha₂, hout⟩ := exists_compl_pair hβ
  have hxs : ∀ x ∈ β, x ∉ (Set.range (emb β hβ))ᶜ := by
    intro x hx
    rw [Set.mem_compl_iff, not_not, range_emb]
    exact hx
  have hcvec : ∀ x ∈ β, c.vec x = 0 := fun x hx => (hc x (hxs x hx)).1
  have hcfix : ∀ x ∈ β, c.perm x = x := fun x hx => (hc x (hxs x hx)).2
  have hcsymm : ∀ x ∈ β, c.perm.symm x = x := fun x hx => hc.perm_symm (hxs x hx)
  have hwperm : w.perm = c.perm := by
    rw [hw, mul_perm]
    rcases he with rfl | rfl
    · rw [one_perm, mul_one]
    · rw [zOf_perm, mul_one]
  have hperm : w.perm = Equiv.swap a₁ a₂ := by
    rcases perm_dichotomy ha₁₂ ha₁ ha₂ hout c.perm hcfix with h1 | h1
    · exfalso
      rw [hwperm, h1, Equiv.Perm.sign_one] at hsign
      exact units_ne_neg_self (1 : ℤˣ) hsign
    · rw [hwperm, h1]
  have hwsymm : ∀ x ∈ β, w.perm.symm x = x := fun x hx => by
    rw [hwperm]
    exact hcsymm x hx
  have hwvec : ∀ x ∈ β, w.vec x = e.vec x := fun x hx => by
    rw [hw, mul_vec, hcvec x hx, hcsymm x hx, zero_add]
  obtain ⟨ε, hε⟩ : ∃ ε : ZMod 2, ∀ x ∈ β, w.vec x = ε := by
    rcases he with rfl | rfl
    · exact ⟨0, fun x hx => by rw [hwvec x hx]; rfl⟩
    · exact ⟨1, fun x hx => by
        rw [hwvec x hx, zOf_vec_apply, if_pos (by rw [range_emb]; exact hx)]⟩
  have hww : w * w = 1 := by
    have hmem : w * w ∈ piSub 6 := (QuotientGroup.eq_one_iff _).mp hsq
    rcases hmem with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨x₀, hx₀⟩ : β.Nonempty := Finset.card_pos.mp (by rw [hβ]; norm_num)
      have h2 := congrFun (congrArg Wr.vec h1) x₀
      rw [mul_vec, hwsymm x₀ hx₀, hε x₀ hx₀, zmod_two_add_self] at h2
      exact absurd (show (0 : ZMod 2) = 1 from h2) (by decide)
  obtain ⟨κ, hκ₁⟩ : ∃ κ : ZMod 2, w.vec a₁ = κ := ⟨_, rfl⟩
  have hκ₂ : w.vec a₂ = κ := by
    have h2 := congrFun (congrArg Wr.vec hww) a₁
    rw [mul_vec, hperm, Equiv.symm_swap, Equiv.swap_apply_left, one_vec, Pi.zero_apply] at h2
    rw [← hκ₁]
    exact ((by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ h2).symm
  have hrγ : ∀ x, x ∈ γ → ∃ i, emb γ hγ i = x := fun x hx => by
    have : x ∈ Set.range (emb γ hγ) := by
      rw [range_emb]
      exact hx
    exact this
  obtain ⟨p, hp⟩ := hrγ a₁ (hγβ a₁ ha₁)
  obtain ⟨q, hq⟩ := hrγ a₂ (hγβ a₂ ha₂)
  have hpq : p ≠ q := fun h => ha₁₂ (by rw [← hp, ← hq, h])
  have hσ : ∀ i, w.perm (emb γ hγ i) = emb γ hγ (Equiv.swap p q i) := by
    intro i
    rw [hperm, ← hp, ← hq]
    exact (emb γ hγ).injective.swap_apply p q i
  have hu : (fun i => w.vec (emb γ hγ i)) = fun i => if i = p ∨ i = q then κ else ε := by
    funext i
    by_cases hi : i = p ∨ i = q
    · rw [if_pos hi]
      rcases hi with h | h
      · rw [h, hp, hκ₁]
      · rw [h, hq, hκ₂]
    · rw [if_neg hi]
      apply hε
      by_contra hiβ
      rcases hout _ hiβ with h | h
      · exact hi (Or.inl ((emb γ hγ).injective (h.trans hp.symm)))
      · exact hi (Or.inr ((emb γ hγ).injective (h.trans hq.symm)))
  obtain ⟨L, hL⟩ : ∃ L : Wr 4, L = ofVec (fun i => if i = p ∨ i = q then κ else ε) *
      ofPerm (Equiv.swap p q) := ⟨_, rfl⟩
  have hLK : ∀ k ∈ kList, L * k * L⁻¹ ∈ kStarList := fun k hk => by
    rw [hL]
    exact conj_swap_kList p q hpq κ ε k hk
  have hLKs : ∀ k ∈ kStarList, L * k * L⁻¹ ∈ kList := fun k hk => by
    rw [hL]
    exact conj_swap_kStarList p q hpq κ ε k hk
  have hkey : ∀ k : Wr 4, w * embed (emb γ hγ) k * w⁻¹ = embed (emb γ hγ) (L * k * L⁻¹) := by
    intro k
    rw [conj_embed_of_perm (emb γ hγ) w (Equiv.swap p q) hσ k, hu, hL]
  have hmk : ∀ k : Wr 4, mkQ 6 (embed (emb γ hγ) (L * k * L⁻¹)) =
      mkQ 6 w * mkQ 6 (embed (emb γ hγ) k) * (mkQ 6 w)⁻¹ := by
    intro k
    rw [← hkey k, map_mul, map_mul, map_inv]
  have hsub : ∀ b : Bool, ∀ x ∈ memBar γ hγ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ ∈ memBar γ hγ (!b) := by
    intro b
    rintro _ ⟨a', ha', rfl⟩
    cases b
    · obtain ⟨k, hk, rfl⟩ := ha'
      exact ⟨embed (emb γ hγ) (L * k * L⁻¹), ⟨_, mem_kQ.mpr (hLKs k (mem_kQStar.mp hk)), rfl⟩, hmk k⟩
    · obtain ⟨k, hk, rfl⟩ := ha'
      exact ⟨embed (emb γ hγ) (L * k * L⁻¹), ⟨_, mem_kQStar.mpr (hLK k (mem_kQ.mp hk)), rfl⟩, hmk k⟩
  have hg : mkQ 6 w * mkQ 6 w = 1 := by
    rw [← map_mul]
    exact hsq
  have hginv : (mkQ 6 w)⁻¹ = mkQ 6 w := inv_eq_of_mul_eq_one_right hg
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hsub b x hx
  · intro hy
    refine ⟨mkQ 6 w * y * (mkQ 6 w)⁻¹, ?_, ?_⟩
    · have := hsub (!b) y hy
      rwa [Bool.not_not] at this
    · show mkQ 6 w * (mkQ 6 w * y * (mkQ 6 w)⁻¹) * (mkQ 6 w)⁻¹ = y
      rw [hginv]
      calc mkQ 6 w * (mkQ 6 w * y * mkQ 6 w) * mkQ 6 w
          = (mkQ 6 w * mkQ 6 w) * y * (mkQ 6 w * mkQ 6 w) := by group
        _ = y := by rw [hg, one_mul, mul_one]

end Swap

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
