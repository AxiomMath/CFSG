module

public import CFSG.ClassicalInvolution.Q3.AE.Conj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2Conj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Mem
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2Basic
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2ConjE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def Into (g : Wr 8) (P M : Subgroup (AEQ 8)) : Prop :=
  ∀ x ∈ P, mkQ 8 g * x * (mkQ 8 g)⁻¹ ∈ M

theorem Into.trans {g g' : Wr 8} {P M N : Subgroup (AEQ 8)} (h1 : Into g P M) (h2 : Into g' M N) :
    Into (g' * g) P N := by
  intro x hx
  have := h2 _ (h1 x hx)
  rw [map_mul, mul_inv_rev]
  convert this using 1
  group

theorem memBar_true (α : Finset (Fin 8)) (h : α.card = 4) :
    memBar α h true = (memK (emb α h)).map (mkQ 8) := rfl

theorem memBar_false (α : Finset (Fin 8)) (h : α.card = 4) :
    memBar α h false = (memKStar (emb α h)).map (mkQ 8) := rfl

theorem into_flip {ι : Fin 4 ↪ Fin 8} {j : Fin 8} (hj : j ∉ Set.range ι) :
    Into (twinVec ι j) ((memK ι).map (mkQ 8)) ((memKStar ι).map (mkQ 8)) ∧
    Into (twinVec ι j) ((memKStar ι).map (mkQ 8)) ((memK ι).map (mkQ 8)) := by
  have hinv : (twinVec ι j)⁻¹ = twinVec ι j := inv_eq_of_mul_eq_one_right (twinVec_mul_self ι j)
  have hmap := map_conj_memK ι hj
  constructor
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨twinVec ι j * w * (twinVec ι j)⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [← hmap]
    exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [← hmap] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    refine ⟨w', hw', ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul,
      map_inv, hinv]
    have h2 : mkQ 8 (twinVec ι j) * mkQ 8 (twinVec ι j) = 1 := by
      rw [← map_mul, twinVec_mul_self, map_one]
    have h3 : (mkQ 8 (twinVec ι j))⁻¹ = mkQ 8 (twinVec ι j) := inv_eq_of_mul_eq_one_right h2
    rw [h3]
    calc mkQ 8 w' = (mkQ 8 (twinVec ι j) * mkQ 8 (twinVec ι j)) * mkQ 8 w' *
          (mkQ 8 (twinVec ι j) * mkQ 8 (twinVec ι j)) := by rw [h2]; group
      _ = _ := by group

theorem into_flip_memBar {α : Finset (Fin 8)} (h : α.card = 4) {j : Fin 8} (hj : j ∉ α) (b : Bool) :
    Into (twinVec (emb α h) j) (memBar α h b) (memBar α h (!b)) := by
  have hj' : j ∉ Set.range (emb α h) := by rw [range_emb]; exact hj
  cases b
  · exact (into_flip hj').2
  · exact (into_flip hj').1

theorem twinVec_comm (ι ι' : Fin 4 ↪ Fin 8) : twinVec ι (ι' 0) = twinVec ι' (ι 0) := by
  unfold twinVec
  congr 1
  funext x
  exact add_comm _ _

theorem conj_S4 : ∀ c : Equiv.Perm (Fin 4),
    ((∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList) ∧
      (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList)) ∨
    ((∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList) ∧
      (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList)) := by decide +kernel

theorem into_perm {α β : Finset (Fin 8)} {h : α.card = 4} {h' : β.card = 4}
    (σ : Equiv.Perm (Fin 8)) (c : Equiv.Perm (Fin 4))
    (hemb : (emb α h).trans σ.toEmbedding = c.toEmbedding.trans (emb β h')) :
    ∃ e : Bool, ∀ b : Bool, Into (ofPerm σ) (memBar α h b) (memBar β h' (xor b e)) := by
  have step : ∀ k : Wr 4, ofPerm σ * embed (emb α h) k * (ofPerm σ)⁻¹ =
      embed (emb β h') (ofPerm c * k * (ofPerm c)⁻¹) := by
    intro k
    rw [conj_perm_embed, hemb, embed_trans_perm]
  have img : ∀ k : Wr 4, mkQ 8 (ofPerm σ) * mkQ 8 (embed (emb α h) k) * (mkQ 8 (ofPerm σ))⁻¹ =
      mkQ 8 (embed (emb β h') (ofPerm c * k * (ofPerm c)⁻¹)) := by
    intro k
    rw [← step k, map_mul, map_mul, map_inv]
  rcases conj_S4 c with ⟨hK, hS⟩ | ⟨hK, hS⟩
  · refine ⟨false, fun b => ?_⟩
    cases b
    · rintro _ ⟨w, ⟨k, hk, rfl⟩, rfl⟩
      rw [img]
      exact ⟨_, ⟨_, mem_kQStar.mpr (hS k (mem_kQStar.mp hk)), rfl⟩, rfl⟩
    · rintro _ ⟨w, ⟨k, hk, rfl⟩, rfl⟩
      rw [img]
      exact ⟨_, ⟨_, mem_kQ.mpr (hK k (mem_kQ.mp hk)), rfl⟩, rfl⟩
  · refine ⟨true, fun b => ?_⟩
    cases b
    · rintro _ ⟨w, ⟨k, hk, rfl⟩, rfl⟩
      rw [img]
      exact ⟨_, ⟨_, mem_kQ.mpr (hS k (mem_kQStar.mp hk)), rfl⟩, rfl⟩
    · rintro _ ⟨w, ⟨k, hk, rfl⟩, rfl⟩
      rw [img]
      exact ⟨_, ⟨_, mem_kQStar.mpr (hK k (mem_kQ.mp hk)), rfl⟩, rfl⟩

@[expose] def permsTo : List (List (List (Fin 8))) := [
  [],
  [[0, 1], [2, 3], [4, 5], [6, 7]],
  [[1, 2], [5, 6]],
  [[0, 2, 3, 1], [4, 6, 7, 5]],
  [[2, 3], [6, 7]],
  [[0, 1], [4, 5]],
  [[1, 4, 2], [3, 5, 6]],
  [[0, 4, 6, 7, 3, 1], [2, 5]],
  [[4, 5], [6, 7]],
  [[0, 1], [2, 3]],
  [[1, 2], [4, 6, 7, 5]],
  [[0, 2, 3, 1], [5, 6]],
  [[2, 3], [4, 5]],
  [[0, 1], [6, 7]]]

theorem perm_target8 : ∀ α ∈ affinePlanes, ∃ t ∈ permsTo, (∀ x ∈ α0, pc t x ∈ α) ∧
    (∀ x ∈ α1, pc t x ∈ αᶜ) ∧
    (∀ s ∈ affinePlanes, s.map (pc t).toEmbedding ∈ affinePlanes ∧
      s.map (pc t)⁻¹.toEmbedding ∈ affinePlanes) ∧ Equiv.Perm.sign (pc t) = 1 := by
  decide +kernel

theorem exists_local' {n : ℕ} (ι ι' : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, σ (ι i) ∈ Set.range ι') : ∃ c : Equiv.Perm (Fin 4), ∀ i, σ (ι i) = ι' (c i) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.exists_local ι ι' σ h

theorem bool_aux1 : ∀ b b' e0 : Bool, b' ≠ b →
    ((xor true e0 = b ∧ xor false e0 = b') ∨ ((!(xor true e0)) = b ∧ (!(xor false e0)) = b')) := by
  decide

theorem bool_aux2 : ∀ b b' e0 e1 : Bool, ∃ f : Bool, b = xor (xor true e0) f ∧
    (b' = xor (xor true e1) f ∨ b' = xor (xor false e1) f) := by decide

theorem pair_conj {α β : Finset (Fin 8)} (hα : α ∈ affinePlanes) (h4 : α.card = 4) (b : Bool)
    (h4' : β.card = 4) (b' : Bool) (hβ : β = α ∨ β = αᶜ) (hne : ¬ (β = α ∧ b' = b)) :
    (∃ g ∈ aeSubOver agl32, Into g (memBar α0 α0_card true) (memBar α h4 b) ∧
      Into g (memBar α0 α0_card false) (memBar β h4' b')) ∨
    (∃ g ∈ aeSubOver agl32, Into g (memBar α0 α0_card true) (memBar α h4 b) ∧
      Into g (memBar α1 α1_card true) (memBar β h4' b')) ∨
    (∃ g ∈ aeSubOver agl32, Into g (memBar α0 α0_card true) (memBar α h4 b) ∧
      Into g (memBar α1 α1_card false) (memBar β h4' b')) := by
  have h4c : αᶜ.card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, h4]
  obtain ⟨t, -, hmap0, hmap1, hσF, hσs⟩ := perm_target8 α hα
  set σ := pc t with hσ
  have hmem0 : ∀ i, σ (emb α0 α0_card i) ∈ Set.range (emb α h4) := by
    intro i
    rw [range_emb]
    apply hmap0
    have : emb α0 α0_card i ∈ Set.range (emb α0 α0_card) := Set.mem_range_self i
    rw [range_emb] at this
    exact this
  have hmem1 : ∀ i, σ (emb α1 α1_card i) ∈ Set.range (emb αᶜ h4c) := by
    intro i
    rw [range_emb]
    apply hmap1
    have : emb α1 α1_card i ∈ Set.range (emb α1 α1_card) := Set.mem_range_self i
    rw [range_emb] at this
    exact this
  obtain ⟨c0, hc0⟩ := exists_local' _ _ σ hmem0
  obtain ⟨c1, hc1⟩ := exists_local' _ _ σ hmem1
  have hemb0 : (emb α0 α0_card).trans σ.toEmbedding = c0.toEmbedding.trans (emb α h4) :=
    Function.Embedding.ext fun i => hc0 i
  have hemb1 : (emb α1 α1_card).trans σ.toEmbedding = c1.toEmbedding.trans (emb αᶜ h4c) :=
    Function.Embedding.ext fun i => hc1 i
  obtain ⟨e0, hA⟩ := into_perm σ c0 hemb0
  obtain ⟨e1, hB⟩ := into_perm σ c1 hemb1
  have hg0 : ofPerm σ ∈ aeSubOver agl32 := ofPerm_mem_aeSubOver hσF hσs
  have hαne : (emb αᶜ h4c 0) ∉ α := by
    have : emb αᶜ h4c 0 ∈ Set.range (emb αᶜ h4c) := Set.mem_range_self 0
    rw [range_emb] at this
    simpa using this
  have hαne' : (emb α h4 0) ∉ αᶜ := by
    have : emb α h4 0 ∈ Set.range (emb α h4) := Set.mem_range_self 0
    rw [range_emb] at this
    simpa using this
  rcases hβ with hβ | hβ
  ·
    have hβ' := hβ.symm
    subst hβ'
    have hbb : b' ≠ b := fun h => hne ⟨rfl, h⟩
    have hjr : (twinVec (emb α h4) (emb αᶜ h4c 0)) ∈ aeSubOver agl32 :=
      twinVec_mem _ (by rw [range_emb]; simpa using hαne) _
    left
    rcases bool_aux1 b b' e0 hbb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · subst hb1; subst hb2
      exact ⟨ofPerm σ, hg0, hA true, hA false⟩
    · subst hb1; subst hb2
      refine ⟨twinVec (emb α h4) (emb αᶜ h4c 0) * ofPerm σ, (aeSubOver agl32).mul_mem hjr hg0,
        (Into.trans (hA true) (into_flip_memBar h4 hαne (xor true e0))),
        (Into.trans (hA false) (into_flip_memBar h4 hαne (xor false e0)))⟩
  ·
    subst hβ
    obtain ⟨f, hf1, hf2⟩ := bool_aux2 b b' e0 e1
    set w := twinVec (emb α h4) (emb αᶜ h4c 0) with hw
    have hwm : w ∈ aeSubOver agl32 :=
      twinVec_mem _ (by rw [range_emb]; simpa using hαne) _
    have hwα : ∀ c, Into w (memBar α h4 c) (memBar α h4 (!c)) :=
      into_flip_memBar h4 hαne
    have hwβ : ∀ c, Into w (memBar αᶜ h4' c) (memBar αᶜ h4' (!c)) := by
      intro c
      have := into_flip_memBar h4' hαne' c
      rwa [← twinVec_comm] at this
    subst hf1
    right
    cases f
    · rcases hf2 with hf2 | hf2
      · left
        subst hf2
        refine ⟨ofPerm σ, hg0, ?_, ?_⟩
        · intro x hx; have := hA true x hx; simpa using this
        · intro x hx; have := hB true x hx; simpa using this
      · right
        subst hf2
        refine ⟨ofPerm σ, hg0, ?_, ?_⟩
        · intro x hx; have := hA true x hx; simpa using this
        · intro x hx; have := hB false x hx; simpa using this
    · rcases hf2 with hf2 | hf2
      · left
        subst hf2
        refine ⟨w * ofPerm σ, (aeSubOver agl32).mul_mem hwm hg0, ?_, ?_⟩
        · intro x hx
          have := (Into.trans (hA true) (hwα (xor true e0))) x hx
          simpa using this
        · intro x hx
          have := (Into.trans (hB true) (hwβ (xor true e1))) x hx
          simpa using this
      · right
        subst hf2
        refine ⟨w * ofPerm σ, (aeSubOver agl32).mul_mem hwm hg0, ?_, ?_⟩
        · intro x hx
          have := (Into.trans (hA true) (hwα (xor true e0))) x hx
          simpa using this
        · intro x hx
          have := (Into.trans (hB false) (hwβ (xor false e1))) x hx
          simpa using this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
