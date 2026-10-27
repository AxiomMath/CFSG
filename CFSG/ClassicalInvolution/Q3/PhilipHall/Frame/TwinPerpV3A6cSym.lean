module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cFin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Trans

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5

section Pair

variable {n : ℕ}

theorem map_eq_of_forall_mem {α β : Finset (Fin n)} (σ : Equiv.Perm (Fin n)) (h : α.card = 4)
    (h' : β.card = 4) (hσ : ∀ x ∈ α, σ x ∈ β) : α.map σ.toEmbedding = β := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact hσ x hx
  · rw [Finset.card_map, h, h']

theorem zBar_congr {α β : Finset (Fin n)} (e : α = β) (h : α.card = 4) (h' : β.card = 4) :
    zBar α h = zBar β h' := by
  subst e
  rfl

theorem exists_conj_twin (hn : 5 ≤ n) {α β : Finset (Fin n)} (h : α.card = 4) (h' : β.card = 4) (b : Bool) :
    ∃ w ∈ aeSub n, (memBar α h true).map (MulAut.conj (mkQ n w)).toMonoidHom = memBar β h' b ∧
      (memBar α h false).map (MulAut.conj (mkQ n w)).toMonoidHom = memBar β h' (!b) ∧
      mkQ n w * zBar α h * (mkQ n w)⁻¹ = zBar β h' := by
  classical
  obtain ⟨σ, hσs, hσ⟩ := exists_even_perm hn h h'
  have hmem : ∀ i, σ (emb α h i) ∈ Set.range (emb β h') := by
    intro i
    rw [range_emb]
    apply hσ
    have : emb α h i ∈ Set.range (emb α h) := Set.mem_range_self i
    rw [range_emb] at this
    exact this
  obtain ⟨c0, hc0⟩ := exists_local σ hmem
  have hemb : (emb α h).trans σ.toEmbedding = c0.toEmbedding.trans (emb β h') :=
    Function.Embedding.ext fun i => hc0 i
  obtain ⟨e, he⟩ := conj_memBar_perm hn σ c0 hemb
  have hσW : ofPerm σ ∈ aeSub n :=
    (ofPerm_mem_aeSubOver (A := ⊤) (Subgroup.mem_top σ) hσs).1
  have hz : mkQ n (ofPerm σ) * zBar α h * (mkQ n (ofPerm σ))⁻¹ = zBar β h' := by
    have hc : (α.map σ.toEmbedding).card = 4 := by rw [Finset.card_map, h]
    rw [conj_zBar_ofPerm σ α h hc]
    exact zBar_congr (map_eq_of_forall_mem σ h h' hσ) hc h'
  by_cases hbe : e = !b
  · subst hbe
    refine ⟨ofPerm σ, hσW, ?_, ?_, hz⟩
    · rw [he true]
      cases b <;> rfl
    · rw [he false]
      cases b <;> rfl
  · obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ β := by
      by_contra hcon
      push Not at hcon
      have : (Finset.univ : Finset (Fin n)) ⊆ β := fun x _ => hcon x
      have h1 := Finset.card_le_card this
      rw [Finset.card_univ, Fintype.card_fin, h'] at h1
      omega
    have heb : e = b := by
      revert hbe
      cases e <;> cases b <;> simp
    subst heb
    have hcomp : (MulAut.conj (mkQ n (twinVec (emb β h') j * ofPerm σ))).toMonoidHom =
        (MulAut.conj (mkQ n (twinVec (emb β h') j))).toMonoidHom.comp
          (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom := by
      rw [map_mul]
      refine MonoidHom.ext fun x => ?_
      simp [MulAut.conj_apply, mul_assoc]
    refine ⟨twinVec (emb β h') j * ofPerm σ, ?_, ?_, ?_, ?_⟩
    · refine (aeSub n).mul_mem ?_ hσW
      exact (twinVec_mem (emb β h') (by rw [range_emb]; exact hj) ⊤).1
    · rw [hcomp, ← Subgroup.map_map, he true, conj_memBar_flip hn h' hj]
      cases e <;> rfl
    · rw [hcomp, ← Subgroup.map_map, he false, conj_memBar_flip hn h' hj]
      cases e <;> rfl
    · have hv : TC.Thin.permQ n (mkQ n (twinVec (emb β h') j)) = 1 := rfl
      have hcz : mkQ n (twinVec (emb β h') j) * zBar β h' = zBar β h' * mkQ n (twinVec (emb β h') j) :=
        V_comm hv (permQ_zBar β h')
      rw [map_mul, mul_inv_rev]
      calc mkQ n (twinVec (emb β h') j) * mkQ n (ofPerm σ) * zBar α h *
            ((mkQ n (ofPerm σ))⁻¹ * (mkQ n (twinVec (emb β h') j))⁻¹)
          = mkQ n (twinVec (emb β h') j) * (mkQ n (ofPerm σ) * zBar α h * (mkQ n (ofPerm σ))⁻¹) *
            (mkQ n (twinVec (emb β h') j))⁻¹ := by group
        _ = zBar β h' := by rw [hz, hcz, mul_inv_cancel_right]

end Pair

section Local

theorem InU.conj {g x : AEQ 6} (hg : g ∈ TL4.aeModel 6) (hx : InU x) : InU (g * x * g⁻¹) :=
  ⟨(TL4.aeModel 6).mul_mem ((TL4.aeModel 6).mul_mem hg hx.1) ((TL4.aeModel 6).inv_mem hg), by
    rw [map_mul, map_mul, hx.2, mul_one, map_inv, mul_inv_cancel]⟩

theorem permQ_conj {g x : AEQ 6} (hx : TC.Thin.permQ 6 x = 1) : TC.Thin.permQ 6 (g * x * g⁻¹) = 1 := by
  rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]

theorem conj_conj_inv (g x : AEQ 6) : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group

theorem conj_inj {g a b : AEQ 6} (h : g * a * g⁻¹ = g * b * g⁻¹) : a = b := by
  simpa using h

theorem comm_pull {g x : AEQ 6} {K L : Subgroup (AEQ 6)} (hKL : ∀ k ∈ K, g * k * g⁻¹ ∈ L)
    (hx : ∀ l ∈ L, l * x = x * l) : ∀ k ∈ K, k * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * x * g⁻¹⁻¹ * k := by
  intro k hk
  have e := hx _ (hKL k hk)
  calc k * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * (g * k * g⁻¹ * x) * g := by group
    _ = g⁻¹ * (x * (g * k * g⁻¹)) * g := by rw [e]
    _ = _ := by group

@[expose] def CentUAt (K K' : Subgroup (AEQ 6)) (z : AEQ 6) : Prop :=
  ∀ x : AEQ 6, InU x → (∀ k ∈ K, k * x = x * k) → (∀ k ∈ K', k * x = x * k) → x = 1 ∨ x = z

@[expose] def Twin2At (K K' : Subgroup (AEQ 6)) : Prop :=
  ∃ f : Fin 8 → AEQ 6, Function.Injective f ∧
    ∀ i, TC.Thin.permQ 6 (f i) = 1 ∧ ∃ k ∈ K, ∃ k' ∈ K', f i = k * k'

@[expose] def Twin3At (K K' : Subgroup (AEQ 6)) (z : AEQ 6) : Prop :=
  ∀ x y : AEQ 6, (∀ k ∈ K, k * x = x * k) → (∀ k ∈ K', k * x = x * k) →
    (∀ k ∈ K, k * y = y * k) → (∀ k ∈ K', k * y = y * k) →
    x * x = z → y * y = 1 → y * x * y⁻¹ = x * z →
      TC.Thin.permQ 6 y = 1 ∨ TC.Thin.permQ 6 (y * x) = 1

@[expose] def Twin4At (K K' : Subgroup (AEQ 6)) (z : AEQ 6) : Prop :=
  ∀ g : AEQ 6, (∀ x : AEQ 6, InU x → x * g * x⁻¹ * g⁻¹ = 1 ∨ x * g * x⁻¹ * g⁻¹ = z) →
    (∃ x : AEQ 6, InU x ∧ x * g * x⁻¹ * g⁻¹ = z) → ∀ δ : AEQ 6, TC.Thin.permQ 6 δ = 1 →
    (∀ k ∈ K, k * δ = δ * k) → (∀ k ∈ K', k * δ = δ * k) → δ ≠ 1 → δ ≠ z → g * δ * g⁻¹ ≠ δ

variable {g : AEQ 6} {K K' L L' : Subgroup (AEQ 6)} {z : AEQ 6}

theorem CentUAt.conj (hg : g ∈ TL4.aeModel 6) (hK : ∀ k ∈ K, g * k * g⁻¹ ∈ L)
    (hK' : ∀ k ∈ K', g * k * g⁻¹ ∈ L') (H : CentUAt K K' z) : CentUAt L L' (g * z * g⁻¹) := by
  intro x hx h1 h2
  rcases H _ (InU.conj ((TL4.aeModel 6).inv_mem hg) hx) (comm_pull hK h1) (comm_pull hK' h2) with hy | hy
  · left
    rw [← conj_conj_inv g x, hy]
    group
  · right
    rw [← conj_conj_inv g x, hy]

theorem Twin2At.conj (hK : ∀ k ∈ K, g * k * g⁻¹ ∈ L) (hK' : ∀ k ∈ K', g * k * g⁻¹ ∈ L')
    (H : Twin2At K K') : Twin2At L L' := by
  obtain ⟨f, hf, hfi⟩ := H
  refine ⟨fun i => g * f i * g⁻¹, fun i j hij => hf (conj_inj hij), fun i => ?_⟩
  obtain ⟨hp, k, hk, k', hk', he⟩ := hfi i
  refine ⟨permQ_conj hp, _, hK k hk, _, hK' k' hk', ?_⟩
  simp only [he]
  group

theorem Twin3At.conj (hK : ∀ k ∈ K, g * k * g⁻¹ ∈ L) (hK' : ∀ k ∈ K', g * k * g⁻¹ ∈ L')
    (H : Twin3At K K' z) : Twin3At L L' (g * z * g⁻¹) := by
  intro x y hx1 hx2 hy1 hy2 hxx hyy hyx
  have hy := H (g⁻¹ * x * g⁻¹⁻¹) (g⁻¹ * y * g⁻¹⁻¹) (comm_pull hK hx1) (comm_pull hK' hx2)
    (comm_pull hK hy1) (comm_pull hK' hy2)
    (by
      calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * (x * x) * g := by group
        _ = z := by rw [hxx]; group)
    (by
      calc g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (y * y) * g := by group
        _ = 1 := by rw [hyy]; group)
    (by
      calc g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) * (g⁻¹ * y * g⁻¹⁻¹)⁻¹ = g⁻¹ * (y * x * y⁻¹) * g := by group
        _ = g⁻¹ * x * g⁻¹⁻¹ * z := by rw [hyx]; group)
  rcases hy with hy | hy
  · left
    rw [← conj_conj_inv g y]
    exact permQ_conj hy
  · right
    have e : y * x = g * (g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by group
    rw [e]
    exact permQ_conj hy

theorem Twin4At.conj (hg : g ∈ TL4.aeModel 6) (hK : ∀ k ∈ K, g * k * g⁻¹ ∈ L)
    (hK' : ∀ k ∈ K', g * k * g⁻¹ ∈ L') (H : Twin4At K K' z) : Twin4At L L' (g * z * g⁻¹) := by
  intro t H1 H2 δ hδ hd1 hd2 hδ1 hδz
  have hcomm : ∀ x : AEQ 6, g * x * g⁻¹ * t * (g * x * g⁻¹)⁻¹ * t⁻¹ =
      g * (x * (g⁻¹ * t * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * t * g⁻¹⁻¹)⁻¹) * g⁻¹ := fun x => by group
  have h1 : ∀ x : AEQ 6, InU x → x * (g⁻¹ * t * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * t * g⁻¹⁻¹)⁻¹ = 1 ∨
      x * (g⁻¹ * t * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * t * g⁻¹⁻¹)⁻¹ = z := by
    intro x hx
    rcases H1 _ (InU.conj hg hx) with e | e
    · left
      rw [hcomm] at e
      exact conj_inj (e.trans (by group))
    · right
      rw [hcomm] at e
      exact conj_inj e
  have h2 : ∃ x : AEQ 6, InU x ∧ x * (g⁻¹ * t * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * t * g⁻¹⁻¹)⁻¹ = z := by
    obtain ⟨x, hx, e⟩ := H2
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, InU.conj ((TL4.aeModel 6).inv_mem hg) hx, conj_inj (g := g) ?_⟩
    rw [← hcomm, conj_conj_inv]
    exact e
  intro hfix
  refine H _ h1 h2 (g⁻¹ * δ * g⁻¹⁻¹) (permQ_conj hδ) (comm_pull hK hd1) (comm_pull hK' hd2) ?_ ?_ ?_
  · intro e
    apply hδ1
    rw [← conj_conj_inv g δ, e]
    group
  · intro e
    apply hδz
    rw [← conj_conj_inv g δ, e]
  · calc g⁻¹ * t * g⁻¹⁻¹ * (g⁻¹ * δ * g⁻¹⁻¹) * (g⁻¹ * t * g⁻¹⁻¹)⁻¹ = g⁻¹ * (t * δ * t⁻¹) * g := by group
      _ = g⁻¹ * δ * g⁻¹⁻¹ := by rw [hfix]; group

end Local

theorem ae6Fin_of_base {α₀ : Finset (Fin 6)} (h₀ : α₀.card = 4)
    (htrans : ∀ x y : AEQ 6, InU x → InU y → x ≠ 1 → y ≠ 1 → ∃ g ∈ TL4.aeModel 6, g * x * g⁻¹ = y)
    (hcent : CentUAt (memBar α₀ h₀ true) (memBar α₀ h₀ false) (zBar α₀ h₀))
    (h2 : Twin2At (memBar α₀ h₀ true) (memBar α₀ h₀ false))
    (h3 : Twin3At (memBar α₀ h₀ true) (memBar α₀ h₀ false) (zBar α₀ h₀))
    (h4 : Twin4At (memBar α₀ h₀ true) (memBar α₀ h₀ false) (zBar α₀ h₀)) : AE6Fin := by
  have key : ∀ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool), ∃ g ∈ TL4.aeModel 6,
      (∀ k ∈ memBar α₀ h₀ true, g * k * g⁻¹ ∈ memBar α h b) ∧
      (∀ k ∈ memBar α₀ h₀ false, g * k * g⁻¹ ∈ memBar α h (!b)) ∧ g * zBar α₀ h₀ * g⁻¹ = zBar α h := by
    intro α h b
    obtain ⟨w, hw, hT, hF, hz⟩ := exists_conj_twin (by norm_num) h₀ h b
    refine ⟨mkQ 6 w, ⟨w, hw, rfl⟩, fun k hk => ?_, fun k hk => ?_, hz⟩
    · rw [← hT]
      exact Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩
    · rw [← hF]
      exact Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩
  refine ⟨htrans, fun α h b => ?_, fun α h b => ?_, fun α h b => ?_, fun α h b => ?_⟩
  · obtain ⟨g, hg, hT, hF, hz⟩ := key α h b
    have := hcent.conj hg hT hF
    rw [hz] at this
    exact this
  · obtain ⟨g, -, hT, hF, -⟩ := key α h b
    exact h2.conj hT hF
  · obtain ⟨g, -, hT, hF, hz⟩ := key α h b
    have := h3.conj hT hF
    rw [hz] at this
    exact this
  · obtain ⟨g, hg, hT, hF, hz⟩ := key α h b
    have := h4.conj hg hT hF
    rw [hz] at this
    exact this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
