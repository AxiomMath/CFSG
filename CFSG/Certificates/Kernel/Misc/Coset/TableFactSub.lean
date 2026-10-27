module

public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Sporadic.Recognition.CoverChainSub

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable CFSG.Certificates CFSG.Sporadic.Recognition.CoverRecipe

variable {m : ℕ}

theorem TableFact.genSub_index_sub {ws₀ ws : List (List (Fin m × Bool))}
    (hsub : ∀ w ∈ ws₀, w ∈ ws) (hm : m < 256) (T : List (Fin m)) {N : ℕ}
    (h : KB.TableFact m (ws₀.map encW) (T.map fun x => [(x.val, true)]) N) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).index ≤ N := by
  obtain ⟨π, hπs, hπo⟩ := exists_surjective_PG hsub
  obtain ⟨hfi₀, hidx₀⟩ := TableFact.genSub_index ws₀ hm T h
  have hmap : (genSub {r : FreeGroup (Fin m) | r ∈ ws₀.map FreeGroup.mk} T).map π =
      genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T := by
    unfold genSub
    rw [MonoidHom.map_closure, Set.image_image]
    simp only [hπo]
  have hdvd := Subgroup.index_map_dvd
    (H := genSub {r : FreeGroup (Fin m) | r ∈ ws₀.map FreeGroup.mk} T) hπs
  rw [hmap] at hdvd
  have hne : (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).index ≠ 0 :=
    fun h0 => by
      rw [h0, zero_dvd_iff] at hdvd
      exact hfi₀.index_ne_zero hdvd
  exact ⟨⟨hne⟩, (Nat.le_of_dvd (Nat.pos_of_ne_zero hfi₀.index_ne_zero) hdvd).trans hidx₀⟩

theorem TableFact.card_sub {ws₀ ws : List (List (Fin m × Bool))} (hsub : ∀ w ∈ ws₀, w ∈ ws)
    (hm : m < 256) {N : ℕ} (h : KB.TableFact m (ws₀.map encW) [] N) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ N := by
  obtain ⟨hf, hc⟩ := TableFact.card ws₀ hm h
  obtain ⟨π, hπs, -⟩ := exists_surjective_PG hsub
  exact ⟨Finite.of_surjective π hπs, (Nat.card_le_card_of_surjective π hπs).trans hc⟩

theorem card_PG_le_chain₂_tf {ws L₂ : List (List (Fin m × Bool))} {S : List ℕ}
    {L₁ : List (List (Fin (subsetOf m S).length × Bool))} (hm : m < 256)
    (hm₁ : (subsetOf m S).length < 256)
    (h₂s : ∀ w ∈ L₂, w ∈ ws) (h₁s : ∀ w ∈ L₁, w ∈ restrictWords (subsetOf m S) ws) {n₂ n₁ : ℕ}
    (h₂ : KB.TableFact m (L₂.map encW) ((subsetOf m S).map fun x => [(x.val, true)]) n₂)
    (h₁ : KB.TableFact (subsetOf m S).length (L₁.map encW) [] n₁) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₂ * n₁ :=
  card_le_of_index_restrict ws (subsetOf m S) (TableFact.genSub_index_sub h₂s hm _ h₂)
    (TableFact.card_sub h₁s hm₁ h₁)

theorem card_PG_le_chain₃_tf {ws L₃ : List (List (Fin m × Bool))} {S₁ S₂ : List ℕ}
    {L₂ : List (List (Fin (subsetOf m S₁).length × Bool))}
    {L₁ : List (List (Fin (subsetOf (subsetOf m S₁).length S₂).length × Bool))} (hm : m < 256)
    (hm₂ : (subsetOf m S₁).length < 256) (hm₁ : (subsetOf (subsetOf m S₁).length S₂).length < 256)
    (h₃s : ∀ w ∈ L₃, w ∈ ws) (h₂s : ∀ w ∈ L₂, w ∈ restrictWords (subsetOf m S₁) ws)
    (h₁s : ∀ w ∈ L₁, w ∈ restrictWords (subsetOf (subsetOf m S₁).length S₂)
      (restrictWords (subsetOf m S₁) ws)) {n₃ n₂ n₁ : ℕ}
    (h₃ : KB.TableFact m (L₃.map encW) ((subsetOf m S₁).map fun x => [(x.val, true)]) n₃)
    (h₂ : KB.TableFact (subsetOf m S₁).length (L₂.map encW)
      ((subsetOf (subsetOf m S₁).length S₂).map fun x => [(x.val, true)]) n₂)
    (h₁ : KB.TableFact (subsetOf (subsetOf m S₁).length S₂).length (L₁.map encW) [] n₁) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₃ * (n₂ * n₁) :=
  card_le_of_index_restrict ws (subsetOf m S₁) (TableFact.genSub_index_sub h₃s hm _ h₃)
    (card_PG_le_chain₂_tf hm₂ hm₁ h₂s h₁s h₂ h₁)

end CFSG.KC.MiscCoset

end
