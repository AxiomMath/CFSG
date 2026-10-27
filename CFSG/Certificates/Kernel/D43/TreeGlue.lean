module

public import CFSG.Certificates.Kernel.D43.TreeSound
public import CFSG.Milestones.ASVolI.F48.Small.Pres

public section

namespace CFSG.KC.D43

open CFSG.ASVolI

variable {G : Type*} [Group G]

@[expose] def digW (l : Fin 8 × Bool) : ℕ := if l.2 then l.1.val + 1 else l.1.val + 9

@[expose] def encW (w : List (Fin 8 × Bool)) : ℕ := w.foldl (fun acc l => acc * 32 + digW l) 0

theorem encW_append (w : List (Fin 8 × Bool)) (l : Fin 8 × Bool) :
    encW (w ++ [l]) = encW w * 32 + digW l := by
  simp [encW, List.foldl_append]

theorem dG_digW (γ : ℕ → G) (l : Fin 8 × Bool) :
    dG γ (digW l) = cond l.2 (γ l.1) (γ l.1)⁻¹ := by
  obtain ⟨k, b⟩ := l
  have hk := k.2
  cases b
  · simp only [digW, Bool.false_eq_true, if_false, cond_false, dG]
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
  · simp only [digW, if_true, cond_true, dG]
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]

theorem wG_encW (γ : ℕ → G) (w : List (Fin 8 × Bool)) :
    ∀ f, w.length ≤ f → wG γ f (encW w) = burnsideF48s_ev (fun k : Fin 8 => γ k) w := by
  induction w using List.reverseRecOn with
  | nil =>
    intro f _
    cases f <;> rfl
  | append_singleton w l ih =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hd1 : 1 ≤ digW l := by unfold digW; split <;> omega
    have hd2 : digW l < 32 := by unfold digW; have := l.1.2; split <;> omega
    have e1 : (encW w * 32 + digW l) / 32 = encW w := by omega
    have e2 : (encW w * 32 + digW l) % 32 = digW l := by omega
    rw [encW_append, wG, if_neg (by omega), e1, e2, ih f (by simp at hf; omega), dG_digW,
      burnsideF48s_ev_append]
    simp [burnsideF48s_ev]

variable [MulAction G (Fin 26572)]

theorem le_ncard_orbit_of_trees {F W R Q : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ)
    {ℓ o s b M C : ℕ} (hs : s ≤ 256 * C) (hb : b < 26572)
    (h : ∀ c < C, treeChunk F W R Q ℓ o s b M c = true) :
    s ≤ (MulAction.orbit ↥(maskGroup γ W M) (⟨b, hb⟩ : Fin 26572)).ncard := by
  obtain ⟨hlt, hinj, hmem⟩ := treeChunks_spec hγ hs hb h
  let f : ℕ → Fin 26572 := fun t => ⟨ptAt R o t % 26572, Nat.mod_lt _ (by norm_num)⟩
  have hf : ∀ t < s, ((f t : Fin 26572) : ℕ) = ptAt R o t := fun t ht =>
    Nat.mod_eq_of_lt (hlt t ht)
  have hsub : (((Finset.range s).image f : Finset (Fin 26572)) : Set (Fin 26572)) ⊆
      MulAction.orbit ↥(maskGroup γ W M) (⟨b, hb⟩ : Fin 26572) := by
    intro q hq
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    obtain ⟨g, hg, hgt⟩ := hmem t ht
    exact ⟨⟨g, hg⟩, Fin.ext (by rw [hf t ht]; exact hgt)⟩
  have hcard : ((Finset.range s).image f).card = s := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro t ht t' ht' he
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    exact hinj t ht t' ht' (by rw [← hf t ht, ← hf t' ht', he])
  calc s = (((Finset.range s).image f : Finset (Fin 26572)) : Set (Fin 26572)).ncard := by
        rw [Set.ncard_coe_finset, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem maskGroup_eq {W : ℕ → ℕ} {γ : ℕ → G} {M : ℕ} (hM : M < 2 ^ 17) {S : Finset (Fin 17)}
    (hS : ∀ j : Fin 17, M.testBit j = true ↔ j ∈ S) {f : Fin 17 → G}
    (hf : ∀ j : Fin 17, lG γ W j = f j) :
    maskGroup γ W M = Subgroup.closure (f '' ↑S) := by
  unfold maskGroup
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj17 : j < 17 := by
      by_contra hc
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num)
        (by omega)))] at hj
      exact Bool.false_ne_true hj
    exact ⟨⟨j, hj17⟩, (hS ⟨j, hj17⟩).1 hj, (hf ⟨j, hj17⟩).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, (hS j).2 hj, (hf j).symm⟩

end CFSG.KC.D43

end
