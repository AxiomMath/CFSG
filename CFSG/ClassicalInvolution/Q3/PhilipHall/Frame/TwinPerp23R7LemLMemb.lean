module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLV4
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.Q3.AE.Bar

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE

variable {k : ℕ}

section PermParts

theorem kList_perm_mem : ∀ m ∈ kList, m.perm ∈ v4List := by decide +kernel

theorem kStarList_perm_mem : ∀ m ∈ kStarList, m.perm ∈ v4List := by decide +kernel

theorem v4List_mem_kList : ∀ δ ∈ v4List, ∃ m ∈ kList, m.perm = δ := by decide +kernel

theorem v4List_mem_kStarList : ∀ δ ∈ v4List, ∃ m ∈ kStarList, m.perm = δ := by decide +kernel

theorem swap_mul_swap_mem_v4List : ∀ i j l m : Fin 4, i ≠ j → i ≠ l → i ≠ m → j ≠ l → j ≠ m → l ≠ m →
    Equiv.swap i j * Equiv.swap l m ∈ v4List := by decide +kernel

theorem memAt_perm (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) :
    ∀ m ∈ memAt α h b, ∃ δ ∈ v4List, m.perm = embedPerm (emb α h) δ := by
  intro m hm
  cases b
  · obtain ⟨m₀, hm₀, rfl⟩ := hm
    exact ⟨m₀.perm, kStarList_perm_mem m₀ hm₀, rfl⟩
  · obtain ⟨m₀, hm₀, rfl⟩ := hm
    exact ⟨m₀.perm, kList_perm_mem m₀ hm₀, rfl⟩

theorem memAt_perm_surj (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) :
    ∀ δ ∈ v4List, ∃ m ∈ memAt α h b, m.perm = embedPerm (emb α h) δ := by
  intro δ hδ
  cases b
  · obtain ⟨m₀, hm₀, hp⟩ := v4List_mem_kStarList δ hδ
    exact ⟨embed (emb α h) m₀, ⟨m₀, hm₀, rfl⟩, by rw [embed_perm, hp]⟩
  · obtain ⟨m₀, hm₀, hp⟩ := v4List_mem_kList δ hδ
    exact ⟨embed (emb α h) m₀, ⟨m₀, hm₀, rfl⟩, by rw [embed_perm, hp]⟩

@[expose] noncomputable def V4S (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) :
    Subgroup (Equiv.Perm (Fin k)) :=
  (memBar α h b).map (TL4.permBar k)

theorem mem_V4S_iff (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) (x : Equiv.Perm (Fin k)) :
    x ∈ V4S α h b ↔ ∃ δ ∈ v4List, x = embedPerm (emb α h) δ := by
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    obtain ⟨δ, hδ, hmδ⟩ := memAt_perm α h b m hm
    exact ⟨δ, hδ, by rw [TL4.permBar_mkQ]; exact hmδ⟩
  · rintro ⟨δ, hδ, rfl⟩
    obtain ⟨m, hm, hmδ⟩ := memAt_perm_surj α h b δ hδ
    exact ⟨mkQ k m, ⟨m, hm, rfl⟩, by rw [TL4.permBar_mkQ]; exact hmδ⟩

theorem V4S_bool (α : Finset (Fin k)) (h : α.card = 4) (b b' : Bool) : V4S α h b = V4S α h b' := by
  ext x
  rw [mem_V4S_iff, mem_V4S_iff]

theorem natCard_V4S_le (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) :
    Nat.card ↥(V4S α h b) ≤ 4 := by
  have hsub : ((V4S α h b : Subgroup (Equiv.Perm (Fin k))) : Set (Equiv.Perm (Fin k))) ⊆
      ↑(v4List.toFinset.image (embedPerm (emb α h))) := by
    intro x hx
    obtain ⟨δ, hδ, rfl⟩ := (mem_V4S_iff α h b x).mp hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    exact ⟨δ, hδ, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : (v4List.toFinset.image (embedPerm (emb α h))).card ≤ 4 :=
    (Finset.card_image_le).trans (List.toFinset_card_le _)
  have h3 : Nat.card ↥(V4S α h b) =
      ((V4S α h b : Subgroup (Equiv.Perm (Fin k))) : Set (Equiv.Perm (Fin k))).ncard :=
    Nat.card_coe_set_eq ((V4S α h b : Subgroup (Equiv.Perm (Fin k))) : Set (Equiv.Perm (Fin k)))
  omega

end PermParts

section Swaps

theorem embedPerm_swap (ι : Fin 4 ↪ Fin k) (i j : Fin 4) :
    embedPerm ι (Equiv.swap i j) = Equiv.swap (ι i) (ι j) := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨l, rfl⟩ := hx
    rw [embedPerm_apply]
    exact (ι.injective.swap_apply i j l).symm
  · rw [embedPerm_of_not_mem ι _ hx]
    symm
    apply Equiv.swap_apply_of_ne_of_ne
    · rintro rfl
      exact hx ⟨i, rfl⟩
    · rintro rfl
      exact hx ⟨j, rfl⟩

theorem embedPerm_d₁ (ι : Fin 4 ↪ Fin k) :
    embedPerm ι d₁ = Equiv.swap (ι 0) (ι 1) * Equiv.swap (ι 2) (ι 3) := by
  rw [d₁, embedPerm_mul, embedPerm_swap, embedPerm_swap]

theorem embedPerm_d₂ (ι : Fin 4 ↪ Fin k) :
    embedPerm ι d₂ = Equiv.swap (ι 0) (ι 2) * Equiv.swap (ι 1) (ι 3) := by
  rw [d₂, embedPerm_mul, embedPerm_swap, embedPerm_swap]

theorem embedPerm_d₃ (ι : Fin 4 ↪ Fin k) :
    embedPerm ι d₃ = Equiv.swap (ι 0) (ι 3) * Equiv.swap (ι 1) (ι 2) := by
  rw [d₃, embedPerm_mul, embedPerm_swap, embedPerm_swap]

theorem swap_mul_swap_mem_V4S (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) {x y z u : Fin k}
    (hx : x ∈ α) (hy : y ∈ α) (hz : z ∈ α) (hu : u ∈ α) (hxy : x ≠ y) (hxz : x ≠ z) (hxu : x ≠ u)
    (hyz : y ≠ z) (hyu : y ≠ u) (hzu : z ≠ u) :
    Equiv.swap x y * Equiv.swap z u ∈ V4S α h b := by
  have hr : ∀ t ∈ α, ∃ i, emb α h i = t := fun t ht => by
    have : t ∈ Set.range (emb α h) := by rw [range_emb]; exact ht
    exact this
  obtain ⟨i, rfl⟩ := hr x hx
  obtain ⟨j, rfl⟩ := hr y hy
  obtain ⟨l, rfl⟩ := hr z hz
  obtain ⟨m, rfl⟩ := hr u hu
  have hne : ∀ {a b' : Fin 4}, emb α h a ≠ emb α h b' → a ≠ b' := fun hab e =>
    hab (congrArg _ e)
  rw [mem_V4S_iff]
  refine ⟨Equiv.swap i j * Equiv.swap l m, ?_, ?_⟩
  · exact swap_mul_swap_mem_v4List i j l m (hne hxy) (hne hxz) (hne hxu) (hne hyz) (hne hyu)
      (hne hzu)
  · rw [embedPerm_mul, embedPerm_swap, embedPerm_swap]

theorem V4S_cases (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) {D : Equiv.Perm (Fin k)}
    (hD : D ∈ V4S α h b) :
    D = 1 ∨ D = Equiv.swap (emb α h 0) (emb α h 1) * Equiv.swap (emb α h 2) (emb α h 3) ∨
      D = Equiv.swap (emb α h 0) (emb α h 2) * Equiv.swap (emb α h 1) (emb α h 3) ∨
      D = Equiv.swap (emb α h 0) (emb α h 3) * Equiv.swap (emb α h 1) (emb α h 2) := by
  obtain ⟨δ, hδ, rfl⟩ := (mem_V4S_iff α h b D).mp hD
  simp only [v4List, List.mem_cons, List.not_mem_nil, or_false] at hδ
  rcases hδ with rfl | rfl | rfl | rfl
  · exact Or.inl (embedPerm_one _)
  · exact Or.inr (Or.inl (embedPerm_d₁ _))
  · exact Or.inr (Or.inr (Or.inl (embedPerm_d₂ _)))
  · exact Or.inr (Or.inr (Or.inr (embedPerm_d₃ _)))

theorem map_univ_emb (α : Finset (Fin k)) (h : α.card = 4) : Finset.univ.map (emb α h) = α := by
  apply Finset.coe_injective
  rw [Finset.coe_map, Finset.coe_univ, Set.image_univ, range_emb]

end Swaps

section Centralizing

theorem perm_comm_of_mkQ_comm {w m : Wr k} (hc : mkQ k w * mkQ k m = mkQ k m * mkQ k w) :
    w.perm * m.perm = m.perm * w.perm := by
  rcases comm_or_of_mkQ_comm hc with h1 | h1
  · have := congrArg Wr.perm h1
    rwa [Wr.mul_perm, Wr.mul_perm] at this
  · have := congrArg Wr.perm h1
    rwa [Wr.mul_perm, Wr.mul_perm, Wr.mul_perm, show (Wr.allOnes k).perm = 1 from rfl, mul_one] at this

theorem commV_of_le_centralizer {α : Finset (Fin k)} {h : α.card = 4} {b : Bool} {w : Wr k}
    (hM : memBar α h b ≤ Subgroup.centralizer ({mkQ k w} : Set (AEQ k))) :
    CommV w.perm (emb α h) := by
  intro δ hδ
  obtain ⟨m, hm, hmδ⟩ := memAt_perm_surj α h b δ hδ
  have hc := (Subgroup.mem_centralizer_singleton_iff.mp (hM ⟨m, hm, rfl⟩)).symm
  rw [← hmδ]
  exact perm_comm_of_mkQ_comm hc

theorem exists_notMem_range_emb (hk : 5 ≤ k) (α : Finset (Fin k)) (h : α.card = 4) :
    ∃ p : Fin k, p ∉ Set.range (emb α h) := by
  have hlt : α.card < (Finset.univ : Finset (Fin k)).card := by
    rw [h, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨p, by rw [range_emb]; exact hp⟩

theorem const_of_le_centralizer (hk : 5 ≤ k) {α : Finset (Fin k)} {h : α.card = 4} {b : Bool}
    {w : Wr k} (hw : w.perm = 1)
    (hM : memBar α h b ≤ Subgroup.centralizer ({mkQ k w} : Set (AEQ k))) :
    ∀ x ∈ α, ∀ y ∈ α, w.vec x = w.vec y := by
  intro x hx y hy
  have hr : ∀ t ∈ α, ∃ i, emb α h i = t := fun t ht => by
    have : t ∈ Set.range (emb α h) := by rw [range_emb]; exact ht
    exact this
  obtain ⟨i, rfl⟩ := hr x hx
  obtain ⟨j, rfl⟩ := hr y hy
  obtain ⟨δ, hδ, hδi⟩ := v4_trans i j
  obtain ⟨m, hm, hmδ⟩ := memAt_perm_surj α h b δ hδ
  have hc := (Subgroup.mem_centralizer_singleton_iff.mp (hM ⟨m, hm, rfl⟩)).symm
  rcases comm_or_of_mkQ_comm hc with h1 | h1
  · have h2 := congrFun (congrArg Wr.vec h1) (emb α h j)
    rw [Wr.mul_vec, Wr.mul_vec, hw, hmδ, embedPerm_symm_apply] at h2
    have h3 : δ.symm j = i := (Equiv.symm_apply_eq δ).mpr hδi.symm
    rw [h3] at h2
    have h4 : (1 : Equiv.Perm (Fin k)).symm (emb α h j) = emb α h j := rfl
    rw [h4, add_comm] at h2
    exact (add_left_cancel h2).symm
  · obtain ⟨p, hp⟩ := exists_notMem_range_emb hk α h
    have hs := supportedOn_of_mem_memAt hm
    have h2 := congrFun (congrArg Wr.vec h1) p
    rw [Wr.mul_vec, Wr.mul_vec, Wr.mul_vec, hw, (hs p hp).1, hs.perm_symm hp,
      show (Wr.allOnes k).vec _ = 1 from rfl] at h2
    have h4 : (1 : Equiv.Perm (Fin k)).symm p = p := rfl
    rw [h4, (hs p hp).1, add_zero, zero_add] at h2
    have h5 : (1 : ZMod 2) = 0 := by
      have h6 : w.vec p + 1 = w.vec p + 0 := by rw [add_zero]; exact h2.symm
      exact add_left_cancel h6
    exact absurd h5 (by decide)

theorem le_centralizer_of_const {α : Finset (Fin k)} {h : α.card = 4} {b : Bool} {w : Wr k}
    (hw : w.perm = 1) (hconst : ∀ x ∈ α, ∀ y ∈ α, w.vec x = w.vec y) :
    memBar α h b ≤ Subgroup.centralizer ({mkQ k w} : Set (AEQ k)) := by
  rintro _ ⟨m, hm, rfl⟩
  have hs := supportedOn_of_mem_memAt hm
  have hmw : w * m = m * w := by
    refine Wr.ext (funext fun p => ?_) ?_
    · rw [Wr.mul_vec, Wr.mul_vec, hw]
      have h4 : (1 : Equiv.Perm (Fin k)).symm p = p := rfl
      rw [h4]
      have hvec : w.vec (m.perm.symm p) = w.vec p := by
        by_cases hp : p ∈ Set.range (emb α h)
        · refine hconst _ ?_ _ ?_
          · have := hs.perm_mem hp
            rw [range_emb] at this
            exact this
          · rw [range_emb] at hp
            exact hp
        · rw [hs.perm_symm hp]
      rw [hvec, add_comm]
    · rw [Wr.mul_perm, Wr.mul_perm, hw, one_mul, mul_one]
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hmw]

end Centralizing

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
