module

public import Certificates.Certificate55114
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

variable {n : ℕ}

theorem ae117_check :
    (adjCheck 5 () = true ∧ adjCheck 6 () = true ∧ adjCheck 7 () = true) ∧
      (cocCheck₅ () = true ∧ cocCheck₆ () = true ∧ cocCheck₇ () = true) ∧
      (genCheck₅ () = true ∧ genCheck₆ () = true ∧ genCheck₇ () = true) ∧
      (spanCheck 5 () = true ∧ spanCheck 6 () = true ∧ spanCheck 7 () = true) :=
  Certificates.certificate55114

theorem inPi_iff (x : Wr n) : inPi x = true ↔ mkQ n x = 1 := by
  rw [show mkQ n x = 1 ↔ x ∈ piSub n from QuotientGroup.eq_one_iff x, mem_piSub]
  simp [inPi]

theorem eqPi_iff (x y : Wr n) : eqPi x y = true ↔ mkQ n x = mkQ n y := by
  have hπ : (allOnes n)⁻¹ = allOnes n := inv_eq_of_mul_eq_one_right (allOnes_mul_self n)
  simp only [eqPi, Bool.or_eq_true, decide_eq_true_eq, mkQ_eq_iff]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (inv_mul_cancel x)
    · right
      rw [mul_inv_rev, hπ, mul_assoc, inv_mul_cancel, mul_one]
  · rintro (h | h)
    · exact Or.inl (inv_mul_eq_one.mp h)
    · right
      have hy : y = x * allOnes n := by rw [← h]; group
      rw [hy, mul_assoc, allOnes_mul_self, mul_one]

theorem ord5Pi_iff (x : Wr n) : ord5Pi x = true ↔ orderOf (mkQ n x) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  unfold ord5Pi
  rw [Bool.and_eq_true, inPi_iff (x ^ 5), map_pow]
  constructor
  · rintro ⟨hx, h5⟩
    refine orderOf_eq_prime h5 fun h1 => ?_
    rw [← inPi_iff] at h1
    rw [h1] at hx
    exact absurd hx (by decide)
  · intro h
    refine ⟨?_, by rw [← h]; exact pow_orderOf_eq_one _⟩
    cases hp : inPi x
    · rfl
    · rw [inPi_iff] at hp
      rw [hp, orderOf_one] at h
      omega

theorem indL_nil : indL ([] : List (Fin n)) = 0 := funext fun i => by simp [indL]

theorem one_eq_mk : (1 : Wr 4) = ⟨vec4 [], 1⟩ := Wr.ext (funext fun i => by simp [vec4]; rfl) rfl

theorem embedVec_vec4 (ι : Fin 4 ↪ Fin n) (s : List (Fin 4)) :
    embedVec ι (vec4 s) = indL (s.map ι) := by
  classical
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedVec_apply]
    simp only [vec4, indL, List.mem_map, ι.injective.eq_iff, exists_eq_right]
  · rw [embedVec_of_not_mem ι _ hx]
    simp only [indL, List.mem_map]
    split_ifs with h2
    · obtain ⟨i, -, rfl⟩ := h2
      exact absurd ⟨i, rfl⟩ hx
    · rfl

theorem embedPerm_swap (ι : Fin 4 ↪ Fin n) (i j : Fin 4) :
    embedPerm ι (Equiv.swap i j) = Equiv.swap (ι i) (ι j) := by
  classical
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨k, rfl⟩ := hx
    rw [embedPerm_apply, ι.injective.map_swap]
  · rw [embedPerm_of_not_mem ι _ hx, Equiv.swap_apply_of_ne_of_ne] <;> rintro rfl <;>
      exact hx ⟨_, rfl⟩

theorem embed_mk (ι : Fin 4 ↪ Fin n) (s : List (Fin 4)) (σ : Equiv.Perm (Fin 4)) :
    embed ι ⟨vec4 s, σ⟩ = ⟨indL (s.map ι), embedPerm ι σ⟩ :=
  Wr.ext (embedVec_vec4 ι s) rfl

theorem embedPerm_d₁ (ι : Fin 4 ↪ Fin n) :
    embedPerm ι d₁ = Equiv.swap (ι 0) (ι 1) * Equiv.swap (ι 2) (ι 3) := by
  rw [d₁, embedPerm_mul, embedPerm_swap, embedPerm_swap]

theorem embedPerm_d₂ (ι : Fin 4 ↪ Fin n) :
    embedPerm ι d₂ = Equiv.swap (ι 0) (ι 2) * Equiv.swap (ι 1) (ι 3) := by
  rw [d₂, embedPerm_mul, embedPerm_swap, embedPerm_swap]

theorem embedPerm_d₃ (ι : Fin 4 ↪ Fin n) :
    embedPerm ι d₃ = Equiv.swap (ι 0) (ι 3) * Equiv.swap (ι 1) (ι 2) := by
  rw [d₃, embedPerm_mul, embedPerm_swap, embedPerm_swap]

theorem memLC_eq (ι : Fin 4 ↪ Fin n) (b : Bool) :
    memLC (ι 0) (ι 1) (ι 2) (ι 3) b = (if b then kList else kStarList).map (embed ι) := by
  have h1 : embed ι 1 = ⟨indL [], 1⟩ := by rw [map_one, indL_nil]; rfl
  cases b <;>
    simp only [memLC, kList, kStarList, zQ, List.map_cons, List.map_nil, h1, embed_mk,
      embedPerm_d₁, embedPerm_d₂, embedPerm_d₃, embedPerm_one, Bool.false_eq_true, ↓reduceIte]

theorem sort_eq (α : Finset (Fin n)) (h : α.card = 4) :
    α.sort (· ≤ ·) = [emb α h 0, emb α h 1, emb α h 2, emb α h 3] := by
  have hl : (α.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort, h]
  apply List.ext_getElem (by rw [hl]; rfl)
  intro i h1 h2
  have hi : i < 4 := by rw [hl] at h1; exact h1
  interval_cases i <;> simp [emb, Finset.orderEmbOfFin_apply]

theorem memAtL_eq (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    memAtL α b = (if b then kList else kStarList).map (embed (emb α h)) := by
  rw [← memLC_eq, memAtL, sort_eq α h]

theorem mem_memBar_iff (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) (x : AEQ n) :
    x ∈ memBar α h b ↔ ∃ a ∈ memAtL α b, mkQ n a = x := by
  rw [memAtL_eq α h b]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨_, hmem, rfl⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
    exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨_, hmem, rfl⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
    exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

theorem evalG_foldl_map {G H : Type*} [Group G] [Group H] (f : G →* H) (gens : List G)
    (w : List ℕ) (acc : G) :
    f (w.foldl (fun acc k =>
        acc * if k % 2 = 0 then gens.getD (k / 2) 1 else (gens.getD (k / 2) 1)⁻¹) acc) =
      w.foldl (fun acc k => acc * if k % 2 = 0 then (gens.map f).getD (k / 2) 1
        else ((gens.map f).getD (k / 2) 1)⁻¹) (f acc) := by
  induction w generalizing acc with
  | nil => rfl
  | cons k w ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    have hget : ∀ o : Option G, (o.map f).getD 1 = f (o.getD 1) := by
      intro o
      cases o <;> simp
    split_ifs <;> simp [hget]

theorem evalG_map {G H : Type*} [Group G] [Group H] (f : G →* H) (gens : List G) (w : List ℕ) :
    f (evalG gens w) = evalG (gens.map f) w := by
  unfold evalG
  rw [evalG_foldl_map, map_one]

@[expose] def AdjInv (n : ℕ) : Prop :=
  ∀ (α : Finset (Fin n)) (h : α.card = 4) (α' : Finset (Fin n)) (h' : α'.card = 4),
    (α ∩ α').card = 3 ↔ ∃ b b' : Bool, ∃ k ∈ memBar α h b, ∃ k' ∈ memBar α' h' b',
      orderOf (k * k') = 5

theorem adjInv_of_check (hc : adjCheck n () = true) : AdjInv n := by
  have hP : adjProp n := of_decide_eq_true hc
  intro α h α' h'
  rw [hP α (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h⟩) α'
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h'⟩)]
  constructor
  · rintro ⟨b, -, b', -, k, hk, k', hk', h5⟩
    refine ⟨b, b', mkQ n k, (mem_memBar_iff α h b _).mpr ⟨k, hk, rfl⟩, mkQ n k',
      (mem_memBar_iff α' h' b' _).mpr ⟨k', hk', rfl⟩, ?_⟩
    rw [← map_mul, ← ord5Pi_iff]
    exact h5
  · rintro ⟨b, b', x, hx, x', hx', h5⟩
    obtain ⟨k, hk, rfl⟩ := (mem_memBar_iff α h b x).mp hx
    obtain ⟨k', hk', rfl⟩ := (mem_memBar_iff α' h' b' x').mp hx'
    refine ⟨b, by cases b <;> simp, b', by cases b' <;> simp, k, hk, k', hk', ?_⟩
    rw [ord5Pi_iff, map_mul]
    exact h5

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
