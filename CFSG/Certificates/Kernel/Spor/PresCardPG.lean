module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Certificates.NativeValidSchreier

public section

namespace CFSG.KS.PresPG

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem card_closure_le_PG {m : ℕ} {ws : List (List (Fin m × Bool))} [Finite (PG m ws)]
    {G : Type*} [Group G] (x : Fin m → G) (h : ∀ w ∈ ws, FreeGroup.lift x (FreeGroup.mk w) = 1) :
    Nat.card (Subgroup.closure (Set.range x)) ≤ Nat.card (PG m ws) := by
  have hr : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift x r = 1 := by
    rintro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact h w hw
  let φ : PG m ws →* G := PresentedGroup.toGroup hr
  have hle : Subgroup.closure (Set.range x) ≤ φ.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hr⟩
  have hs := φ.rangeRestrict_surjective
  have : Finite φ.range := Finite.of_surjective _ hs
  exact (Subgroup.card_le_of_le hle).trans (Nat.card_le_card_of_surjective _ hs)

theorem wordIn_mem_closure {G : Type*} [Group G] (k : ℕ) (gs : ℕ → G) (w : List ℤ) :
    CFSG.Sporadic.Schreier.Tits.wordIn k gs w ∈
      Subgroup.closure (Set.range fun h : Fin k => gs h.val) := by
  unfold CFSG.Sporadic.Schreier.Tits.wordIn Quiver.SchreierGraph.evalWord
  rw [← FreeGroup.range_lift_eq_closure]
  exact ⟨_, rfl⟩

private theorem permOfArr_congr {n : ℕ} {t r u : Array ℕ} (h : isInvA n t r = true)
    (he : ∀ i < n, t[i]! = u[i]!) : permOfArr n t = permOfArr n u := by
  have hc : (∀ i < n, u[i]! < n) ∧ ∀ i < n, ∀ j < n, u[i]! = u[j]! → i = j :=
    ⟨fun i hi => he i hi ▸ (isInvA_spec h hi).1, fun i hi j hj hij => by
      rw [← (isInvA_spec h hi).2, ← (isInvA_spec h hj).2, he i hi, he j hj, hij]⟩
  have hu : Rep n u (permOfArr n u) := fun x => by
    rw [permOfArr, dite_eq_left hc]
    rfl
  have ht : Rep n u (permOfArr n t) := fun x => by
    rw [← he x x.2]
    exact (rep_permOfArr h).1 x
  exact ht.unique hu

private theorem siftA_mem_aux {n : ℕ} {K : Subgroup (Equiv.Perm (Fin n))} {levels : Array Level}
    {base : Array ℕ}
    (hT : ∀ i (hi : i < levels.size), ∀ k < levels[i].pts.size, ∃ T ∈ K,
      Rep n levels[i].tr[k]! T ∧ Rep n levels[i].trInv[k]! T⁻¹) :
    ∀ d l, levels.size - l = d → ∀ (g : Array ℕ) (G : Equiv.Perm (Fin n)), Rep n g G →
      siftA n levels base l g = true → G ∈ K := by
  intro d
  induction d with
  | zero =>
    intro l hl g G hg h
    have hlt : ¬ l < levels.size := by omega
    rw [siftA, dif_neg hlt] at h
    rw [eq_of_eqA hg rep_idA h]
    exact one_mem _
  | succ d ih =>
    intro l hl g G hg h
    have hlt : l < levels.size := by omega
    rw [siftA, dif_pos hlt] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, h⟩ := h
    obtain ⟨T, hTK, -, hr2⟩ := hT l hlt _ hk
    have := ih (l + 1) (by omega) _ (T⁻¹ * G) (rep_compA hr2 hg) h
    simpa using K.mul_mem hTK this

theorem siftA_mem {n chunks : Nat} {O S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} (hc : rawChainOK n O S base W chunks = true) {k : Nat} (hk : O.size = k)
    {g : Array Nat} (hg : isInvA n g (invCand n g) = true)
    (h : siftA n (rawLevels n S base) base 0 g = true) :
    permOfArr n g ∈ Subgroup.closure (Set.range fun j : Fin k => permOfArr n O[j.val]!) := by
  classical
  set K := Subgroup.closure (Set.range fun j : Fin k => permOfArr n O[j.val]!) with hK
  have hF := CFSG.Certificates.chainCheckFacts hc
  set gs : ℕ → Equiv.Perm (Fin n) := fun j => permOfArr n S[j]! with hgs
  have hrepS : ∀ j < S.size, Rep n S[j]! (gs j) :=
    fun j hj => (rep_permOfArr (hF.strong_inv j hj)).1
  have hrepSi : ∀ j < S.size, Rep n (rawInvs n S)[j]! (gs j)⁻¹ :=
    fun j hj => (rep_permOfArr (hF.strong_inv j hj)).2
  have hgsK : ∀ j < S.size, gs j ∈ K := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjk : j < O.size
      · have he := hF.initial j hjk
        have hOj : permOfArr n S[j]! = permOfArr n O[j]! :=
          permOfArr_congr (hF.strong_inv j hj) (fun i hi => by
            have := allLt_spec (n := n) (p := fun i => (S[j]!)[i]! == (O[j]!)[i]!) he hi
            simpa using this)
        show permOfArr n S[j]! ∈ K
        rw [hOj]
        exact Subgroup.subset_closure ⟨⟨j, by omega⟩, rfl⟩
      · obtain ⟨hl, he⟩ := hF.words j hj (by omega)
        have hw := rep_wordA (S := S) (Sinv := rawInvs n S) (gs := gs) (j := j)
          (fun h hh => hrepS h (by omega)) (fun h hh => hrepSi h (by omega)) W[j]! hl
        rw [eq_of_eqA (hrepS j hj) hw he]
        exact CFSG.Sporadic.Schreier.Tits.wordIn_mem (fun i hi => ih i hi (by omega)) _
  have hsteps : ∀ i, ∀ a ∈ rawSteps n S base i, ∃ G ∈ K, Rep n a G := by
    intro i a ha
    simp only [rawSteps, levelSteps, Array.mem_append, List.mem_toArray, List.mem_map] at ha
    have hidx : ∀ j ∈ levelIdx S base i, j < S.size := fun j hj =>
      List.mem_range.1 (List.mem_filter.1 hj).1
    rcases ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨gs j, hgsK j (hidx j hj), hrepS j (hidx j hj)⟩
    · exact ⟨(gs j)⁻¹, inv_mem (hgsK j (hidx j hj)), hrepSi j (hidx j hj)⟩
  have hlev : ∀ i (hi : i < (rawLevels n S base).size), ∀ k < (rawLevels n S base)[i].pts.size,
      ∃ T ∈ K, Rep n (rawLevels n S base)[i].tr[k]! T ∧
        Rep n (rawLevels n S base)[i].trInv[k]! T⁻¹ := by
    intro i hi
    have hib : i < base.size := by simpa [rawLevels] using hi
    have h1 := hF.level i hib
    rw [getElem!_pos (rawLevels n S base) i hi] at h1
    have F := CFSG.Certificates.ChainArrays.levelFacts_of_levelOK h1
    generalize (rawLevels n S base)[i] = L at F ⊢
    have key : ∀ k, k < L.pts.size → ∃ T ∈ K, Rep n L.tr[k]! T := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        have hrep := (rep_permOfArr (F.tr_inv k hk)).1
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [eq_of_eqA hrep rep_idA F.tr_zero] at hrep
          exact ⟨1, one_mem _, hrep⟩
        · have hl := F.lab_lt k hk hk0
          have hmem : (rawSteps n S base i)[L.lab[k]!]! ∈ rawSteps n S base i := by
            rw [getElem!_pos (rawSteps n S base i) _ hl]
            exact Array.getElem_mem hl
          obtain ⟨Gs, hGs, hrs⟩ := hsteps i _ hmem
          have hp := F.par_lt k hk hk0
          obtain ⟨G', hG', hr'⟩ := ih _ hp (by omega)
          have e := eq_of_eqA hrep (rep_compA hrs hr') (F.tr_step k hk hk0)
          rw [e] at hrep
          exact ⟨Gs * G', K.mul_mem hGs hG', hrep⟩
    intro k hk
    obtain ⟨T, hT, hr⟩ := key k hk
    exact ⟨T, hT, hr, rep_inv_of_isInvA hr (F.tr_inv k hk)⟩
  exact siftA_mem_aux hlev _ 0 rfl g _ (rep_permOfArr hg).1 h

end CFSG.KS.PresPG

end
