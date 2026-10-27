module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympLevi

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open SymplecticHigher (flagStabilizer mem_flagStabilizer)

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

@[expose] noncomputable def spFlagLeviCoord (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)
    (j : Fin (r + 1)) : flagStabilizer r K I →* StatedSp r K := by
  classical
  exact if (j : ℕ) = 0 then (spFlagResEmb t).comp (spFlagResHom hI htI)
    else if hj : (j : ℕ) ∈ I then
      (spFlagCutEmb (spFlagPrev I j) j (hI j hj)).comp (spFlagCutHom hI (spFlagPrev_mem I j) hj)
    else 1

@[expose] noncomputable def spFlagLeviBlock (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) (j : Fin (r + 1)) :
    Subgroup (StatedSp r K) := by
  classical
  exact if (j : ℕ) = 0 then (commutator (StatedSp (r - t) K)).map (spFlagResEmb t)
    else if hj : (j : ℕ) ∈ I then
      ((spFlagCutEmb (spFlagPrev I j) j (hI j hj)).comp Matrix.SpecialLinearGroup.toGL).range
    else ⊥

@[expose] noncomputable def spFlagLeviHom (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I) :
    flagStabilizer r K I →* (Fin (r + 1) → StatedSp r K) :=
  MonoidHom.pi (spFlagLeviCoord hI htI)

variable (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)

theorem spFlagLeviCoord_of_eq_zero {j : Fin (r + 1)} (hj : (j : ℕ) = 0) :
    spFlagLeviCoord (K := K) hI htI j = (spFlagResEmb t).comp (spFlagResHom hI htI) := by
  classical
  simp only [spFlagLeviCoord, hj, ↓reduceIte]

theorem spFlagLeviCoord_of_mem {j : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I) :
    spFlagLeviCoord (K := K) hI htI j = (spFlagCutEmb (spFlagPrev I j) j (hI j hj)).comp
      (spFlagCutHom hI (spFlagPrev_mem I j) hj) := by
  classical
  simp only [spFlagLeviCoord, hj0, hj, ↓reduceIte, ↓reduceDIte]

theorem spFlagLeviCoord_of_not_mem {j : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∉ I) :
    spFlagLeviCoord (K := K) hI htI j = 1 := by
  classical
  simp only [spFlagLeviCoord, hj0, hj, ↓reduceIte, ↓reduceDIte]

theorem spFlagLeviBlock_of_eq_zero {j : Fin (r + 1)} (hj : (j : ℕ) = 0) :
    spFlagLeviBlock (K := K) hI t j = (commutator (StatedSp (r - t) K)).map (spFlagResEmb t) := by
  classical
  simp only [spFlagLeviBlock, hj, ↓reduceIte]

theorem spFlagLeviBlock_of_mem {j : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I) :
    spFlagLeviBlock (K := K) hI t j =
      ((spFlagCutEmb (spFlagPrev I j) j (hI j hj)).comp Matrix.SpecialLinearGroup.toGL).range := by
  classical
  simp only [spFlagLeviBlock, hj0, hj, ↓reduceIte, ↓reduceDIte]

theorem spFlagLeviBlock_of_not_mem {j : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∉ I) :
    spFlagLeviBlock (K := K) hI t j = ⊥ := by
  classical
  simp only [spFlagLeviBlock, hj0, hj, ↓reduceIte, ↓reduceDIte]

theorem isPGroup_ker_spFlagLeviHom [Finite K] [CharP K 2] (hI1 : ∀ i ∈ I, 1 ≤ i) :
    IsPGroup 2 (spFlagLeviHom (K := K) hI htI).ker := by
  rintro ⟨g, hg⟩
  have hcoord : ∀ j, spFlagLeviCoord hI htI j g = 1 := fun j =>
    congrFun (MonoidHom.mem_ker.mp hg) j
  have hres : spFlagResMat t (mat r K g) = 1 := by
    have h := hcoord 0
    rw [spFlagLeviCoord_of_eq_zero hI htI rfl, MonoidHom.comp_apply,
      ← map_one (spFlagResEmb (r := r) (K := K) t)] at h
    rw [← mat_spFlagResHom hI htI, spFlagResEmb_injective t h, map_one]
  have hcut : ∀ (b : ℕ) (hb : b ∈ I),
      spFlagCutMat (spFlagPrev I b) b (hI b hb) (mat r K g) = 1 := by
    intro b hb
    have h := hcoord ⟨b, by have := hI b hb; omega⟩
    rw [spFlagLeviCoord_of_mem hI htI (by have := hI1 b hb; simp; omega) hb, MonoidHom.comp_apply,
      ← map_one (spFlagCutEmb (K := K) (spFlagPrev I b) b (hI b hb))] at h
    rw [← coe_spFlagCutHom hI (spFlagPrev_mem I b) hb, spFlagCutEmb_injective _ _ _ h,
      Units.val_one]
  obtain ⟨n, hn⟩ := isPGroup_spFlag_unipotent (r := r) (K := K)
    ⟨g, mem_unipotent_of_blocks hI htI g.2 hcut hres⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hn
  simpa using this

theorem spFlagResHom_resEmb (hmax : ∀ c ∈ I, c ≤ t) (c : StatedSp (r - t) K) :
    spFlagResHom hI htI ⟨spFlagResEmb t c, spFlagResEmb_mem hI hmax c⟩ = c :=
  mat_injective (by rw [mat_spFlagResHom]; exact spFlagResMat_spFlagResEmb t c)

theorem spFlagLeviCoord_resEmb (hmax : ∀ c ∈ I, c ≤ t) (c : StatedSp (r - t) K)
    (j : Fin (r + 1)) :
    spFlagLeviCoord hI htI j ⟨spFlagResEmb t c, spFlagResEmb_mem hI hmax c⟩ =
      if (j : ℕ) = 0 then spFlagResEmb t c else 1 := by
  by_cases hj0 : (j : ℕ) = 0
  · rw [spFlagLeviCoord_of_eq_zero hI htI hj0, MonoidHom.comp_apply,
      spFlagResHom_resEmb hI htI hmax c, ite_eq_left hj0]
  rw [ite_eq_right hj0]
  by_cases hj : (j : ℕ) ∈ I
  · rw [spFlagLeviCoord_of_mem hI htI hj0 hj, MonoidHom.comp_apply]
    have h1 : spFlagCutHom hI (spFlagPrev_mem I j) hj
        ⟨spFlagResEmb t c, spFlagResEmb_mem hI hmax c⟩ = 1 :=
      Units.ext (by
        rw [coe_spFlagCutHom]
        exact spFlagCutMat_spFlagResEmb _ (hmax _ hj) c)
    rw [h1, map_one]
  · rw [spFlagLeviCoord_of_not_mem hI htI hj0 hj, MonoidHom.one_apply]

theorem le_spFlagPrev_or_le {b c : ℕ} (hc : c ∈ I) : c ≤ spFlagPrev I b ∨ b ≤ c := by
  by_cases hcb : c < b
  · exact Or.inl (le_spFlagPrev hc hcb)
  · exact Or.inr (not_lt.mp hcb)

theorem spFlagLeviCoord_cutEmb (hmax : ∀ c ∈ I, c ≤ t) {b : ℕ} (hb : b ∈ I) (hb1 : 1 ≤ b)
    (A : GL (Fin (b - spFlagPrev I b)) K) (j : Fin (r + 1)) :
    spFlagLeviCoord hI htI j ⟨spFlagCutEmb (spFlagPrev I b) b (hI b hb) A,
        spFlagCutEmb_mem hI _ (fun _ hc => le_spFlagPrev_or_le hc) A⟩ =
      if (j : ℕ) = b then spFlagCutEmb (spFlagPrev I b) b (hI b hb) A else 1 := by
  set g : flagStabilizer r K I := ⟨spFlagCutEmb (spFlagPrev I b) b (hI b hb) A,
    spFlagCutEmb_mem hI _ (fun _ hc => le_spFlagPrev_or_le hc) A⟩
  have hprev := spFlagPrev_le I b
  by_cases hj0 : (j : ℕ) = 0
  · rw [spFlagLeviCoord_of_eq_zero hI htI hj0, MonoidHom.comp_apply]
    have h1 : spFlagResHom hI htI g = 1 := by
      refine mat_injective ?_
      rw [mat_spFlagResHom, map_one]
      exact spFlagResMat_spFlagCutEmb _ (hmax b hb) A
    rw [h1, map_one, ite_eq_right (by omega)]
  by_cases hj : (j : ℕ) ∈ I
  · rw [spFlagLeviCoord_of_mem hI htI hj0 hj, MonoidHom.comp_apply]
    by_cases hjb : (j : ℕ) = b
    · rw [ite_eq_left hjb]
      subst hjb
      have h1 : spFlagCutHom hI (spFlagPrev_mem I _) hj g = A := by
        refine Units.ext ?_
        rw [coe_spFlagCutHom]
        exact spFlagCutMat_spFlagCutEmb _ _ _ A
      rw [h1]
    · rw [ite_eq_right hjb]
      have hd : (j : ℕ) ≤ spFlagPrev I b ∨ b ≤ spFlagPrev I j := by
        rcases lt_or_gt_of_ne hjb with h | h
        · exact Or.inl (le_spFlagPrev hj h)
        · exact Or.inr (le_spFlagPrev hb h)
      have h1 : spFlagCutHom hI (spFlagPrev_mem I j) hj g = 1 :=
        Units.ext (by
          rw [coe_spFlagCutHom, Units.val_one]
          exact spFlagCutMat_spFlagCutEmb_of_disjoint _ _ hd A)
      rw [h1, map_one]
  · rw [spFlagLeviCoord_of_not_mem hI htI hj0 hj, MonoidHom.one_apply, ite_eq_right]
    rintro rfl
    exact hj hb

theorem pi_le_range_spFlagLeviHom (hmax : ∀ c ∈ I, c ≤ t) :
    Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI t) ≤ (spFlagLeviHom hI htI).range := by
  classical
  rw [Subgroup.pi_le_iff]
  intro j
  rintro _ ⟨s, hs, rfl⟩
  by_cases hj0 : (j : ℕ) = 0
  · rw [spFlagLeviBlock_of_eq_zero hI hj0] at hs
    obtain ⟨c, -, rfl⟩ := hs
    refine ⟨⟨spFlagResEmb t c, spFlagResEmb_mem hI hmax c⟩, funext fun i => ?_⟩
    rw [spFlagLeviHom, MonoidHom.pi_apply, spFlagLeviCoord_resEmb hI htI hmax,
      MonoidHom.mulSingle_apply]
    by_cases hi : (i : ℕ) = 0
    · rw [ite_eq_left hi, show i = j from Fin.ext (hi.trans hj0.symm), Pi.mulSingle_eq_same]
    · rw [ite_eq_right hi, Pi.mulSingle_eq_of_ne (fun h => hi (by rw [h]; exact hj0))]
  by_cases hj : (j : ℕ) ∈ I
  · rw [spFlagLeviBlock_of_mem hI hj0 hj] at hs
    obtain ⟨A, rfl⟩ := hs
    have hjr : (j : ℕ) ≤ r := hI _ hj
    refine ⟨⟨spFlagCutEmb (spFlagPrev I j) j (hI j hj) (Matrix.SpecialLinearGroup.toGL A),
      spFlagCutEmb_mem hI _ (fun _ hc => le_spFlagPrev_or_le hc) _⟩, funext fun i => ?_⟩
    rw [spFlagLeviHom, MonoidHom.pi_apply, spFlagLeviCoord_cutEmb hI htI hmax hj (by omega),
      MonoidHom.mulSingle_apply, MonoidHom.comp_apply]
    by_cases hi : (i : ℕ) = (j : ℕ)
    · rw [ite_eq_left hi, show i = j from Fin.ext hi, Pi.mulSingle_eq_same]
    · rw [ite_eq_right hi, Pi.mulSingle_eq_of_ne (fun h => hi (by rw [h]))]
  · rw [spFlagLeviBlock_of_not_mem hI hj0 hj, SetLike.mem_coe, Subgroup.mem_bot] at hs
    rw [hs, map_one]
    exact one_mem _

theorem commutator_le_range_toGL (n : ℕ) :
    commutator (GL (Fin n) K) ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin n) (R := K)).range := by
  intro g hg
  have h1 := Abelianization.commutator_subset_ker Matrix.GeneralLinearGroup.det hg
  exact ⟨⟨g, by simpa [Units.ext_iff] using MonoidHom.mem_ker.mp h1⟩, by ext; rfl⟩

theorem commutator_range_spFlagLeviHom_le :
    ⁅(spFlagLeviHom (K := K) hI htI).range, (spFlagLeviHom (K := K) hI htI).range⁆ ≤
      Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI t) := by
  intro x hx
  rw [Subgroup.mem_pi]
  intro j _
  have hxj : x j ∈ ⁅(spFlagLeviCoord (K := K) hI htI j).range,
      (spFlagLeviCoord (K := K) hI htI j).range⁆ := by
    have h := Subgroup.mem_map_of_mem (Pi.evalMonoidHom (fun _ : Fin (r + 1) => StatedSp r K) j)
      hx
    rwa [Subgroup.map_commutator, MonoidHom.map_range] at h
  by_cases hj0 : (j : ℕ) = 0
  · rw [spFlagLeviBlock_of_eq_zero hI hj0, commutator_def, Subgroup.map_commutator]
    rw [spFlagLeviCoord_of_eq_zero hI htI hj0] at hxj
    refine Subgroup.commutator_mono ?_ ?_ hxj <;>
    · rw [MonoidHom.range_comp, ← MonoidHom.range_eq_map]
      exact Subgroup.map_le_range _ _
  by_cases hj : (j : ℕ) ∈ I
  · rw [spFlagLeviBlock_of_mem hI hj0 hj, MonoidHom.range_comp]
    rw [spFlagLeviCoord_of_mem hI htI hj0 hj] at hxj
    have hle : ((spFlagCutEmb (K := K) (spFlagPrev I j) j (hI j hj)).comp
        (spFlagCutHom hI (spFlagPrev_mem I j) hj)).range ≤
        (⊤ : Subgroup (GL (Fin (j - spFlagPrev I j)) K)).map (spFlagCutEmb (spFlagPrev I j) j
          (hI j hj)) := by
      rw [MonoidHom.range_comp]
      exact Subgroup.map_mono le_top
    have h2 := Subgroup.commutator_mono hle hle hxj
    rw [← Subgroup.map_commutator, ← commutator_def] at h2
    exact Subgroup.map_mono (commutator_le_range_toGL _) h2
  · rw [spFlagLeviCoord_of_not_mem hI htI hj0 hj, MonoidHom.range_one,
      Subgroup.commutator_bot_left] at hxj
    rw [spFlagLeviBlock_of_not_mem hI hj0 hj]
    exact hxj

end CFSG.AGLEmbedding.LeviBlock
