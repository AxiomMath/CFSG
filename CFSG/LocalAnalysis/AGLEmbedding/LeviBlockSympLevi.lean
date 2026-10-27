module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympBlocks
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed spEmbedMat mat_spEmbed
  spEmbedMat_apply_image spEmbedMat_apply_of_not_mem)
open SymplecticHigher (flagStabilizer mem_flagStabilizer)

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spFlagPrev (I : Set ℕ) (b : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (· ∈ I) (b - 1)

theorem spFlagPrev_le (I : Set ℕ) (b : ℕ) : spFlagPrev I b ≤ b - 1 := by
  classical
  exact Nat.findGreatest_le _

theorem spFlagPrev_mem (I : Set ℕ) (b : ℕ) : spFlagPrev I b = 0 ∨ spFlagPrev I b ∈ I := by
  classical
  by_cases h : spFlagPrev I b = 0
  · exact Or.inl h
  · exact Or.inr (Nat.findGreatest_of_ne_zero rfl h)

theorem le_spFlagPrev {I : Set ℕ} {b c : ℕ} (hc : c ∈ I) (hcb : c < b) : c ≤ spFlagPrev I b := by
  classical
  exact Nat.le_findGreatest (by omega) hc

@[expose] noncomputable def spFlagCutEmb (a b : ℕ) (hb : b ≤ r) :
    GL (Fin (b - a)) K →* StatedSp r K :=
  (spEmbed (spFlagShift a b hb) (spFlagShift_injective a b hb)).comp SymplecticTorusWeyl.leviSp

@[expose] noncomputable def spFlagResEmb (t : ℕ) : StatedSp (r - t) K →* StatedSp r K :=
  spEmbed (spFlagShift t r le_rfl) (spFlagShift_injective t r le_rfl)

theorem mat_spFlagCutEmb (a b : ℕ) (hb : b ≤ r) (A : GL (Fin (b - a)) K) :
    mat r K (spFlagCutEmb a b hb A) = spEmbedMat (spFlagShift a b hb)
      (fromBlocks (A : Matrix (Fin (b - a)) (Fin (b - a)) K) 0 0
        ((A⁻¹ : GL (Fin (b - a)) K) : Matrix (Fin (b - a)) (Fin (b - a)) K)ᵀ) := by
  rw [spFlagCutEmb, MonoidHom.comp_apply, mat_spEmbed, mat_apply, SymplecticTorusWeyl.coe_leviSp]

theorem spFlagResEmb_injective (t : ℕ) : Function.Injective (spFlagResEmb (r := r) (K := K) t) :=
  CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbed_injective _

theorem spFlagCutEmb_injective (a b : ℕ) (hb : b ≤ r) :
    Function.Injective (spFlagCutEmb (K := K) a b hb) := by
  intro A B h
  have h1 := congrArg (fun g => spFlagCutMat a b hb (mat r K g)) h
  apply Units.ext
  have key : ∀ C : GL (Fin (b - a)) K,
      spFlagCutMat a b hb (mat r K (spFlagCutEmb a b hb C)) = (C : Matrix _ _ K) := by
    intro C
    rw [mat_spFlagCutEmb]
    ext i j
    exact (spEmbedMat_apply_image (spFlagShift_injective a b hb) _ (Sum.inl i) (Sum.inl j)).trans
      (by simp)
  simpa [key] using h1

theorem spFlag_submatrix_spEmbedMat {m : ℕ} {σ : Fin m → Fin r}
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) {ι : Type*} [DecidableEq ι]
    {e : ι → Fin r ⊕ Fin r} (he : Function.Injective e)
    (hσe : ∀ i, e i ∉ Set.range (Sum.map σ σ)) : (spEmbedMat σ g).submatrix e e = 1 := by
  ext i j
  rw [submatrix_apply, spEmbedMat_apply_of_not_mem _ (fun h => hσe i h.1)]
  simp only [one_apply, he.eq_iff]

theorem lt_of_mem_range_spFlagShift_map {a b : ℕ} (hb : b ≤ r) {k : Fin r ⊕ Fin r}
    (hk : k ∈ Set.range (Sum.map (spFlagShift a b hb) (spFlagShift a b hb))) :
    ∃ j : Fin r, a ≤ (j : ℕ) ∧ (j : ℕ) < b ∧ (k = Sum.inl j ∨ k = Sum.inr j) := by
  obtain ⟨x | x, rfl⟩ := hk
  · have := x.isLt
    exact ⟨_, by simp [coe_spFlagShift], by simp [coe_spFlagShift]; omega, Or.inl rfl⟩
  · have := x.isLt
    exact ⟨_, by simp [coe_spFlagShift], by simp [coe_spFlagShift]; omega, Or.inr rfl⟩

theorem spFlagCutMat_spFlagCutEmb (a b : ℕ) (hb : b ≤ r) (A : GL (Fin (b - a)) K) :
    spFlagCutMat a b hb (mat r K (spFlagCutEmb a b hb A)) = A := by
  rw [mat_spFlagCutEmb]
  ext i j
  exact (spEmbedMat_apply_image (spFlagShift_injective a b hb) _ (Sum.inl i) (Sum.inl j)).trans
    (by simp)

theorem spFlagCutMat_spFlagCutEmb_of_disjoint {a b a' b' : ℕ} (hb : b ≤ r) (hb' : b' ≤ r)
    (hd : b' ≤ a ∨ b ≤ a') (A : GL (Fin (b - a)) K) :
    spFlagCutMat a' b' hb' (mat r K (spFlagCutEmb a b hb A)) = 1 := by
  rw [mat_spFlagCutEmb]
  refine spFlag_submatrix_spEmbedMat _ (Sum.inl_injective.comp (spFlagShift_injective _ _ _))
    fun i h => ?_
  obtain ⟨j, h1, h2, hj⟩ := lt_of_mem_range_spFlagShift_map hb h
  have hi := i.isLt
  rcases hj with hj | hj
  · simp only [Function.comp_apply, Sum.inl.injEq] at hj
    have := congrArg Fin.val hj
    simp only [coe_spFlagShift] at this
    omega
  · exact Sum.inl_ne_inr hj

theorem spFlagResMat_spFlagCutEmb {a b t : ℕ} (hb : b ≤ r) (hbt : b ≤ t)
    (A : GL (Fin (b - a)) K) : spFlagResMat t (mat r K (spFlagCutEmb a b hb A)) = 1 := by
  rw [mat_spFlagCutEmb]
  refine spFlag_submatrix_spEmbedMat _ (spFlagResIdx_injective t) fun α h => ?_
  obtain ⟨j, -, h2, hj⟩ := lt_of_mem_range_spFlagShift_map hb h
  rcases spFlagResIdx_cases t α with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi] at hj <;>
    rcases hj with hj | hj <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hj <;>
    · have := congrArg Fin.val hj
      simp only [coe_spFlagShift] at this
      omega

theorem spFlagResMat_spFlagResEmb (t : ℕ) (M : StatedSp (r - t) K) :
    spFlagResMat t (mat r K (spFlagResEmb t M)) = mat (r - t) K M := by
  ext α β
  exact spEmbedMat_apply_image (spFlagShift_injective t r le_rfl) _ α β

theorem spFlagCutMat_spFlagResEmb {a b t : ℕ} (hb : b ≤ r) (hbt : b ≤ t) (M : StatedSp (r - t) K) :
    spFlagCutMat a b hb (mat r K (spFlagResEmb t M)) = 1 := by
  refine spFlag_submatrix_spEmbedMat _ (Sum.inl_injective.comp (spFlagShift_injective _ _ _))
    fun i h => ?_
  obtain ⟨j, h1, -, hj⟩ := lt_of_mem_range_spFlagShift_map le_rfl h
  have hi := i.isLt
  rcases hj with hj | hj
  · simp only [Function.comp_apply, Sum.inl.injEq] at hj
    have := congrArg Fin.val hj
    simp only [coe_spFlagShift] at this
    omega
  · exact Sum.inl_ne_inr hj

theorem spFlag_mulVec_mem_isoFlag {c : ℕ} {E : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hE : ∀ l : Fin r, (l : ℕ) < c → ∀ k : Fin r ⊕ Fin r,
      (∀ j : Fin r, k = Sum.inl j → c ≤ (j : ℕ)) → E k (Sum.inl l) = 0)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ SymplecticFlag.isoFlag r K c) :
    E *ᵥ v ∈ SymplecticFlag.isoFlag r K c := by
  obtain ⟨hv1, hv2⟩ := SymplecticFlag.mem_isoFlag.mp hv
  have key : ∀ k : Fin r ⊕ Fin r, (∀ j : Fin r, k = Sum.inl j → c ≤ (j : ℕ)) →
      (E *ᵥ v) k = 0 := by
    intro k hk
    simp only [mulVec, dotProduct, Fintype.sum_sum_type]
    rw [Finset.sum_eq_zero fun l _ => ?_, Finset.sum_eq_zero fun l _ => ?_, add_zero]
    · rw [hv1 l, mul_zero]
    · by_cases hl : (l : ℕ) < c
      · rw [hE l hl k hk, zero_mul]
      · rw [hv2 l (not_lt.mp hl), mul_zero]
  refine SymplecticFlag.mem_isoFlag.mpr ⟨fun j => key _ fun _ h => absurd h Sum.inr_ne_inl,
    fun j hj => key _ fun j' h => ?_⟩
  rw [Sum.inl.injEq] at h
  exact h ▸ hj

theorem spFlag_mem_flagStabilizer {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {g : StatedSp r K}
    (h : ∀ c ∈ I, ∀ v ∈ SymplecticFlag.isoFlag r K c,
      mat r K g *ᵥ v ∈ SymplecticFlag.isoFlag r K c ∧
        mat r K g⁻¹ *ᵥ v ∈ SymplecticFlag.isoFlag r K c) :
    g ∈ flagStabilizer r K I := by
  refine mem_flagStabilizer.mpr fun c hc => ?_
  rw [SymplecticFlag.flag, ite_eq_left (hI c hc)]
  exact SymplecticFlag.mem_stabilizer_of_mulVec_mem (fun v hv => (h c hc v hv).1)
    fun v hv => (h c hc v hv).2

theorem spFlagCutEmb_entry {a b c : ℕ} (hb : b ≤ r) (hc : c ≤ a ∨ b ≤ c) (A : GL (Fin (b - a)) K)
    (l : Fin r) (hl : (l : ℕ) < c) (k : Fin r ⊕ Fin r)
    (hk : ∀ j : Fin r, k = Sum.inl j → c ≤ (j : ℕ)) :
    mat r K (spFlagCutEmb a b hb A) k (Sum.inl l) = 0 := by
  rw [mat_spFlagCutEmb]
  by_cases hboth : k ∈ Set.range (Sum.map (spFlagShift a b hb) (spFlagShift a b hb)) ∧
      Sum.inl l ∈ Set.range (Sum.map (spFlagShift a b hb) (spFlagShift a b hb))
  · obtain ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩ := hboth
    rw [← hy, spEmbedMat_apply_image (spFlagShift_injective a b hb)]
    rcases y with y | y
    · rcases x with x | x
      · exfalso
        have hx := x.isLt
        have hy' : (l : ℕ) = a + y := by
          simp only [Sum.map_inl, Sum.inl.injEq] at hy
          rw [← hy, coe_spFlagShift]
        have := hk _ rfl
        simp only [coe_spFlagShift] at this
        omega
      · simp
    · exact absurd hy (by simp)
  · rw [spEmbedMat_apply_of_not_mem _ hboth, one_apply, ite_eq_right]
    rintro rfl
    exact absurd (hk l rfl) (not_le.mpr hl)

theorem spFlagCutEmb_mem {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {a b : ℕ} (hb : b ≤ r)
    (hab : ∀ c ∈ I, c ≤ a ∨ b ≤ c) (A : GL (Fin (b - a)) K) :
    spFlagCutEmb a b hb A ∈ flagStabilizer r K I := by
  refine spFlag_mem_flagStabilizer hI fun c hc v hv => ⟨?_, ?_⟩
  · exact spFlag_mulVec_mem_isoFlag (spFlagCutEmb_entry hb (hab c hc) A) hv
  · rw [← map_inv]
    exact spFlag_mulVec_mem_isoFlag (spFlagCutEmb_entry hb (hab c hc) A⁻¹) hv

theorem spFlagResEmb_entry {t c : ℕ} (hc : c ≤ t) (M : StatedSp (r - t) K) (l : Fin r)
    (hl : (l : ℕ) < c) (k : Fin r ⊕ Fin r) (hk : ∀ j : Fin r, k = Sum.inl j → c ≤ (j : ℕ)) :
    mat r K (spFlagResEmb t M) k (Sum.inl l) = 0 := by
  have hnot : ¬(k ∈ Set.range (Sum.map (spFlagShift t r le_rfl) (spFlagShift t r le_rfl)) ∧
      Sum.inl l ∈ Set.range (Sum.map (spFlagShift t r le_rfl) (spFlagShift t r le_rfl))) := by
    rintro ⟨-, h⟩
    obtain ⟨j, h1, -, hj⟩ := lt_of_mem_range_spFlagShift_map le_rfl h
    rcases hj with hj | hj
    · rw [Sum.inl.injEq] at hj
      subst hj
      omega
    · exact Sum.inl_ne_inr hj
  rw [spFlagResEmb, mat_spEmbed, spEmbedMat_apply_of_not_mem _ hnot, one_apply, ite_eq_right]
  rintro rfl
  exact absurd (hk l rfl) (not_le.mpr hl)

theorem spFlagResEmb_mem {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (ht : ∀ c ∈ I, c ≤ t)
    (M : StatedSp (r - t) K) : spFlagResEmb t M ∈ flagStabilizer r K I := by
  refine spFlag_mem_flagStabilizer hI fun c hc v hv => ⟨?_, ?_⟩
  · exact spFlag_mulVec_mem_isoFlag (spFlagResEmb_entry (ht c hc) M) hv
  · rw [← map_inv]
    exact spFlag_mulVec_mem_isoFlag (spFlagResEmb_entry (ht c hc) M⁻¹) hv

theorem mem_unipotent_of_blocks {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)
    {g : StatedSp r K} (hg : g ∈ flagStabilizer r K I)
    (hcut : ∀ (b : ℕ) (hb : b ∈ I), spFlagCutMat (spFlagPrev I b) b (hI b hb) (mat r K g) = 1)
    (hres : spFlagResMat t (mat r K g) = 1) : g ∈ SymplecticFlag.unipotent r K := by
  classical
  have hgt := spFlag_mem_stabilizer hI hg htI
  have htr : t ≤ r := hI t htI
  have hresE : ∀ α β, mat r K g (spFlagResIdx t α) (spFlagResIdx t β) =
      (1 : Matrix (Fin (r - t) ⊕ Fin (r - t)) (Fin (r - t) ⊕ Fin (r - t)) K) α β :=
    fun α β => congrFun (congrFun hres α) β
  have hshift : ∀ j : Fin r, t ≤ (j : ℕ) → ∃ i : Fin (r - t), spFlagShift t r le_rfl i = j :=
    fun j hj => (mem_range_spFlagShift le_rfl).mpr ⟨hj, j.isLt⟩
  have hdiag : ∀ i j : Fin r, (j : ℕ) ≤ (i : ℕ) →
      mat r K g (Sum.inl i) (Sum.inl j) = if i = j then 1 else 0 := by
    intro i j hji
    by_cases hjt : t ≤ (j : ℕ)
    · obtain ⟨i', rfl⟩ := hshift i (hjt.trans hji)
      obtain ⟨j', rfl⟩ := hshift j hjt
      have := hresE (Sum.inl i') (Sum.inl j')
      rw [spFlagResIdx, Sum.map_inl, Sum.map_inl] at this
      rw [this, one_apply]
      simp [(spFlagShift_injective t r le_rfl).eq_iff]
    · have hex : ∃ c, c ∈ I ∧ (j : ℕ) < c := ⟨t, htI, not_le.mp hjt⟩
      set b := Nat.find hex with hbdef
      have hbI : b ∈ I := (Nat.find_spec hex).1
      have hjb : (j : ℕ) < b := (Nat.find_spec hex).2
      have hprev : spFlagPrev I b ≤ (j : ℕ) := by
        rcases spFlagPrev_mem I b with h0 | hmem
        · omega
        · by_contra hlt
          have := Nat.find_min' hex ⟨hmem, not_le.mp hlt⟩
          have := spFlagPrev_le I b
          omega
      by_cases hib : (i : ℕ) < b
      · have := congrFun (congrFun (hcut b hbI) ⟨(i : ℕ) - spFlagPrev I b, by omega⟩)
          ⟨(j : ℕ) - spFlagPrev I b, by omega⟩
        rw [spFlagCutMat_apply] at this
        have hi' : spFlagShift (spFlagPrev I b) b (hI b hbI) ⟨(i : ℕ) - spFlagPrev I b, by omega⟩ =
            i := Fin.ext (by simp [coe_spFlagShift]; omega)
        have hj' : spFlagShift (spFlagPrev I b) b (hI b hbI) ⟨(j : ℕ) - spFlagPrev I b, by omega⟩ =
            j := Fin.ext (by simp [coe_spFlagShift]; omega)
        rw [hi', hj', one_apply] at this
        rw [this]
        congr 1
        exact propext ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega),
          fun h => by subst h; rfl⟩
      · rw [spFlag_inl_inl_eq_zero (spFlag_mem_stabilizer hI hg hbI) hjb (not_lt.mp hib),
          ite_eq_right]
        rintro rfl
        omega
  have hlow : (mat r K g).toBlocks₂₁ = 0 := by
    ext i j
    rw [toBlocks₂₁, of_apply, Matrix.zero_apply]
    by_cases hjt : t ≤ (j : ℕ)
    · by_cases hit : t ≤ (i : ℕ)
      · obtain ⟨i', rfl⟩ := hshift i hit
        obtain ⟨j', rfl⟩ := hshift j hjt
        have := hresE (Sum.inr i') (Sum.inl j')
        rw [spFlagResIdx, Sum.map_inr, Sum.map_inl] at this
        rw [this]
        simp
      · exact spFlag_inr_eq_zero hgt (not_le.mp hit) fun _ h => absurd h Sum.inl_ne_inr
    · exact spFlag_inr_inl_eq_zero hgt (not_le.mp hjt) i
  obtain ⟨-, C, hC, hgC⟩ := SymplecticFlag.exists_blockMat_of_toBlocks₂₁_eq_zero hlow
  refine ⟨_, C, ⟨fun i j hji => ?_, fun i => ?_⟩, hC, hgC⟩
  · rw [toBlocks₁₁, of_apply, ← mat_apply, hdiag i j hji.le]
    exact ite_eq_right (ne_of_gt hji)
  · rw [toBlocks₁₁, of_apply, ← mat_apply, hdiag i i le_rfl, ite_eq_left rfl]

theorem isPGroup_spFlag_unipotent [Finite K] [CharP K 2] :
    IsPGroup 2 (SymplecticFlag.unipotent r K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  rw [← hP]
  exact P.isPGroup'

end CFSG.AGLEmbedding.LeviBlock
