module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpMat
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer fieldSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

theorem exists_data [Finite K] [CharP K 2] (hr : 2 ≤ r) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ}
    (htI : t ∈ I) {α : MulAut (StatedSp r K)} (hα : Odd (orderOf α))
    (hn : SpNormFix (fun i hi => (hI i hi).2) htI α) :
    ∃ (g : flagStabilizer r K I) (σ : K ≃+* K),
      ∀ x, α x = (g : StatedSp r K) * fieldSp r K σ x * (g : StatedSp r K)⁻¹ := by
  obtain ⟨g, σ, hg⟩ := exists_conj_fieldSp_of_odd hr hα
  have hgQ : g ∈ flagStabilizer r K I := by
    apply mem_flagStabilizer_of_conj_mem hI
    intro q hq
    have h1 : α (fieldSp r K σ⁻¹ q) = g * q * g⁻¹ := by
      rw [hg, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [← h1]
    exact hn.1 _ (fieldSp_mem_flagStabilizer (fun i hi => (hI i hi).2) σ⁻¹ hq)
  exact ⟨⟨g, hgQ⟩, σ, hg⟩

variable (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)

theorem map_one_add_single {ι : Type*} [DecidableEq ι] (σ : K ≃+* K) (i j : ι) (t : K) :
    (1 + Matrix.single i j t : Matrix ι ι K).map σ = 1 + Matrix.single i j (σ t) := by
  ext k l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

include hI htI in
theorem cut_relation (hI1 : ∀ i ∈ I, 1 ≤ i) {α : MulAut (StatedSp r K)}
    (hn : SpNormFix hI htI α) {g : flagStabilizer r K I} {σ : K ≃+* K}
    (hα : ∀ x, α x = (g : StatedSp r K) * fieldSp r K σ x * (g : StatedSp r K)⁻¹) {b : ℕ}
    (hb : b ∈ I) (s : Matrix.SpecialLinearGroup (Fin (b - spFlagPrev I b)) K) :
    ((spFlagCutHom hI (spFlagPrev_mem I b) hb g : GL (Fin (b - spFlagPrev I b)) K) :
        Matrix (Fin (b - spFlagPrev I b)) (Fin (b - spFlagPrev I b)) K) *
      (s : Matrix (Fin (b - spFlagPrev I b)) (Fin (b - spFlagPrev I b)) K).map σ =
    (s : Matrix (Fin (b - spFlagPrev I b)) (Fin (b - spFlagPrev I b)) K) *
      ((spFlagCutHom hI (spFlagPrev_mem I b) hb g : GL (Fin (b - spFlagPrev I b)) K) :
        Matrix (Fin (b - spFlagPrev I b)) (Fin (b - spFlagPrev I b)) K) := by
  set β := spFlagCutHom (K := K) hI (spFlagPrev_mem I b) hb with hβ
  set x₀ : StatedSp r K := spFlagCutEmb (spFlagPrev I b) b (hI b hb)
    (Matrix.SpecialLinearGroup.toGL s) with hx₀
  have hx₀Q : x₀ ∈ flagStabilizer r K I :=
    spFlagCutEmb_mem hI _ (fun _ hc => le_spFlagPrev_or_le hc) _
  have hσx₀ : fieldSp r K σ x₀ ∈ flagStabilizer r K I := fieldSp_mem_flagStabilizer hI σ hx₀Q
  obtain ⟨u, hu1, hu⟩ := hn.2.1 b hb s
  have hu' : u = g * ⟨fieldSp r K σ x₀, hσx₀⟩ * g⁻¹ * (⟨x₀, hx₀Q⟩ : flagStabilizer r K I)⁻¹ := by
    apply Subtype.ext
    rw [hu, hα]
    rfl
  have h1 := cutHom_eq_one_of_leviHom_eq_one hI htI hI1 hb hu1
  rw [hu', map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  have h3 := congrArg (fun y : GL (Fin (b - spFlagPrev I b)) K =>
    (y : Matrix (Fin (b - spFlagPrev I b)) (Fin (b - spFlagPrev I b)) K)) h1
  simp only [Units.val_mul] at h3
  have hβx : β ⟨x₀, hx₀Q⟩ = Matrix.SpecialLinearGroup.toGL s := cutHom_cutEmb hI hb _
  have hβσ := cutHom_fieldSp hI (spFlagPrev_mem I b) hb σ ⟨x₀, hx₀Q⟩ hσx₀
  rw [← hβ, hβx] at hβσ
  rw [hβσ, hβx] at h3
  exact h3

include hI htI in
theorem res_relation (hmax : ∀ c ∈ I, c ≤ t) {α : MulAut (StatedSp r K)}
    (hn : SpNormFix hI htI α) {g : flagStabilizer r K I} {σ : K ≃+* K}
    (hα : ∀ x, α x = (g : StatedSp r K) * fieldSp r K σ x * (g : StatedSp r K)⁻¹)
    {c : StatedSp (r - t) K} (hc : c ∈ spResBlock K (r - t)) :
    spFlagResHom hI htI g * fieldSp (r - t) K σ c = c * spFlagResHom hI htI g := by
  set x₀ : StatedSp r K := spFlagResEmb t c with hx₀
  have hx₀Q : x₀ ∈ flagStabilizer r K I := spFlagResEmb_mem hI hmax c
  have hσx₀ : fieldSp r K σ x₀ ∈ flagStabilizer r K I := fieldSp_mem_flagStabilizer hI σ hx₀Q
  obtain ⟨u, hu1, hu⟩ := hn.2.2 c hc
  have hu' : u = g * ⟨fieldSp r K σ x₀, hσx₀⟩ * g⁻¹ * (⟨x₀, hx₀Q⟩ : flagStabilizer r K I)⁻¹ := by
    apply Subtype.ext
    rw [hu, hα]
    rfl
  have h1 := resHom_eq_one_of_leviHom_eq_one hI htI hu1
  rw [hu', map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
    mul_inv_eq_iff_eq_mul, resHom_fieldSp' hI htI σ ⟨x₀, hx₀Q⟩ hσx₀,
    resHom_resEmb hI htI hmax c] at h1
  exact h1

theorem ringEquiv_eq_one_of_card_two (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 := by
  obtain ⟨u, hu0, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  have h1 : (1 : K) = u := huniq 1 one_ne_zero
  ext x
  by_cases hx : x = 0
  · rw [hx, map_zero]
    rfl
  · rw [huniq x hx, ← h1, map_one]
    rfl

theorem pairRootMat_inl_inr_self_eq {m : ℕ} (i : Fin m) (t : K) :
    SymplecticHigher.pairRootMat K (Sum.inl i) (Sum.inr i) t =
      1 + Matrix.single (Sum.inl i) (Sum.inr i) t := by
  rw [SymplecticHigher.pairRootMat_inl_inr_self, Matrix.smul_single, smul_eq_mul, mul_one]

include hI htI in
theorem sigma_eq_one [Finite K] [CharP K 2] (hI1 : ∀ i ∈ I, 1 ≤ i) (hmax : ∀ c ∈ I, c ≤ t)
    (hbig : 1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b) {α : MulAut (StatedSp r K)}
    (hn : SpNormFix hI htI α) {g : flagStabilizer r K I} {σ : K ≃+* K}
    (hα : ∀ x, α x = (g : StatedSp r K) * fieldSp r K σ x * (g : StatedSp r K)⁻¹) : σ = 1 := by
  by_cases hK : Nat.card K = 2
  · exact ringEquiv_eq_one_of_card_two hK σ
  have key : ∀ t' : K, σ t' = t' := by
    rcases hbig with hm | ⟨b, hb, hk⟩
    ·
      set m := r - t with hmdef
      have hm' : 1 ≤ m := hm
      have hres : spResBlock K m = ⊤ := by
        have hs : ¬ (m = 1 ∧ Nat.card K = 2) := fun h => hK h.2
        rw [spResBlock, if_neg hs]
        exact (isQuasisimple_statedSp_of_not_small (K := K) hm' hs (fun h => hK h.2)).1
      set i₀ : Fin m := ⟨0, hm'⟩ with hi₀
      have hab : (Sum.inl i₀ : Fin m ⊕ Fin m) ≠ Sum.inr i₀ := Sum.inl_ne_inr
      set γ := spFlagResHom hI htI g with hγ
      refine eq_of_transvection_rel σ.toRingHom (B := mat m K γ) (B' := mat m K γ⁻¹) ?_ hab ?_
      · rw [← map_mul, inv_mul_cancel, map_one]
      · intro t'
        have hc : SymplecticHigher.pairRootElt hab t' ∈ spResBlock K m := by
          rw [hres]
          exact Subgroup.mem_top _
        have hmatc : mat m K (SymplecticHigher.pairRootElt hab t') =
            1 + Matrix.single (Sum.inl i₀) (Sum.inr i₀) t' :=
          pairRootMat_inl_inr_self_eq i₀ t'
        have h := congrArg (mat m K) (res_relation hI htI hmax hn hα hc)
        rw [map_mul, map_mul, mat_fieldSp, hmatc, map_one_add_single] at h
        exact h
    ·
      set k := b - spFlagPrev I b with hkdef
      set i₀ : Fin k := ⟨0, by omega⟩ with hi₀
      set j₀ : Fin k := ⟨1, by omega⟩ with hj₀
      have hij : i₀ ≠ j₀ := fun h => by
        have := congrArg Fin.val h
        simp [i₀, j₀] at this
      set B := spFlagCutHom hI (spFlagPrev_mem I b) hb g with hB
      have hBB' : ((B⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *
          ((B : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      refine eq_of_transvection_rel σ.toRingHom hBB' hij (fun t' => ?_)
      have h := cut_relation hI htI hI1 hn hα hb (Matrix.SpecialLinearGroup.transvection hij t')
      rw [Matrix.SpecialLinearGroup.transvection_coe, map_one_add_single] at h
      exact h
  ext x
  exact key x

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
